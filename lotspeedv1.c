/*
 * lotspeed_zeta_v5_8_da.c
 * Zeta-TCP (Dynamic Alpha Edition)
 * 核心：FAST TCP + 动态 Alpha 适配 + RTT 低通滤波
 * 适用场景：中美跨境 BGP、长距离高带宽链路
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/version.h>
#include <linux/moduleparam.h>
#include <linux/jiffies.h>
#include <linux/time.h>
#include <linux/string.h>
#include <linux/math64.h>
#include <net/tcp.h>
#include <linux/tcp.h>
#include <linux/hashtable.h>
#include <linux/slab.h>

#define SAFETY_CHECK(ptr, ret) do { \
    if (unlikely(!(ptr))) { \
        return ret; \
    } \
} while (0)

#define SAFE_DIV64(n, d) ((d) ? div64_u64((n), (d)) : 0)

#define LOTSPEED_BETA_SCALE 1024
#define LOTSPEED_PROBE_RTT_INTERVAL_MS 10000
#define LOTSPEED_PROBE_RTT_DURATION_MS 500
#define LOTSPEED_MAX_U32 ((u32)~0U)
#define FAST_GAMMA_SHIFT 7  // 使用 128 (1<<7) 作为标度，优化除法为位移

// --- 模块参数 ---
static unsigned long lotserver_rate = 125000000;      // 1Gbps 默认上限
static unsigned int lotserver_min_cwnd = 16;
static unsigned int lotserver_max_cwnd = 65535;       // 针对大带宽调高
static unsigned int lotserver_beta = 800;             // 丢包缩减 (800/1024 ~ 78%)
static bool lotserver_turbo = false;
static bool lotserver_safe_mode = true;
static unsigned int lotserver_fast_alpha = 30;        // 基础 Alpha
static unsigned int lotserver_fast_gamma = 40;        // 响应灵敏度
static unsigned int lotserver_fast_ss_exit = 25;      // SS 退出阈值
static bool lotserver_hd_enable = true;
static unsigned int lotserver_hd_thresh_us = 160000;  // 160ms 判定为高延迟
static unsigned int lotserver_hd_ref_us = 80000;      // 参考 RTT
static unsigned int lotserver_hd_gamma_boost = 20;
static unsigned int lotserver_hd_alpha_boost = 15;
static bool lotserver_brave_enable = true;
static unsigned int lotserver_brave_rtt_pct = 40;     // 跨境抖动容忍度 40%
static unsigned int lotserver_brave_hold_ms = 600;    // 冻结 600ms
static unsigned int lotserver_brave_floor_pct = 90;   // 地板窗口 90%

// --- 内部状态 ---
enum lotspeed_state {
    FAST_STARTUP = 0,
    FAST_CA,
    PROBE_RTT,
};

struct lotspeed {
    u64 pacing_rate;
    u32 rtt_min;          // 过滤后的基准 RTT
    u32 last_state_ts;
    u32 probe_rtt_ts;
    u32 brave_hold_cwnd;
    u32 brave_freeze_until;
    u32 dyn_alpha;        // 动态生成的 Alpha
    enum lotspeed_state state;
    bool ss_mode;
};

static void enter_state(struct sock *sk, enum lotspeed_state new_state)
{
    struct lotspeed *ca = inet_csk_ca(sk);
    if (ca->state != new_state) {
        ca->state = new_state;
        ca->last_state_ts = tcp_jiffies32;
    }
}

static void lotspeed_init(struct sock *sk)
{
    struct tcp_sock *tp = tcp_sk(sk);
    struct lotspeed *ca = inet_csk_ca(sk);

    memset(ca, 0, sizeof(*ca));
    ca->state = FAST_STARTUP;
    ca->ss_mode = true;
    ca->last_state_ts = tcp_jiffies32;
    ca->probe_rtt_ts = tcp_jiffies32;
    ca->dyn_alpha = lotserver_fast_alpha;
    tp->snd_ssthresh = TCP_INFINITE_SSTHRESH;

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0)
    cmpxchg(&sk->sk_pacing_status, SK_PACING_NONE, SK_PACING_NEEDED);
#endif
}

// --- 核心控制算法 ---
static void lotspeed_adapt_and_control(struct sock *sk, const struct rate_sample *rs, int flag)
{
    struct tcp_sock *tp = tcp_sk(sk);
    struct lotspeed *ca = inet_csk_ca(sk);
    u32 raw_rtt_us = tp->srtt_us >> 3;
    u32 rtt_us, base_rtt;
    u32 cwnd = tp->snd_cwnd;
    u32 mss = tp->mss_cache ? : 1460;
    u64 gamma, cwnd_target;
    bool high_delay_path;
    u32 now_jif = tcp_jiffies32;

    SAFETY_CHECK(tp && ca, );

    // 1. RTT 低通滤波：平滑 BGP 切换带来的瞬时波动 (权重 7/8)
    if (likely(ca->rtt_min > 0 && raw_rtt_us > 0)) {
        rtt_us = (ca->rtt_min * 7 + raw_rtt_us) >> 3;
    } else {
        rtt_us = raw_rtt_us ? raw_rtt_us : 1000;
    }

    // 更新基准 RTT
    if (!ca->rtt_min || rtt_us < ca->rtt_min)
        ca->rtt_min = rtt_us;
    
    base_rtt = ca->rtt_min;

    // 2. PROBE_RTT 周期性探测逻辑
    if (ca->state != PROBE_RTT &&
        time_after32(now_jif, ca->probe_rtt_ts + msecs_to_jiffies(LOTSPEED_PROBE_RTT_INTERVAL_MS))) {
        enter_state(sk, PROBE_RTT);
    }

    if (ca->state == PROBE_RTT) {
        tp->snd_cwnd = lotserver_min_cwnd;
        if (time_after32(now_jif, ca->last_state_ts + msecs_to_jiffies(LOTSPEED_PROBE_RTT_DURATION_MS))) {
            ca->probe_rtt_ts = now_jif;
            enter_state(sk, ca->ss_mode ? FAST_STARTUP : FAST_CA);
        }
        goto out_pacing;
    }

    // 3. Dynamic Alpha 适配
    if (base_rtt > 0) {
        u32 inflate_pct = (rtt_us * 100) / base_rtt;
        if (inflate_pct <= 110) { 
            // 链路空闲，Alpha 逐步增加以探索上限
            ca->dyn_alpha = min_t(u32, lotserver_fast_alpha * 3, ca->dyn_alpha + 2);
        } else if (inflate_pct > 140) {
            // 拥塞出现，Alpha 快速收缩
            ca->dyn_alpha = max_t(u32, lotserver_fast_alpha / 2, ca->dyn_alpha - 4);
        }
    }

    // 4. 慢启动与拥塞避免
    if (ca->ss_mode) {
        if (rs && rs->acked_sacked > 0)
            cwnd = tp->snd_cwnd + rs->acked_sacked;
        
        if (base_rtt && rtt_us > base_rtt + (base_rtt * lotserver_fast_ss_exit) / 100) {
            ca->ss_mode = false;
            enter_state(sk, FAST_CA);
        }
        tp->snd_cwnd = clamp(cwnd, lotserver_min_cwnd, lotserver_max_cwnd);
    } else {
        // FAST 核心公式计算
        // gamma 转换为 128 进制
        gamma = min_t(u64, (u64)lotserver_fast_gamma * 128 / 100, 128);

        if (base_rtt > 0 && rtt_us > 0) {
            cwnd_target = ((u64)tp->snd_cwnd * base_rtt) / rtt_us;
            cwnd_target += ca->dyn_alpha;

            high_delay_path = lotserver_hd_enable && base_rtt >= lotserver_hd_thresh_us;
            if (high_delay_path) {
                u64 ref = lotserver_hd_ref_us ? lotserver_hd_ref_us : 80000;
                u64 rho = clamp_t(u64, (u64)base_rtt * 128 / ref, 128, 512); 
                cwnd_target = (cwnd_target * rho) >> 7;
                cwnd_target += lotserver_hd_alpha_boost;
                gamma = min_t(u64, gamma + (lotserver_hd_gamma_boost * 128 / 100), 128);
            }

            // 迭代更新: cwnd = ( (128-gamma)*cwnd + gamma*target ) / 128
            cwnd = (u32)(((u64)tp->snd_cwnd * (128 - gamma) + cwnd_target * gamma) >> 7);
        }
        tp->snd_cwnd = clamp_t(u32, cwnd, lotserver_min_cwnd, lotserver_max_cwnd);
    }

    // 勇敢模式 (Brave Mode) 保护
    if (lotserver_brave_enable && base_rtt > 0) {
        if (rtt_us > base_rtt + (base_rtt * lotserver_brave_rtt_pct) / 100) {
            ca->brave_hold_cwnd = tp->snd_cwnd;
            ca->brave_freeze_until = now_jif + msecs_to_jiffies(lotserver_brave_hold_ms);
        }
        if (time_before(now_jif, ca->brave_freeze_until)) {
            u32 floor = (ca->brave_hold_cwnd * lotserver_brave_floor_pct) / 100;
            if (tp->snd_cwnd < floor) tp->snd_cwnd = floor;
        }
    }

out_pacing:
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0)
    if (mss > 0 && rtt_us > 0) {
        u64 rate = SAFE_DIV64((u64)tp->snd_cwnd * mss * USEC_PER_SEC, rtt_us);
        if (rate > lotserver_rate) rate = lotserver_rate;
        sk->sk_pacing_rate = rate;
    }
#endif
}

// --- 基础 Hook ---
static u32 lotspeed_ssthresh(struct sock *sk)
{
    struct tcp_sock *tp = tcp_sk(sk);
    struct lotspeed *ca = inet_csk_ca(sk);
    if (ca) ca->ss_mode = false;
    return max_t(u32, (tp->snd_cwnd * lotserver_beta) / LOTSPEED_BETA_SCALE, lotserver_min_cwnd);
}

static void lotspeed_cong_control(struct sock *sk, const struct rate_sample *rs)
{
    lotspeed_adapt_and_control(sk, rs, 0);
}

static struct tcp_congestion_ops lotspeed_ops __read_mostly = {
    .name         = "lotspeed",
    .owner        = THIS_MODULE,
    .init         = lotspeed_init,
    .cong_control = lotspeed_cong_control,
    .ssthresh     = lotspeed_ssthresh,
    .flags        = TCP_CONG_NON_RESTRICTED,
};

static int __init lotspeed_module_init(void)
{
    return tcp_register_congestion_control(&lotspeed_ops);
}

static void __exit lotspeed_module_exit(void)
{
    tcp_unregister_congestion_control(&lotspeed_ops);
}

module_init(lotspeed_module_init);
module_exit(lotspeed_module_exit);

MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("LotSpeed Zeta DA - Dynamic Alpha for Trans-Pacific BGP");
MODULE_VERSION("5.8");
