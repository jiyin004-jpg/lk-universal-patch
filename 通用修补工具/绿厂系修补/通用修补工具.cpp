/* ============================================================
   通用伪回锁 + 免授权深刷 修补工具 (通用版)
   ------------------------------------------------------------
   不按固件版本区分, 不写死偏移地址:
   1) 内嵌 AArch64 迷你解码器, 按"指令语义结构"动态定位修补点
   2) 对从没见过的固件, 也能自动分析出:
      - 锁定状态检查 (bl; cmp w0,#3; b.hi)
      - 全局状态读取 (adrp; ldr 全局; cmp wN,#3; b.hi)
      - verifiedbootstate 引导状态分发
      - UFS 写保护门控 (0xc200120 ioctl)
      - Orange 警告分发
      - img_auth_required (跳过镜像签名认证)
      - SBC / 安全查询 (SMC 查询或寄存器直读)
   3) 统一打桩方式: 函数头 -> mov w0,#0; ret 或 单指令替换
   4) 每个修补点先验证指令结构, 避免误伤
   QQ 交流群: 2167063739
   ============================================================ */
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <vector>
#include <algorithm>

#ifdef _WIN32
#include <windows.h>
#endif
#ifdef _MSC_VER
#pragma execution_character_set("utf-8")
#endif

typedef uint8_t  u8;
typedef uint32_t u32;
typedef uint64_t u64;

static inline u32 rd32(const u8* p) {
    return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24);
}
static inline void wr32(u8* p, u32 v) {
    p[0] = (u8)(v & 0xff); p[1] = (u8)((v >> 8) & 0xff);
    p[2] = (u8)((v >> 16) & 0xff); p[3] = (u8)((v >> 24) & 0xff);
}
static inline int64_t sext(int64_t v, int bits) {
    if (v & ((int64_t)1 << (bits - 1))) v -= ((int64_t)1 << bits);
    return v;
}

/* ==================== MTK 分区容器识别 ==================== */
#define MTK_MAGIC 0x58881688u
struct Partition { std::string name; u64 data_off; u64 data_len; };

static bool find_partition(const std::vector<u8>& img, const char* want, Partition& out) {
    for (size_t off = 0; off + 0x200 <= img.size(); off += 4) {
        if (rd32(&img[off]) != MTK_MAGIC) continue;
        char name[33]; memcpy(name, &img[off + 8], 32); name[32] = 0;
        if (strcmp(name, want) != 0) continue;
        u32 dsize = rd32(&img[off + 4]);
        u32 dsize_ext = rd32(&img[off + 0x48]);
        u64 dsize64 = ((u64)dsize_ext << 32) | dsize;
        u32 hdr_size = rd32(&img[off + 0x34]);
        if (hdr_size == 0 || hdr_size > 0x1000) hdr_size = 0x200;
        if (dsize64 == 0 || off + hdr_size + dsize64 > img.size()) continue;
        out.name = name; out.data_off = off + hdr_size; out.data_len = dsize64;
        return true;
    }
    return false;
}

/* ==================== AArch64 迷你解码器 (语义判定) ==================== */
static inline bool is_bl(u32 v)    { return (v & 0xFC000000u) == 0x94000000u; }
static inline bool is_b(u32 v)     { return (v & 0xFC000000u) == 0x14000000u; }
static inline bool is_bcond(u32 v) { return (v & 0xFF000010u) == 0x54000000u; }
static inline bool is_adrp_rd(u32 v, int* rd) {
    if ((v & 0x9F000000u) != 0x90000000u) return false;
    *rd = v & 0x1F;
    return true;
}
static inline bool is_pacia(u32 v) { return v == 0xD503233Fu; }

static inline bool is_stp_x29x30_pre(u32 v, int* imm) {
    if ((v & 0xFFC00000u) != 0xA9800000u) return false;
    if ((v & 0x1Fu) != 29 || ((v >> 10) & 0x1Fu) != 30) return false;
    int i7 = (int)sext((v >> 15) & 0x7F, 7);
    *imm = i7 * 8;
    return true;
}
/* stp x29,x30,[sp,#imm] (非 pre-index, 通常跟在 sub sp 后). A899 掩码 + Rt=x29 R2=x30 */
static inline bool is_stp_x29x30_off(u32 v, int* imm) {
    if ((v & 0xFFC00000u) != 0xA9000000u) return false;
    if ((v & 0x1Fu) != 29 || ((v >> 10) & 0x1Fu) != 30) return false;
    *imm = (int)(((v >> 15) & 0x7F) * 8);
    return true;
}
/* sub sp,sp,#imm (栈帧建立, 替代 stp pre-index 的另一种序言形态) */
static inline bool is_sub_sp_imm(u32 v, int* imm) {
    if ((v & 0xFF8003FFu) != 0xD10003FFu) return false;
    *imm = (int)(((v >> 10) & 0xFFF) << (((v >> 22) & 3) * 12));
    return true;
}
static inline bool is_cmp_w_imm(u32 v, int* rn, int* imm) {
    if ((v & 0x7F000000u) != 0x71000000u) return false;
    if ((v & 0x1Fu) != 31) return false;
    *rn = (v >> 5) & 0x1F;
    *imm = (int)(((v >> 10) & 0xFFF) << (((v >> 22) & 3) * 12));   /* 含 lsl#12 移位 */
    return true;
}
static inline bool is_mov_w_imm(u32 v, int* rd, int* imm) {
    if ((v & 0x80000000u) != 0) return false;              /* 只认 32 位 mov w (bit31=0) */
    if ((v & 0x7F800000u) != 0x52800000u) return false;
    *rd = v & 0x1F;
    *imm = (int)(((v >> 5) & 0xFFFF) << (((v >> 21) & 3) * 16));
    return true;
}
static inline bool is_movk_w(u32 v, int* rd, int* imm) {
    if ((v & 0x80000000u) != 0) return false;              /* 只认 32 位 movk w (bit31=0) */
    if ((v & 0x7F800000u) != 0x72800000u) return false;
    *rd = v & 0x1F;
    *imm = (int)(((v >> 5) & 0xFFFF) << (((v >> 21) & 3) * 16));
    return true;
}
/* csel D,A,B,eq (条件选择, cond=eq), 同时接受 32/64 位并回传 sf;
   补丁按宽度生成 mov xD,xA / mov wD,wA (老工具对 32 位 csel 误写 64 位 mov) */
static inline bool is_csel_x_eq(u32 v, int* rd, int* rn, int* rm, int* sf) {
    if ((v & 0x7FE00C00u) != 0x1A800000u) return false;
    if (((v >> 12) & 0xF) != 0) return false;   /* 只接受 cond=eq */
    *rd = v & 0x1F; *rn = (v >> 5) & 0x1F; *rm = (v >> 16) & 0x1F;
    *sf = (int)((v >> 31) & 1);
    return true;
}
/* cset wD (csinc wD,wzr,wzr,cond): Rn=Rm=31 */
static inline bool is_cset_w(u32 v, int* rd, int* cond) {
    if ((v & 0x7FE00C00u) != 0x1A800400u) return false;
    if (((v >> 5) & 0x1F) != 31 || ((v >> 16) & 0x1F) != 31) return false;
    *rd = v & 0x1F; *cond = (v >> 12) & 0xF;
    return true;
}
/* and w0,w0,#imm (逻辑与立即数, 用于 bl2 安全校验特征结尾) */
static inline bool is_and_w0_w0_imm(u32 v) {
    if ((v & 0x7F000000u) != 0x12000000u) return false;
    if ((v & 0x3FF) != 0) return false;   /* Rd=Rn=0 (bits[9:0] 全为 0) */
    return true;
}

static inline bool is_ldr_w_imm(u32 v, int* rt, int* rn, int* imm12) {
    if ((v & 0xFFC00000u) != 0xB9400000u) return false;
    *rt = v & 0x1F; *rn = (v >> 5) & 0x1F; *imm12 = (int)((v >> 10) & 0xFFF);
    return true;
}
static inline bool is_ldrsw_x_imm(u32 v, int* rt, int* rn, int* imm12) {
    if ((v & 0xFFC00000u) != 0xB9800000u) return false;
    *rt = v & 0x1F; *rn = (v >> 5) & 0x1F; *imm12 = (int)((v >> 10) & 0xFFF);
    return true;
}
static inline bool is_str_w_imm(u32 v, int* rt, int* rn, int* imm12) {
    if ((v & 0xFFC00000u) != 0xB9000000u) return false;
    *rt = v & 0x1F; *rn = (v >> 5) & 0x1F; *imm12 = (int)((v >> 10) & 0xFFF);
    return true;
}
static inline bool is_add_x_imm(u32 v, int* rd, int* rn, int* imm) {
    if ((v & 0x9F000000u) != 0x91000000u) return false;   /* 保留 sf 位 */
    *rd = v & 0x1F; *rn = (v >> 5) & 0x1F;
    *imm = (int)(((v >> 10) & 0xFFF) << (((v >> 22) & 3) * 12));   /* 含 lsl#12 移位 */
    return true;
}
static inline bool is_add_w_imm(u32 v, int* rd, int* rn, int* imm) {
    if ((v & 0x7F000000u) != 0x11000000u) return false;
    *rd = v & 0x1F; *rn = (v >> 5) & 0x1F;
    *imm = (int)(((v >> 10) & 0xFFF) << (((v >> 22) & 3) * 12));   /* 含 lsl#12 移位 */
    return true;
}

/* ==================== 结果 ==================== */
enum { PR_OK = 1, PR_ALREADY = 0, PR_FAIL = -1, PR_SKIP = -2 };  /* SKIP=此固件无该结构 */
struct PatchInfo { std::string name; std::string desc; u64 at; int result; };

static void note_result(std::vector<PatchInfo>& stats, const char* name, const char* desc,
                        u64 at, int result) {
    PatchInfo pi;
    pi.name = name; pi.desc = desc; pi.at = at; pi.result = result;
    stats.push_back(pi);
}
static void note_fail(std::vector<PatchInfo>& stats, const char* name, const char* desc) {
    note_result(stats, name, desc, 0, PR_FAIL);
}

/* 函数头打桩: 前 2 条 -> mov x0,#0; ret (验证是合法函数开头)
   若已是返回 0 的打桩 (mov w0,#0;ret 或 mov x0,#0;ret) 视为已存在 */
static int stub_function(u8* reg, size_t reg_len, u64 off) {
    if (off + 8 > reg_len) return PR_FAIL;
    u32 i0 = rd32(reg + off);
    int imm;
    bool hdr_ok = is_stp_x29x30_pre(i0, &imm) || is_pacia(i0) ||
                  /* sub sp,#imm 序言: 下一条须是 stp x29,x30,[sp,#imm] (合法栈帧建立) */
                  (is_sub_sp_imm(i0, &imm) && is_stp_x29x30_off(rd32(reg + off + 4), &imm));
    if (!hdr_ok) {
        u32 i1 = rd32(reg + off + 4);
        if (i1 == 0xD65F03C0u && (i0 == 0x52800000u || i0 == 0xD2800000u)) return PR_ALREADY;
        return PR_FAIL;
    }
    if ((rd32(reg + off) == 0x52800000u || rd32(reg + off) == 0xD2800000u) &&
        rd32(reg + off + 4) == 0xD65F03C0u) return PR_ALREADY;
    wr32(reg + off, 0x52800000u);   /* mov w0,#0 (与已知可用镜像逐字节一致) */
    wr32(reg + off + 4, 0xD65F03C0u);
    return PR_OK;
}

/* ==================== 函数开头扫描 ==================== */
static void scan_function_starts(const u8* reg, size_t len, std::vector<u64>& out) {
    for (u64 off = 0; off + 4 <= len; off += 4) {
        u32 v = rd32(reg + off);
        int im;
        if (is_stp_x29x30_pre(v, &im) || is_pacia(v)) { out.push_back(off); continue; }
        /* sub sp 序言也算函数头, 但前一条是 paciasp 时真函数头在前 (避免重复收集) */
        if (is_sub_sp_imm(v, &im)) {
            bool prev_hdr = off >= 4 && (is_pacia(rd32(reg + off - 4)) ||
                                         is_stp_x29x30_pre(rd32(reg + off - 4), &im));
            if (!prev_hdr) out.push_back(off);
        }
    }
}

/* 从引用点向前找最近函数头.
   若遇到"已打桩函数头"形态(mov x0,#0;ret 标准打桩 / stub4 末尾 mov w0,#0;ret)
   则直接返回该位置(不漂移到更前面的 stp), 由 stub_function 识别为已存在. */
static u64 find_function_start(const u8* reg, size_t len, u64 from) {
    u64 fn = from;
    while (true) {
        u32 v = rd32(reg + fn);
        int im;
        if (is_stp_x29x30_pre(v, &im) || is_pacia(v)) return fn;
        /* sub sp 序言是函数头, 但若其前一条是 paciasp/stp-pre, 真正的函数头在前 (PAC 前缀序言) */
        if (is_sub_sp_imm(v, &im)) {
            bool prev_hdr = fn >= 4 && (is_pacia(rd32(reg + fn - 4)) ||
                                        is_stp_x29x30_pre(rd32(reg + fn - 4), &im));
            if (!prev_hdr) return fn;
        }
        if (fn + 8 <= len && rd32(reg + fn + 4) == 0xD65F03C0u) {
            if (v == 0xD2800000u) return fn;                    /* mov x0,#0; ret = 标准打桩头 */
            if (v == 0x52800000u && fn >= 8) {                  /* mov w0,#0; ret, 查是否 stub4 末尾 */
                u32 a2 = rd32(reg + fn - 4);
                u32 a3 = rd32(reg + fn - 8);
                if ((a2 & 0xFFC00000u) == 0xB9000000u && (a3 & 0x7F800000u) == 0x52800000u)
                    return fn - 8;                              /* stub4 起点 (mov wN,#1) */
            }
        }
        if (fn == 0 || from - fn > 0x600) break;
        fn -= 4;
    }
    return (u64)-1;   /* 未找到 (偏移 0 是合法函数头, 不能用 0 当哨兵) */
}

/* ==================== 字符串引用定位 ====================
   编译器可能把 adrp+add 指向字符串段起点, 也可能指向 needle 子串位置 (如 "Set WP fail").
   因此对 str_off 与其段起点同时查找引用 */
static void find_string_refs(const u8* reg, size_t len, u64 str_off, std::vector<u64>& refs) {
    /* 段起点: 向前延伸到连续 ASCII 可打印的开头 */
    u64 seg = str_off;
    while (seg > 0 && reg[seg - 1] >= 0x20 && reg[seg - 1] <= 0x7e) seg--;
    u64 offs[2] = { str_off, seg };
    for (int k = 0; k < 2; k++) {
        u64 page = offs[k] & ~0xFFFull;
        u32 pgoff = (u32)(offs[k] & 0xFFF);
        for (u64 off = 0; off + 8 <= len; off += 4) {
            u32 v = rd32(reg + off);
            if ((v & 0x9F000000u) != 0x90000000u) continue;
            int rd = v & 0x1F;
            int immlo = (v >> 29) & 3, immhi = (v >> 5) & 0x7FFFF;
            int64_t imm = sext(((int64_t)immhi << 2) | immlo, 21) << 12;
            u64 pg = (off & ~0xFFFull) + imm;
            if (pg != page) continue;
            for (int j = 1; j <= 10; j++) {
                u64 a = off + (u64)j * 4;
                if (a + 4 > len) break;
                u32 w = rd32(reg + a);
                int r2, rn, ia;
                /* 编译器可能用 add x 或 add w 组装字符串地址 */
                if ((is_add_x_imm(w, &r2, &rn, &ia) || is_add_w_imm(w, &r2, &rn, &ia)) &&
                    rn == rd && (u32)ia == pgoff) {
                    refs.push_back(a);
                    break;
                }
            }
        }
    }
    /* 去重 */
    if (refs.size() > 1) {
        std::sort(refs.begin(), refs.end());
        refs.erase(std::unique(refs.begin(), refs.end()), refs.end());
    }
}

/* 在 region 内定位字符串 (精确匹配), 返回相对偏移 */
static bool locate_string(const u8* reg, size_t len, const char* needle, u64* out) {
    size_t sl = strlen(needle);
    for (size_t i = 0; i + sl <= len; i++) {
        if (memcmp(reg + i, needle, sl) == 0) { *out = (u64)i; return true; }
    }
    return false;
}

/* 归一化: 小写 + 仅保留字母数字 (用于跨固件容错比较) */
static std::string norm_str(const std::string& s) {
    std::string r;
    for (size_t i = 0; i < s.size(); i++) {
        unsigned char c = (unsigned char)s[i];
        if (isalnum(c)) r += (char)tolower(c);
    }
    return r;
}

/* 模糊定位字符串: 先精确匹配; 失败后扫描所有 ASCII 字符串段, 归一化后 needle 是候选的子串
   (容忍大小写/下划线/空格/格式符差异, 如 "Orange State" 命中 "OrangeState"/"orange_state")
   防误匹配: 归一化长度差 <= 8 (防止 "orangestate" 命中 "...orangestatereasons..." 超长不相关串) */
static bool locate_string_fuzzy(const u8* reg, size_t len, const char* needle, u64* out) {
    if (locate_string(reg, len, needle, out)) return true;
    std::string n2 = norm_str(needle);
    if (n2.size() < 6) return false;  /* 太短容易误命中 */
    size_t i = 0;
    while (i < len) {
        if (reg[i] < 0x20 || reg[i] > 0x7e) { i++; continue; }
        size_t j = i;
        while (j < len && reg[j] >= 0x20 && reg[j] <= 0x7e) j++;
        if (j - i >= 8) {  /* 只对像样的长字符串做归一化匹配 */
            std::string cur((const char*)reg + i, j - i);
            std::string cn = norm_str(cur);
            if (cn.find(n2) != std::string::npos) {
                size_t dl = cn.size() > n2.size() ? cn.size() - n2.size() : n2.size() - cn.size();
                if (dl <= 8) {  /* 长度收紧: 只接受与 needle 归一化长度接近的候选 */
                    *out = i;  /* 返回该字符串段起点 (adrp+add 引用指向段起点) */
                    return true;
                }
            }
        }
        i = j;
    }
    return false;
}

/* 多候选: 每个候选先精确, 再模糊 */
static bool locate_string_any(const u8* reg, size_t len, const char* const* needles, int n, u64* out) {
    for (int i = 0; i < n; i++)
        if (locate_string(reg, len, needles[i], out)) return true;
    for (int i = 0; i < n; i++)
        if (locate_string_fuzzy(reg, len, needles[i], out)) return true;
    return false;
}

/* ==================== 公共打桩辅助 ====================
   1) state_read_reg: 解码"状态读取指令"的寄存器 (支持 ldr wN / ldrsw xN / 已打桩 mov wN,#imm),
      失败返回 -1
   2) patch_state_zero: 把状态读取打桩为 mov wN,#0 (强制状态=0)
      -> 全局状态读取 / 锁定状态检查(直接读全局型) / 引导分发(跳表型) 三处共用
   3) find_fn_by_string: 字符串引用 -> 最近函数头
      -> img_auth / orange / ufs-swf / verifiedboot(字符串模式) 共用 */
static int state_read_reg(u32 v) {
    int rt, rn, imm12, immv;
    if (is_ldr_w_imm(v, &rt, &rn, &imm12)) return rt;
    if (is_ldrsw_x_imm(v, &rt, &rn, &imm12)) return rt;
    if (is_mov_w_imm(v, &rt, &immv)) return rt;
    return -1;
}
static int patch_state_zero(u8* reg, size_t len, u64 at) {
    if (at + 4 > len) return PR_FAIL;
    int rt = state_read_reg(rd32(reg + at));
    if (rt < 0) return PR_FAIL;
    u32 rep = 0x52800000u | (u32)rt;
    if (rd32(reg + at) == rep) return PR_ALREADY;
    wr32(reg + at, rep);
    return PR_OK;
}
static u64 find_fn_by_string(const u8* reg, size_t len,
                             const char* const* needles, int n) {
    u64 str_off;
    if (!locate_string_any(reg, len, needles, n, &str_off)) return 0;
    std::vector<u64> refs;
    find_string_refs(reg, len, str_off, refs);
    for (size_t r = 0; r < refs.size(); r++) {
        u64 fn = find_function_start(reg, len, refs[r]);
        if (fn != (u64)-1) return fn;
    }
    return 0;
}

/* ==================== 语义定位器 (每类返回候选地址 + 类型) ====================
   type: 0=锁定状态bl  1=全局状态ldr  2=SMC查询函数头  3=寄存器查询函数头
         4=img_auth函数头  5=UFS门控ldr  6=orange函数头  7=verifiedboot函数头
*/
static void locate_lock_state(const u8* reg, size_t len,
                              std::vector<std::pair<u64,int>>& found) {
    /* 1) bl 查询型: 函数头后 bl; cmp w0,#3; b.hi */
    std::vector<u64> starts;
    scan_function_starts(reg, len, starts);
    for (size_t s = 0; s < starts.size(); s++) {
        for (int i = 1; i <= 8; i++) {
            u64 a = starts[s] + (u64)i * 4;
            if (a + 12 > len) break;
            if (!is_bl(rd32(reg + a))) continue;
            int r2, i2;
            u32 c3 = rd32(reg + a + 8);
            if (is_cmp_w_imm(rd32(reg + a + 4), &r2, &i2) && i2 == 3 && r2 == 0 &&
                is_bcond(c3) && (c3 & 0xF) == 0x8) {
                found.push_back(std::make_pair(a, 0));
                break;
            }
        }
    }
    /* 2) 直接读全局型 (新固件): adrp; ldr/ldrsw xN,[xN,#imm]; cmp wN,#3; b.hi
          (与"全局状态读取"同结构, 此处作为锁定状态检查识别, 打桩为 mov wN,#0;
          若状态位已被"全局状态读取"打成 mov wN,#0 也识别为已存在) */
    if (found.empty()) {
        for (u64 off = 4; off + 12 <= len; off += 4) {
            u32 v = rd32(reg + off);
            int rt, rn, imm12, immv;
            bool is_ldr = is_ldr_w_imm(v, &rt, &rn, &imm12) ||
                          is_ldrsw_x_imm(v, &rt, &rn, &imm12);
            if (!is_ldr && !is_mov_w_imm(v, &rt, &immv)) continue;
            if (!is_ldr && immv != 0) continue;   /* 只接受已打桩的 mov wN,#0 */
            /* adrp 目标须等于 ldr 基址(rn) 或已打桩 mov 的值寄存器(rt), 防无关 adrp 误命中 */
            int adrp_rd;
            if (!is_adrp_rd(rd32(reg + off - 4), &adrp_rd)) continue;
            if (adrp_rd != (is_ldr ? rn : rt)) continue;
            int r2, i2;
            if (is_cmp_w_imm(rd32(reg + off + 4), &r2, &i2) && i2 == 3 && r2 == rt) {
                u32 c3 = rd32(reg + off + 8);
                if (is_bcond(c3) && (c3 & 0xF) == 0x8) {
                    found.push_back(std::make_pair(off, 9));
                    break;
                }
            }
        }
    }
    /* 3) 枚举分发型 (vivo/iQOO, 回退): 标准 bl;cmp#3;b.hi 与直读;cmp#3;b.hi 都没有时,
          找 "adrp; ldr 全局; 随后 ≥3 个同寄存器 cmp wN,#imm" 的分发点 (状态枚举 0/1/2/3).
          这是 switch 型锁定状态检查; 打桩为 mov wN,#0 (强制状态=0), 与全局状态读取共用点.
          复用与 locate_global_state 相同的 switch 判定结构. */
    if (found.empty()) {
        for (u64 off = 4; off + 12 <= len; off += 4) {
            u32 v = rd32(reg + off);
            int rt, rn, imm12, immv;
            bool is_ldr = is_ldr_w_imm(v, &rt, &rn, &imm12) ||
                          is_ldrsw_x_imm(v, &rt, &rn, &imm12);
            if (!is_ldr && !is_mov_w_imm(v, &rt, &immv)) continue;
            if (!is_ldr && immv != 0) continue;   /* 只接受已打桩的 mov wN,#0 */
            /* adrp 目标须等于 ldr 基址(rn) 或已打桩 mov 的值寄存器(rt), 防无关 adrp 误命中 */
            int adrp_rd;
            if (!is_adrp_rd(rd32(reg + off - 4), &adrp_rd)) continue;
            if (adrp_rd != (is_ldr ? rn : rt)) continue;
            int cmps = 0;
            for (int j = 1; j <= 12; j++) {
                u64 a = off + (u64)j * 4;
                if (a + 4 > len) break;
                u32 w = rd32(reg + a);
                int r3, i3;
                if (is_cmp_w_imm(w, &r3, &i3) && r3 == rt) { cmps++; continue; }
                int rt2, rn2, i12;
                if ((is_ldr_w_imm(w, &rt2, &rn2, &i12) || is_ldrsw_x_imm(w, &rt2, &rn2, &i12) ||
                     is_mov_w_imm(w, &rt2, &immv) || is_add_w_imm(w, &rt2, &rn2, &i12)) && rt2 == rt) {
                    cmps = 0; break;
                }
            }
            if (cmps >= 3) { found.push_back(std::make_pair(off, 9)); break; }
        }
    }
}

static void locate_global_state(const u8* reg, size_t len,
                                std::vector<std::pair<u64,int>>& found) {
    for (u64 off = 4; off + 12 <= len; off += 4) {
        u32 v = rd32(reg + off);
        int rt, rn, imm12, immv;
        bool is_ldr = is_ldr_w_imm(v, &rt, &rn, &imm12) ||
                      is_ldrsw_x_imm(v, &rt, &rn, &imm12);
        if (!is_ldr && !is_mov_w_imm(v, &rt, &immv)) continue;
        if (!is_ldr && immv != 0) continue;   /* 只接受已打桩的 mov wN,#0 (镜像已修过) */
        /* adrp 目标须等于 ldr 基址(rn) 或已打桩 mov 的值寄存器(rt), 防无关 adrp 误命中 */
        int adrp_rd;
        if (!is_adrp_rd(rd32(reg + off - 4), &adrp_rd)) continue;
        if (adrp_rd != (is_ldr ? rn : rt)) continue;
        /* A) 标准型: ldr;cmp wN,#3;b.hi (OPPO/小米/真我) */
        int r2, i2;
        if (is_cmp_w_imm(rd32(reg + off + 4), &r2, &i2) && i2 == 3 && r2 == rt) {
            u32 c3 = rd32(reg + off + 8);
            if (is_bcond(c3) && (c3 & 0xF) == 0x8) {
                found.push_back(std::make_pair(off, 1));
                return;
            }
        }
        /* B) switch 型 (vivo/iQOO): ldr 后 ≤12 条内 ≥3 个同寄存器 cmp wN,#imm
           (状态枚举多值分发, 如 verifiedboot green/yellow/orange/red=0/1/2/3)
           若中间出现同寄存器重新定义 (ldr/mov/add), 说明 ldr 结果被覆盖 -> 跳过 */
        int cmps = 0;
        for (int j = 1; j <= 12; j++) {
            u64 a = off + (u64)j * 4;
            if (a + 4 > len) break;   /* 防越界读 (off+12<=len 只保证到 off+12) */
            u32 w = rd32(reg + a);
            int r3, i3;
            if (is_cmp_w_imm(w, &r3, &i3) && r3 == rt) { cmps++; continue; }
            /* 同寄存器被重新定义 (写 rt) */
            int rt2, rn2, i12, imv;
            if ((is_ldr_w_imm(w, &rt2, &rn2, &i12) || is_ldrsw_x_imm(w, &rt2, &rn2, &i12) ||
                 is_mov_w_imm(w, &rt2, &imv) || is_add_w_imm(w, &rt2, &rn2, &i12)) && rt2 == rt) {
                cmps = 0; break;
            }
        }
        if (cmps >= 3) {
            found.push_back(std::make_pair(off, 1));
            return;
        }
    }
}

/* ============ 安全校验类定位器 (老工具 mod3/mod4/mod5/6/8/bl2 策略的通用化) ============
   type 10: rpmb/状态读取打桩 (mod3) — 找调用者特征后打桩 bl 目标函数头
   type 11: csel 条件选择强制 (mod4) — cmp wN,#0; csel xD,xA,xB,eq; mov x0,xR; bl
   type 12: 锁定状态写回校验 (mod5/6/8) — cmp wN,#3; cset wM; str wM,[xK]
   type 14: bl2 安全校验查询 (bl2) — stp x29,x30;add x29,sp;bl;bl;and w0,w0,#1
*/
static void locate_rpmb_read(const u8* reg, size_t len,
                             std::vector<std::pair<u64,int>>& found) {
    /* 调用者特征: mov wN,#1; add xM,sp,#X; str wN,[xM,#X]; bl; ldr wK,[xM,#X]; cmp wJ,#0; cset w0
       -> 打桩 bl 目标函数 (rpmb/状态读取, 直接返回 0) */
    for (u64 off = 4; off + 32 <= len; off += 4) {
        int rn1, imm1;
        if (!is_mov_w_imm(rd32(reg + off), &rn1, &imm1) || imm1 != 1) continue;
        int radd, rnadd, immadd;
        if (!is_add_x_imm(rd32(reg + off + 4), &radd, &rnadd, &immadd)) continue;
        if (rnadd != 31) continue;                    /* add xM,sp,#X */
        int rt2, rn2, i2;
        if (!is_str_w_imm(rd32(reg + off + 8), &rt2, &rn2, &i2)) continue;  /* str wN,[sp/#xM,#X] */
        if (rt2 != rn1 || !(rn2 == 31 || rn2 == radd) || (u32)i2 * 4 != (u32)immadd) continue;
        if (!is_bl(rd32(reg + off + 12))) continue;
        /* bl 后 ≤6 条内: ldr wK,[sp/#xM,#X]; cmp wJ,#0; cset w0 */
        bool found_seq = false;
        for (int j = 1; j <= 6; j++) {
            u64 a = off + 12 + (u64)j * 4;
            if (a + 12 > len) break;
            int rk, rn4, i4;
            if (!is_ldr_w_imm(rd32(reg + a), &rk, &rn4, &i4)) continue;
            if (!(rn4 == 31 || rn4 == radd) || (u32)i4 * 4 != (u32)immadd) continue;
            int rc, ic;
            if (!is_cmp_w_imm(rd32(reg + a + 4), &rc, &ic) || ic != 0) continue;
            int rcs, ccs;
            if (!is_cset_w(rd32(reg + a + 8), &rcs, &ccs) || rcs != 0) continue;
            found_seq = true;
            break;
        }
        if (!found_seq) continue;
        /* 解析 bl 目标函数并打桩 */
        u32 blv = rd32(reg + off + 12);
        u64 tgt = (off + 12) + (sext(blv & 0x3FFFFFF, 26) << 2);
        found.push_back(std::make_pair(tgt, 10));
        return;
    }
}

static void locate_csel_param(const u8* reg, size_t len,
                              std::vector<std::pair<u64,int>>& found) {
    /* cmp wN,#0; [csel D,A,B,eq | 已打桩 mov]; mov x0,xR; bl -> 强制 csel 恒取 xA */
    for (u64 off = 4; off + 16 <= len; off += 4) {
        int rn1, imm1;
        if (!is_cmp_w_imm(rd32(reg + off), &rn1, &imm1) || imm1 != 0) continue;
        u32 v1 = rd32(reg + off + 4);
        int rd, rn, rm, sf;
        bool is_csel = is_csel_x_eq(v1, &rd, &rn, &rm, &sf);
        bool is_done = !is_csel && ((v1 & 0xFFE0FFE0u) == 0xAA0003E0u ||
                                    (v1 & 0xFFE0FFE0u) == 0x2A0003E0u);  /* 已打桩 mov xD,xA / mov wD,wA */
        if (!is_csel && !is_done) continue;
        /* 后一条应为 mov x0,xR (传送类), 再后一条 bl */
        u32 v2 = rd32(reg + off + 8);
        if ((v2 & 0xFFE00000u) != 0xAA000000u) continue;  /* mov x 家族 (保留 sf 位) */
        if ((v2 & 0x1F) != 0) continue;                   /* Rd=x0 */
        if (!is_bl(rd32(reg + off + 12))) continue;
        found.push_back(std::make_pair(off + 4, 11));
        return;
    }
}

static void locate_state_write(const u8* reg, size_t len,
                               std::vector<std::pair<u64,int>>& found) {
    /* 锁定状态写回校验: cmp wN,#3; cset wM; str wM,[xK,#imm] -> 打桩函数头
       (mod568_stub: mov w8,#1; str w8,[x0]; mov w0,#0; ret) */
    for (u64 off = 4; off + 12 <= len; off += 4) {
        int rn1, imm1;
        if (!is_cmp_w_imm(rd32(reg + off), &rn1, &imm1) || imm1 != 3) continue;
        int rd, cond;
        if (!is_cset_w(rd32(reg + off + 4), &rd, &cond)) continue;
        u32 v3 = rd32(reg + off + 8);
        if ((v3 & 0xFFC00000u) != 0xB9000000u) continue;  /* str w 立即数 */
        if (((v3 >> 5) & 0x1F) == 31 || (v3 & 0x1F) != (u32)rd) continue;  /* str wM,[xK] */
        u64 fn = find_function_start(reg, len, off);
        if (fn != (u64)-1) {
            /* 优先打外层 paciasp 入口 (PAC 函数头, 覆盖其后的 stp 帧建立), 与已知可用镜像一致 */
            if (fn >= 4 && is_pacia(rd32(reg + fn - 4))) fn -= 4;
            found.push_back(std::make_pair(fn, 12));
            return;
        }
    }
}

static void locate_bl2_sec(const u8* reg, size_t len,
                           std::vector<std::pair<u64,int>>& found) {
    /* bl2 安全校验查询: stp x29,x30,[sp,#-0x10]!; add x29,sp,#0; bl; bl; and w0,w0,#1 */
    for (u64 off = 0; off + 20 <= len; off += 4) {
        int imm;
        u32 v0 = rd32(reg + off);
        if (!is_stp_x29x30_pre(v0, &imm) || imm != -0x10) continue;
        int rd2, rn2, i2;
        u32 v1 = rd32(reg + off + 4);
        if (!is_add_x_imm(v1, &rd2, &rn2, &i2) || rn2 != 31 || i2 != 0) continue;
        if (!is_bl(rd32(reg + off + 8))) continue;
        if (!is_bl(rd32(reg + off + 12))) continue;
        if (!is_and_w0_w0_imm(rd32(reg + off + 16))) continue;
        /* 打桩第 2 个 bl 的目标 (真正的安全校验函数), 而不是模式起点(调用者),
           与已知可用镜像的 bl2 修补位置一致 */
        u32 blv = rd32(reg + off + 12);
        u64 tgt = (off + 12) + (sext(blv & 0x3FFFFFF, 26) << 2);
        found.push_back(std::make_pair(tgt, 14));
        return;
    }
}

static void locate_ufs_swp(const u8* reg, size_t len,
                           std::vector<std::pair<u64,int>>& found) {
    auto add = [&](u64 a, int t) {
        for (size_t i = 0; i < found.size(); i++)
            if (found[i].first == a) return;
        found.push_back(std::make_pair(a, t));
    };
    /* A) ioctl 参数清零 (v2/老工具 mod7): mov w0,#0x120; [ldr w2,[xN,#imm] | mov w2,#0(已打桩)]; movk w0,#0xc200,lsl16
          -> 打 ldr w2 为 mov w2,#0 (ioctl 参数 w2 清零, 确保写保护命令以宽松模式执行) */
    for (u64 off = 4; off + 8 <= len; off += 4) {
        int rd, imm;
        if (!is_mov_w_imm(rd32(reg + off), &rd, &imm) || imm != 0x120 || rd != 0) continue;
        for (int j = 1; j <= 8; j++) {
            int r2, im2;
            if (!is_movk_w(rd32(reg + off + (u64)j * 4), &r2, &im2) || (u32)im2 != 0xc2000000u || r2 != 0) continue;
            for (int k = 1; k < j; k++) {
                u64 a = off + (u64)k * 4;
                int rt, rn, i12;
                if ((is_ldr_w_imm(rd32(reg + a), &rt, &rn, &i12) && rt == 2) ||
                    rd32(reg + a) == 0x52800002u) {   /* ldr w2 或已打桩 mov w2,#0 */
                    add(a, 15);
                    break;
                }
            }
            /* 老工具 mod10: 同一 ioctl 区域的 ldrsw x1,[sp,#..] -> mov w1,#1 (与已知可用一致) */
            for (int k = 1; k < j; k++) {
                u64 a = off + (u64)k * 4;
                int rt, rn, i12;
                if (is_ldrsw_x_imm(rd32(reg + a), &rt, &rn, &i12) && rt == 1 && rn == 31)
                    add(a, 5);
            }
            break;
        }
    }
    /* B1) 0xc200120 ioctl 门控变体 (500 固件): ldr wN,[sp,#X]; cbz wN 出现在
          mov w0,#0x120 ... movk w0,#0xc200,lsl16 之前 → 打 ldr 为 mov wN,#1 (门控恒通过) */
    for (u64 off = 4; off + 8 <= len; off += 4) {
        int rd, imm;
        if (!is_mov_w_imm(rd32(reg + off), &rd, &imm) || imm != 0x120 || rd != 0) continue;
        u64 movk_at = 0;
        for (int j = 1; j <= 6; j++) {
            int r2, im2;
            if (is_movk_w(rd32(reg + off + (u64)j * 4), &r2, &im2) && (u32)im2 == 0xc2000000u && r2 == 0)
                { movk_at = off + (u64)j * 4; break; }
        }
        if (movk_at == 0) continue;
        for (u64 k = 1; k <= 12; k++) {
            u64 a = movk_at - k * 4;
            if (a + 8 > len || a < 4) break;
            u32 vv = rd32(reg + a);
            int rt = 0, rn, i12, rd2, im2;
            bool isldr = is_ldr_w_imm(vv, &rt, &rn, &i12) && rn == 31;
            bool ismov1 = !isldr && is_mov_w_imm(vv, &rd2, &im2) && im2 == 1;
            if (ismov1) rt = rd2;
            if (!isldr && !ismov1) continue;
            u32 c = rd32(reg + a + 4);
            if ((c & 0x7F000000u) == 0x34000000u && (c & 0x1F) == (u32)rt) add(a, 5);
        }
    }
    /* B2) 0xc200120 ioctl 门控: mov w0,#0x120; movk w0,#0xc200,lsl16 后的 ldr sp+..;cbz */
    for (u64 off = 0; off + 8 <= len; off += 4) {
        int rd, imm;
        if (!is_mov_w_imm(rd32(reg + off), &rd, &imm) || imm != 0x120 || rd != 0) continue;
        int r2, im2;
        if (!is_movk_w(rd32(reg + off + 4), &r2, &im2) || (u32)im2 != 0xc2000000u || r2 != 0) continue;
        for (int j = 2; j <= 16; j++) {
            u64 a = off + (u64)j * 4;
            if (a + 8 > len) break;
            u32 v = rd32(reg + a);
            int rt = 0, rn, i12, rd2, im2;
            bool isldr = is_ldr_w_imm(v, &rt, &rn, &i12) && rn == 31;
            bool ismov1 = !isldr && is_mov_w_imm(v, &rd2, &im2) && im2 == 1;
            if (ismov1) rt = rd2;
            if (!isldr && !ismov1) continue;
            u32 c = rd32(reg + a + 4);
            if ((c & 0x7F000000u) == 0x34000000u && (c & 0x1F) == (u32)rt) add(a, 5);
        }
    }
    /* 注: 不再打桩 set_write_protect 函数本身 (已知可用镜像不打它, 避免过多修补) */
}

/* 扫描"全局状态装载型 state==2 门".
   uncond_done=false: 找"待补"形态 (cmp wN,#2; b.cond, 非 eq), 供修补;
   uncond_done=true : 找"已补"形态 (cmp wN,#2; 无条件 b) —— 前次修补把 b.cond
                      换成同目标 b 后的样子, 用于重复运行时报"已存在"而非误报未找到.
   安全门槛两种形态一致: (1) wN 来自全局装载 (排除 GPT 访问器/字节反转的入参/长度
   边界判断); (2) 前 ≤6 条有同寄存器 cmp wN,#1 (确认为多态 boot-state 分发);
   (3) 分支后是 PAC 保护叶块 (hdr_after) 或有绿色跳转. 输出为分支所在地址 (off+4). */
static void scan_orange_candidates(const u8* reg, size_t len, bool uncond_done,
                                   std::vector<u64>& out) {
    auto from_global_state = [&](u64 off, int rn) -> bool {
        for (int k = 1; k <= 8 && off >= (u64)k * 4; k++) {
            u32 w = rd32(reg + off - (u64)k * 4);
            int rt, rn2, imm12;
            bool is_ldr = false;
            if (is_ldr_w_imm(w, &rt, &rn2, &imm12) && rt == rn) is_ldr = true;
            else if (is_ldrsw_x_imm(w, &rt, &rn2, &imm12) && rt == rn) is_ldr = true;
            if (!is_ldr) continue;
            /* 若该 ldr 已在镜像最前几字节(其 adrp 必然在镜像外), 视为非全局型, 防越界读 reg-4 */
            if (off < (u64)(k + 1) * 4) break;
            u32 a = rd32(reg + off - (u64)(k + 1) * 4);
            int ard;
            if (is_adrp_rd(a, &ard) && ard == rn2) return true;
            break;   /* 找到同寄存器装载但非全局, 不再向前找 */
        }
        return false;
    };

    for (u64 off = 4; off + 12 <= len; off += 4) {
        int rn, imm;
        if (!is_cmp_w_imm(rd32(reg + off), &rn, &imm) || imm != 2) continue;
        u32 b = rd32(reg + off + 4);
        if (uncond_done) {
            if (!is_b(b)) continue;                        /* 已补形态: cmp 后是无条件 b */
        } else {
            if (!is_bcond(b) || (b & 0xF) == 0) continue;  /* 待补形态: b.cond (非 eq) */
        }
        if (!from_global_state(off, rn)) continue;
        int im2;
        bool hdr_after = is_pacia(rd32(reg + off + 8)) ||
                         is_stp_x29x30_pre(rd32(reg + off + 8), &im2);
        bool has_cmp1 = false, has_green_b = false;
        for (int k = 1; k <= 6 && off >= (u64)k * 4; k++) {
            int r1, i1;
            u32 w = rd32(reg + off - (u64)k * 4);
            if (is_cmp_w_imm(w, &r1, &i1) && i1 == 1 && r1 == rn) has_cmp1 = true;
            if (is_b(w)) has_green_b = true;
        }
        if (has_cmp1 && (hdr_after || has_green_b)) out.push_back(off + 4);
    }
}

static void locate_orange(const u8* reg, size_t len,
                          std::vector<std::pair<u64,int>>& found) {
    /* 去黄字(通用化): 找 orange(2) 分发点 "cmp wN,#2; b.cond", 把条件分支改成
       无条件 b(同目标), 绕过 orange 警告函数, 与已知可用镜像语义一致.
       语义: state==2 视为非橙直接走返回, 只去掉画黄字与等待, 开机链路照常,
       state==3 断电保护不动. 全量收集逐一修补; 无全局装载型门时一律不补
       (宁可报告未找到, 不打错点), 保证第一遍正确、重复运行幂等、不误伤. */
    std::vector<u64> offs;
    scan_orange_candidates(reg, len, false, offs);
    for (size_t i = 0; i < offs.size(); i++)
        found.push_back(std::make_pair(offs[i], 8));   /* 指向 b.cond */
}

static void locate_verifiedboot(const u8* reg, size_t len,
                               std::vector<std::pair<u64,int>>& found) {
    /* 1) 字符串引用模式 (多候选 + 模糊) */
    const char* needles[] = { "verifiedbootstate", "verified_boot_state", "vb_state" };
    u64 fn = find_fn_by_string(reg, len, needles, 3);
    if (fn > 0) { found.push_back(std::make_pair(fn, 7)); return; }
    /* 2) 跳表模式: cmp wN,#3; b.hi; 随后查表加载
          - 函数指针表: ldr xA,[xB,xC,lsl#3]  (0xF8600800)
          - 32位偏移表: ldrsw xA,[xB,xC,lsl#2] (0xB8800800)
          先收集所有候选, 优先选"cmp 之前 ≤12 条内存在同寄存器状态读取 ldr/ldrsw"的
          (真分发), 防止把函数中部的无关 cmp#3;b.hi+索引加载误当成 verifiedboot
          返回状态读取点 (cmp 之前的 ldr; 可能已被"全局状态读取"打过桩) */
    u64 best_ldr = 0, best_fb = 0;
    for (u64 off = 4; off + 16 <= len; off += 4) {
        int rn, imm;
        if (!is_cmp_w_imm(rd32(reg + off), &rn, &imm) || imm != 3) continue;
        u32 c3 = rd32(reg + off + 4);
        if (!is_bcond(c3) || (c3 & 0xF) != 0x8) continue;
        for (int j = 3; j <= 8; j++) {
            u32 v = rd32(reg + off + (u64)j * 4);
            /* 寄存器索引加载族: 掩码 0xFFC00C00 保留 bits 31:22 + 11:10 (忽略 option/S/Rm)
               - LDR X: 掩码后 0xF8400800 (V=1)
               - LDRSW X: 掩码后 0xB8800800 (兼容 lsl#2 / sxtw 等 option 变体) */
            if ((v & 0xFFC00C00u) == 0xF8400800u ||
                (v & 0xFFC00C00u) == 0xB8800800u) {
                if (off >= 8) {
                    /* 往前找状态读取: cmp 之前 ≤12 条内, 同 wN 的 ldr wN / ldrsw xN
                       (若已被"全局状态读取/锁定状态检查"打成 mov wN,#0 也接受) */
                    u64 ldr_at = 0;
                    for (u64 k = 1; k <= 12; k++) {
                        u64 a = off - k * 4;
                        if (a >= len) break;
                        int rtt, rnn, i12;
                        u32 lv = rd32(reg + a);
                        if (is_ldr_w_imm(lv, &rtt, &rnn, &i12) && rtt == rn) { ldr_at = a; break; }
                        if (is_ldrsw_x_imm(lv, &rtt, &rnn, &i12) && rtt == rn) { ldr_at = a; break; }
                        int imv;
                        if (is_mov_w_imm(lv, &rtt, &imv) && imv == 0 && rtt == rn) { ldr_at = a; break; }
                    }
                    if (ldr_at > 0) { if (best_ldr == 0) best_ldr = ldr_at; }
                    else if (best_fb == 0) best_fb = off - 4;
                }
                break;
            }
        }
    }
    if (best_ldr > 0) found.push_back(std::make_pair(best_ldr, 7));
    else if (best_fb > 0) found.push_back(std::make_pair(best_fb, 7));
}

/* ==================== 文件/控制台 ==================== */
#ifdef _WIN32
static FILE* open_file(const char* path, const char* mode) {
    wchar_t wpath[4096], wmode[16];
    if (MultiByteToWideChar(CP_UTF8, 0, path, -1, wpath, 4096) == 0) return nullptr;
    if (MultiByteToWideChar(CP_UTF8, 0, mode, -1, wmode, 16) == 0) return nullptr;
    return _wfopen(wpath, wmode);
}
#else
static FILE* open_file(const char* path, const char* mode) { return fopen(path, mode); }
#endif

static bool read_file(const std::string& path, std::vector<u8>& out) {
    FILE* f = open_file(path.c_str(), "rb");
    if (!f) return false;
#ifdef _WIN32
    _fseeki64(f, 0, SEEK_END); __int64 sz = _ftelli64(f); _fseeki64(f, 0, SEEK_SET);
#else
    fseeko(f, 0, SEEK_END); off_t sz = ftello(f); fseeko(f, 0, SEEK_SET);
#endif
    if (sz <= 0) { fclose(f); return false; }
    out.resize((size_t)sz);
    size_t rd = fread(out.data(), 1, (size_t)sz, f);
    fclose(f);
    return rd == (size_t)sz;
}
static bool write_file(const std::string& path, const std::vector<u8>& data) {
    FILE* f = open_file(path.c_str(), "wb");
    if (!f) return false;
    size_t wr = fwrite(data.data(), 1, data.size(), f);
    fclose(f);
    return wr == data.size();
}
static std::string make_out_name(const std::string& in) {
    size_t dot = in.find_last_of('.');
    size_t slash = in.find_last_of("/\\");
    if (dot != std::string::npos && (slash == std::string::npos || dot > slash))
        return in.substr(0, dot) + "_patched" + in.substr(dot);
    return in + "_patched";
}
static std::string trim(const std::string& s) {
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == std::string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b - a + 1);
}
static void init_console() {
#ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCP(CP_UTF8);
#endif
}
static void press_enter() {
    printf("\n按回车键退出...");
    fflush(stdout);
    int c;
    do { c = getchar(); } while (c != '\n' && c != EOF);
}

/* 询问修补类别: 返回位掩码 (bit0=伪装回锁, bit1=去黄字, bit2=去写保护).
   bl2 安全校验(免授权深刷)不再作为可选类别, 无条件自动执行, 与旧版一致. */
static int ask_categories() {
    printf("\n请选择要修补的类别 (多个用逗号如 1,3; 回车=全部):\n");
    printf("  [1] 伪装回锁 : 强制显示已锁\n");
    printf("  [2] 去黄字警告 : 去掉 Orange 警告\n");
    printf("  [3] 去写保护 : 绕过 UFS 写保护\n");
    for (int attempt = 0; attempt < 3; attempt++) {
        printf("请选择: ");
        fflush(stdout);
        char line[64];
        if (!fgets(line, sizeof(line), stdin)) return 15;
        std::string s = trim(line);
        if (s.empty()) return 15;   /* 回车 = 全部 */
        int m = 0;
        bool bad_digit = false;
        for (size_t i = 0; i < s.size(); i++) {
            char c = s[i];
            if (c == '1') m |= 1;
            else if (c == '2') m |= 2;
            else if (c == '3') m |= 8;
            else if (c >= '4' && c <= '9') bad_digit = true;   /* 不存在的选项 4-9 */
        }
        if (m != 0) return m;
        if (attempt < 2) {
            printf("  无法识别 (只支持 1-3 或其组合, 如 1,3)。%s\n",
                   bad_digit ? "注意没有选项 4/5..., 请重新输入:" : "请重新输入:");
        } else {
            printf("  多次无法识别, 已按全部处理。\n");
            return 15;
        }
    }
    return 15;
}

/* 处理单个文件: 读取 -> 识别分区 -> 按 cats 类别修补 -> 报告 -> 写输出.
   返回 0=成功(写出), 1=失败/无需写出; 计数经出参返回. */
static int process_file(const std::string& path, int cats,
                        int* pok, int* palready, int* pskip, int* pfail) {
    std::vector<u8> img;
    if (!read_file(path, img)) { printf("错误: 无法读取文件: %s\n", path.c_str()); return 1; }

    /* ---- 自动识别分区 ---- */
    Partition lk, bl2;
    bool has_lk = find_partition(img, "lk", lk);
    bool has_bl2 = find_partition(img, "bl2_ext", bl2);
    printf("\n[分区识别] %s\n", has_lk ? "MTK 容器 (含 lk 分区)" : "裸镜像 (按整体处理)");
    if (has_lk)  printf("  lk:      偏移 %#llx  大小 %#llx\n", (unsigned long long)lk.data_off, (unsigned long long)lk.data_len);
    if (has_bl2) printf("  bl2_ext: 偏移 %#llx  大小 %#llx\n", (unsigned long long)bl2.data_off, (unsigned long long)bl2.data_len);

    std::vector<PatchInfo> stats;

    /* ---- LK 层语义修补 ---- */
    u8* lk_data = has_lk ? img.data() + lk.data_off : img.data();
    size_t lk_len = has_lk ? (size_t)lk.data_len : img.size();
    u64 lk_base = has_lk ? lk.data_off : 0;

    {
        std::vector<std::pair<u64,int>> hits;

        /* 类别1: 伪装回锁 */
        if (cats & 1) {
            /* 1) 全局状态读取 (先打桩, 锁定状态/引导分发可能引用同一个状态点) */
            hits.clear();
            locate_global_state(lk_data, lk_len, hits);
            if (hits.empty()) note_fail(stats, "全局状态读取", "未找到 adrp;ldr全局;cmp wN,#3;b.hi 结构");
            for (size_t h = 0; h < hits.size(); h++) {
                int rr = patch_state_zero(lk_data, lk_len, hits[h].first);
                note_result(stats, "全局状态读取", "ldr 全局;cmp wN,#3;b.hi -> mov wN,#0",
                            lk_base + hits[h].first, rr);
            }

            /* 2) 锁定状态检查 */
            hits.clear();
            locate_lock_state(lk_data, lk_len, hits);
            if (hits.empty()) note_fail(stats, "锁定状态检查", "未找到 bl;cmp 或 全局直读;cmp wN,#3;b.hi 结构");
            for (size_t h = 0; h < hits.size() && h < 2; h++) {
                u64 at = hits[h].first;
                int rr;
                if (hits[h].second == 9) {
                    /* 直接读全局型: 状态读取 ldr/ldrsw -> mov wN,#0 (强制状态=0)
                       (若已被"全局状态读取"打成 mov wN,#0, 解码出寄存器报告已存在) */
                    rr = patch_state_zero(lk_data, lk_len, at);
                    note_result(stats, "锁定状态检查", "全局状态读/枚举分发 -> mov wN,#0 (强制状态=0)",
                                lk_base + at, rr);
                } else {
                    rr = (rd32(lk_data + at) == 0x52800000u) ? PR_ALREADY : PR_OK;
                    if (rr == PR_OK) wr32(lk_data + at, 0x52800000u);
                    note_result(stats, "锁定状态检查", "bl;cmp w0,#3;b.hi -> mov w0,#0",
                                lk_base + at, rr);
                }
                if (rr == PR_OK) break;
            }

            /* 3) verifiedbootstate 分发 */
            hits.clear();
            locate_verifiedboot(lk_data, lk_len, hits);
            if (hits.empty()) note_fail(stats, "引导状态分发", "未找到 verifiedbootstate 引用/跳表");
            for (size_t h = 0; h < hits.size(); h++) {
                u64 at = hits[h].first;
                int rr;
                if (hits[h].second == 7 && state_read_reg(rd32(lk_data + at)) >= 0) {
                    /* 跳表模式: 状态读取 ldr/ldrsw -> mov wN,#0 (强制查表[0]=green)
                       (若已被"全局状态读取"打成 mov wN,#0, 报告已存在) */
                    rr = patch_state_zero(lk_data, lk_len, at);
                    note_result(stats, "引导状态分发", "verifiedboot 跳表 -> mov wN,#0 (强制绿色)",
                                lk_base + at, rr);
                } else if (hits[h].second == 7 && (rd32(lk_data + at) & 0x7F800000u) == 0x52800000u) {
                    /* 状态读取位置已是 mov -> 视为已处理 */
                    note_result(stats, "引导状态分发", "verifiedboot 跳表状态已置 0 (与全局状态读取同点)",
                                lk_base + at, PR_ALREADY);
                } else {
                    /* 字符串引用模式: 打桩函数 */
                    rr = stub_function(lk_data, lk_len, at);
                    note_result(stats, "引导状态分发", "verifiedbootstate 引用函数 -> 强制绿色",
                                lk_base + at, rr);
                }
                break;
            }

            /* 4) rpmb/状态读取函数打桩 (mod3) */
            hits.clear();
            locate_rpmb_read(lk_data, lk_len, hits);
            if (hits.empty()) note_result(stats, "rpmb 状态读取", "此固件无该结构 (跳过)", 0, PR_SKIP);
            for (size_t h = 0; h < hits.size(); h++) {
                int rr = stub_function(lk_data, lk_len, hits[h].first);
                note_result(stats, "rpmb 状态读取", "rpmb/状态读取函数 -> 返回0",
                            lk_base + hits[h].first, rr);
                break;
            }

            /* 5) csel 条件选择强制 (mod4) */
            hits.clear();
            locate_csel_param(lk_data, lk_len, hits);
            if (hits.empty()) note_result(stats, "条件选择", "此固件无该结构 (跳过)", 0, PR_SKIP);
            for (size_t h = 0; h < hits.size(); h++) {
                u64 at = hits[h].first;
                int rdd, rnn, rmm, sff;
                u32 cv = rd32(lk_data + at);
                int rr;
                if (is_csel_x_eq(cv, &rdd, &rnn, &rmm, &sff)) {
                    /* 按 csel 宽度生成对应 mov: 64位 -> mov xD,xA; 32位 -> mov wD,wA */
                    u32 rep = ((sff ? 0xAA0003E0u : 0x2A0003E0u) |
                               ((u32)rnn << 16) | (u32)rdd);
                    rr = (cv == rep) ? PR_ALREADY : PR_OK;
                    if (rr == PR_OK) wr32(lk_data + at, rep);
                    note_result(stats, "条件选择",
                                sff ? "csel xD,xA,xB,eq -> mov xD,xA (恒取 xA)"
                                    : "csel wD,wA,wB,eq -> mov wD,wA (恒取 wA)",
                                lk_base + at, rr);
                } else if ((cv & 0xFFE0FFE0u) == 0xAA0003E0u ||
                           (cv & 0xFFE0FFE0u) == 0x2A0003E0u) {
                    /* 已被老工具打成 mov xD,xA / mov wD,wA -> 已存在 */
                    note_result(stats, "条件选择", "csel 已强制为 mov (已存在)",
                                lk_base + at, PR_ALREADY);
                } else {
                    note_fail(stats, "条件选择", "定位点指令异常");
                }
                break;
            }

            /* 6) 锁定状态写回校验 (mod5/6/8) */
            hits.clear();
            locate_state_write(lk_data, lk_len, hits);
            if (hits.empty()) note_result(stats, "状态写回校验", "此固件无该结构 (跳过)", 0, PR_SKIP);
            for (size_t h = 0; h < hits.size(); h++) {
                u64 at = hits[h].first;
                int rr;
                static const u32 stub4[4] = { 0x52800028u, 0xB9000008u, 0x52800000u, 0xD65F03C0u };
                if (at + 16 > lk_len) { rr = PR_FAIL; }
                else if (rd32(lk_data + at) == stub4[0] && rd32(lk_data + at + 4) == stub4[1] &&
                         rd32(lk_data + at + 8) == stub4[2] && rd32(lk_data + at + 12) == stub4[3]) {
                    rr = PR_ALREADY;
                } else {
                    /* 打桩需函数头前 4 条可替换 (stp/pacia 开头即可) */
                    u32 i0 = rd32(lk_data + at);
                    int im;
                    if (!is_stp_x29x30_pre(i0, &im) && !is_pacia(i0)) rr = PR_FAIL;
                    else {
                        for (int k = 0; k < 4; k++) wr32(lk_data + at + (u64)k * 4, stub4[k]);
                        rr = PR_OK;
                    }
                }
                note_result(stats, "状态写回校验", "锁定状态写回 -> mov w8,#1;str [x0];mov w0,#0;ret",
                            lk_base + at, rr);
                break;
            }
        }
        if (cats & 2) {
            hits.clear();
            locate_orange(lk_data, lk_len, hits);
            if (hits.empty()) {
                /* 没有"待补"的 b.cond 门: 先看是否前次已把分支改成无条件 b (已补),
                   避免把"已打过黄字补丁"误报成"未找到" */
                std::vector<u64> done;
                scan_orange_candidates(lk_data, lk_len, true, done);
                if (!done.empty()) {
                    for (size_t d = 0; d < done.size(); d++)
                        note_result(stats, "Orange 警告",
                                    "orange 分支已是无条件跳过 (前次已补)",
                                    lk_base + done[d], PR_ALREADY);
                } else {
                    /* 无 "Orange State" 门 (小米/红米系用 verifiedboot 状态分发控制警告):
                       若引导状态分发已强制绿色, 警告自然不触发 -> 跳过 */
                    bool vb_ok = false;
                    for (size_t s = 0; s < stats.size(); s++)
                        if (stats[s].name == "引导状态分发" && stats[s].result != PR_FAIL)
                            vb_ok = true;
                    if (vb_ok) {
                        note_result(stats, "Orange 警告", "无 Orange 门 (由引导状态强制绿色覆盖)",
                                    0, PR_SKIP);
                    } else {
                        note_fail(stats, "Orange 警告",
                                  "未找到全局状态==2 的黄字门 (小米/红米系请连同[1]伪装回锁, 由强制绿色覆盖)");
                    }
                }
            }
            for (size_t h = 0; h < hits.size(); h++) {
                u64 at = hits[h].first;
                u32 bv = rd32(lk_data + at);
                if (!is_bcond(bv)) { note_fail(stats, "Orange 警告", "定位点非条件分支"); break; }
                /* 计算 b.cond 目标 (imm19 在 bits[23:5]), 生成无条件 b (同目标, 绕过 orange 警告) */
                int64_t disp = sext((bv >> 5) & 0x7FFFF, 19);
                u64 target = at + (disp << 2);
                u32 repl = 0x14000000u | (u32)(((target - at) >> 2) & 0x03FFFFFF);
                int rr = (rd32(lk_data + at) == repl) ? PR_ALREADY : PR_OK;
                if (rr == PR_OK) wr32(lk_data + at, repl);
                note_result(stats, "Orange 警告", "orange(2) 分发分支 -> 无条件跳过警告",
                            lk_base + at, rr);
                /* 通用化: 全量命中逐一修补, 不再只打第一个 */
            }
        }

        /* 类别4: 读写保护 (UFS-SWP 旁路) */
        if (cats & 8) {
            hits.clear();
            locate_ufs_swp(lk_data, lk_len, hits);
            if (hits.empty()) note_fail(stats, "UFS 写保护门控", "未找到 0xc200120 ioctl 门控 / SWP 函数");
            for (size_t h = 0; h < hits.size(); h++) {
                u64 at = hits[h].first;
                int rr;
                if (hits[h].second == 8) {
                    /* set_write_protect / rpmb_ufs_set_wp -> 打桩返回 0 (旁路写保护) */
                    rr = stub_function(lk_data, lk_len, at);
                    note_result(stats, "UFS 写保护门控", "set_write_protect -> 返回0 (旁路写保护)",
                                lk_base + at, rr);
                } else if (hits[h].second == 15) {
                    /* ioctl 参数 w2 清零 (mov w2,#0): 确保 0xc200120 写保护命令以宽松模式执行 */
                    u32 rep = 0x52800002u;  /* mov w2,#0 */
                    rr = (rd32(lk_data + at) == rep) ? PR_ALREADY : PR_OK;
                    if (rr == PR_OK) wr32(lk_data + at, rep);
                    note_result(stats, "UFS 写保护门控", "ioctl 参数 ldr w2 -> mov w2,#0",
                                lk_base + at, rr);
                } else {
                    int rt = 0, rn, imm12, immv;
                    u32 lv = rd32(lk_data + at);
                    if (!is_ldr_w_imm(lv, &rt, &rn, &imm12))
                        if (!is_ldrsw_x_imm(lv, &rt, &rn, &imm12))
                            is_mov_w_imm(lv, &rt, &immv);  /* 已打桩 mov wN,#1 */
                    u32 rep = 0x52800020u | (u32)rt;  /* mov wN,#1 (门控恒通过) */
                    rr = (lv == rep) ? PR_ALREADY : PR_OK;
                    if (rr == PR_OK) wr32(lk_data + at, rep);
                    note_result(stats, "UFS 写保护门控", "ldr wN,[sp,#..];cbz -> mov wN,#1",
                                lk_base + at, rr);
                }
            }
        }
    }

    /* ---- bl2_ext 层语义修补 (免授权深刷: bl2 安全校验, 无条件自动执行, 与旧版一致) ---- */
    if (has_bl2) {
        u8* bl2_data = img.data() + bl2.data_off;
        size_t bl2_len = (size_t)bl2.data_len;
        u64 bl2_base = bl2.data_off;
        std::vector<std::pair<u64,int>> hits;

        /* 免授权深刷仅做 bl2 安全校验 (与已知可用镜像一致, 不做 img_auth/SBC 额外打桩) */

        /* bl2 安全校验查询 (老工具 bl2 策略) */
        hits.clear();
        locate_bl2_sec(bl2_data, bl2_len, hits);
        if (hits.empty()) note_result(stats, "bl2 安全校验", "此固件无该结构 (跳过)", 0, PR_SKIP);
        for (size_t h = 0; h < hits.size(); h++) {
            int rr = stub_function(bl2_data, bl2_len, hits[h].first);
            note_result(stats, "bl2 安全校验", "安全校验查询函数 -> 返回0",
                        bl2_base + hits[h].first, rr);
            break;
        }
    } else {
        note_result(stats, "免授权深刷", "镜像不含 bl2_ext 分区 (跳过)", 0, PR_SKIP);
    }

    /* ---- 报告 ---- */
    int ok = 0, already = 0, skip = 0, fail = 0;
    std::string fails;
    for (size_t i = 0; i < stats.size(); i++) {
        if (stats[i].result == PR_OK) ok++;
        else if (stats[i].result == PR_ALREADY) already++;
        else if (stats[i].result == PR_SKIP) skip++;
        else { fail++; if (!fails.empty()) fails += ", "; fails += stats[i].name; }
    }
    printf("\n==== 修补报告 ====\n");
    for (size_t i = 0; i < stats.size(); i++) {
        const char* st = stats[i].result == PR_OK ? "已修补" :
                         stats[i].result == PR_ALREADY ? "已存在" :
                         stats[i].result == PR_SKIP ? "跳过" : "失败";
        printf("  [%s] %-16s @ %#llx  %s\n", st, stats[i].name.c_str(),
               (unsigned long long)stats[i].at, stats[i].desc.c_str());
    }
    printf("成功 %d, 已存在 %d, 跳过 %d, 失败 %d\n", ok, already, skip, fail);
    if (fail > 0) printf("失败点: %s\n", fails.c_str());

    /* 出参必须在两条返回路径都写 (ok==0 时也要回传计数给批量汇总) */
    if (pok) *pok = ok;
    if (palready) *palready = already;
    if (pskip) *pskip = skip;
    if (pfail) *pfail = fail;

    if (ok == 0) {
        if (already > 0) printf("\n镜像已修补过, 无需重复修补。\n");
        else printf("\n未找到可修补的特征 (可能是不支持的镜像)。\n");
        return 1;
    }

    std::string out = make_out_name(path);
    if (!write_file(out, img)) {
        printf("\n错误: 无法写入输出文件: %s\n", out.c_str());
        return 1;
    }
    printf("输出文件: %s\n", out.c_str());
    return 0;
}

/* ---- 批量处理: 依次处理每个文件, 汇总 ---- */
static int run_batch(const std::vector<std::string>& paths, int cats) {
    int tok = 0, talready = 0, tskip = 0, tfail = 0, written = 0, nowrite = 0;
    for (size_t i = 0; i < paths.size(); i++) {
        printf("\n==================== [%u/%u] %s ====================\n",
               (unsigned)(i + 1), (unsigned)paths.size(), paths[i].c_str());
        int ok = 0, already = 0, skip = 0, fail = 0;
        if (process_file(paths[i], cats, &ok, &already, &skip, &fail) == 0) written++;
        else nowrite++;
        tok += ok; talready += already; tskip += skip; tfail += fail;
    }
    printf("\n============================================================\n");
    printf(" 批量完成: 文件 %u, 成功 %d, 已存在 %d, 跳过 %d, 失败 %d\n",
           (unsigned)paths.size(), tok, talready, tskip, tfail);
    printf(" 已生成输出 %u 个, 未生成 %u 个\n", written, nowrite);
    printf("============================================================\n");
    return tfail == 0 ? 0 : 1;
}

/* ---- 入口: 有命令行参数 = 批量(拖拽), 无参数 = 交互输入 ---- */
static int entry_point(std::vector<std::string>& paths) {
    init_console();
    printf("============================================================\n");
    printf(" 通用伪回锁 + 免授权深刷修补工具 (通用版, 动态分析)\n");
    printf(" 不依赖具体固件: 按 AArch64 指令语义自动定位修补点\n");
    printf(" 用法: 把镜像文件拖到本程序上可批量修补, 或直接输入路径\n");
    printf(" QQ群: 2167063739\n");
    printf("============================================================\n");
    for (size_t i = 0; i < paths.size(); i++) {
        std::string& p = paths[i];
        if (p.size() >= 2 && p.front() == '"' && p.back() == '"')
            p = p.substr(1, p.size() - 2);
    }
    if (paths.empty()) {
        printf("请输入文件路径: ");
        fflush(stdout);
        char buf[4096];
        if (!fgets(buf, sizeof(buf), stdin)) { press_enter(); return 1; }
        std::string path = trim(buf);
        if (path.size() >= 2 && path.front() == '"' && path.back() == '"')
            path = path.substr(1, path.size() - 2);
        if (path.empty()) { printf("错误: 未输入文件路径\n"); press_enter(); return 1; }
        paths.push_back(path);
    } else {
        printf("批量模式: %u 个文件\n", (unsigned)paths.size());
        for (size_t i = 0; i < paths.size(); i++)
            printf("  [%u] %s\n", (unsigned)(i + 1), paths[i].c_str());
    }

    int cats = ask_categories();
    printf("已选类别: %s%s%s\n", (cats & 1) ? "伪装回锁 " : "",
           (cats & 2) ? "去黄字 " : "", (cats & 8) ? "去写保护" : "");
    printf("bl2 安全校验(免授权深刷): 自动执行\n");
    int rc = run_batch(paths, cats);
    press_enter();
    return rc;
}

#ifdef _WIN32
int wmain(int argc, wchar_t** argv) {
    std::vector<std::string> paths;
    for (int i = 1; i < argc; i++) {
        char buf[4096];
        if (WideCharToMultiByte(CP_UTF8, 0, argv[i], -1, buf, (int)sizeof(buf), NULL, NULL) > 0)
            paths.push_back(buf);
    }
    return entry_point(paths);
}
#else
int main(int argc, char** argv) {
    std::vector<std::string> paths;
    for (int i = 1; i < argc; i++) paths.push_back(argv[i]);
    return entry_point(paths);
}
#endif
