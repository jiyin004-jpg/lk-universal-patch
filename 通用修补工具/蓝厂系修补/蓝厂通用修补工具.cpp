/* ============================================================
  蓝厂(vivo/iQOO)通用 LK 修补工具 (通用版)
  原则: 在 MTK 容器链内自动推导打桩; 每个被改动的镜像(含 bl2_ext)都对其自带
        cert2 做免重签(内容/头哈希换 90B 前置块), 保留原厂证书结构, 可过 boot 校验.
  bl2_ext 免授权深刷(抄绿厂, 显式可选, 默认不含): 定位 "stp x29,x30,[sp,#-0x10]!;
        add x29,sp,#0; bl;bl;and w0,w0,#imm" 并把第 2 个 bl 的安全校验函数头打成返回 0;
        定位不到/目标非函数头则不冒险, 只跳过. 需要时用隐藏选项 10888(全部+bl2) 或 10887(仅bl2).
  不写死偏移: 对 lk 载荷做 AArch64 指令语义扫描自动定位 6 点, 分 3 类可选打桩.
  B/C/D 采用 "chooser 语义锚": 定位按锁状态全局 V 分发 androidboot.verifiedbootstate=
  绿/黄/橙/红 的分发函数(chooser), B=其函数头, C=其状态装载(读全局 V 处),
  D=另一读同一 V 且含 cmp#1 + cmp#2;b.ne 的 Orange 门函数的 b.ne.
  (chooser 签名缺失时回退历史形态 C-0x3C/C+0xE0 相对锚.)
  E/A/F 独立语义定位, E 容忍 paciasp/stp预/sub 任意开场.
    [1] 伪装回锁 = C 状态装载恒0 + E 写回判定恒1(体内1字); B(chooser)保留原结构不打桩
    [2] 去黄字警告 = D Orange门 (b.ne->b)
    [3] 去写保护 = A 强制参数槽(本 LK 无对应语义时如实报告, 退化为仅 F) + F UFS门控
    (定位: A=cmp#0;csel;mov x0;bl  C=chooser 首处读 V 载荷  E=cmp#3;cset;str 中的 cset
          F=movk 0xc200 前 0x24 内 [sp]ldr+cbz)
   免重签(必做, 后台自动): 无论选哪类, 打完桩后自动在 cert2 前插 90B 槽块重算
         内容/头哈希, 保留原厂签名结构, 保证改后镜像可过 boot 校验(否则不开机).
   fail-safe: 所选类别的关键语义点缺失/非唯一 -> 报告并拒绝输出.
   用法: 拖拽镜像 / 命令行 <in> [out] [ref]; 回车或自动(EOF)=全部类别
  编码: 源码 UTF-8 无 BOM; 编译请加 -finput-charset=UTF-8 -fexec-charset=UTF-8
       (MSVC 用 /utf-8), 运行期自动切换控制台到 UTF-8.
  QQ 交流群: 2167063739
  ============================================================ */
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <map>
#include <algorithm>
#ifdef _WIN32
#include <windows.h>
#endif
#if defined(_MSC_VER) && !defined(__clang__)
#pragma execution_character_set("utf-8")
#endif
typedef uint8_t u8; typedef uint32_t u32; typedef uint64_t u64; typedef int64_t i64;
static inline u32 rd32(const u8*p){return (u32)p[0]|((u32)p[1]<<8)|((u32)p[2]<<16)|((u32)p[3]<<24);}
static inline void wr32(u8*p,u32 v){p[0]=(u8)v;p[1]=(u8)(v>>8);p[2]=(u8)(v>>16);p[3]=(u8)(v>>24);}
/* ==================== SHA-256 ==================== */
static const u32 K[64]={
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static inline u32 ror(u32 x,int n){return (x>>n)|(x<<(32-n));}
static void sha256(const u8*msg,size_t mlen,u8 out[32]){
    size_t pad=((mlen+8)/64+1)*64; std::vector<u8>b(pad,0);
    memcpy(b.data(),msg,mlen); b[mlen]=0x80;
    u64 bl=(u64)mlen*8; for(int i=0;i<8;i++) b[pad-1-i]=(u8)(bl>>(i*8));
    u32 h[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    for(size_t z=0;z<pad;z+=64){
        u32 w[64];
        for(int i=0;i<16;i++) w[i]=((u32)b[z+i*4]<<24)|((u32)b[z+i*4+1]<<16)|((u32)b[z+i*4+2]<<8)|(u32)b[z+i*4+3];
        for(int i=16;i<64;i++){ u32 s0=ror(w[i-15],7)^ror(w[i-15],18)^(w[i-15]>>3);
            u32 s1=ror(w[i-2],17)^ror(w[i-2],19)^(w[i-2]>>10); w[i]=w[i-16]+s0+w[i-7]+s1; }
        u32 a=h[0],bb=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
        for(int i=0;i<64;i++){
            u32 t1=hh+(ror(e,6)^ror(e,11)^ror(e,25))+((e&f)^(~e&g))+K[i]+w[i];
            u32 t2=(ror(a,2)^ror(a,13)^ror(a,22))+((a&bb)^(a&c)^(bb&c));
            hh=g;g=f;f=e;e=d+t1;d=c;c=bb;bb=a;a=t1+t2; }
        h[0]+=a;h[1]+=bb;h[2]+=c;h[3]+=d;h[4]+=e;h[5]+=f;h[6]+=g;h[7]+=hh;
    }
    for(int i=0;i<8;i++){out[i*4]=(u8)(h[i]>>24);out[i*4+1]=(u8)(h[i]>>16);out[i*4+2]=(u8)(h[i]>>8);out[i*4+3]=(u8)h[i];}
}
/* ==================== AArch64 迷你解码器 (语义判定) ==================== */
static inline bool is_bl(u32 v){return (v&0xFC000000u)==0x94000000u;}
static inline bool is_b(u32 v){return (v&0xFC000000u)==0x14000000u;}
static inline bool is_bcond(u32 v){return (v&0xFF000010u)==0x54000000u;}
static inline bool is_adrp(u32 v){return (v&0x9F000000u)==0x90000000u;}
static inline bool is_pacia(u32 v){return v==0xD503233Fu;}
static inline bool is_autia(u32 v){return v==0xD50323BFu;}
static inline bool is_bti(u32 v){return (v&0xFFFFFF3Fu)==0xD503241Fu;}   /* bti c/j/jc */
static inline bool is_sub_sp(u32 v){return (v&0xFF8003FFu)==0xD10003FFu;}
static inline bool is_stp_x29x30_pre(u32 v){
    if((v&0xFFC00000u)!=0xA9800000u)return false;
    return (v&0x1Fu)==29&&((v>>10)&0x1Fu)==30;}
static inline bool is_stp_x29x30_off(u32 v){
    if((v&0xFFC00000u)!=0xA9000000u)return false;
    return (v&0x1Fu)==29&&((v>>10)&0x1Fu)==30;}
/* cmp wN,#imm (SUBS wzr,wN,#imm) */
static inline bool is_cmp_wi(u32 v,int*rn,int*imm){
    if((v&0x7F000000u)!=0x71000000u)return false;
    if((v&0x1Fu)!=31)return false;
    *rn=(v>>5)&0x1F;*imm=(int)(((v>>10)&0xFFF)<<(((v>>22)&3)*12));return true;}
static inline bool is_ldr_w_imm(u32 v,int*rt,int*rn,int*iu){
    if((v&0xFFC00000u)!=0xB9400000u)return false;
    *rt=v&0x1F;*rn=(v>>5)&0x1F;*iu=(v>>10)&0xFFF;return true;}
static inline bool is_str_w_imm(u32 v,int*rt,int*rn,int*iu){
    if((v&0xFFC00000u)!=0xB9000000u)return false;
    *rt=v&0x1F;*rn=(v>>5)&0x1F;*iu=(v>>10)&0xFFF;return true;}
static inline bool is_mov_w_imm(u32 v,int*rd,int*imm){
    if((v&0x80000000u)!=0)return false;
    if((v&0x7F800000u)!=0x52800000u)return false;
    *rd=v&0x1F;*imm=(int)(((v>>5)&0xFFFF)<<(((v>>21)&3)*16));return true;}
/* mov wD,wS = orr wD,wzr,wS */
static inline bool is_mov_w_reg(u32 v,int*rd,int*rs){
    if((v&0xFFE0FFE0u)!=0x2A0003E0u)return false;
    *rd=v&0x1F;*rs=(v>>16)&0x1F;return true;}
/* csel/cset 家族 (opc 位宽松, cond 单独取) */
static inline bool is_sel_fam(u32 v,int*rd,int*rn,int*rm,int*cond){
    u32 m=v&0x7FE00C00u;
    if(m!=0x1A800000u&&m!=0x1A800400u&&m!=0x1A800800u&&m!=0x1A800C00u)return false;
    *rd=v&0x1F;*rn=(v>>5)&0x1F;*rm=(v>>16)&0x1F;*cond=(v>>12)&0xF;return true;}
static inline bool is_cbz_w(u32 v,int*rt){
    if((v&0xFF000000u)!=0x34000000u)return false;
    *rt=v&0x1F;return true;}
static inline u32 imm12u(u32 v){return (v>>10)&0xFFF;}

/* ==================== MTK 容器链 ==================== */
#define MAGIC 0x58881688u
#define SMAGIC 0x58891689u
#define HDRSZ 0x200u
#define PLEN 90
static const u8 OID_CONTENT[12]={0x06,0x07,0x60,0x86,0x76,0x93,0x16,0x02,0x01,0x03,0x21,0x00};
static const u8 OID_HDR[12]={0x06,0x07,0x60,0x86,0x76,0x93,0x16,0x02,0x04,0x03,0x21,0x00};
struct Node{std::string name;u64 hdr,dsize,data,end;};
static bool ascii_ok(const u8*p,int n){for(int i=0;i<n;i++)if(p[i]<0x20||p[i]>0x7e)return false;return true;}
static void parse_nodes(const std::vector<u8>&d,std::vector<Node>&v){
    size_t i=0,n=d.size();
    while(i+HDRSZ<=n){
        if(rd32(&d[i])!=MAGIC){i+=0x10;continue;}
        u32 ds=rd32(&d[i]+4);
        if(!ds||i+HDRSZ+ds>n){i+=0x10;continue;}
        char nm[9];memcpy(nm,&d[i]+8,8);nm[8]=0;
        size_t nl=0;while(nl<8&&nm[nl])nl++;
        if(nl==0||!ascii_ok((const u8*)nm,(int)nl)){i+=0x10;continue;}
        if(rd32(&d[i]+0x30)!=SMAGIC){i+=0x10;continue;}
        Node nd;nd.name=std::string(nm,nl);nd.hdr=i;nd.dsize=ds;nd.data=i+HDRSZ;nd.end=i+HDRSZ+ds;
        v.push_back(nd);i=(i+HDRSZ+ds+0xF)&~(size_t)0xF;
    }
}
static bool find_slot(const u8*data,size_t len,const u8*oid12,u8 val[32]){
    for(size_t p=0;p+12+32<=len;p++){
        if(memcmp(data+p,oid12,12))continue;
        memcpy(val,data+p+12,32);return true;
    }
    return false;
}
static void tohex(const u8*v,int n,char*o){
    static const char*H="0123456789abcdef";
    for(int i=0;i<n;i++){o[i*2]=H[v[i]>>4];o[i*2+1]=H[v[i]&15];}
    o[n*2]=0;
}
/* ==================== 免重签伪造 ==================== */
struct Report{u64 lk_hdr,lk_data,c1_hdr,c2_hdr,payload_len;u8 hh[32],ch[32];std::vector<u8>out;std::string err;bool ok=false,swapped=false,pristine=false;};
static Report forge(const std::vector<u8>&img){
    Report R;std::vector<Node>nd;parse_nodes(img,nd);
    if(nd.empty()){R.err="未找到 MTK 容器链";return R;}
    const Node*lk=0,*c1=0,*c2=0;
    for(size_t i=0;i<nd.size();i++)if(nd[i].name=="lk"){lk=&nd[i];break;}
    if(!lk){R.err="未找到 lk 节点";return R;}
    bool after=false,havec1=false;
    for(size_t i=0;i<nd.size();i++){
        const Node&x=nd[i];
        if(&x==lk){after=true;continue;}
        if(!after)continue;
        if(!c1&&x.name=="cert1"){c1=&x;havec1=true;}
        else if(havec1&&x.name=="cert2"){c2=&x;break;}
    }
    if(!c1||!c2){R.err="未找到 cert1/cert2";return R;}
    R.lk_hdr=lk->hdr;R.lk_data=lk->data;R.c1_hdr=c1->hdr;R.c2_hdr=c2->hdr;
    R.payload_len=c1->hdr-lk->data;
    sha256(&img[lk->hdr],HDRSZ,R.hh);
    sha256(&img[lk->data],(size_t)R.payload_len,R.ch);
    const u8*cd=&img[c2->data];size_t cdlen=(size_t)(c2->end-c2->data);
    u8 v1[32],v2[32];
    if(!find_slot(cd,cdlen,OID_CONTENT,v1)){R.err="cert2 内未找到内容哈希 OID 槽";return R;}
    if(!find_slot(cd,cdlen,OID_HDR,v2)){R.err="cert2 内未找到头哈希 OID 槽";return R;}
    if(memcmp(v1,R.ch,32)!=0||memcmp(v2,R.hh,32)!=0){
        if(memcmp(v1,R.hh,32)==0&&memcmp(v2,R.ch,32)==0)R.swapped=true;
        /* 载荷已被本工具打桩: 原槽为原厂哈希, 与打桩后 ch 必然不同, 属预期 -> 继续伪造 */
    }else R.pristine=true;
    /* 前置块检测: cert2 数据前 90B 是否已是本工具块(不看哈希新旧) */
    bool haveBlock=(cdlen>=PLEN&&cd[0]==0xa0&&cd[1]==0x58
        &&memcmp(cd+2,OID_HDR,12)==0&&memcmp(cd+46,OID_CONTENT,12)==0);
    u8 block[PLEN];
    block[0]=0xa0;block[1]=0x58;
    memcpy(block+2,OID_HDR,12);memcpy(block+14,R.hh,32);
    memcpy(block+46,OID_CONTENT,12);memcpy(block+58,R.ch,32);
    u64 tgt=c2->hdr;
    for(size_t i=0;i<nd.size();i++){
        const Node&x=nd[i];
        std::vector<u8>hdr(img.begin()+x.hdr,img.begin()+x.hdr+HDRSZ);
        if(x.hdr==tgt&&haveBlock){
            /* 已有本工具前置块: 原位覆盖为按当前载荷重算的新块(内容哈希刷新), dsize 不变, 不再二次插块 */
            R.out.insert(R.out.end(),hdr.begin(),hdr.end());
            R.out.insert(R.out.end(),block,block+PLEN);
            R.out.insert(R.out.end(),img.begin()+x.data+PLEN,img.begin()+x.end);
        }else if(x.hdr==tgt){
            /* 无前置块: 正常插入 90B 块并 dsize+PLEN */
            wr32(&hdr[4],(u32)(x.dsize+PLEN));
            R.out.insert(R.out.end(),hdr.begin(),hdr.end());
            R.out.insert(R.out.end(),block,block+PLEN);
            R.out.insert(R.out.end(),img.begin()+x.data,img.begin()+x.end);
        }else{
            R.out.insert(R.out.end(),hdr.begin(),hdr.end());
            R.out.insert(R.out.end(),img.begin()+x.data,img.begin()+x.end);
        }
        while(R.out.size()%0x10)R.out.push_back(0);
    }
    if(R.out.size()<img.size())R.out.resize(img.size(),0);
    R.ok=true;return R;
}
static std::string selfcheck(const std::vector<u8>&out){
    std::vector<Node>nd;parse_nodes(out,nd);
    if(nd.empty())return "无容器链";
    const Node*lk=0,*c1=0,*c2=0;
    for(size_t i=0;i<nd.size();i++)if(nd[i].name=="lk"){lk=&nd[i];break;}
    if(!lk)return "无 lk";
    bool after=false,havec1=false;
    for(size_t i=0;i<nd.size();i++){
        const Node&x=nd[i];
        if(&x==lk){after=true;continue;}
        if(!after)continue;
        if(!c1&&x.name=="cert1"){c1=&x;havec1=true;}
        else if(havec1&&x.name=="cert2"){c2=&x;break;}
    }
    if(!c1||!c2)return "无 cert";
    u8 hh[32],ch[32];
    sha256(&out[lk->hdr],HDRSZ,hh);
    sha256(&out[lk->data],(size_t)(c1->hdr-lk->data),ch);
    const u8*cd=&out[c2->data];size_t clen=(size_t)(c2->end-c2->data);
    u8 v1[32],v2[32];
    if(!find_slot(cd,clen,OID_CONTENT,v1))return "内容槽缺失";
    if(!find_slot(cd,clen,OID_HDR,v2))return "头槽缺失";
    return (memcmp(v1,ch,32)==0&&memcmp(v2,hh,32)==0)?"OK":"槽不匹配";
}
/* ==================== 语义定位器 (lk 载荷内扫描, 要求唯一命中) ==================== */
/* A: cmp wN,#0; csel D,A,B,eq(且 Rm==N); mov x0,x(rd|rm); bl   -> csel 处 */
static void locate_A(const u8*b,size_t n,std::vector<u64>&o){
    for(size_t i=4;i+16<=n;i+=4){
        int rn0,im0;if(!is_cmp_wi(rd32(b+i),&rn0,&im0)||im0!=0)continue;
        int rd,rn,rm,cond;
        if(!is_sel_fam(rd32(b+i+4),&rd,&rn,&rm,&cond)||cond!=0||rm!=rn0)continue;
        u32 mv=rd32(b+i+8);int mrs=(mv>>16)&0x1F;   /* mov x0,xR: 源在 Rm 域 */
        if((mv&0xFFE0FFE0u)!=0xAA0003E0u||(mv&0x1F)!=0)continue;   /* mov x0,xR */
        if(mrs!=rd&&mrs!=rm)continue;
        if(!is_bl(rd32(b+i+12)))continue;
        o.push_back(i+4);
    }
}
/* C: adrp xAR; ldr wN,[xAR,#i]; cmp wN,#1; b.gt                -> ldr 处 */
static void locate_C(const u8*b,size_t n,std::vector<u64>&o){
    for(size_t i=4;i+12<=n;i+=4){
        if(!is_adrp(rd32(b+i)))continue;
        int ar=rd32(b+i)&0x1F;
        int rt,rn,iu;if(!is_ldr_w_imm(rd32(b+i+4),&rt,&rn,&iu)||rn!=ar)continue;
        int rn2,im2;if(!is_cmp_wi(rd32(b+i+8),&rn2,&im2)||im2!=1||rn2!=rt)continue;
        u32 bv=rd32(b+i+12);if(!is_bcond(bv)||(bv&0xF)!=12)continue; /* b.gt */
        o.push_back(i+4);
    }
}
static bool fn_hdr(const u8*b,size_t n,u64 off){
    u32 v=rd32(b+off);
    /* 注意: bti 不是函数头——switch/br 跳转表常以 bti j 作落地垫, 若当作头会把同一函数切碎 */
    if(is_pacia(v))return true;
    if(is_stp_x29x30_pre(v))return true;
    if(is_sub_sp(v)){
        if(off>=4&&is_pacia(rd32(b+off-4)))return false; /* 前有 PAC, 头在前 */
        return off+4<=n&&is_stp_x29x30_off(rd32(b+off+4));
    }
    return false;
}
static u64 back_to_fn(const u8*b,size_t n,u64 from){
    for(u64 f=from;;f-=4){
        if(f<4||from-f>0x800)break;
        if(fn_hdr(b,n,f)){
            if(f>=4&&is_pacia(rd32(b+f-4)))f-=4;   /* 更外层 PAC 入口优先 */
            return f;
        }
    }
    return (u64)-1;
}
/* 通用化 BCD: chooser(verifiedbootstate) 语义链 + 橙门独立定位 */
static inline bool is_add_imm_x(u32 v,int*rd,int*rn,u32*imm){
    if((v&0xFFC00000u)!=0x91000000u)return false;             /* add x,x,#uimm12 */
    *rd=(int)(v&0x1F);*rn=(int)((v>>5)&0x1F);*imm=(v>>10)&0xFFF;return true;
}
static inline u64 adrp_target(u32 v,u64 pc){
    u32 immlo=(v>>29)&3u,immhi=(v>>5)&0x7FFFFu;
    int imm=(int)((immhi<<2)|immlo);
    if(imm&0x100000)imm-=0x200000;                            /* 21 位符号扩展 */
    return (pc&~(u64)0xFFFu)+((i64)imm<<12);
}
/* 判断 off 处 ldr wN,[xM,#i] 的基址是否来自其前 0x40 内 adrp, 若是则回传全局字节地址 */
static bool global_w_load_at(const u8*b,u64 off,int*rt,int*rn,int*iu,u64*addr){
    if(!is_ldr_w_imm(rd32(b+off),rt,rn,iu))return false;
    if(*rn==31)return false;                                   /* [sp] 非全局 */
    for(u64 k=off;k>=4&&off-k<=0x40;k-=4){
        u32 v=rd32(b+k-4);
        if(!is_adrp(v))continue;
        if(((int)(v&0x1F))!=*rn)continue;
        *addr=adrp_target(v,k-4)+((u64)(*iu)<<2);              /* ldr w: imm12*4 */
        return true;
    }
    return false;
}
/* E: 收集所有 cmp#3;sel;str 回溯头, 要求唯一头 */
static bool locate_Eu(const u8*b,size_t n,u64*out){
    u64 first=(u64)-1;bool multi=false;
    for(size_t i=4;i+12<=n;i+=4){
        int rn0,im0;if(!is_cmp_wi(rd32(b+i),&rn0,&im0)||im0!=3)continue;
        int rd,rn,rm,cond;
        if(!is_sel_fam(rd32(b+i+4),&rd,&rn,&rm,&cond))continue;
        int rt2,rn2,iu2;
        if(!is_str_w_imm(rd32(b+i+8),&rt2,&rn2,&iu2)||rt2!=rd)continue;
        u64 f=back_to_fn(b,n,i);
        if(f!=(u64)-1){ if(first==(u64)-1)first=f; else if(first!=f)multi=true; }
    }
    if(first==(u64)-1||multi)return false;
    *out=first;return true;
}
struct BCD{bool ok;u64 B,C,D;int creg;u64 V;};
/* 以 "verifiedbootstate 分发函数(chooser)" 为语义锚: 它按锁状态全局 V 选绿/黄/橙/红 */
static BCD locate_bcd(const u8*b,size_t len){
    BCD r;r.ok=false;r.B=r.C=r.D=(u64)-1;r.creg=-1;r.V=0;
    static const char pfx[]="androidboot.verifiedbootstate=";
    size_t pl=sizeof(pfx)-1;
    std::vector<u64>sites;
    for(u64 i=0;i+8<=len;i+=4){
        u32 a=rd32(b+i);if(!is_adrp(a))continue;
        int ar=(int)(a&0x1F);
        u64 pg=adrp_target(a,i);
        for(u64 j=i+4;j+4<=len&&j-i<=0x80;j+=4){
            int rd,rn;u32 im;
            if(!is_add_imm_x(rd32(b+j),&rd,&rn,&im)||rn!=ar)continue;
            u64 tgt=pg+im;
            if(tgt<=len&&tgt+pl<=len&&memcmp(b+tgt,pfx,pl)==0){sites.push_back(j);break;}
        }
    }
    std::sort(sites.begin(),sites.end());
    sites.erase(std::unique(sites.begin(),sites.end()),sites.end());
    if(sites.size()<3)return r;
    std::map<u64,int>hc;
    for(size_t k=0;k<sites.size();k++){u64 h=back_to_fn(b,len,sites[k]);if(h!=(u64)-1)hc[h]++;}
    u64 Bh=(u64)-1;bool amb=false;
    for(std::map<u64,int>::iterator it=hc.begin();it!=hc.end();++it)
        if(it->second>=3){if(Bh!=(u64)-1)amb=true;Bh=it->first;}
    if(Bh==(u64)-1||amb)return r;
    r.B=Bh;
    u64 first=sites[0];
    for(u64 i=Bh;i+4<=first&&i+8<=len;i+=4){
        u32 a=rd32(b+i);if(!is_adrp(a))continue;
        int ar=(int)(a&0x1F);u64 pg=adrp_target(a,i);
        for(u64 j=i+4;j+4<=len&&j<=i+24;j+=4){
            int rt,rn,iu;
            if(!is_ldr_w_imm(rd32(b+j),&rt,&rn,&iu)||rn!=ar)continue;
            bool used=false;
            for(u64 q=j+4;q+4<=first&&q<=j+0x40;q+=4){
                int r2,i2;
                if(is_cmp_wi(rd32(b+q),&r2,&i2)&&r2==rt&&i2>=1&&i2<=3){used=true;break;}
            }
            if(!used)continue;
            r.C=j;r.creg=rt;r.V=pg+((u64)iu<<2);
            break;
        }
        if(r.C!=(u64)-1)break;
    }
    if(r.C==(u64)-1)return r;
    std::vector<u64>Ds;
    for(u64 i=0;i+8<=len&&Ds.size()<2;i+=4){
        int rn,im;if(!is_cmp_wi(rd32(b+i),&rn,&im)||im!=2)continue;
        u32 bv=rd32(b+i+4);if(!is_bcond(bv)||(bv&0xF)!=1)continue; /* cmp#2;b.ne */
        u64 h=back_to_fn(b,len,i);
        if(h==(u64)-1||h==Bh)continue;
        bool has1=false,hasV=false;
        for(u64 j=h;j<i&&j+4<=len;j+=4){
            int r2,i2;if(is_cmp_wi(rd32(b+j),&r2,&i2)&&r2==rn&&i2==1)has1=true;
            int rt2,rn2,iu2;u64 ad2;
            if(global_w_load_at(b,j,&rt2,&rn2,&iu2,&ad2)&&rt2==rn&&ad2==r.V)hasV=true;
        }
        if(has1&&hasV)Ds.push_back(i+4);
    }
    if(Ds.size()!=1)return r;
    r.D=Ds[0];r.ok=true;
    return r;
}
/* F: movk w?,#0xc200 前 0x24 内 [sp]ldr wN + cbz wN             -> ldr 处 */
static void locate_F(const u8*b,size_t n,std::vector<u64>&o){
    for(size_t i=4;i+8<=n;i+=4){
        if(rd32(b+i)!=0x72B84000u)continue;
        size_t s=i>0x24?i-0x24:0;
        for(size_t j=s;j+8<i&&j+8<=n;j+=4){
            int rt,rn,iu;if(!is_ldr_w_imm(rd32(b+j),&rt,&rn,&iu)||rn!=31)continue;
            int ct;if(!is_cbz_w(rd32(b+j+4),&ct)||ct!=rt)continue;
            o.push_back(j);break;
        }
    }
}
static void patch_at(u8*at,const char*name,u64 off,int nw,const u32*r){
    bool repl=true;
    for(int j=0;j<nw;j++)if(rd32(at+j*4)!=r[j]){repl=false;break;}
    if(repl){printf("  %s @%#08llx 已是目标形态(幂等)\n",name,(unsigned long long)off);return;}
    for(int j=0;j<nw;j++)wr32(at+j*4,r[j]);
    printf("  %s @%#08llx 已打桩(%d字)\n",name,(unsigned long long)off,nw);
}
/* 定位收集唯一化: 成功写 *out 返回 1; 无候选/多候选返回 0 */
static bool pick_one(const std::vector<u64>&c,const char*name,const char*what,u64*out){
    if(c.size()==1){*out=c[0];return true;}
    printf("  %s 定位%s: %s (%u 候选",name,c.empty()?"失败":"非唯一",c.empty()?"无候选":"",(unsigned)c.size());
    for(size_t i=0;i<c.size()&&i<6;i++)printf(" %#llx",(unsigned long long)c[i]);
    printf(")\n");
    return false;
}
/* E 函数体内"状态写回"点: cmp wN,#3; sel(cset/csinc...); str wN,[xK] -> 返回 sel 指令偏移与结果寄存器.
   用于在函数体内把判定结果改成恒 1(不整段替换函数头, 保留原函数结构/正常返回). */
static bool locate_E_sel(const u8*b,size_t n,u64*selOff,int*reg){
    u64 first=(u64)-1;bool multi=false;int r=-1;
    for(size_t i=4;i+12<=n;i+=4){
        int rn0,im0;if(!is_cmp_wi(rd32(b+i),&rn0,&im0)||im0!=3)continue;
        int rd,rn,rm,cond;
        if(!is_sel_fam(rd32(b+i+4),&rd,&rn,&rm,&cond))continue;
        int rt2,rn2,iu2;
        if(!is_str_w_imm(rd32(b+i+8),&rt2,&rn2,&iu2)||rt2!=rd)continue;
        if(first==(u64)-1){first=i+4;r=rd;}
        else if(first!=i+4)multi=true;
    }
    if(first==(u64)-1||multi)return false;
    *selOff=first;*reg=r;return true;
}
/* 6 点选择性语义打桩 (按 cats 分类). base=lk 载荷文件偏移, len=lk dsize.
   通用化: B/C/D 不再靠 C 锚点的固定 C-0x3C/C+0xE0 相对偏移,
   而以 "verifiedbootstate 分发函数(chooser)" 与 "橙门函数" 为独立语义锚,
   可同时覆盖历史(如 verified_lk)与新一代(如 lk_b, chooser/橙门布局不同)构建.
   打桩原则: 尽量只改"单指令/返回值", 不整段替换函数头破坏原函数结构.
   B(chooser)不再桩化为整段返回0, 保留原结构, 状态由 C(状态读->0)强制. */
static bool apply_patches(std::vector<u8>&img,u64 base,u64 len,int cats){
    bool w1=(cats&1)!=0,w2=(cats&2)!=0,w3=(cats&4)!=0;   /* 伪装回锁 / 去黄字 / 去写保护 */
    printf("\n[语义定位+选择性打桩] 在 lk 载荷内做类别桩(单指令原位改写, 尽量保留原函数结构);\n");
    printf("  bl2_ext 免授权深刷为显式可选(10888=含, 默认类别不含).\n");
    printf("  已选: %s%s%s\n",w1?"[1]伪装回锁(C+E,不砍B) ":"",w2?"[2]去黄字(D) ":"",w3?"[3]去写保护(A/F)":"");
    const u8*b=&img[base];
    u64 relA=(u64)-1,relB=0,relC=0,relD=0,relE=0,relF=0;
    int eReg=0;bool aFound=true;

    /* ---- [1]/[2]: B(chooser 函数头)/C(状态装载)/D(橙门) ---- */
    if(w1||w2){
        BCD r=locate_bcd(b,len);
        if(r.ok){
            relB=r.B;relC=r.C;relD=r.D;
            printf("  [chooser 语义锚] verifiedbootstate 分发函数命中:\n");
            printf("    B chooser函数头=%#llx  C 状态装载=%#llx(读全局%#llx)  D 橙门=%#llx\n",
                   (unsigned long long)relB,(unsigned long long)relC,
                   (unsigned long long)r.V,(unsigned long long)relD);
        }else{
            /* 传统相对锚回退 (chooser 签名缺失时用 C-0x3C/C+0xE0, 仅支持历史形态) */
            std::vector<u64>cC;locate_C(b,len,cC);
            if(!pick_one(cC,"C(锚,legacy)","状态装载",&relC))return false;
            if(w1){
                if(relC<0x3C){printf("  B/C 锚定越界\n");return false;}
                relB=relC-0x3C;
                if(!(is_pacia(rd32(b+relB))&&is_sub_sp(rd32(b+relB+4)))){printf("  B 锚点非 [paciasp;sub sp]\n");return false;}
            }
            if(w2){
                relD=relC+0xE0;
                if(relD+8>len){printf("  D 越界\n");return false;}
                {int rn,im;if(!(is_cmp_wi(rd32(b+relD-4),&rn,&im)&&im==2)){printf("  D-4 非 cmp#2\n");return false;}}
                u32 dv=rd32(b+relD);if(!(is_bcond(dv)&&(dv&0xF)==1)){printf("  D 非 b.ne\n");return false;}
            }
        }
    }
    if(w1){
        if(!locate_E_sel(b,len,&relE,&eReg)){printf("  E 定位失败或非唯一(状态写回校验 cset 点)\n");return false;}
    }
    if(w3){
        std::vector<u64>ca;locate_A(b,len,ca);
        if(!pick_one(ca,"A","强制参数槽",&relA)){
            printf("  A 点在本 LK 版本无对应语义(cmp#0;csel;bl 强制参数槽缺失),\n");
            printf("     [3]去写保护降级为仅应用 F(UFS门控) 点\n");
            relA=(u64)-1;aFound=false;
        }
        std::vector<u64>cF;locate_F(b,len,cF);
        if(!pick_one(cF,"F","UFS门控",&relF))return false;
    }
    bool all=true;
    int done=0,total=(w1?2:0)+(w2?1:0)+(w3?(aFound?2:1):0);   /* [1]=C+E (B 保留结构不再计桩) */
    u64 lo=(u64)-1,hi=0;
    auto fileoff=[&](u64 r){return base+r;};
    auto note_ok=[&](u64 r){done++;if(r<lo)lo=r;if(r>hi)hi=r;};
    /* A (类3): csel wD,wA,wB,eq -> mov wD,wA (orr wD,wzr,wA) */
    if(w3&&aFound){u32 sv=rd32(b+relA);int sd,srn,srm,scond;
     if(is_sel_fam(sv,&sd,&srn,&srm,&scond)&&scond==0){
        u32 r=0x2A0003E0u|((u32)srn<<16)|(u32)sd;
        patch_at(&img[fileoff(relA)],"A 强制参数槽(csel->mov)",fileoff(relA),1,&r);note_ok(relA);
     }else if(is_mov_w_reg(sv,&sd,&srn)){
        printf("  A 已是目标形态(幂等) @%#llx\n",(unsigned long long)fileoff(relA));note_ok(relA);
     }else{printf("  A 定位处指令异常\n");all=false;}}
    /* B (类1): 保留 chooser 原函数结构(不整段头替换为返回0)——引导状态由 C(状态读->0)强制.
       此改动贴合绿厂做法, 也避免"砍掉引导路径上需正常完成的函数"导致开机异常. */
    if(w1){
        if(fn_hdr(b,len,relB))printf("  B chooser 函数头保留原结构(不整段返回0), 状态由 C 强制\n");
        else printf("  B chooser 函数头形态异常, 忽略(仍继续 C/E)\n");
    }
    /* C (类1): ldr wN,[..] -> mov wN,#0 */
    if(w1){u32 lv=rd32(b+relC);int rt,rn,iu;
     if(is_mov_w_imm(lv,&rt,&iu)&&iu==0){
        printf("  C 已是目标形态(幂等) @%#llx\n",(unsigned long long)fileoff(relC));note_ok(relC);
     }else if(is_ldr_w_imm(lv,&rt,&rn,&iu)){u32 r=0x52800000u|(u32)rt;
        patch_at(&img[fileoff(relC)],"C 状态装载恒0",fileoff(relC),1,&r);note_ok(relC);}
     else{printf("  C 定位处指令异常\n");all=false;}}
    /* D (类2): b.ne -> 无条件 b (同位移, imm19 符号扩展为 imm26) */
    if(w2){u32 dv=rd32(b+relD);u32 i19=(dv>>5)&0x7FFFF;
     if(i19&0x40000u)i19|=0x3FC0000u;
     u32 r=0x14000000u|i19;
     patch_at(&img[fileoff(relD)],"D Orange门改无条件b",fileoff(relD),1,&r);note_ok(relD);}
    /* E (类1): 保留原函数头/帧, 只把函数体内 "状态!=3"(cset/csel) 一句改成恒 1,
       函数照常调用/读状态/正常返回, 仅写回结果恒为 1 (不破坏原函数结构). */
    if(w1){u32 sv=rd32(b+relE);int d0,s0,s1,c0;
     if(is_mov_w_imm(sv,&d0,&s0)&&s0==1){
        printf("  E 已是目标形态(幂等) @%#llx (mov w%d,#1)\n",(unsigned long long)fileoff(relE),d0);note_ok(relE);
     }else if(is_sel_fam(sv,&d0,&s0,&s1,&c0)){
        u32 r=0x52800000u|0x20u|(u32)d0;              /* mov wD,#1 */
        patch_at(&img[fileoff(relE)],"E 状态写回判定恒1(体内1字,保结构)",fileoff(relE),1,&r);note_ok(relE);
     }else{printf("  E 定位处指令异常\n");all=false;}}
    /* F (类3): ldr wN,[sp,#i] -> mov wN,#1 */
    if(w3){u32 lv=rd32(b+relF);int rt,rn,iu;
     if(is_mov_w_imm(lv,&rt,&iu)&&iu==1){
        printf("  F 已是目标形态(幂等) @%#llx\n",(unsigned long long)fileoff(relF));note_ok(relF);
     }else if(is_ldr_w_imm(lv,&rt,&rn,&iu)){u32 r=0x52800000u|(u32)rt|0x20u;
        patch_at(&img[fileoff(relF)],"F UFS门控读取恒1",fileoff(relF),1,&r);note_ok(relF);}
     else{printf("  F 定位处指令异常\n");all=false;}}
    if(all&&done>0){
        printf("  [覆盖验证] %d/%d 个选中点位于载荷内 rel %#llx~%#llx, 均 < dsize=%#llx\n"
               "              => 修改落在免重签内容哈希覆盖区, 可过 boot 验证\n",
               done,total,(unsigned long long)lo,(unsigned long long)hi,(unsigned long long)len);
    }
    return all;
}
/* ==================== 差异/IO ==================== */
static std::vector<std::pair<size_t,size_t>>rle_diff(const std::vector<u8>&a,const std::vector<u8>&b){
    std::vector<std::pair<size_t,size_t>>dl;
    size_t n=a.size()<b.size()?a.size():b.size(),i=0;
    while(i<n){
        if(a[i]!=b[i]){
            size_t j=i;while(j<n&&a[j]!=b[j])j++;
            dl.push_back(std::make_pair(i,j-i));i=j;
        }else i++;
    }
    if(a.size()!=b.size())dl.push_back(std::make_pair(n,
        a.size()>b.size()?a.size()-b.size():b.size()-a.size()));
    return dl;
}
#ifdef _WIN32
static FILE*open_file(const char*path,const char*mode){
    wchar_t wp[4096],wm[16];
    if(MultiByteToWideChar(CP_UTF8,0,path,-1,wp,4096)==0)return 0;
    if(MultiByteToWideChar(CP_UTF8,0,mode,-1,wm,16)==0)return 0;
    return _wfopen(wp,wm);
}
#else
static FILE*open_file(const char*path,const char*mode){return fopen(path,mode);}
#endif
static bool read_file(const std::string&p,std::vector<u8>&out){
    FILE*f=open_file(p.c_str(),"rb");
    if(!f)return false;
#ifdef _WIN32
    _fseeki64(f,0,SEEK_END);__int64 sz=_ftelli64(f);_fseeki64(f,0,SEEK_SET);
#else
    fseeko(f,0,SEEK_END);long long sz=ftello(f);fseeko(f,0,SEEK_SET);
#endif
    if(sz<=0){fclose(f);return false;}
    out.resize((size_t)sz);
    bool ok=fread(out.data(),1,(size_t)sz,f)==(size_t)sz;
    fclose(f);return ok;
}
static bool write_file(const std::string&p,const std::vector<u8>&d){
    FILE*f=open_file(p.c_str(),"wb");
    if(!f)return false;
    bool ok=fwrite(d.data(),1,d.size(),f)==d.size();
    fclose(f);return ok;
}
static std::string trim(const std::string&s){
    size_t a=s.find_first_not_of(" \t\r\n");
    if(a==std::string::npos)return"";
    size_t b=s.find_last_not_of(" \t\r\n");
    return s.substr(a,b-a+1);
}
static void init_console(){
#ifdef _WIN32
    /* 源码为 UTF-8(无 BOM); 运行期把控制台输出/输入代码页统一切到 UTF-8,
       保证中文提示在任何 Windows 代码页(GBK 936 / 437 ...)下都不乱码.
       若被重定向/管道, 输出保持原始 UTF-8 字节, 文件亦为合法 UTF-8. */
    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCP(CP_UTF8);
    setvbuf(stdout,NULL,_IONBF,0);   /* 无缓冲: 交互提示必先于输入出现, 避免顺序错乱 */
    setvbuf(stderr,NULL,_IONBF,0);
#endif
}
static void press_enter(){printf("\n按回车键退出...");fflush(stdout);int c;do{c=getchar();}while(c!='\n'&&c!=EOF);}
/* 询问修补类别: 返回位掩码 (bit0=伪装回锁, bit1=去黄字, bit2=去写保护).
   免重签不在此选择 —— 必做, 后台自动执行. EOF/回车=全部(兼容拖拽自动/回归脚本). */
#define CATS_FORGERY_ONLY 0x40000000   /* 隐藏选项 10886: 仅做免重签(不打功能桩), 用于单独验证伪造是否被接受 */
#define CATS_FORGE_BL2    0x40000001   /* 隐藏选项 10887: 仅免重签 + bl2 深刷(不打 lk 功能桩), 判断 lk 桩是否黑屏来源 */
#define CATS_ALL_BL2      0x40000002   /* 隐藏选项 10888: 正常类别 + bl2 深刷(默认类别不含 bl2, 需要时用这个) */
static int ask_categories(){
    printf("\n请选择要修补的类别 (多个用逗号如 1,3; 回车=全部):\n");
    printf("  [1] 伪装回锁 : 锁定检查/状态装载/写回校验 恒为已锁 (B+C+E 点)\n");
    printf("  [2] 去黄字警告 : 去掉 Orange 警告等待 (D 点)\n");
    printf("  [3] 去写保护 : 绕过 UFS 写保护 + 强制开启参数 (A+F 点)\n");
    for(int attempt=0;attempt<3;attempt++){
        printf("请选择: ");fflush(stdout);
        char line[64];
        if(!fgets(line,sizeof(line),stdin))return 7;      /* EOF = 全部 */
        std::string s=trim(line);
        if(s=="10886")return CATS_FORGERY_ONLY;           /* 隐藏选项: 仅免重签 */
        if(s=="10887")return CATS_FORGE_BL2;              /* 隐藏选项: 仅免重签+bl2深刷(不打lk桩) */
        if(s=="10888")return CATS_ALL_BL2;                /* 隐藏选项: 正常类别 + bl2 深刷 */
        if(s.empty())return 7;                            /* 回车 = 全部 */
        int m=0;bool bad=false;
        for(size_t i=0;i<s.size();i++){
            char c=s[i];
            if(c=='1')m|=1;else if(c=='2')m|=2;else if(c=='3')m|=4;
            else if(c>='4'&&c<='9')bad=true;
        }
        if(m!=0)return m;
        if(attempt<2)printf("  无法识别 (只支持 1-3 或其组合, 如 1,3)。%s\n",
                            bad?"注意没有选项 4/5..., 请重新输入:":"请重新输入:");
        else{printf("  多次无法识别, 已按全部处理。\n");return 7;}
    }
    return 7;
}
/* 判断当前载荷是否仍含"原生(未补桩)语义点"。
   用途: cert2 带本工具前置块且哈希匹配时, 区分
     A) 真幂等 = 载荷已被补桩(原生锚已被打掉, 语义定位不到) -> 原样输出;
     B) 仅伪造 = cert2 已伪造但载荷仍是原生(锚点齐全未打桩) -> 需要补桩并原位刷新块. */
static bool payload_needs_patch(const u8*b,u64 len,int cats){
    bool w1=(cats&1)!=0,w2=(cats&2)!=0,w3=(cats&4)!=0;
    bool need=false;
    if(w1||w2){
        BCD r=locate_bcd(b,len);
        if(r.ok){
            /* B 不再整段桩化(保结构), 故不判 B; 判 C(状态读->0) 与 E(体内 cset->mov #1) */
            u32 cv=rd32(b+r.C);int rt,im;bool cT=is_mov_w_imm(cv,&rt,&im)&&im==0;
            bool dT=((rd32(b+r.D)&0xFC000000u)==0x14000000u);               /* 无条件 b */
            u64 es=(u64)-1;int er=-1;
            bool eT=locate_E_sel(b,len,&es,&er)&&is_mov_w_imm(rd32(b+es),&rt,&im)&&im==1;
            if((w1&&(!cT||!eT))||(w2&&!dT))need=true;
        }
        /* locate_bcd 失败 = 原生锚已不存在(已桩/形态破坏) -> 不再补 */
    }
    if(w3){
        std::vector<u64>cf;locate_F(b,len,cf);
        if(cf.size()==1){u32 fv=rd32(b+cf[0]);int rt,im;if(!(is_mov_w_imm(fv,&rt,&im)&&im==1))need=true;}
    }
    return need;
}
/* ==================== bl2_ext 免授权深刷 (抄绿厂, 自动推导) ==================== */
static inline bool is_stp_x29x30_pre_imm(u32 v,int*imm){
    if((v&0xFFC00000u)!=0xA9800000u)return false;
    if((v&0x1Fu)!=29||((v>>10)&0x1Fu)!=30)return false;
    int i7=(int)((v>>15)&0x7F); if(i7&0x40)i7-=0x80; *imm=i7*8; return true;
}
static inline bool is_add_x29_sp0(u32 v){ return v==0x910003FDu; }          /* add x29,sp,#0 */
static inline bool is_and_w0_w0_imm(u32 v){                                  /* and w0,w0,#imm */
    return (v&0x7F000000u)==0x12000000u && (v&0x3FFu)==0;
}
/* bl2 安全校验查询: stp x29,x30,[sp,#-0x10]!; add x29,sp,#0; bl; bl; and w0,w0,#imm
   打桩目标 = 第 2 个 bl 的真正安全校验函数头 (与已知可用镜像/绿厂一致) */
static bool locate_bl2_sec(const u8*reg,u64 len,u64*patOff,u64*tgt){
    for(u64 off=0;off+20<=len;off+=4){
        int imm;
        if(!is_stp_x29x30_pre_imm(rd32(reg+off),&imm)||imm!=-0x10)continue;
        if(!is_add_x29_sp0(rd32(reg+off+4)))continue;
        if(!is_bl(rd32(reg+off+8))||!is_bl(rd32(reg+off+12)))continue;
        if(!is_and_w0_w0_imm(rd32(reg+off+16)))continue;
        u32 blv=rd32(reg+off+12); i64 disp=(i64)(blv&0x3FFFFFFu);
        if(disp&0x2000000)disp-=0x4000000;
        if(patOff)*patOff=off;
        if(tgt)*tgt=off+12+(disp<<2);
        return true;
    }
    return false;
}
/* 打桩 bl2 安全校验查询函数(返回 0); 返回 true 表示已应用(需随后对 bl2 cert2 免重签) */
static bool apply_bl2_sec(std::vector<u8>&img){
    printf("\n[深刷bl2 自动] bl2_ext 安全校验免授权 (抄绿厂自动推导)\n");
    std::vector<Node>nd;parse_nodes(img,nd);
    const Node*bl2=0;
    for(size_t i=0;i<nd.size();i++)if(nd[i].name=="bl2_ext"){bl2=&nd[i];break;}
    if(!bl2){printf("  bl2_ext: 无该分区(跳过)\n");return false;}
    u64 po,to;
    if(!locate_bl2_sec(&img[bl2->data],bl2->dsize,&po,&to)){
        printf("  bl2_ext 安全校验查询: 未发现该结构(此固件无, 跳过)\n");return false;
    }
    u64 at=bl2->data+to;
    if(rd32(&img[at])==0x52800000u&&rd32(&img[at+4])==0xD65F03C0u){
        printf("  bl2_ext 安全校验查询 @%#llx 已是 mov w0,#0;ret(幂等)\n",(unsigned long long)at);
        return true;   /* 桩已在 -> 仍校验/刷新 bl2 cert2 */
    }
    if(!fn_hdr(img.data(),img.size(),at)){
        printf("  bl2_ext 目标 @%#llx 非函数头, 不冒险打桩\n",(unsigned long long)at);return false;
    }
    wr32(&img[at],0x52800000u);wr32(&img[at+4],0xD65F03C0u);
    printf("  bl2_ext 安全校验查询函数 -> 返回0 @%#llx (bl2_ext+%#llx)\n",
           (unsigned long long)at,(unsigned long long)to);
    return true;
}
/* 仅对 bl2_ext 分区做免重签 (内容/头哈希换块, 插入或原位刷新 90B) */
static Report forge_bl2(const std::vector<u8>&img){
    Report R;std::vector<Node>nd;parse_nodes(img,nd);
    if(nd.empty()){R.err="无容器链";return R;}
    int li=-1;for(size_t i=0;i<nd.size();i++)if(nd[i].name=="bl2_ext"){li=(int)i;break;}
    if(li<0){R.err="无 bl2_ext";return R;}
    if(li+2>=(int)nd.size()||nd[li+1].name!="cert1"||nd[li+2].name!="cert2"){R.err="bl2_ext 后非 cert1/cert2";return R;}
    const Node&im=nd[li];const Node&c1=nd[li+1];const Node&c2=nd[li+2];
    sha256(&img[im.hdr],HDRSZ,R.hh);
    sha256(&img[im.data],(size_t)(c1.hdr-im.data),R.ch);
    const u8*cd=&img[c2.data];size_t cdlen=(size_t)(c2.end-c2.data);
    u8 v1[32],v2[32];
    if(!find_slot(cd,cdlen,OID_CONTENT,v1)){R.err="bl2 cert2 未找到内容哈希 OID 槽";return R;}
    if(!find_slot(cd,cdlen,OID_HDR,v2)){R.err="bl2 cert2 未找到头哈希 OID 槽";return R;}
    bool haveBlock=(cdlen>=PLEN&&cd[0]==0xa0&&cd[1]==0x58
        &&memcmp(cd+2,OID_HDR,12)==0&&memcmp(cd+46,OID_CONTENT,12)==0);
    u8 block[PLEN];
    block[0]=0xa0;block[1]=0x58;
    memcpy(block+2,OID_HDR,12);memcpy(block+14,R.hh,32);
    memcpy(block+46,OID_CONTENT,12);memcpy(block+58,R.ch,32);
    u64 tgt=c2.hdr;
    for(size_t i=0;i<nd.size();i++){
        const Node&x=nd[i];
        std::vector<u8>hdr(img.begin()+x.hdr,img.begin()+x.hdr+HDRSZ);
        if(x.hdr==tgt&&haveBlock){
            R.out.insert(R.out.end(),hdr.begin(),hdr.end());
            R.out.insert(R.out.end(),block,block+PLEN);
            R.out.insert(R.out.end(),img.begin()+x.data+PLEN,img.begin()+x.end);
        }else if(x.hdr==tgt){
            wr32(&hdr[4],(u32)(x.dsize+PLEN));
            R.out.insert(R.out.end(),hdr.begin(),hdr.end());
            R.out.insert(R.out.end(),block,block+PLEN);
            R.out.insert(R.out.end(),img.begin()+x.data,img.begin()+x.end);
        }else{
            R.out.insert(R.out.end(),hdr.begin(),hdr.end());
            R.out.insert(R.out.end(),img.begin()+x.data,img.begin()+x.end);
        }
        while(R.out.size()%0x10)R.out.push_back(0);
    }
    if(R.out.size()<img.size())R.out.resize(img.size(),0);
    R.ok=true;return R;
}
/* bl2_ext 免重签自检 */
static std::string selfcheck_bl2(const std::vector<u8>&out){
    std::vector<Node>nd;parse_nodes(out,nd);
    int li=-1;for(size_t i=0;i<nd.size();i++)if(nd[i].name=="bl2_ext"){li=(int)i;break;}
    if(li<0)return "无 bl2_ext";
    if(li+2>=(int)nd.size()||nd[li+1].name!="cert1"||nd[li+2].name!="cert2")return "bl2 cert 缺失";
    const Node&im=nd[li];const Node&c1=nd[li+1];const Node&c2=nd[li+2];
    u8 hh[32],ch[32];
    sha256(&out[im.hdr],HDRSZ,hh);
    sha256(&out[im.data],(size_t)(c1.hdr-im.data),ch);
    const u8*cd=&out[c2.data];size_t clen=(size_t)(c2.end-c2.data);
    if(!(clen>=PLEN&&cd[0]==0xa0&&cd[1]==0x58))return "bl2 无前置块";
    if(memcmp(cd+2,OID_HDR,12)!=0||memcmp(cd+14,hh,32)!=0)return "bl2 头槽不匹配";
    if(memcmp(cd+46,OID_CONTENT,12)!=0||memcmp(cd+58,ch,32)!=0)return "bl2 内容槽不匹配";
    return "OK";
}
/* ==================== 处理单文件 ==================== */
static int process_one(const std::string&in,const std::string&out_arg,const std::string&ref_arg,int cats){
    bool forgeOnly=(cats==CATS_FORGERY_ONLY);   /* 隐藏 10886: 仅免重签, 不打桩 */
    bool forgeBl2 =(cats==CATS_FORGE_BL2);      /* 隐藏 10887: 仅免重签+bl2深刷, 不打lk桩 */
    int  eff      =(cats==CATS_ALL_BL2)?7:cats; /* 10888 = 全类别 + bl2 深刷 */
    std::vector<u8>img;
    if(!read_file(in,img)){printf("错误: 无法读取文件: %s\n",in.c_str());return 1;}
    printf("\n[容器识别]\n");
    std::vector<Node>nd;parse_nodes(img,nd);
    printf("  容器链: %u 个容器\n",(unsigned)nd.size());
    for(size_t i=0;i<nd.size();i++)
        printf("    %-8s @ %#llx dsize=%#llx\n",nd[i].name.c_str(),
               (unsigned long long)nd[i].hdr,(unsigned long long)nd[i].dsize);
    if(nd.empty()){printf("失败: 非 MTK 容器链镜像\n");return 1;}
    const Node*ln=0;
    for(size_t i=0;i<nd.size();i++)if(nd[i].name=="lk"){ln=&nd[i];break;}
    if(!ln){printf("失败: 未找到 lk 节点\n");return 1;}
    printf("  lk 载荷文件区 [%#llx,%#llx) dsize=%#llx (语义扫描区间)\n",
           (unsigned long long)ln->data,(unsigned long long)ln->end,(unsigned long long)ln->dsize);

    /* ===== 已修补识别: lk 后首个 cert2 若已带本工具伪造块(前90B)且哈希与当前载荷一致 => 幂等 ===== */
    const Node*c1x=0,*c2x=0;
    {bool after=false,havec1=false;
     for(size_t i=0;i<nd.size();i++){
        const Node&x=nd[i];
        if(&x==ln){after=true;continue;}
        if(!after)continue;
        if(!c1x&&x.name=="cert1"){c1x=&x;havec1=true;}
        else if(havec1&&x.name=="cert2"){c2x=&x;break;}
     }}
    bool blockPresent=false;   /* cert2 是否已带本工具前置块 */
    int  idemState=0;          /* 0=正常补桩; 1=真幂等(已补桩,原样输出); 2=已伪造cert2但载荷未补桩(需补桩+原位刷新) */
    if(!forgeOnly&&!forgeBl2&&c1x&&c2x){  /* 隐藏 10886/10887: 跳过幂等判定, 直接做免重签(±bl2) */
        const u8*cd=&img[c2x->data];size_t cdlen=(size_t)(c2x->end-c2x->data);
        if(cdlen>=PLEN&&cd[0]==0xa0&&cd[1]==0x58){
            blockPresent=true;
            u8 hh[32],ch[32];
            sha256(&img[ln->hdr],HDRSZ,hh);
            sha256(&img[ln->data],(size_t)(c1x->hdr-ln->data),ch);
            bool match=(memcmp(cd+2,OID_HDR,12)==0&&memcmp(cd+14,hh,32)==0
                     &&memcmp(cd+46,OID_CONTENT,12)==0&&memcmp(cd+58,ch,32)==0);
            if(!match){
                printf("\n[已修补识别] cert2 携带本工具伪造块, 但块内哈希与当前载荷不一致\n");
                printf("  => 镜像在修补后又被动过, 语义基准已破坏; 请用原始未修补镜像重新修补\n");
                return 1;
            }
            if(!payload_needs_patch(&img[ln->data],ln->dsize,eff)){
                idemState=1;
                printf("\n[已修补识别] 命中: cert2 携带本工具伪造块, 哈希匹配, 且载荷已含所选类别功能桩\n");
                printf("  => 真幂等, 直接原样输出\n");
            }else{
                idemState=2;
                printf("\n[已修补识别] cert2 已带本工具伪造块(哈希与当前载荷一致),\n");
                printf("  但载荷仍是原生形态、未含所选类别功能桩(仅免重签伪造、未打桩)\n");
                printf("  => 将补打所选桩点, 并原位刷新前置块内容哈希(不再二次插块)\n");
            }
        }
    }

    /* 写输出+参考对比(普通路径与幂等路径共用) */
    auto do_write=[&](const std::vector<u8>&data,const char*tag)->int{
        std::string out=out_arg.empty()?in:out_arg;
        if(out_arg.empty()){
            size_t dot=out.find_last_of('.');size_t slash=out.find_last_of("/\\");
            if(dot!=std::string::npos&&(slash==std::string::npos||dot>slash))out=out.substr(0,dot)+"_norsgn_patched"+out.substr(dot);
            else out+="_norsgn_patched.bin";
        }
        if(!write_file(out,data)){printf("错误: 无法写入 %s\n",out.c_str());return 1;}
        printf("\n输出文件: %s (大小 %#llx) [%s]\n",out.c_str(),(unsigned long long)data.size(),tag);
        if(!ref_arg.empty()){
            std::vector<u8>ref;
            if(read_file(ref_arg,ref)){
                auto dl=rle_diff(data,ref);u64 diffb=0;
                for(size_t i=0;i<dl.size();i++)diffb+=(u64)dl[i].second;
                printf("\n[对比] %s\n  len差=%#llx 区段=%u 不同字节=%llu\n",
                       ref_arg.c_str(),(unsigned long long)(data.size()>ref.size()?data.size()-ref.size():ref.size()-data.size()),
                       (unsigned)dl.size(),(unsigned long long)diffb);
                size_t show=dl.size()<24?dl.size():24;
                for(size_t i=0;i<show;i++)printf("  [%#zx..%#zx) %uB\n",dl[i].first,dl[i].first+dl[i].second,(unsigned)dl[i].second);
                if(dl.size()>show)printf("  ... 还有 %u 段\n",(unsigned)(dl.size()-show));
            }else printf("\n警告: 无法读取参考 %s\n",ref_arg.c_str());
        }
        return 0;
    };

    if(forgeOnly){
        printf("\n[仅免重签] 隐藏选项 10886: 不打任何功能桩, 只对当前载荷重算哈希并写/刷新 cert2 前置块\n");
        printf("  (用于单独验证免重签伪造本身是否被设备接受; 不改任何指令)\n");
        Report R=forge(img);
        if(!R.ok){printf("\n失败: %s\n",R.err.c_str());return 1;}
        printf("  免重签完成: 内容哈希=当前载荷, 头哈希=当前镜像头\n");
        std::string sc=selfcheck(R.out);
        printf("  自检: %s\n",sc.c_str());
        if(sc!="OK"){printf("失败: 自检未通过, 不输出\n");return 1;}
        return do_write(R.out,"仅免重签(不打桩)");
    }
    if(forgeBl2){
        printf("\n[仅免重签+bl2深刷] 隐藏选项 10887: 不打 lk 功能桩, 只做 bl2_ext 免授权 + lk/bl2 cert2 免重签\n");
        printf("  (用于判断 lk 功能桩是否黑屏来源; bl2 深刷单独叠加)\n");
        bool bd=apply_bl2_sec(img);
        Report R=forge(img);
        if(!R.ok){printf("\n失败: %s\n",R.err.c_str());return 1;}
        if(bd){
            Report RB=forge_bl2(R.out);
            if(!RB.ok){printf("\n失败: bl2_ext 免重签: %s\n",RB.err.c_str());return 1;}
            R=RB;
        }
        std::string sc=selfcheck(R.out);
        printf("  自检(lk): %s\n",sc.c_str());
        if(sc!="OK"){printf("失败: 自检未通过, 不输出\n");return 1;}
        if(bd){
            std::string scb=selfcheck_bl2(R.out);
            printf("  自检(bl2_ext): %s\n",scb.c_str());
            if(scb!="OK"){printf("失败: bl2_ext 自检未通过, 不输出\n");return 1;}
        }
        return do_write(R.out,bd?"仅免重签+深刷bl2(不打lk桩)":"仅免重签(不打lk桩)");
    }
    if(idemState==1){
        if(cats!=7)
            printf("  (该镜像为整包修补后的真幂等形态, 已含所选类别全部打桩, 直接原样输出)\n");
        return do_write(img,"真幂等(已补桩), 原样输出");
    }
    if(!apply_patches(img,ln->data,ln->dsize,eff)){
        printf("\n失败: 打桩中止, 不输出\n");
        printf("  (非本工具伪造块形态且所选类别语义定位失败: 可能已被其他方式打桩, 请用原始镜像重新修补)\n");
        return 1;
    }
    /* ---- bl2_ext 免授权深刷(自动): 打桩 bl2 安全校验查询 -> 返回 0, 并对 bl2 cert2 免重签 ---- */
    /* bl2 深刷 = 显式可选: 默认类别(1/2/3/7)不含; 只有 10888(正常+bl2) 或 10887(仅bl2) 才做 */
    bool bl2dirty=false;
    if(cats==CATS_ALL_BL2) bl2dirty=apply_bl2_sec(img);
    Report R=forge(img);
    if(!R.ok){printf("\n失败: %s\n",R.err.c_str());return 1;}
    if(bl2dirty){
        Report RB=forge_bl2(R.out);
        if(!RB.ok){printf("\n失败: bl2_ext 免重签: %s\n",RB.err.c_str());return 1;}
        R=RB;
    }
    if(blockPresent){
        printf("\n[免重签后台处理] 载荷已补桩, 前置块内容哈希已原位刷新(复用既有 90B 块, 不二次插块)\n");
        printf("  (必需步骤, 不重算则改后镜像校验失败不开机; 原厂签名结构保留, 刷入无需重签)\n");
    }else{
        printf("\n[免重签后台处理] 内容/头哈希已自动重算, cert2 前插 90B 槽块\n");
        printf("  (必需步骤, 不重算则改后镜像校验失败不开机; 原厂签名结构保留, 刷入无需重签)\n");
    }
    std::string sc=selfcheck(R.out);
    printf("  自检(lk): %s\n",sc.c_str());
    if(sc!="OK"){printf("失败: 自检未通过, 不输出\n");return 1;}
    if(bl2dirty){
        std::string scb=selfcheck_bl2(R.out);
        printf("  自检(bl2_ext): %s\n",scb.c_str());
        if(scb!="OK"){printf("失败: bl2_ext 自检未通过, 不输出\n");return 1;}
    }
    return do_write(R.out,bl2dirty?"选择性打桩+深刷bl2+免重签":"选择性打桩+免重签");
}
/* ==================== 入口 ==================== */
static int entry_point(std::vector<std::string>&paths,std::string&out_arg,std::string&ref_arg){
    init_console();
    printf("============================================================\n");
    printf(" 蓝厂(vivo/iQOO)通用 LK 修补工具 (通用版)\n");
    printf(" AArch64 语义自动定位 6 点, 打桩类别可自选; 免重签后台自动执行\n");
    printf(" 用法: 拖拽蓝厂 lk 镜像到本程序, 或命令行 <文件> [输出] [参考]\n");
    printf(" QQ 交流群: 2167063739\n");
    printf("============================================================\n");
    for(size_t i=0;i<paths.size();i++)
        if(paths[i].size()>=2&&paths[i].front()=='"'&&paths[i].back()=='"')paths[i]=paths[i].substr(1,paths[i].size()-2);
    if(paths.empty()){
        printf("请输入文件路径: ");fflush(stdout);
        char buf[4096];
        if(!fgets(buf,sizeof(buf),stdin)){press_enter();return 1;}
        std::string p=trim(buf);
        if(p.size()>=2&&p.front()=='"'&&p.back()=='"')p=p.substr(1,p.size()-2);
        if(p.empty()){printf("错误: 未输入文件路径\n");press_enter();return 1;}
        paths.push_back(p);
    }else{
        printf("批量处理 %u 个文件:\n",(unsigned)paths.size());
        for(size_t i=0;i<paths.size();i++)printf("  [%u] %s\n",(unsigned)(i+1),paths[i].c_str());
    }
    int cats=ask_categories();
    if(cats==CATS_FORGERY_ONLY)
        printf("已选: [隐藏 10886] 仅免重签(不打功能桩)\n");
    else if(cats==CATS_FORGE_BL2)
        printf("已选: [隐藏 10887] 仅免重签+bl2深刷(不打 lk 功能桩)\n");
    else if(cats==CATS_ALL_BL2)
        printf("已选: [隐藏 10888] 全部类别 + bl2 深刷\n");
    else
        printf("已选类别: %s%s%s\n",(cats&1)?"伪装回锁 ":"",(cats&2)?"去黄字 ":"",(cats&4)?"去写保护":"");
    int rc=0,ok=0;
    for(size_t i=0;i<paths.size();i++){
        std::string oa=paths.size()==1?out_arg:"";
        printf("\n==================== [%u/%u] %s ====================\n",
               (unsigned)(i+1),(unsigned)paths.size(),paths[i].c_str());
        if(process_one(paths[i],oa,ref_arg,cats)==0)ok++; else rc=1;
    }
    printf("\n[批次结果] 文件 %u/%u 成功, %u 失败",
           ok,(unsigned)paths.size(),(unsigned)(paths.size()-ok));
    if(cats==CATS_FORGERY_ONLY)printf("   [隐藏 10886: 仅免重签]");
    else if(cats==CATS_FORGE_BL2)printf("   [隐藏 10887: 仅免重签+深刷bl2(不打lk桩)]");
    else if(cats==CATS_ALL_BL2)printf("   [隐藏 10888: 全部类别 + bl2 深刷]");
    else if(cats==7)printf("   [全部类别(默认不含 bl2 深刷)]");
    else printf("   [类别: %s%s%s]",
                (cats&1)?"伪装回锁 ":"",(cats&2)?"去黄字 ":"",(cats&4)?"去写保护":"");
    printf("\n免重签 = 最终必做步骤: 无论选哪类, 每个被改动镜像的 cert2 都会重算哈希并写/刷新 90B 前置块(未改动则保持), 不改 cert1、不动原厂证书体。\n");
    printf("完成。\n");press_enter();
    return rc;
}
#ifdef _WIN32
int wmain(int argc,wchar_t**argv){
    std::vector<std::string>paths;std::string out_arg,ref_arg;
    for(int i=1;i<argc;i++){
        char buf[4096];
        if(WideCharToMultiByte(CP_UTF8,0,argv[i],-1,buf,(int)sizeof(buf),NULL,NULL)<=0)continue;
        std::string s=buf;
        if(paths.empty())paths.push_back(s);
        else if(out_arg.empty())out_arg=s;
        else if(ref_arg.empty())ref_arg=s;
        else paths.push_back(s);
    }
    return entry_point(paths,out_arg,ref_arg);
}
#else
int main(int argc,char**argv){
    std::vector<std::string>paths;std::string out_arg,ref_arg;
    for(int i=1;i<argc;i++){
        std::string s=argv[i];
        if(paths.empty())paths.push_back(s);
        else if(out_arg.empty())out_arg=s;
        else if(ref_arg.empty())ref_arg=s;
        else paths.push_back(s);
    }
    return entry_point(paths,out_arg,ref_arg);
}
#endif
