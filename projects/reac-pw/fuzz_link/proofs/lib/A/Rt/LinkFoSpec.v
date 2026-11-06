(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the contract of fmemopen(g_said, 4096, "w") as
   mark_quietly calls it (0x88410 `jal 0x430a8`, a0 = g_said 0x62fee0, a1 = 4096, a2 = "w" 0x21260; then
   0x88414 `sd a0, g_sink`, 0x88418 `beqz a0` to the abort).

   The shape is pcap's afmemopen_spec (libreac/fuzz_pcap lib/A/Stdio/PFmemopenISpec.v, origin/ossv/recipes; its
   relocated copy is (internal path) (internal record, sha256 7f1ad5eb0b04)), the form of
   cgif's YE01.v afopen_spec: afn_pre with a stack window, the caller's frame chain in CTX, the universe rows of the one
   malloc, the event, live-byte and meter room of one AMF_BLOCK request; the post an SRr over ajournal with the
   footprint [sink_token], one allocator event, mo_le, the descriptors and the file system kept, 4096 <= res, res mod
   16 = 0 and the block list grown by (res, AMF_BLOCK). What is link's: the "w" arm of musl's fmemopen, and the stream
   in the vocabulary of LinkMfDefs.v (amf_k, amf_dyn over the frame's amemfile_at, AMemFileSink.v), so the callers of
   the print path see one FILE. ONE statement at two entries: afmemopen_w_spec CTX pc ... holds at pc = LA_W_FMEMOPEN
   0x430a8 (the wrapper's 4-byte jump, the top lemma) and at pc = LA_FMEMOPEN 0x96a1c (musl fmemopen, where the
   wrapper's tail jump arrives with the same sp, ra, a0..a2 and callee-saved registers).

   THE CODE (listings link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST), image A):
   - 0x430a8 `j 0x48024`; ___interceptor_fmemopen 0x48024 (20 instructions): frame 32, jal TryAsanInitFromRtl 0x5b214
     (frame 16; returns at once: asan_inited is 1, the AR const law), loads REAL(fmemopen) from the cell 0xa3780 (image
     value 0x96a1c, AMemFile.v link_amf_real_fmemopen), restores a0..a2, ra, s0..s2, pops its frame (+0x48) and
     `jr t1` (+0x4c): a tail jump, so musl fmemopen returns to the caller's ra.
   - musl fmemopen 0x96a1c (464 bytes, frame 48):
     +0x28..+0x30 strchr(mode, '+') through the strchr wrapper 0x43054 (`j 0x44118`, ___interceptor_strchr, which
       calls REAL(strchr) through the cell 0xa36e8 = 0x9b0a0, musl strchr -> __strchrnul 0x9b0dc): 0 for "w";
     +0x34 `lbu a1, 0(s3)` mode[0] = 'w'; +0x3c/+0x40 a0 = "rwa" 0x20291; +0x44 strchr("rwa", 'w') = 0x20292;
     +0x48 `beqz a0` not taken (the EINVAL arm +0x60 is not reached); +0x4c `bnez s1` taken (buf = g_said <> 0; the
       size sign test +0x50 and the ENOMEM arm are not reached); +0x90 `beqz s1` not taken;
     +0x94/+0x98 malloc(0x518 = AMF_BLOCK) through the wrapper 0x540cc; its return address +0x9c = 0x96ab8 is ra;
       +0x9c `bnez a0` taken: the NULL arm +0xa0 (`j` to the zero return) is dead under the room premises, by the
       frame's malloc rule (Reusable/YC5d.v amalloc04_rule: 4096 <= res whenever its room premises hold), as pcap's
       header explains;
     +0xbc memset(f, 0, 0x110 = AMF_ZEROED) through the wrapper 0x52d70 (the AsanAPI's aa_memset_icpt);
     +0xc0..+0xe0 the stores of AMemFile.v amf_fm (cookie +152, buf +88, buf_size +96, fd +120, lbf +144);
     +0xe4 `bnez s1` taken (no buf2 memset); +0xfc/+0x100 c.size = 4096, c.buf = g_said; +0x104/+0x108 c.mode =
       mode[0] = 119; +0x10c `bnez s4` not taken (no '+'); +0x110..+0x118 mode[0] <> 'r', so +0x11c a0 = 4 and +0x128
       flags = F_NORD (AF_NORD); +0x12c..+0x13c mode[0] is neither 'a' nor 'r', so +0x160 `beqz s4` taken: c.len
       stays 0 (memset) and g_said is neither read (no strnlen) nor written (no `sb zero, 0(s1)`);
     +0x168..+0x19c read / write / seek / close = mread / mwrite / mseek / mclose; +0x18c `lbu` __libc.threaded = 0,
       so +0x1a8 lock = -1; +0x1b0..+0x1c8 pops its frame, +0x1cc `j 0x971d0` tail jump to __ofl_add with a0 = f.
   - __ofl_add 0x971d0 (frame 16): jal __ofl_lock 0x97194 (frame 16; jal __lock 0x9b4d4, which returns at once:
     +0x4 `lb` __libc.need_locks = 0, +0x8 `beqz` to the `ret` +0x1f8; returns &head), +0x14 `ld` old head (0),
     +0x18 f->next = old head, +0x24 head = f, jal __ofl_unlock 0x971c4 (`j` __unlock 0x9b75c: the lock word is 0, not
     negative, so nothing is stored), returns f.
   So the stores are: [sp - 48, sp) (the wrapper and TryAsanInitFromRtl), [sp - 48, sp) again (musl fmemopen), the
   windows of its callees below it, the fresh block's first AMF_ZEROED bytes (amf_fm, the plain mf_state's stores), and
   the open-file list head. The block's bytes past AMF_ZEROED (the ungetc slack and the 1024-byte buffer at +280) are
   as the malloc left them: no clause states them, because nothing reads them before writing (__fwritex /
   printf_core write the buffer at wpos, and mwrite copies only the k pending bytes, amf_pend in LinkMfDefs.v).

   THE PREMISES, each with the instructions that need it:
   - amf_head_law MS (AMemFileSink.v): the head the journal spares (YCbq.v AOFL_HEAD = sk_ofl_head) is the head
     __ofl_add stores (+0x24), as pcap's `as_ofl_head K = AOFL_HEAD`;
   - afn_pre at AFMW_STK (YCbq.v): AR, ra, gp, tp, the stack window, the chain; AFMW_STK = 48 + ASTACK, see below;
   - In (spine ch) CTX and the two universe rows: the malloc call +0x98 records ra :: the chain s0 heads (fmemopen
     does not write s0 before it, +0x08 saves it, +0xb0 first writes it; the wrapper restores s0 and ra before its
     tail jump), the donor's callee form (pcap's spec, cgif A/ACeb.v:29-39);
   - a0 = amf_buf MS, a1 = amf_size MS, a2 = LA_MODE_W: fmemopen +0x24 / +0x20 / +0x1c keep them in s1 / s2 / s3;
   - val_mem (rd W mem) LA_MODE_W 8 119: the 8-byte word at the mode string, "w\0" and the six 0 bytes of its ASan
     global's redzone (0x21260 is an asan global of size 2; the image holds 77 00 00 00 00 00 00 00). __strchrnul reads
     the aligned word (+0x44 `ld a4, 0(a0)`) and then the bytes (+0xc0 `lbu`), strchr reads *r (+0x14), the wrapper's
     internal_strlen reads "w\0" (strchr returned 0), fmemopen reads mode[0] at +0x34, +0x104, +0x110, +0x12c;
   - garr8 (rd W mem) LA_RWA "rwa\0": musl's mode-set literal (+0x3c/+0x40); __strchrnul reads 'r' and 'w'
     (+0x20 `lbu`, the address is not 8-aligned), strchr reads *r = 'w' (pcap's asrc_stdio_env carries the same bytes);
   - the window [mc_lo, mc_hi) holds the image's bytes: __strchrnul's two word constants (+0x40 `ld` 0x10378 =
     0x0101010101010100, +0x4c `ld` 0x10360 = 0x8080808080808080), read in the strchr(mode, '+') call; AR does not pin
     them (pcap's mc_lo / mc_hi premise; cgif A/AE39.v mconsts_view's body; link's window is [0x10360, 0x10380));
   - amf_env MS (rd W mem): __libc.threaded = 0 (+0x18c, lock = -1), __libc.need_locks = 0 (__lock +0x4, early return),
     ofl_lock = 0 (__unlock stores nothing; the post's amf_env);
   - val_mem (rd W mem) (amf_ofl_head MS) 8 0: the list is empty (the first mark: mark_quietly calls fmemopen only
     when g_sink is 0, and g_sink, g_say and the head move together, AMemFileSink.v amf_gi's first arm), so
     f->next = 0 (__ofl_add +0x14 / +0x18) and amemfile_at's next field holds;
   - st_nev S + 1 <= EV_MAX, blocks_bytes S + AMF_BLOCK <= LIVE_MAX, mo_ok MT S (mo_malloc MT AMF_BLOCK): the room
     premises of the frame's malloc rule for the call +0x98 (0 <= AMF_BLOCK < MALLOC_MAX needs no premise,
     AMemFile.v amf_block_size_ok).
   No premise on g_said's bytes or shadow: mode "w" reads nothing of it and writes nothing there (the caller states
   them for mwrite, LinkMfDefs.v amf_buf_ok). No AddrHashMap / meta premise: the wrapper and the strchr wrapper's
   taken path touch none (pcap's spec header).

   THE STACK. AFMW_STK = 48 + ASTACK = 16432: musl fmemopen's frame of 48 plus the allocator's budget for the call
   +0x98 at offset -48 (amalloc04_rule asks ASTACK - o <= STK); it bounds every other use, all at the same entry sp:
   the wrapper's 32 + TryAsanInitFromRtl's 16 (popped before the tail jump), 48 + the memset wrapper's ESTACK (4096),
   48 + the strchr wrapper's measured run (0x7f0 + 0x70 = 2144, strchr 16, __strchrnul 16: 2176; pcap A/AE2j.v
   SC_WIN), and __ofl_add's 16 + __ofl_lock's 16 after the pop. pcap keeps cgif's AFOPEN_STK 18624 with slack; link's
   window is the bound itself, so mark_quietly's K is 32 + AFMW_STK.

   THE POST, in LinkMfDefs.v's vocabulary: amf_k MS (rd W' mem') res 0 (amemfile_at with the window empty), amf_dyn
   MS (rd W' mem') res AF_NORD 0 0 0 0 0 0 (flags F_NORD, orientation 0, wend / wpos / wbase 0, cookie pos 0 and
   len 0), the head = res, and amf_env (the lock word is 0 again); and the depot's wild part does not grow (YG01.v
   wild_part over as_universe B): the one malloc records ra :: the chain's spine (or [pc0]), a fixed row of the
   universe by the premises above, so no wild trace is added (asked by mark_quietly's walk for its LedPost; the walk
   takes the malloc through lib/A/Rt/LinkMallocDepot.v amalloc04_rule_d). The plain twin is lib/Prog/fmemopen_c.v
   fmemopen_w_contract (memfile_k mem' h 0, mf_dyn mem' h F_NORD 0 0 0 0 0 0, ofl_one, stdio_ok); its proof does not
   carry over (link-a/plan/common-printf.md (internal record, sha256 baa75a923376), "The plain side").

   This file is the statement only. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK18 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* musl's mode-set literal "rwa\0" (fmemopen +0x3c auipc a0,0xfff8a; +0x40 addi a0,a0,-0x7c7) *)
Definition LA_RWA : Z := 0x20291.
(* the return address of fmemopen's malloc call (+0x98 jal 0x540cc; +0x9c) *)
Definition LA_FM_MALLOC_RA : Z := 0x96ab8.
(* fmemopen's frame (+0x00 addi sp,sp,-0x30) plus the allocator's stack budget (YC5d.v amalloc04_rule) *)
Definition AFMW_STK : Z := 48 + ASTACK.
(* the footprint: the sink token alone, so the journal spares the open-file list head (YCbq.v fp_spares) *)
Definition afmemopen_w_fp : list (Z * Z) := [YI16.sink_token].
(* the bytes of "rwa\0" *)
Definition rwa_Z : list Z := [114; 119; 97; 0].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ajournal is stated under the frame's sink-head class; it is passed explicitly (link_asink_head), as pcap's. *)
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MS : amemfile_syms.
Variable MT : ameter_ops.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The premises over the argument registers and the bytes at the call (the witness's object, LinkFoWitness.v):
   the arguments, the mode word, "rwa\0", __strchrnul's constant window, the stdio words and the empty list. *)
Definition afm_w_args (mc_lo mc_hi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = w64 (amf_buf MS) /\ getr regs 11 = w64 (amf_size MS) /\ getr regs 12 = w64 LA_MODE_W /\
  val_mem segs m LA_MODE_W 8 119 /\
  garr8 segs m LA_RWA rwa_Z /\
  (forall a, mc_lo <= a < mc_hi ->
     amf_rd segs m a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) /\
  amf_env segs MS m /\
  val_mem segs m (amf_ofl_head MS) 8 0.

(* The whole precondition at an entry: pcap's afmemopen_spec premises in its order, the stream clause replaced. *)
Definition afm_w_pre (CTX : list (list Z)) (ra mc_lo mc_hi : Z) (ly : alayout) (S : astate) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
  @amf_head_law SK MS /\
  afn_pre segs B AFMW_STK ly S W regs mem md ch /\
  In (spine ch) CTX /\
  afm_w_args mc_lo mc_hi regs (rd W mem) /\
  st_nev S + 1 <= EV_MAX /\ blocks_bytes S + AMF_BLOCK <= LIVE_MAX /\
  mo_ok MT S (mo_malloc MT AMF_BLOCK) /\
  In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (ra :: c))) (as_universe B)).

(* The post: the return to ra with res in a0, the journal from the entry (one event, the token footprint), the
   callee-saved registers, the side stack, the meter, the descriptors and the file system, the fresh block appended,
   link's memory FILE at res with an empty window, linked as the list's one FILE, and no new wild trace. *)
Definition afm_w_post (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (res : Z),
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal segs B AFMW_STK (spZ regs) afmemopen_w_fp ly S W mem md [] ly' S' W' mem' md' 1 /\
    aregs_preserved regs regs' /\ getr regs' 10 = w64 res /\ frames S' = frames S /\
    mo_le MT S S' (mo_malloc MT AMF_BLOCK) /\
    m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
    4096 <= res /\ res mod 16 = 0 /\
    ablocks B ly' S' = ablocks B ly S ++ [(res, AMF_BLOCK)] /\
    amf_k segs MS (rd W' mem') res 0 /\
    amf_dyn segs MS (rd W' mem') res AF_NORD 0 0 0 0 0 0 /\
    val_mem segs (rd W' mem') (amf_ofl_head MS) 8 res /\
    amf_env segs MS (rd W' mem') /\
    (length (wild_part (as_universe B) (st_depot S')) <= length (wild_part (as_universe B) (st_depot S)))%nat.

(* pc: the entry (LA_W_FMEMOPEN for the callers; LA_FMEMOPEN inside the walk); ra: the malloc call's return address
   (LA_FM_MALLOC_RA); [mc_lo, mc_hi): __strchrnul's constant window (AE39.v MC_LO / MC_HI = 0x10360 / 0x10380). *)
Definition afmemopen_w_spec (CTX : list (list Z)) (pc ra mc_lo mc_hi : Z) : Prop :=
  forall W ly S regs mem md ch,
  afm_w_pre CTX ra mc_lo mc_hi ly S W regs mem md ch ->
  SRr segs W (cfg_at segs pc regs mem md) (afm_w_post regs ly S W mem md).

End a.

(* SK is EXPLICIT for every user of the spec (pcap's ruling for afmemopen_spec): link's head is link_asink_head
   (AMemFile.v), and no global sink_head instance may stand in for it. afm_w_pre / afm_w_post keep it implicit; their
   users pass it by name, (SK := link_asink_head). *)
Arguments afmemopen_w_spec {fx rc} SK.
Check (fun fx rc (SK : YI16.sink_head) => afmemopen_w_spec (fx:=fx) (rc:=rc) SK).
