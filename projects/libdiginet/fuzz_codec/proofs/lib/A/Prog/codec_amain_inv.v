(* The boundary layer of the image-A walk of LLVMFuzzerTestOneInput (fuzz_codec.asan, entry 0x8084c, 2758
   instructions, real frame 288 realigned to 32, and a side-stack frame of class 3 of 448 bytes taken at 0x808bc):
   one predicate per cut of the listing, the statement of each segment lemma, the composition of the segments
   into one walk from the entry to the return, and the step from that walk to the A-level contract
   codec_lib_contract_x of lib/A/Prog/CPgMainC.v.

   Shape. A cut is a `world tfibsegs -> config -> Prop`, the form of an SRr post-condition: `mcut g pos sp1 kv pc P`
   says the run is at pc, the journal from the entry state g holds with the entry's own side-stack frame (3, pos)
   as its `own`, the facts every cut after the prologue shares hold (mcommon), and P holds of the state. A segment
   is `forall ..., <start cut> W2 c2 -> SRr tfibsegs W2 c2 <end cuts>`; each is proved in its own file, from the
   Section hypotheses its file names (the kit's laws, the runtime contracts, the callee contracts).

   The frame (F = frame_addr (e_ly g) 3 pos, 64-aligned; offsets from F):
     +32 SCRIBBLE's 10-byte payload pl (owe(), fuzz_codec.c:214; shadow bytes 4, 5 = 00 02 at 0x82854 / 0x8285c,
     f8 f8 again at 0x82918 / 0x8291c), +64 char text[65], +176 struct call k (184 bytes, fuzz_codec.c:74-90),
     +432 the dots byte of COUNTER_TEXT, +504 the flag address the frame request writes.
   Its 56 shadow bytes from shadow_addr F (0x808f4-0x80a14): f1 x4 | f8 f8 | f2 f2 | 00 x8 01 | f2 x5 | k x23 |
   f2 x9 | f8 | f3, with k's 23 bytes f8 (marked unusable) outside the loop body and 00 (marked usable) inside it
   (0x80af4-0x80b4c marks them usable, 0x8275c-0x827b8 unusable again).
   The machine frame (sp1 = 32 * ((sp0 - 288) / 32), 0x8084c / 0x8088c): the spills 16(sp1) .. 120(sp1) written
   once at 0x80a20-0x80ab8, struct fuzz_in at 152(sp1) (in.p) and 160(sp1) (in.n), the thirteen saved words at
   sp0 - 104 .. sp0 - 8 (0x80854-0x80884); inside OWE9, 8(sp1) holds s3 (0x8284c / 0x82924); inside OWE10,
   174(sp1) .. 183(sp1) hold COUNTER's pl[10] (0x82658-0x8269c); both are below sp0 - 104 and away from 16 .. 127
   and 152 .. 167.
   Registers at every cut after the prologue (set at 0x80888-0x80a98, kept by every callee): sp = s1 = sp1,
   s0 = sp0, s2 = shadow_addr F, s3 = F + 432, s4 = SHADOW_OFF, s5 = -8, s6 = F + 176, s9 = F + 64, s11 = 10,
   s10 = ops (the loop counter).

   The cuts (pc, the measured listing of the plan's segment table):
     HEAD 0x80abc (loop head); RDk = the switch table at 0x20eac, entry k (k = 0..13), RD14 = 0x81208 (MASKS);
     RUN 0x820d0 (the readers' common tail: kind loaded, run()'s switch; seg-A.txt starts RUN at 0x820d8 and counts
     0x820d0-0x820d4 in each of RD0..RD11); ENCk = run()'s table at 0x20ee4, entry k (k = 0..10), ENC11 = 0x821f4
     (SYSEX); JOIN 0x8220c (the encoder returned; seg-A.txt starts OWEH at 0x82214); OWEk = owe()'s table at 0x20f10,
     entry k (k = 0..10), OWE11 = 0x827c8; CHK 0x8273c (the three record checks); LATCH 0x8275c (k marked unusable,
     ops + 1, the ops test); EXIT 0x82f94 (frame release and epilogue).
   The content of k at each cut is the plain walk's (lib/Prog/codec_main_inv.v of the plain branch): the record
   HEAD leaves, the readers' ranges, the encoder's output, owe()'s answer; the plain agreement lemmas of
   lib/Prog/codec_agree.v (agree_all, refusal, enc_fail_none, owe_ok_wf) refute the checks' abort branches. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACeh ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ================================ image A: the entry function's own constants ================================
   Read from the pinned image (sha256 7d470194ffdb...): DESK holds the three ints 0, 1, 2; SPEC_DESK holds the three
   pointers 0, 0x9d6a0 (SPEC_C24), 0x9d6c0 (SPEC_PC). The personality table and the read window are CPgWalk's
   CA_PERS / CA_RLO / CA_RHI. *)
Definition CM_DESK : Z := 0x20f40.
Definition CM_SPEC_DESK : Z := 0x9d660.
Definition CM_SPEC_C24 : Z := 0x9d6a0.
Definition CM_SPEC_PC : Z := 0x9d6c0.

(* The callees' entries (the `jal` targets of the listing). *)
Definition AM_check_pers : Z := 0x83364.
Definition AM_pers_of : Z := 0x84888.
Definition AM_text_arg : Z := 0x835d4.
Definition AM_check_seg7 : Z := 0x83ae4.
Definition AM_check_text_counter : Z := 0x83b5c.
Definition AM_owed_counter_text : Z := 0x83df8.
Definition AM_check_text_scribble : Z := 0x83798.
Definition AM_check_masks : Z := 0x842b0.
Definition AM_check_refusal : Z := 0x844dc.
Definition AM_check_range : Z := 0x84590.
Definition AM_check_bytes : Z := 0x84640.
Definition AM_fader : Z := 0x84ba8.
Definition AM_button : Z := 0x84d5c.
Definition AM_touch : Z := 0x84eb8.
Definition AM_vpot : Z := 0x8502c.
Definition AM_jog : Z := 0x85190.
Definition AM_sysex : Z := 0x848b4.
Definition AM_ring : Z := 0x85314.
Definition AM_meter : Z := 0x85600.
Definition AM_sleds : Z := 0x85834.
Definition AM_cleds : Z := 0x85a7c.
Definition AM_scribble : Z := 0x85e24.
Definition AM_counter : Z := 0x86608.
(* The runtime entries the walk calls besides lib/A/AF0l.v's Tfib_code ones (pc_stack_malloc 3 = 0x3d400,
   pc_asan_memset 0x51e34, pc_asan_memcpy 0x51998): the shadow fill with 0xf5 the frame release calls at 0x82fd8. *)
Definition AM_set_shadow_f5 : Z := 0x54960.

(* ================================ the cuts' pcs ================================ *)
Definition PC_HEAD : Z := 0x80abc.
(* the switch table at 0x20eac (entries 0..13, read from the pinned image) and the MASKS default *)
Definition rd_pc (kind : Z) : Z :=
nth (Z.to_nat kind) [0x80c34; 0x80f68; 0x80e30; 0x80e98; 0x80d08; 0x80fd0; 0x8109c; 0x80f00; 0x811a0; 0x80dc8;
0x81104; 0x80c9c; 0x80d70; 0x81038; 0x81208] 0.
Definition PC_RUN : Z := 0x820d0.
(* run()'s table at 0x20ee4 (entries 0..10) and the SYSEX default *)
Definition enc_pc (kind : Z) : Z :=
nth (Z.to_nat kind) [0x820f4; 0x82194; 0x8214c; 0x82164; 0x8213c; 0x821ac; 0x821c4; 0x8217c; 0x821e0; 0x8210c;
0x82124; 0x821f4] 0.
Definition PC_JOIN : Z := 0x8220c.
(* owe()'s table at 0x20f10 (entries 0..10) and the SYSEX default *)
Definition owe_pc (kind : Z) : Z :=
nth (Z.to_nat kind) [0x82268; 0x82438; 0x82378; 0x823cc; 0x822f0; 0x82488; 0x82580; 0x82414; 0x8270c; 0x8230c;
0x82618; 0x827c8] 0.
Definition PC_CHK : Z := 0x8273c.
Definition PC_LATCH : Z := 0x8275c.
Definition PC_EXIT : Z := 0x82f94.

(* ================================ the frame's shadow ================================ *)
Definition SH_F1 : Z := 0xf1.
Definition SH_F2 : Z := 0xf2.
Definition SH_F3 : Z := 0xf3.
Definition SH_F8 : Z := 0xf8.
(* the 56 shadow bytes of the frame, with k's 23 bytes kv (0xf8 outside the loop body, 0 inside it) *)
Definition shm (kv : Z) : list Z :=
[SH_F1; SH_F1; SH_F1; SH_F1; SH_F8; SH_F8; SH_F2; SH_F2; 0; 0; 0; 0; 0; 0; 0; 0; 1; SH_F2; SH_F2; SH_F2; SH_F2; SH_F2]
++ repeat kv 23 ++ repeat SH_F2 9 ++ [SH_F8; SH_F3].

(* ================================ the call record over Z ================================
   The plain walk's record facts (lib/Prog/codec_main_inv.v: k_rd, pd_ok, enc_k, owe_k, rdr_k, rec_ok,
   owe_want_ok) restated over lib/A/Prog/CPgBase.v's kcallZ. *)
Definition fa5 : list Z := repeat 0xa5 32.
(* k as HEAD leaves it: memset to 0 (0x80b5c), kind stored (sw, 0x80b94), p and desk stored (0x80bcc, 0x80bf8),
   before and out memset to 0xa5 (0x80c08). *)
Definition k_rdZ (kind pv dv : Z) : kcallZ :=
mkKcallZ kind pv dv 0 0 0 0 (repeat 0 24) 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
(* k.p and k.desk as HEAD sets them from DESK[op / 15 % 3] (and RD12 / RD13 when k.p is NULL): NULL, or the
   personality and spec desk of Control|24, or of ProControl; od the desk both describe. *)
Definition pd_okA (pv dv : Z) (od : option desk) : Prop :=
(pv = 0 /\ dv = 0 /\ od = None) \/
(pv = CA_PERS /\ dv = CM_SPEC_C24 /\ od = Some c24) \/
(pv = CA_PERS + 24 /\ dv = CM_SPEC_PC /\ od = Some pc).
(* the library call run() makes for k, owe()'s answer for k, and the readers' ranges *)
Definition enc_kZ (k : kcallZ) (od : option desk) : Z * option cmd :=
enc_of_call (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k).
Definition owe_kZ (k : kcallZ) (od : option desk) : Z * cmd :=
owe_spec (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k).
Definition rdr_kZ (k : kcallZ) : Prop :=
reader_ok (kz_kind k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k).
(* the record run() is called with: a kind it handles, the personality pair, the readers' ranges, before and out
   0xa5^32 *)
Definition enc_okZ (k : kcallZ) (od : option desk) : Prop :=
0 <= kz_kind k <= 11 /\ pd_okA (kz_p k) (kz_desk k) od /\ rdr_kZ k /\ kz_before k = fa5 /\ kz_out k = fa5.
(* the record after run(): out is what the encoder wrote over 0xa5^32 *)
Definition rec_okZ (k : kcallZ) (od : option desk) : Prop :=
0 <= kz_kind k <= 11 /\ pd_okA (kz_p k) (kz_desk k) od /\ rdr_kZ k /\ kz_before k = fa5 /\
kz_out k = cmd_outZ fa5 (snd (enc_kZ k od)).
(* the want fields after owe(): want_rc its code; on success want[0..len), want_len, want_key, want_display its
   command; on failure want_len = want_key = want_display = 0 *)
Definition owe_want_okZ (k : kcallZ) (od : option desk) : Prop :=
kz_want_rc k = fst (owe_kZ k od) /\
(if fst (owe_kZ k od) =? 0 then
   let '(bs, key, dp) := snd (owe_kZ k od) in
   kz_want_len k = Z.of_nat (length bs) /\ firstn (length bs) (kz_want k) = map u8 bs /\
   kz_want_key k = key /\ kz_want_display k = dp
 else kz_want_len k = 0 /\ kz_want_key k = 0 /\ kz_want_display k = 0).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of the contract (lib/A/Prog/CPgMainC.v), at image A's segments and constants. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.

(* ---- the entry state the whole walk is relative to ---- *)
Record ectx : Type := mkEctx {
e_ly : alayout; e_S : astate; e_W : world tfibsegs; e_mem : word -> option byte; e_md : Model;
e_regs : bvmap 5 word; e_p : Z; e_n : Z; e_pl : list byte; e_M : Z }.
Definition e_sp0 (g : ectx) : Z := spZ (e_regs g).
(* the entry's class-3 frame; frame_addr reads ly_F only, which layout_le keeps *)
Definition FA (g : ectx) (pos : Z) : Z := frame_addr (e_ly g) 3 pos.
(* the contract's pre-condition at the entry state (lib/A/Prog/CPgMainC.v), as one name *)
Definition e_pre (g : ectx) : Prop :=
codec_lib_pre_x tfibsegs B MT K XM_LIB CA_RLO CA_RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK
(e_regs g) (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) (e_pl g) (e_M g).

(* ---- what every cut after the prologue carries ---- *)
Definition mcommon (g : ectx) (pos sp1 kv : Z) (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
e_pre g /\
(* the machine frame: 0x8084c addi sp,sp,-288; 0x8088c andi sp,sp,-32; 0x80890 mv s1,sp; 0x80888 addi s0,sp,288 *)
sp1 = 32 * ((e_sp0 g - 288) / 32) /\
getr regs2 2 = w64 sp1 /\ getr regs2 9 = w64 sp1 /\ getr regs2 8 = w64 (e_sp0 g) /\
getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
(* 0x808ac s4 = the shadow offset; 0x80900 + 0x8092c s2 = shadow_addr F; 0x80908 s5 = -8; 0x80a30 s6 = k;
   0x80a48 s9 = text; 0x80a4c s3 = the dots byte; 0x80a98 s11 = 10 *)
getr regs2 20 = w64 SHADOW_OFF /\ getr regs2 18 = w64 (shadow_addr (FA g pos)) /\ getr regs2 21 = w64 (-8) /\
getr regs2 22 = w64 (FA g pos + 176) /\ getr regs2 25 = w64 (FA g pos + 64) /\
getr regs2 19 = w64 (FA g pos + 432) /\ getr regs2 27 = w64 10 /\
(* the frame is 64-aligned (lib/A/ACem.v frame_al64), as lib/A/Prog/CPgSat.v's object lemmas take it *)
FA g pos mod 64 = 0 /\
(* the spills, 0x80a20-0x80ab8 (k = F + 176) *)
val_mem tfibsegs (rd W2 mem2) (sp1 + 16) 8 (FA g pos + 176 + 47) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 24) 8 (FA g pos + 34) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 32) 8 (FA g pos + 32) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 40) 8 (FA g pos + 176 + 144) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 48) 8 0x5cb0 /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 56) 8 (FA g pos + 176 + 148) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 64) 8 (FA g pos) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 72) 8 (FA g pos) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 80) 8 0x13f0 /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 88) 8 (FA g pos + 176 + 40) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 96) 8 (FA g pos + 176 + 108) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 104) 8 (FA g pos + 176 + 168) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 112) 8 CM_DESK /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 120) 8 (FA g pos + 176 + 76) /\
(* the thirteen saved words, which the epilogue restores (0x80854-0x80884, 0x830d0-0x83100) *)
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 8) 8 (raZ (e_regs g)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 16) 8 (bv_unsigned (getr (e_regs g) 8)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)) /\
(* the flag address the frame request wrote at F + 504, which the release reads (0x82fdc) *)
val_mem tfibsegs (rd W2 mem2) (FA g pos + 504) 8 (flag_addr (e_ly g) 3 pos) /\
(* the frame's 56 shadow bytes *)
(forall i, 0 <= i < 56 ->
 aview tfibsegs (w_H W2) mem2 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm kv) 0)) /\
(* the input bytes (the journal keeps them: this walk's footprint is empty) and the heap blocks *)
garr8 tfibsegs (rd W2 mem2) (e_p g) (map (fun b : byte => bv_unsigned b) (e_pl g)) /\
Permutation (ablocks B ly2 S2) (ablocks B (e_ly g) (e_S g)).

(* A cut: at pc, with the journal from the entry state and the entry's own frame. *)
Definition mcut (g : ectx) (pos sp1 kv pc : Z)
(P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k,
c2 = cfg_at tfibsegs pc regs2 mem2 md2 /\
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
ly2 S2 W2 mem2 md2 k /\
frames S2 = [(3, pos)] /\ 0 <= k <= EV_LIB /\ mo_le MT (e_S g) S2 0 /\
mcommon g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 /\
P ly2 S2 W2 regs2 mem2 md2.

(* the input cursor struct fuzz_in at 152(sp1): c bytes taken (0x80a44, 0x80a50 and every reader) *)
Definition cur_at (g : ectx) (sp1 c : Z) (W2 : world tfibsegs) (mem2 : word -> option byte) : Prop :=
0 <= c <= e_n g /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 152) 8 (e_p g + c) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 160) 8 (e_n g - c).
(* the loop counter s10 (0x80a40 li s10,0; 0x827ac addiw s10,s10,1) *)
Definition ops_at (ops : Z) (regs2 : bvmap 5 word) : Prop :=
0 <= ops <= 255 /\ getr regs2 26 = w64 ops.
(* the call record at k = F + 176 *)
Definition k_at (g : ectx) (pos : Z) (k : kcallZ) (W2 : world tfibsegs) (mem2 : word -> option byte) : Prop :=
kcall_atA tfibsegs W2 mem2 (FA g pos + 176) k /\ kcall_wfZ k.

(* ================================ the cuts ================================ *)
(* the entry: the contract's state, before the frame exists *)
Definition inv_entry (g : ectx) : world tfibsegs -> config -> Prop :=
fun W2 c2 => W2 = e_W g /\ c2 = cfg_at tfibsegs A_LLVMF (e_regs g) (e_mem g) (e_md g).

(* HEAD 0x80abc: ops passes done (ops < 256), c input bytes taken; k marked unusable, its bytes any. *)
Definition inv_head (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 SH_F8 PC_HEAD (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ exists c, cur_at g sp1 c W2 mem2).

(* RDk, the reader of kind k: the op byte taken (in.n was not 0), k marked usable and set as HEAD sets it;
   s7 = k.p (0x80bc8), which RD12 / RD13 test. *)
Definition inv_rd (g : ectx) (pos sp1 ops kind : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 (rd_pc kind) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= kind <= 14 /\
exists c pv dv od, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ pd_okA pv dv od /\ getr regs2 23 = w64 pv /\
k_at g pos (k_rdZ kind pv dv) W2 mem2).

(* RUN 0x820d0: a reader of kinds 0..11 is done; k is the record run() is called with. *)
Definition inv_run (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_RUN (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ enc_okZ k od).

(* ENCk: run()'s call of the encoder of kind k (from RUN, and from RD12 / RD13 with kind 9 / 10). *)
Definition inv_enc (g : ectx) (pos sp1 ops kind : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 (enc_pc kind) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= kind <= 11 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ enc_okZ k od /\ kz_kind k = kind).

(* JOIN 0x8220c: the encoder returned its code in a0, out holds what it wrote. *)
Definition inv_join (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_JOIN (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
getr regs2 10 = w64 (fst (enc_kZ k od))).

(* OWEk: owe()'s case for kind k, past its common part (0x8220c-0x82264): k.rc = the encoder's code
   (0x82214), want_rc = 0 (0x82234 / 0x822d4) and want_len = want_key = want_display = 0 (the memset at
   0x82244 / 0x822e4), the desk test passed (a NULL desk only for BUTTON, JOG, SYSEX: the mask 0x812 at
   0x82224), s7 = k.desk (0x82210). *)
Definition inv_owe (g : ectx) (pos sp1 ops kind : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 (owe_pc kind) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= kind <= 11 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\ kz_kind k = kind /\
(od = None -> kind = 1 \/ kind = 4 \/ kind = 11) /\
kz_rc k = fst (enc_kZ k od) /\
kz_want_rc k = 0 /\ kz_want_len k = 0 /\ kz_want_key k = 0 /\ kz_want_display k = 0 /\
getr regs2 23 = w64 (kz_desk k)).

(* CHK 0x8273c: owe() done; k.rc the encoder's code, the want fields owe()'s answer. *)
Definition inv_chk (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_CHK (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
kz_rc k = fst (enc_kZ k od) /\ owe_want_okZ k od).

(* LATCH 0x8275c: the end of a pass (from CHK, from COUNTER_TEXT's refusal at 0x81098 and from MASKS at
   0x82a3c); k still marked usable, its bytes any. *)
Definition inv_latch (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_LATCH (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ exists c, cur_at g sp1 c W2 mem2).

(* EXIT 0x82f94: the loop is done (in.n = 0 at 0x80ac4, or 256 passes at 0x827c0). *)
Definition inv_exit (g : ectx) (pos sp1 : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 SH_F8 PC_EXIT (fun _ _ _ _ _ _ => True).

(* The return: the frame is released (own = []), a0 = 0, the callee-saved registers and the blocks kept, the
   meter not charged. lib/A/Prog/CPgMainC.v's post follows from it (amain_contract_of_walk). *)
Definition inv_retj (g : ectx) : world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k,
c2 = cfg_at tfibsegs RA_LLVMF regs2 mem2 md2 /\
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [] ly2 S2 W2 mem2 md2 k /\
0 <= k <= EV_LIB /\ aregs_preserved (e_regs g) regs2 /\ getr regs2 10 = w64 0 /\
Permutation (ablocks B ly2 S2) (ablocks B (e_ly g) (e_S g)) /\ mo_le MT (e_S g) S2 0.

(* ================================ the segment statements ================================
   Each is `start -> SRr tfibsegs W2 c2 end`. Each is proved in its own file, under Section hypotheses
   taken only from: the kit's laws (ameter_laws, ameter_fs_laws, TfibLib, AR_laws, model_laws, ro_tfa_below_ofl),
   the runtime contracts (astack_malloc_realizes .. 3, stack_malloc_progressP, astack_free_law,
   frame_flag_lawP, aintrin_realizes OSet 0x51e34 / OCpy 0x51998, aset_shadow_realizes AM_set_shadow_f5 0xf5),
   the start-up facts (globs_marked .. CODEC_GLOBS, img_shadow_vis), the string rows' freedom
   cpw_rows_free B CA_ROSTRS (lib/A/Prog/CPgWalkRo.v; the closing discharges it from TfibSyms B by
   cpw_rows_free_syms), and the A-level contracts of the callees
   at the AM_* entries and CPgWalk's CA_* instance. Lemmas a segment proof may use besides the kit's: ACeh.arodata_ok_journal
   (the read-only image kept along the journal) and lib/A/Prog/codec_amain_lem.v (the record and personality
   facts several segments share). This file does not move. *)

(* ENTRY 0x8084c-0x80ab8, 156 instructions: the prologue, the class-3 frame request (0x808bc) with its
   machine-stack fallback refuted (the use-after-return cell is 1, the request returns a frame at or above
   4096), the frame's description words and shadow map, the size test (0x80954 / 0x80a18, n < 2^26 by the
   pre-condition), check_personality (0x80a3c), the spills and the loop constants. *)
Definition seg_entry : Prop :=
forall g W2 c2, inv_entry g W2 c2 -> e_pre g ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists pos sp1, inv_head g pos sp1 0 W3 c3).

(* HEAD 0x80abc-0x80c30, 104 instructions: the in.n test (to EXIT when 0), the op byte, k marked usable, the
   memset of k, op % 15, diginet_personality_of(DESK[op / 15 % 3]), SPEC_DESK[op / 15 % 3], the memset of before
   and out, and the switch on the kind. *)
Definition seg_head : Prop :=
forall g pos sp1 ops W2 c2, inv_head g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => inv_exit g pos sp1 W3 c3 \/ exists kind, inv_rd g pos sp1 ops kind W3 c3).

(* RD0 .. RD11: the reader of the kind, to RUN. *)
Definition seg_rd_run (kind : Z) : Prop :=
forall g pos sp1 ops W2 c2, inv_rd g pos sp1 ops kind W2 c2 -> SRr tfibsegs W2 c2 (inv_run g pos sp1 ops).
(* RD12 SCRIBBLE_TEXT: k.p / k.desk set to Control|24 when NULL, k.a, text_arg, check_text_scribble, kind 9. *)
Definition seg_rd12 : Prop :=
forall g pos sp1 ops W2 c2, inv_rd g pos sp1 ops 12 W2 c2 -> SRr tfibsegs W2 c2 (inv_enc g pos sp1 ops 9).
(* RD13 COUNTER_TEXT: the dots byte marked usable, k.p / k.desk as RD12, text_arg, check_text_seg7,
   check_text_counter, owed_counter_text; on its refusal to LATCH, else kind 10 and k.b = dots. *)
Definition seg_rd13 : Prop :=
forall g pos sp1 ops W2 c2, inv_rd g pos sp1 ops 13 W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => inv_enc g pos sp1 ops 10 W3 c3 \/ inv_latch g pos sp1 ops W3 c3).
(* RD14 MASKS: the two readers, check_text_masks, to LATCH. *)
Definition seg_rd14 : Prop :=
forall g pos sp1 ops W2 c2, inv_rd g pos sp1 ops 14 W2 c2 -> SRr tfibsegs W2 c2 (inv_latch g pos sp1 ops).
(* RUN 0x820d0-0x820f0: the kind loaded and run()'s switch. *)
Definition seg_run : Prop :=
forall g pos sp1 ops W2 c2, inv_run g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists kind, inv_enc g pos sp1 ops kind W3 c3).
(* ENC0 .. ENC11: the arguments from k and the encoder call, to JOIN. *)
Definition seg_enc (kind : Z) : Prop :=
forall g pos sp1 ops W2 c2, inv_enc g pos sp1 ops kind W2 c2 -> SRr tfibsegs W2 c2 (inv_join g pos sp1 ops).
(* OWEH 0x8220c-0x82264, 0x822d4-0x822ec, 0x827d4-0x827dc: owe()'s common part; to OWEk, or to CHK with
   want_rc = -1 when the kind needs a desk and k.desk is NULL. *)
Definition seg_oweh : Prop :=
forall g pos sp1 ops W2 c2, inv_join g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => inv_chk g pos sp1 ops W3 c3 \/ exists kind, inv_owe g pos sp1 ops kind W3 c3).
(* OWE0 .. OWE11: owe()'s case for the kind, with the tails it runs through, to CHK. *)
Definition seg_owe (kind : Z) : Prop :=
forall g pos sp1 ops W2 c2, inv_owe g pos sp1 ops kind W2 c2 -> SRr tfibsegs W2 c2 (inv_chk g pos sp1 ops).
(* CHK 0x8273c-0x82758: check_refusal, check_range, and check_bytes when k.rc = 0. *)
Definition seg_chk : Prop :=
forall g pos sp1 ops W2 c2, inv_chk g pos sp1 ops W2 c2 -> SRr tfibsegs W2 c2 (inv_latch g pos sp1 ops).
(* LATCH 0x8275c-0x827c4: k marked unusable, ops + 1, to EXIT after 256 passes, else to HEAD. *)
Definition seg_latch : Prop :=
forall g pos sp1 ops W2 c2, inv_latch g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => (ops = 255 /\ inv_exit g pos sp1 W3 c3) \/
                                  (ops < 255 /\ inv_head g pos sp1 (ops + 1) W3 c3)).
(* EXIT 0x82f94-0x83108, 94 instructions: text marked unusable, the frame's first word retired, the frame's shadow
   filled with 0xf5 (0x82fd8) and its flag cleared (0x82fdc), the epilogue, a0 = 0, ret. *)
Definition seg_exit : Prop :=
forall g pos sp1 W2 c2, inv_exit g pos sp1 W2 c2 -> SRr tfibsegs W2 c2 (inv_retj g).

(* ================================ the composition ================================ *)
Lemma mcut_P : forall g pos sp1 kv pc P W2 c2, mcut g pos sp1 kv pc P W2 c2 ->
exists ly2 S2 regs2 mem2 md2, P ly2 S2 W2 regs2 mem2 md2.
Proof.
intros g pos sp1 kv pc P W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & k & _ & _ & _ & _ & _ & _ & HP).
exists ly2, S2, regs2, mem2, md2. exact HP.
Qed.

Lemma kind_split_14 : forall kind, 0 <= kind <= 14 ->
0 <= kind <= 11 \/ kind = 12 \/ kind = 13 \/ kind = 14.
Proof. intros kind Hk. lia. Qed.

(* The walk is the segments chained from the entry to the return. The loop is SRr_loop on 256 - ops: every
   pass from HEAD at ops reaches EXIT or HEAD at ops + 1. *)
Theorem amain_of_segments :
seg_entry -> seg_head -> (forall kind, 0 <= kind <= 11 -> seg_rd_run kind) -> seg_rd12 -> seg_rd13 ->
seg_rd14 -> seg_run -> (forall kind, 0 <= kind <= 11 -> seg_enc kind) -> seg_oweh ->
(forall kind, 0 <= kind <= 11 -> seg_owe kind) -> seg_chk -> seg_latch -> seg_exit ->
forall g W2 c2, inv_entry g W2 c2 -> e_pre g -> SRr tfibsegs W2 c2 (inv_retj g).
Proof.
intros hE hH hR hR12 hR13 hR14 hRun hEnc hOH hOw hC hL hX g W c HE HP.
eapply SRr_bind; [exact (hE g W c HE HP)|]. intros W1 c1 _ (pos & sp1 & H1).
assert (LOOP : forall ops W2 c2, inv_head g pos sp1 ops W2 c2 -> SRr tfibsegs W2 c2 (inv_exit g pos sp1)).
{ apply (SRr_loop tfibsegs Z (fun ops => Z.to_nat (256 - ops)) (fun ops => inv_head g pos sp1 ops)
    (inv_exit g pos sp1)).
  intros ops W2 c2 H2.
  set (Q := fun W3 c3 => inv_exit g pos sp1 W3 c3 \/
             exists x', (Z.to_nat (256 - x') < Z.to_nat (256 - ops))%nat /\ inv_head g pos sp1 x' W3 c3).
  assert (LT : forall W3 c3, inv_latch g pos sp1 ops W3 c3 -> SRr tfibsegs W3 c3 Q).
  { intros W3 c3 H3. eapply SRr_mono; [exact (hL g pos sp1 ops W3 c3 H3)|].
    intros W4 c4 _ [[_ H4] | [Hlt H4]]; [left; exact H4|].
    right. exists (ops + 1). split; [|exact H4].
    destruct (mcut_P _ _ _ _ _ _ _ _ H2) as (? & ? & ? & ? & ? & (Hops & _) & _). lia. }
  assert (CK : forall W3 c3, inv_chk g pos sp1 ops W3 c3 -> SRr tfibsegs W3 c3 Q).
  { intros W3 c3 H3. eapply SRr_bind; [exact (hC g pos sp1 ops W3 c3 H3)|]. intros W4 c4 _ H4. exact (LT W4 c4 H4). }
  assert (JN : forall W3 c3, inv_join g pos sp1 ops W3 c3 -> SRr tfibsegs W3 c3 Q).
  { intros W3 c3 H3. eapply SRr_bind; [exact (hOH g pos sp1 ops W3 c3 H3)|].
    intros W4 c4 _ [H4 | (kind & H4)]; [exact (CK W4 c4 H4)|].
    destruct (mcut_P _ _ _ _ _ _ _ _ H4) as (? & ? & ? & ? & ? & _ & Hk & _).
    eapply SRr_bind; [exact (hOw kind Hk g pos sp1 ops W4 c4 H4)|]. intros W5 c5 _ H5. exact (CK W5 c5 H5). }
  assert (EN : forall kind W3 c3, inv_enc g pos sp1 ops kind W3 c3 -> SRr tfibsegs W3 c3 Q).
  { intros kind W3 c3 H3.
    destruct (mcut_P _ _ _ _ _ _ _ _ H3) as (? & ? & ? & ? & ? & _ & Hk & _).
    eapply SRr_bind; [exact (hEnc kind Hk g pos sp1 ops W3 c3 H3)|]. intros W4 c4 _ H4. exact (JN W4 c4 H4). }
  assert (RN : forall W3 c3, inv_run g pos sp1 ops W3 c3 -> SRr tfibsegs W3 c3 Q).
  { intros W3 c3 H3. eapply SRr_bind; [exact (hRun g pos sp1 ops W3 c3 H3)|].
    intros W4 c4 _ (kind & H4). exact (EN kind W4 c4 H4). }
  eapply SRr_bind; [exact (hH g pos sp1 ops W2 c2 H2)|]. intros W3 c3 _ [HX | (kind & H3)].
  - apply SRr_ret. left. exact HX.
  - destruct (mcut_P _ _ _ _ _ _ _ _ H3) as (? & ? & ? & ? & ? & _ & Hk & _).
    destruct (kind_split_14 kind Hk) as [Hk' | [-> | [-> | ->]]].
    + eapply SRr_bind; [exact (hR kind Hk' g pos sp1 ops W3 c3 H3)|]. intros W4 c4 _ H4. exact (RN W4 c4 H4).
    + eapply SRr_bind; [exact (hR12 g pos sp1 ops W3 c3 H3)|]. intros W4 c4 _ H4. exact (EN 9 W4 c4 H4).
    + eapply SRr_bind; [exact (hR13 g pos sp1 ops W3 c3 H3)|]. intros W4 c4 _ [H4 | H4].
      * exact (EN 10 W4 c4 H4).
      * exact (LT W4 c4 H4).
    + eapply SRr_bind; [exact (hR14 g pos sp1 ops W3 c3 H3)|]. intros W4 c4 _ H4. exact (LT W4 c4 H4). }
eapply SRr_bind; [exact (LOOP 0 W1 c1 H1)|]. intros W2 c2 _ H2. exact (hX g pos sp1 W2 c2 H2).
Qed.

(* ================================ from the walk to the contract ================================ *)
Section con.
Context {LS : lib_shape}.
Hypothesis MTL : ameter_laws MT.
Hypothesis AIL : asink_img_laws tfibsegs B K.
Hypothesis HXN : forall n, 0 <= XN_LIB n.
(* codec writes no file: the library shape's leaf is the silent one *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* the walk's journal has an empty footprint; the contract's post states it over [sink_token] *)
Lemma amain_fp_widen : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal tfibsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
refine (conj HAR (conj Hly (conj Hsecs (conj Hwle (conj _ (conj Hfrs (conj Hnev (conj Hk (conj F1
  (conj _ (conj _ (conj _ (conj _ (conj Hpres (conj Hstk (conj F5 HQT)))))))))))))))).
- apply (aos_step_mono [] FP md md'); [|exact Hio]. intros Ho. exfalso. exact (sink_closed_nil Ho).
- intros p n i H1 H2 Hi _. apply (F2 p n i H1 H2 Hi). apply inFP_nil.
- intros a Hi Hns He _. apply (F3 a Hi Hns He). apply fp_spares_closed. exact sink_closed_nil.
- intros cid pos a H1 H2 _. apply (F4 cid pos a H1 H2). apply inFP_nil.
- intros p n i H1 H2 Hi. exfalso. exact (inFP_nil _ (Hgone p n i H1 H2 Hi)).
Qed.

Lemma srz_enter_am : forall (W : world tfibsegs) (c : config) (T : TSet),
AI tfibsegs (w_H W) (w_A W) (cfg_model c) ->
SRr tfibsegs W c (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') -> srealizes tfibsegs c' T) ->
srealizes tfibsegs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

Theorem amain_contract_of_walk :
(forall g W2 c2, inv_entry g W2 c2 -> e_pre g -> SRr tfibsegs W2 c2 (inv_retj g)) ->
codec_lib_contract_x tfibsegs B MT K XM_LIB XN_LIB CA_RLO CA_RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros WALK ly S W regs mem md p n pl M Kl HAI HPRE HK.
rewrite LEAF.
set (g := mkEctx ly S W mem md regs p n pl M).
assert (HE : inv_entry g W (cfg_at tfibsegs A_LLVMF regs mem md)) by (split; reflexivity).
pose proof HPRE as HPRE0.
destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK).
apply (srz_enter_am W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono; [exact (WALK g W _ HE HPRE0)|].
intros W' c' Hwle (ly' & S' & regs' & mem' & md' & k & -> & HJ & Hk & HPR & Ha0 & HPerm & HMLE) HAI'.
cbn [e_sp0 e_ly e_S e_W e_mem e_md e_regs] in HJ, HPR, HPerm, HMLE.
pose proof HJ as (_ & _ & _ & _ & Hio & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hio) as (Efd & Efsys & _ & _).
apply (HK (LL 0 (m_fs md) []) W' _ Hwle HAI').
exists ly', S', regs', mem', md', k. split; [reflexivity|].
unfold codec_lib_post_x. cbn [ll_fs ll_ret ll_out].
split; [apply amain_fp_widen; exact HJ|]. split; [lia|]. split; [exact HPR|]. split; [exact Ha0|].
split; [exact HPerm|].
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [unfold m_fs; rewrite Efsys; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact HSORT|].
split; [eapply (asink_none_kept tfibsegs B K AIL); [exact HJ | exact sink_closed_nil | exact HSNK]|].
split; [exact (ameta_inv_kept tfibsegs B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
split; [apply (mo_le_mono MT MTL _ _ 0 _ HMLE (HXN n))|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; lia|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; lia | exact Hi].
- apply inFP_nil.
Qed.
End con.
End b.
End a.

(* ================================ satisfiability ================================
   The pure part of every cut holds of a concrete record: a Control|24 FADER record at each stage of the pass,
   built by the plain functions themselves. The machine-state part of every cut is the journal and the kit's
   vocabulary, which the entry state satisfies by the released walks' construction. *)
Definition sat_k_rd : kcallZ := Eval vm_compute in k_rdZ 0 CA_PERS CM_SPEC_C24.
Definition sat_k_enc : kcallZ := sat_k_rd.
Definition sat_k_join : kcallZ := Eval vm_compute in
mkKcallZ 0 CA_PERS CM_SPEC_C24 0 0 0 0 (repeat 0 24) 0 0 fa5 (cmd_outZ fa5 (snd (enc_kZ sat_k_rd (Some c24))))
0 (repeat 0 24) 0 0 0.
Definition sat_k_owe : kcallZ := Eval vm_compute in
mkKcallZ 0 CA_PERS CM_SPEC_C24 0 0 0 0 (repeat 0 24) 0 (fst (enc_kZ sat_k_rd (Some c24))) fa5
(cmd_outZ fa5 (snd (enc_kZ sat_k_rd (Some c24)))) 0 (repeat 0 24) 0 0 0.
Definition sat_k_chk : kcallZ := Eval vm_compute in
let w := owe_kZ sat_k_rd (Some c24) in
let '(bs, key, dp) := snd w in
mkKcallZ 0 CA_PERS CM_SPEC_C24 0 0 0 0 (repeat 0 24) 0 (fst (enc_kZ sat_k_rd (Some c24))) fa5
(cmd_outZ fa5 (snd (enc_kZ sat_k_rd (Some c24)))) (fst w) (map u8 bs ++ repeat 0 (24 - length bs))
(Z.of_nat (length bs)) key dp.

Lemma amain_pure_sat :
(kcall_wfZ sat_k_rd /\ pd_okA (kz_p sat_k_rd) (kz_desk sat_k_rd) (Some c24)) /\
(kcall_wfZ sat_k_enc /\ enc_okZ sat_k_enc (Some c24)) /\
(kcall_wfZ sat_k_join /\ rec_okZ sat_k_join (Some c24)) /\
(kcall_wfZ sat_k_owe /\ rec_okZ sat_k_owe (Some c24) /\ kz_rc sat_k_owe = fst (enc_kZ sat_k_owe (Some c24)) /\
 kz_want_rc sat_k_owe = 0 /\ kz_want_len sat_k_owe = 0 /\ kz_want_key sat_k_owe = 0 /\
 kz_want_display sat_k_owe = 0) /\
(kcall_wfZ sat_k_chk /\ rec_okZ sat_k_chk (Some c24) /\ kz_rc sat_k_chk = fst (enc_kZ sat_k_chk (Some c24)) /\
 owe_want_okZ sat_k_chk (Some c24)) /\
length (shm 0) = 56%nat /\ length (shm SH_F8) = 56%nat /\
(* k's 23 shadow bytes, text's 8 + 1, the dots byte, at the offsets the frame lays out *)
(forall kv i, (22 <= i < 45)%nat -> nth i (shm kv) 0 = kv) /\
(forall kv i, (8 <= i < 16)%nat -> nth i (shm kv) 0 = 0) /\ (forall kv, nth 16 (shm kv) 0 = 1) /\
(forall kv, nth 54 (shm kv) 0 = SH_F8) /\
(* the machine frame at a 16-aligned sp0: sp1 is 32-aligned, between sp0 - 320 and sp0 - 288 *)
(forall sp0, sp0 mod 16 = 0 -> let sp1 := 32 * ((sp0 - 288) / 32) in
 sp1 mod 32 = 0 /\ sp0 - 320 <= sp1 <= sp0 - 288 /\ sp1 + 184 <= sp0 - 104).
Proof.
(* every leaf goal is closed: a computed equation, a computed comparison, a premise with kind 0 that cannot
   hold, the bytes' range over repeat 0 24, or the Control|24 personality pair *)
Ltac sat_leaf :=
  first [ reflexivity
        | (vm_compute; reflexivity)
        | (apply Z.leb_le; vm_compute; reflexivity)
        | (apply Z.ltb_lt; vm_compute; reflexivity)
        | (let H := fresh "H" in intros H; vm_compute in H; discriminate H)
        | (apply Forall_forall; let x := fresh "x" in let Hx := fresh "Hx" in
           intros x Hx; vm_compute in Hx;
           repeat (destruct Hx as [<- | Hx]; [lia|]); destruct Hx)
        | (right; left; repeat split) ].
Ltac sat_t :=
  unfold enc_okZ, rec_okZ, rdr_kZ, reader_ok, kcall_wfZ, pd_okA;
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want
       kz_want_len kz_want_key kz_want_display sat_k_rd sat_k_enc sat_k_join sat_k_owe sat_k_chk];
  repeat match goal with |- _ /\ _ => split end; sat_leaf.
split; [sat_t|]. split; [sat_t|]. split; [sat_t|]. split; [sat_t|].
split; [split; [sat_t | split; [sat_t | split; [sat_t |]]]|].
{ unfold owe_want_okZ. vm_compute. repeat split; reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
split; [intros kv i Hi; do 45 (destruct i as [|i]; [try lia; reflexivity|]); lia|].
split; [intros kv i Hi; do 16 (destruct i as [|i]; [try lia; reflexivity|]); lia|].
split; [intros kv; reflexivity|]. split; [intros kv; reflexivity|].
intros sp0 Hsp0 sp1. subst sp1. pose proof (Z.div_mod (sp0 - 288) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)) as M.
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. lia.
Qed.
