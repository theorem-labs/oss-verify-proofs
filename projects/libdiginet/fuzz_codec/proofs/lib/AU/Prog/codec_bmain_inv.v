(* The boundary layer of the image-B walk of LLVMFuzzerTestOneInput (fuzz_codec.asan-ubsan, sha256 73109e32e77b,
   entry 0x8099c, 3040 instructions of the 6647-instruction program table, real frame 320 realigned to 32, and a
   side-stack frame of class 3 of 480 bytes taken at 0x80a0c): one predicate per cut of the listing, the statement
   of each segment lemma, the composition of the segments into one walk from the entry to the return, the step from
   that walk to the contract codec_lib_contract_x of lib/A/Prog/CPgMainC.v at image B's constants, the UBSan trap
   edges every segment must refute, and the pure witnesses of the cuts.

   It is the image-A boundary layer (lib/A/Prog/codec_amain_inv.v) with image B's code: the same cuts, statements
   and composition, the frame, registers, spills and pcs read from image B's listing and image.

   Shape. A cut is a `world tfibsegs -> config -> Prop`, the form of an SRr post-condition: `mcut g pos sp1 kv pc P`
   says the run is at pc, the journal from the entry state g holds with the entry's own side-stack frame (3, pos)
   as its `own`, the facts every cut after the prologue shares hold (mcommon), and P holds of the state. A segment
   is `forall ..., <start cut> W2 c2 -> SRr tfibsegs W2 c2 <end cuts>`; each is proved in its own file, from the
   Section hypotheses its file names (the kit's laws, the runtime contracts, the callee contracts at image B).

   The frame (F = frame_addr (e_ly g) 3 pos, 64-aligned; offsets from F; image B's frame map, 0x80a80-0x80b74):
     +32 a 3-byte payload (shadow 4), +48 the 10-byte scribble payload (shadow 6, 7), +80 char text[65]
     (shadow 10 .. 18), +192 struct call k (184 bytes, fuzz_codec.c:74-90; shadow 24 .. 46), +448 the dots byte of
     COUNTER_TEXT (shadow 56), +504 the flag address the frame request writes (read at 0x83578).
   Its 60 shadow bytes from shadow_addr F: f1 x4 | f8 | f2 | f8 f8 | f2 f2 | 00 x8 01 | f2 x5 | k x23 | f2 x9 | f8 |
   f3 x3, with k's 23 bytes f8 (marked unusable) outside the loop body and 00 (marked usable) inside it
   (0x80c70-0x80cc8 marks them usable, 0x82df4-0x82e50 unusable again); shadow bytes 60 .. 63 stay 00.
   The machine frame (sp1 = 32 * ((sp0 - 320) / 32), 0x8099c / 0x809dc): the spills 16(sp1) .. 152(sp1) written
   once at 0x80b80-0x80c2c, struct fuzz_in at 184(sp1) (in.p) and 192(sp1) (in.n), the thirteen saved words at
   sp0 - 104 .. sp0 - 8 (0x809a4-0x809d4). 176(sp1) holds F (0x80a40) and is never read; inside OWE10,
   206(sp1) .. 215(sp1) hold COUNTER's pl[10] (0x82cd8-0x82d1c, ended by s3 = sp1 + 216); both are below
   sp0 - 104 and away from 16 .. 159 and 184 .. 199.
   Registers at every cut after the prologue (set at 0x809d8-0x80c10, kept by every callee): sp = s1 = sp1,
   s0 = sp0, s2 = shadow_addr F, s3 = sp1 + 216, s5 = SHADOW_OFF (the shadow base, loaded at 0x809fc),
   s7 = F + 192 (k), s9 = F + 448 (the dots byte; OWE9 and OWE10 use it as a shadow address (0x82958, 0x82cc4);
   every path to CHK reloads it from 128(sp1) at 0x82dd0, and OWE5 / OWE11 also at 0x82fc0 / 0x83034, 0x83064),
   s10 = 1, s11 = -8, and s4 = ops (the loop counter).

   The cuts (pc; the tables are read from the pinned image, each target checked against the listing's roots):
     HEAD 0x80c30 (loop head); RDk = the switch table at 0x20f04, entry k (k = 0..13), RD14 = 0x814f8 (MASKS);
     RUN 0x826f4 (the readers' common tail: kind loaded, run()'s switch; seg-B.txt starts RUN at 0x82700 and counts
     0x826f4-0x826fc in the readers); ENCk = run()'s table at 0x20f3c, entry k (k = 0..10), ENC11 = 0x8281c
     (SYSEX); JOIN 0x82834 (the encoder returned; seg-B.txt's OWEH root); OWEk = owe()'s table at 0x20f68,
     entry k (k = 0..10), OWE11 = 0x82e60; CHK 0x82dd4 (the three record checks); LATCH 0x82df4 (k marked
     unusable, ops + 1, the ops test); EXIT 0x83530 (frame release and epilogue).
   The content of k at each cut is the plain walk's: the record HEAD leaves, the readers' ranges, the encoder's
   output, owe()'s answer; the plain agreement lemmas of lib/Prog/codec_agree.v refute the checks' abort branches.

   UBSan. The function's only trap is the `unimp` at 0x836b8 (BM_TRAP below). 118 edges reach it: 24 conditional
   branches to it and 94 conditional branches that fall through into a `j 0x836b8`. 88 of the 94 are the
   `in->p++` pointer-overflow check of fuzz.h:45 (`addi x,p,1; sd ..,192(s1); bltu s10,x,ok; j trap`, s10 = 1);
   bm_inpp_ok refutes all of them. The lemmas of the section `traps` check the lists against the image's own code
   table (tfibtbl_lib), including that no other branch or jump of the function reaches the trap. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP0m YP0e YP09 YP02 YI00 YI04 YI08 YI09 YI16 YN3v YI0w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YCeh YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require APgImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ================================ image B: the entry function's own constants ================================
   Read from the pinned image: DESK (0x20fa0, the symbol LLVMFuzzerTestOneInput.DESK) holds the three ints 0, 1, 2;
   SPEC_DESK (0x9df80, LLVMFuzzerTestOneInput.SPEC_DESK) holds the three pointers 0, 0x9dfc0 (SPEC_C24), 0x9dfe0
   (SPEC_PC). The personality table and the read window are CPgWalkU's CB_PERS / CB_RLO / CB_RHI. *)
Definition CM_DESK : Z := 0x20fa0.
Definition CM_SPEC_DESK : Z := 0x9df80.
Definition CM_SPEC_C24 : Z := 0x9dfc0.
Definition CM_SPEC_PC : Z := 0x9dfe0.

(* The callees' entries (the `jal` targets of the listing); bm_entries_sigma checks each against the address the
   unit's generated listing table (lib/AU/APgImg.v) gives its symbol. *)
Definition BM_check_pers : Z := 0x8391c.
Definition BM_pers_of : Z := 0x8513c.
Definition BM_text_arg : Z := 0x83ba0.
Definition BM_check_seg7 : Z := 0x84148.
Definition BM_check_text_counter : Z := 0x841c4.
Definition BM_owed_counter_text : Z := 0x84474.
Definition BM_check_text_scribble : Z := 0x83dbc.
Definition BM_check_masks : Z := 0x84974.
Definition BM_check_refusal : Z := 0x84bc4.
Definition BM_check_range : Z := 0x84c84.
Definition BM_check_bytes : Z := 0x84d40.
Definition BM_owe_sysex : Z := 0x84e8c.
Definition BM_fader : Z := 0x8540c.
Definition BM_button : Z := 0x855dc.
Definition BM_touch : Z := 0x85744.
Definition BM_vpot : Z := 0x85914.
Definition BM_jog : Z := 0x85a8c.
Definition BM_sysex : Z := 0x85174.
Definition BM_ring : Z := 0x85c1c.
Definition BM_meter : Z := 0x85f4c.
Definition BM_sleds : Z := 0x861d0.
Definition BM_cleds : Z := 0x8648c.
Definition BM_scribble : Z := 0x866c4.
Definition BM_counter : Z := 0x86ee4.
(* The runtime entries the walk calls: the class-3 frame request (0x80a0c), the checked fill (HEAD 0x80cd8 /
   0x80da0, OWEH 0x8286c / 0x82914) and copy (RD11, OWE5, OWE9, OWE10), and the shadow fill with 0xf5 the frame
   release calls at 0x83574. *)
Definition BM_stack_malloc_3 : Z := 0x3d550.
Definition BM_asan_memset : Z := 0x51f84.
Definition BM_asan_memcpy : Z := 0x51ae8.
Definition BM_set_shadow_f5 : Z := 0x54ab0.

Lemma bm_entries_sigma :
  BM_check_pers = APgImg.codec_asanubsan_sigma AS_check_personality /\
  BM_pers_of = APgImg.codec_asanubsan_sigma AS_diginet_personality_of /\
  BM_text_arg = APgImg.codec_asanubsan_sigma AS_text_arg /\
  BM_check_seg7 = APgImg.codec_asanubsan_sigma AS_check_text_seg7 /\
  BM_check_text_counter = APgImg.codec_asanubsan_sigma AS_check_text_counter /\
  BM_owed_counter_text = APgImg.codec_asanubsan_sigma AS_owed_counter_text /\
  BM_check_text_scribble = APgImg.codec_asanubsan_sigma AS_check_text_scribble /\
  BM_check_masks = APgImg.codec_asanubsan_sigma AS_check_text_masks /\
  BM_check_refusal = APgImg.codec_asanubsan_sigma AS_check_refusal /\
  BM_check_range = APgImg.codec_asanubsan_sigma AS_check_range /\
  BM_check_bytes = APgImg.codec_asanubsan_sigma AS_check_bytes /\
  BM_owe_sysex = APgImg.codec_asanubsan_sigma AS_owe_sysex /\
  BM_fader = APgImg.codec_asanubsan_sigma AS_diginet_fader_encode /\
  BM_button = APgImg.codec_asanubsan_sigma AS_diginet_button_encode /\
  BM_touch = APgImg.codec_asanubsan_sigma AS_diginet_touch_encode /\
  BM_vpot = APgImg.codec_asanubsan_sigma AS_diginet_vpot_encode /\
  BM_jog = APgImg.codec_asanubsan_sigma AS_diginet_jog_encode /\
  BM_sysex = APgImg.codec_asanubsan_sigma AS_diginet_sysex_encode /\
  BM_ring = APgImg.codec_asanubsan_sigma AS_diginet_ring_encode /\
  BM_meter = APgImg.codec_asanubsan_sigma AS_diginet_meter_encode /\
  BM_sleds = APgImg.codec_asanubsan_sigma AS_diginet_strip_leds_encode /\
  BM_cleds = APgImg.codec_asanubsan_sigma AS_diginet_counter_leds_encode /\
  BM_scribble = APgImg.codec_asanubsan_sigma AS_diginet_scribble_encode /\
  BM_counter = APgImg.codec_asanubsan_sigma AS_diginet_counter_encode /\
  BM_stack_malloc_3 = APgImg.codec_asanubsan_sigma AS___asan_stack_malloc_3 /\
  BM_asan_memset = APgImg.codec_asanubsan_sigma AS___asan_memset /\
  BM_asan_memcpy = APgImg.codec_asanubsan_sigma AS___asan_memcpy /\
  BM_set_shadow_f5 = APgImg.codec_asanubsan_sigma AS___asan_set_shadow_f5 /\
  A_LLVMF = APgImg.codec_asanubsan_text.
Proof. repeat split; reflexivity. Qed.

(* ================================ the cuts' pcs ================================ *)
Definition PC_HEAD : Z := 0x80c30.
(* the switch table at 0x20f04 (entries 0..13, read from the pinned image) and the MASKS default (0x80dac) *)
Definition rd_pc (kind : Z) : Z :=
nth (Z.to_nat kind) [0x80dcc; 0x811f4; 0x81080; 0x810fc; 0x80f28; 0x81270; 0x81350; 0x81178; 0x81478; 0x81004;
0x813cc; 0x80e48; 0x80fa4; 0x812ec; 0x814f8] 0.
Definition PC_RUN : Z := 0x826f4.
(* run()'s table at 0x20f3c (entries 0..10) and the SYSEX default (0x826fc) *)
Definition enc_pc (kind : Z) : Z :=
nth (Z.to_nat kind) [0x8271c; 0x827bc; 0x82774; 0x8278c; 0x82764; 0x827d4; 0x827ec; 0x827a4; 0x82808; 0x82734;
0x8274c; 0x8281c] 0.
Definition PC_JOIN : Z := 0x82834.
(* owe()'s table at 0x20f68 (entries 0..10) and the SYSEX default (0x82874) *)
Definition owe_pc (kind : Z) : Z :=
nth (Z.to_nat kind) [0x82894; 0x82a98; 0x829b8; 0x82a14; 0x82920; 0x82af0; 0x82be4; 0x82a68; 0x82d98; 0x8293c;
0x82c8c; 0x82e60] 0.
Definition PC_CHK : Z := 0x82dd4.
Definition PC_LATCH : Z := 0x82df4.
Definition PC_EXIT : Z := 0x83530.

(* ================================ the frame's shadow ================================ *)
Definition SH_F1 : Z := 0xf1.
Definition SH_F2 : Z := 0xf2.
Definition SH_F3 : Z := 0xf3.
Definition SH_F8 : Z := 0xf8.
(* the 60 shadow bytes of the frame, with k's 23 bytes kv (0xf8 outside the loop body, 0 inside it) *)
Definition shm (kv : Z) : list Z :=
[SH_F1; SH_F1; SH_F1; SH_F1; SH_F8; SH_F2; SH_F8; SH_F8; SH_F2; SH_F2; 0; 0; 0; 0; 0; 0; 0; 0; 1;
 SH_F2; SH_F2; SH_F2; SH_F2; SH_F2]
++ repeat kv 23 ++ repeat SH_F2 9 ++ [SH_F8; SH_F3; SH_F3; SH_F3].

(* ================================ the call record over Z ================================
   The record facts of the image-A layer, over lib/A/Prog/CPgBase.v's kcallZ (the record and its layout are the
   same at both images). *)
Definition fa5 : list Z := repeat 0xa5 32.
(* k as HEAD leaves it: memset to 0 (0x80cd8), kind stored (sw, 0x80d28), p and desk stored (0x80d68, 0x80d90),
   before and out memset to 0xa5 (0x80da0). *)
Definition k_rdZ (kind pv dv : Z) : kcallZ :=
mkKcallZ kind pv dv 0 0 0 0 (repeat 0 24) 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
(* k.p and k.desk as HEAD sets them from DESK[op / 15 % 3] (and RD12 / RD13 when k.p is NULL): NULL, or the
   personality and spec desk of Control|24, or of ProControl; od the desk both describe. *)
Definition pd_okB (pv dv : Z) (od : option desk) : Prop :=
(pv = 0 /\ dv = 0 /\ od = None) \/
(pv = CB_PERS /\ dv = CM_SPEC_C24 /\ od = Some c24) \/
(pv = CB_PERS + 24 /\ dv = CM_SPEC_PC /\ od = Some pc).
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
0 <= kz_kind k <= 11 /\ pd_okB (kz_p k) (kz_desk k) od /\ rdr_kZ k /\ kz_before k = fa5 /\ kz_out k = fa5.
(* the record after run(): out is what the encoder wrote over 0xa5^32 *)
Definition rec_okZ (k : kcallZ) (od : option desk) : Prop :=
0 <= kz_kind k <= 11 /\ pd_okB (kz_p k) (kz_desk k) od /\ rdr_kZ k /\ kz_before k = fa5 /\
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
(* The Section of the contract (lib/A/Prog/CPgMainC.v), at image B's segments and constants. *)
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
(* the contract's pre-condition at the entry state (lib/A/Prog/CPgMainC.v at image B), as one name *)
Definition e_pre (g : ectx) : Prop :=
codec_lib_pre_x tfibsegs B MT K XM_LIB CB_RLO CB_RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK
(e_regs g) (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) (e_pl g) (e_M g).

(* ---- what every cut after the prologue carries ---- *)
Definition mcommon (g : ectx) (pos sp1 kv : Z) (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
e_pre g /\
(* the machine frame: 0x8099c addi sp,sp,-320; 0x809dc andi sp,sp,-32; 0x809e0 mv s1,sp; 0x809d8 addi s0,sp,320 *)
sp1 = 32 * ((e_sp0 g - 320) / 32) /\
getr regs2 2 = w64 sp1 /\ getr regs2 9 = w64 sp1 /\ getr regs2 8 = w64 (e_sp0 g) /\
getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
(* 0x809fc s5 = the shadow offset; 0x80a50 + 0x80a7c s2 = shadow_addr F; 0x80a54 s11 = -8; 0x80b94 s7 = k;
   0x80bac s9 = the dots byte; 0x80c10 s3 = sp1 + 216; 0x80bf0 s10 = 1 *)
getr regs2 21 = w64 SHADOW_OFF /\ getr regs2 18 = w64 (shadow_addr (FA g pos)) /\ getr regs2 27 = w64 (-8) /\
getr regs2 23 = w64 (FA g pos + 192) /\ getr regs2 25 = w64 (FA g pos + 448) /\
getr regs2 19 = w64 (sp1 + 216) /\ getr regs2 26 = w64 1 /\
(* the frame is 64-aligned (lib/AU/YCem.v frame_al64) *)
FA g pos mod 64 = 0 /\
(* the spills, 0x80b80-0x80c2c (k = F + 192) *)
val_mem tfibsegs (rd W2 mem2) (sp1 + 16) 8 (FA g pos + 192 + 47) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 24) 8 (FA g pos + 192 + 144) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 32) 8 (FA g pos + 50) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 40) 8 (FA g pos + 192 + 148) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 48) 8 0x990 /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 56) 8 0x5cb0 /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 64) 8 (FA g pos + 48) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 72) 8 (FA g pos) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 80) 8 (FA g pos) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 88) 8 (FA g pos + 34) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 96) 8 (FA g pos + 33) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 104) 8 (FA g pos + 80) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 112) 8 (FA g pos + 32) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 120) 8 (FA g pos + 192 + 40) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 128) 8 (FA g pos + 448) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 136) 8 (FA g pos + 192 + 168) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 144) 8 (FA g pos + 192 + 108) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 152) 8 (FA g pos + 192 + 76) /\
(* the thirteen saved words, which the epilogue restores (0x809a4-0x809d4, 0x8367c-0x836ac) *)
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
(* the flag address the frame request wrote at F + 504, which the release reads (0x83578) *)
val_mem tfibsegs (rd W2 mem2) (FA g pos + 504) 8 (flag_addr (e_ly g) 3 pos) /\
(* the frame's 60 shadow bytes *)
(forall i, 0 <= i < 60 ->
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

(* the input cursor struct fuzz_in at 184(sp1): c bytes taken (0x80ba8, 0x80bb0 and every reader) *)
Definition cur_at (g : ectx) (sp1 c : Z) (W2 : world tfibsegs) (mem2 : word -> option byte) : Prop :=
0 <= c <= e_n g /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 184) 8 (e_p g + c) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 192) 8 (e_n g - c).
(* the loop counter s4 (0x80ba4 li s4,0; 0x82e44 addiw s4,s4,1) *)
Definition ops_at (ops : Z) (regs2 : bvmap 5 word) : Prop :=
0 <= ops <= 255 /\ getr regs2 20 = w64 ops.
(* the call record at k = F + 192 *)
Definition k_at (g : ectx) (pos : Z) (k : kcallZ) (W2 : world tfibsegs) (mem2 : word -> option byte) : Prop :=
kcall_atA tfibsegs W2 mem2 (FA g pos + 192) k /\ kcall_wfZ k.

(* ================================ the cuts ================================ *)
(* the entry: the contract's state, before the frame exists *)
Definition inv_entry (g : ectx) : world tfibsegs -> config -> Prop :=
fun W2 c2 => W2 = e_W g /\ c2 = cfg_at tfibsegs A_LLVMF (e_regs g) (e_mem g) (e_md g).

(* HEAD 0x80c30: ops passes done (ops < 256), c input bytes taken; k marked unusable, its bytes any. *)
Definition inv_head (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 SH_F8 PC_HEAD (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ exists c, cur_at g sp1 c W2 mem2).

(* RDk, the reader of kind k: the op byte taken (in.n was not 0), k marked usable and set as HEAD sets it;
   s6 = k.p (0x80d54), which RD12 / RD13 test. *)
Definition inv_rd (g : ectx) (pos sp1 ops kind : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 (rd_pc kind) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= kind <= 14 /\
exists c pv dv od, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ pd_okB pv dv od /\ getr regs2 22 = w64 pv /\
k_at g pos (k_rdZ kind pv dv) W2 mem2).

(* RUN 0x826f4: a reader of kinds 0..11 is done; k is the record run() is called with. *)
Definition inv_run (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_RUN (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ enc_okZ k od).

(* ENCk: run()'s call of the encoder of kind k (from RUN, and from RD12 / RD13 with kind 9 / 10). *)
Definition inv_enc (g : ectx) (pos sp1 ops kind : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 (enc_pc kind) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= kind <= 11 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ enc_okZ k od /\ kz_kind k = kind).

(* JOIN 0x82834: the encoder returned its code in a0, out holds what it wrote. *)
Definition inv_join (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_JOIN (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
getr regs2 10 = w64 (fst (enc_kZ k od))).

(* OWEk: owe()'s case for kind k, past its common part (0x82834-0x82890): k.rc = the encoder's code (0x8283c),
   want_rc = 0 (0x8285c / 0x82904) and want_len = want_key = want_display = 0 (the checked fill of k + 168 at
   0x8286c / 0x82914), the desk test passed (a NULL desk only for BUTTON, JOG, SYSEX: the mask 0x812 at 0x8284c),
   s6 = k.desk (0x82838). *)
Definition inv_owe (g : ectx) (pos sp1 ops kind : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 (owe_pc kind) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= kind <= 11 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\ kz_kind k = kind /\
(od = None -> kind = 1 \/ kind = 4 \/ kind = 11) /\
kz_rc k = fst (enc_kZ k od) /\
kz_want_rc k = 0 /\ kz_want_len k = 0 /\ kz_want_key k = 0 /\ kz_want_display k = 0 /\
getr regs2 22 = w64 (kz_desk k)).

(* CHK 0x82dd4: owe() done; k.rc the encoder's code, the want fields owe()'s answer. *)
Definition inv_chk (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_CHK (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
kz_rc k = fst (enc_kZ k od) /\ owe_want_okZ k od).

(* LATCH 0x82df4: the end of a pass (from CHK, from COUNTER_TEXT's refusal at 0x8134c and from MASKS at
   0x82188); k still marked usable, its bytes any. *)
Definition inv_latch (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_LATCH (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ exists c, cur_at g sp1 c W2 mem2).

(* EXIT 0x83530: the loop is done (in.n = 0 at 0x80c34, or 256 passes at 0x82e58). *)
Definition inv_exit (g : ectx) (pos sp1 : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 SH_F8 PC_EXIT (fun _ _ _ _ _ _ => True).

(* The return: the frame is released (own = []), a0 = 0, the callee-saved registers and the blocks kept, the
   meter not charged. lib/A/Prog/CPgMainC.v's post follows from it (bmain_contract_of_walk). *)
Definition inv_retj (g : ectx) : world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k,
c2 = cfg_at tfibsegs RA_LLVMF regs2 mem2 md2 /\
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [] ly2 S2 W2 mem2 md2 k /\
0 <= k <= EV_LIB /\ aregs_preserved (e_regs g) regs2 /\ getr regs2 10 = w64 0 /\
Permutation (ablocks B ly2 S2) (ablocks B (e_ly g) (e_S g)) /\ mo_le MT (e_S g) S2 0.

(* ================================ the segment statements ================================
   Each is `start -> SRr tfibsegs W2 c2 end`. Each is proved in its own file, under Section hypotheses taken
   only from: the kit's laws (ameter_laws, ameter_fs_laws, TfibLib, AR_laws, model_laws, ro_tfa_below_ofl), the
   runtime contracts at image B (astack_malloc_realizes .. 3 at BM_stack_malloc_3, stack_malloc_progressP,
   astack_free_law, frame_flag_lawP of lib/Reusable/YCbq.v (converted for AU/YCem's flag rules by CPgWalkU's
   ffl_U_of_A), aintrin_realizes OSet BM_asan_memset / OCpy BM_asan_memcpy,
   aset_shadow_realizes BM_set_shadow_f5 0xf5), the start-up facts (globs_marked .. CODEC_GLOBS of
   lib/AU/Prog/CodecGlobs.v, img_shadow_vis), the string rows' freedom cpw_rows_free B CB_ROSTRS
   (lib/AU/Prog/CPgWalkRoU.v), and the image-B contracts of the callees (lib/AU/Prog/CPgEncU.v,
   CPgChkU.v) at the BM_* entries and CPgWalkU's CB_* instance. Every UBSan trap edge of the segment's range
   (section traps below) is refuted inside its proof. *)

(* ENTRY 0x8099c-0x80c2c, 165 instructions: the prologue, the class-3 frame request (0x80a0c, 480 bytes) with its
   machine-stack fallback refuted (the use-after-return cell is 1, the request returns a frame at or above 4096),
   the frame's description words (0x80a6c-0x80a74) and shadow map (0x80a80-0x80b74), the size test (0x80aa4 /
   0x80b78, n < 2^26 by the pre-condition), check_personality (0x80ba0), the spills and the loop constants. *)
Definition seg_entry : Prop :=
forall g W2 c2, inv_entry g W2 c2 -> e_pre g ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists pos sp1, inv_head g pos sp1 0 W3 c3).

(* HEAD 0x80c30-0x80dc8, 113 instructions: the in.n test (to EXIT when 0), the op byte, k marked usable, the
   checked fill of k, op % 15, diginet_personality_of(DESK[op / 15 % 3]), SPEC_DESK[op / 15 % 3], the checked fill
   of before and out, and the switch on the kind. *)
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
(* RUN 0x826f4-0x82718: the kind loaded and run()'s switch. *)
Definition seg_run : Prop :=
forall g pos sp1 ops W2 c2, inv_run g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists kind, inv_enc g pos sp1 ops kind W3 c3).
(* ENC0 .. ENC11: the arguments from k and the encoder call, to JOIN. *)
Definition seg_enc (kind : Z) : Prop :=
forall g pos sp1 ops W2 c2, inv_enc g pos sp1 ops kind W2 c2 -> SRr tfibsegs W2 c2 (inv_join g pos sp1 ops).
(* OWEH 0x82834-0x82890, 0x82904-0x8291c, 0x82e6c-0x82e74: owe()'s common part; to OWEk, or to CHK with
   want_rc = -1 when the kind needs a desk and k.desk is NULL. *)
Definition seg_oweh : Prop :=
forall g pos sp1 ops W2 c2, inv_join g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => inv_chk g pos sp1 ops W3 c3 \/ exists kind, inv_owe g pos sp1 ops kind W3 c3).
(* OWE0 .. OWE11: owe()'s case for the kind, with the tails it runs through, to CHK. *)
Definition seg_owe (kind : Z) : Prop :=
forall g pos sp1 ops W2 c2, inv_owe g pos sp1 ops kind W2 c2 -> SRr tfibsegs W2 c2 (inv_chk g pos sp1 ops).
(* CHK 0x82dd4-0x82df0: check_refusal, check_range, and check_bytes when k.rc = 0. *)
Definition seg_chk : Prop :=
forall g pos sp1 ops W2 c2, inv_chk g pos sp1 ops W2 c2 -> SRr tfibsegs W2 c2 (inv_latch g pos sp1 ops).
(* LATCH 0x82df4-0x82e5c: k marked unusable, ops + 1, to EXIT after 256 passes, else to HEAD. *)
Definition seg_latch : Prop :=
forall g pos sp1 ops W2 c2, inv_latch g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => (ops = 255 /\ inv_exit g pos sp1 W3 c3) \/
                                  (ops < 255 /\ inv_head g pos sp1 (ops + 1) W3 c3)).
(* EXIT 0x83530-0x836b4, 98 instructions: text marked unusable, the frame's first word retired, the frame's shadow
   filled with 0xf5 (0x83574) and its flag cleared (0x83578), the epilogue, a0 = 0, ret. *)
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
Theorem bmain_of_segments :
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
Lemma bmain_fp_widen : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
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

Lemma srz_enter_bm : forall (W : world tfibsegs) (c : config) (T : TSet),
AI tfibsegs (w_H W) (w_A W) (cfg_model c) ->
SRr tfibsegs W c (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') -> srealizes tfibsegs c' T) ->
srealizes tfibsegs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

Theorem bmain_contract_of_walk :
(forall g W2 c2, inv_entry g W2 c2 -> e_pre g -> SRr tfibsegs W2 c2 (inv_retj g)) ->
codec_lib_contract_x tfibsegs B MT K XM_LIB XN_LIB CB_RLO CB_RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros WALK ly S W regs mem md p n pl M Kl HAI HPRE HK.
rewrite LEAF.
set (g := mkEctx ly S W mem md regs p n pl M).
assert (HE : inv_entry g W (cfg_at tfibsegs A_LLVMF regs mem md)) by (split; reflexivity).
pose proof HPRE as HPRE0.
destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK).
apply (srz_enter_bm W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono; [exact (WALK g W _ HE HPRE0)|].
intros W' c' Hwle (ly' & S' & regs' & mem' & md' & k & -> & HJ & Hk & HPR & Ha0 & HPerm & HMLE) HAI'.
cbn [e_sp0 e_ly e_S e_W e_mem e_md e_regs] in HJ, HPR, HPerm, HMLE.
pose proof HJ as (_ & _ & _ & _ & Hio & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hio) as (Efd & Efsys & _ & _).
apply (HK (LL 0 (m_fs md) []) W' _ Hwle HAI').
exists ly', S', regs', mem', md', k. split; [reflexivity|].
unfold codec_lib_post_x. cbn [ll_fs ll_ret ll_out].
split; [apply bmain_fp_widen; exact HJ|]. split; [lia|]. split; [exact HPR|]. split; [exact Ha0|].
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

(* ================================ the UBSan trap edges ================================
   How the lists were made: every instruction of the function's 3040 slots (0x8099c .. 0x83918) of the neutral
   listing was classified; the SYSTEM-opcode instructions are only the `unimp` at 0x836b8; the edges into it are
   the conditional branches whose target is 0x836b8 (bm_trap_taken) and the `j 0x836b8` instructions, each
   reached only by falling through the conditional branch just before it, whose target skips it
   (bm_trap_inpp ++ bm_trap_other, by that branch's pc). The lemmas below check all of it against the image's
   own code table tfibtbl_lib (lib/AU/YCef.v, built from fuzz_codec.asan-ubsan's loaded segments): the shape of
   every listed edge, and that no other slot of the function branches or jumps to the trap or to a `j` to it.

   The refutation of each edge, by the fact the cut carries:
   - bm_trap_inpp (88, fuzz.h:45 `*in->p++`, HEAD, RD0 .. RD11, RD12, RD14): trap iff p + 1 <= 1 unsigned for
     the cursor p in [4096, 2^47]; bm_inpp_ok.
   - 0x80d2c, 0x80d6c (HEAD, fuzz_codec.c:574-575): the pointer-overflow checks of DESK + 4 i and
     SPEC_DESK + 8 i, i <= 2; the tables lie far below 2^64.
   - 0x81594, 0x815a8 (RD11, fuzz.h:67 `in->p += n`): p + n wraps, or (p = 0) = (p + n <> 0); refuted by
     4096 <= p and p + n <= the allocator ceiling.
   - 0x815e4, 0x815f0 (RD12, fuzz_codec.c:509): k.desk NULL or not 8-aligned; pd_okB (SPEC_C24 / SPEC_PC are
     32-aligned).
   - taken edges: 0x82894 / 0x8289c (OWE0, :139), 0x829b8 / 0x829c0 (OWE2, :158), 0x82a14 / 0x82a1c (OWE3, :164),
     0x82a68 / 0x82a70 (OWE7, :203), 0x82af0 / 0x82af8 (OWE5, :177), 0x82bfc / 0x82c04 (OWE6, :195),
     0x82cb4 / 0x82cbc (OWE10, :224), 0x82d98 / 0x82da0 (OWE8, :202), 0x82948 / 0x82950 (OWE9, :212), 0x82e7c
     (OWE7 / OWE8 tail, :206): the desk d NULL or not 8-aligned, refuted by inv_owe's desk fact and pd_okB;
     0x8297c (OWE9, :95), 0x8303c (OWE11, :95): seven_bit's p = k.bytes = F + 232 NULL; 0x82b70 (OWE5, :182),
     0x82d68 (OWE10, :108), 0x82f2c (OWE9, :215): pointer overflow of a frame object plus a small index, refuted by
     F + 480 <= the allocator ceiling. *)
Definition BM_TRAP : Z := 0x836b8.
Definition BM_NSLOTS : nat := 3040.
Definition bm_trap_taken : list Z :=
[0x82894; 0x8289c; 0x82948; 0x82950; 0x8297c; 0x829b8; 0x829c0; 0x82a14; 0x82a1c;
 0x82a68; 0x82a70; 0x82af0; 0x82af8; 0x82b70; 0x82bfc; 0x82c04; 0x82cb4; 0x82cbc;
 0x82d68; 0x82d98; 0x82da0; 0x82e7c; 0x82f2c; 0x8303c].
Definition bm_trap_inpp : list Z :=
[0x80c4c; 0x80de4; 0x80e18; 0x80e60; 0x80ea0; 0x80ee4; 0x80f40; 0x80f74; 0x80fd8;
 0x8101c; 0x81050; 0x81098; 0x810cc; 0x81114; 0x81148; 0x81190; 0x811c4; 0x8120c;
 0x81240; 0x81288; 0x812bc; 0x81368; 0x8139c; 0x813e4; 0x8142c; 0x81494; 0x814c8;
 0x81510; 0x81544; 0x816ac; 0x816e0; 0x81728; 0x8175c; 0x817c8; 0x81830; 0x81864;
 0x818c8; 0x818fc; 0x81948; 0x8197c; 0x819e0; 0x81a14; 0x81a68; 0x81a9c; 0x81b00;
 0x81b34; 0x81b80; 0x81bb4; 0x81c18; 0x81c4c; 0x81c98; 0x81ccc; 0x81d30; 0x81d64;
 0x81db8; 0x81dec; 0x81e50; 0x81e84; 0x81ee0; 0x81f14; 0x81f78; 0x81fac; 0x82000;
 0x82034; 0x8207c; 0x820b0; 0x82104; 0x82138; 0x821a8; 0x821dc; 0x82224; 0x82258;
 0x822c4; 0x822f8; 0x82340; 0x82374; 0x823bc; 0x823f0; 0x82454; 0x82484; 0x824d4;
 0x82504; 0x82568; 0x82598; 0x825f0; 0x82620; 0x82688; 0x826b8].
Definition bm_trap_other : list Z := [0x80d2c; 0x80d6c; 0x81594; 0x815a8; 0x815e4; 0x815f0].
Definition bm_trap_fall : list Z := bm_trap_inpp ++ bm_trap_other.

(* the instruction word at a slot, and the fields of the RV64 encodings the check reads *)
Definition bm_word (a : Z) : Z := match clookup tfibtbl_lib a with Some w => w | None => 0 end.
Definition rv_bits (w lo n : Z) : Z := Z.land (Z.shiftr w lo) (Z.ones n).
Definition rv_sext (v n : Z) : Z := if v <? 2 ^ (n - 1) then v else v - 2 ^ n.
Definition rv_opc (w : Z) : Z := rv_bits w 0 7.
Definition rv_rd (w : Z) : Z := rv_bits w 7 5.
Definition rv_f3 (w : Z) : Z := rv_bits w 12 3.
Definition rv_rs1 (w : Z) : Z := rv_bits w 15 5.
Definition rv_rs2 (w : Z) : Z := rv_bits w 20 5.
Definition rv_iimm (w : Z) : Z := rv_sext (rv_bits w 20 12) 12.
Definition rv_simm (w : Z) : Z := rv_sext (rv_bits w 25 7 * 32 + rv_bits w 7 5) 12.
Definition rv_bimm (w : Z) : Z :=
rv_sext (rv_bits w 31 1 * 4096 + rv_bits w 7 1 * 2048 + rv_bits w 25 6 * 32 + rv_bits w 8 4 * 2) 13.
Definition rv_jimm (w : Z) : Z :=
rv_sext (rv_bits w 31 1 * 1048576 + rv_bits w 12 8 * 4096 + rv_bits w 20 1 * 2048 + rv_bits w 21 10 * 2) 21.
(* a conditional branch at a to t; a `jal x0` (j) at a to t; any jump or branch at a to t *)
Definition is_br_to (a t : Z) : bool := (rv_opc (bm_word a) =? 99) && (a + rv_bimm (bm_word a) =? t).
Definition is_j_to (a t : Z) : bool :=
(rv_opc (bm_word a) =? 111) && (rv_rd (bm_word a) =? 0) && (a + rv_jimm (bm_word a) =? t).
Definition is_xfer_to (a t : Z) : bool :=
is_br_to a t || ((rv_opc (bm_word a) =? 111) && (a + rv_jimm (bm_word a) =? t)).
Definition bm_slot (i : nat) : Z := A_LLVMF + 4 * Z.of_nat i.
Definition bm_slots : list Z := map bm_slot (seq 0 BM_NSLOTS).
Definition in_zl (l : list Z) (a : Z) : bool := existsb (Z.eqb a) l.
(* the shape of an in->p++ edge: `addi x,y,1` at a - 8, `sd _,192(s1)` at a - 4, `bltu s10,x,a+8` at a,
   `j BM_TRAP` at a + 4 *)
Definition inpp_shape (a : Z) : bool :=
let w := bm_word a in let wa := bm_word (a - 8) in let ws := bm_word (a - 4) in
(rv_opc w =? 99) && (rv_f3 w =? 6) && (rv_rs1 w =? 26) && (a + rv_bimm w =? a + 8) && is_j_to (a + 4) BM_TRAP &&
(rv_opc wa =? 19) && (rv_f3 wa =? 0) && (rv_rd wa =? rv_rs2 w) && (rv_iimm wa =? 1) &&
(rv_opc ws =? 35) && (rv_f3 ws =? 3) && (rv_rs1 ws =? 9) && (rv_simm ws =? 192).

Section traps.
(* The function's slots are all present in the table, and its last slot is 0x83918. *)
Lemma bm_slots_present : forallb (fun a => match clookup tfibtbl_lib a with Some _ => true | None => false end)
  bm_slots = true.
Proof. vm_compute. reflexivity. Qed.
(* The only SYSTEM instruction of the function is the `unimp` (0xc0001073) at BM_TRAP, and the slot before it is
   `ret`, so nothing falls into it. *)
Lemma bm_trap_only : forallb (fun a => negb (rv_opc (bm_word a) =? 115) || (a =? BM_TRAP)) bm_slots = true /\
  bm_word BM_TRAP = 0xc0001073 /\ bm_word (BM_TRAP - 4) = 0x8067.
Proof. split; [|split]; vm_compute; reflexivity. Qed.
(* Every listed edge has its shape: a conditional branch to BM_TRAP; a conditional branch over a `j BM_TRAP`. *)
Lemma bm_trap_taken_ok : forallb (fun a => is_br_to a BM_TRAP) bm_trap_taken = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bm_trap_fall_ok : forallb (fun a => is_br_to a (a + 8) && is_j_to (a + 4) BM_TRAP) bm_trap_fall = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bm_trap_inpp_ok : forallb inpp_shape bm_trap_inpp = true.
Proof. vm_compute. reflexivity. Qed.
(* Completeness: every slot that branches to BM_TRAP is in bm_trap_taken; every `j BM_TRAP` follows a branch of
   bm_trap_fall; no slot branches or jumps to the slot of a `j BM_TRAP`. *)
Lemma bm_trap_complete :
  forallb (fun a => (negb (is_br_to a BM_TRAP) || in_zl bm_trap_taken a) &&
                    (negb (is_j_to a BM_TRAP) || in_zl bm_trap_fall (a - 4)) &&
                    forallb (fun b => negb (is_xfer_to a (b + 4))) bm_trap_fall) bm_slots = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bm_trap_counts : length bm_trap_taken = 24%nat /\ length bm_trap_inpp = 88%nat /\
  length bm_trap_other = 6%nat /\ length bm_slots = BM_NSLOTS.
Proof. vm_compute. repeat split; reflexivity. Qed.
End traps.

(* The in->p++ family: the branch `bltu s10,x` with s10 = 1 and x = p + 1 goes to its fall-through (the trap) only
   if p + 1 <= 1 unsigned; for a cursor p in [1, 2^64 - 2] it does not. *)
Lemma bm_inpp_ok : forall p, 1 <= p -> p + 1 < 2 ^ 64 -> 1 < (p + 1) mod 2 ^ 64.
Proof. intros p H1 H2. rewrite Z.mod_small by lia. lia. Qed.
(* the same, as the engine compares the two operands: s10 is the literal 1, x an offset of the atom holding p *)
Lemma bm_inpp_ok_U : forall E n p o, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> 0 <= o ->
  1 <= p + o -> p + o + 1 < 2 ^ 64 -> U E (SLit 1) < U E (SOff n (o + 1)).
Proof.
intros E n p o Hn Hp Ho H1 H2. rewrite (cw_U_offx E n p (o + 1) Hn Hp).
rewrite U_lit by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ================================ satisfiability of the cuts' pure part ================================
   The record part of every cut holds of a concrete record: a Control|24 FADER record at each stage of the pass,
   built by the plain functions themselves; the frame's shadow map has its objects where the frame lays them out;
   the machine frame sits where mcommon puts it. The entry state's part is codec_bmain_sat.v's, and it is
   CONDITIONAL: it holds at every state satisfying lib/AU/YD1w.v's lib_pre and the other premises of its lib_site_x
   (the harness's call of this function), which this tree shows only inside the driver loop's proof
   (lib/AU/YD1r.v calls_loop), not by a closed inhabitant. *)
Definition sat_k_rd : kcallZ := Eval vm_compute in k_rdZ 0 CB_PERS CM_SPEC_C24.
Definition sat_k_enc : kcallZ := sat_k_rd.
Definition sat_k_join : kcallZ := Eval vm_compute in
mkKcallZ 0 CB_PERS CM_SPEC_C24 0 0 0 0 (repeat 0 24) 0 0 fa5 (cmd_outZ fa5 (snd (enc_kZ sat_k_rd (Some c24))))
0 (repeat 0 24) 0 0 0.
Definition sat_k_owe : kcallZ := Eval vm_compute in
mkKcallZ 0 CB_PERS CM_SPEC_C24 0 0 0 0 (repeat 0 24) 0 (fst (enc_kZ sat_k_rd (Some c24))) fa5
(cmd_outZ fa5 (snd (enc_kZ sat_k_rd (Some c24)))) 0 (repeat 0 24) 0 0 0.
Definition sat_k_chk : kcallZ := Eval vm_compute in
let w := owe_kZ sat_k_rd (Some c24) in
let '(bs, key, dp) := snd w in
mkKcallZ 0 CB_PERS CM_SPEC_C24 0 0 0 0 (repeat 0 24) 0 (fst (enc_kZ sat_k_rd (Some c24))) fa5
(cmd_outZ fa5 (snd (enc_kZ sat_k_rd (Some c24)))) (fst w) (map u8 bs ++ repeat 0 (24 - length bs))
(Z.of_nat (length bs)) key dp.

Lemma bmain_pure_sat :
(kcall_wfZ sat_k_rd /\ pd_okB (kz_p sat_k_rd) (kz_desk sat_k_rd) (Some c24)) /\
(kcall_wfZ sat_k_enc /\ enc_okZ sat_k_enc (Some c24)) /\
(kcall_wfZ sat_k_join /\ rec_okZ sat_k_join (Some c24)) /\
(kcall_wfZ sat_k_owe /\ rec_okZ sat_k_owe (Some c24) /\ kz_rc sat_k_owe = fst (enc_kZ sat_k_owe (Some c24)) /\
 kz_want_rc sat_k_owe = 0 /\ kz_want_len sat_k_owe = 0 /\ kz_want_key sat_k_owe = 0 /\
 kz_want_display sat_k_owe = 0) /\
(kcall_wfZ sat_k_chk /\ rec_okZ sat_k_chk (Some c24) /\ kz_rc sat_k_chk = fst (enc_kZ sat_k_chk (Some c24)) /\
 owe_want_okZ sat_k_chk (Some c24)) /\
length (shm 0) = 60%nat /\ length (shm SH_F8) = 60%nat /\
(* k's 23 shadow bytes, text's 8 + 1, the dots byte, at the offsets the frame lays out *)
(forall kv i, (24 <= i < 47)%nat -> nth i (shm kv) 0 = kv) /\
(forall kv i, (10 <= i < 18)%nat -> nth i (shm kv) 0 = 0) /\ (forall kv, nth 18 (shm kv) 0 = 1) /\
(forall kv, nth 56 (shm kv) 0 = SH_F8) /\
(* the machine frame at a 16-aligned sp0: sp1 is 32-aligned, between sp0 - 352 and sp0 - 320, and the spills,
   the cursor and OWE10's scratch end below the saved words *)
(forall sp0, sp0 mod 16 = 0 -> let sp1 := 32 * ((sp0 - 320) / 32) in
 sp1 mod 32 = 0 /\ sp0 - 352 < sp1 <= sp0 - 320 /\ sp1 + 216 <= sp0 - 104) /\
(* the desk pointers the UBSan checks test are non-NULL and 8-aligned *)
(CM_SPEC_C24 mod 8 = 0 /\ CM_SPEC_PC mod 8 = 0 /\ 0 < CM_SPEC_C24 /\ 0 < CM_SPEC_PC).
Proof.
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
  unfold enc_okZ, rec_okZ, rdr_kZ, reader_ok, kcall_wfZ, pd_okB;
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want
       kz_want_len kz_want_key kz_want_display sat_k_rd sat_k_enc sat_k_join sat_k_owe sat_k_chk];
  repeat match goal with |- _ /\ _ => split end; sat_leaf.
split; [sat_t|]. split; [sat_t|]. split; [sat_t|]. split; [sat_t|].
split; [split; [sat_t | split; [sat_t | split; [sat_t |]]]|].
{ unfold owe_want_okZ. vm_compute. repeat split; reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
split; [intros kv i Hi; do 47 (destruct i as [|i]; [try lia; reflexivity|]); lia|].
split; [intros kv i Hi; do 18 (destruct i as [|i]; [try lia; reflexivity|]); lia|].
split; [intros kv; reflexivity|]. split; [intros kv; reflexivity|].
split.
- intros sp0 Hsp0 sp1. subst sp1. pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as M.
  split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. lia.
- unfold CM_SPEC_C24, CM_SPEC_PC. repeat split; first [reflexivity | lia].
Qed.
