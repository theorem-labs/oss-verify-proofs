(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-278
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1557-1564, 1568-1573, 1593-1605 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_w4tail.v, with its addresses changed; 915 of its 1024 lines of code are new or changed and 1169 lines of the source are left out. *)
(* Piece w4 of segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), +0x14c8 .. +0x1524
   (0x81c3c .. 0x81c98): j_w4_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v, from jc2 to jc3.

   The code, by what it does to registers and memory:
     0x81c3c .. 0x81c4c   x10 := mf+64 (the frame address SF); x18 := SF + 688 (&w4); the shadow byte of w4
                          (x23 + 86) := 0; the two put_dec counters mf+208 and mf+200 := 0
     0x81c50 .. 0x81c60   put_dec (b = x18, p = mf+208, v = mf+176 = t_in, mn = 2)
     0x81c64 .. 0x81c74   put_dec (b = x18, p = mf+208, v = mf+160 = t_out, mn = 2)
     0x81c78 .. 0x81c94   x6 := mf+168 (the shadow base); x10 := mf+208 (= 4); two UBSan bound tests
                          (counter > 7 at 0x81c84, &w4 + counter wrapping at 0x81c8c), both refuted; the byte
                          w4 + 4 := 0 (the NUL).
   Each run starts from a symbolic state of its own (ss_w41, ss_w42, ss_w43); the facts of the start cut reach the
   end through what each run and each call keeps. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic states of the three runs. Run 1 (+0x14c8, 0x81c3c .. the call at 0x81c60): the machine frame
   (base s1, atom 9) with mf+64 = SF (atom 32) and mf+176 = t_in (atom 33), writable on the two counters
   mf+200 .. mf+215; the shadow cell of w4 (base s7, atom 23, offset 86), writable. *)
Definition w4_mf1 : YP09.region := YP09.mkRegion (Some 9%nat) 64 216 200 216
[YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 176 (CVal 8 (SOff 33 0))].
Definition w4_sh1 : YP09.region := YP09.mkRegion (Some 23%nat) 86 87 86 87 [].
Definition ss_w41 : sstate := mkSS 0x14c8 sr_atoms [w4_mf1; w4_sh1] None (mkFacts [] [] []).
(* Run 2 (+0x14f0, 0x81c64 .. the call at 0x81c74): mf+160 = t_out (atom 32), read-only. *)
Definition w4_mf2 : YP09.region := YP09.mkRegion (Some 9%nat) 160 168 160 160
[YP09.mkChunk 160 (CVal 8 (SOff 32 0))].
Definition ss_w42 : sstate := mkSS 0x14f0 sr_atoms [w4_mf2] None (mkFacts [] [] []).
(* Run 3 (+0x1504, 0x81c78 .. 0x81c98): mf+168 = the shadow base (atom 32) and mf+208 = 4, read-only; the NUL
   byte w4 + 4 (base s2, atom 18), writable. *)
Definition w4_mf3 : YP09.region := YP09.mkRegion (Some 9%nat) 168 216 168 168
[YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 208 (CVal 8 (SLit 4))].
Definition w4_nul3 : YP09.region := YP09.mkRegion (Some 18%nat) 4 5 4 5 [].
Definition ss_w43 : sstate := mkSS 0x1504 sr_atoms [w4_mf3; w4_nul3] None (mkFacts [] [] []).

Lemma w4_m8 : forall a, a mod 32 = 0 -> (a + 208) mod 8 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->].
exists (4 * p + 26). ring.
Qed.
Lemma w4_dec_pos : forall v mn, 1 <= put_dec_c.dec_len v mn.
Proof.
intros v mn. unfold put_dec_c.dec_len, IdentSpec.DEC. rewrite length_app.
assert (H : (1 <= length (IdentSpec.dec_digits (S (Z.to_nat (Z.log2 v))) v))%nat).
{ cbn [IdentSpec.dec_digits]. rewrite length_app. cbn [length]. lia. }
lia.
Qed.
Lemma w4_zsh : forall (rdr : reader) lo len x n, zero_shadow rdr SHADOW_OFF lo len -> 0 <= lo ->
  lo + 64 <= x -> 0 < n -> x + n + 96 <= lo + len ->
  range_addressable rdr SHADOW_OFF x n /\ shadow_hull_vis rdr x n.
Proof.
intros rdr lo len x n Hz Hlo Hx Hn Hxn. unfold zero_shadow in Hz. split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8))
    by (unfold shadow_of_addr; lia).
  apply Hz. clear Hz. lia.
- intros s Hs. unfold shadow_addr in Hs.
  replace s with (shadow_of_addr SHADOW_OFF lo + (s - SHADOW_OFF - lo / 8)) by (unfold shadow_of_addr; lia).
  rewrite Hz; [discriminate|]. clear Hz. unfold SHADOW_OFF in *. lia.
Qed.
(* The UBSan bound test at 0x81c8c: the complement of &w4 is far above the counter 4. *)
Lemma w4_br_not : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1)))) (sv_denot E (SLit 4)) = false.
Proof.
intros E n v H Hv. rewrite YI04.branch_ltu_U, U_SAlu, (U_atom E n v H ltac:(lia)), !U_SLit.
cbn [zalu_raw]. replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
rewrite lxor_allones by lia. rewrite !zcanon_id by (unfold M64; lia). apply Z.ltb_ge. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation AJ g pos lyc Sc W mem md k := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k).


(* Where the entry's frame and the machine frame lie, from the journal at any state of the walk. *)
Lemma w4_geo : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf ->
  frame_addr lyc 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
  in_app (SFa g pos) 1024 /\ alloc_ceiling <= mf - 2 * ESTACK /\ e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\
  2 * ESTACK + 336 <= LLVMF_STK /\ alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + LLVMF_STK <= e_sp0 g /\
  e_sp0 g <= ly_stk_hi lyc.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct Hly as (_ & _ & _ & _ & _ & EF0 & _ & _ & _ & Eslo & Eshi & _).
assert (EF : frame_addr lyc 4 pos = SFa g pos).
{ unfold SFa, frame_addr. rewrite EF0. reflexivity. }
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin) as (F1 & F2 & F3).
rewrite EF in F1, F2, F3. change (fs_frame_bytes 4) with 1024 in F2, F3.
pose proof HSTK as HS. unfold STK_LLVMF, ASTACK in HS. unfold ESTACK.
clear HJ HAR Hin Hfrs EF0.
split; [exact EF|]. split; [lia|]. split; [lia|]. split; [exact F3|]. split; [lia|]. split; [exact Hal16|].
split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma w4_twr_fr : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k sp q n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf -> mf <= sp ->
  SFa g pos <= q -> q + n <= SFa g pos + 1024 ->
  twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem sp q n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k sp q n HJ Hfrs Hmf Hsp Hq1 Hq2 a Ha.
destruct (w4_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf) as (EF & G1 & G2 & G3 & G4 & _).
assert (Hw : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF.
  change (fs_frame_bytes 4) with 1024. lia. }
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
clear HJ.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. unfold ESTACK in *. lia.
Qed.

Lemma w4_stk : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k q n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf ->
  mf <= q -> 0 < n -> q + n + 96 <= e_sp0 g ->
  twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf q n /\
  tsrc_ok W mem mf q n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k q n HJ Hfrs Hmf Hq Hn Hqn.
destruct (w4_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf)
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  ltac:(left; reflexivity)) as HZ.
cbn [fst snd] in HZ.
destruct (w4_zsh (aview SEGS (w_H W) mem) (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) q n HZ
  ltac:(lia) ltac:(lia) Hn ltac:(lia)) as [HRA HHV].
assert (Hw : forall a, q <= a < q + n ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ intros a Ha. left. lia. }
split.
- intros a Ha. destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hw a Ha)) as [Hp Ho].
  split; [exact (Hw a Ha)|]. split; [exact Hp|]. split; [exact Ho|]. lia.
- split; [intros a Ha; split; [apply aview_some_of_apresent; apply Hpres; lia | lia]|].
  split; [exact HRA|]. split; [exact HHV|].
  split; [right; lia|]. lia.
Qed.

(* put_dec at 0x81c60 / 0x81c74: b = w4 (SF+688), p = mf+208 holding n, v <= 40, mn = 2, the 8 bytes of w4
   addressable (0x81c44 cleared their shadow cell). *)
Lemma w4_pd : AR_laws SEGS B -> identb_prog_sig_ok (PI := PI) -> put_dec.tput_dec_spec B ->
  STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB ->
  forall (g : ectx) (pos mf : Z) (W : world SEGS) (regs : bvmap 5 word) mem md lyc Sc k n v retk,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> 0 <= k <= EV_LLVMF ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (SFa g pos + V_w4) -> getr regs 11 = w64 (mf + M_n1) ->
  getr regs 12 = w64 v -> getr regs 13 = w64 2 -> 0 <= v <= 40 ->
  0 <= n -> n + put_dec_c.dec_len v 2 <= N_w4 ->
  val_mem SEGS (rd W mem) (mf + M_n1) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (SFa g pos + V_w4) N_w4 ->
  SRr SEGS W (cfg_at SEGS (SIGMA IB_put_dec) regs mem md)
    (put_dec.tput_dec_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
       lyc Sc W mem k regs (SFa g pos + V_w4) (mf + M_n1) n v 2).
Proof.
intros LAWS PSIG HPD HSTK HEV g pos mf W regs mem md lyc Sc k n v retk HEP HJ Hfrs Hk Hmf Hmf32 R1 Hrk Hrk2
  R2 R3 R4 R10 R11 R12 R13 Rv Hn Hlen HVM HRA.
destruct (w4_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs (proj1 Hmf))
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof (w4_dec_pos v 2) as HD.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HPS : put_dec.PUT_DEC_STK = 4208) by reflexivity.
assert (Hsp : spZ regs = mf) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hsig : SIGMA IB_put_dec = BASE + AF_put_dec) by (apply PSIG; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
destruct HEP as (_ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
destruct (w4_stk LAWS HSTK g pos mf lyc Sc W mem md k (mf + M_n1) 8 HJ Hfrs (proj1 Hmf)
  ltac:(unfold M_n1; lia) ltac:(lia) ltac:(unfold M_n1; lia)) as [WP SP].
assert (WB : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf
  (SFa g pos + V_w4 + n) (put_dec_c.dec_len v 2)).
{ apply (w4_twr_fr LAWS HSTK g pos mf lyc Sc W mem md k mf); [exact HJ | exact Hfrs | exact (proj1 Hmf) | lia | |];
  unfold V_w4, N_w4 in *; lia. }
assert (SB : tsrc_ok W mem mf (SFa g pos + V_w4 + n) (put_dec_c.dec_len v 2)).
{ split; [intros a Ha; split; [apply aview_some_of_apresent; exact (proj1 (proj2 (WB a Ha))) | unfold V_w4, N_w4 in *; lia]|].
  split; [eapply range_addressable_sub; [exact HRA | unfold V_w4, N_w4 in *; lia | unfold V_w4, N_w4 in *; lia]|].
  split.
  { apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W mem md 4 pos _ _ (proj1 HJ)
      ltac:(rewrite Hfrs; left; reflexivity));
      [rewrite EF; unfold V_w4; lia | rewrite EF; change (fs_frame_bytes 4) with 1024; unfold V_w4, N_w4 in *; lia | lia]. }
  split; [apply (amem_range_sub_app (SFa g pos) 1024 _ _ G3 G2); unfold V_w4, N_w4 in *; lia|].
  unfold V_w4, N_w4 in *; lia. }
rewrite Hsig.
refine (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k regs
  (SFa g pos + V_w4) (mf + M_n1) n v 2 HJ _ _ R3 R4 R10 R11 _ _ R13 ltac:(lia) _ _ _ _ _ _ _ HVM _ _ _ _ _ _ _ _).
- rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hrk2].
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
- left. rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. lia.
- rewrite Hsp. exact Hmf32.
- rewrite Hsp, HPS. lia.
- rewrite Hsp. lia.
- rewrite Hfrs. cbn [length]. lia.
- unfold M_n1. exact (w4_m8 mf Hmf32).
- unfold V_w4. lia.
- exact Hn.
- rewrite Hsp. exact WP.
- rewrite Hsp. exact WB.
- rewrite Hsp. exact SP.
- rewrite Hsp. exact SB.
- right. unfold M_n1, V_w4, N_w4 in *. lia.
- left. rewrite Hsp. unfold M_n1. lia.
- right. rewrite Hsp, HPS. unfold V_w4, N_w4 in *. lia.
- unfold put_dec.EV_PUT_DEC. lia.
Qed.

(* The start states of the three runs. *)
Lemma w4_ent1 : forall (W : world SEGS) (regs : bvmap 5 word) mem mf sh SF ti,
  getr regs 9 = w64 mf -> getr regs 23 = w64 sh ->
  alloc_ceiling <= mf -> mf + 216 <= 2 ^ 47 -> 0 <= sh -> sh + 87 <= alloc_ceiling ->
  0 <= SF < 2 ^ 47 -> 0 <= ti < 256 ->
  val_mem SEGS (rd W mem) (mf + 64) 8 SF -> val_mem SEGS (rd W mem) (mf + 176) 8 ti ->
  (forall o, 200 <= o < 216 -> apresent (w_H W) mem (mf + o)) -> apresent (w_H W) mem (sh + 86) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SF; Z_to_bv 64 ti])) ss_w41
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x14c8)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf sh SF ti R9 R23 H1 H2 H3 H4 H5 H6 V64 V176 P1 P2.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs [Z_to_bv 64 SF; Z_to_bv 64 ti])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SF; Z_to_bv 64 ti]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (U23 : bv_unsigned (ew E 23) = sh).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl), R23.
  apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ti) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
rewrite restrict_mkst_fx. unfold ss_w41. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold w4_mf1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply P1. lia.
    * constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 32 0) SF);
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V64].
      -- apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 33 0) ti);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V176].
  + unfold w4_sh1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace o with 86 by lia. apply (apresent_writable SEGS). exact P2.
- apply pairwise_disjoint_of_extents. unfold w4_mf1, w4_sh1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert H1 H2 H3 H4. clear. intros. repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

Lemma w4_ent2 : forall (W : world SEGS) (regs : bvmap 5 word) mem mf vo,
  getr regs 9 = w64 mf -> alloc_ceiling <= mf -> mf + 216 <= 2 ^ 47 -> 0 <= vo < 256 ->
  val_mem SEGS (rd W mem) (mf + 160) 8 vo ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 vo])) ss_w42
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x14f0)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf vo R9 H1 H2 H3 V160.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs [Z_to_bv 64 vo])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 vo]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 vo) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold ss_w42. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold w4_mf2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 32 0) vo);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V160].
- apply pairwise_disjoint_of_extents. unfold w4_mf2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

Lemma w4_ent3 : forall (W : world SEGS) (regs : bvmap 5 word) mem mf s2,
  getr regs 9 = w64 mf -> getr regs 18 = w64 s2 ->
  alloc_ceiling <= mf -> mf + 216 <= 2 ^ 47 -> 0 <= s2 -> s2 + 5 <= alloc_ceiling ->
  val_mem SEGS (rd W mem) (mf + 168) 8 SHADOW_OFF -> val_mem SEGS (rd W mem) (mf + 208) 8 4 ->
  apresent (w_H W) mem (s2 + 4) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) ss_w43
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1504)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf s2 R9 R18 H1 H2 H3 H4 V168 V208 P4.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew E 18) = s2).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), R18.
  apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold ss_w43. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold w4_mf3, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia | exact V168].
    * apply (chunk_ok_val SEGS E _ mf 208 8 (SLit 4) 4); [reflexivity | lia | lia | exact V208].
  + unfold w4_nul3, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace o with 4 by lia. apply (apresent_writable SEGS). exact P4.
- apply pairwise_disjoint_of_extents. unfold w4_mf3, w4_nul3, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert H1 H2 H3 H4. clear. intros. repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

(* A value a run stored, read off the state after a run that ends in a call. *)
Lemma w4_chunk : forall E ss ms i r off (n : N) e b v,
  st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r -> base_val E (YP09.r_base r) = b ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (ms_mem ms) (b + off) (N.to_nat n) v.
Proof.
intros E ss ms i r off n e b v HS Hi Hb Hin He Hv Hn.
pose proof (st_ok_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hc). rewrite Hb in Hc.
apply (val_of_chunk_ok SEGS E (ms_mem ms) b off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hc _ Hin).
Qed.
Lemma w4_chunk_pi : forall E ss ms i r off (n : N) e b v,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> base_val E (YP09.r_base r) = b ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (ms_mem ms) (b + off) (N.to_nat n) v.
Proof.
intros E ss ms i r off n e b v HS Hi Hb Hin He Hv Hn.
pose proof (st_ok_pi_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hc). rewrite Hb in Hc.
apply (val_of_chunk_ok SEGS E (ms_mem ms) b off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hc _ Hin).
Qed.

(* What a run or a call may write, and where the facts of the cut live. *)
Definition w4_zone (mf sp0 SF sh a : Z) : Prop :=
  (mf <= a < sp0) \/ (SF <= a < SF + 1024) \/ (sh <= a < sh + 128).
Definition w4_wr (mf SF sh a : Z) : Prop :=
  (mf + 200 <= a < mf + 216) \/ (SF + 688 <= a < SF + 693) \/ a = sh + 86.

(* A callee-saved register is kept by a call. *)
Lemma w4_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' ->
  ((bv_unsigned r =? 2) || (bv_unsigned r =? 3) || (bv_unsigned r =? 4) || (bv_unsigned r =? 8) ||
   (bv_unsigned r =? 9) || ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27)))%bool = true ->
  getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hb.
assert (Hc : acallee_saved (bv_unsigned r)).
{ unfold acallee_saved. repeat rewrite Bool.orb_true_iff in Hb. rewrite Bool.andb_true_iff in Hb.
  rewrite !Z.eqb_eq, !Z.leb_le in Hb. lia. }
pose proof (H (bv_unsigned r) Hc) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma w4_dl : forall v, 0 <= v <= 40 -> put_dec_c.dec_len v 2 = 2.
Proof. intros v Hv. unfold put_dec_c.dec_len. rewrite (SlotModel.DEC2_len v Hv). reflexivity. Qed.
Lemma w4_ra : forall (rdr : reader) F, F mod 8 = 0 -> rdr (SHADOW_OFF + F / 8 + 86) = Some 0 ->
  range_addressable rdr SHADOW_OFF (F + V_w4) N_w4.
Proof.
intros rdr F H8 H x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
unfold V_w4, N_w4 in Hx.
assert (E : x / 8 = F / 8 + 86) by (clear - H8 Hx; Z.div_mod_to_equations; lia).
rewrite E, Z.add_assoc. exact H.
Qed.
Lemma w4_io : forall md md', aos_step [] md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros md md' H.
pose proof (aos_step_closed_same_io [] md md' ltac:(intros (r & [] & _)) H) as (E1 & _ & E3 & _).
unfold m_fds, m_fs. rewrite E1, E3. split; reflexivity.
Qed.

Lemma w4_meter : ameter_laws MT -> forall S0 S2 S3 k,
  mo_le MT S0 S2 (k * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) -> mo_le MT S2 S3 0 ->
  mo_le MT S0 S3 (k * MEV MT) /\ mo_ok MT S3 ((EV_LLVMF - k) * MEV MT).
Proof.
intros MTL S0 S2 S3 k MLE MOK M23.
split.
- pose proof (mo_le_trans MT MTL _ _ _ _ _ MLE M23) as X. rewrite Z.add_0_r in X. exact X.
- apply (mo_ok_step MT MTL S2 S3 0); [|exact M23]. rewrite Z.add_0_l. exact MOK.
Qed.

(* What a put_dec call keeps of the machine frame and of the entry's frame and its shadow. *)
Lemma w4_ckeep : forall pos mf SF sh lyc Sc (W : world SEGS) memc (W' : world SEGS) mem' (Ec : Z -> Prop),
  tcj_kept B put_dec.PUT_DEC_STK lyc Sc W memc W' mem' mf Ec -> alloc_ceiling <= mf ->
  In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SF -> sh = shadow_addr SF ->
  forall a, (mf <= a < 2 ^ 64 \/ SF <= a < SF + 1024 \/ sh <= a < sh + 128) -> ~ Ec a ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a.
Proof.
intros pos mf SF sh lyc Sc W memc W' mem' Ec (K1 & _ & _ & K4 & _) Hmf Hin EF Esh a Ha HE.
destruct Ha as [Ha | Ha].
- apply K1; [lia | lia | exact HE].
- apply (K4 4 pos a Hin); [|exact HE]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, <- Esh.
  change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. destruct Ha as [Ha|Ha]; [left|right]; lia.
Qed.

Lemma w4_garr8_app : forall (m : word -> option byte) a l1 l2, garr8 SEGS m a l1 ->
  garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl | Hl].
- rewrite app_nth1 by exact Hl. exact (H1 j Hl).
- rewrite app_nth2 by exact Hl. destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma w4_garr8_1 : forall (m : word -> option byte) a v, val_mem SEGS m a 1 v -> 0 <= v < 256 ->
  garr8 SEGS m a [v].
Proof.
intros m a v Hv Hr j Hj. cbn [length] in Hj. replace j with 0%nat by lia. cbn [nth Z.of_nat].
rewrite Z.add_0_r. split; [exact Hv | exact Hr].
Qed.
Lemma w4_has_dash_len : forall l, SlotModel.has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.
Lemma w4_tok_len : forall l d,
  length (SlotModel.tok_go d l) = (length l - (if negb d && SlotModel.has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b r IH]; intros d; [reflexivity|].
assert (HD : SlotModel.has_dash (b :: r) = (RcIdentModel.bz b =? 45) || SlotModel.has_dash r) by reflexivity.
rewrite HD. destruct d.
- cbn [SlotModel.tok_go negb andb Datatypes.length]. rewrite IH. cbn [negb andb]. lia.
- destruct (RcIdentModel.bz b =? 45) eqn:E; cbn [SlotModel.tok_go negb andb orb Datatypes.length]; rewrite E;
  cbn [andb orb].
  + rewrite IH. cbn [negb andb]. lia.
  + cbn [Datatypes.length]. rewrite IH. cbn [negb andb]. destruct (SlotModel.has_dash r) eqn:D; [|lia].
    pose proof (w4_has_dash_len r D). lia.
Qed.
Lemma w4_tk_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof.
intro inp. unfold SlotModel.n_TK, SlotModel.TOK, SlotModel.n_lt, SlotModel.n_ln. rewrite w4_tok_len.
cbn [negb andb]. destruct (SlotModel.has_dash (SlotModel.n_EXP_NM inp)) eqn:D; [|lia].
pose proof (w4_has_dash_len _ D). lia.
Qed.

#[local] Notation JKEEP := (jkeep B).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC3 := (jc3 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* The cut at +0x1524 from the cut at +0x14c8, what the piece kept and what it wrote. *)
Lemma w4_mk_jc3 : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf nm tk dp st ly2 S2 (W2 : world SEGS) regs2 mem2 md2 ly5 S5 (W5 : world SEGS)
    regs6 mem6 md6 k,
  k = 4 * Z.of_nat (m_nrec g) + 7 ->
  AJ g pos ly2 S2 W2 mem2 md2 k -> AJ g pos ly5 S5 W5 mem6 md6 k ->
  frames S2 = [(4, pos)] -> frames S5 = [(4, pos)] -> ablocks B ly5 S5 = ablocks B ly2 S2 ->
  0 <= k <= EV_LLVMF -> mo_le MT (e_S g) S5 (k * MEV MT) -> mo_ok MT S5 ((EV_LLVMF - k) * MEV MT) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  getr regs2 25 = w64 (SFa g pos + V_nm) -> getr regs2 26 = w64 (SFa g pos + V_dp) ->
  sh_zero W2 mem2 (SFa g pos + V_nm) N_nm -> sh_zero W2 mem2 (SFa g pos + V_dp) N_dp ->
  val_mem SEGS (rd W2 mem2) (SFa g pos + V_nm) 1 0 -> val_mem SEGS (rd W2 mem2) (mf + 136) 8 st ->
  jstem B LLVMF_STK g pos W2 mem2 st ->
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] -> getr regs6 r = getr regs2 r) ->
  getr regs6 6 = w64 SHADOW_OFF -> getr regs6 18 = w64 (SFa g pos + V_w4) ->
  (forall a, w4_zone mf (e_sp0 g) (SFa g pos) (shadow_addr (SFa g pos)) a ->
     ~ w4_wr mf (SFa g pos) (shadow_addr (SFa g pos)) a -> aview SEGS (w_H W5) mem6 a = aview SEGS (w_H W2) mem2 a) ->
  (forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
     aview SEGS (w_H W5) mem6 (b + i) = aview SEGS (w_H W2) mem2 (b + i)) ->
  aview SEGS (w_H W5) mem6 (shadow_addr (SFa g pos) + 86) = Some 0 ->
  bytes_at8 W5 mem6 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) ->
  val_mem SEGS (rd W5 mem6) (mf + M_n2) 8 0 ->
  JC3 g pos mf nm tk dp st W5 (cfg_at SEGS (BASE + 0x1524) regs6 mem6 md6).
Proof.
intros LAWS HSTK g pos mf nm tk dp st ly2 S2 W2 regs2 mem2 md2 ly5 S5 W5 regs6 mem6 md6 k Hkv HJ HJf Hfrs Hfrsf Hblf
  Hk MLE MOK HC HK R25 R26 SZnm SZdp Vnm V136 Hstem RK R6 R18 KEEP BKEEP S86 BW4 V200.
subst k.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
destruct Hstem as (Hany & Hstb & Hstd & Hstr & Hsta & Hst0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w4_geo LAWS HSTK g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs (proj1 Hmfb)) as (EF & G1 & G2 & G3 & G4 & G5 & G6 & _).
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs) as (_ & _ & _ & HSF64 & _ & _ & Hsfsh).
pose proof HJ as (HAR2 & _).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hsh : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
  by (clear - Esh G1 G2 C1; unfold SHADOW_OFF in Esh; lia).
assert (Hmf0 : alloc_ceiling + 8192 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - G4 G6 Hmfb HES; lia).
(* moving a fact of the cut's memory to the end memory *)
assert (VMS : forall a (n : nat) v, (mf <= a /\ a + Z.of_nat n <= mf + 200) \/ (mf + 216 <= a /\ a + Z.of_nat n <= e_sp0 g) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W5 mem6) a n v).
{ intros a n v Ha Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W5) mem2 mem6 a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; unfold w4_zone, w4_wr; clear - Ha Hkk Hmf0 Hmfb Hsh G2; lia. }
assert (VMF : forall off (n : nat) v, 0 <= off -> (off + Z.of_nat n <= 688 \/ 693 <= off) -> off + Z.of_nat n <= 1024 ->
  val_mem SEGS (rd W2 mem2) (SFa g pos + off) n v -> val_mem SEGS (rd W5 mem6) (SFa g pos + off) n v).
{ intros off n v H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W5) mem2 mem6 (SFa g pos + off) (SFa g pos + off) n v); [|exact Hv].
  intros kk Hkk. apply KEEP; unfold w4_zone, w4_wr; clear - H0 H1 H2 Hkk Hmf0 G2 Hsfsh Hsh; lia. }
assert (GF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 688 ->
  garr8 SEGS (rd W2 mem2) (SFa g pos + off) l -> garr8 SEGS (rd W5 mem6) (SFa g pos + off) l).
{ intros off l H0 H1 Hg. apply (j_garr8_moved SEGS (w_H W2) (w_H W5) mem2 mem6 (SFa g pos + off) l); [|exact Hg].
  intros kk Hkk. apply KEEP; unfold w4_zone, w4_wr; clear - H0 H1 Hkk Hmf0 G2 Hsfsh Hsh; lia. }
assert (SHF : forall off n, 0 <= off -> 0 <= n -> off + n <= 688 ->
  sh_zero W2 mem2 (SFa g pos + off) n -> sh_zero W5 mem6 (SFa g pos + off) n).
{ intros off n H0 Hn H1 Hz. unfold sh_zero in *.
  apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W5) mem6) SHADOW_OFF (SFa g pos + off) n);
  [|exact Hz].
  intros ii Hii. apply KEEP; unfold w4_zone, w4_wr, shadow_of_addr;
  clear - H0 Hn H1 Hii Esh HSF64 Hmf0 G1 G2 Hsfsh Hsh C1; unfold SHADOW_OFF in *; lia. }
assert (SHB : forall off n, 0 <= off -> 0 <= n -> off + n + 7 <= 688 ->
  sh_blk W2 mem2 (SFa g pos + off) n -> sh_blk W5 mem6 (SFa g pos + off) n).
{ intros off n H0 Hn H1 Hz. unfold sh_blk in *.
  apply (j_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W5) mem6) SHADOW_OFF (SFa g pos + off) n);
  [|exact Hz].
  intros ii Hii. apply KEEP; unfold w4_zone, w4_wr, shadow_of_addr;
  clear - H0 Hn H1 Hii Esh HSF64 Hmf0 G1 G2 Hsfsh Hsh C1; unfold SHADOW_OFF in *; lia. }
assert (GB : forall b m l, In (b, m) (ablocks B ly2 S2) -> Z.of_nat (length l) <= req_size m ->
  garr8 SEGS (rd W2 mem2) b l -> garr8 SEGS (rd W5 mem6) b l).
{ intros b m l Hb Hl Hg. apply (j_garr8_moved SEGS (w_H W2) (w_H W5) mem2 mem6 b l); [|exact Hg].
  intros kk Hkk. apply (BKEEP b m kk Hb). clear - Hkk Hl; lia. }
pose proof HJf as (_ & _ & _ & _ & Hio & _).
destruct (w4_io _ _ Hio) as [Efd Efs].
unfold jc3, acut.
exists ly5, S5, regs6, mem6, md6.
split; [reflexivity|]. split; [exact HJf|]. split; [exact Hfrsf|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  split; [rewrite (RK 2%bv ltac:(cbn; tauto)); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(cbn; tauto)); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(cbn; tauto)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact Rtp|].
  split; [apply VMS; [clear; lia | exact V16]|].
  split; [apply VMS; [clear; lia | exact V64]|].
  split; [apply VMS; [clear; lia | exact V192]|].
  split; [apply VMS; [clear; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | exact V104]|].
  split; [apply VMF; [clear; lia | clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [rewrite Efs; reflexivity|].
  pose proof HPRE as (_ & _ & _ & _ & Hpn & Hlen & _).
  unfold bytes_at8 in *. eapply (j_garr8_moved SEGS (w_H W2) (w_H W5) mem2 mem6); [|exact Hinb].
  intros kk Hkk. rewrite length_map, <- Hlen in Hkk.
  destruct Hpn as [(Hn0 & _) | (_ & Hine)]; [clear - Hkk Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
  pose proof (req_size_pos (e_n g) ltac:(clear - Hkk; lia)) as [_ Hrq].
  apply (BKEEP _ _ kk Hine2). clear - Hkk Hrq; lia. }
split.
{ unfold jkeep.
  split; [destruct Hbl as [Hp Hf]; split; [rewrite Hblf; exact Hp | exact Hf]|].
  split; [unfold sh_reg in *; rewrite (RK 23%bv ltac:(cbn; tauto)); exact Rs7|].
  split; [rewrite (RK 24%bv ltac:(cbn; tauto)); exact R24|].
  split; [rewrite (RK 21%bv ltac:(cbn; tauto)); exact R21|].
  split; [apply VMS; [clear; lia | exact V152]|].
  split; [apply VMS; [clear; lia | exact V184]|].
  split; [apply VMS; [clear; lia | exact V144]|].
  split; [apply VMS; [clear; lia | exact V128]|].
  split; [apply VMS; [clear; lia | exact V120]|].
  split; [apply VMS; [clear; lia | exact V176]|].
  split; [apply VMS; [clear; lia | exact V160]|].
  split; [apply VMS; [clear; lia | exact V112]|].
  split.
  { destruct Hid as (Hidb & Hidz & Hidk). unfold id_at. split; [|split].
    - unfold bytes_at8 in *. apply GF; [unfold V_id; clear; lia | | exact Hidb].
      rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE. clear; lia.
    - apply SHF; [unfold V_id; clear; lia | unfold N_id; clear; lia | unfold V_id, N_id; clear; lia | exact Hidz].
    - apply SHB; [unfold V_id; clear; lia | unfold N_id; clear; lia | unfold V_id, N_id; clear; lia | exact Hidk]. }
  intros Hr0. destruct (Hbufs Hr0) as (Bn & Bt & Bd).
  destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (_ & Fn & Ft & Fd).
  destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_caps (e_pl g)) as (Cn & Ct & Cd).
  destruct Hbl as [Hperm _].
  assert (Inn : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
  assert (Int : In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); right; left; reflexivity).
  assert (Ind : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); right; right; left; reflexivity).
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(clear; lia)) as [_ Qn].
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(clear; lia)) as [_ Qt].
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(clear; lia)) as [_ Qd].
  pose proof (w4_tk_len (e_pl g)) as Ltk.
  unfold bytes_at8 in *. split; [|split].
  - apply (GB nm _ _ Inn); [|exact Bn]. rewrite length_map, length_app. cbn [length].
    unfold SlotModel.n_ln in Fn. clear - Fn Qn. lia.
  - apply (GB tk _ _ Int); [|exact Bt]. rewrite length_map, length_app. cbn [length].
    clear - Ft Qt Ltk. lia.
  - apply (GB dp _ _ Ind); [|exact Bd]. rewrite length_map, length_app. cbn [length].
    unfold SlotModel.n_ld in Fd. clear - Fd Qd. lia. }
split; [exact R6|].
split; [exact R18|].
split; [rewrite (RK 25%bv ltac:(cbn; tauto)); exact R25|].
split; [rewrite (RK 26%bv ltac:(cbn; tauto)); exact R26|].
split; [apply SHF; [unfold V_nm; clear; lia | unfold N_nm; clear; lia | unfold V_nm, N_nm; clear; lia | exact SZnm]|].
split; [apply SHF; [unfold V_dp; clear; lia | unfold N_dp; clear; lia | unfold V_dp, N_dp; clear; lia | exact SZdp]|].
split.
{ unfold sh_zero, zero_shadow. intros i Hi.
  replace (shadow_of_addr SHADOW_OFF (SFa g pos + V_w4) + i) with (shadow_addr (SFa g pos) + 86)
    by (unfold shadow_of_addr, V_w4; unfold N_w4 in Hi; rewrite Esh; clear - Hi HSF64; lia).
  exact S86. }
split; [exact BW4|].
split; [exact V200|].
split; [apply VMF; [unfold V_nm; clear; lia | unfold V_nm; clear; lia | unfold V_nm; clear; lia | exact Vnm]|].
split; [apply VMS; [clear; lia | exact V136]|].
pose proof (SlotModel.n_stem_len (e_pl g)) as Lst.
unfold jstem. split; [exact Hany|].
split.
{ destruct Hany as [Est | Hall].
  - rewrite Est. rewrite Est in Hstb. unfold bytes_at8 in *.
    replace (SFa g pos + V_id + 3) with (SFa g pos + 355) in * by (unfold V_id; clear; lia).
    apply GF; [clear; lia | | exact Hstb].
    rewrite length_map, length_app. cbn [length]. clear - Lst. lia.
  - exact (proj1 (Hall _ _ _ _ _ _ HJf)). }
split; [exact Hstd|].
split.
{ destruct Hany as [Est | Hall].
  - apply (range_addressable_agree (aview SEGS (w_H W2) mem2)); [|exact Hstr].
    intros x Hx. unfold shadow_of_addr. apply KEEP; unfold w4_zone, w4_wr; rewrite Est in Hx; unfold V_id in Hx;
    clear - Hx Lst Esh HSF64 Hmf0 G1 G2 Hsfsh Hsh C1; unfold SHADOW_OFF in *; lia.
  - exact (proj2 (Hall _ _ _ _ _ _ HJf)). }
split; [exact Hsta | exact Hst0].
Qed.

Lemma j_w4 : j_w4_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
unfold j_w4_stmt.
intros LAWS HSTK HEV HPD PSIG MTL HMT0 g pos mf nm tk dp st W2 c2 Hc Hwok.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP. pose proof (paj_branch (PI := PI)) as BR.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & R12 & R22 & R25 & R26 & SZnm & SZdp & Vnm & V136 & Hstem).
pose proof HJ as HJ0.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
unfold sh_reg in Rs7.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
destruct (w4_geo LAWS HSTK g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs (proj1 Hmfb))
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR2 Hin4) as (Hf32 & _).
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs) as (_ & _ & _ & HSF64 & _ & _ & Hsfsh).
rewrite EF in Hf32.
pose proof (SlotModel.wok_chans (e_pl g) Hwok) as [Hti Hto].
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *. set (sh := shadow_addr SF) in *.
set (ti := SlotModel.t_in (e_pl g)) in *. set (vo := SlotModel.t_out (e_pl g)) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh : 0 <= sh /\ sh + 128 <= alloc_ceiling) by (clear - Esh G1 G2 C1; unfold SHADOW_OFF in Esh; lia).
assert (Hmf0 : alloc_ceiling + 8192 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - G4 G6 Hmfb HES; lia).
(* ---- run 1: 0x81c3c .. the call at 0x81c60 ---- *)
assert (P86 : apresent (w_H W2) mem2 (sh + 86)).
{ apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly2 S2 W2 mem2 md2 _ (sh + 86) HJ ltac:(
    right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
    unfold in_zr; cbn [fst snd]; rewrite EF, HFB; fold sh; clear; lia))). }
pose proof (w4_ent1 W2 regs2 mem2 mf sh SF ti Rs1 Rs7 ltac:(clear - Hmf0; lia) ltac:(clear - Hmf0; lia)
  ltac:(clear - Hsh; lia) ltac:(clear - Hsh; lia) ltac:(clear - G1 G2 C1; lia) ltac:(clear - Hti; lia) V64 V176
  ltac:(intros o Ho; apply Hpres; clear - Ho Hmfb G7 HES; lia) P86) as HS.
remember (Eimg (Ereg regs2 [Z_to_bv 64 SF; Z_to_bv 64 ti])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs2 r)
  by (intros n r Hn; subst E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE1 : env_agree 32 (Ereg regs2 [Z_to_bv 64 SF; Z_to_bv 64 ti]) E1)
  by (subst E1; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U9 : bv_unsigned (ew E1 9) = mf)
  by (rewrite (EE1 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; clear - Hmf0 C1; lia).
assert (U23 : bv_unsigned (ew E1 23) = sh)
  by (rewrite (EE1 23%nat 23%bv eq_refl), Rs7; apply unsigned_lit_small; clear - Hsh C1; lia).
assert (E32a : ew E1 32 = Z_to_bv 64 SF)
  by (subst E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33a : ew E1 33 = Z_to_bv 64 ti)
  by (subst E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
clear HE1.
unfold cfg_at. change (w64 (BASE + 0x14c8)) with (Z_to_bv 64 (BASE + 0x14c8)).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 0x14c8)) mem2 (seg_rom SEGS))) in HJ.
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold ss_w41 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold w4_mf1, w4_sh1 in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite U9 in Ha. left. clear - Ha Hmfb G7 HES. lia.
  - rewrite U23 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr; cbn [fst snd]. rewrite EF, HFB. fold sh. clear - Ha. lia. }
rename ms into ms1. rename HJ into HJ1. rename HS into HS1.
assert (RK1 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
  getr (ms_regs ms1) r = getr regs2 r).
{ refine (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W2) ms1) regs2 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] HS1 HAE1 _).
  vm_compute. reflexivity. }
prreg HS1 (1%bv : bv 5) Q1. prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11.
prreg HS1 (12%bv : bv 5) Q12. prreg HS1 (13%bv : bv 5) Q13. prreg HS1 (18%bv : bv 5) Q18.
rewrite E32a in Q10. rewrite unsigned_lit_small in Q10 by (clear - G1 G2 C1; lia).
rewrite E32a in Q18. rewrite unsigned_lit_small in Q18 by (clear - G1 G2 C1; lia).
rewrite U9 in Q11. rewrite E33a in Q12.
(* what run 1 stored: the two counters and the shadow cell of w4 *)
assert (W200 : val_mem SEGS (rd W2 (ms_mem ms1)) (mf + 200) 8 0).
{ refine (w4_chunk E1 _ (restrict (w_H W2) ms1) 0 _ 200 8 (SLit 0) mf 0 HS1 eq_refl _ _ eq_refl _ _).
  - cbn [base_val YP09.r_base]. exact U9.
  - cbn [YP09.r_chunks]. left. reflexivity.
  - clear; lia.
  - clear; lia. }
assert (W208 : val_mem SEGS (rd W2 (ms_mem ms1)) (mf + 208) 8 0).
{ refine (w4_chunk E1 _ (restrict (w_H W2) ms1) 0 _ 208 8 (SLit 0) mf 0 HS1 eq_refl _ _ eq_refl _ _).
  - cbn [base_val YP09.r_base]. exact U9.
  - cbn [YP09.r_chunks]. right. left. reflexivity.
  - clear; lia.
  - clear; lia. }
assert (W86 : val_mem SEGS (rd W2 (ms_mem ms1)) (sh + 86) 1 0).
{ refine (w4_chunk E1 _ (restrict (w_H W2) ms1) 1 _ 86 1 (SLit 0) sh 0 HS1 eq_refl _ _ eq_refl _ _).
  - cbn [base_val YP09.r_base]. exact U23.
  - cbn [YP09.r_chunks]. left. reflexivity.
  - clear; lia.
  - clear; lia. }
(* what run 1 kept: every byte outside its two windows *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 200 <= a < mf + 216 \/ a = sh + 86) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. apply (kept_of_frame E1 (ss_mem ss_w41) (w_H W2) mem2 (ms_mem ms1)
    (fun x => mf + 200 <= x < mf + 216 \/ x = sh + 86) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold ss_w41, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U9 in Hr | rewrite U23 in Hr]; clear - Hr; lia. }
clear HF HFr HG.
(* ---- put_dec (w4, mf+208, t_in, 2) at 0x81c60 ---- *)
pmkst HS1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ refine (w4_pd LAWS PSIG HPD HSTK HEV g pos mf W2 (ms_regs ms1) (ms_mem ms1) _ ly2 S2 _ 0 ti 5360 HPRE HJ1
    Hfrs Hk Hmfb Hmf32 Q1 _ eq_refl _ _ _ Q10 Q11 Q12 Q13 _ _ _ W208 _).
  - clear; lia.
  - rewrite (RK1 2%bv ltac:(cbn; tauto)). exact Rsp.
  - rewrite (RK1 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (RK1 4%bv ltac:(cbn; tauto)). exact Rtp.
  - exact Hti.
  - clear; lia.
  - rewrite (w4_dl ti Hti). unfold N_w4. lia.
  - apply w4_ra; [exact (mod32_mod8 _ Hf32)|]. change (SFa g pos) with SF. rewrite <- Esh.
    exact (aview_of_val_mem1 SEGS _ _ _ _ W86 ltac:(clear; lia)). }
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfr3 & Hbl3 & HK3 & Hg3 & Hv3).
unfold put_dec.EV_PUT_DEC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite Q1.
rewrite (w4_dl ti Hti) in HK3, Hv3. rewrite Z.add_0_l in Hv3.
assert (Usp1 : spZ (ms_regs ms1) = mf).
{ unfold spZ. rewrite (RK1 2%bv ltac:(cbn; tauto)), Rsp. apply unsigned_lit_small. clear - Hmf0 C1. lia. }
rewrite Usp1 in HK3.
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hin43 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (w4_geo LAWS HSTK g pos mf ly3 S3 W3 mem3 md3 _ HJ3 Hfrs3 (proj1 Hmfb)) as (EF3 & _).
(* what put_dec kept *)
assert (K2 : forall a, w4_zone mf sp0 SF sh a -> ~ (mf + 208 <= a < mf + 216 \/ SF + 688 <= a < SF + 690) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms1) a).
{ intros a Hz Hw. apply (w4_ckeep pos mf SF sh ly2 S2 W2 (ms_mem ms1) W3 mem3 _ HK3 ltac:(clear - Hmf0; lia)
    Hin4 EF eq_refl a).
  - unfold w4_zone in Hz. clear - Hz G6. lia.
  - unfold M_n1, V_w4. intros Hx. apply Hw. clear - Hx. lia. }
assert (BK2 : forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  ~ (mf + 208 <= b + i < mf + 216 \/ SF + 688 <= b + i < SF + 690) ->
  aview SEGS (w_H W3) mem3 (b + i) = aview SEGS (w_H W2) (ms_mem ms1) (b + i)).
{ intros b m i Hb Hi Hw. apply (proj1 (proj2 HK3) b m i Hb Hi). unfold M_n1, V_w4. intros Hx. apply Hw. clear - Hx. lia. }
(* the registers after the call *)
assert (RA3 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
  getr regs3 r = getr (ms_regs ms1) r).
{ intros r Hr. apply (w4_pres _ _ r HP3). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (R9_3 : getr regs3 9 = w64 mf)
  by (rewrite (RA3 9%bv ltac:(cbn; tauto)), (RK1 9%bv ltac:(cbn; tauto)); exact Rs1).
(* ---- run 2: 0x81c64 .. the call at 0x81c74 ---- *)
assert (V160_3 : val_mem SEGS (rd W3 mem3) (mf + 160) 8 vo).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 160) (mf + 160) 8 vo); [|exact V160].
  intros kk Hkk. rewrite K2;
  [apply K1; clear - Hkk Hmf0 Hsh C1; lia | unfold w4_zone; clear - Hkk Hmfb; lia | clear - Hkk Hmf0 G2; lia]. }
pose proof (w4_ent2 W3 regs3 mem3 mf vo R9_3 ltac:(clear - Hmf0; lia) ltac:(clear - Hmf0; lia)
  ltac:(clear - Hto; lia) V160_3) as HS.
remember (Eimg (Ereg regs3 [Z_to_bv 64 vo])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs3 r)
  by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs3 [Z_to_bv 64 vo]) E2)
  by (subst E2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32b : ew E2 32 = Z_to_bv 64 vo)
  by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U9b : bv_unsigned (ew E2 9) = mf)
  by (rewrite (EE2 9%nat 9%bv eq_refl), R9_3; apply unsigned_lit_small; clear - Hmf0 C1; lia).
clear HE2.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (BASE + 0x14f0)) mem3 (seg_rom SEGS))) in HJ3.
paj_run_shc RUNP RUNC HS HJ3.
{ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo w4_mf2]; lia | apply awr_ok_nil]. }
rename ms into ms4. rename HJ3 into HJ4. rename HS into HS4.
assert (RK4 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
  getr (ms_regs ms4) r = getr regs3 r).
{ refine (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W3) ms4) regs3 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] HS4 HAE2 _).
  vm_compute. reflexivity. }
prreg HS4 (1%bv : bv 5) Q1b. prreg HS4 (10%bv : bv 5) Q10b. prreg HS4 (11%bv : bv 5) Q11b.
prreg HS4 (12%bv : bv 5) Q12b. prreg HS4 (13%bv : bv 5) Q13b.
rewrite (EE2 18%nat 18%bv eq_refl), (RA3 18%bv ltac:(cbn; tauto)), Q18 in Q10b.
rewrite U9b in Q11b. rewrite E32b in Q12b.
(* run 2 writes nothing *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame E2 (ss_mem ss_w42) (w_H W3) mem3 (ms_mem ms4) (fun _ => False) HFr);
  [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr. unfold ss_w42, windows in Hin. cbn in Hin. destruct Hin as [Eq | []].
  injection Eq as <- <- <-. clear - Hr. lia. }
clear HF HFr HG.
assert (V208_4 : val_mem SEGS (rd W3 (ms_mem ms4)) (mf + M_n1) 8 2).
{ apply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms4) (mf + M_n1) (mf + M_n1) 8 2); [|exact Hv3].
  intros kk Hkk. apply K3. unfold M_n1. clear - Hkk Hmf0 C1. lia. }
assert (S86_4 : aview SEGS (w_H W3) (ms_mem ms4) (sh + 86) = Some 0).
{ rewrite K3 by (clear - Hsh C1; lia).
  rewrite K2; [exact (aview_of_val_mem1 SEGS _ _ _ _ W86 ltac:(clear; lia)) | unfold w4_zone; clear - Hsh; lia
  | clear - Hsh Hmf0 Hsfsh; lia]. }
(* ---- put_dec (w4, mf+208, t_out, 2) at 0x81c74 ---- *)
pmkst HS4.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W3 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ refine (w4_pd LAWS PSIG HPD HSTK HEV g pos mf W3 (ms_regs ms4) (ms_mem ms4) _ ly3 S3 _ 2 vo 5380 HPRE HJ4
    Hfrs3 Hk Hmfb Hmf32 Q1b _ eq_refl _ _ _ Q10b Q11b Q12b Q13b _ _ _ V208_4 _).
  - clear; lia.
  - rewrite (RK4 2%bv ltac:(cbn; tauto)), (RA3 2%bv ltac:(cbn; tauto)), (RK1 2%bv ltac:(cbn; tauto)). exact Rsp.
  - rewrite (RK4 3%bv ltac:(cbn; tauto)), (RA3 3%bv ltac:(cbn; tauto)), (RK1 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (RK4 4%bv ltac:(cbn; tauto)), (RA3 4%bv ltac:(cbn; tauto)), (RK1 4%bv ltac:(cbn; tauto)). exact Rtp.
  - exact Hto.
  - clear; lia.
  - rewrite (w4_dl vo Hto). unfold N_w4. lia.
  - apply w4_ra; [exact (mod32_mod8 _ Hf32)|]. change (SFa g pos) with SF. rewrite <- Esh. exact S86_4. }
intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfr5 & Hbl5 & HK5 & Hg5 & Hv5).
unfold put_dec.EV_PUT_DEC in HJ5. rewrite Z.add_0_r in HJ5.
rewrite Q1b.
rewrite (w4_dl vo Hto) in HK5, Hv5. change (2 + 2) with 4 in Hv5.
assert (Usp4 : spZ (ms_regs ms4) = mf).
{ unfold spZ. rewrite (RK4 2%bv ltac:(cbn; tauto)), (RA3 2%bv ltac:(cbn; tauto)), (RK1 2%bv ltac:(cbn; tauto)), Rsp.
  apply unsigned_lit_small. clear - Hmf0 C1. lia. }
rewrite Usp4 in HK5.
assert (Hfrs5 : frames S5 = [(4, pos)]) by (rewrite Hfr5; exact Hfrs3).
assert (Hbl5' : ablocks B ly5 S5 = ablocks B ly2 S2) by (rewrite Hbl5; exact Hbl3).
destruct (w4_geo LAWS HSTK g pos mf ly5 S5 W5 mem5 md5 _ HJ5 Hfrs5 (proj1 Hmfb)) as (EF5 & _).
change (SFa g pos) with SF in EF3, EF5.
assert (K4 : forall a, w4_zone mf sp0 SF sh a -> ~ (mf + 208 <= a < mf + 216 \/ SF + 690 <= a < SF + 692) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms4) a).
{ intros a Hz Hw. apply (w4_ckeep pos mf SF sh ly3 S3 W3 (ms_mem ms4) W5 mem5 _ HK5 ltac:(clear - Hmf0; lia)
    Hin43 EF3 eq_refl a).
  - unfold w4_zone in Hz. clear - Hz G6. lia.
  - unfold M_n1, V_w4. intros Hx. apply Hw. clear - Hx. lia. }
assert (BK4 : forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  ~ (mf + 208 <= b + i < mf + 216 \/ SF + 690 <= b + i < SF + 692) ->
  aview SEGS (w_H W5) mem5 (b + i) = aview SEGS (w_H W3) (ms_mem ms4) (b + i)).
{ intros b m i Hb Hi Hw. apply (proj1 (proj2 HK5) b m i); [rewrite Hbl3; exact Hb | exact Hi |].
  unfold M_n1, V_w4. intros Hx. apply Hw. clear - Hx. lia. }
assert (RA5 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
  getr regs5 r = getr (ms_regs ms4) r).
{ intros r Hr. apply (w4_pres _ _ r HP5). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (R9_5 : getr regs5 9 = w64 mf)
  by (rewrite (RA5 9%bv ltac:(cbn; tauto)), (RK4 9%bv ltac:(cbn; tauto)), (RA3 9%bv ltac:(cbn; tauto)),
      (RK1 9%bv ltac:(cbn; tauto)); exact Rs1).
assert (R18_5 : getr regs5 18 = w64 (SF + 688))
  by (rewrite (RA5 18%bv ltac:(cbn; tauto)), (RK4 18%bv ltac:(cbn; tauto)), (RA3 18%bv ltac:(cbn; tauto));
      exact Q18).
(* ---- run 3: 0x81c78 .. 0x81c98 ---- *)
assert (V168_5 : val_mem SEGS (rd W5 mem5) (mf + 168) 8 SHADOW_OFF).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W5) mem2 mem5 (mf + 168) (mf + 168) 8 SHADOW_OFF); [|exact V168].
  intros kk Hkk.
  rewrite K4; [| unfold w4_zone; clear - Hkk Hmfb; lia | clear - Hkk Hmf0 G2; lia].
  rewrite K3 by (clear - Hkk Hmf0 C1; lia).
  rewrite K2; [| unfold w4_zone; clear - Hkk Hmfb; lia | clear - Hkk Hmf0 G2; lia].
  apply K1; clear - Hkk Hmf0 Hsh C1; lia. }
assert (P692 : apresent (w_H W5) mem5 (SF + 688 + 4)).
{ apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly5 S5 W5 mem5 md5 _ (SF + 688 + 4) HJ5 ltac:(
    right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; rewrite EF5, HFB; clear; lia))). }
pose proof (w4_ent3 W5 regs5 mem5 mf (SF + 688) R9_5 R18_5 ltac:(clear - Hmf0; lia) ltac:(clear - Hmf0; lia)
  ltac:(clear - G1; lia) ltac:(clear - G2; lia) V168_5 Hv5 P692) as HS.
remember (Eimg (Ereg regs5 [Z_to_bv 64 SHADOW_OFF])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs5 r)
  by (intros n r Hn; subst E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs5 [Z_to_bv 64 SHADOW_OFF]) E3)
  by (subst E3; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32c : ew E3 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E18c : ew E3 18 = Z_to_bv 64 (SF + 688)) by (rewrite (EE3 18%nat 18%bv eq_refl); exact R18_5).
assert (U18c : bv_unsigned (ew E3 18) = SF + 688)
  by (rewrite E18c; apply unsigned_lit_small; clear - G1 G2 C1; lia).
clear HE3.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 (BASE + 0x1504)) mem5 (seg_rom SEGS))) in HJ5.
paj_run_to_sh RUNTOP HS HJ5 0x1524.
{ intros a (r & Hr & Ha). unfold ss_w43 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold w4_mf3, w4_nul3 in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [clear - Ha; lia|].
  rewrite U18c in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr; cbn [fst snd]. rewrite EF5, HFB. clear - Ha. lia. }
rename ms into ms5a. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
psrr_branch_pi RUNP BR HS.
{ rewrite (w4_br_not E3 18 (SF + 688) E18c ltac:(clear - G1 G2 C1; lia)) in Hc. discriminate Hc. }
clear Hc.
paj_run_to_sh RUNTOP HS HJ5 0x1524.
{ intros a (r & Hr & Ha). cbn [ss_mem add_cond In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [clear - Ha; lia|].
  rewrite U18c in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr; cbn [fst snd]. rewrite EF5, HFB. clear - Ha. lia. }
rename ms into ms6.
(* what run 3 stored and kept *)
assert (RK6 : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
  getr (ms_regs ms6) r = getr regs5 r).
{ refine (regs_kept_of_st_ok_pi E3 _ (restrict (w_H W5) ms6) regs5 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] HS HAE3 _).
  vm_compute. reflexivity. }
prreg HS (6%bv : bv 5) Q6. rewrite E32c in Q6.
assert (NUL6 : val_mem SEGS (rd W5 (ms_mem ms6)) (SF + 688 + 4) 1 0).
{ refine (w4_chunk_pi E3 _ (restrict (w_H W5) ms6) 1 _ 4 1 (SLit 0) (SF + 688) 0 HS eq_refl _ _ eq_refl _ _).
  - cbn [base_val YP09.r_base]. exact U18c.
  - cbn [YP09.r_chunks]. left. reflexivity.
  - clear; lia.
  - clear; lia. }
assert (K5 : forall a, 0 <= a < 2 ^ 64 -> a <> SF + 692 ->
  aview SEGS (w_H W5) (ms_mem ms6) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha Hw. transitivity (aview SEGS (w_H W5) (ms_mem ms5a) a).
  - apply (kept_of_frame E3 _ (w_H W5) (ms_mem ms5a) (ms_mem ms6) (fun x => x = SF + 692) HFr);
    [| exact Ha | exact Hw].
    intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    [clear - Hr; lia | rewrite U18c in Hr; clear - Hr; lia].
  - apply (kept_of_frame E3 (ss_mem ss_w43) (w_H W5) _ (ms_mem ms5a) (fun x => x = SF + 692) HFra);
    [| exact Ha | exact Hw].
    intros bb wlo whi aa Hin Hr. unfold ss_w43, windows in Hin. cbn in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    [clear - Hr; lia | rewrite U18c in Hr; clear - Hr; lia]. }
clear HF HFr HG HFa HFra HGa.
(* the whole piece, composed *)
assert (KALL : forall a, w4_zone mf sp0 SF sh a -> ~ w4_wr mf SF sh a ->
  aview SEGS (w_H W5) (ms_mem ms6) a = aview SEGS (w_H W2) mem2 a).
{ intros a Hz Hw. unfold w4_wr in Hw.
  assert (Ha : 0 <= a < 2 ^ 64) by (unfold w4_zone in Hz; clear - Hz Hmf0 Hsh G1 G2 G6 C1; lia).
  rewrite K5; [| exact Ha | clear - Hw; lia].
  rewrite K4; [| exact Hz | clear - Hw; lia].
  rewrite K3 by exact Ha.
  rewrite K2; [| exact Hz | clear - Hw; lia].
  apply K1; [exact Ha | clear - Hw; lia]. }
assert (BALL : forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  aview SEGS (w_H W5) (ms_mem ms6) (b + i) = aview SEGS (w_H W2) mem2 (b + i)).
{ intros b m i Hb Hi.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & Hb4096 & Hbce & Hbapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 4 pos HAR2 Hb Hin4) as Hd.
  rewrite EF, HFB in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hsha : ~ (sh <= b + i < sh + 128)).
  { intros Hx. apply (fshadow_not_app SF 128 b (req_size m) (b + i)); [exact G1 | clear - G2 C1; lia | exact Hbapp
    | rewrite Esh in Hx; unfold SHADOW_OFF in Hx; clear - Hx; lia | clear - Hi; lia]. }
  rewrite K5 by (clear - Hb4096 Hbce Hi Hd C1; lia).
  rewrite (BK4 b m i Hb Hi) by (clear - Hbce Hi Hd Hmf0; lia).
  rewrite K3 by (clear - Hb4096 Hbce Hi C1; lia).
  rewrite (BK2 b m i Hb Hi) by (clear - Hbce Hi Hd Hmf0; lia).
  apply K1; [clear - Hb4096 Hbce Hi C1; lia | clear - Hbce Hi Hmf0 Hsha; lia]. }
assert (S86F : aview SEGS (w_H W5) (ms_mem ms6) (sh + 86) = Some 0).
{ rewrite K5 by (clear - Hsh Hsfsh C1; lia).
  rewrite K4; [| unfold w4_zone; clear - Hsh; lia | clear - Hsh Hmf0 Hsfsh; lia].
  rewrite K3 by (clear - Hsh C1; lia).
  rewrite K2; [| unfold w4_zone; clear - Hsh; lia | clear - Hsh Hmf0 Hsfsh; lia].
  exact (aview_of_val_mem1 SEGS _ _ _ _ W86 ltac:(clear; lia)). }
assert (V200F : val_mem SEGS (rd W5 (ms_mem ms6)) (mf + M_n2) 8 0).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W5) (ms_mem ms1) (ms_mem ms6) (mf + 200) (mf + M_n2) 8 0); [|exact W200].
  intros kk Hkk. unfold M_n2.
  rewrite K5 by (clear - Hkk Hmf0 G2 C1; lia).
  rewrite K4; [| unfold w4_zone; clear - Hkk Hmfb; lia | clear - Hkk Hmf0 G2; lia].
  rewrite K3 by (clear - Hkk Hmf0 C1; lia).
  rewrite K2; [reflexivity | unfold w4_zone; clear - Hkk Hmfb; lia | clear - Hkk Hmf0 G2; lia]. }
rewrite Z.add_0_r in Hg3.
assert (BW4F : bytes_at8 W5 (ms_mem ms6) (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0])).
{ unfold bytes_at8, SlotModel.n_W4. rewrite !map_app.
  pose proof (SlotModel.DEC2_len (SlotModel.t_in (e_pl g)) Hti) as Li.
  pose proof (SlotModel.DEC2_len (SlotModel.t_out (e_pl g)) Hto) as Lo.
  apply w4_garr8_app; [apply w4_garr8_app|].
  - eapply (j_garr8_moved SEGS (w_H W3) (w_H W5) mem3 (ms_mem ms6)); [|exact Hg3].
    intros kk Hkk. rewrite length_map, Li in Hkk. change (SFa g pos) with SF. unfold V_w4.
    rewrite K5 by (clear - Hkk G1 G2 C1; lia).
    rewrite K4; [| unfold w4_zone; clear - Hkk; lia | clear - Hkk Hmf0 G2; lia].
    apply K3. clear - Hkk G1 G2 C1. lia.
  - rewrite length_map, Li. change (Z.of_nat 2) with 2.
    eapply (j_garr8_moved SEGS (w_H W5) (w_H W5) mem5 (ms_mem ms6)); [|exact Hg5].
    intros kk Hkk. rewrite length_map, Lo in Hkk. change (SFa g pos) with SF. unfold V_w4.
    apply K5; clear - Hkk G1 G2 C1; lia.
  - rewrite length_app, !length_map, Li, Lo. change (Z.of_nat (2 + 2)) with 4.
    change (SFa g pos) with SF. unfold V_w4.
    change (map (fun b : byte => bv_unsigned b) [RcIdentModel.zb 0]) with [bv_unsigned (RcIdentModel.zb 0)].
    replace (bv_unsigned (RcIdentModel.zb 0)) with 0 by reflexivity.
    apply w4_garr8_1; [exact NUL6 | clear; lia]. }
assert (RKF : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
  getr (ms_regs ms6) r = getr regs2 r).
{ intros r Hr.
  assert (Hr' : In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv])
    by (cbn [In] in Hr |- *; tauto).
  rewrite (RK6 r Hr'), (RA5 r Hr'), (RK4 r Hr'), (RA3 r Hr'). exact (RK1 r Hr). }
assert (R18F : getr (ms_regs ms6) 18 = w64 (SFa g pos + V_w4))
  by (rewrite (RK6 18%bv ltac:(cbn; tauto)); exact R18_5).
destruct (w4_meter MTL (e_S g) S2 S5 _ MLE MOK (HMT0 S2 S5)) as [MLE5 MOK5].
(* ---- the cut jc3 at +0x1524 ---- *)
apply SRr_ret.
pmkst HS.
exact (w4_mk_jc3 LAWS HSTK g pos mf nm tk dp st ly2 S2 W2 regs2 mem2 md2 ly5 S5 W5 (ms_regs ms6) (ms_mem ms6) _ _
  eq_refl HJ0 HJ5 Hfrs Hfrs5 Hbl5' Hk MLE5 MOK5 HC HK R25 R26 SZnm SZdp Vnm V136 Hstem RKF Q6 R18F KALL BALL S86F BW4F
  V200F).
Qed.
Check (j_w4 : j_w4_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS).
End c.
End b.
End a.
