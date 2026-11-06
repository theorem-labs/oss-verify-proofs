(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 263 of its 317 lines of code are new or changed and 526 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel put_dec_c IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D3_hand_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma d3_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [p ->]. destruct Hb as [q ->]. exists (2 * p - q). ring.
Qed.
Lemma d3_m16 : forall a, a mod 32 = 0 -> a mod 16 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->]. exists (2 * p). ring.
Qed.
Lemma d3_m8 : forall a, a mod 32 = 0 -> (a + 208) mod 8 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->].
exists (4 * p + 26). ring.
Qed.
Lemma d3_dec_pos : forall v mn, 1 <= put_dec_c.dec_len v mn.
Proof.
intros v mn. unfold put_dec_c.dec_len, IdentSpec.DEC. rewrite length_app.
assert (H : (1 <= length (IdentSpec.dec_digits (S (Z.to_nat (Z.log2 v))) v))%nat).
{ cbn [IdentSpec.dec_digits]. rewrite length_app. cbn [length]. lia. }
lia.
Qed.
Lemma d3_zsh : forall (rdr : reader) lo len x n, zero_shadow rdr SHADOW_OFF lo len -> 0 <= lo ->
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

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation AJ g pos lyc Sc W mem md k := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k).

Lemma d3_geo : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
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

Lemma d3_obj : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k x n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf -> 0 < n ->
  d3_inobj B g pos lyc Sc x n ->
  (forall a, x <= a < x + n -> aview SEGS (w_H W) mem a <> None) /\
  4096 <= x /\ x + n <= alloc_ceiling /\ amem_range x n /\ shadow_hull_vis (aview SEGS (w_H W) mem) x n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k x n HJ Hfrs Hmf Hn Hobj.
destruct (d3_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf) as (EF & G1 & G2 & G3 & _).
pose proof (proj1 HJ) as HAR.
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
clear HJ.
destruct Hobj as [(Hx1 & Hx2) | (b & m & Hbm & Hb1 & Hb2)].
- destruct (al_frames _ _ LAWS lyc Sc W mem md 4 pos HAR Hin) as (_ & _ & Hfp & _).
  rewrite EF in Hfp. change (fs_frame_bytes 4) with 1024 in Hfp.
  split; [intros a Ha; apply aview_some_of_apresent; exact (proj1 (Hfp a ltac:(lia)))|].
  split; [lia|]. split; [lia|].
  split; [apply (amem_range_sub_app (SFa g pos) 1024 x n G3 G2); lia|].
  apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W mem md 4 pos x n HAR Hin);
    [rewrite EF; lia | rewrite EF; change (fs_frame_bytes 4) with 1024; lia | exact Hn].
- destruct (al_blocks _ _ LAWS lyc Sc W mem md b m HAR Hbm) as (_ & H4096 & Hceil & _ & Hbp & _).
  split; [intros a Ha; apply aview_some_of_apresent; exact (proj1 (Hbp a ltac:(lia)))|].
  split; [lia|]. split; [lia|].
  split; [eapply amem_range_of_block; eassumption|].
  eapply shadow_hull_vis_of_block; eassumption.
Qed.

Lemma d3_twr_fr : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k sp q n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf -> mf <= sp ->
  SFa g pos <= q -> q + n <= SFa g pos + 1024 ->
  twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem sp q n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k sp q n HJ Hfrs Hmf Hsp Hq1 Hq2 a Ha.
destruct (d3_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf) as (EF & G1 & G2 & G3 & G4 & _).
assert (Hw : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF.
  change (fs_frame_bytes 4) with 1024. lia. }
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
clear HJ.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. unfold ESTACK in *. lia.
Qed.

Lemma d3_stk : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) pos mf lyc Sc (W : world SEGS) mem md k q n,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf ->
  mf <= q -> 0 < n -> q + n + 96 <= e_sp0 g ->
  twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf q n /\
  tsrc_ok W mem mf q n.
Proof.
intros LAWS HSTK g pos mf lyc Sc W mem md k q n HJ Hfrs Hmf Hq Hn Hqn.
destruct (d3_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs Hmf)
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  ltac:(left; reflexivity)) as HZ.
cbn [fst snd] in HZ.
destruct (d3_zsh (aview SEGS (w_H W) mem) (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) q n HZ
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

Lemma d3_pd : d3_pd_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
unfold d3_pd_stmt.
intros LAWS PSIG HPD HSTK HEV g pos mf W regs mem md lyc Sc k n v mn retk HEP HJ Hfrs Hk Hmf Hmf32 R1 Hrk Hrk2
  R2 R3 R4 R10 R11 R12 R13 Rv Rmn Hn Hlen HVM HRA.
destruct (d3_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs (proj1 Hmf))
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof (d3_dec_pos v mn) as HD.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HPS : put_dec.PUT_DEC_STK = 4208) by reflexivity.
assert (Hsp : spZ regs = mf) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hsig : SIGMA IB_put_dec = BASE + AF_put_dec) by (apply PSIG; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
destruct HEP as (_ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
destruct (d3_stk LAWS HSTK g pos mf lyc Sc W mem md k (mf + M_n1) 8 HJ Hfrs (proj1 Hmf)
  ltac:(unfold M_n1; lia) ltac:(lia) ltac:(unfold M_n1; lia)) as [WP SP].
assert (WB : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf
  (SFa g pos + V_ev + n) (put_dec_c.dec_len v mn)).
{ apply (d3_twr_fr LAWS HSTK g pos mf lyc Sc W mem md k mf); [exact HJ | exact Hfrs | exact (proj1 Hmf) | lia | |];
  unfold V_ev, N_ev in *; lia. }
assert (SB : tsrc_ok W mem mf (SFa g pos + V_ev + n) (put_dec_c.dec_len v mn)).
{ split; [intros a Ha; split; [apply aview_some_of_apresent; exact (proj1 (proj2 (WB a Ha))) | unfold V_ev, N_ev in *; lia]|].
  split; [eapply range_addressable_sub; [exact HRA | unfold V_ev, N_ev in *; lia | unfold V_ev, N_ev in *; lia]|].
  split.
  { apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W mem md 4 pos _ _ (proj1 HJ)
      ltac:(rewrite Hfrs; left; reflexivity));
      [rewrite EF; unfold V_ev; lia | rewrite EF; change (fs_frame_bytes 4) with 1024; unfold V_ev, N_ev in *; lia | lia]. }
  split; [apply (amem_range_sub_app (SFa g pos) 1024 _ _ G3 G2); unfold V_ev, N_ev in *; lia|].
  unfold V_ev, N_ev in *; lia. }
rewrite Hsig.
refine (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k regs
  (SFa g pos + V_ev) (mf + M_n1) n v mn HJ _ _ R3 R4 R10 R11 _ _ R13 Rmn _ _ _ _ _ _ _ HVM _ _ _ _ _ _ _ _).
- rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hrk2].
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
- left. rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. lia.
- rewrite Hsp. exact Hmf32.
- rewrite Hsp, HPS. lia.
- rewrite Hsp. lia.
- rewrite Hfrs. cbn [length]. lia.
- unfold M_n1. exact (d3_m8 mf Hmf32).
- unfold V_ev. lia.
- exact Hn.
- rewrite Hsp. exact WP.
- rewrite Hsp. exact WB.
- rewrite Hsp. exact SP.
- rewrite Hsp. exact SB.
- right. unfold M_n1, V_ev, N_ev in *. lia.
- left. rewrite Hsp. unfold M_n1. lia.
- right. rewrite Hsp, HPS. unfold V_ev, N_ev in *. lia.
- unfold put_dec.EV_PUT_DEC. lia.
Qed.

Lemma d3_vs : d3_vs_stmt B LLVMF_STK.
Proof.
unfold d3_vs_stmt.
intros LAWS PSIG HVS HSTK g pos mf W regs mem md lyc Sc k ma mi pa retk HJ Hfrs Hmf Hmf32 R1 Hrk Hrk2 R2 R3 R4
  R10 R11 R12 R13 R14 Rma Rmi Rpa HRA.
destruct (d3_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs (proj1 Hmf))
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof asan_consts as (C1 & _). pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HVK : reac_identity_reac_ver_str.REAC_VER_STR_STK = 4224) by reflexivity.
assert (Hsp : spZ regs = mf) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hsig : SIGMA IB_reac_identity_reac_ver_str = BASE + AF_reac_identity_reac_ver_str)
  by (apply PSIG; reflexivity).
assert (WV : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyc Sc [(4, pos)] W mem mf (SFa g pos + V_v) 20).
{ apply (d3_twr_fr LAWS HSTK g pos mf lyc Sc W mem md k mf); [exact HJ | exact Hfrs | exact (proj1 Hmf) | lia | |];
  unfold V_v; lia. }
rewrite Hsig.
refine (HVS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k regs
  ma mi pa (SFa g pos + V_v) 20 HJ _ _ R3 R4 _ _ _ R10 R11 R12 R13 R14 Rma Rmi Rpa _ _ _ _).
- rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hrk2].
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- rewrite Hsp. exact (d3_m16 mf Hmf32).
- rewrite Hsp, HVK. lia.
- rewrite Hsp. lia.
- unfold V_v. lia.
- lia.
- intros _. split; [rewrite Hsp; exact WV|]. split.
  + right. exists 4, pos. split; [rewrite Hfrs; left; reflexivity|]. rewrite EF.
    change (fs_frame_bytes 4) with 1024. unfold V_v. lia.
  + unfold N_v in HRA. exact HRA.
- rewrite Hfrs. cbn [length]. lia.
Qed.

Lemma d3_bc : d3_bc_stmt B LLVMF_STK.
Proof.
unfold d3_bc_stmt.
intros LAWS ABCMP HSTK g pos mf W regs mem md lyc Sc k x y n retk HJ Hfrs Hmf Hmf32 R1 Hrk Hrk2 R2 R3 R4
  R10 R11 R12 Hn Ox Oy HRx HRy.
destruct (d3_geo LAWS HSTK g pos mf lyc Sc W mem md k HJ Hfrs (proj1 Hmf))
  as (EF & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
destruct (d3_obj LAWS HSTK g pos mf lyc Sc W mem md k x n HJ Hfrs (proj1 Hmf) ltac:(lia) Ox)
  as (Vx & X0 & X1 & Mx & Hx).
destruct (d3_obj LAWS HSTK g pos mf lyc Sc W mem md k y n HJ Hfrs (proj1 Hmf) ltac:(lia) Oy)
  as (Vy & Y0 & Y1 & My & Hy).
pose proof asan_consts as (C1 & _).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regs = e_sp0 g + (mf - e_sp0 g))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W regs mem
    LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc md k x y n (mf - e_sp0 g)
    (Z_to_bv 64 (BASE + retk)) HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - exact (d3_mod16 mf (e_sp0 g) Hmf32 G5).
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | exact Hrk2].
  - intros a Ha. split; [exact (Vx a Ha)|]. rewrite Hsp. lia.
  - intros a Ha. split; [exact (Vy a Ha)|]. rewrite Hsp. lia.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact Mx.
  - exact My.
  - exact HRx.
  - intros _. exact Hx.
  - exact HRy.
  - intros _. exact Hy. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|]. split; [exact Hcmp|].
split; [|exact Hpres].
intros a Ha Hw. apply Hfr; [exact Ha|]. clear - Hw. lia.
Qed.

Check (d3_pd : d3_pd_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS).
Check (d3_vs : d3_vs_stmt B LLVMF_STK).
Check (d3_bc : d3_bc_stmt B LLVMF_STK).
End c.
End b.
End a.
