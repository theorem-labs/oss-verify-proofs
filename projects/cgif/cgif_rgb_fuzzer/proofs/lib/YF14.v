(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF2r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (p cur nr lim h : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33e64 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 p cur nr lim h.
Local Notation XW := (YF2r.XW p cur nr lim h).
Local Notation E0 := (YF2r.E0 regs0 p cur nr lim h).
Local Notation Er := (YF2r.Er regs0 p cur nr lim h).
Local Notation E2 := (YF2r.E2 regs0 p cur nr lim h).
Local Notation E1 := (YF2r.E1 regs0 p cur nr lim h).
Local Notation EqP := (YF2r.EqP regs0 p cur nr lim h).
Local Notation EqCUR := (YF2r.EqCUR regs0 p cur nr lim h).
Local Notation EqNR := (YF2r.EqNR regs0 p cur nr lim h).
Local Notation EqLIM := (YF2r.EqLIM regs0 p cur nr lim h).
Local Notation EqH := (YF2r.EqH regs0 p cur nr lim h).
Local Notation R_CUR := YF2r.R_CUR.
Local Notation REG0 := YF2r.REG0.
Local Notation FFL := YF2r.FFL.
Local Notation SR0 := YF2r.SR0.
Local Notation SS0 := YF2r.SS0.
Local Notation WIN := YF2r.WIN.
Local Notation win_sub := YF2r.win_sub.
Local Notation win_sub_sound := (YF2r.win_sub_sound ly regs0).
Local Notation WSK0 := YF2r.WSK0.
Local Notation sk_ok := YF2r.sk_ok.
Local Notation WSK0_ok := (YF2r.WSK0_ok regs0 p cur nr lim h).
Local Notation windows_WIN := (YF2r.windows_WIN ly regs0).
Local Notation MEQ := (YF2r.MEQ mem0).
Local Notation MEQ_frame := (YF2r.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (YF2r.MEQ_0 mem0).
Local Notation SREGS := YF2r.SREGS.
Local Notation at_L := (YF2r.at_L W regs0 mem0 md0 p cur nr lim h).
Local Notation at_XG := (YF2r.at_XG W regs0 mem0 md0 p cur nr lim h).
Local Notation postL := (YF2r.postL W regs0 mem0 md0 p cur nr lim h).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hregs Hp Hcur Hnr Hh Hcell SEED].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by img_lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac zdec Hbr := zbranch Hbr; unfold zcanon, M64 in Hbr;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hbr;
first [apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr | apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.leb_le in Hbr | apply Z.leb_gt in Hbr]; img_lia.
Ltac uncond HS := unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Lemma segGL : SRr tfxsegs W cfg0 postL.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hregs as (R11 & R12 & R13 & R14). destruct Hp as [P1 P2]. destruct Hcur as (C1 & C2 & C3 & C4 & C5). destruct Hh as [G1 G2].
evalS HS.
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = p) by (img_try (unfold rho_of; rewrite EqP; unfold w64; img_apply unsigned_lit_small; clear - P1; numconst; img_lia)).
assert (R33 : rho_of E0 33%nat = cur) by (img_try (unfold rho_of; rewrite EqCUR; unfold w64; img_apply unsigned_lit_small; clear - C1 C2 C3; numconst; img_lia)).
assert (R34 : rho_of E0 34%nat = nr) by (img_try (unfold rho_of; rewrite EqNR; unfold w64; img_apply unsigned_lit_small; clear - Hnr P1; numconst; img_lia)).
assert (R35 : rho_of E0 35%nat = lim) by (img_try (unfold rho_of; rewrite EqLIM; unfold w64; img_apply unsigned_lit_small; clear - C1 C2 C3; numconst; img_lia)).
assert (R36 : rho_of E0 36%nat = h) by (img_try (unfold rho_of; rewrite EqH; unfold w64; img_apply unsigned_lit_small; clear - G1; numconst; img_lia)).
assert (UP : bv_unsigned (w64 p) = p) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - P1; numconst; img_lia)).
Ltac sregs HS :=
intros r Hr; cbn [YF2r.SREGS In] in Hr;
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with
| R11 : getr regs0 11 = _, R14 : getr regs0 14 = _ |- getr _ ?r = getr regs0 ?r =>
first [ let k := img_ev (Z.to_nat (bv_unsigned r)) in reg_atom HS r k
| let Q := fresh "Q" in rreg HS r Q; rewrite Q; symmetry; first [img_exact R11 | img_exact R14 | rewrite R11; img_refl | rewrite R14; img_refl] ]
end.
Ltac finish HS HLT NRE :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|]; split; [img_try (img_exact HLT)|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [img_try (rewrite HshR at 1; img_refl)|] end;
split; [img_try (sregs HS)|];
split; [img_try (let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqCUR; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia)|];
split; [img_try (let Q := fresh "Q" in rreg HS (13%bv : bv 5) Q; rewrite Q; rewrite NRE; first [img_exact EqH | img_exact EqNR | cbn [sv_denot]; rewrite ?EqH, ?EqNR; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl]) |];
assumption.
Ltac loop_test HS NRE SK0 :=
srr_run_sh tfxtbl_rtG_ok HS; meq_acc SK0;
srr_branch_sh tfxtbl_rtG_ok HS;
[
assert (HEQ : cur + 8 = lim) by (img_try (lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => zdec Hbr end));
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end; uncond HS;
srr_run_to_sh tfxtbl_rtG_ok HS (0x33e90 + D_150); meq_acc SK0;
unfold YF2r.postL; replace (cur + 8 <? lim) with false by (img_try (symmetry; img_apply Z.ltb_ge; img_lia));
finish HS HEQ NRE
| assert (HLT : cur + 8 < lim) by (img_try (lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => zdec Hbr end));
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end; uncond HS;
srr_run_to_sh tfxtbl_rtG_ok HS (0x33e64 + D_150); meq_acc SK0;
unfold YF2r.postL; replace (cur + 8 <? lim) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia));
finish HS HLT NRE ].
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
destruct (Z_lt_dec p h) as [HGT|HLE].
-
assert (NRE : nr_step p nr h = nr) by (img_try (unfold nr_step; replace (h <=? p) with false by (symmetry; img_apply Z.leb_gt; img_lia); img_refl)).
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HGT; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R36 P1 G1 HGT; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
loop_test HS NRE SK0.
- destruct (Z_lt_dec nr h) as [HNEW|HOLD].
+
assert (NRE : nr_step p nr h = h) by (img_try (unfold nr_step; replace (h <=? p) with true by (symmetry; img_apply Z.leb_le; img_lia); replace (nr <? h) with true by (symmetry; img_apply Z.ltb_lt; img_lia); img_refl)).
srr_branch_sh tfxtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HLE HNEW; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R36 P1 G1 HLE; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
loop_test HS NRE SK0.
+
assert (NRE : nr_step p nr h = nr) by (img_try (unfold nr_step; replace (nr <? h) with false by (symmetry; img_apply Z.ltb_ge; img_lia); rewrite Bool.andb_false_r; img_refl)).
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HLE HOLD; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R36 P1 G1 HLE; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
loop_test HS NRE SK0.
Qed.
End WK.
End a.
