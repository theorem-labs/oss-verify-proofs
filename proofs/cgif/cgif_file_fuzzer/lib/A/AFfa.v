(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFgw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (p cur nr lim h : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x3385c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 p cur nr lim h.
Local Notation XW := (AFgw.XW p cur nr lim h).
Local Notation E0 := (AFgw.E0 regs0 p cur nr lim h).
Local Notation Er := (AFgw.Er regs0 p cur nr lim h).
Local Notation E2 := (AFgw.E2 regs0 p cur nr lim h).
Local Notation E1 := (AFgw.E1 regs0 p cur nr lim h).
Local Notation EqP := (AFgw.EqP regs0 p cur nr lim h).
Local Notation EqCUR := (AFgw.EqCUR regs0 p cur nr lim h).
Local Notation EqNR := (AFgw.EqNR regs0 p cur nr lim h).
Local Notation EqLIM := (AFgw.EqLIM regs0 p cur nr lim h).
Local Notation EqH := (AFgw.EqH regs0 p cur nr lim h).
Local Notation R_CUR := AFgw.R_CUR.
Local Notation REG0 := AFgw.REG0.
Local Notation FFL := AFgw.FFL.
Local Notation SR0 := AFgw.SR0.
Local Notation SS0 := AFgw.SS0.
Local Notation WIN := AFgw.WIN.
Local Notation win_sub := AFgw.win_sub.
Local Notation win_sub_sound := (AFgw.win_sub_sound ly regs0).
Local Notation WSK0 := AFgw.WSK0.
Local Notation sk_ok := AFgw.sk_ok.
Local Notation WSK0_ok := (AFgw.WSK0_ok regs0 p cur nr lim h).
Local Notation windows_WIN := (AFgw.windows_WIN ly regs0).
Local Notation MEQ := (AFgw.MEQ mem0).
Local Notation MEQ_frame := (AFgw.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFgw.MEQ_0 mem0).
Local Notation SREGS := AFgw.SREGS.
Local Notation at_L := (AFgw.at_L W regs0 mem0 md0 p cur nr lim h).
Local Notation at_XG := (AFgw.at_XG W regs0 mem0 md0 p cur nr lim h).
Local Notation postL := (AFgw.postL W regs0 mem0 md0 p cur nr lim h).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hregs Hp Hcur Hnr Hh Hcell SEED].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac zdec Hbr := zbranch Hbr; unfold zcanon, M64 in Hbr;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hbr;
first [apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr | apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.leb_le in Hbr | apply Z.leb_gt in Hbr]; lia.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Lemma segGL : SRr tfibsegs W cfg0 postL.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hregs as (R11 & R12 & R13 & R14). destruct Hp as [P1 P2]. destruct Hcur as (C1 & C2 & C3 & C4 & C5). destruct Hh as [G1 G2].
evalS HS.
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = p) by (unfold rho_of; rewrite EqP; unfold w64; apply unsigned_lit_small; clear - P1; numconst; lia).
assert (R33 : rho_of E0 33%nat = cur) by (unfold rho_of; rewrite EqCUR; unfold w64; apply unsigned_lit_small; clear - C1 C2 C3; numconst; lia).
assert (R34 : rho_of E0 34%nat = nr) by (unfold rho_of; rewrite EqNR; unfold w64; apply unsigned_lit_small; clear - Hnr P1; numconst; lia).
assert (R35 : rho_of E0 35%nat = lim) by (unfold rho_of; rewrite EqLIM; unfold w64; apply unsigned_lit_small; clear - C1 C2 C3; numconst; lia).
assert (R36 : rho_of E0 36%nat = h) by (unfold rho_of; rewrite EqH; unfold w64; apply unsigned_lit_small; clear - G1; numconst; lia).
assert (UP : bv_unsigned (w64 p) = p) by (unfold w64; apply unsigned_lit_small; clear - P1; numconst; lia).
Ltac sregs HS :=
intros r Hr; cbn [AFgw.SREGS In] in Hr;
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with
| R11 : getr regs0 11 = _, R14 : getr regs0 14 = _ |- getr _ ?r = getr regs0 ?r =>
first [ let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_atom HS r k
| let Q := fresh "Q" in rreg HS r Q; rewrite Q; symmetry; first [exact R11 | exact R14 | rewrite R11; reflexivity | rewrite R14; reflexivity] ]
end.
Ltac finish HS HLT NRE :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [exact HLT|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end;
split; [sregs HS|];
split; [let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqCUR; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia|];
split; [let Q := fresh "Q" in rreg HS (13%bv : bv 5) Q; rewrite Q; rewrite NRE; first [exact EqH | exact EqNR | cbn [sv_denot]; rewrite ?EqH, ?EqNR; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity] |];
assumption.
Ltac loop_test HS NRE SK0 :=
srr_run_sh tfibtbl_rtG_ok HS; meq_acc SK0;
srr_branch_sh tfibtbl_rtG_ok HS;
[
assert (HEQ : cur + 8 = lim) by (lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => zdec Hbr end);
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end; uncond HS;
srr_run_to_sh tfibtbl_rtG_ok HS 0x33888; meq_acc SK0;
unfold AFgw.postL; replace (cur + 8 <? lim) with false by (symmetry; apply Z.ltb_ge; lia);
finish HS HEQ NRE
| assert (HLT : cur + 8 < lim) by (lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => zdec Hbr end);
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end; uncond HS;
srr_run_to_sh tfibtbl_rtG_ok HS 0x3385c; meq_acc SK0;
unfold AFgw.postL; replace (cur + 8 <? lim) with true by (symmetry; apply Z.ltb_lt; lia);
finish HS HLT NRE ].
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
destruct (Z_lt_dec p h) as [HGT|HLE].
-
assert (NRE : nr_step p nr h = nr) by (unfold nr_step; replace (h <=? p) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HGT; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R36 P1 G1 HGT; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
loop_test HS NRE SK0.
- destruct (Z_lt_dec nr h) as [HNEW|HOLD].
+
assert (NRE : nr_step p nr h = h) by (unfold nr_step; replace (h <=? p) with true by (symmetry; apply Z.leb_le; lia); replace (nr <? h) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
srr_branch_sh tfibtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HLE HNEW; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R36 P1 G1 HLE; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
loop_test HS NRE SK0.
+
assert (NRE : nr_step p nr h = nr) by (unfold nr_step; replace (nr <? h) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r; reflexivity).
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HLE HOLD; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R36 P1 G1 HLE; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
loop_test HS NRE SK0.
Qed.
End WK.
End a.
