(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YFfbM.v (commit 67deba317dfb, blob 3aabf856aa41) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 4 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFhl AFgw AFfa.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFfb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09R YA0pM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecMatA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFIB_IMG_END in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.

Ltac numconstA := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.

Lemma mat_win_mono : forall (Z1 Z2 : Z -> Prop) (m0 m : list word),
(forall a, Z1 a -> Z2 a) -> DMrcSecMatA.mat_win Z1 m0 m -> DMrcSecMatA.mat_win Z2 m0 m.
Proof. intros Z1 Z2 m0 m HZ HW q Hq. destruct (HW q Hq) as [H|(a & Ha & ->)]; [left; exact H | right; exists a; split; [exact (HZ a Ha) | reflexivity]]. Qed.
Lemma mat_win_trans : forall (Zn : Z -> Prop) (m0 m1 m2 : list word),
DMrcSecMatA.mat_win Zn m0 m1 -> DMrcSecMatA.mat_win Zn m1 m2 -> DMrcSecMatA.mat_win Zn m0 m2.
Proof. intros Zn m0 m1 m2 H1 H2 q Hq. destruct (H2 q Hq) as [H|H]; [exact (H1 q H) | right; exact H]. Qed.
Lemma mat_win_refl : forall (Zn : Z -> Prop) (m : list word), DMrcSecMatA.mat_win Zn m m.
Proof. intros Zn m q Hq. left. exact Hq. Qed.

Lemma acc_run : forall (Zn : Z -> Prop) (E : env) (rs : smem) (md : Model) (matS mat' : list word),
(forall a, in_rrange E rs a -> Zn a) ->
DMrcSecMatA.mat_win Zn matS (m_vm_materialized md) ->
mat_in_win E rs md (with_vm_backing (m_vm_lazy md) mat' md) ->
DMrcSecMatA.mat_win Zn matS mat'.
Proof.
intros Zn E rs md matS mat' HZ HA HW q Hq.
destruct (HW q Hq) as [H|(a & Ha & ->)]; [exact (HA q H) | right; exists a; split; [exact (HZ a Ha) | reflexivity]].
Qed.

Lemma rr_cell : forall (E : env) (rs : smem) (a v : Z), base_val E (Some 33%nat) = v ->
forallb (fun r => match YP09.r_base r with Some k => Nat.eqb k 33 | None => false end && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8)) rs = true ->
in_rrange E rs a -> v <= a < v + 8.
Proof.
intros E rs a v Hv Hb (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Hc. cbn beta in Hc.
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct (YP09.r_base r) as [k|] eqn:Eb; [|discriminate]. apply Nat.eqb_eq in H1. subst k. subst v. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (p cur nr lim h : Z).
Variable mat0 : list word.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34b00) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 p cur nr lim h.
Local Notation E0 := (AFgw.E0 regs0 p cur nr lim h).
Local Notation Er := (AFgw.Er regs0 p cur nr lim h).
Local Notation EqP := (AFgw.EqP regs0 p cur nr lim h).
Local Notation EqCUR := (AFgw.EqCUR regs0 p cur nr lim h).
Local Notation EqNR := (AFgw.EqNR regs0 p cur nr lim h).
Local Notation EqLIM := (AFgw.EqLIM regs0 p cur nr lim h).
Local Notation EqH := (AFgw.EqH regs0 p cur nr lim h).
Local Notation WSK0 := AFgw.WSK0.
Local Notation WSK0_ok := (AFgw.WSK0_ok regs0 p cur nr lim h).
Local Notation MEQ := (AFgw.MEQ mem0).
Local Notation MEQ_frame := (AFgw.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFgw.MEQ_0 mem0).
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
numconstA; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac zdec Hbr := zbranch Hbr; unfold zcanon, M64 in Hbr;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hbr;
first [apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr | apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.leb_le in Hbr | apply Z.leb_gt in Hbr]; lia.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].

Ltac macc R33 :=
lazymatch goal with
| HW : mat_in_win ?E ?rs ?md _, ACC : DMrcSecMatA.mat_win _ _ _ |- _ =>
let HZ := fresh "HZ" in let A2 := fresh "ACC" in
assert (HZ : forall a, in_rrange E rs a -> cur <= a < cur + 8)
by (intros ?a ?Ha; exact (rr_cell E rs _ cur R33 ltac:(vm_compute; reflexivity) Ha));
pose proof (acc_run (fun a => cur <= a < cur + 8) E rs md _ _ HZ ACC HW) as A2;
clear HZ HW ACC; rename A2 into ACC; srr_norm_model
end.
Lemma segGL_M : SRr tfibsegs W cfg0
(fun W' c' => postL W' c' /\ DMrcSecMatA.mat_win (fun a => cur <= a < cur + 8) mat0 (m_vm_materialized (cfg_model c'))).
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hregs as (R11 & R12 & R13 & R14). destruct Hp as [P1 P2]. destruct Hcur as (C1 & C2 & C3 & C4 & C5). destruct Hh as [G1 G2].
evalS HS.
pose proof MEQ_0 as MQ.
pose proof (mat_win_refl (fun a => cur <= a < cur + 8) mat0) as ACC.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = p) by (unfold rho_of; rewrite EqP; unfold w64; apply unsigned_lit_small; clear - P1; numconstA; lia).
assert (R33 : rho_of E0 33%nat = cur) by (unfold rho_of; rewrite EqCUR; unfold w64; apply unsigned_lit_small; clear - C1 C2 C3; numconstA; lia).
assert (R34 : rho_of E0 34%nat = nr) by (unfold rho_of; rewrite EqNR; unfold w64; apply unsigned_lit_small; clear - Hnr P1; numconstA; lia).
assert (R35 : rho_of E0 35%nat = lim) by (unfold rho_of; rewrite EqLIM; unfold w64; apply unsigned_lit_small; clear - C1 C2 C3; numconstA; lia).
assert (R36 : rho_of E0 36%nat = h) by (unfold rho_of; rewrite EqH; unfold w64; apply unsigned_lit_small; clear - G1; numconstA; lia).
assert (UP : bv_unsigned (w64 p) = p) by (unfold w64; apply unsigned_lit_small; clear - P1; numconstA; lia).
Ltac sregsM HS :=
intros r Hr; cbn [AFgw.SREGS In] in Hr;
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with
| R11 : getr regs0 11 = _, R14 : getr regs0 14 = _ |- getr _ ?r = getr regs0 ?r =>
first [ let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_atom HS r k
| let Q := fresh "Q" in rreg HS r Q; rewrite Q; symmetry; first [exact R11 | exact R14 | rewrite R11; reflexivity | rewrite R14; reflexivity] ]
end.
Ltac finishM HS HLT NRE :=
lazymatch goal with ACC : DMrcSecMatA.mat_win _ _ _ |- _ =>
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [| exact ACC]; split; [reflexivity|]; split; [exact HLT|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end end;
split; [sregsM HS|];
split; [let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqCUR; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia|];
split; [let Q := fresh "Q" in rreg HS (13%bv : bv 5) Q; rewrite Q; rewrite NRE; first [exact EqH | exact EqNR | cbn [sv_denot]; rewrite ?EqH, ?EqNR; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity] |];
assumption.
Ltac loop_testM HS NRE SK0 R33 :=
srr_run_shM tfibtbl_rtG_ok HS; meq_acc SK0; macc R33;
srr_branch_sh tfibtbl_rtG_ok HS;
[
assert (HEQ : cur + 8 = lim) by (lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => zdec Hbr end);
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end; uncond HS;
srr_run_to_shM tfibtbl_rtG_ok HS 0x34b2c; meq_acc SK0; macc R33;
unfold AFgw.postL; replace (cur + 8 <? lim) with false by (symmetry; apply Z.ltb_ge; lia);
finishM HS HEQ NRE
| assert (HLT : cur + 8 < lim) by (lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => zdec Hbr end);
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end; uncond HS;
srr_run_to_shM tfibtbl_rtG_ok HS 0x34b00; meq_acc SK0; macc R33;
unfold AFgw.postL; replace (cur + 8 <? lim) with true by (symmetry; apply Z.ltb_lt; lia);
finishM HS HLT NRE ].
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. macc R33.
destruct (Z_lt_dec p h) as [HGT|HLE].
-
assert (NRE : nr_step p nr h = nr) by (unfold nr_step; replace (h <=? p) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HGT; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. macc R33.
srr_branch_sh tfibtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R36 P1 G1 HGT; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
loop_testM HS NRE SK0 R33.
- destruct (Z_lt_dec nr h) as [HNEW|HOLD].
+
assert (NRE : nr_step p nr h = h) by (unfold nr_step; replace (h <=? p) with true by (symmetry; apply Z.leb_le; lia); replace (nr <? h) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
srr_branch_sh tfibtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HLE HNEW; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. macc R33.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R36 P1 G1 HLE; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
loop_testM HS NRE SK0 R33.
+
assert (NRE : nr_step p nr h = nr) by (unfold nr_step; replace (nr <? h) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r; reflexivity).
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R34 R36 P1 Hnr G1 HLE HOLD; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. macc R33.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R36 P1 G1 HLE; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
loop_testM HS NRE SK0 R33.
Qed.
End WK.
End a.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout) (md : Model).
Variables (p lim : Z).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hp : 4096 <= p < ASAN_CEIL /\ p mod 16 = 0.
Hypothesis Hlim : lim <= ASAN_CEIL /\ lim mod 8 = 0.

Definition ZGL (cur a : Z) : Prop := cur <= a < lim.
Theorem gloop_M : forall hs cur nr regs mem mat, hs <> [] -> AFfb.stL W p lim cur nr hs regs mem ->
SRr tfibsegs W (mkCfg (mkst regs (w64 0x34b00) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => AFfb.at_XGf W md lim regs mem (AFfb.scan p nr hs) W' c' /\
DMrcSecMatA.mat_win (ZGL cur) mat (m_vm_materialized (cfg_model c'))).
Proof.
induction hs as [|h hs IH]; intros cur nr regs mem mat NE ST; [exfalso; exact (NE eq_refl)|].
pose proof (AFfb.seed_L W ly p lim LY IMG Hp Hlim cur nr h hs regs mem ST) as FH.
pose proof ST as (R11 & R12 & R13 & R14 & C1 & C2 & C3 & Hnr & CELLS). cbn [length] in C3.
assert (CL : cur + 8 <= lim) by lia.
eapply SRr_bind; [exact (segGL_M W ly regs mem md p cur nr lim h mat FH)|]. intros W' c' _ [POST MW].
pose proof (mat_win_mono (fun a => cur <= a < cur + 8) (ZGL cur) _ _ ltac:(intros a Ha; unfold ZGL; cbv beta in Ha; lia) MW) as MW1. clear MW. rename MW1 into MW.
unfold AFgw.postL in POST. destruct hs as [|h2 hs2].
-   cbn [length] in C3. replace (cur + 8 <? lim) with false in POST by (symmetry; apply Z.ltb_ge; lia).
destruct POST as (-> & _ & regs' & mem' & mat' & -> & SR & A12 & A13 & MQ). apply SRr_ret.
split; [| exact MW].
split; [reflexivity|]. exists regs', mem', mat'. splits; [reflexivity | exact SR | rewrite A12; f_equal; lia | rewrite A13; reflexivity | intros x; exact (MQ x ltac:(intros []))].
- replace (cur + 8 <? lim) with true in POST by (symmetry; apply Z.ltb_lt; cbn [length] in C3; lia).
destruct POST as (-> & _ & regs' & mem' & mat' & -> & SR & A12 & A13 & MQ).
assert (MQ' : forall x, mem' x = mem x) by (intros x; exact (MQ x ltac:(intros []))).
rewrite AFfb.scan_cons.
eapply SRr_mono; [apply (IH (cur + 8) (nr_step p nr h) regs' mem' mat' ltac:(discriminate))|].
+ destruct (CELLS 0%nat h eq_refl) as (_ & _ & G1 & _). unfold AFfb.stL.
pose proof (AFfb.nr_step_range p nr h Hnr ltac:(clear - G1; numconst; lia)) as NR'.
refine (conj _ (conj A12 (conj A13 (conj _ (conj _ (conj _ (conj _ (conj NR' _)))))))).
{ rewrite (SR 11%bv ltac:(cbn; tauto)). exact R11. }
{ rewrite (SR 14%bv ltac:(cbn; tauto)). exact R14. }
{ lia. }
{ clear - C2. replace (cur + 8) with (cur + 1 * 8) by lia. rewrite Z_mod_plus_full. exact C2. }
{ cbn [length] in *. lia. }
intros j h' Hj. destruct (CELLS (S j) h' Hj) as (V & PR & G1' & G2'). rewrite Nat2Z.inj_succ in V, PR.
replace (cur + 8 * Z.succ (Z.of_nat j)) with (cur + 8 + 8 * Z.of_nat j) in V, PR by lia.
splits; [| | exact (proj1 G1') | exact (proj2 G1') | exact G2'].
* eapply val_mem_frame; [| exact V]. intros x _. exact (MQ' _).
* intros a Ha. pose proof (PR a Ha) as X. unfold apresent in *. rewrite (MQ' _). exact X.
+ intros W'' c'' _ ((-> & regs'' & mem'' & mat'' & -> & SR' & B12 & B13 & MQ'') & MW2).
pose proof (mat_win_mono (ZGL (cur + 8)) (ZGL cur) _ _ ltac:(intros a Ha; unfold ZGL in *; lia) MW2) as MW3. clear MW2. rename MW3 into MW2.
split; [split; [reflexivity|] | exact (mat_win_trans _ _ _ _ MW MW2)]. exists regs'', mem'', mat''.
splits; [reflexivity | intros r Hr; rewrite (SR' r Hr); exact (SR r Hr) | exact B12 | exact B13 | intros x; rewrite (MQ'' x); exact (MQ' x)].
Qed.
End c.
End b.
