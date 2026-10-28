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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFex AFfu AFf2 AFfq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFgp AFh3 AFf1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_wvb : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre B ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = false.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Local Notation QSZv := (AFgq.QSZv q).
Local Notation QBv := (AFgq.QBv q).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 ENQ)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & _ & Hk & _). exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hst & _). exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & Hnq & _). exact Hnq. Qed.
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma HQL : qloose X. Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL). exact (qloosem_loose _ QL). Qed.
Lemma IMG : img_cover ly.
Proof. destruct ENQ as ((_ & LED & _) & _). exact (img_cover_of_ledger ly X md LED). Qed.
Lemma ZT : zone3 T kThreadObjSize.
Proof.
pose proof (Forall_nth_f _ _ 2 _ (lo_app ly LO) eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
exact (zone3_intro ly T kThreadObjSize IMG ltac:(clear; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LO) eq_refl eq_refl)).
Qed.
Definition lb : batch := match rev (qc_list q) with b :: _ => b | [] => mkBatch 0 [] end.
Definition initr : list batch := match rev (qc_list q) with _ :: t => t | [] => [] end.
Lemma Hrev : rev (qc_list q) = lb :: initr.
Proof. unfold lb, initr. unfold need_new_batch in HNB. destruct (rev (qc_list q)); [discriminate | reflexivity]. Qed.
Lemma E0 : qc_list q = rev initr ++ [lb]. Proof. rewrite <- (rev_involutive (qc_list q)), Hrev. reflexivity. Qed.
Lemma lb_in : In lb (all_batches X).
Proof. unfold all_batches. apply in_app_iff. left. rewrite E0. apply in_app_iff. right. left. reflexivity. Qed.
Definition QLv : Z := SB + b_self lb.
Definition CNTv : Z := Z.of_nat (length (b_items lb)).
Definition BSZv : Z := b_bytes lb.
Local Notation SLv := (AFgp.SLv QLv CNTv).
Lemma Hroom : CNTv < kBatchSlots.
Proof.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) lb lb_in) as [L1 L2].
unfold need_new_batch in HNB. rewrite Hrev in HNB. apply Z.eqb_neq in HNB. unfold CNTv, kBatchSlots in *. lia.
Qed.
Lemma last_geom : ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\ kHighMemBeg <= QLv /\ QLv + kBatchBytes <= ASAN_CEIL.
Proof.
destruct (AFf2.batch_geom B ly X rd0 M [] sp0 HSP lb lb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (lo_high ly LO) as [P1 P2].
unfold QLv. rewrite Eb. unfold region_base in *. rewrite region_off_eq in * by (unfold kBatchClass; lia). ceil; unfold kBatchClass, kBatchBytes, kSpaceSize, kPrimResvSize, kHighMemBeg, ASAN_CEIL in *.
splits; lia.
Qed.
Lemma last_cells : val_mem tfibsegs m0 (QLv + 8) 8 BSZv /\ val_mem tfibsegs m0 (QLv + 16) 8 CNTv.
Proof.
assert (IN : forall c, In c (batch_cells (qc_list q)) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. left. unfold qc_cells. do 4 right. exact Hc. }
assert (OWN : forall c, In c (batch_own_cells lb (ANum 0)) -> In c (batch_cells (qc_list q))).
{ intros c Hc. apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|].
rewrite next_exp_app_new. exact Hc. }
unfold BSZv, CNTv, QLv. split.
- replace (SB + b_self lb + 8) with (aeval B ly (aoff (batch_exp lb) 8)) by (cbn; lia).
apply (AFfq.cell_stateZ B ly X W mem M _ _ 8 _ (IN _ (OWN _ ltac:(unfold batch_own_cells; right; left; reflexivity))) eq_refl).
- replace (SB + b_self lb + 16) with (aeval B ly (aoff (batch_exp lb) 16)) by (cbn; lia).
apply (AFfq.cell_stateZ B ly X W mem M _ _ 8 _ (IN _ (OWN _ ltac:(unfold batch_own_cells; right; right; left; reflexivity))) eq_refl).
Qed.
Lemma bsz_range : kBatchBytes <= BSZv /\ BSZv <= QBv.
Proof.
unfold BSZv, AFgq.QBv. split; [exact (AFfq.b_bytes_ge B ly X W mem M lb lb_in)|].
rewrite (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)), E0, sum_bytes_app. cbn [sum_bytes fold_right].
pose proof (AFfq.sum_bytes_ge B ly X W mem M (rev initr) ltac:(intros b Hb; unfold all_batches; apply in_app_iff; left; rewrite E0; apply in_app_iff; left; exact Hb)). lia.
Qed.
Lemma slot_present : forall a, SLv + 24 <= a < SLv + 32 -> apresent H0 mem a.
Proof.
intros a Ha. pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof Hroom as HR. unfold AFgp.SLv in Ha.
assert (JI : In (aoff (batch_exp lb) (24 + 8 * CNTv), kBatchBytes - 24 - 8 * CNTv) (ajunk B ly X)).
{ unfold ajunk. do 2 right. rewrite !in_app_iff. do 4 right. left. unfold quar_junk. apply in_flat_map. exists lb. split; [exact lb_in|]. unfold batch_junk, CNTv. left. reflexivity. }
pose proof (AFfq.vis_range B ly X W mem M _ _ (a - (SLv + 24)) (or_introl JI)) as V. cbn [aeval aoff batch_exp] in V.
specialize (V ltac:(unfold AFgp.SLv, CNTv, kBatchBytes, kBatchSlots in *; lia)).
replace (SB + (b_self lb + (24 + 8 * CNTv)) + (a - (SLv + 24))) with a in V by (unfold AFgp.SLv, QLv; lia).
apply AFfu.vis_apresent; [| exact V]. ceil; unfold AFgp.SLv, QLv, CNTv, kBatchBytes, kBatchSlots, kHighMemBeg, ASAN_CEIL, TFIB_IMG_END in *. lia.
Qed.
Local Notation E0' := (AFgp.E0 ly regs u nn QSZv QLv QBv CNTv BSZv).
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac nums := ceil; unfold AFgp.SLv, CNTv, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, QSTACK, TFIB_IMG_END, t_qc in *.
Lemma chunk_atom8 : forall (E : env) m base a k0 x, ew E k0 = w64 x -> 0 <= x < 2 ^ 64 -> val_mem tfibsegs m (base + a) 8 x ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk a (CVal 8 (SOff k0 0))).
Proof.
intros E m base a k0 x Hk0 Hx Hm. eapply chunk_ok_val; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hx | cbn; lia | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Theorem FH_ok : AFgp.free_hyps W ly regs mem u nn QSZv QLv QBv CNTv BSZv.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES. rewrite (ts_tp _ TB) in Htp.
pose proof (AFfq.u_facts B ly X W mem k M Hk) as (U1 & U2 & U3 & U4). pose proof (AFfq.u_zone B ly X W mem k M IMG Hk) as UZ.
pose proof (AFfq.q_facts B ly X W mem sp0 k M HSP Hk HQL) as (Qa & Qb & Qc & Qd).
pose proof (AFfq.root_vals B ly X W mem M) as (V1 & V2 & V3 & V4).
pose proof (AFfq.GEO B ly X W mem M) as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & _).
pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof last_cells as [C8 C16]. pose proof bsz_range as [B1 B2]. pose proof Hroom as HR. pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (lo_high ly LO) as H. pose proof ZT as H1. unfold in_high in H. unfold zone3 in H1. cbn [fst snd] in H.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QSZ1 : 1 <= QSZv) by (unfold AFgq.QSZv; rewrite E0, length_app; cbn [length]; lia).
assert (C0 : 0 <= CNTv) by (unfold CNTv; lia).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
constructor.
- exact LO.
- exact Htp.
- exact Hra.
- exact Hra4.
- split; [exact Hlo | exact Hhi].
- exact Hal.
- exact HPRES.
- split; [exact UZ | exact U3].
- exact IMG.
- exact U4.
- nums. splits; lia.
- splits; [exact L1 | exact L2 | exact L3 | exact C0 | exact HR | nums; lia | nums; lia | |].
+ intros a Ha. destruct (Z_lt_le_dec a (QLv + 16)).
* replace a with (QLv + 8 + (a - (QLv + 8))) by lia. apply (AFfq.val_mem_present W mem _ 8 _ _ C8); [lia | apply off_img_high; nums; lia].
* replace a with (QLv + 16 + (a - (QLv + 16))) by lia. apply (AFfq.val_mem_present W mem _ 8 _ _ C16); [lia | apply off_img_high; nums; lia].
+ exact slot_present.
-
rewrite restrict_mkst_fx. unfold AFgp.SS0, AFgp.SR0, sr_set. cbn [bv_eqb]. unfold AFgp.E0, w64. apply (entry_st_ok_full tfibsegs).
+ repeat (apply regs_ok_pin; [| intros XX; discriminate |]); [apply regs_ok_Ereg | ..]; cbn [sv_denot].
* exact Htp.
* change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 32) with (Z_to_bv 64 T). rewrite Ha0. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
* change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 32) with (Z_to_bv 64 T). rewrite Ha1. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
* change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 34) with (Z_to_bv 64 u). rewrite Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. reflexivity.
* change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 35) with (Z_to_bv 64 nn). rewrite Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. set (E := Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)).
assert (BV2 : bv_unsigned (ew E 2) = sp0) by (rewrite (AFgp.E2 ly regs u nn QSZv QLv QBv CNTv BSZv : ew E 2 = getr regs 2); reflexivity).
assert (BV32 : bv_unsigned (ew E 32) = T) by (change (ew E 32) with (w64 T); unfold w64; apply unsigned_lit_small; clear - H1; nums; lia).
assert (BV38 : bv_unsigned (ew E 38) = QLv) by (change (ew E 38) with (w64 QLv); unfold w64; apply unsigned_lit_small; clear - L4 L5; nums; lia).
assert (BV47 : bv_unsigned (ew E 47) = SLv) by (change (ew E 47) with (w64 SLv); unfold w64; apply unsigned_lit_small; clear - L4 L5 C0 HR; nums; lia).
unfold AFgp.REG0, AFgp.R_ROOT, AFgp.R_LAST, AFgp.R_SLOT.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E m0 2 sp0 (- 64)); [exact BV2 | nums; lia | lia |].
intros a Ha. apply apresent_writable; [nums; lia | apply HPRES; clear -Ha; nums; lia]. }
apply Forall_cons.
{   reg_intro. rewrite BV32. unfold t_qc in *.
split; [nums; lia|]. split; [nums; lia|]. split.
{ intros o Ho. apply (AFfq.val_mem_writable W mem _ _ _ _ V4); [cbn; lia | apply (zone3_off_img _ _ _ ZT); nums; lia]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom8 E _ _ _ 36%nat QSZv); [reflexivity | lia | exact V1].
- apply (chunk_atom8 E _ _ _ 38%nat QLv); [reflexivity | nums; lia |].
replace QLv with (AFgq.QLv ly q) by (unfold AFgq.QLv, QLv; rewrite Hrev; reflexivity). eapply val_mem_addr; [exact V3 | lia].
- apply (chunk_atom8 E _ _ _ 39%nat QBv); [reflexivity | nums; lia | eapply val_mem_addr; [exact V4 | lia]]. }
apply Forall_cons.
{   reg_intro. rewrite BV38.
split; [nums; lia|]. split; [nums; lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 16).
- apply (AFfq.val_mem_writable W mem _ _ _ _ C8); [cbn; lia | apply off_img_high; nums; lia].
- apply (AFfq.val_mem_writable W mem _ _ _ _ C16); [cbn; lia | apply off_img_high; nums; lia]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom8 E _ _ _ 46%nat BSZv); [reflexivity | nums; lia | exact C8].
- apply (chunk_atom8 E _ _ _ 45%nat CNTv); [reflexivity | nums; lia | exact C16]. }
apply Forall_cons; [|apply Forall_nil].
{   reg_intro. rewrite BV47.
split; [nums; lia|]. split; [nums; lia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable; [nums; lia|]. apply slot_present. lia. }
+ apply pairwise_disjoint_of_extents. unfold AFgp.REG0, AFgp.R_ROOT, AFgp.R_LAST, AFgp.R_SLOT, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (AFgp.E2 ly regs u nn QSZv QLv QBv CNTv BSZv : ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 2 = getr regs 2). fold sp0.
change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 32) with (w64 T).
change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 38) with (w64 QLv).
change (ew (Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)) 47) with (w64 SLv).
unfold w64. rewrite !unsigned_lit_small by (nums; lia).
unfold t_qc. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold AFgp.SLv, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kBatchBytes, kBatchSlots, kSpaceSize, kPrimResvSize, QSTACK in *.
repeat split; lia.
+ split; [|split; exact I]. cbn [AFgp.FFP f_atoms atoms_ok].
set (E := Ereg regs (AFgp.XW ly u nn QSZv QLv QBv CNTv BSZv)).
assert (E2' : ew E 2 = w64 sp0) by (rewrite (AFgp.E2 ly regs u nn QSZv QLv QBv CNTv BSZv : ew E 2 = getr regs 2); unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k0 Xv lo hi al, ew E k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, QSTACK in *.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp Hlo Hhi T4 T7 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [reflexivity| | | |]. all: clear - CR0 TAL H1; first [lia | exact TAL]. }
split. { apply (AF 34%nat u); [reflexivity| | | |]. all: clear - CR0 U1 U2 U3 U4; first [lia | change (2 ^ 4) with 16; exact U3]. }
split. { apply (AF 35%nat nn); [reflexivity| | | |]. all: clear - CR0 U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat QSZv); [reflexivity| | | |]. all: clear - CR0 Qc QSZ1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat QLv); [reflexivity| | | |]. all: clear - CR0 L3 L4 L5; first [lia | change (2 ^ 13) with 8192; exact L3]. }
split. { apply (AF 39%nat QBv); [reflexivity| | | |]. all: clear - CR0 Qa Qb U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 45%nat CNTv); [reflexivity| | | |]. all: clear - CR0 C0 HR; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 46%nat BSZv); [reflexivity| | | |]. all: clear - CR0 B1 B2 Qa Qb U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 47%nat SLv); [reflexivity| | | |]. all: clear - CR0 L3 L4 L5 C0 HR; unfold AFgp.SLv; first [lia | change (2 ^ 3) with 8; lia]. }
Qed.
Local Notation WINp := (AFgp.WIN ly regs QLv CNTv).
Local Notation S' := (AFf1.S' X k).
Lemma WIN_zone : forall a, WINp a -> (sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof Hroom as HR. pose proof (lo_space_in ly LO) as [SI1 SI2].
unfold AFgp.WIN, AFgp.SLv in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- left. exact Hw.
- right; left. clear - Hw. unfold t_qc, kThreadObjSize in *. lia.
- right; right. clear - Hw L1 L2 SI2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
- right; right. clear - Hw L1 L2 SI2 HR. unfold CNTv, kBatchBytes, kBatchSlots, kSpaceSize, kPrimResvSize in *. lia.
Qed.
Lemma WIN_dec : forall a, WINp a \/ ~ WINp a.
Proof.
intros a. unfold AFgp.WIN. fold sp0.
destruct (Z_le_gt_dec (sp0 - 64) a); destruct (Z_lt_ge_dec a sp0); destruct (Z_le_gt_dec (T + t_qc + 24) a); destruct (Z_lt_ge_dec a (T + t_qc + 32));
destruct (Z_le_gt_dec (QLv + 8) a); destruct (Z_lt_ge_dec a (QLv + 24)); destruct (Z_le_gt_dec (SLv + 24) a); destruct (Z_lt_ge_dec a (SLv + 32)); lia.
Qed.
Definition low_okp (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_okp (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okp a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okp (TFIB_TSD + o) w
| ATp o => low_okp (TFIB_TP + o) w
| AInst o => low_okp (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locp : forallb const_loc_okp (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINp (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locp c Hc) as K. unfold const_loc_okp in K.
pose proof (lo_high ly LO) as H. pose proof ZT as H1. unfold in_high in H. unfold zone3 in H1. cbn [fst snd] in H.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (AFfq.GEO B ly X W mem M) as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINp a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okp a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINp (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_okp in L.
split; [apply ZN|]; clear - L Hi H H1 T7 S1; unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, QSTACK, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6270976 / 8) with 783872 in *; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi H1 T4 T7 S1 S2 G_PT G_TS; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi C1 C2 S1 S2 T4 T7 G_PC G_TC G_CS; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi D1 D2 S1 S2 T4 T7 G_PD G_TD G_DS; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma FINPH : forall W' c', AFgp.at_RETP W ly regs mem md u nn QLv QBv CNTv BSZv W' c' -> enq_leaf B ly X W regs mem md k (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL').
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS). cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof last_geom as (L1 & L2 & L3 & L4 & L5). pose proof Hroom as HR.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (WD : forall a, WINp a -> AFf1.D ly lb sp0 a).
{ intros a Hw. unfold AFf1.D, AFf1.DT, AFf1.DL, AFf1.DS. unfold AFf1.QLv, AFf1.CNTv.
unfold AFgp.WIN, AFgp.SLv in Hw. fold sp0 in Hw. unfold QLv, CNTv in Hw.
destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [do 2 right; clear - Hw; unfold QSTACK; lia | left; exact Hw | right; left; left; exact Hw | right; left; right; lia]. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf1.D ly lb sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (mem' x) as [b'|] eqn:E'; [cbn in HN; discriminate|].
destruct (mem x) as [b0|] eqn:Eb0; [|exact (Hv HN)].
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- apply (MEQ' x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes q + nn) 8 i)).
{ apply (VM _ _ 8%nat _ _ V1); [reflexivity | unfold AFgq.QBv; reflexivity]. }
assert (NEW_lsz : forall i, (i < 8)%nat -> rd' (AFf1.QLv ly lb + 8 + Z.of_nat i) = Some (YG0f.le_byte (b_bytes lb + nn) 8 i)).
{ apply (VM _ _ 8%nat _ _ V2); [unfold AFf1.QLv, QLv; reflexivity | unfold BSZv; reflexivity]. }
assert (NEW_lcnt : forall i, (i < 8)%nat -> rd' (AFf1.QLv ly lb + 16 + Z.of_nat i) = Some (YG0f.le_byte (AFf1.CNTv lb + 1) 8 i)).
{ apply (VM _ _ 8%nat _ _ V3); [unfold AFf1.QLv, QLv; reflexivity | unfold AFf1.CNTv, CNTv; reflexivity]. }
assert (NEW_slot : forall i, (i < 8)%nat -> rd' (AFf1.QLv ly lb + 24 + 8 * AFf1.CNTv lb + Z.of_nat i) = Some (YG0f.le_byte (u - 16) 8 i)).
{ apply (VM _ _ 8%nat _ _ V4); [unfold AFgp.SLv, AFf1.QLv, AFf1.CNTv, QLv, CNTv; lia | reflexivity]. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc)|].
intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as [X1 X2]. apply aview_same.
apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. exact X1. }
pose proof (AFf1.enq_finp_ARm B TB ly X rd rd' M' k Hk Hst Hnq lb initr Hrev Hroom sp0 HSP' IMG AG VIS NEW_qb NEW_lsz NEW_lcnt NEW_slot CONST') as MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md), None. split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
2:{ split; [reflexivity|]. split; [exact HNB|]. split; [reflexivity|]. split; reflexivity. }
split; [|split; [apply layout_le_refl | split; [apply wle_refl | split; [|split; [|split]]]]].
- split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (AFf1.ALedger_S' ly X k tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as [BUD PIN]. split; [| exact (AFf1.asecA_S' ly X k _ PIN)].
eapply Z.le_trans; [exact BUD|]. rewrite <- (AFf1.abudget_S' X k). apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [exact MF | reflexivity].
* reflexivity.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
pose proof ZT as hT. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize in hT.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold AFf1.D, AFf1.DT, AFf1.DL, AFf1.DS, AFf1.QLv, AFf1.CNTv. unfold QLv in L4.
clear - SBg hT L4 T7 HSP' HR. unfold kHighMemBeg, QSTACK, CNTv, kBatchSlots, t_qc in *. intros [Y|[[Y|Y]|Y]]; lia.
- intros r Hr'. apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - R. unfold AFgp.CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
- apply same_io_wvb.
- intros a Ha NO NO' NS NE. apply AG; [exact Ha|]. intros HD.
destruct (AFf1.D_owned B ly X rd M' lb initr Hrev Hroom sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ apply (apresent_same (w_H W) mem); [|apply HPRES; exact Ha]. apply MEQ'.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp HSP' T7; unfold QSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof (AFfq.GEO B ly X W mem M) as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
pose proof (lo_high ly LO) as H. pose proof ZT as H1. unfold in_high in H. unfold zone3 in H1. cbn [fst snd] in H.
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' H H1. ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. lia.
+ apply PRESW. unfold AFgp.WIN. left. fold sp0. lia.
Qed.
Theorem tfib_enqueue_room_arm :
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
rewrite (enqueue_room_eq k X HNB). change (set_qthread (qc_push q k None) X) with S'. cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh3.segP W ly regs mem md u nn QSZv QLv QBv CNTv BSZv (m_vm_materialized md) FH_ok).
- intros W' c' _ HR. exact (FINPH W' c' HR).
Qed.
End e.
Theorem tfib_enqueue_room : forall B, TfibSyms B -> tfib_enqueue_spec_nb B false.
Proof.
intros B TB ly X W regs mem md k HNB ENQ. pose proof ENQ as ((M0 & _) & _).
exact (tfib_enqueue_room_arm B TB ly X W regs mem md k ENQ HNB ltac:(rewrite (am_tsd B ly X _ M0); apply (ts_tsd _ TB))).
Qed.
End d.
