(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFf0 AFf2 AFgi AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj YFfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFgq AFgr AFh5 AFh6 AFg3 AFg5 AFft AFfq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma same_io_wvb2 : forall md md' mat mat', same_io (with_vm_backing (m_vm_lazy md) mat md) md' -> same_io md (with_vm_backing (m_vm_lazy md') mat' md').
Proof.
intros [fd [maps lazy mat0] io fs proc lim tm] [fd' [maps' lazy' mat0'] io' fs' proc' lim' tm'] mat mat'. unfold same_io. cbn. intros (I1 & I2 & I3 & I4). repeat split; congruence.
Qed.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre B ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Hypothesis Hl0 : pc_chunks (cache X kBatchClass) = [].
Hypothesis R1 : tfib_refill_spec B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 ENQ)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & _ & Hk & _). exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hst & _). exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & Hnq & _). exact Hnq. Qed.
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma HQL : qloose X.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL). exact (qloosem_loose _ QL). Qed.
Lemma IMG : img_cover ly.
Proof. destruct ENQ as ((_ & LED & _) & _). exact (img_cover_of_ledger ly X md LED). Qed.
Local Notation jst := (AFfq.jst ly W mem).
Local Notation cell_sym := (AFfq.cell_sym B TB ly X W mem M).
Local Notation cell_lit := (AFfq.cell_lit B TB ly X W mem M).
Local Notation cell_state := (AFfq.cell_state B ly X W mem M).
Local Notation cell_stateZ := (AFfq.cell_stateZ B ly X W mem M).
Local Notation val_mem_present := (AFfq.val_mem_present W mem).
Local Notation jst_val := (AFfq.jst_val B ly X W mem sp0 M HSP).
Local Notation root_vals := (AFfq.root_vals B ly X W mem M).
Local Notation count_val := (AFfq.count_val B ly X W mem M).
Local Notation u_facts := (AFfq.u_facts B ly X W mem k M Hk).
Local Notation u_zone := (AFfq.u_zone B ly X W mem k M IMG Hk).
Local Notation q_facts := (AFfq.q_facts B ly X W mem sp0 k M HSP Hk HQL).
Local Notation last_facts := (AFfq.last_facts B ly X W mem sp0 M HSP HNB).
Local Notation chunk_lit := (AFfq.chunk_lit W mem).
Local Notation chunk_lit_at := (AFfq.chunk_lit_at W mem).
Local Notation chunk_atom := (AFfq.chunk_atom W mem).
Local Notation val_mem_writable := (AFfq.val_mem_writable W mem).
Local Notation GEO := (AFfq.GEO B ly X W mem M).
Lemma HI0 : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
kHighMemBeg <= region_base ly kBatchClass /\ region_base ly kBatchClass + 2 ^ 32 <= ASAN_CEIL /\ region_base ly kBatchClass mod 65536 = 0.
Proof.
pose proof (lo_high ly LO) as [P1 P2].
pose proof (Forall_nth_f _ _ 2 _ (lo_app ly LO) eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LO) eq_refl eq_refl)) as T1.
assert (T2 : T + kThreadObjSize <= ASAN_CEIL) by (clear - T1; unfold zone3 in T1; lia). clear IT.
pose proof (lo_top ly LO) as (_ & _ & _ & S4 & _ & _ & S7). pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1' & R2 & R3 & R4 & R5).
splits; assumption.
Qed.
Ltac offw := first [ lia | apply off_img_high; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI0)))); unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, AFgq.CSLv, AFgr.CSLv in *; lia ].
Local Notation E0 := (AFgq.E0 ly regs u nn q 0 0 jst).
Local Notation QSZv := (AFgq.QSZv q).
Local Notation QFv := (AFgq.QFv ly q).
Local Notation QLv := (AFgq.QLv ly q).
Local Notation QBv := (AFgq.QBv q).
Local Notation NBv := (AFgq.NBv ly 0).
Local Notation CSLv := (AFgq.CSLv ly 0).
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgq.E2 ly regs u nn q 0 0 jst). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma EqU : ew E0 34 = w64 u. Proof. reflexivity. Qed.
Lemma EqN : ew E0 35 = w64 nn. Proof. reflexivity. Qed.
Lemma EqQSZ : ew E0 36 = w64 QSZv. Proof. reflexivity. Qed.
Lemma EqQF : ew E0 37 = w64 QFv. Proof. reflexivity. Qed.
Lemma EqQL : ew E0 38 = w64 QLv. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 39 = w64 QBv. Proof. reflexivity. Qed.
Lemma EqCNT : ew E0 40 = w64 0. Proof. reflexivity. Qed.
Lemma EqCP : ew E0 41 = w64 0. Proof. reflexivity. Qed.
Lemma EqJST : ew E0 42 = w64 jst. Proof. reflexivity. Qed.
Lemma EqNB : ew E0 43 = w64 NBv. Proof. reflexivity. Qed.
Lemma EqCSL : ew E0 44 = w64 CSLv. Proof. reflexivity. Qed.
Lemma count0 : val_mem tfibsegs m0 (T + t_cache + 1920) 4 0.
Proof. pose proof count_val as C. rewrite Hl0 in C. destruct (st_cache_inited X); exact C. Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgq.REG0.
Proof.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hR1 & hR2 & _). pose proof HSP as [S1 S2].
pose proof root_vals as (V1 & V2 & V3 & V4). pose proof count0 as C1. pose proof jst_val as [J1 J1R]. pose proof q_facts as (Qa & Qb & Qc & Qd). assert (Qc0 : 0 <= QSZv) by (unfold AFgq.QSZv; clear; lia).
assert (QLR : 0 <= QLv < ASAN_CEIL).
{ unfold AFgq.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; lia|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & _). unfold AFgq.QLv in L1, L2. rewrite Hrev in L1, L2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. lia. }
pose proof u_facts as (Ua & Ub & Uc & Ud).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hR1, hR2, S1, S2, QLR, Qb, Qd, Ua, Ub.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold AFgq.REG0, AFgq.R_ROOT, AFgq.R_CNT, AFgq.R_JST, flit4, flit8, fatom8.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- 64)); [rewrite E2; reflexivity | lia | lia |].
intros a Ha. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia | apply HPRES; clear -Ha; unfold QSTACK in *; lia]. }
apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_qc in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [apply (val_mem_writable _ _ _ _ V1) | destruct (Z_lt_le_dec o 96); [apply (val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [apply (val_mem_writable _ _ _ _ V3) | apply (val_mem_writable _ _ _ _ V4)]]];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom E0 _ _ 8 36%nat 0 QSZv); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | r8 | cbn; lia].
- apply (chunk_atom E0 _ _ 8 37%nat 0 QFv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | r8 | cbn; lia].
- apply (chunk_atom E0 _ _ 8 38%nat 0 QLv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | r8 | cbn; lia].
- apply (chunk_atom E0 _ _ 8 39%nat 0 QBv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom E0 _ _ 4 40%nat 0 0); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact C1 | lia] | r4 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom E0 _ _ 8 42%nat 0 jst); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom E0 0 _ 8 33%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | | r8 | cbn; lia].
rewrite Z.add_0_l. replace 666040 with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TB); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
do 3 (apply Forall_cons; [lit_region|]). apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgq.REG0.
Proof.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (_ & _ & _ & _ & _ & _ & G_TS & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold AFgq.REG0, AFgq.R_ROOT, AFgq.R_CNT, AFgq.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, EqT. unfold w64. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
fold sp0. rewrite !unsigned_lit_small by lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; lia | clear - hT1 CR0; lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgq.FFQ).
Proof.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hR1 & hR2 & hR3). pose proof HSP as [S1 S2].
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as (Qa & Qb & Qc & Qd). pose proof jst_val as [_ JR].
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QLR : 0 <= QLv < ASAN_CEIL /\ QLv mod 8192 = 0).
{ unfold AFgq.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & _). unfold AFgq.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [lia | exact L3]. }
destruct QLR as [QLR QLA].
assert (ENB : NBv = region_base ly kBatchClass) by (unfold AFgq.NBv, region_base; lia).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hR1, hR2, S1, S2, U1, U2, QLR, Qb, Qd.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [AFgq.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [exact EqT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat SB); [exact EqSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 34%nat u); [exact EqU| | | |]. all: clear - CR0 U1 U2 U3 U4; first [lia | change (2 ^ 4) with 16; exact U3]. }
split. { apply (AF 35%nat nn); [exact EqN| | | |]. all: clear - CR0 U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat QSZv); [exact EqQSZ| | | |]. all: clear - CR0 Qc; unfold AFgq.QSZv in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat QFv); [exact EqQF| | | |]. all: clear - CR0 Qd; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat QLv); [exact EqQL| | | |]. all: clear - CR0 QLR QLA; first [lia | change (2 ^ 13) with 8192; exact QLA]. }
split. { apply (AF 39%nat QBv); [exact EqQB| | | |]. all: clear - CR0 Qa Qb U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat 0); [exact EqCNT| | | |]. all: clear; first [lia | reflexivity]. }
split. { apply (AF 41%nat 0); [exact EqCP| | | |]. all: clear; first [lia | reflexivity]. }
split. { apply (AF 42%nat jst); [exact EqJST| | | |]. all: clear - CR0 JR; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat NBv); [exact EqNB| | | |]. all: rewrite ?ENB; clear - CR0 hR1 hR2 hR3; first [lia | change (2 ^ 13) with 8192; apply Z.mod_divide in hR3 as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (8 * c); lia]. }
split; [|exact I]. { apply (AF 44%nat CSLv); [exact EqCSL| | | |]. all: clear - CR0 hT1 hT2 TAL; unfold AFgq.CSLv, t_cache in *;
first [lia | change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (1024 * c + 535); lia]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgq.SS0 (restrict (w_H W) (mkst regs (w64 0x357d0) mem (seg_rom tfibsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha3 & Ha4 & _). rewrite (ts_tp _ TB) in Htp.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
rewrite restrict_mkst_fx. unfold AFgq.SS0, AFgq.SR0, sr_set. cbn [bv_eqb]. unfold AFgq.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q 0 0 jst). rewrite EqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q 0 0 jst). rewrite EqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q 0 0 jst). rewrite EqU, Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q 0 0 jst). rewrite EqN, Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FH0_ok : AFgq.free_hyps W ly regs mem u nn q 0 0 jst.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as QF. pose proof jst_val as [_ JR].
constructor.
- exact LO.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- split; [exact Hlo | exact Hhi].
- exact Hal.
- exact HPRES.
- split; [exact u_zone | exact U3].
- exact IMG.
- exact U4.
- exact QF.
- exact HNB.
- intros lb initr Hrev. pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). splits; assumption.
- lia.
- intros Hc. exfalso. lia.
- exact JR.
- exact SEED_ok.
Qed.
Lemma val_mem_agree : forall (Hh : word -> bool) m m' a (n : nat) v i,
val_mem tfibsegs (mrestrict Hh m) a n v -> val_mem tfibsegs (mrestrict Hh m') a n v -> 0 <= i < Z.of_nat n ->
aview tfibsegs Hh m' (a + i) = aview tfibsegs Hh m (a + i).
Proof.
intros Hh m m' a n v i V V' Hi. unfold aview.
pose proof (V (Z.to_nat i) ltac:(lia)) as E. pose proof (V' (Z.to_nat i) ltac:(lia)) as E'. rewrite Z2Nat.id in E, E' by lia.
rewrite E, E'. reflexivity.
Qed.
Lemma val_mem_some : forall (Hh : word -> bool) m a (n : nat) v i,
val_mem tfibsegs (mrestrict Hh m) a n v -> 0 <= i < Z.of_nat n -> aview tfibsegs Hh m (a + i) <> None.
Proof.
intros Hh m a n v i V Hi. unfold aview. pose proof (V (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite E. discriminate.
Qed.
Lemma aview_raw_some : forall (Hh : word -> bool) m a, 0 <= a < 2 ^ 64 -> aview tfibsegs Hh m a <> None -> TFIB_IMG_END <= a -> m (w64 a) <> None /\ Hh (w64 a) = false.
Proof.
intros Hh m a Ha Hv Himg. unfold aview, mbyte, mrestrict in Hv. unfold w64.
rewrite (seg_rom_none_high a ltac:(lia)) in Hv.
destruct (Hh (Z_to_bv 64 a)) eqn:Hx; [exfalso; apply Hv; reflexivity|].
destruct (m (Z_to_bv 64 a)) eqn:E; [split; [congruence | reflexivity] | exfalso; apply Hv; reflexivity].
Qed.
Section f.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mat : list word).
Let md1 := with_vm_backing (m_vm_lazy md) mat md.
Hypothesis R_ra : getr regs1 1 = w64 0x35924.
Hypothesis R_sp : getr regs1 2 = w64 (sp0 - 64).
Hypothesis R_gp : getr regs1 3 = getr regs 3.
Hypothesis R_tp : getr regs1 4 = getr regs 4.
Hypothesis R_a0 : getr regs1 10 = w64 (T + t_cache).
Hypothesis R_a1 : getr regs1 11 = w64 (T + t_cache + 1920).
Hypothesis R_a2 : getr regs1 12 = w64 0xa2998.
Hypothesis R_a3 : getr regs1 13 = w64 24.
Hypothesis MQ1 : AFgq.MEQ0 ly regs mem mem1.
Hypothesis PR1 : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W) mem1 a.
Hypothesis V1 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc) 8 QSZv.
Hypothesis V2 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc + 8) 8 QFv.
Hypothesis V3 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc + 16) 8 QLv.
Hypothesis V4 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc + 24) 8 QBv.
Hypothesis V5 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_cache + 1920) 4 0.
Hypothesis V6 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_cache_stats + 16) 8 jst.
Lemma AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a.
Proof.
intros a Ha Hs. pose proof root_vals as (W1 & W2 & W3 & W4). pose proof count0 as W5. pose proof jst_val as [W6 _].
assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
destruct (EM (T + t_qc) (T + t_qc + 8)) as [C|C1]; [replace a with (T + t_qc + (a - (T + t_qc))) by lia; apply (val_mem_agree _ _ _ _ 8 _ _ W1 V1); lia|].
destruct (EM (T + t_qc + 8) (T + t_qc + 16)) as [C|C2]; [replace a with (T + t_qc + 8 + (a - (T + t_qc + 8))) by lia; apply (val_mem_agree _ _ _ _ 8 _ _ W2 V2); lia|].
destruct (EM (T + t_qc + 16) (T + t_qc + 24)) as [C|C3]; [replace a with (T + t_qc + 16 + (a - (T + t_qc + 16))) by lia; apply (val_mem_agree _ _ _ _ 8 _ _ W3 V3); lia|].
destruct (EM (T + t_qc + 24) (T + t_qc + 32)) as [C|C4]; [replace a with (T + t_qc + 24 + (a - (T + t_qc + 24))) by lia; apply (val_mem_agree _ _ _ _ 8 _ _ W4 V4); lia|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C5]; [replace a with (T + t_cache + 1920 + (a - (T + t_cache + 1920))) by lia; apply (val_mem_agree _ _ _ _ 4 _ _ W5 V5); lia|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C6]; [replace a with (T + t_cache_stats + 16 + (a - (T + t_cache_stats + 16))) by lia; apply (val_mem_agree _ _ _ _ 8 _ _ W6 V6); lia|].
apply aview_same. apply MQ1. rewrite unsigned_lit_small by exact Ha. unfold AFgq.WIN0, AFgq.WINT. fold sp0. clear - Hs C1 C2 C3 C4 C5 C6. lia.
Qed.
Lemma PRES1 : forall a, sp0 - QSTACK <= a < sp0 -> apresent (w_H W) mem1 a.
Proof.
intros a Ha. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & _ & HPRES & _). unfold spZ in *. fold sp0 in Hlo, HPRES.
destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb]; [|apply PR1; lia].
apply (apresent_same (w_H W) mem); [|apply HPRES; exact Ha]. apply MQ1.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _). pose proof GEO as (_ & _ & _ & _ & _ & _ & G_TS & _). pose proof HSP as [S1 S2].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha S1 hS1 Usp; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
unfold AFgq.WIN0, AFgq.WINT. fold sp0. clear - Ha Hb G_TS S1 S2 hT1 hT2. unfold QSTACK, kThreadObjSize, t_qc, t_cache, t_cache_stats in *. lia.
Qed.
Lemma VIS_T : forall a, AFgq.WINT ly a -> aview tfibsegs (w_H W) mem1 a <> None.
Proof.
intros a Hw. unfold AFgq.WINT in Hw.
assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
destruct (EM (T + t_qc) (T + t_qc + 8)) as [C|C1]; [replace a with (T + t_qc + (a - (T + t_qc))) by lia; apply (val_mem_some _ _ _ 8 _ _ V1); lia|].
destruct (EM (T + t_qc + 8) (T + t_qc + 16)) as [C|C2]; [replace a with (T + t_qc + 8 + (a - (T + t_qc + 8))) by lia; apply (val_mem_some _ _ _ 8 _ _ V2); lia|].
destruct (EM (T + t_qc + 16) (T + t_qc + 24)) as [C|C3]; [replace a with (T + t_qc + 16 + (a - (T + t_qc + 16))) by lia; apply (val_mem_some _ _ _ 8 _ _ V3); lia|].
destruct (EM (T + t_qc + 24) (T + t_qc + 32)) as [C|C4]; [replace a with (T + t_qc + 24 + (a - (T + t_qc + 24))) by lia; apply (val_mem_some _ _ _ 8 _ _ V4); lia|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C5]; [replace a with (T + t_cache + 1920 + (a - (T + t_cache + 1920))) by lia; apply (val_mem_some _ _ _ 4 _ _ V5); lia|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C6]; [replace a with (T + t_cache_stats + 16 + (a - (T + t_cache_stats + 16))) by lia; apply (val_mem_some _ _ _ 8 _ _ V6); lia|].
exfalso. clear - Hw C1 C2 C3 C4 C5 C6. lia.
Qed.
Lemma AR1 : AR tfibsegs B ly X W mem1 md1.
Proof.
destruct ENQ as (HAR & _). pose proof HSP as [S1 S2]. pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply (AR_frame_law_ok tfibsegs B ly X W mem md mem1 md1 HAR).
- intros a Ha Ho. apply AG1; [exact Ha|]. intros Hs. apply (AR_stack_law_ok tfibsegs B ly X W mem md a HAR); [|exact Ho]. clear - Hs S1 S2. unfold QSTACK in *. lia.
- intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem1 x); discriminate|].
destruct (mem1 x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (Z_lt_le_dec a' (sp0 - 64)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a' sp0) as [Hc|Hc]].
2:{ destruct (PR1 a' ltac:(lia)) as [_ [bb Hbb]]. unfold w64 in Hbb. rewrite Ex in Hbb. congruence. }
all: pose proof (AG1 a' Ha' ltac:(lia)) as A; unfold aview, mbyte, mrestrict in A; rewrite Ex, Hx, E', E0, ROM in A; cbn in A; discriminate.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Hb Hx. apply (MQ1 (w64 a)). assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
unfold w64. rewrite unsigned_lit_small by exact Ha'. intros Hw. unfold AFgq.WIN0 in Hw. fold sp0 in Hw. destruct Hw as [Hw|Hw].
+ destruct (PR1 a Hw) as [Hh _]. unfold w64 in Hh, Hx. rewrite Hx in Hh. discriminate.
+ destruct (aview_raw_some (w_H W) mem1 a Ha' (VIS_T a Hw) ltac:(clear - Ha; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia)) as [_ Hh].
unfold w64 in Hh, Hx. rewrite Hx in Hh. discriminate.
Qed.
Lemma REFILL_PRE : refill_pre B ly X W regs1 mem1 md1 kBatchClass.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES. pose proof HSP as [S1 S2]. pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (SP1 : spZ regs1 = sp0 - 64).
{ unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small. clear - Usp S1 hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. lia. }
unfold refill_pre. rewrite SP1. unfold raZ. rewrite R_ra, R_gp, R_tp, R_a0, R_a1, R_a2, R_a3.
split; [exact AR1|]. split; [exact Hbud|]. split; [exact Hpev|]. split; [exact QL|].
split; [vm_compute; reflexivity|]. split; [unfold w64; rewrite unsigned_lit_small by lia; lia|].
split; [clear - Hal; replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [clear - S1; unfold QSTACK, RSTACK in *; lia|]. split; [lia|].
split; [intros a Ha; apply PRES1; clear - Ha; unfold QSTACK, RSTACK in *; lia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [reflexivity|]. split; [unfold kBatchClass; f_equal; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [unfold kBatchClass; lia | exact Hl0].
Qed.
End f.
Lemma refill_tree_apostg : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> preg s c ->
forall tr r, apath (refill_tree c s) tr r -> gflag tr = true ->
WfP U (pp - 1) cc bb (snd r) /\ regs_only s (snd r) /\ st_cache_inited (snd r) = true /\ pc_chunks (cache (snd r) c) <> [].
Proof.
clear. intros U pp cc bb s c W Hc Hpp Hreg tr r Hp Hg.
pose proof (atok_apath_flag _ true _ tr r (refill_tree_ok U pp cc bb s c true W Hc Hpp Hreg) Hp) as (A1 & A2 & A3 & A4).
rewrite (last_flag_true tr Hg) in A4. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros E. discriminate (A4 E).
Qed.
Lemma val_mem_xfer : forall (Hh Hh' : word -> bool) m m' a (n : nat) v,
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs Hh' m' (a + i) = aview tfibsegs Hh m (a + i)) ->
val_mem tfibsegs (mrestrict Hh m) a n v -> val_mem tfibsegs (mrestrict Hh' m') a n v.
Proof.
clear. intros Hh Hh' m m' a n v AG V kk Hk. rewrite <- (V kk Hk). apply (AFgr.aview_eq_mbyte Hh Hh' m m'). apply AG. lia.
Qed.
Section h.
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mat : list word).
Let md1 := with_vm_backing (m_vm_lazy md) mat md.
Hypothesis R_ra : getr regs1 1 = w64 0x35924.
Hypothesis R_sp : getr regs1 2 = w64 (sp0 - 64).
Hypothesis R_gp : getr regs1 3 = getr regs 3.
Hypothesis R_tp : getr regs1 4 = getr regs 4.
Hypothesis R_s0 : getr regs1 8 = w64 (T + t_cache + 1920).
Hypothesis R_s1 : getr regs1 9 = w64 (T + t_cache).
Hypothesis R_s2 : getr regs1 18 = w64 (u - 16).
Hypothesis R_s3 : getr regs1 19 = w64 (T + t_qc).
Hypothesis R_s4 : getr regs1 20 = getr regs 12.
Hypothesis R_s5 : getr regs1 21 = w64 nn.
Hypothesis R_hi : forall r : bv 5, In r [22; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r.
Hypothesis MQ1 : AFgq.MEQ0 ly regs mem mem1.
Hypothesis PR1 : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W) mem1 a.
Hypothesis F1 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 8) 8 (bv_unsigned (getr regs 1)).
Hypothesis F2 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 16) 8 (bv_unsigned (getr regs 8)).
Hypothesis F3 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 24) 8 (bv_unsigned (getr regs 9)).
Hypothesis F4 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 32) 8 (bv_unsigned (getr regs 18)).
Hypothesis F5 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 40) 8 (bv_unsigned (getr regs 19)).
Hypothesis F6 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 48) 8 (bv_unsigned (getr regs 20)).
Hypothesis F7 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 56) 8 (bv_unsigned (getr regs 21)).
Hypothesis G1 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc) 8 QSZv.
Hypothesis G2 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc + 8) 8 QFv.
Hypothesis G3 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc + 16) 8 QLv.
Hypothesis G4 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_qc + 24) 8 QBv.
Hypothesis G5 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_cache + 1920) 4 0.
Hypothesis G6 : val_mem tfibsegs (mrestrict (w_H W) mem1) (T + t_cache_stats + 16) 8 jst.
Variables (W5 : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (X1 : astate).
Hypothesis POST : acall_post tfibsegs B RSTACK ly X W regs1 mem1 md1 (fun _ => False) ly X1 W5 regs' mem' md'.
Hypothesis RO : regs_only X X1.
Hypothesis CI : st_cache_inited X1 = true.
Hypothesis HA0 : getr regs' 10 = w64 1.
Variables (o1 : Z) (l1' : list Z).
Hypothesis El1 : pc_chunks (cache X1 kBatchClass) = o1 :: l1'.
Local Notation l1 := (o1 :: l1').
Local Notation rd5 := (aview tfibsegs (w_H W5) mem').
Local Notation m5 := (mrestrict (w_H W5) mem').
Local Notation q1 := (st_qthread X1).
Definition cnt1 : Z := Z.of_nat (length l1).
Definition coff1 : Z := last l1 0.
Local Notation jst1 := (AFfq.jst ly W5 mem').
Local Notation ra0 := (bv_unsigned (getr regs 1)).
Local Notation s00 := (bv_unsigned (getr regs 8)).
Local Notation s10 := (bv_unsigned (getr regs 9)).
Local Notation s20 := (bv_unsigned (getr regs 18)).
Local Notation s30 := (bv_unsigned (getr regs 19)).
Local Notation s40 := (bv_unsigned (getr regs 20)).
Local Notation s50 := (bv_unsigned (getr regs 21)).
Lemma M1 : ARm B ly X1 rd5. Proof. exact (proj1 (proj1 POST)). Qed.
Lemma Hk1 : In k (st_chunks X1). Proof. destruct RO as (Rck & _). rewrite Rck. exact Hk. Qed.
Lemma Hq1 : st_qthread X1 = st_qthread X. Proof. destruct RO as (_ & _ & _ & _ & Rqt & _). exact Rqt. Qed.
Lemma HQL1 : qloose X1.
Proof. destruct RO as (Rck & _ & _ & _ & Rqt & Rqg & _). pose proof HQL as Q0. unfold qloose, quar_n, queued_n, q_items, all_batches in *. rewrite Rck, Rqt, Rqg. exact Q0. Qed.
Lemma HNB1 : need_new_batch (st_qthread X1) = true. Proof. rewrite Hq1. exact HNB. Qed.
Lemma Hl1ne : l1 <> []. Proof. discriminate. Qed.
Local Notation cell_sym1 := (AFfq.cell_sym B TB ly X1 W5 mem' M1).
Local Notation cell_lit1 := (AFfq.cell_lit B TB ly X1 W5 mem' M1).
Local Notation jst_val1 := (AFfq.jst_val B ly X1 W5 mem' sp0 M1 HSP).
Local Notation root_vals1 := (AFfq.root_vals B ly X1 W5 mem' M1).
Local Notation u_facts1 := (AFfq.u_facts B ly X1 W5 mem' k M1 Hk1).
Local Notation u_zone1 := (AFfq.u_zone B ly X1 W5 mem' k M1 IMG Hk1).
Local Notation q_facts1 := (AFfq.q_facts B ly X1 W5 mem' sp0 k M1 HSP Hk1 HQL1).
Local Notation last_facts1 := (AFfq.last_facts B ly X1 W5 mem' sp0 M1 HSP HNB1).
Local Notation chunk_lit1 := (AFfq.chunk_lit W5 mem').
Local Notation chunk_atom1 := (AFfq.chunk_atom W5 mem').
Local Notation val_mem_writable1 := (AFfq.val_mem_writable W5 mem').
Local Notation HI1 := (AFfq.HI B ly X1 W5 mem' sp0 M1 HSP IMG l1 El1 Hl1ne).
Local Notation cache_vals1 := (AFfq.cache_vals B ly X1 W5 mem' M1 l1 El1 Hl1ne).
Local Notation hit_facts1 := (AFfq.hit_facts B ly X1 W5 mem' sp0 M1 HSP IMG HNB1 l1 El1 Hl1ne).
Local Notation ER := (AFgr.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50).
Local Notation QSZ1 := (AFgr.QSZv q1).
Local Notation QF1 := (AFgr.QFv ly q1).
Local Notation QL1 := (AFgr.QLv ly q1).
Local Notation QB1 := (AFgr.QBv q1).
Local Notation CP1 := (AFgr.CPv coff1).
Local Notation NB1 := (AFgr.NBv ly coff1).
Local Notation CSL1 := (AFgr.CSLv ly cnt1).
Lemma SP' : getr regs' 2 = w64 (sp0 - 64).
Proof. destruct POST as (_ & _ & _ & CS & _). rewrite <- R_sp. exact (CS 2 ltac:(unfold acallee_saved; lia)). Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.
Lemma SPv : bv_unsigned (getr regs' 2) = sp0 - 64.
Proof. rewrite SP'. unfold w64. apply unsigned_lit_small. pose proof HSP as [S1 _]. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). pose proof Usp. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. lia. Qed.
Lemma CSV : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs1 r.
Proof. intros r Hr. destruct POST as (_ & _ & _ & CS & _). rewrite <- (Z_to_bv_bv_unsigned 5 r) at 1 2. exact (CS (bv_unsigned r) Hr). Qed.
Lemma FRAME_AG : forall a, sp0 - 64 <= a < sp0 -> aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) mem1 a.
Proof.
intros a Ha. destruct POST as (AR5 & _ & _ & _ & _ & FR & _). pose proof HSP as [S1 S2]. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). pose proof Usp as U.
apply FR.
- clear - Ha S1 hS1 U. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X W mem md a (proj1 ENQ)). clear - Ha S1 S2. unfold QSTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X1 W5 mem' md' a AR5). clear - Ha S1 S2. unfold QSTACK in *. lia.
- unfold ascratch, spZ. rewrite R_sp, (ts_errno _ TB). unfold w64. rewrite unsigned_lit_small by (clear - S1 hS1 U; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia).
clear - Ha S1 hS1. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_ERRNO, QSTACK, kHighMemBeg in *. lia.
- intros [].
Qed.
Lemma FRAME_PRES : forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W5) mem' a.
Proof.
intros a Ha. pose proof HSP as [S1 S2]. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). pose proof Usp as U.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha S1 hS1 U; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia).
destruct (PR1 a Ha) as [Hh [b Hb]].
assert (V : aview tfibsegs (w_H W5) mem' a <> None).
{ rewrite (FRAME_AG a Ha). unfold aview, mbyte, mrestrict. unfold w64 in Hh, Hb. rewrite Hh, Hb. cbn. discriminate. }
destruct (aview_raw_some (w_H W5) mem' a Ha' V ltac:(clear - Ha S1 hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, QSTACK, kHighMemBeg in *; lia)) as [Hm Hh5].
split; [exact Hh5|]. destruct (mem' (w64 a)) as [b'|] eqn:E; [exists b'; exact E | exfalso; exact (Hm eq_refl)].
Qed.
Lemma FRAME_VAL : forall a v, sp0 - 64 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict (w_H W) mem1) a 8 v -> val_mem tfibsegs m5 a 8 v.
Proof. intros a v H1 H2 V. apply (val_mem_xfer (w_H W) (w_H W5) mem1 mem' a 8 v); [|exact V]. intros i Hi. apply FRAME_AG. lia. Qed.
Lemma E2R : ew ER 2 = getr regs' 2. Proof. exact (AFgr.E2 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). Qed.
Lemma REqT : ew ER 32 = w64 T. Proof. reflexivity. Qed.
Lemma REqSB : ew ER 33 = w64 SB. Proof. reflexivity. Qed.
Lemma REqU : ew ER 34 = w64 u. Proof. reflexivity. Qed.
Lemma REqN : ew ER 35 = w64 nn. Proof. reflexivity. Qed.
Lemma REqQSZ : ew ER 36 = w64 QSZ1. Proof. reflexivity. Qed.
Lemma REqQF : ew ER 37 = w64 QF1. Proof. reflexivity. Qed.
Lemma REqQL : ew ER 38 = w64 QL1. Proof. reflexivity. Qed.
Lemma REqQB : ew ER 39 = w64 QB1. Proof. reflexivity. Qed.
Lemma REqCNT : ew ER 40 = w64 cnt1. Proof. reflexivity. Qed.
Lemma REqCP : ew ER 41 = w64 CP1. Proof. reflexivity. Qed.
Lemma REqJST : ew ER 42 = w64 jst1. Proof. reflexivity. Qed.
Lemma REqNB : ew ER 43 = w64 NB1. Proof. reflexivity. Qed.
Lemma REqCSL : ew ER 44 = w64 CSL1. Proof. reflexivity. Qed.
Lemma REqRA : ew ER 45 = w64 ra0. Proof. reflexivity. Qed.
Lemma REqS0 : ew ER 46 = w64 s00. Proof. reflexivity. Qed.
Lemma REqS1 : ew ER 47 = w64 s10. Proof. reflexivity. Qed.
Lemma REqS2 : ew ER 48 = w64 s20. Proof. reflexivity. Qed.
Lemma REqS3 : ew ER 49 = w64 s30. Proof. reflexivity. Qed.
Lemma REqS4 : ew ER 50 = w64 s40. Proof. reflexivity. Qed.
Lemma REqS5 : ew ER 51 = w64 s50. Proof. reflexivity. Qed.
Lemma BV2R : bv_unsigned (ew ER 2) = sp0 - 64. Proof. rewrite E2R. exact SPv. Qed.
Local Ltac wfq2wfr :=
change (AFgq.QSZv q1) with QSZ1 in *; change (AFgq.QFv ly q1) with QF1 in *; change (AFgq.QLv ly q1) with QL1 in *;
change (AFgq.QBv q1) with QB1 in *; change (AFgq.CPv (AFfq.coff l1)) with CP1 in *;
change (AFgq.NBv ly (AFfq.coff l1)) with NB1 in *; change (AFgq.CSLv ly (AFfq.cnt l1)) with CSL1 in *;
change (AFfq.cnt l1) with cnt1 in *; change (AFfq.coff l1) with coff1 in *.
Local Ltac reg_introR := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8R := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4R := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_regionR :=
reg_introR; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit1; [apply cell_lit1; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma QLR1 : 0 <= QL1 < ASAN_CEIL /\ QL1 mod 8192 = 0.
Proof.
pose proof HI1 as (hP1 & hP2 & _ & _ & _ & _ & hSP1 & hSP2 & _).
unfold AFgr.QLv. destruct (rev (qc_list q1)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|].
pose proof (last_facts1 lb initr Hrev) as (L1 & L2 & L3 & _). unfold AFgq.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [lia | exact L3].
Qed.
Lemma REG0R_ok : Forall (region_ok tfibsegs ER m5) AFgr.REG0.
Proof.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
pose proof root_vals1 as (V1 & V2 & V3 & V4). pose proof cache_vals1 as (C1 & C2 & C3 & C4 & C5). pose proof jst_val1 as [J1 J1R]. pose proof q_facts1 as (Qa & Qb & Qc & Qd).
wfq2wfr. assert (Qc0 : 0 <= QSZ1) by (unfold AFgr.QSZv; clear; lia).
pose proof QLR1 as [QLR _]. pose proof u_facts1 as (Ua & Ub & Uc & Ud). pose proof Usp as U.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, QLR, Qb, Qd, Ua, Ub.
unfold AFgr.REG0, AFgr.R_FRAME, AFgr.R_ROOT, AFgr.R_CNT, AFgr.R_JST, flit4, flit8, fatom8.
apply Forall_cons.
{   reg_introR. rewrite BV2R.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]].
- apply (chunk_atom1 ER _ _ 8 51%nat 0 s50); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 56) _ ltac:(lia) ltac:(lia) F7) | lia] | pose proof (u64_range (getr regs 21)); r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 50%nat 0 s40); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 48) _ ltac:(lia) ltac:(lia) F6) | lia] | pose proof (u64_range (getr regs 20)); r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 49%nat 0 s30); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 40) _ ltac:(lia) ltac:(lia) F5) | lia] | pose proof (u64_range (getr regs 19)); r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 48%nat 0 s20); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 32) _ ltac:(lia) ltac:(lia) F4) | lia] | pose proof (u64_range (getr regs 18)); r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 47%nat 0 s10); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 24) _ ltac:(lia) ltac:(lia) F3) | lia] | pose proof (u64_range (getr regs 9)); r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 46%nat 0 s00); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 16) _ ltac:(lia) ltac:(lia) F2) | lia] | pose proof (u64_range (getr regs 8)); r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 45%nat 0 ra0); [rewrite Z.sub_0_r; reflexivity | rewrite Z.sub_0_r; apply u64_range | eapply val_mem_addr; [exact (FRAME_VAL (sp0 - 8) _ ltac:(lia) ltac:(lia) F1) | lia] | pose proof (u64_range (getr regs 1)); r8R | cbn; lia]. }
apply Forall_cons. {   reg_introR. rewrite REqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_qc in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [apply (val_mem_writable1 _ _ _ _ V1) | destruct (Z_lt_le_dec o 96); [apply (val_mem_writable1 _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [apply (val_mem_writable1 _ _ _ _ V3) | apply (val_mem_writable1 _ _ _ _ V4)]]];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom1 ER _ _ 8 36%nat 0 QSZ1); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 37%nat 0 QF1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 38%nat 0 QL1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | r8R | cbn; lia].
- apply (chunk_atom1 ER _ _ 8 39%nat 0 QB1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | r8R | cbn; lia]. }
apply Forall_cons. {   reg_introR. rewrite REqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable1 _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom1 ER _ _ 4 40%nat 0 cnt1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact C1 | lia] | r4R | cbn; lia]. }
apply Forall_cons. {   reg_introR. rewrite REqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable1 _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom1 ER _ _ 8 42%nat 0 jst1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | r8R | cbn; lia]. }
apply Forall_cons. {   reg_introR. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom1 ER 0 _ 8 33%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | | r8R | cbn; lia].
rewrite Z.add_0_l. replace 666040 with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TB); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym1. vm_compute. reflexivity. }
do 3 (apply Forall_cons; [lit_regionR|]). apply Forall_nil.
Qed.
Lemma PAIRSR_ok : pairwise_disjoint ER AFgr.REG0.
Proof.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (_ & _ & _ & _ & _ & _ & G_TS & _). pose proof Usp as U.
apply pairwise_disjoint_of_extents. unfold AFgr.REG0, AFgr.R_FRAME, AFgr.R_ROOT, AFgr.R_CNT, AFgr.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite BV2R, REqT. unfold w64. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
rewrite !unsigned_lit_small by lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; lia | clear - hT1 CR0; lia].
Qed.
Lemma FACTSR_ok : atoms_ok ER (f_atoms AFgr.FFQ).
Proof.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2]. pose proof Usp as U.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof u_facts1 as (U1 & U2 & U3 & U4). pose proof q_facts1 as (Qa & Qb & Qc & Qd). pose proof jst_val1 as [_ JR].
pose proof cache_vals1 as (_ & _ & _ & C4 & C5). pose proof hit_facts1 as (F1' & F2' & F3' & F4' & F5' & F6' & _). wfq2wfr.
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
pose proof QLR1 as [QLR QLA].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK, RSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, U1, U2, QLR, F2', F4', F5', Qb, Qd.
assert (E2' : ew ER 2 = w64 (sp0 - 64)) by (rewrite E2R; exact SP').
assert (AF : forall k0 Xv lo hi al, ew ER k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok ER k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [AFgr.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK, RSTACK.
split. { apply (AF 2%nat (sp0 - 64)); [exact E2'| | | |]. all: clear - CR0 U S1 S2 hS1 hS2 Hal; first [lia | change (2 ^ 4) with 16; replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal]. }
split. { apply (AF 32%nat T); [exact REqT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat SB); [exact REqSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 34%nat u); [exact REqU| | | |]. all: clear - CR0 U1 U2 U3 U4; first [lia | change (2 ^ 4) with 16; exact U3]. }
split. { apply (AF 35%nat nn); [exact REqN| | | |]. all: clear - CR0 U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat QSZ1); [exact REqQSZ| | | |]. all: clear - CR0 Qc; unfold AFgr.QSZv in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat QF1); [exact REqQF| | | |]. all: clear - CR0 Qd; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat QL1); [exact REqQL| | | |]. all: clear - CR0 QLR QLA; first [lia | change (2 ^ 13) with 8192; exact QLA]. }
split. { apply (AF 39%nat QB1); [exact REqQB| | | |]. all: clear - CR0 Qa Qb U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat cnt1); [exact REqCNT| | | |]. all: clear - CR0 C4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 41%nat CP1); [exact REqCP| | | |]. all: clear - CR0 F1' F2' F3'; unfold AFgr.CPv; first [pose proof (Z.div_pos coff1 16); pose proof (Z.div_lt_upper_bound coff1 16 (2 ^ 27)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 42%nat jst1); [exact REqJST| | | |]. all: clear - CR0 JR; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat NB1); [exact REqNB| | | |]. all: clear - CR0 F4' F5' F6' hP1 hP2 hSP1 hSP2; first [lia | change (2 ^ 13) with 8192; exact F6']. }
split. { apply (AF 44%nat CSL1); [exact REqCSL| | | |]. all: clear - CR0 C4 C5 hT1 hT2 TAL; unfold AFgr.CSLv, t_cache in *;
first [lia | change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (1024 * c + 536 + (cnt1 - 1)); lia]. }
split. { apply (AF 45%nat ra0); [exact REqRA | apply u64_range | pose proof (u64_range (getr regs 1)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 46%nat s00); [exact REqS0 | apply u64_range | pose proof (u64_range (getr regs 8)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 47%nat s10); [exact REqS1 | apply u64_range | pose proof (u64_range (getr regs 9)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 48%nat s20); [exact REqS2 | apply u64_range | pose proof (u64_range (getr regs 18)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 49%nat s30); [exact REqS3 | apply u64_range | pose proof (u64_range (getr regs 19)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split. { apply (AF 50%nat s40); [exact REqS4 | apply u64_range | pose proof (u64_range (getr regs 20)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
split; [|exact I]. { apply (AF 51%nat s50); [exact REqS5 | apply u64_range | pose proof (u64_range (getr regs 21)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
Qed.
Lemma SEEDR_ok : st_ok tfibsegs ER AFgr.SS0 (restrict (w_H W5) (mkst regs' (w64 0x35924) mem' (seg_rom tfibsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
pose proof u_facts1 as (U1 & U2 & U3 & U4). pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
assert (P4 : getr regs' 4 = w64 TFIB_TP) by (rewrite (CSV 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), R_tp; exact Htp).
assert (P8 : getr regs' 8 = w64 (T + t_cache + 1920)) by (rewrite (CSV 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)); exact R_s0).
assert (P9 : getr regs' 9 = w64 (T + t_cache)) by (rewrite (CSV 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)); exact R_s1).
assert (P18 : getr regs' 18 = w64 (u - 16)) by (rewrite (CSV 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)); exact R_s2).
assert (P19 : getr regs' 19 = w64 (T + t_qc)) by (rewrite (CSV 19%bv ltac:(change (bv_unsigned (19%bv : bv 5)) with 19; unfold acallee_saved; lia)); exact R_s3).
assert (P21 : getr regs' 21 = w64 nn) by (rewrite (CSV 21%bv ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)); exact R_s5).
rewrite restrict_mkst_fx. unfold AFgr.SS0, AFgr.SR0, sr_set. cbn [bv_eqb]. unfold AFgr.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg
| intros XX; discriminate | cbn [sv_denot]; exact P4]
| intros XX; discriminate | cbn [sv_denot]; exact HA0]
| intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (AFgr.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqT, P8. unfold w64. rewrite Zbv_add_unsigned. f_equal; unfold t_cache; lia.
+ cbn [sv_denot]. fold (AFgr.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqT, P9. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgr.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqU, P18. unfold w64. rewrite Zbv_add_unsigned. f_equal; lia.
+ cbn [sv_denot]. fold (AFgr.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqT, P19. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgr.E0 ly regs' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50). rewrite REqN, P21. unfold w64. rewrite Zbv_add_unsigned. f_equal; lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0R_ok.
- exact PAIRSR_ok.
- split; [exact FACTSR_ok | split; exact I].
Qed.
Theorem FHR_ok : AFgr.free_hyps W5 ly regs' mem' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof u_facts1 as (U1 & U2 & U3 & U4). pose proof q_facts1 as QF. pose proof jst_val1 as [_ JR]. pose proof cache_vals1 as (C1 & C2 & C3 & C4 & C5).
pose proof hit_facts1 as (F1' & F2' & F3' & F4' & F5' & F6' & F7' & F8'). wfq2wfr.
constructor.
- exact LO.
- rewrite (CSV 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), R_tp. rewrite (ts_tp _ TB) in Htp. exact Htp.
- unfold YK0s.ret_ok in *. unfold w64. rewrite Z_to_bv_bv_unsigned. exact Hra.
- exact Hra4.
- rewrite SPv. unfold QSTACK, RSTACK in *. lia.
- rewrite SPv. replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite SPv. intros a Ha. apply FRAME_PRES. lia.
- rewrite SPv. splits; (eapply val_mem_addr; [apply FRAME_VAL; [| | eassumption]; lia | lia]).
- splits; apply u64_range.
- split; [exact u_zone1 | exact U3].
- exact IMG.
- exact U4.
- exact QF.
- exact HNB1.
- intros lb initr Hrev. pose proof (last_facts1 lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). wfq2wfr. splits; assumption.
- clear - C4 C5. lia.
- intros _. splits; try assumption.
- exact JR.
- exact SEEDR_ok.
Qed.
Local Notation WINr := (AFgr.WIN ly q1 cnt1 coff1).
Local Notation S'1 := (AFf2.S' X1 k l1).
Lemma WINR_zone : forall a, WINr a -> (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & HL). wfq2wfr.
unfold AFgr.WIN, AFgr.WINT, AFgr.WINA in Hw.
destruct Hw as [Hw|[[_ Hw]|[Hq Hw]]].
- left. clear - Hw. unfold t_qc, t_cache, t_cache_stats, kThreadObjSize in *. lia.
- right. clear - Hw hN1 hN2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
- right. destruct (rev (qc_list q1)) as [|lb initr] eqn:Hrev.
+ exfalso. apply Hq. rewrite <- (rev_involutive (qc_list q1)), Hrev. reflexivity.
+ pose proof (HL lb initr eq_refl) as [L1 L2]. unfold AFgq.QLv, AFgr.QLv in L1, L2, Hw. rewrite ?Hrev in Hw, L1, L2.
clear - Hw L1 L2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
Qed.
Lemma WINR_dec : forall a, WINr a \/ ~ WINr a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
pose proof cache_vals1 as (_ & _ & _ & _ & C5). wfq2wfr.
assert (LQ : qc_list q1 = [] \/ qc_list q1 <> []) by (destruct (qc_list q1); [left; reflexivity | right; discriminate]).
unfold AFgr.WIN, AFgr.WINT, AFgr.WINA.
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C1]; [left; left; left; exact C|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C2]; [left; left; right; left; exact C|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C3]; [left; left; right; right; exact C|].
destruct (EM NB1 (NB1 + 32)) as [C|C4]; [left; right; left; split; [exact C5 | exact C]|].
destruct LQ as [LQ|LQ].
- right. intros [[Y1|[Y2|Y3]]|[[_ Y4]|[Y5 _]]]; [exact (C1 Y1) | exact (C2 Y2) | exact (C3 Y3) | exact (C4 Y4) | exact (Y5 LQ)].
- destruct (EM QL1 (QL1 + 8)) as [C|C6]; [left; right; right; split; [exact LQ | exact C]|].
right. intros [[Y1|[Y2|Y3]]|[[_ Y4]|[_ Y5]]]; [exact (C1 Y1) | exact (C2 Y2) | exact (C3 Y3) | exact (C4 Y4) | exact (C6 Y5)].
Qed.
Lemma CONST_OUTR : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINr (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (AFg5.Tfib_const_locq ly) c Hc) as K. unfold AFg5.const_loc_okq in K.
pose proof HI1 as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINr a).
{ intros a Hn Hw. exact (Hn (WINR_zone a Hw)). }
assert (LOW : forall a, AFg5.low_okq a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINr (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold AFg5.low_okq in L.
split; [apply ZN|]; clear - L Hi hP1 hT1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6270976 / 8) with 783872 in *; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 G_PT; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize in *; lia.
- split; [apply ZN|]; clear - K Hi C1 C2 G_PC G_TC; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi D1 D2 G_PD G_TD; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize in *; lia.
Qed.
Lemma aowned_same : forall S1 S2 a, st_chunks S2 = st_chunks S1 -> st_fs S2 = st_fs S1 -> aowned B ly S2 a -> aowned B ly S1 a.
Proof. clear. intros S1 S2 a E1 E2 H. unfold aowned, aclient_byte, sec_extents, frames in *. rewrite E1, E2 in H. exact H. Qed.
Lemma FINR : forall W6 c6, AFh6.at_RETR W5 ly regs' mem' md' u nn q1 cnt1 coff1 ra0 s00 s10 s20 s30 s40 s50 W6 c6 ->
enq_leaf B ly X W regs mem md k (tt, S'1) W6 c6.
Proof.
intros W6 c6 HR.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL0).
destruct HAR as (M0 & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof POST as POST'. destruct POST' as (AR5 & LLE & WLE & CS & SIO & FR & PRS). destruct AR5 as (M5 & LED5 & BUD5 & MW5 & HSH5).
destruct HR as (-> & regs6 & mem6 & mat6 & -> & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QCS & MEQ6 & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
set (rd6 := aview tfibsegs (w_H W5) mem6).
pose proof Usp as U. pose proof HSP as HSP'. pose proof cache_vals1 as (_ & _ & _ & C4 & C5). wfq2wfr.
destruct RO as (Rck & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev).
assert (ENB : NB1 = SB + (region_off kBatchClass + last l1 0)) by (unfold AFgr.NBv, coff1; lia).
assert (SPR : spZ regs1 = sp0 - 64).
{ unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small. pose proof HI0 as (_ & _ & _ & _ & hS1 & _). clear - U hS1 HSP'. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *. lia. }
assert (WD : forall a, WINr a -> AFf2.D ly X1 l1 sp0 a).
{ intros a Hw. unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS.
unfold AFgr.WIN, AFgr.WINT, AFgr.WINA in Hw. rewrite ENB in Hw.
destruct Hw as [Hw|[[_ Hw]|[Hq Hw]]].
- left. exact Hw.
- right; left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFf2.QLv. unfold AFgr.QLv in Hw. exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf2.D ly X1 l1 sp0 a -> rd6 a = rd5 a).
{ intros a Ha ND. subst rd6. apply aview_same. apply (MEQ6 (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WD a X')). }
assert (VIS : forall a, rd5 a <> None -> rd6 a <> None).
{ intros a Hv HN. subst rd6. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W5 x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem6 x); discriminate|].
destruct (mem6 x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem' x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WINR_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ6 x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W5 (w64 a) = true -> mem6 (w64 a) = mem' (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (WINR_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- apply (MEQ6 x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W5) mem6) a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd6 (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd6. exact (AFg5.val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd6 (T + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list q1)) + 1) 8 i)).
{ apply (VM _ _ 8%nat _ _ V1); [reflexivity | unfold AFgr.QSZv; reflexivity]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd6 (T + t_qc + 8 + Z.of_nat i) =
Some (YG0f.le_byte (match qc_list q1 with [] => SB + (region_off kBatchClass + last l1 0) | b0 :: _ => SB + b_self b0 end) 8 i)).
{ apply (VM _ _ 8%nat _ _ V2); [reflexivity|]. unfold AFh6.QF', AFgr.QFv. rewrite ENB. destruct (qc_list q1); reflexivity. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd6 (T + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte (SB + (region_off kBatchClass + last l1 0)) 8 i)).
{ apply (VM _ _ 8%nat _ _ V3); [reflexivity | exact ENB]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd6 (T + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes q1 + nn + kBatchBytes) 8 i)).
{ apply (VM _ _ 8%nat _ _ V4); [reflexivity | unfold AFgr.QBv; reflexivity]. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd6 (T + t_cache + 1920 + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length l1) - 1) 4 i)).
{ apply (VM _ _ 4%nat _ _ V5); [reflexivity | unfold cnt1; reflexivity]. }
assert (NEW_n0 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + Z.of_nat i) = Some (YG0f.le_byte 0 8 i)).
{ apply (VM _ _ 8%nat _ _ V6); [exact ENB | reflexivity]. }
assert (NEW_n8 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + 8 + Z.of_nat i) = Some (YG0f.le_byte (nn + kBatchBytes) 8 i)).
{ apply (VM _ _ 8%nat _ _ V7); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_n16 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + 16 + Z.of_nat i) = Some (YG0f.le_byte 1 8 i)).
{ apply (VM _ _ 8%nat _ _ V8); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_n24 : forall i, (i < 8)%nat -> rd6 (SB + (region_off kBatchClass + last l1 0) + 24 + Z.of_nat i) = Some (YG0f.le_byte (u - 16) 8 i)).
{ apply (VM _ _ 8%nat _ _ V9); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_lnext : forall lb initr, rev (qc_list q1) = lb :: initr ->
forall i, (i < 8)%nat -> rd6 (SB + b_self lb + Z.of_nat i) = Some (YG0f.le_byte (SB + (region_off kBatchClass + last l1 0)) 8 i)).
{ intros lb initr Hrev. apply (VM _ _ 8%nat _ _ (VL lb initr Hrev)); [| exact ENB]. unfold AFgr.QLv. rewrite Hrev. reflexivity. }
assert (CONST' : Forall (cell_holds B ly rd6) (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd5); [exact (proj1 (Forall_forall _ _) (am_const B ly X1 _ M5) c Hc)|].
intros i Hi. subst rd6. destruct (proj1 (Forall_forall _ _) CONST_OUTR c Hc i Hi) as [X1' X2]. apply aview_same.
apply (MEQ6 (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. exact X1'. }
assert (Hnq1 : ~ In (ck_beg k) (map ck_beg (q_items X1))).
{ unfold q_items, all_batches. rewrite Rqt, Rqg. exact Hnq. }
assert (Hbev1 : Z.of_nat (length (all_batches X1)) + 1 <= st_nev X1) by (unfold all_batches; rewrite Rqt, Rqg, Rnev; exact Hbev).
pose proof (AFf2.enq_fin_ARm B TB ly X1 rd5 rd6 M5 k Hk1 Hst Hnq1 HNB1   CI l1 El1 Hl1ne sp0 HSP' IMG AG VIS
NEW_qs NEW_qf NEW_ql NEW_qb NEW_cnt NEW_n0 NEW_n8 NEW_n16 NEW_n24 NEW_lnext CONST' Hbev1) as MF.
exists regs6, mem6, (with_vm_backing (m_vm_lazy md') mat6 md'), (Some (region_off kBatchClass + last l1 0)). split.
{ unfold cfg_at, raZ, w64. reflexivity. }
split.
2:{ split; [cbn; rewrite Rqt; reflexivity|]. split; [exact HNB|]. split; [cbn; exact Rck|]. split; [cbn; exact Rqg | cbn; exact Rfs]. }
split; [|split; [apply layout_le_refl | split; [exact WLE | split; [|split; [|split]]]]].
- split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (AFf2.ALedger_S' ly X1 k l1 tfibsegs md' LED5) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD5 as [BUD5 PIN5]. split; [| exact (AFf2.asecA_S' ly X1 k l1 _ PIN5)].
eapply Z.le_trans; [exact BUD5|]. rewrite <- (AFf2.abudget_S' X1 k l1). apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW5].
+ eapply (ahs_transfer tfibsegs B ly X1 _ (w_H W5) mem' mem6 (al_img_env tfibsegs ly X1 _ (am_layout B ly X1 _ M5) LED5) M5 HSH5 VIS HSK).
* eapply (aclient_band_same_frames B ly X1); [exact MF | reflexivity].
*   reflexivity.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. subst rd6. apply aview_same. apply (MEQ6 (Z_to_bv 64 _)).
rewrite unsigned_lit_small by (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia). intros Hw. pose proof (WINR_zone _ Hw) as Z3.
pose proof HI1 as (hP1 & _ & hT1 & _). clear - Z3 SBg hP1 hT1. unfold zone3, zone3cases, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, kThreadObjSize, kPrimResvSize in *. lia.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ (r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)) by lia.
destruct RR as [->|[->|[->|[->|[->|[->|[->|RR]]]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q2, SPv. unfold w64, sp0. replace (bv_unsigned (getr regs 2) - 64 + 64) with (bv_unsigned (getr regs 2)) by lia. apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q8. apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q9. apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q18. apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 19) with (19%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q19. apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 20) with (20%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q20. apply Z_to_bv_bv_unsigned.
+ replace (Z_to_bv 5 21) with (21%bv : bv 5) by (symmetry; apply bv_eq; vm_compute; reflexivity). rewrite Q21. apply Z_to_bv_bv_unsigned.
+ assert (E6 : getr regs6 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ apply QCS. clear - RR. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
rewrite E6, (CS r ltac:(unfold acallee_saved; clear - RR; lia)).
clear - RR R_gp R_tp R_hi. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst r;
first [exact R_gp | exact R_tp | apply R_hi; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right])].
-   exact (same_io_wvb2 md md' mat mat6 SIO).
-
intros a Ha NO NO' NS NE.
assert (NO1 : ~ aowned B ly X1 a) by (intros O; apply NO; exact (aowned_same X X1 a Rck Rfs O)).
assert (NDS : ~ AFf2.DS sp0 a) by (intros O; apply NS; unfold ascratch, spZ; left; exact O).
rewrite AG; [| exact Ha | intros HD; destruct (AFf2.D_owned B ly X1 rd5 M5 k CI l1 El1 Hl1ne sp0 HSP' a (proj1 Ha) HD) as [O|O]; [exact (NO1 O) | exact (NDS O)]].
rewrite FR; [| exact Ha | exact NO | exact NO1 | | intros []].
2:{ unfold ascratch in NS |- *. rewrite SPR. unfold spZ in NS. fold sp0 in NS. intros [O|O]; apply NS; [left; clear - O; unfold QSTACK, RSTACK in *; lia | right; exact O]. }
apply (AG1 mem1 MQ1 G1 G2 G3 G4 G5 G6 a Ha). intros O. apply NS. unfold ascratch, spZ. left. fold sp0. clear - O. unfold QSTACK. lia.
-
intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ apply (apresent_same (w_H W5) mem'); [|apply PRS; rewrite SPR; clear - Ha Hb; unfold QSTACK, RSTACK in *; lia]. apply MEQ6.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha U HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WINR_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. lia.
+ apply (apresent_same (w_H W5) mem'); [|apply FRAME_PRES; lia]. apply MEQ6.
pose proof HI0 as (hP1 & hP2 & hT1 & hT2 & hS1 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha U HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WINR_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. lia.
Qed.
Lemma TAIL_SRr : forall mat', SRr tfibsegs W5 (mkCfg (mkst regs' (w64 0x35924) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat' md'))
(enq_leaf B ly X W regs mem md k (tt, S'1)).
Proof.
intros mat'. eapply SRr_mono; [exact (AFh6.segT W5 ly regs' mem' md' u nn q1 cnt1 coff1 jst1 ra0 s00 s10 s20 s30 s40 s50 mat' FHR_ok)|].
intros W6 c6 _ HR. exact (FINR W6 c6 HR).
Qed.
End h.
Lemma WfX1 : WfP (as_universe B) 1 0 0 X.
Proof.
destruct ENQ as (_ & _ & Hbev & (Hpev & _) & _).
apply (AFf2.WfP_reslack _ 0 0 0 1 0 X WF ltac:(lia) ltac:(lia)); [lia| |exact (wf_fa_room _ _ _ _ _ WF)]. pose proof (wf_batches_ev _ _ _ _ _ WF). lia.
Qed.
Theorem tfib_enqueue_miss_arm :
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
apply (amreal_enqueue_nb k X W _ _ HNB).
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
apply amreal_after_SRr. eapply SRr_mono; [exact (AFh5.segR1 W ly regs mem md u nn q 0 0 jst (m_vm_materialized md) FH0_ok eq_refl)|].
intros W' c' _ HC. destruct HC as (-> & regs1 & mem1 & mat & -> & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 & R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
pose proof (R1 ly X W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass
(REFILL_PRE regs1 mem1 mat R_ra R_sp R_gp R_tp R_a0 R_a1 R_a2 R_a3 MQ1 PR1 V1 V2 V3 V4 V5 V6)) as RR.
unfold cfg_at, A_Refill in RR.
pose proof (refill_tree_apostg (as_universe B) 1 0 0 X kBatchClass WfX1 ltac:(unfold kBatchClass; lia) ltac:(lia) (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 ENQ))))))) as APOST.
pose proof (amreal_apostg tfibsegs (refill_tree kBatchClass X) _ W _ _ APOST RR) as RR2. clear RR.
eapply amreal_mono; [|exact RR2]. cbv beta. intros [[] X1] W5 c5 [(WX1 & RO & CI & NE1) HL]. cbn [fst snd] in WX1, RO, CI, NE1, HL.
destruct HL as (regs' & mem' & md' & -> & POST & HA0).
unfold enq_after_refill. cbn [snd].
destruct (pc_chunks (cache X1 kBatchClass)) as [|o1 l1'] eqn:El1.
-
exfalso. apply NE1. first [reflexivity | exact El1].
-
cbn [snd] in HA0. rewrite El1 in HA0.
unfold cfg_at, raZ. rewrite R_ra. unfold w64 at 1. rewrite unsigned_lit_small by lia. rewrite <- (wvb_self md') at 1.
exact (TAIL_SRr regs1 mem1 mat R_sp R_gp R_tp R_s0 R_s1 R_s2 R_s3 R_s5 R_hi MQ1 PR1 F1 F2 F3 F4 F5 F6 F7 V1 V2 V3 V4 V5 V6
W5 regs' mem' md' X1 POST RO CI HA0 o1 l1' El1 (m_vm_materialized md')).
Qed.
End e.
Theorem tfib_enqueue_miss : forall B, TfibSyms B -> tfib_refill_spec B -> forall ly X W regs mem md k,
enq_pre B ly X W regs mem md k -> need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) = [] ->
ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
intros B TB R1 ly X W regs mem md k ENQ HNB Hl0 HTSD.
exact (tfib_enqueue_miss_arm B TB ly X W regs mem md k ENQ HNB Hl0 R1 HTSD).
Qed.
Theorem tfib_enqueue_nb : forall B, TfibSyms B -> tfib_refill_spec B -> tfib_enqueue_spec_nb B true.
Proof.
intros B TB R1 ly X W regs mem md k HNB ENQ.
assert (HT : ly_tsd ly = TFIB_TSD).
{ destruct ENQ as ((M & _) & _). rewrite (am_tsd B ly X _ M). exact (ts_tsd _ TB). }
destruct (pc_chunks (cache X kBatchClass)) as [|o l0] eqn:E.
- exact (tfib_enqueue_miss B TB R1 ly X W regs mem md k ENQ HNB E HT).
- apply (tfib_enqueue_hit B TB ly X W regs mem md k ENQ HNB); [rewrite E; discriminate | exact HT].
Qed.
End d.
