(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFhl AFgw AFfa.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFIB_IMG_END in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Definition scan (p : Z) (nr : Z) (hs : list Z) : Z := fold_left (fun acc h => nr_step p acc h) hs nr.
Lemma scan_cons : forall p nr h hs, scan p nr (h :: hs) = scan p (nr_step p nr h) hs.
Proof. reflexivity. Qed.
Lemma nr_step_range : forall p nr h, 0 <= nr <= p -> 0 <= h -> 0 <= nr_step p nr h <= p.
Proof. intros p nr h H1 H2. unfold nr_step. destruct (h <=? p) eqn:E1; destruct (nr <? h) eqn:E2; cbn [andb]; first [apply Z.leb_le in E1 | apply Z.leb_gt in E1]; lia. Qed.
Lemma scan_spec : forall p hs nr, 0 <= nr <= p -> Forall (fun h => 0 <= h) hs ->
(scan p nr hs = nr \/ In (scan p nr hs) hs) /\ nr <= scan p nr hs <= p /\ (forall h, In h hs -> h <= p -> h <= scan p nr hs).
Proof.
intros p hs. induction hs as [|h hs IH]; intros nr Hnr HF.
- cbn. splits; [left; reflexivity | lia | lia | intros h [] ].
- apply Forall_cons_iff in HF as [Hh HF]. rewrite scan_cons. pose proof (nr_step_range p nr h Hnr Hh) as R.
destruct (IH (nr_step p nr h) R HF) as (A1 & A2 & A3).
assert (ST : nr <= nr_step p nr h /\ (h <= p -> h <= nr_step p nr h) /\ (nr_step p nr h = nr \/ nr_step p nr h = h)).
{ unfold nr_step. destruct (h <=? p) eqn:E1; destruct (nr <? h) eqn:E2; cbn [andb];
first [apply Z.leb_le in E1 | apply Z.leb_gt in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia. }
destruct ST as (S1 & S2 & S3). splits.
+ destruct A1 as [A1|A1]; [| right; right; exact A1]. rewrite A1. destruct S3 as [S3|S3]; [left; exact S3 | right; left; symmetry; exact S3].
+ lia.
+ lia.
+ intros h' [<-|Hin] Hle; [| exact (A3 h' Hin Hle)]. lia.
Qed.
Lemma scan_finds_map : forall p hs (map len : Z) (lens : Z -> Z),
Forall (fun h => 0 <= h) hs -> In map hs -> map <= p < map + len ->
(forall h, In h hs -> h <> map -> h + lens h <= map \/ map + len <= h) -> (forall h, In h hs -> 0 < lens h) ->
0 < map -> scan p 0 hs = map.
Proof.
intros p hs map len lens HF Hin Hp DISJ POS Hp0.
destruct (scan_spec p hs 0 ltac:(lia) HF) as (A1 & A2 & A3).
pose proof (A3 map Hin ltac:(lia)) as LE.
destruct A1 as [A1|A1]; [lia|].
destruct (Z.eq_dec (scan p 0 hs) map) as [E|NE]; [exact E|]. exfalso.
destruct (DISJ _ A1 NE) as [D|D]; [| lia]. pose proof (POS _ A1). lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variables (W : world tfibsegs) (ly : alayout) (md : Model).
Variables (p lim : Z).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hp : 4096 <= p < ASAN_CEIL /\ p mod 16 = 0.
Hypothesis Hlim : lim <= ASAN_CEIL /\ lim mod 8 = 0.
Definition stL (cur nr : Z) (hs : list Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
getr regs 11 = w64 p /\ getr regs 12 = w64 cur /\ getr regs 13 = w64 nr /\ getr regs 14 = w64 lim /\
4096 <= cur /\ cur mod 8 = 0 /\ cur + 8 * Z.of_nat (length hs) = lim /\ 0 <= nr <= p /\
(forall j h, nth_error hs j = Some h ->
val_mem tfibsegs (mrestrict (w_H W) mem) (cur + 8 * Z.of_nat j) 8 h /\
(forall a, cur + 8 * Z.of_nat j <= a < cur + 8 * Z.of_nat j + 8 -> apresent (w_H W) mem a) /\
4096 <= h < ASAN_CEIL /\ h mod 4096 = 0).
Lemma seed_L : forall cur nr h hs regs mem, stL cur nr (h :: hs) regs mem -> AFgw.free_hyps W ly regs mem p cur nr lim h.
Proof.
intros cur nr h hs regs mem (R11 & R12 & R13 & R14 & C1 & C2 & C3 & Hnr & CELLS).
destruct (CELLS 0%nat h eq_refl) as (V & PR & G1 & G2). cbn [Z.of_nat Z.mul] in V, PR. rewrite Z.add_0_r in V. setoid_rewrite Z.add_0_r in PR.
cbn [length] in C3. destruct Hp as [P1 P2]. destruct Hlim as [L1 L2].
assert (C4 : cur + 8 <= lim) by lia.
assert (Ucur : 0 <= cur < 2 ^ 64) by (clear - C1 C4 L1; numconst; lia).
constructor.
- exact LY.
- exact IMG.
- splits; assumption.
- split; assumption.
- splits; try assumption; lia.
- exact Hnr.
- split; assumption.
- split; [exact V | exact PR].
-
rewrite restrict_mkst_fx. unfold AFgw.SS0, AFgw.SR0, sr_set. cbn [bv_eqb]. unfold AFgw.E0, w64. apply (entry_st_ok_full tfibsegs).
+ repeat (apply regs_ok_pin; [| intros XX; discriminate |]); [apply regs_ok_Ereg | ..]; cbn [sv_denot].
* change (ew _ 32) with (Z_to_bv 64 p). rewrite R11. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* change (ew _ 33) with (Z_to_bv 64 cur). rewrite R12. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* change (ew _ 34) with (Z_to_bv 64 nr). rewrite R13. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
* change (ew _ 35) with (Z_to_bv 64 lim). rewrite R14. unfold w64. rewrite Zbv_add_unsigned. first [reflexivity | f_equal; lia].
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. unfold AFgw.REG0, AFgw.R_CUR. apply Forall_cons; [|apply Forall_nil].
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
change (ew _ 33) with (Z_to_bv 64 cur). rewrite unsigned_lit_small by exact Ucur.
split; [lia|]. split; [clear - C1 C4 L1; numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom8 _ _ _ _ 36%nat h); [reflexivity | clear - G1; numconst; lia | rewrite Z.add_0_r; exact V].
+ apply pairwise_disjoint_of_extents. unfold AFgw.REG0, AFgw.R_CUR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. exact (conj I I).
+ split; [|split; exact I]. cbn [AFgw.FFL f_atoms atoms_ok]. numconst.
split. { apply (afact_intro _ 32%nat p); [reflexivity | lia | lia | change (2 ^ 4) with 16; exact P2 | clear; lia]. }
split. { apply (afact_intro _ 33%nat cur); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact C2 | clear; lia]. }
split. { apply (afact_intro _ 34%nat nr); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; lia]. }
split. { apply (afact_intro _ 35%nat lim); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact L2 | clear; lia]. }
split; [|exact I]. { apply (afact_intro _ 36%nat h); [reflexivity | lia | lia | change (2 ^ 12) with 4096; exact G2 | clear; lia]. }
Qed.
Definition at_XGf (regs : bvmap 5 word) (mem : word -> option byte) (nrf : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat',
c' = mkCfg (mkst regs' (w64 0x33888) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md) /\
(forall r : bv 5, In r AFgw.SREGS -> getr regs' r = getr regs r) /\
getr regs' 12 = w64 lim /\ getr regs' 13 = w64 nrf /\
(forall x, mem' x = mem x).
Theorem gloop : forall hs cur nr regs mem mat, hs <> [] -> stL cur nr hs regs mem ->
SRr tfibsegs W (mkCfg (mkst regs (w64 0x3385c) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(at_XGf regs mem (scan p nr hs)).
Proof.
induction hs as [|h hs IH]; intros cur nr regs mem mat NE ST; [exfalso; exact (NE eq_refl)|].
pose proof (seed_L cur nr h hs regs mem ST) as FH. pose proof ST as (R11 & R12 & R13 & R14 & C1 & C2 & C3 & Hnr & CELLS). cbn [length] in C3.
eapply SRr_bind; [exact (segGL W ly regs mem md p cur nr lim h mat FH)|]. intros W' c' _ POST.
unfold AFgw.postL in POST. destruct hs as [|h2 hs2].
-   cbn [length] in C3. replace (cur + 8 <? lim) with false in POST by (symmetry; apply Z.ltb_ge; lia).
destruct POST as (-> & _ & regs' & mem' & mat' & -> & SR & A12 & A13 & MQ). apply SRr_ret.
split; [reflexivity|]. exists regs', mem', mat'. splits; [reflexivity | exact SR | rewrite A12; f_equal; lia | rewrite A13; reflexivity | intros x; exact (MQ x ltac:(intros []))].
- replace (cur + 8 <? lim) with true in POST by (symmetry; apply Z.ltb_lt; cbn [length] in C3; lia).
destruct POST as (-> & _ & regs' & mem' & mat' & -> & SR & A12 & A13 & MQ).
assert (MQ' : forall x, mem' x = mem x) by (intros x; exact (MQ x ltac:(intros []))).
rewrite scan_cons.
eapply SRr_mono; [apply (IH (cur + 8) (nr_step p nr h) regs' mem' mat' ltac:(discriminate))|].
+ destruct (CELLS 0%nat h eq_refl) as (_ & _ & G1 & _). unfold stL.
pose proof (nr_step_range p nr h Hnr ltac:(clear - G1; numconst; lia)) as NR'.
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
+ intros W'' c'' _ (-> & regs'' & mem'' & mat'' & -> & SR' & B12 & B13 & MQ''). split; [reflexivity|]. exists regs'', mem'', mat''.
splits; [reflexivity | intros r Hr; rewrite (SR' r Hr); exact (SR r Hr) | exact B12 | exact B13 | intros x; rewrite (MQ'' x); exact (MQ' x)].
Qed.
End c.
End b.
