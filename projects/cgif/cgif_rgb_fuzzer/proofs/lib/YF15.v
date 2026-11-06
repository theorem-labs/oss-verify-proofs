(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF3g YF2r YF14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, TFX_IMG_END in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Definition scan (p : Z) (nr : Z) (hs : list Z) : Z := fold_left (fun acc h => nr_step p acc h) hs nr.
Lemma scan_cons : forall p nr h hs, scan p nr (h :: hs) = scan p (nr_step p nr h) hs.
Proof. img_refl. Qed.
Lemma nr_step_range : forall p nr h, 0 <= nr <= p -> 0 <= h -> 0 <= nr_step p nr h <= p.
Proof. intros p nr h H1 H2. unfold nr_step. destruct (h <=? p) eqn:E1; destruct (nr <? h) eqn:E2; cbn [andb]; first [apply Z.leb_le in E1 | apply Z.leb_gt in E1]; img_lia. Qed.
Lemma scan_spec : forall p hs nr, 0 <= nr <= p -> Forall (fun h => 0 <= h) hs ->
(scan p nr hs = nr \/ In (scan p nr hs) hs) /\ nr <= scan p nr hs <= p /\ (forall h, In h hs -> h <= p -> h <= scan p nr hs).
Proof.
intros p hs. induction hs as [|h hs IH]; intros nr Hnr HF.
- cbn. splits; [img_try (left; img_refl) | img_lia | img_lia | img_try (intros h []) ].
- apply Forall_cons_iff in HF as [Hh HF]. rewrite scan_cons. pose proof (nr_step_range p nr h Hnr Hh) as R.
destruct (IH (nr_step p nr h) R HF) as (A1 & A2 & A3).
assert (ST : nr <= nr_step p nr h /\ (h <= p -> h <= nr_step p nr h) /\ (nr_step p nr h = nr \/ nr_step p nr h = h)).
{ unfold nr_step. destruct (h <=? p) eqn:E1; destruct (nr <? h) eqn:E2; cbn [andb];
first [apply Z.leb_le in E1 | apply Z.leb_gt in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; img_lia. }
destruct ST as (S1 & S2 & S3). splits.
+ destruct A1 as [A1|A1]; [| img_try (right; right; img_exact A1)]. rewrite A1. destruct S3 as [S3|S3]; [img_try (left; img_exact S3) | img_try (right; left; symmetry; img_exact S3)].
+ img_lia.
+ img_lia.
+ intros h' [<-|Hin] Hle; [| img_try (img_exact (A3 h' Hin Hle))]. img_lia.
Qed.
Lemma scan_finds_map : forall p hs (map len : Z) (lens : Z -> Z),
Forall (fun h => 0 <= h) hs -> In map hs -> map <= p < map + len ->
(forall h, In h hs -> h <> map -> h + lens h <= map \/ map + len <= h) -> (forall h, In h hs -> 0 < lens h) ->
0 < map -> scan p 0 hs = map.
Proof.
intros p hs map len lens HF Hin Hp DISJ POS Hp0.
destruct (scan_spec p hs 0 ltac:(img_lia) HF) as (A1 & A2 & A3).
pose proof (A3 map Hin ltac:(img_lia)) as LE.
destruct A1 as [A1|A1]; [img_lia|].
destruct (Z.eq_dec (scan p 0 hs) map) as [E|NE]; [img_try (img_exact E)|]. exfalso.
destruct (DISJ _ A1 NE) as [D|D]; [| img_lia]. pose proof (POS _ A1). img_lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout) (md : Model).
Variables (p lim : Z).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hp : 4096 <= p < ASAN_CEIL /\ p mod 16 = 0.
Hypothesis Hlim : lim <= ASAN_CEIL /\ lim mod 8 = 0.
Definition stL (cur nr : Z) (hs : list Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
getr regs 11 = w64 p /\ getr regs 12 = w64 cur /\ getr regs 13 = w64 nr /\ getr regs 14 = w64 lim /\
4096 <= cur /\ cur mod 8 = 0 /\ cur + 8 * Z.of_nat (length hs) = lim /\ 0 <= nr <= p /\
(forall j h, nth_error hs j = Some h ->
val_mem tfxsegs (mrestrict (w_H W) mem) (cur + 8 * Z.of_nat j) 8 h /\
(forall a, cur + 8 * Z.of_nat j <= a < cur + 8 * Z.of_nat j + 8 -> apresent (w_H W) mem a) /\
4096 <= h < ASAN_CEIL /\ h mod 4096 = 0).
Lemma seed_L : forall cur nr h hs regs mem, stL cur nr (h :: hs) regs mem -> YF2r.free_hyps W ly regs mem p cur nr lim h.
Proof.
intros cur nr h hs regs mem (R11 & R12 & R13 & R14 & C1 & C2 & C3 & Hnr & CELLS).
destruct (CELLS 0%nat h eq_refl) as (V & PR & G1 & G2). cbn [Z.of_nat Z.mul] in V, PR. rewrite Z.add_0_r in V. setoid_rewrite Z.add_0_r in PR.
cbn [length] in C3. destruct Hp as [P1 P2]. destruct Hlim as [L1 L2].
assert (C4 : cur + 8 <= lim) by img_lia.
assert (Ucur : 0 <= cur < 2 ^ 64) by (img_try (clear - C1 C4 L1; numconst; img_lia)).
constructor.
- img_exact LY.
- img_exact IMG.
- splits; assumption.
- split; assumption.
- splits; try assumption; img_lia.
- img_exact Hnr.
- split; assumption.
- split; [img_try (img_exact V) | img_try (img_exact PR)].
-
rewrite restrict_mkst_fx. unfold YF2r.SS0, YF2r.SR0, sr_set. cbn [bv_eqb]. unfold YF2r.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ repeat (img_apply regs_ok_pin; [| img_try (intros XX; discriminate) |]); [img_try (img_apply regs_ok_Ereg) | ..]; cbn [sv_denot].
* change (ew _ 32) with (Z_to_bv 64 p). rewrite R11. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* change (ew _ 33) with (Z_to_bv 64 cur). rewrite R12. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* change (ew _ 34) with (Z_to_bv 64 nr). rewrite R13. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* change (ew _ 35) with (Z_to_bv 64 lim). rewrite R14. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. unfold YF2r.REG0, YF2r.R_CUR. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (ew _ 33) with (Z_to_bv 64 cur). rewrite unsigned_lit_small by img_exact Ucur.
split; [img_lia|]. split; [img_try (clear - C1 C4 L1; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom8 _ _ _ _ 36%nat h); [img_refl | img_try (clear - G1; numconst; img_lia) | img_try (rewrite Z.add_0_r; img_exact V)].
+ img_apply pairwise_disjoint_of_extents. unfold YF2r.REG0, YF2r.R_CUR, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. img_exact (conj I I).
+ split; [|img_try (split; img_exact I)]. cbn [YF2r.FFL f_atoms atoms_ok]. numconst.
split. { img_apply (afact_intro _ 32%nat p); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 4) with 16; img_exact P2) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro _ 33%nat cur); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 3) with 8; img_exact C2) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro _ 34%nat nr); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro _ 35%nat lim); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 3) with 8; img_exact L2) | img_try (clear; img_lia)]. }
split; [|img_try (img_exact I)]. { img_apply (afact_intro _ 36%nat h); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 12) with 4096; img_exact G2) | img_try (clear; img_lia)]. }
Qed.
Definition at_XGf (regs : bvmap 5 word) (mem : word -> option byte) (nrf : Z) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat',
c' = mkCfg (mkst regs' (w64 (0x33e90 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md) /\
(forall r : bv 5, In r YF2r.SREGS -> getr regs' r = getr regs r) /\
getr regs' 12 = w64 lim /\ getr regs' 13 = w64 nrf /\
(forall x, mem' x = mem x).
Theorem gloop : forall hs cur nr regs mem mat, hs <> [] -> stL cur nr hs regs mem ->
SRr tfxsegs W (mkCfg (mkst regs (w64 (0x33e64 + D_150)) mem (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(at_XGf regs mem (scan p nr hs)).
Proof.
induction hs as [|h hs IH]; intros cur nr regs mem mat NE ST; [img_try (exfalso; img_exact (NE eq_refl))|].
pose proof (seed_L cur nr h hs regs mem ST) as FH. pose proof ST as (R11 & R12 & R13 & R14 & C1 & C2 & C3 & Hnr & CELLS). cbn [length] in C3.
eapply SRr_bind; [img_try (img_exact (segGL W ly regs mem md p cur nr lim h mat FH))|]. intros W' c' _ POST.
unfold YF2r.postL in POST. destruct hs as [|h2 hs2].
-   cbn [length] in C3. replace (cur + 8 <? lim) with false in POST by (img_try (symmetry; img_apply Z.ltb_ge; img_lia)).
destruct POST as (-> & _ & regs' & mem' & mat' & -> & SR & A12 & A13 & MQ). img_apply SRr_ret.
split; [img_refl|]. exists regs', mem', mat'. splits; [img_refl | img_try (img_exact SR) | img_try (rewrite A12; f_equal; img_lia) | img_try (rewrite A13; img_refl) | img_try (intros x; img_exact (MQ x ltac:(intros [])))].
- replace (cur + 8 <? lim) with true in POST by (img_try (symmetry; img_apply Z.ltb_lt; cbn [length] in C3; img_lia)).
destruct POST as (-> & _ & regs' & mem' & mat' & -> & SR & A12 & A13 & MQ).
assert (MQ' : forall x, mem' x = mem x) by (img_try (intros x; img_exact (MQ x ltac:(intros [])))).
rewrite scan_cons.
eapply SRr_mono; [img_try (img_apply (IH (cur + 8) (nr_step p nr h) regs' mem' mat' ltac:(discriminate)))|].
+ destruct (CELLS 0%nat h eq_refl) as (_ & _ & G1 & _). unfold stL.
pose proof (nr_step_range p nr h Hnr ltac:(img_try (clear - G1; numconst; img_lia))) as NR'.
refine (conj _ (conj A12 (conj A13 (conj _ (conj _ (conj _ (conj _ (conj NR' _)))))))).
{ rewrite (SR 11%bv ltac:(img_try (cbn; tauto))). img_exact R11. }
{ rewrite (SR 14%bv ltac:(img_try (cbn; tauto))). img_exact R14. }
{ img_lia. }
{ clear - C2. replace (cur + 8) with (cur + 1 * 8) by img_lia. rewrite Z_mod_plus_full. img_exact C2. }
{ cbn [length] in *. img_lia. }
intros j h' Hj. destruct (CELLS (S j) h' Hj) as (V & PR & G1' & G2'). rewrite Nat2Z.inj_succ in V, PR.
replace (cur + 8 * Z.succ (Z.of_nat j)) with (cur + 8 + 8 * Z.of_nat j) in V, PR by img_lia.
splits; [| | img_try (img_exact (proj1 G1')) | img_try (img_exact (proj2 G1')) | img_try (img_exact G2')].
* eapply val_mem_frame; [| img_try (img_exact V)]. intros x _. img_exact (MQ' _).
* intros a Ha. pose proof (PR a Ha) as X. unfold apresent in *. rewrite (MQ' _). img_exact X.
+ intros W'' c'' _ (-> & regs'' & mem'' & mat'' & -> & SR' & B12 & B13 & MQ''). split; [img_refl|]. exists regs'', mem'', mat''.
splits; [img_refl | img_try (intros r Hr; rewrite (SR' r Hr); img_exact (SR r Hr)) | img_try (img_exact B12) | img_try (img_exact B13) | img_try (intros x; rewrite (MQ'' x); img_exact (MQ' x))].
Qed.
End c.
End b.
