(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG01 YG0h YG0d YF8z YF90 YF93 YC1d YD16 YCcx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition TraBx (xs : list (list Z)) : asyms := {|
as_code := as_code TraB; as_inst := as_inst TraB; as_gp := as_gp TraB; as_tp := as_tp TraB; as_tsd := as_tsd TraB;
as_shadow_cell := as_shadow_cell TraB; as_uar_cell := as_uar_cell TraB; as_got_shadow := as_got_shadow TraB; as_got_uar := as_got_uar TraB;
as_errno := as_errno TraB; as_depot := as_depot TraB; as_store := as_store TraB;
as_ialloc_lo := as_ialloc_lo TraB; as_ialloc_hi := as_ialloc_hi TraB; as_ialloc_w := as_ialloc_w TraB; as_ialloc_flag := as_ialloc_flag TraB;
as_oom_byte := as_oom_byte TraB; as_dhash := as_dhash TraB; as_const := as_const TraB; as_junk := as_junk TraB;
as_owned_static := as_owned_static TraB; as_zero_shadow := as_zero_shadow TraB;
as_universe := Tra_universe ++ xs |}.
Lemma TraBx_ok : forall xs, asyms_ok (TraBx xs).
Proof. intros xs. destruct TraB_ok as [H1 H2 H3 H4 H5 H6]. constructor; [exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6]. Qed.
Theorem TraBx_syms : forall xs, universe_ok (Tra_universe ++ xs) -> TraSyms (TraBx xs).
Proof.
intros xs HU.
destruct TraB_syms as [S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 S18 S19 S20 S21 S22 S23].
constructor; [exact S1 | exact S2 | exact S3 | exact S4 | exact S5 | exact S6 | exact S7 | exact S8 | exact S9 | exact S10 | exact S11 | exact S12 | exact S13
| exact (TraBx_ok xs) | exact S15 | exact S16 | exact S17 | exact S18 | exact S19 | exact S20 | exact HU | | exact S23].
intros t Ht. cbn [as_universe TraBx]. apply in_or_app. left. exact (S22 t Ht).
Qed.
Definition run_k1 (n : Z) : list Z := rrfc_trace (pc_malloc_ra0 Tra_code) RRFC_malloc_ra n.
Definition run_k2 (n : Z) : list Z := rrfc_trace (pc_free_ra0 Tra_code) RRFC_free_ra n.
Definition run_xs (n : Z) : list (list Z) :=
if 4096 <=? n then
let xs1 := if memZL (run_k1 n) Tra_universe then [] else [run_k1 n] in
if memZL (run_k2 n) (Tra_universe ++ xs1) then xs1 else xs1 ++ [run_k2 n]
else [].
Lemma NoDup_snoc : forall (A : Type) (l : list A) (t : A), NoDup l -> ~ In t l -> NoDup (l ++ [t]).
Proof.
intros A l t. induction l as [|a l IH]; intros HN Hn; cbn; [constructor; [intros [] | constructor]|].
inversion HN as [|? ? Ha HN']; subst. constructor.
- intros Hin. apply in_app_or in Hin as [Hin | [<- | []]]; [exact (Ha Hin) | apply Hn; left; reflexivity].
- apply IH; [exact HN' | intros Hin; apply Hn; right; exact Hin].
Qed.
Lemma rrfc_trace_len : forall pc0 site n, (length (rrfc_trace pc0 site n) <= kUnwindMax)%nat.
Proof. intros. unfold rrfc_trace, kUnwindMax. destruct (n =? pc0); cbn; lia. Qed.
Lemma universe_ok_snoc : forall U t, universe_ok U -> Z.of_nat (length U) + 1 <= DEPOT_MAX -> (length t <= kUnwindMax)%nat -> ~ In t U -> universe_ok (U ++ [t]).
Proof.
intros U t (H1 & H2 & H3) Hl Ht Hn. split; [rewrite length_app; cbn [length]; lia|]. split.
- apply Forall_app. split; [exact H2 | constructor; [exact Ht | constructor]].
- apply NoDup_snoc; assumption.
Qed.
Lemma Tra_universe_room : Z.of_nat (length Tra_universe) + 2 <= DEPOT_MAX.
Proof. unfold DEPOT_MAX. vm_compute. discriminate. Qed.
Theorem run_universe_ok : forall n, universe_ok (Tra_universe ++ run_xs n).
Proof.
intros n. pose proof Tra_universe_ok as HU. pose proof Tra_universe_room as HR. unfold run_xs.
destruct (4096 <=? n); [| rewrite app_nil_r; exact HU].
cbv zeta. destruct (memZL (run_k1 n) Tra_universe) eqn:M1.
- rewrite app_nil_r. destruct (memZL (run_k2 n) Tra_universe) eqn:M2; [rewrite app_nil_r; exact HU|].
cbn [app]. apply universe_ok_snoc; [exact HU | lia | apply rrfc_trace_len | apply memZL_false; exact M2].
- assert (HU1 : universe_ok (Tra_universe ++ [run_k1 n])) by (apply universe_ok_snoc; [exact HU | lia | apply rrfc_trace_len | apply memZL_false; exact M1]).
destruct (memZL (run_k2 n) (Tra_universe ++ [run_k1 n])) eqn:M2; [exact HU1|].
rewrite app_assoc. apply universe_ok_snoc; [exact HU1 | rewrite length_app; cbn [length]; lia | apply rrfc_trace_len | apply memZL_false; exact M2].
Qed.
Theorem run_rrfc_universe : forall n, rrfc_universe (TraBx (run_xs n)) n.
Proof.
intros n Hn. cbn [as_universe as_code TraBx TraB]. fold (run_k1 n). fold (run_k2 n). unfold run_xs.
replace (4096 <=? n) with true by (symmetry; apply Z.leb_le; exact Hn). cbv zeta.
destruct (memZL (run_k1 n) Tra_universe) eqn:M1.
- rewrite app_nil_r. destruct (memZL (run_k2 n) Tra_universe) eqn:M2.
+ rewrite app_nil_r. split; apply memZL_In; assumption.
+ split; [apply in_or_app; left; apply memZL_In; exact M1 | apply in_or_app; right; left; reflexivity].
- destruct (memZL (run_k2 n) (Tra_universe ++ [run_k1 n])) eqn:M2.
+ split; [apply in_or_app; right; left; reflexivity | apply memZL_In; exact M2].
+ rewrite app_assoc. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity | apply in_or_app; right; left; reflexivity].
Qed.
