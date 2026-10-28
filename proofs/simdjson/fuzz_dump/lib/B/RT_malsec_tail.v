(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma set_mem_nretA_zero : forall (ms0 : machine_state) (m : word -> option byte) (P len : word),
  (forall a, apply_zeros m [(P, len)] a = m a) ->
  set_mem (nretA ms0 (mkEffect P [] [(P, len)])) m = nretA (set_mem ms0 m) (mkEffect P [] [(P, len)]).
Proof.
  intros ms0 m P len Hz. unfold nretA, advance_past_svc, apply_effect, set_mem. cbn.
  f_equal. symmetry. apply functional_extensionality. intros a. exact (Hz a).
Qed.

From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_state RT_rep RT_sys_stmt RT_malsec_state.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Lemma page_base_lt : forall a : word, bv_unsigned a < bv_unsigned (page_base a) + 4096.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)).
  rewrite unsigned_lit by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]). lia.
Qed.

Lemma map_range_visible : forall (Σ : rtsA) P n mo (a : word), layout_ok (lay Σ) -> ARTM_A (sgΣ Σ P n) mo -> sgrant_ok Σ P (smsz n) ->
  P <= bv_unsigned a < P + smsz n -> HID (rtA_allow Σ) mo a = false.
Proof.
  intros Σ P n mo a HL HA (HG & Hap) Ha. pose proof HL as ((Hsp1 & Hsp2) & _). unfold sp_window_hi in Hsp2. pose proof HA as (_ & _ & _ & _ & (_ & _ & _ & _ & Hcf & _)).
  unfold grant_ok, l_ACEIL, STACK_WIN in HG. destruct HG as (G1 & G2 & G3 & _).
  pose proof (ART_wf' := tt). clear ART_wf'.
  unfold HID. apply orb_false_iff. split.
  - unfold mkH. apply andb_false_iff. left.
    destruct (page_in_ranges (page_base a) (m_vm_lazy mo)) eqn:Hp; [|reflexivity]. exfalso.
    unfold page_in_ranges in Hp. apply existsb_exists in Hp as (r & Hr & Hrp).
    apply andb_prop in Hrp as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2.
    pose proof (page_base_le a). pose proof (page_base_lt a). unfold page_size in R2.
    assert (Hc : BackingAlgebra.covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) (bv_unsigned a) = true).
    { rewrite BackingAlgebra.covered_app. apply orb_true_iff. right. unfold BackingAlgebra.covered. apply existsb_exists.
      exists r. split; [exact Hr|]. unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S.
      apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    pose proof (Hcf _ Hc) as HC0. cbn [lay sgΣ] in HC0. unfold BackingAlgebra.covered in HC0. apply existsb_exists in HC0 as (e & He & Hex).
    assert (HeR : In e (rt_maps Σ)) by (unfold rt_maps; apply in_or_app; right; exact He).
    pose proof (proj1 (Forall_forall _ _) Hap e HeR) as D. unfold apart in D.
    unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S in Hex.
    apply andb_prop in Hex as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. clear - D X1 X2 Ha. lia.
  - apply Z.leb_gt. lia.
Qed.

Lemma revealed_zero_range : forall A A' mo ms0 ms1 ms (P len : Z), 0 <= P -> 0 <= len -> P + len < 2 ^ 64 ->
  ms0 = nretA ms1 (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 len)]) ->
  revealed A A' mo ms0 ms ->
  (forall a : word, P <= bv_unsigned a < P + len -> HID A mo a = false) ->
  forall a : word, apply_zeros (ms_mem ms) [(Z_to_bv 64 P, Z_to_bv 64 len)] a = ms_mem ms a.
Proof.
  intros A A' mo ms0 ms1 ms P len H0 H1 H2 E (_ & Hv & _) Hvis a. unfold apply_zeros.
  destruct (zeros_cover [(Z_to_bv 64 P, Z_to_bv 64 len)] a) eqn:Hz; [|reflexivity].
  unfold zeros_cover in Hz. cbn [existsb fst snd] in Hz. rewrite orb_false_r in Hz.
  rewrite !unsigned_lit in Hz by lia. apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
  rewrite (Hv a (Hvis a ltac:(lia))). subst ms0. unfold nretA, advance_past_svc, apply_effect. cbn [ms_mem eff_unmaps eff_zeros eff_copies eff_writes].
  unfold apply_zeros at 1. cbn [apply_unmaps apply_copies apply_writes].
  unfold zeros_cover. cbn [existsb fst snd]. rewrite !unsigned_lit by lia.
  replace ((P <=? bv_unsigned a) && (bv_unsigned a <? P + len)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma nret_revealed : forall A A' mo ms0 ms1 ms (P len : Z), 0 <= P -> 0 <= len -> P + len < 2 ^ 64 ->
  ms0 = nretA ms1 (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 len)]) ->
  revealed A A' mo ms0 ms ->
  (forall a : word, P <= bv_unsigned a < P + len -> HID A mo a = false) ->
  ms = nretA (set_mem ms1 (ms_mem ms)) (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 len)]).
Proof.
  intros A A' mo ms0 ms1 ms P len H0 H1 H2 E Hrev Hvis.
  pose proof (revealed_zero_range A A' mo ms0 ms1 ms P len H0 H1 H2 E Hrev Hvis) as HZ.
  rewrite <- (set_mem_nretA_zero ms1 (ms_mem ms) _ _ HZ). destruct Hrev as (E1 & _). rewrite E1 at 1. rewrite E. reflexivity.
Qed.
