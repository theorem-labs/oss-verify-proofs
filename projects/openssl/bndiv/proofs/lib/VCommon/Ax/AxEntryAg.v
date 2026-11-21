(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the agreement lemmas take the rseq flag and cover the new entry-block variables for execfn, the stack top, the draw and the launch auxv (ag_execfn, ag_top, ag_la, entry_xstrvar); placeholder comments dropped). *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxEntryRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma to_Z_of_Z_small (z : Z) : 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). exact H. Qed.

Lemma entry_var_big (z : Z) : 2 ^ 40 <= z < 2 ^ 63 -> entry_var (of_Z z) = true.
Proof.
  intros H. unfold entry_var. apply orb_true_iff. right. apply leb_spec.
  rewrite (to_Z_of_Z_small z) by lia. change (to_Z 1099511627776) with (2 ^ 40). lia.
Qed.

Lemma entry_lenvar (k : Z) : 0 <= k < 2 ^ 20 -> entry_var (lenvar k) = true.
Proof. intros H. apply entry_var_big. lia. Qed.
Lemma entry_strvar (k j : Z) : 0 <= k < 2 ^ 20 -> 0 <= j < 2 ^ 17 -> entry_var (strvar k j) = true.
Proof. intros Hk Hj. apply entry_var_big. nia. Qed.
Lemma entry_elenvar (k : Z) : 0 <= k < 2 ^ 20 -> entry_var (elenvar k) = true.
Proof. intros H. apply entry_var_big. lia. Qed.
Lemma entry_estrvar (k j : Z) : 0 <= k < 2 ^ 20 -> 0 <= j < 2 ^ 17 -> entry_var (estrvar k j) = true.
Proof. intros Hk Hj. apply entry_var_big. nia. Qed.

Lemma entry_x0 : entry_var v_x0 = true. Proof. reflexivity. Qed.
Lemma entry_x1 : entry_var v_x1 = true. Proof. reflexivity. Qed.
Lemma entry_x2 : entry_var v_x2 = true. Proof. reflexivity. Qed.
Lemma entry_x3 : entry_var v_x3 = true. Proof. reflexivity. Qed.
Lemma entry_b : entry_var v_b = true. Proof. reflexivity. Qed.
Lemma entry_r0 : entry_var v_r0 = true. Proof. reflexivity. Qed.
Lemma entry_r1 : entry_var v_r1 = true. Proof. reflexivity. Qed.
Lemma entry_hw : entry_var v_hw = true. Proof. reflexivity. Qed.
Lemma entry_uid : entry_var v_uid = true. Proof. reflexivity. Qed.
Lemma entry_argc : entry_var v_argc = true. Proof. reflexivity. Qed.
Lemma entry_envc : entry_var v_envc = true. Proof. reflexivity. Qed.
Lemma entry_ta : entry_var v_ta = true. Proof. reflexivity. Qed.
Lemma entry_te : entry_var v_te = true. Proof. reflexivity. Qed.
Lemma entry_q : entry_var v_q = true. Proof. reflexivity. Qed.

Lemma entry_xstrvar (j : Z) : 0 <= j < 2 ^ 17 -> entry_var (xstrvar j) = true.
Proof. intros Hj. apply entry_var_big. lia. Qed.

Lemma dec_strs_agree (ρ ρ' : valuation) (cnt : int) (len : Z -> int) (bytev : Z -> Z -> int) :
  ρ' cnt = ρ cnt ->
  (forall k, 0 <= k < ρ cnt -> ρ' (len k) = ρ (len k) /\ forall j, 0 <= j < ρ (len k) -> ρ' (bytev k j) = ρ (bytev k j)) ->
  dec_strs ρ' cnt len bytev = dec_strs ρ cnt len bytev.
Proof.
  intros Hc H. unfold dec_strs. rewrite Hc. apply map_ext_in. intros k Hk. apply in_seq in Hk.
  destruct (H (Z.of_nat k) ltac:(lia)) as [Hl Hb]. rewrite Hl. apply map_ext_in. intros j Hj. apply in_seq in Hj.
  rewrite (Hb (Z.of_nat j)) by lia. reflexivity.
Qed.

Section Agree.
Local Set Default Proof Using "All".
Variable r : bool.
Variables ρ ρ' : valuation.
Hypothesis Hag : forall x : int, entry_var x = true -> ρ' x = ρ x.
Hypothesis HF : eb_facts r ρ.

Lemma ag_argc : ρ' v_argc = ρ v_argc. Proof. apply Hag. reflexivity. Qed.
Lemma ag_envc : ρ' v_envc = ρ v_envc. Proof. apply Hag. reflexivity. Qed.

Lemma ag_sp : sp_val ρ' = sp_val ρ.
Proof. unfold sp_val, sp_terms. cbn [teval]. rewrite !Hag by reflexivity. reflexivity. Qed.

Lemma ag_argv : dec_argv ρ' = dec_argv ρ.
Proof.
  destruct HF as (Hc & _ & Ha & _). unfold dec_argv. apply dec_strs_agree; [exact ag_argc|].
  intros k Hk. destruct (Ha k Hk) as [Hl _]. split; [apply Hag, entry_lenvar; lia|].
  intros j Hj. apply Hag, entry_strvar; lia.
Qed.

Lemma ag_envp : dec_envp ρ' = dec_envp ρ.
Proof.
  destruct HF as (_ & Hc & _ & He & _). unfold dec_envp. apply dec_strs_agree; [exact ag_envc|].
  intros k Hk. destruct (He k Hk) as [Hl _]. split; [apply Hag, entry_elenvar; lia|].
  intros j Hj. apply Hag, entry_estrvar; lia.
Qed.

Lemma ag_execfn : dec_execfn ρ' = dec_execfn ρ.
Proof.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & (Hxl & Hxb) & _). unfold dec_execfn.
  rewrite (Hag v_xl) by reflexivity. apply map_ext_in. intros j Hj. apply in_seq in Hj.
  rewrite (Hag (xstrvar (Z.of_nat j))) by (apply entry_xstrvar; lia). reflexivity.
Qed.

Lemma ag_top : dec_top r ρ' = dec_top r ρ.
Proof. unfold dec_top, str_off. rewrite ag_sp, !Hag by reflexivity. reflexivity. Qed.

Lemma ag_draw : dec_draw r ρ' = dec_draw r ρ.
Proof.
  unfold dec_draw. rewrite ag_top. f_equal. unfold dec_random. rewrite (Hag v_r0), (Hag v_r1) by reflexivity. reflexivity.
Qed.

Lemma ag_la : dec_la r ρ' = dec_la r ρ.
Proof. unfold dec_la. rewrite !Hag by reflexivity. reflexivity. Qed.

Lemma ag_image (ph : PhdrInfo) : eb_image r ph ρ' = eb_image r ph ρ.
Proof. unfold eb_image. rewrite ag_sp, ag_top, ag_argv, ag_envp, ag_execfn, ag_draw, ag_la, !Hag by reflexivity. reflexivity. Qed.

Lemma ag_facts : eb_facts r ρ'.
Proof.
  pose proof HF as (Hc & He & Ha & Hv & Hta & Hte & Hpar & Hg & (Hxl & Hxb) & Hr0 & Hr1 & Hu & Hh & Hgid & Hent & Hvd & Hmss & Hs1 & Hs2 & Hs3).
  unfold eb_facts. rewrite ag_argc, ag_envc, ag_argv, ag_envp, ag_sp, ag_top, !(Hag v_ta), !(Hag v_te), !(Hag v_par),
    !(Hag v_g), !(Hag v_xl), !(Hag v_r0), !(Hag v_r1), !(Hag v_uid), !(Hag v_hw), !(Hag v_gid), !(Hag v_ent),
    !(Hag v_vd), !(Hag v_mss) by reflexivity.
  split; [exact Hc|]. split; [exact He|].
  split.
  { intros k Hk. destruct (Ha k Hk) as [Hl Hb]. rewrite (Hag (lenvar k)) by (apply entry_lenvar; lia). split; [exact Hl|].
    intros j Hj. rewrite (Hag (strvar k j)) by (apply entry_strvar; lia). exact (Hb j Hj). }
  split.
  { intros k Hk. destruct (Hv k Hk) as [Hl Hb]. rewrite (Hag (elenvar k)) by (apply entry_elenvar; lia). split; [exact Hl|].
    intros j Hj. rewrite (Hag (estrvar k j)) by (apply entry_estrvar; lia). exact (Hb j Hj). }
  split; [exact Hta|]. split; [exact Hte|]. split; [exact Hpar|]. split; [exact Hg|].
  split; [split; [exact Hxl|]; intros j Hj; rewrite (Hag (xstrvar j)) by (apply entry_xstrvar; lia); exact (Hxb j Hj)|].
  exact (conj Hr0 (conj Hr1 (conj Hu (conj Hh (conj Hgid (conj Hent (conj Hvd (conj Hmss (conj Hs1 (conj Hs2 Hs3)))))))))).
Qed.

End Agree.

Theorem eb_rel_agree (r : bool) (ph : PhdrInfo) (ρ ρ' : valuation) (m : word -> option byte) (b n : Z) :
  (forall x : int, entry_var x = true -> ρ' x = ρ x) -> eb_rel r ph ρ m b n -> eb_rel r ph ρ' m b n.
Proof.
  intros Hag (HF & Hb & Hn & Hm). unfold eb_rel.
  rewrite (ag_image r ρ ρ' Hag HF ph), (ag_sp r ρ ρ' Hag HF).
  split; [exact (ag_facts r ρ ρ' Hag HF)|]. split; [exact Hb|]. split; [exact Hn | exact Hm].
Qed.

Theorem eb_rel_frame (r : bool) (ph : PhdrInfo) (ρ : valuation) (m m' : word -> option byte) (b n : Z) :
  (forall z, 0 <= z < n -> m' (Z_to_bv 64 (b + z)) = m (Z_to_bv 64 (b + z))) -> eb_rel r ph ρ m b n -> eb_rel r ph ρ m' b n.
Proof.
  intros Hfr (HF & Hb & Hn & Hm). split; [exact HF|]. split; [exact Hb|]. split; [exact Hn|].
  intros z Hz. rewrite Hfr by lia. exact (Hm z Hz).
Qed.

Lemma eb_rel_facts (r : bool) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (b n : Z) :
  eb_rel r ph ρ m b n -> eb_facts r ρ.
Proof. intros (HF & _). exact HF. Qed.

Lemma eb_rel_base (r : bool) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (b n : Z) : eb_rel r ph ρ m b n -> b = sp_val ρ.
Proof. intros (_ & Hb & _). exact Hb. Qed.

Lemma eb_rel_size {r : bool} (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (b n : Z) :
  eb_rel r ph ρ m b n -> Z.of_nat (length (eb_image r ph ρ)) <= n.
Proof. intros (_ & _ & Hn & _). exact Hn. Qed.

Lemma eb_rel_byte {r : bool} (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (b n : Z) :
  eb_rel r ph ρ m b n -> forall z, 0 <= z < Z.of_nat (length (eb_image r ph ρ)) ->
  m (Z_to_bv 64 (b + z)) = Some (nth (Z.to_nat z) (eb_image r ph ρ) (Z_to_bv 8 0)).
Proof. intros (_ & _ & _ & Hm). exact Hm. Qed.

Lemma eb_rel_len {r : bool} (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (b n : Z) :
  eb_rel r ph ρ m b n -> forall z, 0 <= z < Z.of_nat (length (eb_image r ph ρ)) -> m (Z_to_bv 64 (b + z)) <> None.
Proof. intros H z Hz. rewrite (eb_rel_byte ph ρ m b n H z Hz). discriminate. Qed.
