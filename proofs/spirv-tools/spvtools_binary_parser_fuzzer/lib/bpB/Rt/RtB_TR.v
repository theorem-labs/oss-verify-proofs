(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsIface.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition tr_prefixes (t : list Z) : list (list Z) := map (fun j => firstn j t) (seq 1 (length t)).
Definition tr_close (L : list (list Z)) : list (list Z) := flat_map tr_prefixes L.
Definition tr_dedup (L : list (list Z)) : list (list Z) := nodup (list_eq_dec Z.eq_dec) L.

Lemma tr_prefixes_in : forall (t : list Z) j, (1 <= j)%nat -> t <> [] -> In (firstn j t) (tr_prefixes t).
Proof.
  intros t j J NE. unfold tr_prefixes. apply in_map_iff.
  destruct (Nat.le_gt_cases j (length t)) as [LE|GT].
  - exists j. split; [reflexivity|]. apply in_seq. lia.
  - exists (length t). split.
    + rewrite firstn_all. rewrite firstn_all2 by lia. reflexivity.
    + apply in_seq. destruct t as [|x t]; [congruence| cbn; lia].
Qed.

Lemma tr_close_in : forall L t j, In t L -> (1 <= j)%nat -> t <> [] -> In (firstn j t) (tr_close L).
Proof. intros L t j IN J NE. unfold tr_close. apply in_flat_map. exists t. split; [exact IN| exact (tr_prefixes_in t j J NE)]. Qed.

Lemma trace_ok_of_full : forall L pc0 t, In (pc0 :: t) L -> ~ In pc0 t -> trace_ok (tr_dedup (tr_close L)) pc0 t.
Proof.
  intros L pc0 t IN NI. split; [exact NI|]. intros j J. unfold tr_dedup. apply nodup_In.
  apply tr_close_in; [exact IN| exact J| discriminate].
Qed.

Definition DRV_MALLOC_RAS : list Z := [0xe8448; 0xe849c; 0xe8728].
Definition DRV_FREE_RAS   : list Z := [0xe84c0; 0xe85f0; 0xe87bc].

Definition TR_base : list (list Z) :=
  OPNEW_TRACE :: map (fun r => [APC0_MALLOC; r]) DRV_MALLOC_RAS ++ map (fun r => [APC0_FREE; r]) DRV_FREE_RAS.

Definition TR_bp (LIB : list (list Z)) : list (list Z) := tr_dedup (tr_close (TR_base ++ LIB)).

Lemma TR_bp_len_le : forall LIB, Nat.leb (length (TR_bp LIB)) 1000 = true -> (length (TR_bp LIB) <= 1000)%nat.
Proof. intros LIB E. apply Nat.leb_le. exact E. Qed.

Lemma TR_bp_op : forall LIB, trace_ok (TR_bp LIB) APC0_MALLOC [ARA_OPNEW].
Proof.
  intros LIB. apply trace_ok_of_full; [apply in_or_app; left; left; reflexivity|].
  unfold APC0_MALLOC, ARA_OPNEW. cbn. lia.
Qed.

Lemma TR_bp_drv : forall LIB,
       trace_ok (TR_bp LIB) APC0_MALLOC [0xe8448]
    /\ trace_ok (TR_bp LIB) APC0_MALLOC [0xe849c]
    /\ trace_ok (TR_bp LIB) APC0_FREE [0xe84c0]
    /\ trace_ok (TR_bp LIB) APC0_FREE [0xe85f0]
    /\ trace_ok (TR_bp LIB) APC0_MALLOC [0xe8728]
    /\ trace_ok (TR_bp LIB) APC0_FREE [0xe87bc].
Proof.
  intros LIB. unfold APC0_MALLOC, APC0_FREE.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); (apply trace_ok_of_full; [apply in_or_app; left; cbn; tauto| cbn; lia]).
Qed.

Lemma TR_bp_lib : forall LIB pc0 t, In (pc0 :: t) LIB -> ~ In pc0 t -> trace_ok (TR_bp LIB) pc0 t.
Proof. intros LIB pc0 t IN NI. apply trace_ok_of_full; [apply in_or_app; right; exact IN| exact NI]. Qed.

Lemma TR_bp_pf : forall LIB PF ra CH,
    Forall (fun pp : Z * list Z => In (fst pp :: snd pp ++ ra :: map snd CH) LIB /\ ~ In (fst pp) (snd pp ++ ra :: map snd CH)) PF ->
    pf_ok (TR_bp LIB) PF ra CH.
Proof.
  intros LIB PF ra CH ALL. unfold pf_ok. eapply Forall_impl; [| exact ALL].
  intros [pc0 pre] [IN NI]. exact (TR_bp_lib LIB pc0 (pre ++ ra :: map snd CH) IN NI).
Qed.
