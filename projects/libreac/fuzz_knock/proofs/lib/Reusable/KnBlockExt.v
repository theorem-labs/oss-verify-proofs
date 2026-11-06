(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): the StackDepot nodes block (NB) and store block (SB) extents of libreac/fuzz_knock in
   the shared ASan kernel's own encoding. knock records no stack trace before main (DepotCfg.depot_has_trace = false), so
   NB and SB are mapped only by the first StackDepot Put; until then the layout holds the "not yet mapped" sentinel
   ly_NB ly = 0 / ly_SB ly = 0, and the kernel's lists hold the empty extent (4096, 0) at the blocks' positions 4 / 5 of
   owned_extents (and so of static_extents). nb_ext / sb_ext ARE those list entries, so a fact stated with them holds at
   whatever layout the state has: before the first Put (empty extent) and after it (the mapped block, nb_ext_set /
   sb_ext_set). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0f.
Import ListNotations.
Open Scope Z_scope.
Definition nb_ext (ly : alayout) : Z * Z := nth 4 (owned_extents ly) (0, 0).
Definition sb_ext (ly : alayout) : Z * Z := nth 5 (owned_extents ly) (0, 0).
Lemma nb_ext_eq : forall ly, nb_ext ly = if (ly_NB ly =? 0)%Z then (4096, 0) else (ly_NB ly, kNodesBlockSize).
Proof. intros ly. reflexivity. Qed.
Lemma sb_ext_eq : forall ly, sb_ext ly = if (ly_SB ly =? 0)%Z then (4096, 0) else (ly_SB ly, kStoreBlockSize).
Proof. intros ly. reflexivity. Qed.
Lemma nb_ext_set : forall ly, ly_NB ly <> 0 -> nb_ext ly = (ly_NB ly, kNodesBlockSize).
Proof. intros ly H. rewrite nb_ext_eq, (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma sb_ext_set : forall ly, ly_SB ly <> 0 -> sb_ext ly = (ly_SB ly, kStoreBlockSize).
Proof. intros ly H. rewrite sb_ext_eq, (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma nb_ext_unset : forall ly, ly_NB ly = 0 -> nb_ext ly = (4096, 0).
Proof. intros ly H. rewrite nb_ext_eq, H. reflexivity. Qed.
Lemma sb_ext_unset : forall ly, ly_SB ly = 0 -> sb_ext ly = (4096, 0).
Proof. intros ly H. rewrite sb_ext_eq, H. reflexivity. Qed.
(* The positional picks the walk files use: nth_error of owned_extents / static_extents at 4 and 5. *)
Lemma nb_ext_nth : forall ly, nth_error (owned_extents ly) 4 = Some (nb_ext ly).
Proof. intros ly. reflexivity. Qed.
Lemma sb_ext_nth : forall ly, nth_error (owned_extents ly) 5 = Some (sb_ext ly).
Proof. intros ly. reflexivity. Qed.
Lemma nb_ext_nth_st : forall ly, nth_error (static_extents ly) 4 = Some (nb_ext ly).
Proof. intros ly. reflexivity. Qed.
Lemma sb_ext_nth_st : forall ly, nth_error (static_extents ly) 5 = Some (sb_ext ly).
Proof. intros ly. reflexivity. Qed.
Lemma nb_ext_len : forall ly, 0 <= snd (nb_ext ly) <= kNodesBlockSize.
Proof. intros ly. rewrite nb_ext_eq. destruct (ly_NB ly =? 0)%Z; cbn [snd]; unfold kNodesBlockSize; lia. Qed.
Lemma sb_ext_len : forall ly, 0 <= snd (sb_ext ly) <= kStoreBlockSize.
Proof. intros ly. rewrite sb_ext_eq. destruct (ly_SB ly =? 0)%Z; cbn [snd]; unfold kStoreBlockSize; lia. Qed.
Lemma nb_ext_pair : forall ly, (fst (nb_ext ly), snd (nb_ext ly)) = nb_ext ly.
Proof. intros ly. destruct (nb_ext ly); reflexivity. Qed.
Lemma sb_ext_pair : forall ly, (fst (sb_ext ly), snd (sb_ext ly)) = sb_ext ly.
Proof. intros ly. destruct (sb_ext ly); reflexivity. Qed.
(* The depot zone at layout l: the static depot zone [zlo, zhi) plus NB and SB by the extents above. zlo / zhi are
   image values, so they are arguments here; each image names its own (asan: AD3j.tfib_dzone_lo / tfib_dzone_hi). *)
Definition DZONE_at (zlo zhi : Z) (l : alayout) (a : Z) : Prop :=
(zlo <= a < zhi) \/ (fst (nb_ext l) <= a < fst (nb_ext l) + snd (nb_ext l)) \/ (fst (sb_ext l) <= a < fst (sb_ext l) + snd (sb_ext l)).
