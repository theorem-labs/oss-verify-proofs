(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocIface MallocInv_defs MallocInv_hints MallocInv_sc3.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition grp_cap (sc : Z) : Z :=
  if size_class sc <=? 127 then 2^16 else Z.min (2^20) (512 * size_class sc + 4111).

Lemma grp_cap_le : forall sc, 1 <= size_class sc -> grp_cap sc <= 2^20.
Proof. intros sc H. unfold grp_cap. destruct (size_class sc <=? 127); lia. Qed.

Lemma grp_cap_small : forall sc, size_class sc <= 127 -> grp_cap sc = 2^16.
Proof. intros sc H. unfold grp_cap. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma grp_cap_big : forall sc, 127 < size_class sc -> grp_cap sc = Z.min (2^20) (512 * size_class sc + 4111).
Proof. intros sc H. unfold grp_cap. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma grp_cap_pos : forall sc, 1 <= size_class sc -> 4096 < grp_cap sc.
Proof. intros sc H. unfold grp_cap. destruct (size_class sc <=? 127) eqn:E; [lia | apply Z.leb_gt in E; lia]. Qed.

(* [comment removed for export] *)
Lemma grp_cap_ge : forall sc, 2^16 <= grp_cap sc.
Proof. intros sc. unfold grp_cap. destruct (size_class sc <=? 127) eqn:E; [lia | apply Z.leb_gt in E; lia]. Qed.

Lemma grp_cap_nest : forall sc j, size_class j <= 127 -> grp_cap j <= grp_cap sc.
Proof. intros sc j H. rewrite (grp_cap_small j H). apply grp_cap_ge. Qed.

(* [comment removed for export] *)
Definition malloc_cap (n : Z) : Z := Z.max (grp_cap (size_to_class_z n)) (grp_cap (size_to_class_z n + 1)).
Definition malloc_db (n : Z) : Z := if n <? MMAP_THRESHOLD then 32768 + malloc_cap n else n + 12307.

Lemma malloc_cap_ge : forall n, 2^16 <= malloc_cap n.
Proof. intros n. unfold malloc_cap. pose proof (grp_cap_ge (size_to_class_z n)). lia. Qed.

Lemma malloc_cap_cls : forall n sc, sc = size_to_class_z n \/ sc = size_to_class_z n + 1 -> grp_cap sc <= malloc_cap n.
Proof. intros n sc [-> | ->]; unfold malloc_cap; lia. Qed.

Lemma malloc_db_small : forall n, n < MMAP_THRESHOLD -> malloc_db n = 32768 + malloc_cap n.
Proof. intros n H. unfold malloc_db. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma malloc_db_big : forall n, MMAP_THRESHOLD <= n -> malloc_db n = n + 12307.
Proof. intros n H. unfold malloc_db. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma malloc_db_pos : forall n, 0 <= n -> 12307 <= malloc_db n.
Proof.
  intros n Hn. unfold malloc_db. destruct (n <? MMAP_THRESHOLD); [pose proof (malloc_cap_ge n); lia | lia].
Qed.

(* [comment removed for export] *)
Lemma ag_len_cap : forall szc req c2 n3,
  1 <= szc <= 8191 -> 0 <= req -> req + 4 <= 16 * szc ->
  1 <= c2 <= 32 -> 16 * szc * c2 < 2^20 ->
  (n3 = page_round_up_Z (16 * szc * c2 + 16) \/ n3 = page_round_up_Z (req + 20)) ->
  n3 <= Z.min (2^20) (512 * szc + 4111) /\ (szc <= 127 -> n3 <= 2^16).
Proof.
  intros szc req c2 n3 Hszc Hreq Hreq4 Hc2 Hspan Hcase.
  destruct (page_round_up_Z_spec (16 * szc * c2 + 16) ltac:(clear - Hszc Hc2; lia)) as [Hn2 Hn2m].
  destruct (page_round_up_Z_spec (req + 20) ltac:(clear - Hreq; lia)) as [Hr20 Hr20m].
  assert (Hm : n3 mod 4096 = 0) by (destruct Hcase as [-> | ->]; assumption).
  assert (Hle : n3 < Z.min (2^20 + 1) (512 * szc + 4112)).
  { destruct Hcase as [-> | ->].
    - (* [comment removed for export] *)
      assert (H16 : 16 * szc * c2 + 16 <= 2^20).
      { replace (16 * szc * c2) with (16 * (szc * c2)) in * by ring. clear - Hspan. lia. }
      assert (Hup : page_round_up_Z (16 * szc * c2 + 16) <= 2^20).
      { clear - Hn2 Hn2m H16. apply Z.mod_divide in Hn2m; [|lia]. destruct Hn2m as [q Hq]. rewrite Hq in *. lia. }
      assert (Hmul : 16 * szc * c2 <= 512 * szc) by (clear - Hszc Hc2; nia).
      clear - Hn2 Hup Hmul. lia.
    - clear - Hr20 Hreq4 Hszc. lia. }
  clear Hn2 Hn2m Hr20 Hr20m Hcase.
  split; [clear - Hle; lia|].
  intros Hs. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. clear - Hle Hs Hq. lia.
Qed.

Lemma ag_len_grp_cap : forall sc req c2 n3,
  1 <= size_class sc <= 8191 -> 0 <= req -> req + 4 <= 16 * size_class sc ->
  1 <= c2 <= 32 -> 16 * size_class sc * c2 < 2^20 ->
  (n3 = page_round_up_Z (16 * size_class sc * c2 + 16) \/ n3 = page_round_up_Z (req + 20)) ->
  n3 <= grp_cap sc.
Proof.
  intros sc req c2 n3 Hszc Hreq Hreq4 Hc2 Hspan Hcase.
  destruct (ag_len_cap _ _ _ _ Hszc Hreq Hreq4 Hc2 Hspan Hcase) as [H1 H2].
  unfold grp_cap. destruct (size_class sc <=? 127) eqn:E; [apply H2; apply Z.leb_le; exact E | exact H1].
Qed.
