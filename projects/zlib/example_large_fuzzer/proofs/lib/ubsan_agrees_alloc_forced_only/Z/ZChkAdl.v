(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkArith.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition b0 : byte := Z_to_bv 8 0.
Definition bZ (d : list byte) : list Z := map bv_unsigned d.
Definition bnth (d : list byte) (k : nat) : Z := bv_unsigned (nth k d b0).

Lemma bZ_length : forall d, length (bZ d) = length d.
Proof. intro d. apply length_map. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition A1 (d : list byte) (s1 s2 : Z) (k : nat) : Z :=
  fst (adl_raw (firstn k (bZ d)) s1 s2).
Definition A2 (d : list byte) (s1 s2 : Z) (k : nat) : Z :=
  snd (adl_raw (firstn k (bZ d)) s1 s2).

Lemma adl_raw_app : forall xs ys s1 s2,
  adl_raw (xs ++ ys) s1 s2
  = adl_raw ys (fst (adl_raw xs s1 s2)) (snd (adl_raw xs s1 s2)).
Proof.
  induction xs as [|x xs IH]; intros ys s1 s2; cbn [app adl_raw fst snd].
  - reflexivity.
  - apply IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition IS1 (init : Z) : Z := Z.land init 65535.
Definition IS2 (init : Z) : Z := Z.land (Z.shiftr init 16) 65535.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lor_lxor_disj : forall a b, Z.land a b = 0 -> Z.lor a b = Z.lxor a b.
Proof.
  intros a b H. apply Z.bits_inj'. intros n Hn.
  assert (Hb : andb (Z.testbit a n) (Z.testbit b n) = false)
    by (rewrite <- Z.land_spec, H, Z.bits_0; reflexivity).
  rewrite Z.lor_spec, Z.lxor_spec.
  destruct (Z.testbit a n), (Z.testbit b n); cbn in Hb |- *; congruence.
Qed.

Lemma combine_lor : forall a s, 0 <= a < 65536 -> 0 <= s ->
  Z.lor (Z.shiftl s 16) a = Z.lxor (Z.shiftl s 16) a.
Proof.
  intros a s Ha Hs. apply lor_lxor_disj. rewrite Z.land_comm.
  apply (land_shiftl_disj a s 16); [change (2 ^ 16) with 65536; lia|lia|lia].
Qed.

(* [comment removed for export] *)
Lemma condsub : forall x, 0 <= x < 2 * ABASE ->
  (if Z.leb x 65520 then x else x - ABASE) = x mod ABASE.
Proof.
  intros x Hx. unfold ABASE in *.
  destruct (Z.leb_spec x 65520) as [H|H].
  - symmetry. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add x (-1) 65521) by lia.
    symmetry. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RQ (x : Z) : Z := Z.shiftr (x * AMAGIC_IMAGE) 64.
Definition RD (x : Z) : Z := x - RQ x.
Definition RH (x : Z) : Z := Z.shiftr (RD x) 1.
Definition RT (x : Z) : Z := Z.shiftr (RQ x + RH x) 15.

(* [comment removed for export] *)
Definition RLIM : Z := 1099511627776.

Lemma RQ_mulhu : forall x, RQ x = mulhu x AMAGIC_IMAGE.
Proof.
  intro x. unfold RQ, mulhu. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma RQ_bound : forall x, 0 <= x < RLIM -> 0 <= RQ x <= x.
Proof.
  intros x Hx. unfold RLIM in Hx. rewrite RQ_mulhu, mulhu_eq by lia.
  split; [apply Z.div_pos; [lia | unfold ABASE; lia]|].
  apply Z.div_le_upper_bound; [unfold ABASE; lia | unfold ABASE; lia].
Qed.

Lemma RD_bound : forall x, 0 <= x < RLIM -> 0 <= RD x <= x.
Proof.
  intros x Hx. pose proof (RQ_bound x Hx). unfold RD. lia.
Qed.

Lemma RH_bound : forall x, 0 <= x < RLIM -> 0 <= RH x <= x.
Proof.
  intros x Hx. pose proof (RD_bound x Hx). unfold RH.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  split; [apply Z.div_pos; lia|].
  apply Z.le_trans with (RD x); [apply Z.div_le_upper_bound; lia | lia].
Qed.

Lemma RT_div : forall x, 0 <= x < RLIM -> RT x = x / ABASE.
Proof.
  intros x Hx. unfold RT, RH, RD. rewrite !RQ_mulhu.
  apply mdiv_image_correct. exact Hx.
Qed.

Lemma RT_bound : forall x, 0 <= x < RLIM -> 0 <= RT x <= x.
Proof.
  intros x Hx. rewrite RT_div by exact Hx. unfold RLIM in Hx.
  split; [apply Z.div_pos; [lia | unfold ABASE; lia]|].
  apply Z.div_le_upper_bound; unfold ABASE; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma firstn_split : forall (A : Type) (k j : nat) (l : list A),
  firstn (k + j) l = firstn k l ++ firstn j (skipn k l).
Proof.
  intros A. induction k as [|k IH]; intros j l; cbn [firstn skipn Nat.add app].
  - reflexivity.
  - destruct l as [|x l]; cbn [firstn skipn app].
    + rewrite firstn_nil. reflexivity.
    + f_equal. apply IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

