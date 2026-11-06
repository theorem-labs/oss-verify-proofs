(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_split.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition INF_LC : list Z := [105; 110; 102].     (* [comment removed for export] *)
Definition NAN_LC : list Z := [110; 97; 110].      (* [comment removed for export] *)
Definition INF_UC : list Z := [73; 78; 70].        (* [comment removed for export] *)
Definition NAN_UC : list Z := [78; 65; 78].        (* [comment removed for export] *)

Definition nf_str (y1 t : Z) : list Z :=
  if Z.land t 32 =? 0 then (if f128_le y1 y1 =? 0 then INF_UC else NAN_UC)
  else (if f128_le y1 y1 =? 0 then INF_LC else NAN_LC).

Definition fmt_fp_nf (o : list Z) (y w p fl t : Z) : option (list Z * Z) :=
  let '(y1, prefix, pl) := ffp_sign y fl in
  if fpclassifyl y1 <=? 1 then
    if (0 <=? w) && (w <=? 1) then Some (o ++ zsub PREFIX_STR prefix pl ++ nf_str y1 t, 3 + pl) else None
  else None.

(* [comment removed for export] *)
Definition fmt_fp' (o : list Z) (y w p fl t : Z) : option (list Z * Z) :=
  match fmt_fp o y w p fl t with
  | Some r => Some r
  | None => fmt_fp_nf o y w p fl t
  end.

(* [comment removed for export] *)
Definition nonfinite (y fl : Z) : Prop := let '(y1, _, _) := ffp_sign y fl in fpclassifyl y1 <= 1.

Lemma fmt_fp_nonfinite_none : forall o y w p fl t, nonfinite y fl -> fmt_fp o y w p fl t = None.
Proof.
  intros o y w p fl t H. rewrite fmt_fp_split. unfold nonfinite in H.
  destruct (ffp_sign y fl) as [[y1 prefix] pl]. apply Z.leb_le in H. rewrite H. reflexivity.
Qed.

Lemma fmt_fp'_finite : forall o y w p fl t, ~ nonfinite y fl -> fmt_fp' o y w p fl t = fmt_fp o y w p fl t.
Proof.
  intros o y w p fl t H. unfold fmt_fp'. destruct (fmt_fp o y w p fl t) as [r|] eqn:E; [reflexivity|].
  unfold fmt_fp_nf. unfold nonfinite in H. destruct (ffp_sign y fl) as [[y1 prefix] pl].
  destruct (Z.leb_spec (fpclassifyl y1) 1); [exfalso; exact (H H0)|reflexivity].
Qed.

Lemma fmt_fp'_nonfinite : forall o y w p fl t, nonfinite y fl -> fmt_fp' o y w p fl t = fmt_fp_nf o y w p fl t.
Proof. intros o y w p fl t H. unfold fmt_fp'. rewrite (fmt_fp_nonfinite_none o y w p fl t H). reflexivity. Qed.

Lemma nonfinite_dec : forall y fl, {nonfinite y fl} + {~ nonfinite y fl}.
Proof. intros y fl. unfold nonfinite. destruct (ffp_sign y fl) as [[y1 prefix] pl]. apply Z_le_dec. Qed.

Lemma nf_str_length : forall y1 t, length (nf_str y1 t) = 3%nat.
Proof. intros y1 t. unfold nf_str. destruct (Z.land t 32 =? 0), (f128_le y1 y1 =? 0); reflexivity. Qed.

Lemma fmt_fp_nf_w : forall o y w p fl t r, fmt_fp_nf o y w p fl t = Some r -> 0 <= w <= 1.
Proof.
  intros o y w p fl t r H. unfold fmt_fp_nf in H. destruct (ffp_sign y fl) as [[y1 prefix] pl].
  destruct (fpclassifyl y1 <=? 1); [|discriminate].
  destruct ((0 <=? w) && (w <=? 1)) eqn:E; [|discriminate].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
