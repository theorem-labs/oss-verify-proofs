(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SoftFloat FmtFp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition nf_str (y t : Z) : list Z :=
  if negb (f128_le y y =? 0) then (if Z.land t 32 =? 0 then [78; 65; 78] else [110; 97; 110])
  else (if Z.land t 32 =? 0 then [73; 78; 70] else [105; 110; 102]).

Definition nf_sign (y fl : Z) : Z * Z * Z :=
  if negb (signbitl y =? 0) then (Z.lxor y F128_SIGNBIT, 0, 1)
  else if negb (Z.land fl MARK_POS =? 0) then (y, 3, 1)
  else if negb (Z.land fl PAD_POS =? 0) then (y, 6, 1)
  else (y, 1, 0).

Definition fmt_fp_nf (o : list Z) (y w p fl t : Z) : option (list Z * Z) :=
  let '(y, prefix, pl) := nf_sign y fl in
  if fpclassifyl y <=? 1 then
    let? o := pad o CHR_sp w (3 + pl) (Z.land fl (Z.lnot ZERO_PAD)) in
    let o := out o (zsub PREFIX_STR prefix pl) in
    let o := out o (nf_str y t) in
    let? o := pad o CHR_sp w (3 + pl) (Z.lxor fl LEFT_ADJ) in
    Some (o, Z.max w (3 + pl))
  else None.

Definition fmt_fp_total (o : list Z) (y w p fl t : Z) : option (list Z * Z) :=
  match fmt_fp_nf o y w p fl t with
  | Some r => Some r
  | None => fmt_fp o y w p fl t
  end.

Lemma nf_str_length : forall y t, length (nf_str y t) = 3%nat.
Proof. intros. unfold nf_str. destruct (negb _), (_ =? _); reflexivity. Qed.

Lemma fmt_fp_total_finite : forall o y w p fl t, fmt_fp_nf o y w p fl t = None -> fmt_fp_total o y w p fl t = fmt_fp o y w p fl t.
Proof. intros o y w p fl t E. unfold fmt_fp_total. rewrite E. reflexivity. Qed.
Lemma fmt_fp_total_nf : forall o y w p fl t r, fmt_fp_nf o y w p fl t = Some r -> fmt_fp_total o y w p fl t = Some r.
Proof. intros o y w p fl t r E. unfold fmt_fp_total. rewrite E. reflexivity. Qed.

Lemma fmt_fp_total_of_finite : forall o y w p fl t r, fmt_fp o y w p fl t = Some r -> fmt_fp_total o y w p fl t = Some r.
Proof.
  intros o y w p fl t r E. unfold fmt_fp_total, fmt_fp_nf, nf_sign. unfold fmt_fp in E |- *.
  destruct (negb (signbitl y =? 0)); [| destruct (negb (Z.land fl MARK_POS =? 0)); [| destruct (negb (Z.land fl PAD_POS =? 0))]];
    (destruct (fpclassifyl _ <=? 1); [discriminate E | exact E]).
Qed.
