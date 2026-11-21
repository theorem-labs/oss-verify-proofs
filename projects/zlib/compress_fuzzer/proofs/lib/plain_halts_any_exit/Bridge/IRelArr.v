(** * Bridge.IRelArr — INTERFACE (part C lead): array relations between the two models.

    S5 arrays are [parr] (length, default function, PositiveMap; a write past
    the length is dropped).  RT arrays are total closures [zarr = Z -> Z] and
    [ztbl = Z -> Code].  Every array conjunct of the state relations
    ([IRelDefl], [IRelInfl]) is one of the two relations below on an index
    range.  Each relation has a boolean checker for computed probes and
    differential checks, with its soundness lemma.

    Ownership: the part C lead.  Groups import this file and do not edit it;
    an interface change goes through the lead (PAIR-GROUPS.md). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** S5's array agrees with RT's on [[lo, hi)]. *)
Definition arr_rel (a : arr) (z : Base.zarr) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> arr_get a i = z i.

(** S5's packed code table agrees with RT's [Code] table on [[lo, hi)]:
    S5 stores [code_pack op bits val = op + 256 bits + 65536 val], which is
    RT's [code_enc]. *)
Definition tbl_rel (a : arr) (t : Base.ztbl) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> arr_get a i = Base.code_enc (t i).

(** ** Checkers

    [zall lo hi p] tests [p] on every index of [[lo, hi)], carrying the index
    as a [Z] (a [seq]-of-[nat] version converts each index from unary and is
    quadratic: it took over 10 minutes on a 64 KiB window). *)

Fixpoint zall_go (n : nat) (i : Z) (p : Z -> bool) : bool :=
  match n with
  | O => true
  | S n' => p i && zall_go n' (i + 1) p
  end.

Definition zall (lo hi : Z) (p : Z -> bool) : bool := zall_go (Z.to_nat (hi - lo)) lo p.

Lemma zall_go_sound : forall n i p, zall_go n i p = true -> forall j, i <= j < i + Z.of_nat n -> p j = true.
Proof.
  induction n as [|n IH]; intros i p H j Hj; [lia|].
  cbn [zall_go] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec j i) as [->|Hne]; [exact H1|].
  apply (IH (i + 1) p H2). lia.
Qed.

Lemma zall_sound : forall lo hi p, zall lo hi p = true -> forall j, lo <= j < hi -> p j = true.
Proof. intros lo hi p H j Hj. apply (zall_go_sound _ _ _ H). lia. Qed.

Definition arr_relb (a : arr) (z : Base.zarr) (lo hi : Z) : bool :=
  zall lo hi (fun i => arr_get a i =? z i).

Definition tbl_relb (a : arr) (t : Base.ztbl) (lo hi : Z) : bool :=
  zall lo hi (fun i => arr_get a i =? Base.code_enc (t i)).

Lemma arr_relb_sound : forall a z lo hi, arr_relb a z lo hi = true -> arr_rel a z lo hi.
Proof. intros a z lo hi H i Hi. apply Z.eqb_eq, (zall_sound _ _ _ H i Hi). Qed.

Lemma tbl_relb_sound : forall a t lo hi, tbl_relb a t lo hi = true -> tbl_rel a t lo hi.
Proof. intros a t lo hi H i Hi. apply Z.eqb_eq, (zall_sound _ _ _ H i Hi). Qed.

(** ** The kit every array step uses *)

Lemma arr_rel_narrow : forall a z lo hi lo' hi',
  lo <= lo' -> hi' <= hi -> arr_rel a z lo hi -> arr_rel a z lo' hi'.
Proof. intros a z lo hi lo' hi' H1 H2 H i Hi. apply H. lia. Qed.

(** The same write on both sides.  S5 drops a write outside its length, so
    the written index must be inside it whenever it is inside the range. *)
Lemma arr_rel_set : forall a z lo hi i v,
  arr_rel a z lo hi -> (lo <= i < hi -> 0 <= i < arr_len a) ->
  arr_rel (arr_set a i v) (Base.zset z i v) lo hi.
Proof.
  intros a z lo hi i v H Hin j Hj.
  destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite arr_get_set_same by (apply Hin; exact Hj). rewrite Base.zset_same. reflexivity.
  - rewrite arr_get_set_other by congruence. rewrite Base.zset_other by exact Hne. apply H, Hj.
Qed.

(** A write outside the range is invisible to it. *)
Lemma arr_rel_set_out_l : forall a z lo hi i v,
  ~ (lo <= i < hi) -> arr_rel a z lo hi -> arr_rel (arr_set a i v) z lo hi.
Proof.
  intros a z lo hi i v Hout H j Hj. rewrite arr_get_set_other by lia. apply H, Hj.
Qed.

Lemma arr_rel_set_out_r : forall a z lo hi i v,
  ~ (lo <= i < hi) -> arr_rel a z lo hi -> arr_rel a (Base.zset z i v) lo hi.
Proof.
  intros a z lo hi i v Hout H j Hj. rewrite Base.zset_other by lia. apply H, Hj.
Qed.

Lemma arr_rel_slice : forall a z lo hi ofs n,
  arr_rel a z lo hi -> lo <= ofs -> ofs + n <= hi -> 0 <= n ->
  arr_slice a ofs n = map (fun k => z (ofs + Z.of_nat k)) (seq 0 (Z.to_nat n)).
Proof.
  intros a z lo hi ofs n H H1 H2 Hn. unfold arr_slice.
  assert (Hgen : forall m o, lo <= o -> o + Z.of_nat m <= hi ->
            arr_slice_nat a o m = map (fun k => z (o + Z.of_nat k)) (seq 0 m)).
  { induction m as [|m IH]; intros o Ho1 Ho2; [reflexivity|].
    cbn [arr_slice_nat seq map]. rewrite Z.add_0_r, (H o) by lia. f_equal.
    rewrite IH by lia. rewrite <- seq_shift, map_map. apply map_ext. intros k. f_equal. lia. }
  apply Hgen; lia.
Qed.
