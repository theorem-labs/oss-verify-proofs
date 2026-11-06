(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
From Stdlib Require Import List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac LiaTuning.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[global] Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

Module LS.
Import Ltac2.
(* [comment removed for export] *)
Ltac2 rec mixed (andc : constr) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Constr.equal h andc then
        (if zt_plain_arith (Array.get args 0) then true
         else if zt_plain_arith (Array.get args 1) then true
         else if mixed andc (Array.get args 0) then true
         else mixed andc (Array.get args 1))
      else false
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 split () : unit :=
  let andc := '@and in
  List.iter (fun h => let (id, body, ty) := h in
    match body with
    | Some _ => ()
    | None =>
        if zt_is_local id then
          (if zt_plain_arith ty then () else if mixed andc ty then
             ltac1:(h |- decompose [and] h) (Ltac1.of_ident id) else ())
        else ()
    end) (Control.hyps ()).
End LS.
Ltac split_mixed := ltac2:(Control.enter LS.split).

Module CJFB.
Lemma kn (X N k n : Z) : X + N <= 2^64 -> (k + n <=? N) = true -> X + k + n <= 2^64.
Proof. intros H1 H2. apply Z.leb_le in H2. lia. Qed.
Lemma n1 (X N n : Z) : X + N <= 2^64 -> (n <=? N) = true -> X + n <= 2^64.
Proof. intros H1 H2. apply Z.leb_le in H2. lia. Qed.
Lemma nonneg (k : nat) (Y : Z) : 0 <= Y -> 0 <= Y + Z.of_nat k.
Proof. intros H. lia. Qed.
Lemma c1 (X k : Z) : (0 <=? k) = true -> X <= X + k.
Proof. intros H. apply Z.leb_le in H. lia. Qed.
Lemma c2 (X j k : Z) : (j <=? k) = true -> X + j <= X + k.
Proof. intros H. apply Z.leb_le in H. lia. Qed.
Lemma c3 (X k n N : Z) : (k + n <=? N) = true -> X + k + n <= X + N.
Proof. intros H. apply Z.leb_le in H. lia. Qed.
Lemma e1 (X j k : Z) : (j =? k) = true -> X + j = X + k.
Proof. intros H. apply Z.eqb_eq in H. lia. Qed.
Lemma e0 (X k : Z) : (k =? 0) = true -> X = X + k.
Proof. intros H. apply Z.eqb_eq in H. lia. Qed.
Lemma r0 (x : Z) : ((0 <=? x) && (x <? 2^64))%bool = true -> 0 <= x < 2^64.
Proof. intros H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.
Lemma r1 (X N : Z) : 0 <= X -> X + N <= 2^64 -> (0 <? N) = true -> 0 <= X < 2^64.
Proof. intros H1 H2 H3. apply Z.ltb_lt in H3. lia. Qed.
End CJFB.

Ltac cjfb_le :=
  lazymatch goal with
  | |- ?X <= ?X + ?k => exact (CJFB.c1 X k eq_refl)
  | |- ?X + ?j <= ?X + ?k => exact (CJFB.c2 X j k eq_refl)
  | |- ?X + ?k + ?n <= ?X + ?N => exact (CJFB.c3 X k n N eq_refl)
  end.
Ltac cj_fast :=
  lazymatch goal with
  | |- ?X + ?k + ?n <= 2 ^ 64 =>
      match goal with
      | H : X + ?N <= 2 ^ 64 |- _ => exact (CJFB.kn X N k n H eq_refl)
      | H : _ /\ X + ?N <= 2 ^ 64 |- _ => exact (CJFB.kn X N k n (proj2 H) eq_refl)
      end
  | |- ?X + ?n <= 2 ^ 64 =>
      match goal with
      | H : X + ?N <= 2 ^ 64 |- _ => exact (CJFB.n1 X N n H eq_refl)
      | H : _ /\ X + ?N <= 2 ^ 64 |- _ => exact (CJFB.n1 X N n (proj2 H) eq_refl)
      end
  | |- 0 <= ?X + Z.of_nat ?k =>
      match goal with
      | H : 0 <= X |- _ => exact (CJFB.nonneg k X H)
      | H : 0 <= X /\ _ |- _ => exact (CJFB.nonneg k X (proj1 H))
      end
  | |- 0 <= ?X < 2 ^ 64 =>
      first [ exact (CJFB.r0 X eq_refl)
            | match goal with
              | H : 0 <= X /\ X + ?N <= 2 ^ 64 |- _ => exact (CJFB.r1 X N (proj1 H) (proj2 H) eq_refl)
              end ]
  | |- ?X <= ?X + _ => cjfb_le
  | |- ?X + _ <= ?X + _ => cjfb_le
  | |- ?X + ?j = ?X + ?k => exact (CJFB.e1 X j k eq_refl)
  | |- ?X = ?X + ?k => exact (CJFB.e0 X k eq_refl)
  | |- (_ <= _ /\ _ <= _) \/ False => left; split; cjfb_le
  end.

Ltac lia_cj_t1 := LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_cj_ts := split_mixed; lia0_prune_logic; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_cj_tse := split_mixed; lia0_prune_logic; Zify.zify; xlia zchecker.
Ltac lia_cj_full := Zify.zify; xlia zchecker.
Ltac lia_cj := first [ cj_fast | lia_cj_t1 | lia_cj_ts | lia_cj_full ].
Ltac lia_cj_nf := first [ cj_fast | lia_cj_t1 | lia_cj_ts | lia_cj_tse ].
Ltac flia_cj := first [ assumption | lia_cj_nf ].

(* [comment removed for export] *)
Ltac simpl_sizes_cj :=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [length].
(* [comment removed for export] *)
Ltac simpl_arr_sizes_cj := rewrite ?u32s_length, ?u64s_length, ?upd_length.
