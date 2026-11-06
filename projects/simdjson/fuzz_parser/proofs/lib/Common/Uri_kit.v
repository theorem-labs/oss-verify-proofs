(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import WStr StrFun F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cu_range : forall w, 0 <= cu w < 2^32.
Proof. intros w. unfold cu. apply Z.mod_pos_bound. lia. Qed.

Lemma unsigned_sx32 : forall w, bv_unsigned (sx32 w) = (if cu w <? 2^31 then cu w else cu w + 2^64 - 2^32).
Proof.
  intros w. unfold sx32, cu. rewrite Z_to_bv_unsigned. rewrite bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as M.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  set (u := bv_unsigned w) in *.
  assert (E32 : (u + 2^31) mod 2^32 = ((u mod 2^32) + 2^31) mod 2^32).
  { rewrite Z.add_mod_idemp_l by lia. reflexivity. } rewrite E32.
  destruct (Z.ltb_spec (u mod 2^32) (2^31)).
  - rewrite (Z.mod_small (u mod 2^32 + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((u mod 2^32 + 2^31) mod 2^32) with (u mod 2^32 + 2^31 - 2^32) by (Z.div_mod_to_equations; nia).
    Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma sx32_eqb_lit : forall w k, 0 <= k < 2^31 -> bv_eqb (sx32 w) (Z_to_bv 64 k) = (cu w =? k).
Proof.
  intros w k Hk. unfold bv_eqb. rewrite unsigned_sx32, unsigned_lit by lia. pose proof (cu_range w).
  destruct (Z.ltb_spec (cu w) (2^31)); [reflexivity|].
  destruct (Z.eqb_spec (cu w + 2^64 - 2^32) k); destruct (Z.eqb_spec (cu w) k); try reflexivity; lia.
Qed.

Lemma sx32_of_unit : forall c, 0 <= c < 2^31 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof. intros c Hc. apply sx32_lit. lia. Qed.

Lemma cu_lit : forall c, 0 <= c < 2^32 -> cu (Z_to_bv 64 c) = c.
Proof. exact cu_of_Z. Qed.


(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.
Lemma zb_read : forall m A l i a,
  bytes_at segs m A (zb l) -> 0 <= i < zlength l -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
  intros m A l i a HB Hi ->.
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  2:{ apply nth_error_None in E. unfold zlength in Hi. lia. }
  replace (znth l i) with c by (unfold znth; destruct (Z.ltb_spec i 0); [lia|]; symmetry; apply nth_error_nth; exact E).
  apply (u8ro_read segs m A (zb l) i); [exact HB| unfold zb; rewrite nth_error_map, E; reflexivity| lia| reflexivity].
Qed.
End WithSegs.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma znth_app_r : forall (a b : list Z) i, zlength a <= i -> znth (a ++ b) i = znth b (i - zlength a).
Proof.
  intros a b i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec (i - Z.of_nat (length a)) 0); [lia|].
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma znth_app_l : forall (a b : list Z) i, i < zlength a -> znth (a ++ b) i = znth a i.
Proof.
  intros a b i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [reflexivity|]. apply app_nth1. lia.
Qed.
Lemma znth_skipn : forall (l : list Z) k i, 0 <= i -> znth (skipn k l) i = znth l (i + Z.of_nat k).
Proof.
  intros l k i Hi. unfold znth. destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec (i + Z.of_nat k) 0); [lia|].
  rewrite nth_skipn. f_equal. lia.
Qed.
Lemma znth_over : forall (l : list Z) i, zlength l <= i -> znth l i = 0.
Proof. intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [reflexivity|]. apply nth_overflow. lia. Qed.
Lemma znth_cons_S : forall c (l : list Z) i, 0 <= i -> znth (c :: l) (i + 1) = znth l i.
Proof. intros c l i H. unfold znth. destruct (Z.ltb_spec (i+1) 0); [lia|]. destruct (Z.ltb_spec i 0); [lia|]. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity. Qed.

(* [comment removed for export] *)
Section Cur.
  Variables (s tail : list Z).
  Let orig := s ++ 0 :: tail.

  Lemma orig_nth : forall i, 0 <= i <= zlength s -> znth orig i = znth s i.
  Proof.
    intros i Hi. subst orig. destruct (Z.lt_ge_cases i (zlength s)).
    - apply znth_app_l. lia.
    - rewrite znth_app_r by lia. replace (i - zlength s) with 0 by lia. rewrite (znth_over s i) by lia. reflexivity.
  Qed.

  Lemma cur_nth : forall acc i, zlength acc <= i <= zlength s -> znth (acc ++ skipn (length acc) orig) i = znth s i.
  Proof.
    intros acc i Hi. unfold zlength in Hi. rewrite znth_app_r by (unfold zlength; lia). unfold zlength. rewrite znth_skipn by lia.
    replace (i - Z.of_nat (length acc) + Z.of_nat (length acc)) with i by lia. apply orig_nth. unfold zlength. lia.
  Qed.

  Lemma skipn_cons_nth : forall k (l : list Z), (k < length l)%nat -> skipn k l = znth l (Z.of_nat k) :: skipn (S k) l.
  Proof.
    intros k l Hk. unfold znth. destruct (Z.ltb_spec (Z.of_nat k) 0); [lia|]. rewrite Nat2Z.id.
    revert l Hk. induction k as [|k IH]; intros [|x l] Hk; cbn in Hk; try lia; [reflexivity|].
    cbn [skipn nth]. all: try (apply IH; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma cur_keep : forall acc, (length acc <= length s)%nat ->
    acc ++ skipn (length acc) orig = (acc ++ [znth s (zlength acc)]) ++ skipn (length (acc ++ [znth s (zlength acc)])) orig.
  Proof.
    intros acc Hl. rewrite <- app_assoc. cbn [app]. f_equal.
    rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
    rewrite (skipn_cons_nth (length acc)) by (subst orig; rewrite length_app; cbn; lia). f_equal.
    unfold zlength. apply orig_nth. unfold zlength. lia.
  Qed.

  Lemma upd_nat_app_len : forall (acc l : list Z) x v, upd_nat (acc ++ x :: l) (length acc) v = acc ++ v :: l.
  Proof. induction acc as [|y acc IH]; intros l x v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma cur_upd : forall acc v, (length acc <= length s)%nat ->
    zupd (acc ++ skipn (length acc) orig) (zlength acc) v = (acc ++ [v]) ++ skipn (length (acc ++ [v])) orig.
  Proof.
    intros acc v Hl. unfold zupd, zlength. destruct (Z.ltb_spec (Z.of_nat (length acc)) 0); [lia|]. rewrite Nat2Z.id.
    rewrite <- app_assoc. cbn [app]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
    rewrite (skipn_cons_nth (length acc)) by (subst orig; rewrite length_app; cbn; lia).
    apply upd_nat_app_len.
  Qed.

  (* [comment removed for export] *)
  Lemma cur_upd2 : forall acc v1 v2, (S (length acc) <= length s)%nat ->
    zupd (zupd (acc ++ skipn (length acc) orig) (zlength acc) v1) (zlength acc + 1) v2
    = (acc ++ [v1; v2]) ++ skipn (length (acc ++ [v1; v2])) orig.
  Proof.
    intros acc v1 v2 Hl. rewrite cur_upd by lia.
    replace (zlength acc + 1) with (zlength (acc ++ [v1])) by (unfold zlength; rewrite length_app; cbn; lia).
    rewrite cur_upd by (rewrite length_app; cbn; lia). rewrite <- !app_assoc. reflexivity.
  Qed.
End Cur.

Lemma swrap32_id : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x H. rewrite bv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)


Lemma cu_sx32 : forall w, cu (sx32 w) = cu w.
Proof.
  intros w. pose proof (cu_range w) as R. unfold cu at 1. rewrite unsigned_sx32.
  destruct (Z.ltb_spec (cu w) (2^31)); [apply Z.mod_small; lia|].
  replace (cu w + 2^64 - 2^32) with (cu w + (2^32 - 1) * 2^32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.




(* [comment removed for export] *)
Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2) with (2^63). lia.
Qed.
Lemma shiftr2_mul4 : forall k, 0 <= k -> Z.shiftr (4 * k) 2 = k.
Proof. intros k Hk. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
Lemma shiftr62_small : forall x, 0 <= x < 2^62 -> Z.shiftr x 62 = 0.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma shiftl2 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.

