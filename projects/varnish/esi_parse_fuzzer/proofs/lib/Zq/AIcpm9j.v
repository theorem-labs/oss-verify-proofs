(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.

Module AFreeLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition apart (a s b t : Z) : Prop := a + s <= b \/ b + t <= a.

Lemma notin_mono : forall a lo hi lo' hi', ~ (lo' <= a < hi') -> lo' <= lo -> hi <= hi' -> ~ (lo <= a < hi).
Proof. intros; lia. Qed.
Lemma outside_of_disj : forall a lo hi, a + 1 <= lo \/ hi <= a -> ~ (lo <= a < hi).
Proof. intros; lia. Qed.

(* [comment removed for export] *)
Lemma apart_gl : forall a s b t, apart a s b t -> forall x n lo hi,
  a <= x -> x + n <= a + s -> b <= lo -> hi <= b + t -> x + n <= lo \/ hi <= x.
Proof. intros a s b t [H|H] x n lo hi H1 H2 H3 H4; [left|right]; lia. Qed.
Lemma apart_gr : forall a s b t, apart a s b t -> forall x n lo hi,
  b <= x -> x + n <= b + t -> a <= lo -> hi <= a + s -> x + n <= lo \/ hi <= x.
Proof. intros a s b t [H|H] x n lo hi H1 H2 H3 H4; [right|left]; lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox H := unfold boxed in H.

(* [comment removed for export] *)
Lemma trc_join : forall m A (w : word) v,
  rw_cells rsegs m A [C8 w] -> rw_cells rsegs m (A + 8) [C4 (Z_to_bv 64 v)] -> rw_cells rsegs m (A + 12) [C4 (Z_to_bv 64 0)] ->
  (v = 1 \/ v = 2) -> ro_cells rsegs m A [C8 w; C8 (Z_to_bv 64 v)].
Proof.
  intros m A w v [[_ B0] _] [[_ B1] _] [[_ B2] _] Hv. cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *.
  split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_app. split; [exact B0|]. rewrite length_le8. change (Z.of_nat 8) with 8.
  assert (E : le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0)) by (destruct Hv as [-> | ->]; reflexivity).
  rewrite E. apply bytes_at_app. split; [exact B1|]. rewrite length_le4. change (A + 8 + Z.of_nat 4) with (A + 8 + 4).
  replace (A + 8 + 4) with (A + 12) by lia. exact B2.
Qed.
End AFreeLib.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Definition zeros (k : nat) : list byte := repeat (Z_to_bv 8 0) k.

Lemma zeros_length : forall k, length (zeros k) = k.
Proof. intros; unfold zeros; apply repeat_length. Qed.

Lemma zeros_nth : forall k i, (i < k)%nat -> nth_error (zeros k) i = Some (Z_to_bv 8 0).
Proof.
  intros k. induction k as [|k IH]; intros i Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma skipn_repeat : forall (A : Type) (b : A) j k, skipn j (repeat b k) = repeat b (k - j).
Proof.
  intros A b j. induction j as [|j IH]; intros k; [cbn; rewrite Nat.sub_0_r; reflexivity|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH.
Qed.

Lemma firstn_repeat : forall (A : Type) (b : A) j k, (j <= k)%nat -> firstn j (repeat b k) = repeat b j.
Proof.
  intros A b j. induction j as [|j IH]; intros k Hk; [reflexivity|].
  destruct k as [|k]; [lia|]. cbn. f_equal. apply IH. lia.
Qed.

Lemma zeros_window : forall k j w, (j + w <= k)%nat -> firstn w (skipn j (zeros k)) = zeros w.
Proof. intros k j w H. unfold zeros. rewrite skipn_repeat, firstn_repeat by lia. reflexivity. Qed.

Lemma zeros_app : forall a b, zeros (a + b) = zeros a ++ zeros b.
Proof. intros; unfold zeros; apply repeat_app. Qed.

(* [comment removed for export] *)
Lemma land_m8 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (x - x mod 8)%Z.
Proof.
  intros x Hx. change 18446744073709551608%Z with (2^64 - 2^3)%Z.
  rewrite land_align_down by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma load8_zeros : bv_extract 0 64 (le_bytes_to_word (zeros 8)) = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Ltac lit_nonneg k := let kz := zlit k in lazymatch eval vm_compute in (andb (Z.leb 0 kz) (Z.ltb kz 4096)) with true => idtac end.
Ltac solve_load_base ::=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lit_nonneg k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lit_nonneg k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

(* [comment removed for export] *)
Definition shadow_off : Z := 2147450880.

(* [comment removed for export] *)
Definition sha (a : Z) : Z := (a / 8 + shadow_off)%Z.
(* [comment removed for export] *)
Definition mapped8 (m : word -> option byte) (a : Z) : Prop :=
  forall i, (0 <= i < 8)%Z -> m (Z_to_bv 64 (a + i)%Z) <> None.

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.

(* [comment removed for export] *)
Definition shadow_ok (m : word -> option byte) (a n : Z) : Prop :=
  exists (ng : nat) (lastb : Z),
    ((a + n - 1) / 8 - a / 8 = Z.of_nat ng)%Z /\
    bytes_at rsegs m (a / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) /\
    (lastb = 0 \/ ((a + n - 1) mod 8 < lastb <= 7))%Z.

Lemma bytes_at_app_l : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply (proj1 (bytes_at_app rsegs m a l1 l2)) in H. tauto. Qed.
Lemma bytes_at_app_r : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m (a + Z.of_nat (length l1)) l2.
Proof. intros m a l1 l2 H. apply (proj1 (bytes_at_app rsegs m a l1 l2)) in H. tauto. Qed.

(* [comment removed for export] *)
Lemma shadow_zero_window : forall m A ng lastb (i w : nat),
  bytes_at rsegs m A (zeros ng ++ [Z_to_bv 8 lastb]) ->
  (i + w <= ng)%nat \/ ((i + w <= S ng)%nat /\ lastb = 0%Z) ->
  bytes_at rsegs m (A + Z.of_nat i) (zeros w).
Proof.
  intros m A ng lastb i w H Hw.
  assert (H' : bytes_at rsegs m A (zeros (S ng)) \/ (i + w <= ng)%nat).
  { destruct Hw as [Hw | [Hw ->]]; [right; exact Hw | left].
    replace (zeros (S ng)) with (zeros ng ++ [Z_to_bv 8 0]); [exact H|].
    replace (S ng) with (ng + 1)%nat by lia. rewrite zeros_app. reflexivity. }
  destruct H' as [H' | Hle].
  - replace (zeros (S ng)) with (zeros i ++ (zeros w ++ zeros (S ng - i - w))) in H'.
    2:{ rewrite <- !zeros_app. f_equal. lia. }
    apply bytes_at_app_r in H'. rewrite zeros_length in H'. apply bytes_at_app_l in H'. exact H'.
  - apply bytes_at_app_l in H.
    replace (zeros ng) with (zeros i ++ (zeros w ++ zeros (ng - i - w))) in H.
    2:{ rewrite <- !zeros_app. f_equal. lia. }
    apply bytes_at_app_r in H. rewrite zeros_length in H. apply bytes_at_app_l in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma shadow_nth : forall ng lastb i,
  (i <= ng)%nat ->
  nth_error (zeros ng ++ [Z_to_bv 8 lastb]) i = Some (if (i <? ng)%nat then Z_to_bv 8 0 else Z_to_bv 8 lastb).
Proof.
  intros ng lastb i Hi. destruct (Nat.ltb_spec i ng).
  - rewrite nth_error_app1 by (rewrite zeros_length; lia). apply zeros_nth. lia.
  - rewrite nth_error_app2 by (rewrite zeros_length; lia). rewrite zeros_length. replace (i - ng)%nat with 0%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma signed_small : forall z, (0 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia. destruct (Z.ltb_spec0 z (2^63)); lia. Qed.

(* [comment removed for export] *)
Lemma sxb_small : forall v, (0 <= v < 128)%Z -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N N.pred].
  change (2^8)%Z with 256%Z. change (256 / 2)%Z with 128%Z.
  rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_roundtrip8 : forall bs : list byte,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256)%Z with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.
Lemma le8_of_bytes8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
  change (2 ^ (8 * Z.of_nat 8))%Z with 18446744073709551616%Z in H1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. rewrite <- Hl. apply Z_to_le_bytes_roundtrip8.
Qed.
Lemma bytes8_word : forall bs : list byte, length bs = 8%nat -> exists w : word, bs = le8 w.
Proof. intros bs H. exists (le_bytes_to_word bs). symmetry. apply le8_of_bytes8. exact H. Qed.
