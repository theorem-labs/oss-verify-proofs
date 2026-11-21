(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stf_self : forall s t, set_tree_fc s t (tree_fc s t) = s.
Proof. intros s [| |]; destruct s; reflexivity. Qed.
Lemma stf_get : forall s t a, tree_fc (set_tree_fc s t a) t = a.
Proof. intros s [| |] a; reflexivity. Qed.
Lemma stf_tree_dl : forall s t a t', tree_dl (set_tree_fc s t a) t' = tree_dl s t'.
Proof. intros s [| |] a [| |]; reflexivity. Qed.
Lemma stf_Len : forall s t a t' n, Len (set_tree_fc s t a) t' n = Len s t' n.
Proof. intros. unfold Len. rewrite stf_tree_dl. reflexivity. Qed.

Lemma stf_set_Code : forall s t a n v,
  set_Code (set_tree_fc s t a) t n v = set_tree_fc s t (arr_set a n (wrap16 v)).
Proof. intros s [| |] a n v; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint gcode (f : Z -> Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S O => f 0 * 2 ^ 1
  | S k' => (f (Z.of_nat k') + gcode f k') * 2 ^ 1
  end.

Lemma gcode_S : forall f k, gcode f (S k) = (f (Z.of_nat k) + gcode f k) * 2 ^ 1.
Proof. intros f [|k]; [cbn [gcode]; change (Z.of_nat 0) with 0; lia | reflexivity]. Qed.

Lemma gcode_bound : forall f k, (forall i, 0 <= i < Z.of_nat k -> 0 <= f i < 65536) ->
  0 <= gcode f k <= 131070 * (2 ^ Z.of_nat k - 1).
Proof.
  intros f k. induction k as [|k IH]; intros H; [cbn; lia|].
  rewrite gcode_S. specialize (IH ltac:(intros; apply H; lia)).
  pose proof (H (Z.of_nat k) ltac:(lia)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. change (2 ^ 1) with 2. lia.
Qed.

Lemma gcode_lt32 : forall f k, (k <= 15)%nat -> (forall i, 0 <= i < Z.of_nat k -> 0 <= f i < 65536) ->
  0 <= gcode f k < 2 ^ 32.
Proof.
  intros f k Hk H. pose proof (gcode_bound f k H).
  assert (2 ^ Z.of_nat k <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 15) with 32768 in *. change (2 ^ 32) with 4294967296. lia.
Qed.

Definition NC (blc : arr) : arr := gen_codes_loop1 16%nat blc (arr_make (MAX_BITS + 1) 0) 0 1.

Lemma loop1_inv : forall blc fuel nc bits,
  (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  arr_len nc = 16 -> 1 <= Z.of_nat bits <= 16 -> (Z.of_nat fuel = 16 - Z.of_nat bits + 1)%Z ->
  (forall k, (1 <= k < bits)%nat -> arr_get nc (Z.of_nat k) = wrap16 (gcode (arr_get blc) k)) ->
  let nc' := gen_codes_loop1 fuel blc nc (gcode (arr_get blc) (Nat.pred bits)) (Z.of_nat bits) in
  arr_len nc' = 16 /\ (forall k, (1 <= k <= 15)%nat -> arr_get nc' (Z.of_nat k) = wrap16 (gcode (arr_get blc) k)).
Proof.
  intros blc fuel. induction fuel as [|fuel IH]; intros nc bits Hb Hlen Hbits Hfuel Hnc; [lia|].
  cbn [gen_codes_loop1]. unfold MAX_BITS.
  destruct (Z.leb_spec (Z.of_nat bits) 15) as [C|C].
  - cbv zeta.
    assert (Eg : wrap32 (Z.shiftl (gcode (arr_get blc) (Nat.pred bits) + arr_get blc (Z.of_nat bits - 1)) 1)
                 = gcode (arr_get blc) bits).
    { destruct bits as [|b]; [lia|]. cbn [Nat.pred]. rewrite gcode_S.
      replace (Z.of_nat (S b) - 1) with (Z.of_nat b) by lia.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.add_comm (gcode _ _)).
      rewrite wrap32_mod. apply Z.mod_small.
      pose proof (gcode_lt32 (arr_get blc) (S b) ltac:(lia) ltac:(intros; apply Hb; lia)) as G.
      rewrite gcode_S in G. exact G. }
    rewrite Eg.
    replace (Z.of_nat bits + 1) with (Z.of_nat (S bits)) by lia.
    apply (IH _ (S bits)); [exact Hb | rewrite arr_len_set; exact Hlen | lia | lia |].
    intros k Hk. rewrite arr_get_set. unfold arr_inb. rewrite Hlen.
    destruct (Nat.eq_dec k bits) as [->|Hne].
    + replace (Z.of_nat bits =? Z.of_nat bits) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (0 <=? Z.of_nat bits) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat bits <? 16) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + replace (Z.of_nat bits =? Z.of_nat k) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      apply Hnc. lia.
  - cbv zeta. split; [exact Hlen|]. intros k Hk. apply Hnc. lia.
Qed.

Lemma NC_spec : forall blc, (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  arr_len (NC blc) = 16
  /\ (forall k, (1 <= k <= 15)%nat -> arr_get (NC blc) (Z.of_nat k) = wrap16 (gcode (arr_get blc) k)).
Proof.
  intros blc Hb. unfold NC, MAX_BITS.
  pose proof (loop1_inv blc 16 (arr_make (15 + 1) 0) 1 Hb ltac:(rewrite arr_len_make; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(intros; lia)) as H.
  cbn [Nat.pred gcode Z.of_nat Pos.of_succ_nat] in H. exact H.
Qed.

Lemma NC_range : forall blc k, (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  1 <= k <= 15 -> 0 <= arr_get (NC blc) k < 65536.
Proof.
  intros blc k Hb Hk. destruct (NC_spec blc Hb) as [_ H].
  replace k with (Z.of_nat (Z.to_nat k)) by lia. rewrite H by lia. apply wrap16_range'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition brl (code res len : Z) : Z := bi_reverse_loop (Z.to_nat len) code res len.

Lemma bi_reverse_brl : forall code len, 1 <= len -> bi_reverse code len = brl code 0 len.
Proof. intros code len H. unfold bi_reverse, brl. rewrite Z.max_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land1_mod : forall code, Z.land code 1 = code mod 2 ^ 1.
Proof. intros code. change (Z.land code 1) with (Z.land code (Z.ones 1)). apply Z.land_ones. lia. Qed.

Lemma lor_bit_bound : forall res code n, 0 <= n -> 0 <= res < 2 ^ n -> 1 < 2 ^ n ->
  0 <= Z.lor (code mod 2 ^ 1) res < 2 ^ n.
Proof.
  intros res code n Hn Hr H1.
  pose proof (Z.mod_pos_bound code (2 ^ 1) ltac:(lia)). change (2 ^ 1) with 2 in *.
  apply (proj1 (lor_lxor_bound (code mod 2) res n ltac:(lia) Hr Hn)).
Qed.

(* [comment removed for export] *)
Lemma brl_step : forall code res len, 2 <= len -> 0 <= code -> 0 <= res ->
  Z.lor (code mod 2 ^ 1) res < 2 ^ 31 ->
  brl code res len = brl (code / 2 ^ 1) (Z.lor (code mod 2 ^ 1) res * 2 ^ 1) (len - 1).
Proof.
  intros code res len Hl Hc Hr Hb. unfold brl.
  replace (Z.to_nat len) with (S (Z.to_nat (len - 1))) by lia. cbn [bi_reverse_loop].
  replace (0 <? len - 1) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite land1_mod, Z.lor_comm. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  rewrite wrap32_mod, Z.mod_small; [reflexivity|].
  pose proof (Z.lor_nonneg (code mod 2 ^ 1) res). pose proof (Z.mod_pos_bound code (2 ^ 1) ltac:(lia)).
  change (2 ^ 32) with (2 * 2 ^ 31). change (2 ^ 1) with 2 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma brl_last : forall code res, 0 <= code -> 0 <= res -> Z.lor (code mod 2 ^ 1) res < 2 ^ 31 ->
  brl code res 1 = Z.lor (code mod 2 ^ 1) res.
Proof.
  intros code res Hc Hr Hb. unfold brl. change (Z.to_nat 1) with 1%nat. cbn [bi_reverse_loop].
  change (0 <? 1 - 1) with false. rewrite land1_mod, Z.lor_comm.
  pose proof (Z.lor_nonneg (code mod 2 ^ 1) res). pose proof (Z.mod_pos_bound code (2 ^ 1) ltac:(lia)).
  rewrite Z.shiftl_mul_pow2, wrap32_mod, Z.mod_small by (change (2 ^ 32) with (2 * 2 ^ 31); change (2 ^ 1) with 2 in *; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop2_S : forall f s0 t a nc mc n,
  gen_codes_loop2 (S f) (set_tree_fc s0 t a) t nc mc n =
    if n <=? mc then
      let len := Len s0 t n in
      if len =? 0 then gen_codes_loop2 f (set_tree_fc s0 t a) t nc mc (n + 1)
      else
        let ncv := arr_get nc len in
        gen_codes_loop2 f (set_tree_fc s0 t (arr_set a n (wrap16 (bi_reverse ncv len)))) t
                        (arr_set nc len (wrap16 (ncv + 1))) mc (n + 1)
    else set_tree_fc s0 t a.
Proof.
  intros. cbn [gen_codes_loop2]. rewrite stf_Len.
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct (Len s0 t n =? 0); [reflexivity|]. rewrite stf_set_Code. reflexivity.
Qed.

Lemma loop2_0 : forall s t nc mc n, gen_codes_loop2 0 s t nc mc n = s.
Proof. reflexivity. Qed.

Lemma loop2_out : forall f s t nc mc n, mc < n -> gen_codes_loop2 f s t nc mc n = s.
Proof.
  intros [|f] s t nc mc n H; [reflexivity|]. cbn [gen_codes_loop2].
  destruct (Z.leb_spec n mc); [lia | reflexivity].
Qed.

(* [comment removed for export] *)

