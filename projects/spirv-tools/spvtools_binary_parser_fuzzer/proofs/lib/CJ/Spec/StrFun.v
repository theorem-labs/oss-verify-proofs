(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: l' => if bv_unsigned b =? c then Some 0%nat
               else match find_byte c l' with Some i => Some (S i) | None => None end
  end.

Definition memchr_res (A : Z) (c : Z) (n : Z) (buf : list byte) : Z :=
  match find_byte c (firstn (Z.to_nat n) buf) with Some i => A + Z.of_nat i | None => 0 end.

Definition memchr_ok (A c n : Z) (buf : list byte) : Prop :=
  match find_byte c (firstn (Z.to_nat n) buf) with
  | Some j => (n <= Z.of_nat (length buf) \/
               Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= Z.of_nat (length buf))%Z
  | None => (n <= Z.of_nat (length buf))%Z
  end.

Definition strnlen_res (n : Z) (buf : list byte) : Z :=
  match find_byte 0 (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i | None => n end.

Section NulTerminated.
  Variables (A n : Z) (str slack : list byte).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.

End NulTerminated.

Fixpoint strncmp_walk (l r : list byte) (k : nat) {struct l} : option Z :=
  match l, r with
  | a :: l', b :: r' =>
      if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%bool
      then Some (bv_unsigned a - bv_unsigned b)
      else match k with O => Some (bv_unsigned a - bv_unsigned b) | S k' => strncmp_walk l' r' k' end
  | _, _ => None
  end.
Definition strncmp_model (l r : list byte) (n : Z) : option Z :=
  if n =? 0 then Some 0 else strncmp_walk l r (Z.to_nat (n - 1)).

Fixpoint memcmp_model (l r : list byte) (n : nat) {struct n} : option Z :=
  match n with
  | O => Some 0
  | S n' =>
      match l, r with
      | a :: l', b :: r' => if bv_unsigned a =? bv_unsigned b then memcmp_model l' r' n' else Some (bv_unsigned a - bv_unsigned b)
      | _, _ => None
      end
  end.

Section WithSegs.
Variable segs : list MemImageType.Segment.

Lemma u8arr_write_bytes : forall m A bs (i : Z) xs,
  u8arr segs m A bs -> (0 <= i)%Z -> (Z.to_nat i + length xs <= length bs)%nat ->
  u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
  intros m A bs i xs [Hb Hw] Hi Hl. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma u8arr_store_ok_n : forall m A bs (i : Z) n a,
  u8arr segs m A bs -> (0 <= i)%Z -> (i + Z.of_nat n <= Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  store_ok segs m a n = true.
Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma rw_cells_CB_length : forall m A n bs, rw_cells segs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[H _] _]. cbn in H. tauto. Qed.
End WithSegs.

Definition filled (c : byte) (bs : list byte) (Q : Z -> Prop) : Prop :=
  forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j -> nth_error bs (Z.to_nat j) = Some c.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma forallb_zseq : forall n f, forallb f (zseq n) = true -> forall c, 0 <= c < Z.of_nat n -> f c = true.
Proof.
  intros n f H c Hc. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
  exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Definition list_Z_eqb (l1 l2 : list Z) : bool := if list_eq_dec Z.eq_dec l1 l2 then true else false.

Definition BC4 := 16843009.
Definition BC8 := 72340172838076673.

Definition copied (src bs : list byte) (k : nat) : Prop :=
  length bs = length src /\ firstn k bs = firstn k src.

Lemma copied_0 : forall src bs, length bs = length src -> copied src bs 0.
Proof. intros src bs H. split; [exact H| reflexivity]. Qed.

Lemma copied_all : forall src bs k, copied src bs k -> (length src <= k)%nat -> bs = src.
Proof.
  intros src bs k [Hl Hf] Hk. rewrite <- (firstn_all2 (n:=k) bs) by lia. rewrite <- (firstn_all2 (n:=k) src) by lia. exact Hf.
Qed.

Lemma firstn_app_len : forall {X} (a b : list X) k, k = length a -> firstn k (a ++ b) = a.
Proof. intros X a b k ->. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma app_firstn_mid_skipn : forall {X} (l : list X) p k,
  firstn p l ++ firstn k (skipn p l) ++ skipn (p + k) l = l.
Proof.
  intros X l p k. rewrite <- (firstn_skipn p l) at 4. f_equal.
  replace (skipn (p + k) l) with (skipn k (skipn p l)) by (rewrite skipn_skipn; f_equal; lia). apply firstn_skipn.
Qed.

Lemma copied_upd : forall src bs p xs,
  copied src bs p -> firstn (length xs) (skipn p src) = xs -> (p + length xs <= length src)%nat ->
  copied src (upd_bytes bs p xs) (p + length xs).
Proof.
  intros src bs p xs [Hl Hf] Hx Hp. split.
  - rewrite upd_bytes_length by lia. exact Hl.
  - unfold upd_bytes. rewrite app_assoc.
    assert (L1 : length (firstn p bs ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
    rewrite (firstn_app_len (firstn p bs ++ xs)) by lia.
    transitivity (firstn (p + length xs) (firstn p src ++ xs ++ skipn (p + length xs) src)).
    + assert (L2 : length (firstn p src ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
      rewrite app_assoc, (firstn_app_len (firstn p src ++ xs)) by lia. rewrite Hf. reflexivity.
    + f_equal. etransitivity; [ | apply (app_firstn_mid_skipn src p (length xs))]. rewrite Hx. reflexivity.
Qed.

Lemma copied_updZ : forall src bs (P : Z) xs,
  copied src bs (Z.to_nat P) -> (0 <= P)%Z -> firstn (length xs) (skipn (Z.to_nat P) src) = xs ->
  (Z.to_nat P + length xs <= length src)%nat ->
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat (length xs))).
Proof.
  intros src bs P xs HC HP Hx Hl. replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
  apply copied_upd; assumption.
Qed.

Lemma window_ex : forall (l : list byte) (i : Z) (k : nat), (Z.to_nat i + k <= length l)%nat ->
  exists xs, firstn k (skipn (Z.to_nat i) l) = xs /\ length xs = k.
Proof. intros l i k H. eexists. split; [reflexivity|]. rewrite firstn_length, skipn_length. lia. Qed.

Lemma window_nth : forall (l xs : list byte) (base : Z) (k c : nat) (i : Z),
  firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c < k)%nat -> i = base + Z.of_nat c ->
  nth_error l (Z.to_nat i) = nth_error xs c.
Proof.
  intros l xs base k c i H Hb Hc ->. rewrite <- H. rewrite nth_error_firstn.
  replace (Nat.ltb c k) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma window_sub : forall (l xs : list byte) (base : Z) (k c j : nat) (i : Z),
  firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c + j <= k)%nat -> i = base + Z.of_nat c ->
  firstn j (skipn (Z.to_nat i) l) = firstn j (skipn c xs).
Proof.
  intros l xs base k c j i H Hb Hc ->. rewrite <- H.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn by lia. f_equal; [lia|]. f_equal. lia.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 2^32.
Proof. reflexivity. Qed.
Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma le_bytes_to_word4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (le_bytes_to_word [b0;b1;b2;b3]) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Proof.
  intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite unsigned_lit by lia. lia.
Qed.

Lemma lw_unsigned4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word [b0;b1;b2;b3]))) =
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof.
  intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word4 by reflexivity.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite bv_swrap32_eq. change (bv_wrap 64 ?x) with (x mod 2^64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma le4_of_mod32 : forall (v : word) (bs : list byte), length bs = 4%nat ->
  bv_unsigned v mod 2^32 = le_val (map bv_unsigned bs) -> le4 v = bs.
Proof.
  intros v bs Hl Hv. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). change (2 ^ 32) with (2^32) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le1_of_mod8 : forall (v : word) (b : byte), bv_unsigned v mod 2^8 = bv_unsigned b -> le1 v = [b].
Proof.
  intros v b Hv. unfold le1. rewrite <- (Z_to_le_bytes_mod 1 _ 8) by (cbn; lia). change (2^8) with (2^8) in *. rewrite Hv.
  cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma le1_zxb : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. apply le1_of_mod8. pose proof (byte_range b). rewrite unsigned_lit by lia. apply Z.mod_small. cbn. lia. Qed.

Lemma le4_lw : forall w : list byte, length w = 4%nat -> le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
  apply le4_of_mod32; [reflexivity|]. rewrite lw_unsigned4. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  Z.div_mod_to_equations. lia.
Qed.

Lemma lor_add : forall hi lo k, 0 <= k -> 0 <= lo < 2^k -> hi mod 2^k = 0 -> Z.lor hi lo = hi + lo.
Proof.
  intros hi lo k Hk Hlo Hhi.
  assert (HL : Z.land hi lo = 0).
  { rewrite <- (Z.mod_small lo (2^k)) by lia. rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
  pose proof (Z.add_lor_land hi lo). lia.
Qed.
Lemma lor_add' : forall lo hi k, 0 <= k -> 0 <= lo < 2^k -> hi mod 2^k = 0 -> Z.lor lo hi = lo + hi.
Proof. intros. rewrite Z.lor_comm, (lor_add hi lo k); lia. Qed.

Lemma land_single_bit : forall x k, 0 <= x -> 0 <= k ->
  Z.land x (2^k) = if x mod 2^(k+1) <? 2^k then 0 else 2^k.
Proof.
  intros x k Hx Hk.
  assert (Hpk : 0 < 2^k < 2^(k+1)). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]. }
  rewrite (Z.land_comm x), <- (land_mod_pow2_r (2^k) x (k+1)) by lia.
  set (r := x mod 2^(k+1)).
  assert (Hr : 0 <= r < 2^(k+1)) by (subst r; apply Z.mod_pos_bound; lia).
  rewrite Z.pow_add_r in Hr by lia. change (2^1) with 2 in Hr.
  destruct (Z.ltb_spec0 r (2^k)) as [Hl|Hl].
  - rewrite Z.land_comm. apply zb_land_pow2_small; lia.
  - replace r with (Z.lor (2^k) (r - 2^k)).
    2:{ rewrite lor_add with (k := k); try lia. rewrite Z.mod_same; lia. }
    rewrite Z.land_lor_distr_r, Z.land_diag, (Z.land_comm (2^k)), zb_land_pow2_small by lia. apply Z.lor_0_r.
Qed.

Lemma land_bit_2 : forall x, 0 <= x -> Z.land x 2 = if x mod 4 <? 2 then 0 else 2.
Proof. intros x Hx. exact (land_single_bit x 1 Hx ltac:(lia)). Qed.
Lemma land_bit_4 : forall x, 0 <= x -> Z.land x 4 = if x mod 8 <? 4 then 0 else 4.
Proof. intros x Hx. exact (land_single_bit x 2 Hx ltac:(lia)). Qed.
Lemma land_bit_8 : forall x, 0 <= x -> Z.land x 8 = if x mod 16 <? 8 then 0 else 8.
Proof. intros x Hx. exact (land_single_bit x 3 Hx ltac:(lia)). Qed.

Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (2^1 - 1) at 1. rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

End AC_1.
