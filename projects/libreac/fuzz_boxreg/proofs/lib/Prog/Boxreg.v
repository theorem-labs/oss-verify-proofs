From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition bsub (bs : list byte) (k n : Z) : list byte := firstn (Z.to_nat n) (skipn (Z.to_nat k) bs).

Definition rd4 (bs : list byte) (k : Z) : Z := bv_swrap 32 (bytes_le_to_Z (bsub bs k 4)).

Definition bx_n (bs : list byte) : Z := rd4 bs 280.
Definition bx_fabric (bs : list byte) : Z := rd4 bs 284.
Definition bx_mac (bs : list byte) (i : Z) : list byte := bsub bs (56 * i) 6.
Definition bx_base (bs : list byte) (i : Z) : Z := rd4 bs (56 * i + 8).
Definition bx_nch (bs : list byte) (i : Z) : Z := rd4 bs (56 * i + 12).
Definition bx_established (bs : list byte) (i : Z) : Z := rd4 bs (56 * i + 16).
Definition bx_pinned (bs : list byte) (i : Z) : Z := rd4 bs (56 * i + 20).
Definition bx_name (bs : list byte) (i : Z) : list byte := bsub bs (56 * i + 24) 32.

Definition zero6 : list byte := repeat (Z_to_bv 8 0) 6.

Definition meets (b1 n1 b2 n2 : Z) : Prop := b1 < b2 + n2 /\ b2 < b1 + n1.

Definition boxreg_B1 (bs : list byte) : Prop := 0 <= bx_n bs <= 5.
Definition boxreg_B2 (bs : list byte) : Prop := 1 <= bx_fabric bs <= 40.
Definition boxreg_B3 (bs : list byte) : Prop :=
  forall i, 0 <= i < bx_n bs ->
    Z.even (bx_nch bs i) = true /\ 2 <= bx_nch bs i <= 40 /\ bx_nch bs i <= bx_fabric bs /\
    0 <= bx_base bs i /\ bx_base bs i + bx_nch bs i <= bx_fabric bs.
Definition boxreg_B4 (bs : list byte) : Prop :=
  forall i j, 0 <= i -> i < j -> j < bx_n bs ->
    ~ meets (bx_base bs i) (bx_nch bs i) (bx_base bs j) (bx_nch bs j).
Definition boxreg_B5 (bs : list byte) : Prop :=
  forall i j, 0 <= i -> i < j -> j < bx_n bs -> bx_mac bs i = zero6 \/ bx_mac bs i <> bx_mac bs j.
Definition boxreg_B6 (bs : list byte) : Prop :=
  forall i, 0 <= i < bx_n bs -> In (Z_to_bv 8 0) (bx_name bs i).
Definition boxreg_B7 (bs : list byte) : Prop :=
  forall i, 0 <= i < bx_n bs -> (bx_pinned bs i = 0 \/ bx_pinned bs i = 1) /\ bx_established bs i = 0.

Definition boxreg_B16 (bs : list byte) : Prop :=
  length bs = 288%nat /\ boxreg_B1 bs /\ boxreg_B2 bs /\ boxreg_B3 bs /\ boxreg_B4 bs /\ boxreg_B5 bs /\
  boxreg_B6 bs.

Definition boxreg_inv (bs : list byte) : Prop := boxreg_B16 bs /\ boxreg_B7 bs.

Lemma bsub_length : forall bs k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  length (bsub bs k n) = Z.to_nat n.
Proof. intros bs k n Hk Hn H. unfold bsub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma bsub_read : forall m r bs k n, bytes_at rsegs m r bs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (r + k)) (Z.to_nat n) = Some (bsub bs k n).
Proof. intros m r bs k n HB Hk Hn H. unfold bsub. apply bytes_at_read; [exact HB | lia | lia]. Qed.

Lemma le4_range : forall l : list byte, length l = 4%nat -> 0 <= bytes_le_to_Z l < 2^32.
Proof.
  intros l H. rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned l) (bytes_ok_map l)) as R.
  rewrite length_map, H in R. exact R.
Qed.

Lemma rd4_range : forall bs k, -2^31 <= rd4 bs k < 2^31.
Proof.
  intros bs k. unfold rd4, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  pose proof (Z.mod_pos_bound (bytes_le_to_Z (bsub bs k 4) + 2^31) (2^32) ltac:(lia)). lia.
Qed.

Lemma lw_rd4 : forall bs k, length (bsub bs k 4) = 4%nat ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word (bsub bs k 4))) = Z_to_bv 64 (rd4 bs k).
Proof.
  intros bs k H. rewrite sext_small. f_equal. rewrite signed_of_extract by lia. unfold rd4. f_equal.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (le4_range _ H) as R. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

Lemma B3_bounds : forall bs i, boxreg_B2 bs -> boxreg_B3 bs -> 0 <= i < bx_n bs ->
  0 <= bx_base bs i <= 38 /\ 2 <= bx_nch bs i <= 40 /\ bx_base bs i + bx_nch bs i <= 40.
Proof. intros bs i H2 H3 Hi. unfold boxreg_B2 in H2. destruct (H3 i Hi) as (_ & ? & ? & ? & ?). lia. Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.

Lemma lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

Lemma swrap_sub : forall a b, -2^31 <= a - b < 2^31 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = a - b.
Proof.
  intros a b H. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma swrap_add : forall a b, -2^31 <= a + b < 2^31 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)) = a + b.
Proof.
  intros a b H. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma rd4_read : forall m r bs k, bytes_at rsegs m r bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (r + k)) 4 = Some (bsub bs k 4).
Proof. intros m r bs k HB Hk H. exact (bsub_read m r bs k 4 HB Hk ltac:(lia) H). Qed.

Lemma addi_lit : forall a c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + c) = Z_to_bv 64 (a + c).
Proof. intros a c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma swrap_addi : forall a c, -2^31 <= a + c < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) + c) = a + c.
Proof.
  intros a c H. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma bytes_at_bsub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (bsub bs k n).
Proof.
  intros m a bs k n HB Hk Hn H. unfold bsub.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in HB.
  apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn in HB. replace (Z.of_nat (Init.Nat.min (Z.to_nat k) (length bs))) with k in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat k) bs)) in HB.
  apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.
