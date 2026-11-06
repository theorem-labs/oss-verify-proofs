From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import Cells Step Tac.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma find_byte_In0 : forall l : list byte, In (Z_to_bv 8 0) l -> exists j, find_byte 0 l = Some j.
Proof.
  induction l as [|b l IH]; intros H; [destruct H|].
  cbn. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|NE]; [eexists; reflexivity|].
  destruct H as [Eb|H]; [subst b; exfalso; apply NE; reflexivity|].
  destruct (IH H) as [j Hj]. rewrite Hj. eexists; reflexivity.
Qed.

Lemma memchr_name : forall A buf, length buf = 32%nat -> In (Z_to_bv 8 0) buf ->
  memchr_ok A (0 mod 256) 32 buf /\ exists j, (j < 32)%nat /\ memchr_res A (0 mod 256) 32 buf = A + Z.of_nat j.
Proof.
  intros A buf HL HI. change (0 mod 256) with 0. change (Z.to_nat 32) with 32%nat.
  unfold memchr_ok, memchr_res. change (Z.to_nat 32) with 32%nat.
  rewrite firstn_all2 by lia.
  destruct (find_byte_In0 buf HI) as [j Hj]. rewrite Hj.
  destruct (find_byte_Some 0 buf j Hj) as (Hl & _ & _).
  split; [left; rewrite HL; lia|]. exists j. split; [lia|reflexivity].
Qed.

Lemma memcmp_eq : forall (l r : list byte) n v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -255 <= v <= 255.
Proof.
  induction l as [|a l IH]; intros r n v Hl Hr Hm.
  - cbn in Hl. subst n. destruct r; [|discriminate]. cbn in Hm. injection Hm as <-. split; [tauto|lia].
  - destruct n as [|n]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    cbn in Hl, Hr, Hm. injection Hl as Hl. injection Hr as Hr.
    pose proof (byte_range a) as Ra. pose proof (byte_range b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH r n v Hl Hr Hm) as [Hiff Hv]. split; [|exact Hv].
      assert (Eab : a = b) by (apply bv_eq; exact E). subst b.
      split; intros H.
      * f_equal. apply Hiff, H.
      * injection H as H. apply Hiff, H.
    + injection Hm as <-. split; [|lia]. split; intros H; [lia|].
      injection H as -> _. exfalso. apply NE. reflexivity.
Qed.

Lemma bv_v_zero : forall v, -255 <= v <= 255 -> (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0)).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|NE]; [reflexivity|].
  apply Z.eqb_neq. intros H. apply NE. Z.div_mod_to_equations. lia.
Qed.

Lemma bsub_length6 : forall bs i, length bs = 288%nat -> 0 <= i < 5 -> length (bx_mac bs i) = 6%nat.
Proof. intros bs i HL Hi. unfold bx_mac. apply bsub_length; rewrite ?HL; lia. Qed.

Lemma bsub_length32 : forall bs i, length bs = 288%nat -> 0 <= i < 5 -> length (bx_name bs i) = 32%nat.
Proof. intros bs i HL Hi. unfold bx_name. apply bsub_length; rewrite ?HL; lia. Qed.

Lemma zero6_length : length zero6 = 6%nat.
Proof. reflexivity. Qed.

Lemma shl_shr32 : forall n, 0 <= n < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 32))) 32 = n.
Proof.
  intros n Hn. rewrite (unsigned_lit n) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma box_addr : forall r i, 0 <= r -> r + 288 <= 2^64 -> 0 <= i <= 5 ->
  Z_to_bv 64 (r + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 6)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 3))))
  = Z_to_bv 64 (r + 56 * i).
Proof.
  intros r i Hr Hr2 Hi. rewrite (unsigned_lit i) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (i * 2 ^ 6)) by lia. rewrite (unsigned_lit (i * 2 ^ 3)) by lia.
  f_equal. lia.
Qed.

Lemma land1_even : forall x, 0 <= x -> Z.even x = true -> Z.land x 1 = 0.
Proof.
  intros x Hx He. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  apply Z.even_spec in He. destruct He as [k ->]. rewrite Z.mul_comm. change (2 ^ 1) with 2. apply Z_mod_mult.
Qed.

Lemma Z_to_bv_neg_wrap : forall z, -2^63 <= z < 0 -> Z_to_bv 64 z = Z_to_bv 64 (z + 2^64).
Proof.
  intros z Hz. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia.
  rewrite Z.add_0_r. reflexivity.
Qed.

Lemma bsub_read_u : forall m r bs k n, bytes_at rsegs m r bs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (r + k)) (Z.to_nat n) = Some (bsub bs k n).
Proof. intros m r bs k n HB Hk Hn H. unfold bsub. apply bytes_at_read; [exact HB | lia | lia]. Qed.

Lemma rd4_read_u : forall m r bs k, bytes_at rsegs m r bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (r + k)) 4 = Some (bsub bs k 4).
Proof. intros m r bs k HB Hk H. exact (bsub_read_u m r bs k 4 HB Hk ltac:(lia) H). Qed.

Lemma bytes_at_bsub_u : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (bsub bs k n).
Proof.
  intros m a bs k n HB Hk Hn H. unfold bsub.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in HB.
  apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn in HB. replace (Z.of_nat (Init.Nat.min (Z.to_nat k) (length bs))) with k in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat k) bs)) in HB.
  apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma zero_ro_u : ro_bytes rsegs 0x10392 zero6.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma cell3_merge : forall m A a b v rest,
  rw_cells rsegs m A (a :: b :: C8 v :: rest) -> rw_cells rsegs m A (a :: b :: CB 8 (le8 v) :: rest).
Proof.
  intros m A a b v rest H.
  pose proof (rw_cells_merge rsegs m A [a; b] [C8 v] rest H) as M. exact M.
Qed.

Lemma land3_mod4 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x Hx H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma mul56 : forall x, 0 <= x <= 5 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 6)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 3))) = Z_to_bv 64 (56 * x).
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x * 2 ^ 6)) by lia. rewrite (unsigned_lit (x * 2 ^ 3)) by lia. f_equal. lia.
Qed.

Lemma not_lit : forall r, 0 <= r < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615) = Z_to_bv 64 (2^64 - 1 - r).
Proof.
  intros r Hr. rewrite (unsigned_lit r) by lia. rewrite zb_lxor_ones by lia. f_equal; try lia.
Qed.
