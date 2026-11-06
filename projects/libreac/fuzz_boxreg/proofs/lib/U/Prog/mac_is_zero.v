From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Step Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg mac_is_zero_c.
Import ListNotations.
Open Scope Z_scope.

Lemma miz_seqz_nz : forall x, x mod 2^64 <> 0 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x H. unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec (x mod 2^64) 1); [ | reflexivity ].
  pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). lia.
Qed.

Lemma miz_seqz_b0 : forall b : byte, bv_unsigned b = 0 -> v_sltiu (zxb b) 1 = Z_to_bv 64 1.
Proof. intros b H. unfold v_sltiu, zxb. rewrite H. reflexivity. Qed.

Lemma miz_seqz_b1 : forall b : byte, bv_unsigned b <> 0 -> v_sltiu (zxb b) 1 = Z_to_bv 64 0.
Proof.
  intros b H. unfold zxb. apply miz_seqz_nz.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite Z.mod_small by lia. exact H.
Qed.

Lemma miz_snez : forall p, 0 < p < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 p) = Z_to_bv 64 1.
Proof.
  intros p Hp. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit p) by lia.
  destruct (Z.ltb_spec (bv_unsigned (Z_to_bv 64 0)) p) as [_|N]; [ reflexivity | ].
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in N. lia.
Qed.

Lemma miz_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  apply unsigned_lit. lia.
Qed.

Lemma miz_nz : forall (l : list byte) (k : nat) (b : byte),
  nth_error l k = Some b -> bv_unsigned b <> 0 -> l <> zero6.
Proof.
  intros l k b Hk Hb E. subst l. unfold zero6 in Hk.
  apply nth_error_In, repeat_spec in Hk. subst b. apply Hb. reflexivity.
Qed.

Lemma miz_b0 : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma miz_zero6 : forall M : list byte, length M = 6%nat ->
  (forall j, 0 <= j < 6 -> nth_error M (Z.to_nat j) = Some (Z_to_bv 8 0)) -> M = zero6.
Proof.
  intros M HL HZ.
  destruct M as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|]]]]]]]; try discriminate HL.
  pose proof (HZ 0 ltac:(lia)) as H0. pose proof (HZ 1 ltac:(lia)) as H1. pose proof (HZ 2 ltac:(lia)) as H2.
  pose proof (HZ 3 ltac:(lia)) as H3. pose proof (HZ 4 ltac:(lia)) as H4. pose proof (HZ 5 ltac:(lia)) as H5.
  cbn in H0, H1, H2, H3, H4, H5.
  injection H0 as ->. injection H1 as ->. injection H2 as ->. injection H3 as ->. injection H4 as ->.
  injection H5 as ->. reflexivity.
Qed.

Definition miz_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (M : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom rsegs) /\
    ((M = zero6 /\ res = Z_to_bv 64 1) \/ (M <> zero6 /\ res = Z_to_bv 64 0)).

Ltac miz_close :=
  apply evt_done; cbv beta delta [miz_q mkR]; do 15 eexists; split; [ reflexivity | ].

Lemma miz_body : forall (k : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (M : list byte),
  0 <= k <= 5 -> 0 < p -> p + 6 <= 2^64 -> bytes_at rsegs m p M -> length M = 6%nat ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 (- p) -> a2 = Z_to_bv 64 1 ->
  a3 = Z_to_bv 64 (p + k) -> a4 = Z_to_bv 64 (p + k) -> a5 = Z_to_bv 64 (5 - k) ->
  (forall j, 0 <= j < k -> nth_error M (Z.to_nat j) = Some (Z_to_bv 8 0)) ->
  (k < 5 -> forall x3 x4 x5 x16 x17 : word,
     x3 = Z_to_bv 64 (p + (k + 1)) -> x4 = Z_to_bv 64 (p + (k + 1)) -> x5 = Z_to_bv 64 (5 - (k + 1)) ->
     (forall j, 0 <= j < k + 1 -> nth_error M (Z.to_nat j) = Some (Z_to_bv 8 0)) ->
     evt rsegs (miz_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m M)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 x3 x4 x5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x13b28) fc None m (seg_rom rsegs))) ->
  evt rsegs (miz_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m M)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b28) fc None m (seg_rom rsegs)).
Proof.
  intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p M
    Hk Hp Hp6 HM HL E0 E1 E2 E3 E4 E5 HZ K.
  subst a0 a1 a2 a3 a4 a5.
  destruct (nth_error M (Z.to_nat k)) as [b|] eqn:Hb; [ | apply nth_error_None in Hb; lia ].
  assert (R : ov_read_bytes rsegs m (wa (p + k)) 1 = Some [b]).
  { rewrite (bytes_at_read rsegs m p M k 1 HM) by lia. f_equal.
    rewrite <- (firstn_skipn_step M (Z.to_nat k) 0 b Hb). reflexivity. }
  step.
  if_cases HC; zify_cond HC; [ exfalso; Z.div_mod_to_equations; lia | ].
  step. step. step. step.
  rewrite miz_seqz_nz by (Z.div_mod_to_equations; lia).
  step.
  if_cases HD; zify_cond HD; [ exfalso; lia | ].
  step.
  if_cases HE; zify_cond HE; [ exfalso; Z.div_mod_to_equations; lia | ].
  step. step.
  if_cases HF; zify_cond HF; rewrite ?miz_ub in HF.
  - step. step. miz_close.
    right. split; [ exact (miz_nz M (Z.to_nat k) b Hb HF) | exact (miz_seqz_b1 b HF) ].
  - assert (HZ1 : forall j, 0 <= j < k + 1 -> nth_error M (Z.to_nat j) = Some (Z_to_bv 8 0)).
    { intros j Hj. destruct (Z.eq_dec j k) as [->|NE]; [ rewrite Hb, (miz_b0 b HF); reflexivity | apply HZ; lia ]. }
    step. step. step. step. step.
    if_cases HG; zify_cond HG.
    + eapply K; [ lia | word_eq_tac | word_eq_tac | word_eq_tac | exact HZ1 ].
    + step. step. miz_close.
      left. split; [ apply miz_zero6; [ exact HL | intros j Hj; apply HZ1; lia ] | exact (miz_seqz_b0 b HF) ].
Qed.

Lemma miz_loop : forall (d : nat) (k : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (M : list byte),
  d = Z.to_nat (5 - k) -> 0 <= k <= 5 -> 0 < p -> p + 6 <= 2^64 -> bytes_at rsegs m p M -> length M = 6%nat ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 (- p) -> a2 = Z_to_bv 64 1 ->
  a3 = Z_to_bv 64 (p + k) -> a4 = Z_to_bv 64 (p + k) -> a5 = Z_to_bv 64 (5 - k) ->
  (forall j, 0 <= j < k -> nth_error M (Z.to_nat j) = Some (Z_to_bv 8 0)) ->
  evt rsegs (miz_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m M)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b28) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p M
      Hd Hk Hp Hp6 HM HL E0 E1 E2 E3 E4 E5 HZ;
    (eapply miz_body; [ exact Hk | exact Hp | exact Hp6 | exact HM | exact HL | exact E0 | exact E1 | exact E2
                      | exact E3 | exact E4 | exact E5 | exact HZ | ]);
    intros Hk5 x3 x4 x5 x16 x17 E3' E4' E5' HZ'.
  - lia.
  - eapply IH with (k := k + 1); [ lia | lia | exact Hp | exact Hp6 | exact HM | exact HL | exact E0 | exact E1
                                 | exact E2 | exact E3' | exact E4' | exact E5' | exact HZ' ].
Qed.

Theorem mac_is_zero_holds : mac_is_zero_contract.
Proof.
  unfold mac_is_zero_contract, MAC_IS_ZERO.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p M
    E0 Hp0 HM HL.
  subst a0.
  pose proof (bytes_at_bound rsegs m p M HM) as PB. rewrite HL in PB. change (Z.of_nat 6) with 6 in PB.
  step. step. step. step. step.
  eapply (miz_loop 5 0) with (p := p) (M := M); [ reflexivity | lia | lia | lia | exact HM | exact HL | reflexivity
                         | rewrite unsigned_lit by lia; word_eq_tac | apply miz_snez; lia
                         | word_eq_tac | word_eq_tac | reflexivity | intros j Hj; lia ].
Qed.
