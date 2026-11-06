From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memmove_c ListStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma ld_shl4 : forall x, (0 <= x)%Z -> Z.shiftl x 4 = (16 * x)%Z.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Definition ld_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (q : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 b1 b2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x146b4) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 a1
                  (Z_to_bv 64 q) b1 b2 a3 a4 a5 a6 a7 (Z_to_bv 64 (16 * bv_unsigned a1)) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ld_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V q : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V)] ->
  rw_cells rsegs m (V + 16 * bv_unsigned a1)%Z [C8 (Z_to_bv 64 q)] ->
  (bv_unsigned a0 + 8 <= bv_unsigned sp - 32)%Z ->
  (0 <= V)%Z -> (V + 16 * bv_unsigned a1 + 8 <= bv_unsigned sp - 32)%Z ->
  evt rsegs (ld_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 q m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14684) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V q ST LO LV LQ D1 V0 D2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1. cbn in RA1.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 10 step.
  rewrite (ld_shl4 (bv_unsigned a1)) by lia.
  remember (V + 16 * bv_unsigned a1)%Z as P eqn:HP.
  step. step.
  apply evt_done. unfold ld_mid1.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. exact FR.
Qed.

Lemma ld_hi : forall x n, (0 <= x < 2 ^ 64)%Z -> (64 <= n)%Z -> Z.testbit x n = false.
Proof. intros x n Hx Hn. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

Lemma ld_lxor : forall x, (0 <= x < 2 ^ 64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
  rewrite Z.sub_nocarry_ldiff.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
    destruct (Z_lt_le_dec n 64) as [H|H].
    + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite (ld_hi x n Hx H). reflexivity.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 64) as [H|H].
    + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    + rewrite (ld_hi x n Hx H). reflexivity.
Qed.

Lemma ld_cnt : forall (w : word) N, (0 <= bv_unsigned w < N)%Z -> (N < 2 ^ 31)%Z ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 N) +
    bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned w) 18446744073709551615)))))) 4) =
  Z_to_bv 64 (16 * (N - bv_unsigned w - 1)).
Proof.
  intros w N H1 H2. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R.
  rewrite ld_lxor by lia.
  rewrite (unsigned_lit N) by lia.
  rewrite (unsigned_lit (18446744073709551615 - bv_unsigned w)) by lia.
  replace (bv_swrap 32 (N + (18446744073709551615 - bv_unsigned w))) with (N - bv_unsigned w - 1)%Z.
  2: { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z.
       change (bv_modulus 32) with 4294967296%Z. Z.div_mod_to_equations. lia. }
  rewrite (unsigned_lit (N - bv_unsigned w - 1)) by lia.
  rewrite ld_shl4 by lia. reflexivity.
Qed.

Lemma ld_res_len : forall (us : list byte) (i N CAP : Z), (0 <= i < N)%Z -> (N <= CAP)%Z ->
  Z.of_nat (length us) = (16 * CAP)%Z ->
  Z.of_nat (length (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1))))) =
  (16 * CAP)%Z.
Proof.
  intros us i N CAP H1 H2 H3. unfold mm_result. rewrite upd_bytes_length; [lia|].
  unfold slice. rewrite length_firstn, length_skipn. lia.
Qed.

Definition ld_end (ra0 sp0 gp tp s00 s01 s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LA i V N CAP : Z) (us : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7 s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(V + 16 * i, V + 16 * (N - 1)); (LA + 8, LA + 12)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 CAP)]
    /\ u8arr rsegs m' V (mm_result us (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i)) (Z.to_nat (16 * (N - i - 1)))).

Lemma ld_run2 : memmove_contract ->
  forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 w0 w1 : word) (V N CAP : Z) (us : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m (bv_unsigned w0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  u8arr rsegs m V us -> Z.of_nat (length us) = (16 * CAP)%Z ->
  (0 <= bv_unsigned w1 < N)%Z -> (N <= CAP)%Z -> (CAP < 2 ^ 30)%Z -> (8 <= V)%Z ->
  (bv_unsigned w0 + 16 <= V \/ V + 16 * CAP <= bv_unsigned w0)%Z ->
  (bv_unsigned w0 + 16 <= bv_unsigned sp0 - 32)%Z -> (V + 16 * CAP <= bv_unsigned sp0 - 32)%Z ->
  (32 <= bv_unsigned sp0)%Z -> mem_inv rsegs m ->
  evt rsegs (ld_end ra0 sp0 gp tp s00 s01 s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned w0) (bv_unsigned w1)
               V N CAP us m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 w0 w1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (16 * bv_unsigned w1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x146b4) fc None m (seg_rom rsegs)).
Proof.
  intros MMV ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 w0 w1 V N CAP us FR LC ARR LUS HI HN HC HV DLV DLS DVS SP32 MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 w0) as RW0. unfold bv_modulus in RW0. cbn in RW0.
  pose proof (munch_refl [(V + 16 * bv_unsigned w1, V + 16 * (N - 1)); (bv_unsigned w0 + 8, bv_unsigned w0 + 12)]%Z m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  rewrite ?ls_sx32 by lia.
  do 5 step.
  rewrite (ld_cnt w1 N) by lia.
  step.
  assert (UA0 : bv_unsigned (Z_to_bv 64 (V + 16 * bv_unsigned w1)) = (V + 16 * bv_unsigned w1)%Z)
    by (apply unsigned_lit; lia).
  assert (UA1 : bv_unsigned (Z_to_bv 64 (V + 16 * bv_unsigned w1 + 16)) = (V + 16 * bv_unsigned w1 + 16)%Z)
    by (apply unsigned_lit; lia).
  assert (UA2 : bv_unsigned (Z_to_bv 64 (16 * (N - bv_unsigned w1 - 1))) = (16 * (N - bv_unsigned w1 - 1))%Z)
    by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MMV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V us);
      [ exact ARR | exact HV | rewrite UA1, UA2; lia | rewrite UA0, UA2; lia | rewrite UA2; lia | exact MI ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memmove_post in PO; rewrite ?UA0, ?UA1, ?UA2 in PO;
      replace (V + 16 * bv_unsigned w1 + 16 - V)%Z with (16 * bv_unsigned w1 + 16)%Z in PO by lia;
      replace (V + 16 * bv_unsigned w1 - V)%Z with (16 * bv_unsigned w1)%Z in PO by lia;
      pose proof (ld_res_len us (bv_unsigned w1) N CAP ltac:(lia) HN LUS) as LR;
      remember (mm_result us (Z.to_nat (16 * bv_unsigned w1 + 16)) (Z.to_nat (16 * bv_unsigned w1))
                  (Z.to_nat (16 * (N - bv_unsigned w1 - 1)))) as res eqn:Eres;
      revert ms' PO;
      post_call rsegs mm ]
  end.
  step. rewrite ?ls_sx32 by lia.
  step. step.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0
    by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  replace (N + -1)%Z with (N - 1)%Z in LC by lia.
  subst res.
  apply evt_done. unfold ld_end.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact LC | exact POST].
Qed.
