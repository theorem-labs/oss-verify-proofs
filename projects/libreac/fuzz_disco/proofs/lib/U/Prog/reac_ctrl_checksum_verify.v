From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_ctrl_checksum_verify_c.
Import ListNotations.
Open Scope Z_scope.

Lemma neq0_64 : forall x, 0 < x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Lemma ltu_lit64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bs : list byte).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.
  Hypothesis Hlen : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs m (p + 18) bs.

  Definition Qv : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' a4' a5' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                    a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom rsegs).

  Lemma loop : forall n i x5,
    (i + n = 32)%nat -> (0 < n)%nat ->
    evt rsegs Qv
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
               (Z_to_bv 64 (18446744073709551615 - p)) (Z_to_bv 64 (18 + Z.of_nat i)) (Z_to_bv 64 50) x5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16070) fc None m (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros i x5 Hin Hn; [lia|].
    pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
    pose proof (psum_range bs i) as PR.
    step.
    rewrite (ltu_lit64 (18446744073709551615 - p) (18 + Z.of_nat i)) by lia.
    replace (18446744073709551615 - p <? 18 + Z.of_nat i) with false by (symmetry; apply Z.ltb_ge; lia).
    step. step. step. step. step.
    rewrite psum_S_zxb.
    assert (R1 : 0 < 18 + Z.of_nat i + 1 <= 2^64) by lia.
    assert (R2 : 0 < 50 <= 2^64) by lia.
    rewrite (eqb_le64 (18 + Z.of_nat i + 1) 50 R1 R2).
    destruct n as [|n].
    - replace (18 + Z.of_nat i + 1 =? 50) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb].
      replace i with 31%nat in * by lia.
      step. step. step. step.
      pose proof (psum_range bs 32) as R32. change (Z.of_nat 32) with 32 in R32.
      rewrite (fin_a0 (psum bs 32)) by lia.
      apply evt_done. unfold Qv, blocksum. do 5 eexists. reflexivity.
    - replace (18 + Z.of_nat i + 1 =? 50) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb].
      replace (18 + Z.of_nat i + 1) with (18 + Z.of_nat (S i)) by lia.
      replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia.
  Qed.
End Loop.

Theorem reac_ctrl_checksum_verify_holds : reac_ctrl_checksum_verify_contract.
Proof.
  unfold reac_ctrl_checksum_verify_contract, REAC_CTRL_CHECKSUM_VERIFY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bs
    Hp Hp50 -> Hlen HB.
  step.
  rewrite (neq0_64 p) by lia.
  step. step. step. step. step.
  rewrite (unsigned_lit p) by lia. rewrite (zb_lxor_ones p) by lia.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (psum bs 0)).
  change (Z_to_bv 64 18) with (Z_to_bv 64 (18 + Z.of_nat 0)).
  replace (p + 18) with (p + 18 + Z.of_nat 0) by lia.
  exact (loop ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bs
           Hp Hp50 Hlen HB 32 0 a5 eq_refl ltac:(lia)).
Qed.
