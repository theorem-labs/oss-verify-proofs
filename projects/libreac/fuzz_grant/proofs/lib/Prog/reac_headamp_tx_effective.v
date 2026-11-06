From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel reac_headamp_tx_effective_c.
Import ListNotations.
Open Scope Z_scope.

Lemma dflt_code : forall p, 0 <= p <= 2 ->
  Z.shiftl (Z.b2z ((p + -2) mod 18446744073709551616 <? 1)) 5 = dflt p.
Proof. intros p H. assert (p = 0 \/ p = 1 \/ p = 2) as [ E | [ E | E ] ] by lia; subst p; reflexivity. Qed.

Theorem reac_headamp_tx_effective_holds : reac_headamp_tx_effective_contract.
Proof.
  unfold reac_headamp_tx_effective_contract, REAC_HEADAMP_TX_EFFECTIVE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t ch p T -> -> -> HCH HP HT.
  assert (Ht : 0 <= t < 2^64).
  { destruct HT as [-> | (HL & H0 & H1 & _)].
    - split; [lia | reflexivity].
    - rewrite HL in H1. change (Z.of_nat 460) with 460 in H1. lia. }
  zstep. zstep.
  if_cases HC1; zify_cond HC1.
  - zstep.
    if_cases HC2; zify_cond HC2.
    + subst t. zstep. zstep. zstep. zstep.
      rewrite eff_t0 by lia. rewrite <- dflt_code by lia.
      finish.
    + destruct HT as [-> | (HL & HB)]; [lia|].
      zstep. zstep.
      if_cases HC3; zify_cond HC3.
      * zstep. zstep. zstep. zstep.
        rewrite eff_ch by lia. rewrite <- dflt_code by lia.
        finish.
      * set (sb := nth (Z.to_nat (144 + 3 * ch + p)) T (Z_to_bv 8 0)).
        set (vb := nth (Z.to_nat (3 * ch + p)) T (Z_to_bv 8 0)).
        assert (RD1 : ov_read_bytes rsegs m (wa (t + (144 + 3 * ch + p))) 1 = Some [sb]).
        { rewrite (bytes_at_read rsegs m t T (144 + 3 * ch + p) 1 HB) by lia.
          rewrite (firstn1_skipn_nth T _ (Z_to_bv 8 0)) by lia. reflexivity. }
        assert (RD2 : ov_read_bytes rsegs m (wa (t + (3 * ch + p))) 1 = Some [vb]).
        { rewrite (bytes_at_read rsegs m t T (3 * ch + p) 1 HB) by lia.
          rewrite (firstn1_skipn_nth T _ (Z_to_bv 8 0)) by lia. reflexivity. }
        zstep. zstep. zstep. zstep.
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
        zstep.
        cbv beta. zstep.
        if_cases HC4; zify_cond HC4.
        -- zstep. zstep. zstep. zstep.
           rewrite eff_cell by lia.
           unfold tb. fold sb. rewrite (proj2 (Z.eqb_eq _ _)) by exact HC4.
           rewrite <- dflt_code by lia.
           finish.
        -- zstep. zstep. zstep. zstep.
           rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
           zstep. zstep.
           rewrite eff_cell by lia.
           unfold tb. fold sb vb. rewrite (proj2 (Z.eqb_neq _ _)) by exact HC4.
           finish.
  - zstep. zstep.
    rewrite eff_p3 by lia.
    finish.
Qed.
