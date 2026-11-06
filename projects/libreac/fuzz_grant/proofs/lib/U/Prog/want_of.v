From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel reac_headamp_default_c want_of_c.
Import ListNotations.
Open Scope Z_scope.

Ltac trap_off H :=
  exfalso; rewrite ?Z.shiftl_mul_pow2 in H by lia; try change (2 ^ 1) with 2 in H;
  rewrite ?Z.mod_small in H by lia; rewrite ?zb_lxor_ones in H by lia; lia.

Theorem want_of_holds : reac_headamp_default_contract -> want_of_contract.
Proof.
  intros DFLT.
  unfold want_of_contract, WANT_OF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m w v ch p WS VS -> -> -> -> HCH HP HLW HBW HLV HBV.
  pose proof (bytes_at_bound rsegs m w WS HBW) as Hw. rewrite HLW in Hw. change (Z.of_nat 144) with 144 in Hw.
  pose proof (bytes_at_bound rsegs m v VS HBV) as Hv. rewrite HLV in Hv. change (Z.of_nat 144) with 144 in Hv.
  change (2 ^ 64) with 18446744073709551616 in Hw, Hv.
  zstep. zstep. zstep. zstep.
  if_cases HT1; zify_cond HT1.
  { trap_off HT1. }
  zstep. zstep.
  if_cases HT2; zify_cond HT2.
  { exfalso. lia. }
  zstep. zstep. zstep.
  if_cases HT3; zify_cond HT3.
  { trap_off HT3. }
  rewrite ?Z.shiftl_mul_pow2 by lia. try change (2 ^ 1) with 2.
  set (wb := nth (Z.to_nat (3 * ch + p)) WS (Z_to_bv 8 0)).
  set (vb := nth (Z.to_nat (3 * ch + p)) VS (Z_to_bv 8 0)).
  assert (RD1 : ov_read_bytes rsegs m (wa (w + (3 * ch + p))) 1 = Some [wb]).
  { rewrite (bytes_at_read rsegs m w WS (3 * ch + p) 1 HBW) by lia.
    rewrite (firstn1_skipn_nth WS _ (Z_to_bv 8 0)) by lia. reflexivity. }
  assert (RD2 : ov_read_bytes rsegs m (wa (v + (3 * ch + p))) 1 = Some [vb]).
  { rewrite (bytes_at_read rsegs m v VS (3 * ch + p) 1 HBV) by lia.
    rewrite (firstn1_skipn_nth VS _ (Z_to_bv 8 0)) by lia. reflexivity. }
  zstep. zstep. zstep.
  if_cases HC; zify_cond HC.
  - zstep. zstep.
    eapply evt_mono.
    + eapply DFLT; [reflexivity | lia].
    + intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
      unfold want, tb. fold wb. rewrite (proj2 (Z.eqb_eq _ _)) by exact HC. reflexivity.
  - zstep. zstep.
    if_cases HT4; zify_cond HT4.
    { trap_off HT4. }
    zstep. zstep. zstep.
    if_cases HT5; zify_cond HT5.
    { trap_off HT5. }
    zstep. zstep. zstep.
    replace (want WS VS ch p) with (bv_unsigned vb)
      by (unfold want, tb; fold wb vb; rewrite (proj2 (Z.eqb_neq _ _)) by exact HC; reflexivity).
    finish.
Qed.
