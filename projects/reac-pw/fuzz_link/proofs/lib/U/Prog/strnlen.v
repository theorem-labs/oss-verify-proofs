From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import memchr_c strnlen_c.
Import ListNotations.
Open Scope Z_scope.

Theorem strnlen_holds : memchr_contract -> strnlen_contract.
Proof.
  intros MC. unfold strnlen_contract, STRNLEN, strnlen_post, strnlen_res.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sa n lo buf
    BUF OK HS HN ST LO SEP MI.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  assert (SR0 : 0 <= Sa < 2 ^ 64) by lia.
  assert (NR0 : 0 <= n < 2 ^ 64) by exact HN.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 9 zstep.
  call MC; [ rewrite (unsigned_lit Sa SR0); exact BUF | rewrite (unsigned_lit Sa SR0), (unsigned_lit n NR0); exact OK | assumption | ].
  rewrite (unsigned_lit Sa SR0), (unsigned_lit n NR0).
  unfold memchr_res.
  try change (bv_unsigned (Z_to_bv 64 0)) with 0. try change (0 mod 256) with 0.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
  - destruct (find_byte_Some _ _ _ FB) as (Hl & _ & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K; [exfalso; lia | ].
    do 6 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    replace (Sa + Z.of_nat i - Sa) with (Z.of_nat i) by lia.
    finish.
  - zstep. if_cases K; zify_cond K; [ | exfalso; lia].
    do 5 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
Qed.
