(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit Sj_akit Sj_acps Sj_num_akit Sj_num_amem Pj_defsA Pj_sfA_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].

Lemma sf_k_machine_bvA : forall e2, (-1074 <= e2 <= 972)%Z ->
  bv_swrap 32 (Z.shiftr (bv_swrap 32 ((e2 mod 18446744073709551616 * 315653) mod 18446744073709551616)) 20) = sf_k e2.
Proof. intros e2 H. rewrite !swrap32_Z. exact (sf_k_machine e2 H). Qed.

Section SF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (jlo : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis QR : (0x10000 <= q - 16 /\ q < 2^47)%Z.
  Hypothesis FR : rw_cells asegs m (q - 16) [CB 8 jlo; C8 ra].
  Hypothesis SZ : shz m 0x29ec0 9904.

  Notation POST := (sf_postA1 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra (Z_to_bv 64 (q + -16)) gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Notation STEP3 := (sf_step3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).
  Notation TZ1 := (sf_tz1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).

  Lemma sf_par : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt asegs POST (SFS 0xe8d54 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 15 zstep.
    zstep. if_cases K3; zify_cond K3.
    { apply STEP3. unfold SF_EMIN, SF_EMAX; lia. }
    apply TZ1. unfold SF_EMIN, SF_EMAX; lia.
  Qed.

  Lemma sf_split : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt asegs POST (SFS 0xe8d2c xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    zstep. if_cases K1.
    -
      zstep. if_cases K2.
      { apply STEP3. unfold SF_EMIN, SF_EMAX; lia. }
      apply sf_par. lia.
    -
      do 4 zstep.
      zstep. if_cases K2.
      { apply TZ1. unfold SF_EMIN, SF_EMAX; lia. }
      do 3 zstep.
      apply STEP3. unfold SF_EMIN, SF_EMAX; lia.
  Qed.

  Lemma sf_mul : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt asegs POST (SFS 0xe8cc8 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 25 zstep.
    apply sf_split. exact HK.
  Qed.

  Lemma sf_main : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt asegs POST (SFS 0xe8c70 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 e2) (Z_to_bv 64 2147450880) xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR SZ.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k_range e2 HE) as HK.
    do 5 zstep.
    zstep.
    rewrite (sf_k_machine_bvA e2 HE).
    set (k := sf_k e2) in *.
    zstep. zstep. zstep. zstep.
    nnorm.
    destruct (image_readable_b asegs m (Z.to_nat 9904) 0x29ec0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).

    zastep. zastep. zastep. zastep.
    if_false.

    zastep. zastep. zastep. zastep. zastep. if_false.
    assert (TZ : Z.of_nat (length tb) = 9904%Z) by (rewrite TL; apply Z2Nat.id; lia). clear TL.
    zstep. zstep. zstep.
    apply sf_mul. exact HK.
  Qed.
End SF.
