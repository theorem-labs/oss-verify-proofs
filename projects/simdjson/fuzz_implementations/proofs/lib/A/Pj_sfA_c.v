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

Lemma sf_k2_machine_bvA : forall e2 c, (-1074 <= e2 <= 972)%Z ->
  (c mod 18446744073709551616 = (e2 * 631305 - 261663) mod 18446744073709551616)%Z ->
  bv_swrap 32 (Z.shiftr (bv_swrap 32 c) 21) = sf_k2 e2.
Proof. intros e2 c H HC. rewrite !swrap32_Z. exact (sf_k2_machine e2 c H HC). Qed.

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
  Notation FIN := (sf_fin ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m).
  Notation EXIT_DEC := (sf_exit_dec ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).

  Lemma sf_exit_inc : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt asegs POST (SFS 0xe90e0 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 6 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply FIN. assumption.
  Qed.

  Lemma sf_tz2 : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt asegs POST (SFS 0xe8ff4 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x4 x5 ya0 ya1 ya6 (b1 b2 : bool), (0 <= x4 <= 2)%Z -> (0 <= x5 <= 1)%Z ->
              evt asegs POST (SFS 0xe90c0 xt0 xt1 xt2 ya0 ya1 xa2 (Z_to_bv 64 (k + (8 * Z.b2z b1 + 4 * Z.b2z b2))) (Z_to_bv 64 x4) (Z_to_bv 64 x5) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros x4 x5 ya0 ya1 ya6 b1 b2 H4 H5.
      pose proof (b2z_rangeA b1). pose proof (b2z_rangeA b2).
      replace (q - 16)%Z with (q + -16)%Z in FR by lia.
      do 7 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
      eapply evt_eq; [| apply evt_done; apply (FIN (k + (8 * Z.b2z b1 + 4 * Z.b2z b2) + x4 + x5 + 1))];
        [num_st_eq | unfold SF_EMIN, SF_EMAX; lia]. }
    assert (K3 : forall x5 ya0 ya1 ya6 (b1 b2 : bool), (0 <= x5 <= 1)%Z ->
              evt asegs POST (SFS 0xe908c xt0 xt1 xt2 ya0 ya1 xa2 (Z_to_bv 64 k) (Z_to_bv 64 (8 * Z.b2z b1 + 4 * Z.b2z b2)) (Z_to_bv 64 x5) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros x5 ya0 ya1 ya6 b1 b2 H5.
      do 11 zstep.
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_rangeA.
      - zstep.
        eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_rangeA. }
    assert (K2 : forall ya0 ya1 ya6 (b1 b2 : bool),
              evt asegs POST (SFS 0xe905c xt0 xt1 xt2 ya0 ya1 xa2 (Z_to_bv 64 k) (Z_to_bv 64 (4 * Z.b2z b2)) (Z_to_bv 64 (8 * Z.b2z b1)) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya6 b1 b2.
      do 10 zstep.
      replace (Z.lor ((8 * Z.b2z b1) mod 18446744073709551616) ((4 * Z.b2z b2) mod 18446744073709551616)) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity).
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_rangeA].
      - zstep.
        eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_rangeA]. }
    assert (K1 : forall ya0 ya1 ya6 (b1 : bool),
              evt asegs POST (SFS 0xe9028 xt0 xt1 xt2 ya0 ya1 xa2 (Z_to_bv 64 k) xa4 (Z_to_bv 64 (Z.b2z b1)) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya6 b1.
      pose proof (b2z_rangeA b1) as R1.
      do 11 zstep. nnorm.
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K2 _ _ _ b1 _)]; num_st_eq.
      - zstep.
        eapply evt_eq; [| eapply (K2 _ _ _ b1 _)]; num_st_eq. }
    do 11 zstep.
    zstep. if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply K1]; num_st_eq.
    - zstep.
      eapply evt_eq; [| eapply K1]; num_st_eq.
  Qed.

  Lemma sf_short2 : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt asegs POST (SFS 0xe8f68 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 20 zstep.
    zstep. if_cases K1.
    { apply sf_tz2. unfold SF_EMIN, SF_EMAX; lia. }
    do 5 zstep.
    zstep. if_cases K2.
    { apply sf_exit_inc. unfold SF_EMIN, SF_EMAX; lia. }
    zstep.
    zstep. if_cases K3.
    { apply sf_exit_inc. unfold SF_EMIN, SF_EMAX; lia. }
    apply EXIT_DEC. unfold SF_EMIN, SF_EMAX; lia.
  Qed.

  Lemma sf_short : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt asegs POST (SFS 0xe8f1c xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 e2) (Z_to_bv 64 2147450880) xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR SZ.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k2_range e2 HE) as HK.
    do 8 zstep.
    zstep.
    rewrite (sf_k2_machine_bvA e2 _ HE) by (Z.div_mod_to_equations; lia).
    set (k := sf_k2 e2) in *.
    do 4 zstep.
    nnorm.
    destruct (image_readable_b asegs m (Z.to_nat 9904) 0x29ec0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    assert (TZ : Z.of_nat (length tb) = 9904%Z) by (rewrite TL; apply Z2Nat.id; lia). clear TL.

    zastep. zastep. zastep. zastep. if_false.
    zstep. zstep.
    apply sf_short2. exact HK.
  Qed.
End SF.
