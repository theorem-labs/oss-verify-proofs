(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit Pj_num_defs Pj_sf_a Pj_sf_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma sf_k2_machine_bv : forall e2 c, (-1074 <= e2 <= 972)%Z ->
  (c mod 18446744073709551616 = (e2 * 631305 - 261663) mod 18446744073709551616)%Z ->
  bv_swrap 32 (Z.shiftr (bv_swrap 32 c) 21) = sf_k2 e2.
Proof. intros e2 c H HC. rewrite !swrap32_Z. exact (sf_k2_machine e2 c H HC). Qed.

Section SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv psegs m.

  Notation POST := (sf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).

  Lemma sf_exit_inc : forall x xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt psegs POST (SFS 0x51330 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 x) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros. do 5 zstep. apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_tz2 : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt psegs POST (SFS 0x5124c xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x4 x5 ya0 ya1 ya6 (b1 b2 : bool), (0 <= x4 <= 2)%Z -> (0 <= x5 <= 1)%Z ->
              evt psegs POST (SFS 0x51318 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 (k + (8 * Z.b2z b1 + 4 * Z.b2z b2))) xa3 (Z_to_bv 64 x4) (Z_to_bv 64 x5) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros x4 x5 ya0 ya1 ya6 b1 b2 H4 H5.
      pose proof (b2z_range b1). pose proof (b2z_range b2).
      do 6 zstep.
      eapply evt_eq; [| apply evt_done; apply (sf_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
                                                  (k + (8 * Z.b2z b1 + 4 * Z.b2z b2) + x4 + x5 + 1))];
        [reflexivity | unfold SF_EMIN, SF_EMAX; lia]. }
    assert (K3 : forall x5 ya0 ya1 ya6 (b1 b2 : bool), (0 <= x5 <= 1)%Z ->
              evt psegs POST (SFS 0x512e4 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 k) xa3 (Z_to_bv 64 (8 * Z.b2z b1 + 4 * Z.b2z b2)) (Z_to_bv 64 x5) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros x5 ya0 ya1 ya6 b1 b2 H5.
      do 11 zstep.
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_range.
      - zstep.
        eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_range. }
    assert (K2 : forall ya0 ya1 ya6 (b1 b2 : bool),
              evt psegs POST (SFS 0x512b4 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 k) xa3 (Z_to_bv 64 (8 * Z.b2z b1)) (Z_to_bv 64 (4 * Z.b2z b2)) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya6 b1 b2.
      do 10 zstep.
      replace (Z.lor ((8 * Z.b2z b1) mod 18446744073709551616) ((4 * Z.b2z b2) mod 18446744073709551616)) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity).
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_range].
      - zstep.
        eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_range]. }
    assert (K1 : forall ya0 ya1 ya5 ya6 (b1 : bool),
              evt psegs POST (SFS 0x51280 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 k) xa3 (Z_to_bv 64 (Z.b2z b1)) ya5 ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya5 ya6 b1.
      pose proof (b2z_range b1) as R1.
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

  Lemma sf_short2 : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt psegs POST (SFS 0x511e4 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 13 zstep.
    zstep. if_cases K1.
    { apply sf_tz2. unfold SF_EMIN, SF_EMAX; lia. }
    do 5 zstep.
    zstep. if_cases K2.
    { apply sf_exit_inc. unfold SF_EMIN, SF_EMAX; lia. }
    zstep.
    zstep. if_cases K3.
    { apply sf_exit_inc. unfold SF_EMIN, SF_EMAX; lia. }
    apply sf_exit_dec; [exact MI| unfold SF_EMIN, SF_EMAX; lia].
  Qed.

  Lemma sf_short : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt psegs POST (SFS 0x5118c xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 e2) xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k2_range e2 HE) as HK.
    do 16 zstep.
    zstep.
    rewrite (sf_k2_machine_bv e2 _ HE) by (Z.div_mod_to_equations; lia).
    set (k := sf_k2 e2) in *.
    do 4 zstep.
    nnorm.
    destruct (image_readable_b psegs m (Z.to_nat 9904) 0x17988 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    destruct (bytes_u64_read psegs m 0x17988 tb (16 * (292 - k)) TB ltac:(lia) ltac:(rewrite TL; lia)) as [w0 RD0].
    zstep.
    apply sf_short2. exact HK.
  Qed.

  Lemma sf_body : forall E t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    (0 <= E <= 2047)%Z ->
    evt psegs POST (SFS 0x50ef0 t0 t1 t2 a0 (Z_to_bv 64 E) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof using MI.
    intros E t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HE.
    zstep.
    zstep. if_cases K0; zify_cond K0.
    {
      zstep. apply sf_main; [exact MI| lia]. }
    zstep.
    zstep. if_cases K1.
    { apply sf_short. lia. }
    do 4 zstep.
    apply sf_main; [exact MI| lia].
  Qed.
End SF.

Theorem sf_proof : sf_stmt.
Proof.
  unfold sf_stmt. intros. unfold SF_ENTRY. apply sf_body; assumption.
Qed.
