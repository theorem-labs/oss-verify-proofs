(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit Sj_akit Sj_acps Sj_num_akit Sj_num_amem Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].

Lemma mod64_mod32A : forall x, ((x mod 18446744073709551616) mod 4294967296 = x mod 4294967296)%Z.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma b2z_rangeA : forall b : bool, (0 <= Z.b2z b <= 1)%Z.
Proof. destruct b; cbn; lia. Qed.

Definition sf_postA1 (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (e mod 4294967296)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ (SF_EMIN <= e <= SF_EMAX)%Z.

Section SF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (jlo : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis QR : (0x10000 <= q - 16 /\ q < 2^47)%Z.
  Hypothesis FR : rw_cells asegs m (q - 16) [CB 8 jlo; C8 ra].

  Notation POST := (sf_postA1 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra (Z_to_bv 64 (q + -16)) gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  Lemma sf_fin : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    POST (MS (mkR ra (Z_to_bv 64 q) gp tp xt0 xt1 xt2 s0 s1 xa0 (Z_to_bv 64 ((x mod 18446744073709551616) mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (ret_pc ra) fc None m (seg_rom asegs)).
  Proof.
    intros. unfold sf_postA1. rewrite mod64_mod32A.
    do 14 eexists. exists x. split; [reflexivity| assumption].
  Qed.

  Lemma sf_exit : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt asegs POST (SFS 0xe3cd0 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 4 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_tz1 : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt asegs POST (SFS 0xe3b5c xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x3 x4 ya0 ya1 ya5 (b1 b2 : bool), (0 <= x3 <= 2)%Z -> (0 <= x4 <= 1)%Z ->
              evt asegs POST (SFS 0xe3c30 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 x3) (Z_to_bv 64 (k + (8 * Z.b2z b1 + 4 * Z.b2z b2))) (Z_to_bv 64 x4) ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros x3 x4 ya0 ya1 ya5 b1 b2 H3 H4.
      pose proof (b2z_rangeA b1). pose proof (b2z_rangeA b2).
      do 4 zstep. apply sf_exit. unfold SF_EMIN, SF_EMAX. lia. }
    assert (K3 : forall x4 ya0 ya1 ya5 (b1 b2 : bool), (0 <= x4 <= 1)%Z ->
              evt asegs POST (SFS 0xe3bf4 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 (8 * Z.b2z b1 + 4 * Z.b2z b2)) (Z_to_bv 64 k) (Z_to_bv 64 x4) ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros x4 ya0 ya1 ya5 b1 b2 H4.
      do 13 zstep.
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_rangeA.
      - zstep.
        eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_rangeA. }
    assert (K2 : forall ya0 ya1 ya5 (b1 b2 : bool),
              evt asegs POST (SFS 0xe3bc4 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 (4 * Z.b2z b2)) (Z_to_bv 64 k) (Z_to_bv 64 (8 * Z.b2z b1)) ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya5 b1 b2.
      do 10 zstep.
      replace (Z.lor ((8 * Z.b2z b1) mod 18446744073709551616) ((4 * Z.b2z b2) mod 18446744073709551616)) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity).
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_rangeA].
      - zstep.
        eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_rangeA]. }
    assert (K1 : forall ya0 ya1 (b1 : bool),
              evt asegs POST (SFS 0xe3b90 xt0 xt1 xt2 ya0 ya1 xa2 (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z b1)) xa5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 b1.
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

  Lemma sf_exit_dec : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt asegs POST (SFS 0xe3da4 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 5 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_step3 : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX)%Z ->
    evt asegs POST (SFS 0xe3c40 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 11 zstep.
    zstep. if_cases K; zify_cond K.
    { apply sf_exit. exact HK. }
    do 7 zstep.
    zstep. if_cases K2; zify_cond K2.
    { apply sf_exit_dec. exact HK. }
    replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 15 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. exact HK.
  Qed.
End SF.
