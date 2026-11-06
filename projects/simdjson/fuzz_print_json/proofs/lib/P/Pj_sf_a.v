(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit Pj_num_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma mod64_mod32 : forall x, ((x mod 18446744073709551616) mod 4294967296 = x mod 4294967296)%Z.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma b2z_range : forall b : bool, (0 <= Z.b2z b <= 1)%Z.
Proof. destruct b; cbn; lia. Qed.

Section SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv psegs m.

  Notation POST := (sf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).

  Lemma sf_fin : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    POST (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 (Z_to_bv 64 ((x mod 18446744073709551616) mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (ret_pc ra) fc None m (seg_rom psegs)).
  Proof.
    intros. unfold sf_post. rewrite mod64_mod32.
    do 14 eexists. exists x. split; [reflexivity| assumption].
  Qed.

  Lemma sf_exit : forall x xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt psegs POST (SFS 0x51180 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 x) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros. zstep. zstep. zstep. apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_tz1 : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt psegs POST (SFS 0x51014 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x3 x4 ya0 ya1 ya5 (b1 b2 : bool), (0 <= x3 <= 2)%Z -> (0 <= x4 <= 1)%Z ->
              evt psegs POST (SFS 0x510e8 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 (k + (8 * Z.b2z b1 + 4 * Z.b2z b2))) (Z_to_bv 64 x3) (Z_to_bv 64 x4) ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros x3 x4 ya0 ya1 ya5 b1 b2 H3 H4.
      pose proof (b2z_range b1). pose proof (b2z_range b2).
      do 4 zstep. apply sf_exit. unfold SF_EMIN, SF_EMAX. lia. }
    assert (K3 : forall x4 ya0 ya1 ya5 (b1 b2 : bool), (0 <= x4 <= 1)%Z ->
              evt psegs POST (SFS 0x510ac xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 k) (Z_to_bv 64 (8 * Z.b2z b1 + 4 * Z.b2z b2)) (Z_to_bv 64 x4) ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros x4 ya0 ya1 ya5 b1 b2 H4.
      do 13 zstep.
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_range.
      - zstep.
        eapply evt_eq; [| eapply (K4 _ _ _ _ _ b1 b2)]; [num_st_eq | | ].
        + rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z. lia.
        + apply b2z_range. }
    assert (K2 : forall ya0 ya1 ya5 (b1 b2 : bool),
              evt psegs POST (SFS 0x5107c xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 k) (Z_to_bv 64 (8 * Z.b2z b1)) (Z_to_bv 64 (4 * Z.b2z b2)) ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya5 b1 b2.
      do 10 zstep.
      replace (Z.lor ((8 * Z.b2z b1) mod 18446744073709551616) ((4 * Z.b2z b2) mod 18446744073709551616)) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity).
      zstep. if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_range].
      - zstep.
        eapply evt_eq; [| eapply (K3 _ _ _ _ b1 b2)]; [num_st_eq | apply b2z_range]. }
    assert (K1 : forall ya0 ya1 ya4 ya5 (b1 : bool),
              evt psegs POST (SFS 0x51048 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z b1)) ya4 ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya4 ya5 b1.
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

  Lemma sf_exit_dec : forall x xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt psegs POST (SFS 0x5123c xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 x) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros. do 4 zstep. apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_step3 : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX)%Z ->
    evt psegs POST (SFS 0x510f8 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 11 zstep.
    zstep. if_cases K; zify_cond K.
    { apply sf_exit. exact HK. }
    do 7 zstep.
    zstep. if_cases K2; zify_cond K2.
    { apply sf_exit_dec. exact HK. }
    do 14 zstep.
    apply evt_done. apply sf_fin. exact HK.
  Qed.
End SF.
