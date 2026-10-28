(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig SjPjBeta.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs.
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
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (sf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma sf_fin : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    POST (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 (Z_to_bv 64 ((x mod 18446744073709551616) mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (ret_pc ra) fc None m (seg_rom usegs)).
  Proof.
    intros. unfold sf_post. rewrite mod64_mod32.
    do 14 eexists. exists x. split; [reflexivity| assumption].
  Qed.

  Lemma sf_exit : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt usegs POST (SFS 0x5b4d8 xt0 xt1 xt2 xa0 (Z_to_bv 64 x) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI. intros. zstep. zstep. zstep. apply evt_done. apply sf_fin. assumption. Qed.

  Lemma sf_exit_dec : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt usegs POST (SFS 0x5b5c0 xt0 xt1 xt2 xa0 (Z_to_bv 64 x) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI. intros. do 4 zstep. apply evt_done. apply sf_fin. assumption. Qed.

  Lemma sf_tz1 : forall k xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt usegs POST (SFS 0x5b384 xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x ya0 ya2 ya3 ya4 ya5 ya6, (-324 <= x <= 307)%Z ->
              evt usegs POST (SFS 0x5b464 xt0 xt1 xt2 ya0 (Z_to_bv 64 x) ya2 ya3 ya4 ya5 ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros x ya0 ya2 ya3 ya4 ya5 ya6 HX.
      do 4 zstep. apply evt_done. apply sf_fin. unfold SF_EMIN, SF_EMAX. lia. }
    assert (K3 : forall x3 x4 ya0 ya2 ya5 ya6, (0 <= x3 <= 2)%Z -> (0 <= x4 <= 12)%Z ->
              evt usegs POST (SFS 0x5b424 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) ya2 (Z_to_bv 64 x3) (Z_to_bv 64 x4) ya5 ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros x3 x4 ya0 ya2 ya5 ya6 H3 H4.
      do 14 zstep.
      lazymatch goal with |- context [Z.b2z ?b] => pose proof (b2z_range b) as RB; set (bb := Z.b2z b) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K4 (k + x4 + x3 + bb)%Z)]; [num_st_eq | lia].
      - zstep.
        eapply evt_eq; [| eapply (K4 (k + x4 + x3 + bb)%Z)]; [num_st_eq | lia]. }
    assert (K2 : forall ya0 ya3 ya5 ya6 (b1 b2 : bool),
              evt usegs POST (SFS 0x5b3e8 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z b1)) ya3 (Z_to_bv 64 (Z.b2z b2)) ya5 ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya3 ya5 ya6 b1 b2.
      pose proof (b2z_range b1) as R1. pose proof (b2z_range b2) as R2.
      do 13 zstep. nnorm.
      match goal with |- context [Z.lor ?x ?y] =>
        lazymatch x with context [Z.b2z b1] =>
          replace (Z.lor x y) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity) end end.
      lazymatch goal with |- context [Z.b2z (?u <? ?v)] => pose proof (b2z_range (u <? v)) as RB; set (b3 := Z.b2z (u <? v)) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K3 (2 * b3)%Z (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z)]; [num_st_eq | lia | lia].
      - zstep.
        eapply evt_eq; [| eapply (K3 (2 * b3)%Z (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z)]; [num_st_eq | lia | lia]. }
    assert (K1 : forall ya0 ya2 ya3 ya4 ya5,
              evt usegs POST (SFS 0x5b3b8 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) ya2 ya3 ya4 ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya2 ya3 ya4 ya5.
      do 10 zstep.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply K2]; num_st_eq.
      - zstep.
        eapply evt_eq; [| eapply K2]; num_st_eq. }
    do 11 zstep.
    zstep. if_cases K.
    - eapply evt_eq; [| eapply K1]; num_st_eq.
    - zstep.
      eapply evt_eq; [| eapply K1]; num_st_eq.
  Qed.

  Lemma sf_step3b : forall k xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX)%Z ->
    evt usegs POST (SFS 0x5b4b4 xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 6 zstep.
    zstep. if_cases K1.
    { apply sf_exit_dec. exact HK. }
    zstep.
    zstep. if_cases K2.
    {   do 9 zstep. apply evt_done. apply sf_fin. exact HK. }
    apply sf_exit. exact HK.
  Qed.

  Lemma sf_step3 : forall k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX)%Z -> (6 <= beta <= 9)%Z ->
    evt usegs POST (SFS 0x5b474 xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 (Z_to_bv 64 beta) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 11 zstep.
    zstep. if_cases K.
    { apply sf_exit. exact HK. }

    assert (beta = 6 \/ beta = 7 \/ beta = 8 \/ beta = 9)%Z as [->|[->|[->| ->]]] by lia;
      (zstep; zstep; zstep; zstep; if_false; apply sf_step3b; exact HK).
  Qed.
End SF.
