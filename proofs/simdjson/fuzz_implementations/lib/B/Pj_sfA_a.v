(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig SjPjBeta.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_num_akit Sj_num_amem Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].

Lemma mod64_mod32B : forall x, ((x mod 18446744073709551616) mod 4294967296 = x mod 4294967296)%Z.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma b2z_rangeB : forall b : bool, (0 <= Z.b2z b <= 1)%Z.
Proof. destruct b; cbn; lia. Qed.

Definition sf_postA1 (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (e mod 4294967296)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ (SF_EMIN <= e <= SF_EMAX)%Z.

Section SF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (jlo : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis QR : (0x10000 <= q - 16 /\ q < 2^47)%Z.
  Hypothesis FR : rw_cells bsegs m (q - 16) [CB 8 jlo; C8 ra].

  Notation POST := (sf_postA1 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra (Z_to_bv 64 (q + -16)) gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  Lemma sf_fin : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    POST (MS (mkR ra (Z_to_bv 64 q) gp tp xt0 xt1 xt2 s0 s1 xa0 (Z_to_bv 64 ((x mod 18446744073709551616) mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (ret_pc ra) fc None m (seg_rom bsegs)).
  Proof.
    intros. unfold sf_postA1. rewrite mod64_mod32B.
    do 14 eexists. exists x. split; [reflexivity| assumption].
  Qed.

  Lemma sf_exit : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt bsegs POST (SFS 0xf62ec xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 4 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_exit_dec : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt bsegs POST (SFS 0xf63ec xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 5 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_exit_inc : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt bsegs POST (SFS 0xf64f4 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 6 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_exit_sub : forall x xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt bsegs POST (SFS 0xf6510 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 x) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
    do 10 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
    apply evt_done. apply sf_fin. assumption.
  Qed.

  Lemma sf_tz1 : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt bsegs POST (SFS 0xf6190 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x ya0 ya1 ya2 ya4 ya5 ya6 ya7, (-324 <= x <= 307)%Z ->
              evt bsegs POST (SFS 0xf6270 xt0 xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 x) ya4 ya5 ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros x ya0 ya1 ya2 ya4 ya5 ya6 ya7 HX. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
      do 5 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
      apply evt_done. apply sf_fin. unfold SF_EMIN, SF_EMAX. lia. }
    assert (K3 : forall x3 x4 ya0 ya1 ya5 ya6 ya7, (0 <= x3 <= 2)%Z -> (0 <= x4 <= 12)%Z ->
              evt bsegs POST (SFS 0xf6230 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 x3) (Z_to_bv 64 k) (Z_to_bv 64 x4) ya5 ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros x3 x4 ya0 ya1 ya5 ya6 ya7 H3 H4.
      do 14 zstep.
      lazymatch goal with |- context [Z.b2z ?b] => pose proof (b2z_rangeB b) as RB; set (bb := Z.b2z b) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K4 (k + x4 + x3 + bb)%Z)]; [num_st_eq | lia].
      - zstep.
        eapply evt_eq; [| eapply (K4 (k + x4 + x3 + bb)%Z)]; [num_st_eq | lia]. }
    assert (K2 : forall ya0 ya4 ya5 (b1 b2 : bool),
              evt bsegs POST (SFS 0xf61f4 xt0 xt1 xt2 ya0 (Z_to_bv 64 (Z.b2z b1)) (Z_to_bv 64 (Z.b2z b2)) (Z_to_bv 64 k) ya4 ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya4 ya5 b1 b2.
      pose proof (b2z_rangeB b1) as R1. pose proof (b2z_rangeB b2) as R2.
      do 13 zstep. nnorm.
      match goal with |- context [Z.lor ?x ?y] =>
        lazymatch x with context [Z.b2z b1] =>
          replace (Z.lor x y) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity) end end.
      lazymatch goal with |- context [Z.b2z (?u <? ?v)] => pose proof (b2z_rangeB (u <? v)) as RB; set (b3 := Z.b2z (u <? v)) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K3 (2 * b3)%Z (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z)]; [num_st_eq | lia | lia].
      - zstep.
        eapply evt_eq; [| eapply (K3 (2 * b3)%Z (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z)]; [num_st_eq | lia | lia]. }
    assert (K1 : forall ya0 ya1 ya2 ya4 ya5,
              evt bsegs POST (SFS 0xf61c4 xt0 xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 k) ya4 ya5 xa6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya2 ya4 ya5.
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

  Lemma sf_step3b : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX)%Z ->
    evt bsegs POST (SFS 0xf62c8 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 6 zstep.
    zstep. if_cases K1.
    { apply sf_exit_dec. exact HK. }
    zstep.
    zstep. if_cases K2.
    { apply sf_exit_sub. exact HK. }
    apply sf_exit. exact HK.
  Qed.

  Lemma sf_step3 : forall k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX)%Z -> (6 <= beta <= 9)%Z ->
    evt bsegs POST (SFS 0xf6288 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 (Z_to_bv 64 beta) xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 11 zstep.
    zstep. if_cases K.
    { apply sf_exit. exact HK. }

    assert (beta = 6 \/ beta = 7 \/ beta = 8 \/ beta = 9)%Z as [->|[->|[->| ->]]] by lia;
      (zstep; zstep; zstep; zstep; if_false; apply sf_step3b; exact HK).
  Qed.
End SF.
