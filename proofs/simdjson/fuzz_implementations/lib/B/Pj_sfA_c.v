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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_num_akit Sj_num_amem Pj_defsA Pj_sfA_a Pj_sfA_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].

Lemma sf_k2_machine_bvB : forall e2 c, (-1074 <= e2 <= 972)%Z ->
  (c mod 18446744073709551616 = (e2 * 631305 - 261663) mod 18446744073709551616)%Z ->
  bv_swrap 32 (Z.shiftr (bv_swrap 32 c) 21) = sf_k2 e2.
Proof. intros e2 c H HC. rewrite !swrap32_Z. exact (sf_k2_machine e2 c H HC). Qed.

Section SF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (jlo : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis QR : (0x10000 <= q - 16 /\ q < 2^47)%Z.
  Hypothesis FR : rw_cells bsegs m (q - 16) [CB 8 jlo; C8 ra].
  Hypothesis SZ : shz m 0x29c80 9904.

  Notation POST := (sf_postA1 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra (Z_to_bv 64 (q + -16)) gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
  Notation FIN := (sf_fin ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m).
  Notation EXIT_DEC := (sf_exit_dec ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).
  Notation EXIT_INC := (sf_exit_inc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).

  Lemma sf_tz2 : forall k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt bsegs POST (SFS 0xf6404 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x ya0 ya1 ya2 ya4 ya5 ya6 ya7, (-324 <= x <= 307)%Z ->
              evt bsegs POST (SFS 0xf64dc xt0 xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 x) ya4 ya5 ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros x ya0 ya1 ya2 ya4 ya5 ya6 ya7 HX. replace (q - 16)%Z with (q + -16)%Z in FR by lia.
      do 5 zstep. replace (q + -16 + 16)%Z with q by lia. zstep.
      apply evt_done. apply FIN. unfold SF_EMIN, SF_EMAX. lia. }
    assert (K3 : forall x4 x5 ya0 ya1 ya2 ya6 ya7, (0 <= x4 <= 2)%Z -> (0 <= x5 <= 12)%Z ->
              evt bsegs POST (SFS 0xf64a4 xt0 xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 k) (Z_to_bv 64 x4) (Z_to_bv 64 x5) ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros x4 x5 ya0 ya1 ya2 ya6 ya7 H4 H5.
      do 12 zstep.
      lazymatch goal with |- context [Z.b2z ?b] => pose proof (b2z_rangeB b) as RB; set (bb := Z.b2z b) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K4 (k + x5 + x4 + bb)%Z)]; [num_st_eq | lia].
      - zstep.
        eapply evt_eq; [| eapply (K4 (k + x5 + x4 + bb)%Z)]; [num_st_eq | lia]. }
    assert (K2 : forall ya0 ya1 ya4 ya6 (b1 b2 : bool),
              evt bsegs POST (SFS 0xf6468 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 (Z.b2z b1)) (Z_to_bv 64 k) ya4 (Z_to_bv 64 (Z.b2z b2)) ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya4 ya6 b1 b2.
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
    assert (K1 : forall ya0 ya1 ya2 ya4 ya5 ya6,
              evt bsegs POST (SFS 0xf6438 xt0 xt1 xt2 ya0 ya1 ya2 (Z_to_bv 64 k) ya4 ya5 ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya1 ya2 ya4 ya5 ya6.
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

  Lemma sf_short2 : forall k b2 xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (0 <= b2 <= 3)%Z ->
    evt bsegs POST (SFS 0xf6394 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 b2) (Z_to_bv 64 k) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k b2 xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 11 zstep.
    zstep. if_cases K1.
    { apply sf_tz2. unfold SF_EMIN, SF_EMAX; lia. }
    assert (b2 = 0 \/ b2 = 1 \/ b2 = 2 \/ b2 = 3)%Z as [->|[->|[->| ->]]] by lia;
      (zstep; zstep; zstep; if_false;
       do 4 zstep;
       zstep; if_cases K2; [apply EXIT_INC; unfold SF_EMIN, SF_EMAX; lia|];
       zstep;
       zstep; if_cases K3; [apply EXIT_INC; unfold SF_EMIN, SF_EMAX; lia|];
       apply EXIT_DEC; unfold SF_EMIN, SF_EMAX; lia).
  Qed.

  Lemma sf_short : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt bsegs POST (SFS 0xf6300 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 e2) (Z_to_bv 64 2147450880) xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR SZ.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k2_range e2 HE) as HK.
    pose proof (sf_beta2_range e2 HE) as HB.
    pose proof (sf_prod_small e2 HE) as [_ P1].
    pose proof (sf_prod2_small e2 HE) as [_ P2].
    do 4 zstep.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mulc e2 631305) by lia.
    replace (Z_to_bv 64 (e2 mod 18446744073709551616 * 631305)) with (Z_to_bv 64 (e2 * 631305))
      by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; symmetry; apply mod64_mulc).
    zstep. if_false.

    do 5 zstep.
    rewrite (sf_k2_machine_bvB e2 _ HE) by (Z.div_mod_to_equations; lia).
    set (k := sf_k2 e2) in *.

    zstep. zstep. nnorm.
    zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zstep. zstep. zstep. zstep. nnorm.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].

    zstep. nnorm.
    destruct (image_readable_b bsegs m (Z.to_nat 9904) 0x29c80 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    assert (TZ : Z.of_nat (length tb) = 9904%Z) by (rewrite TL; apply Z2Nat.id; lia). clear TL.
    zastep. zastep. zastep. zastep. if_false.

    do 6 zstep.
    replace (bv_swrap 32 (Z.shiftr (bv_swrap 32 ((k mod 18446744073709551616 * 18446744073707809969) mod 18446744073709551616)) 19) + e2)%Z
      with (sf_beta2 e2) by (rewrite !swrap32_Z; symmetry; exact (sf_beta2_machine e2 HE)).
    set (b2 := sf_beta2 e2) in *.

    zstep. zstep.
    rewrite (swrap32_id (11 - b2)) by lia.
    zstep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].

    destruct (bytes_u64_read bsegs m 0x29c80 tb (16 * (292 - k)) TB ltac:(lia) ltac:(rewrite TZ; lia)) as [w0 RD0].
    zstep.
    clear RD0 TB TZ tb.
    zstep. zstep. zstep. zstep.
    apply sf_short2; [exact HK | exact HB].
  Qed.
End SF.
