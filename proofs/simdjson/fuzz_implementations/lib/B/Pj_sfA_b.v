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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_num_akit Sj_num_amem Pj_defsA Pj_sfA_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].

Lemma sf_beta_machine_bvB : forall e2, (-1074 <= e2 <= 972)%Z ->
  bv_swrap 32 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (((2 - sf_k e2) * 1741647) mod 18446744073709551616)) 19) mod 18446744073709551616
               + e2 mod 18446744073709551616) = sf_beta e2.
Proof. intros e2 H. rewrite !swrap32_Z. exact (sf_beta_machine e2 H). Qed.

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
  Notation STEP3 := (sf_step3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).
  Notation TZ1 := (sf_tz1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q F fc m jlo MI QR FR).

  Lemma sf_par : forall k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (6 <= beta <= 9)%Z ->
    evt bsegs POST (SFS 0xf6154 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 (Z_to_bv 64 beta) xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 14 zstep.
    zstep. if_cases K3.
    { apply STEP3; [unfold SF_EMIN, SF_EMAX; lia | exact HB]. }
    apply TZ1; unfold SF_EMIN, SF_EMAX; lia.
  Qed.

  Lemma sf_split : forall k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (6 <= beta <= 9)%Z ->
    evt bsegs POST (SFS 0xf6118 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 (Z_to_bv 64 beta) xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    zstep. if_cases K1.
    -
      zstep. if_cases K2.
      { apply STEP3; [unfold SF_EMIN, SF_EMAX; lia | exact HB]. }
      pose proof HB as HB'.
      assert (beta = 6 \/ beta = 7 \/ beta = 8 \/ beta = 9)%Z as [->|[->|[->| ->]]] by lia;
        (zstep; zstep; zstep; zstep; if_false; apply sf_par; [exact HK | lia]).
    -
      do 5 zstep.
      zstep. if_cases K2.
      { apply TZ1; unfold SF_EMIN, SF_EMAX; lia. }
      do 3 zstep.
      apply STEP3; [unfold SF_EMIN, SF_EMAX; lia | exact HB].
  Qed.

  Lemma sf_mul : forall k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (6 <= beta <= 9)%Z ->
    evt bsegs POST (SFS 0xf60e8 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 k) xa4 (Z_to_bv 64 beta) xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR.
    intros k beta xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 12 zstep.
    apply sf_split; assumption.
  Qed.

  Lemma sf_main : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt bsegs POST (SFS 0xf6038 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 e2) (Z_to_bv 64 2147450880) xa7 xt3 xt4 xt5 xt6).
  Proof using MI QR FR SZ.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k_range e2 HE) as HK.
    pose proof (sf_beta_range e2 HE) as HB.
    pose proof (sf_prod_small e2 HE) as [P1 _].
    pose proof (sf_prod2_small e2 HE) as [P2 _].
    pose proof (sf_beta_machine_bvB e2 HE) as BM.
    do 4 zstep.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mulc e2 315653) by lia.
    replace (Z_to_bv 64 (e2 mod 18446744073709551616 * 315653)) with (Z_to_bv 64 (e2 * 315653))
      by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; symmetry; apply mod64_mulc).
    zstep. if_false.

    zstep.
    rewrite (swrap32_Z ((e2 * 315653) mod 18446744073709551616)).
    change (((e2 * 315653) mod 18446744073709551616 + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 ((e2 * 315653) mod 18446744073709551616)).
    rewrite (sw32_small_mod64 (e2 * 315653)) by lia.
    change (Z.shiftr (e2 * 315653) 20) with (sf_k e2). rewrite (swrap32_id (sf_k e2)) by lia.
    set (k := sf_k e2) in *.

    zstep. zstep. zstep. zstep.
    nnorm.
    if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].

    zstep. zstep. zstep. zstep. nnorm. zstep.
    if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zstep. nnorm.
    destruct (image_readable_b bsegs m (Z.to_nat 9904) 0x29c80 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    zastep. zastep. zastep. zastep. if_false.
    zastep. zastep. zastep. zastep. zastep. if_false.
    assert (TZ : Z.of_nat (length tb) = 9904%Z) by (rewrite TL; apply Z2Nat.id; lia). clear TL.

    zstep. zstep. zstep. nnorm.
    zstep. zstep. zstep.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mulc (2 - k) 1741647) by lia.
    replace (Z_to_bv 64 ((2 - k) mod 18446744073709551616 * 1741647)) with (Z_to_bv 64 ((2 - k) * 1741647))
      by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; symmetry; apply mod64_mulc).
    zstep. if_false.

    zstep. zstep.
    rewrite BM.
    set (beta := sf_beta e2) in *.

    zstep. zstep.
    rewrite (swrap32_id (63 - beta)) by lia.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].
    zstep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].

    destruct (bytes_u64_read bsegs m 0x29c80 tb (16 * (294 - k)) TB ltac:(lia) ltac:(rewrite TZ; lia)) as [w0 RD0].
    destruct (bytes_u64_read bsegs m 0x29c80 tb (16 * (294 - k) + 8) TB ltac:(lia) ltac:(rewrite TZ; lia)) as [w1 RD1].
    zstep. zstep.
    clear RD0 RD1 TB TZ tb.
    zstep. zstep. zstep. zstep.
    apply sf_mul; [exact HK | exact HB].
  Qed.
End SF.
