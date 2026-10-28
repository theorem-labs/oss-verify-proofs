(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig SjPjBeta.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs Pj_sf_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma sf_beta_machine_bv : forall e2, (-1074 <= e2 <= 972)%Z ->
  bv_swrap 32 (Z.land (bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land ((2 - sf_k e2) * 1741647) 18446744073709551615)) 19)) 18446744073709551615
               + Z.land e2 18446744073709551615) = sf_beta e2.
Proof.
  intros e2 H. rewrite !land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z. rewrite !swrap32_Z.
  exact (sf_beta_machine e2 H).
Qed.

Section SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (sf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma sf_par : forall k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (6 <= beta <= 9)%Z ->
    evt usegs POST (SFS 0x5b348 xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 (Z_to_bv 64 beta) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 14 zstep.
    zstep. if_cases K3.
    { apply sf_step3; [exact MI| unfold SF_EMIN, SF_EMAX; lia | exact HB]. }
    apply sf_tz1; [exact MI| unfold SF_EMIN, SF_EMAX; lia].
  Qed.

  Lemma sf_split : forall k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (6 <= beta <= 9)%Z ->
    evt usegs POST (SFS 0x5b30c xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 (Z_to_bv 64 beta) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    zstep. if_cases K1.
    -
      zstep. if_cases K2.
      { apply sf_step3; [exact MI| unfold SF_EMIN, SF_EMAX; lia | exact HB]. }
      pose proof HB as HB'.
      assert (beta = 6 \/ beta = 7 \/ beta = 8 \/ beta = 9)%Z as [->|[->|[->| ->]]] by lia;
        (zstep; zstep; zstep; zstep; if_false; apply sf_par; [exact HK | lia]).
    -
      do 5 zstep.
      zstep. if_cases K2.
      { apply sf_tz1; [exact MI| unfold SF_EMIN, SF_EMAX; lia]. }
      do 3 zstep.
      apply sf_step3; [exact MI| unfold SF_EMIN, SF_EMAX; lia | exact HB].
  Qed.

  Lemma sf_mul : forall k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (6 <= beta <= 9)%Z ->
    evt usegs POST (SFS 0x5b2dc xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 (Z_to_bv 64 beta) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k beta xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 12 zstep.
    apply sf_split; assumption.
  Qed.

  Lemma sf_main : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt usegs POST (SFS 0x5b250 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 e2) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k_range e2 HE) as HK.
    pose proof (sf_beta_range e2 HE) as HB.
    pose proof (sf_prod_small e2 HE) as [P1 _].
    pose proof (sf_prod2_small e2 HE) as [P2 _].
    do 4 zstep.
    rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mulc e2 315653) by lia.
    replace (Z_to_bv 64 (e2 mod 18446744073709551616 * 315653)) with (Z_to_bv 64 (e2 * 315653))
      by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; symmetry; apply mod64_mulc).
    zstep.
    if_false.
    zstep.
    rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite (swrap32_Z ((e2 * 315653) mod 18446744073709551616)).
    change (((e2 * 315653) mod 18446744073709551616 + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 ((e2 * 315653) mod 18446744073709551616)).
    rewrite (sw32_small_mod64 (e2 * 315653)) by lia.
    change (Z.shiftr (e2 * 315653) 20) with (sf_k e2). rewrite (swrap32_id (sf_k e2)) by lia.
    pose proof (sf_beta_machine_bv e2 HE) as BM.
    set (beta := sf_beta e2) in *.
    set (k := sf_k e2) in *.

    zstep. zstep. zstep. zstep.
    rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z. nnorm.
    if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].

    zstep. zstep. zstep. zstep. nnorm. zstep.
    if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zstep. zstep. zstep. rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z. nnorm.
    zstep. zstep. zstep.
    rewrite ?land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mulc (2 - k) 1741647) by lia.
    replace (Z_to_bv 64 ((2 - k) mod 18446744073709551616 * 1741647)) with (Z_to_bv 64 ((2 - k) * 1741647))
      by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; symmetry; apply mod64_mulc).
    zstep. if_false.

    zstep. zstep.
    rewrite BM.

    zstep. zstep.
    rewrite (swrap32_id (63 - beta)) by lia.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].
    zstep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].

    zstep. zstep. zstep.
    destruct (image_readable_b usegs m (Z.to_nat 9904) 0x176c0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    destruct (bytes_u64_read usegs m 0x176c0 tb (16 * (294 - k)) TB ltac:(lia) ltac:(rewrite TL; lia)) as [w0 RD0].
    destruct (bytes_u64_read usegs m 0x176c0 tb (16 * (294 - k) + 8) TB ltac:(lia) ltac:(rewrite TL; lia)) as [w1 RD1].
    zstep. zstep.
    clear RD0 RD1 TB TL tb.
    zstep. zstep.
    apply sf_mul; [exact HK | exact HB].
  Qed.
End SF.
