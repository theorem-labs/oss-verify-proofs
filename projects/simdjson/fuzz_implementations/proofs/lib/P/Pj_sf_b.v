(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Pj_num_defs Pj_sf_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma sf_k_machine_bv : forall e2, (-1074 <= e2 <= 972)%Z ->
  bv_swrap 32 (Z.shiftr (bv_swrap 32 ((e2 mod 18446744073709551616 * 315653) mod 18446744073709551616)) 20) = sf_k e2.
Proof. intros e2 H. rewrite !swrap32_Z. exact (sf_k_machine e2 H). Qed.

Section SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv psegs m.

  Notation POST := (sf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).

  Lemma sf_par : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt psegs POST (SFS 0x539fc xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 15 zstep.
    zstep. if_cases K3; zify_cond K3.
    { apply sf_step3; [exact MI| unfold SF_EMIN, SF_EMAX; lia]. }
    apply sf_tz1; [exact MI| unfold SF_EMIN, SF_EMAX; lia].
  Qed.

  Lemma sf_split : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt psegs POST (SFS 0x539d4 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    zstep. if_cases K1.
    -
      zstep. if_cases K2.
      { apply sf_step3; [exact MI| unfold SF_EMIN, SF_EMAX; lia]. }
      apply sf_par. lia.
    -
      do 4 zstep.
      zstep. if_cases K2.
      { apply sf_tz1; [exact MI| unfold SF_EMIN, SF_EMAX; lia]. }
      do 3 zstep.
      apply sf_step3; [exact MI| unfold SF_EMIN, SF_EMAX; lia].
  Qed.

  Lemma sf_mul : forall k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z ->
    evt psegs POST (SFS 0x53994 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 k) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    do 16 zstep.
    apply sf_split. exact HK.
  Qed.

  Lemma sf_main : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt psegs POST (SFS 0x5393c xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 e2) xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k_range e2 HE) as HK.
    do 12 zstep.
    zstep. zstep.
    rewrite (sf_k_machine_bv e2 HE).
    set (k := sf_k e2) in *.
    zstep. zstep. zstep. zstep. zstep.
    nnorm.
    destruct (image_readable_b psegs m (Z.to_nat 9904) 0x18438 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    destruct (bytes_u64_read psegs m 0x18438 tb (16 * (294 - k)) TB ltac:(lia) ltac:(rewrite TL; lia)) as [w0 RD0].
    destruct (bytes_u64_read psegs m 0x18438 tb (16 * (294 - k) + 8) TB ltac:(lia) ltac:(rewrite TL; lia)) as [w1 RD1].
    zstep. zstep. zstep.
    apply sf_mul. exact HK.
  Qed.
End SF.
