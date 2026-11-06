(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.P Require Import F_sf_helpers2.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.P Require F_f128_mul.
Import OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.P.F_f128_mul.F_f128_mul_core1.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.P Require Import F_f128_mul.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Section Model.
  Variables a_lo a_hi b_lo b_hi : Z.
  Let aExp := shr64 (shl64 a_hi 1) 49.
  Let bExp := shr64 (shl64 b_hi 1) 49.
  Let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63.
  Let aSigHi := Z.land a_hi MASK48.
  Let bSigHi := Z.land b_hi MASK48.
  Let aAbsHi := Z.land a_hi ABS_HI.
  Let bAbsHi := Z.land b_hi ABS_HI.

  (* [comment removed for export] *)
  Definition FM_p2b (aSigHi1 aSigLo1 scale1 : Z) : Z :=
    let '(bSigHi1, bSigLo1, scale2) :=
      if shr64 bAbsHi 48 =? 0 then
        let '(nbHi, nbLo, nbClz) := norm_denormal bSigHi b_lo in
        (nbHi, nbLo, scale1 - nbClz + 16)
      else (bSigHi, b_lo, scale1) in
    mul_core signHi aExp bExp aSigHi1 aSigLo1 bSigHi1 bSigLo1 scale2.
  (* [comment removed for export] *)
  Definition FM_p2 : Z :=
    let '(aSigHi1, aSigLo1, scale1) :=
      if shr64 aAbsHi 48 =? 0 then
        let '(naHi, naLo, naClz) := norm_denormal aSigHi a_lo in
        (naHi, naLo, 16 - naClz)
      else (aSigHi, a_lo, 0) in
    FM_p2b aSigHi1 aSigLo1 scale1.
  (* [comment removed for export] *)
  Definition FM_inf : Z :=
    if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
      (if negb (Z.lor b_lo bAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
    else if Z.lor (Z.lxor bAbsHi INF_HI) b_lo =? 0 then
      (if negb (Z.lor a_lo aAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
    else if Z.lor a_lo aAbsHi =? 0 then mk128 signHi 0
    else if Z.lor b_lo bAbsHi =? 0 then mk128 signHi 0
    else FM_p2.
  (* [comment removed for export] *)
  Definition FM_b : Z :=
    let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
    if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo else FM_inf.
  (* [comment removed for export] *)
  Definition FM_a : Z :=
    let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
    if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo else FM_b.
  Definition f128_mul_w : Z :=
    let aExpM := add64 aExp 0xffffffffffff8001 in
    let bExpM := add64 bExp 0xffffffffffff8001 in
    if negb (orb (aExpM <? 0xffffffffffff8002) (bExpM <=? 0xffffffffffff8001))
    then mul_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0
    else FM_a.
End Model.

Lemma f128_mul_words : forall a_lo a_hi b_lo b_hi,
  0 <= a_lo < 2^64 -> 0 <= a_hi < 2^64 -> 0 <= b_lo < 2^64 -> 0 <= b_hi < 2^64 ->
  f128_mul (mk128 a_hi a_lo) (mk128 b_hi b_lo) = f128_mul_w a_lo a_hi b_lo b_hi.
Proof. intros. unfold f128_mul. rewrite !lo64_mk128, !hi64_mk128 by lia. reflexivity. Qed.

Lemma nd_hi_range : forall h l, 0 <= l < 2^64 -> 0 <= nd_hi h l < 2^64.
Proof.
  intros h l Hl. unfold nd_hi, norm_denormal, shl128_mirror.
  destruct (is_neg64 _).
  - apply Z_lor_range. apply SoftFloat.wrap64_range. apply (zr_shiftr (Z.shiftr l 1)); [apply (zr_shiftr l 1); [exact Hl|lia] | apply Z.land_nonneg; right; lia].
  - apply SoftFloat.wrap64_range.
Qed.
Lemma nd_lo_range : forall h l, 0 <= nd_lo h l < 2^64.
Proof.
  intros h l. unfold nd_lo, norm_denormal, shl128_mirror.
  apply (zr_land_r _ _). { unfold sra63, ONES64. destruct (is_neg64 _); lia. } apply SoftFloat.wrap64_range.
Qed.

Section Walk.
  Variables (sp a0 a1 a2 a3 : word).
  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
End Walk.