(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_memset.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fwritex.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_pad.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_frexpl.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_divtf3_main.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import FmtFp_split.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import FmtFp_splitR.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import FmtFp_splitH.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import FmtFp_facts.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import FmtFp_facts2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fmt_fp_calls.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fmt_fp_pre.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fmt_fp_pre2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fmt_fp_pre3.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_fmt_fp_pre4.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require F_fmt_fp_join.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMX Require Import ShZero QcF IcptCells FfpTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Open Scope bv_scope.

Definition FMT_FP_DEPTH : Z := 4640.

Definition fmt_fp_facts (y fl p t : Z) : Prop :=
  yn_fact y /\ yn_fact (Z.lxor y F128_SIGNBIT)
  /\ dig_words_fact y fl /\ e2_range_fact y fl /\ dn_phase_fact y fl p t
  /\ words_all_fact y fl p t /\ carry_fact y fl p t /\ azr_fact y fl p t
  /\ below_a_fact y fl p t.

Definition fmt_fp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (o0 o1 : list Z) (junk0 : list byte)
    (canary : word) (ret : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - FMT_FP_DEPTH, bv_unsigned sp);
              (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc'
    /\ stk rsegs m' (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
    /\ ssp_cells m' canary
    /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

Definition fmt_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
         (w p fl t : Z) (o0 o1 : list Z) (ret : Z),
    let y := (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z in
    let Fp := bv_unsigned a0 in
    fmt_fp o0 y w p fl t = Some (o1, ret) ->
    fmt_fp_facts y fl p t ->
    (5152 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (7069720 <= bv_unsigned sp - FMT_FP_DEPTH)%Z ->
    (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z -> (length junk0 < 256)%nat ->
    stk rsegs m (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp) ->
    mem_inv rsegs m ->

    ffp_acx rsegs m (bv_unsigned sp) B (Z.of_nat (length o0) + Z.of_nat (length junk0)) Fp ->
    frm0 fc ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt rsegs (fmt_fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp fl0 j1 j2 lbfw B o0 o1 junk0 canary ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14b4a0) fc None m (seg_rom rsegs)).

Lemma fmt_fp_spec : fmt_fp_stmt.
Proof.
  unfold fmt_fp_stmt. intros until ret. cbv zeta.
  intros HM (YN0 & YN1 & DIGB & E2B & DNB0 & WBA0 & CAR0 & AZR0 & BLA0) SPLO SPHI GLO AF AB Hw Hp Hfl Ht Hta ROOM J256 ST MI ACX FRM WF SSP Ha3 Ha4 Ha5 Ha6 Hps.
  eapply evt_mono.
  { eapply (F_fmt_fp_join.ffp_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a0 F m fl0 j1 j2 lbfw B junk0 canary w p fl t o0 o1 ret);
      eassumption. }
  intros ms' H. exact H.
Qed.
