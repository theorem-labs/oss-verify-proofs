(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import FmtFp_split FmtFp_splitR FmtFp_splitH FmtFp_facts FmtFp_facts2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memset F_memcpy F_fwritex F_pad F_frexpl F_divtf3_main F_fmt_fp_lib F_fmt_fp_calls F_fmt_fp_pre F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require F_fmt_fp_join.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
             Ft (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - FMT_FP_DEPTH, bv_unsigned sp);
              (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ frm0 fc'
    /\ stk usegs m' (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp)
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
    (5152 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (1112064 <= bv_unsigned sp - FMT_FP_DEPTH)%Z ->
    (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z -> (length junk0 < 256)%nat ->
    stk usegs m (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp) ->
    mem_inv usegs m ->
    frm0 fc ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt usegs (fmt_fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp fl0 j1 j2 lbfw B o0 o1 junk0 canary ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc6f2c) fc None m (seg_rom usegs)).

Lemma fmt_fp_spec : fmt_fp_stmt.
Proof.
  unfold fmt_fp_stmt. intros until ret. cbv zeta.
  intros HM (YN0 & YN1 & DIGB & E2B & DNB0 & WBA0 & CAR0 & AZR0 & BLA0) SPLO SPHI GLO AF AB Hw Hp Hfl Ht Hta ROOM J256 ST MI FRM WF SSP Ha3 Ha4 Ha5 Ha6 Hps.
  eapply evt_mono.
  { eapply (F_fmt_fp_join.ffp_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a0 F m fl0 j1 j2 lbfw B junk0 canary w p fl t o0 o1 ret);
      eassumption. }
  intros ms' H. exact H.
Qed.
