(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memset G_memcpy G_fwritex G_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_frexpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmodl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_splitR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_FmtFp_facts2.G_FmtFp_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_FmtFp_facts2 G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_fmt_fp_pre G_fmt_fp_pre2 G_fmt_fp_pre3 G_fmt_fp_pre4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_join.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_fmt_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_fmt_fp : CodeAtT img_segs (sym 0x1973c) (fmt_fp_prog_at IMG)}.
  Context {RB_fmt_fp : RelCode (sym 0x1973c) 5832}.
  Context {RO_103c0 : RoB img_segs (sym 0x103c0) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 176; BV 8 65])}.
  Context {RO_10428 : RoB img_segs (sym 0x10428) ([BV 8 83; BV 8 90; BV 8 155; BV 8 160; BV 8 47; BV 8 184; BV 8 68; BV 8 0])}.
  Context {RO_103f0 : RoB img_segs (sym 0x103f0) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 224; BV 8 63])}.
  Context {RO_103d8 : RoB img_segs (sym 0x103d8) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 240; BV 8 63])}.
  Context {RO_10420 : RoB img_segs (sym 0x10420) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 248; BV 8 63])}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_signbitl_1973c : GLRN 0x1973c 0x1b128}.
  Context {RN_B_fpclassifyl_1973c : GLRN 0x1973c 0x1b130}.
  Context {RN_B_frexpl_1973c : GLRN 0x1973c 0x1b174}.
  Context {RN_B_floatsitf_1973c : GLRN 0x1973c 0x1bad0}.
  Context {RN_B_multf3_1973c : GLRN 0x1973c 0x1b3d0}.
  Context {RN_B_letf2_1973c : GLRN 0x1973c 0x1b24c}.
  Context {RN_B_extenddftf2_1973c : GLRN 0x1973c 0x1af98}.
  Context {RN_B_scalbn_1973c : GLRN 0x1973c 0x1bbd8}.
  Context {RN_B_subtf3_1973c : GLRN 0x1973c 0x1bc70}.
  Context {RN_B_addtf3_1973c : GLRN 0x1973c 0x1bc80}.
  Context {RN_B_memset_1973c : GLRN 0x1973c 0x21738}.
  Context {RN_B_fwritex_1973c : GLRN 0x1973c 0x17d50}.
  Context {RN_B_fixunstfsi_1973c : GLRN 0x1973c 0x1c488}.
  Context {RN_B_floatunsitf_1973c : GLRN 0x1973c 0x1c51c}.
  Context {RN_B_fixtfsi_1973c : GLRN 0x1973c 0x1c608}.
  Context {RN_B_divtf3_1973c : GLRN 0x1973c 0x1c6b0}.
  Context {RN_B_pad_1973c : GLRN 0x1973c 0x19668}.
  Context {RN_B_stack_chk_fail_1973c : GLRN 0x1973c 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_K_102ac : GLRS 0x102ac}.
  Context {RS_K_103c0 : GLRS 0x103c0}.
  Context {RS_K_1031d : GLRS 0x1031d}.
  Context {RS_K_10385 : GLRS 0x10385}.
  Context {RS_K_10326 : GLRS 0x10326}.
  Context {RS_K_10381 : GLRS 0x10381}.
  Context {RS_K_10428 : GLRS 0x10428}.
  Context {RS_K_10b9c : GLRS 0x10b9c}.
  Context {RS_K_103f0 : GLRS 0x103f0}.
  Context {RS_K_103d8 : GLRS 0x103d8}.
  Context {RS_K_10420 : GLRS 0x10420}.
  Context {RS_K_102de : GLRS 0x102de}.
  Context {RS_102de : GLRS 0x102de}.
  Let rp_102de : (0 <= sym 0x102de /\ sym 0x102de < 2^30)%Z := @rel_sym_pf _ RS_102de.
  Context {RS_102ac : GLRS 0x102ac}.
  Let rp_102ac : (0 <= sym 0x102ac /\ sym 0x102ac < 2^30)%Z := @rel_sym_pf _ RS_102ac.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {SPEC_pad : pad_contract}.
  Context {SPEC_memset : memset_contract}.
  Context {SPEC_memcpy : memcpy_contract}.
  Context {SPEC_pad_call : pad_call_c}.
  Context {SPEC_fwritex_call : fwritex_call_c}.
  Context {SPEC_letf2_callv : letf2_callv_c}.
  Context {SPEC_letf2_callv0 : letf2_callv0_c}.
  Context {SPEC_fixunstfsi_callv : fixunstfsi_callv_c}.
  Context {SPEC_floatsitf_callv : floatsitf_callv_c}.
  Context {SPEC_floatsitf_callp : floatsitf_callp_c}.
  Context {SPEC_floatunsitf_callv : floatunsitf_callv_c}.
  Context {SPEC_floatunsitf_callfix : floatunsitf_callfix_c}.
  Context {SPEC_extenddftf2_callv : extenddftf2_callv_c}.
  Context {SPEC_multf3_callq : multf3_callq_c}.
  Context {SPEC_divtf3_callq : divtf3_callq_c}.
  Context {SPEC_divtf3_spec : divtf3_spec_c}.
  Context {SPEC_addtf3_callq : addtf3_callq_c}.
  Context {SPEC_subtf3_callq : subtf3_callq_c}.
  Context {SPEC_frexpl_callq : frexpl_callq_c}.
  Context {SPEC_signbitl_callv : signbitl_callv_c}.
  Context {SPEC_fpclassifyl_callv : fpclassifyl_callv_c}.
  Context {RL0_0 : ZFact (sym 0x102de + 1 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x102de + 1 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL1_0 : ZFact (sym 0x102ac + 19 <= sym 0x34288)%Z}.
  Let rl1_0 : (sym 0x102ac + 19 <= sym 0x34288)%Z := @zfact_pf _ RL1_0.
  Context {RL2_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl2_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL2_0.
  Context {RO_dot : RoB img_segs (sym 0x102de) (cons (Z_to_bv 8 46) nil)}.
  Context {RO_prefix : RoB img_segs (sym 0x102ac) (zb PREFIX_STR)}.
  Context {RQ_34288 : ZFact (0x20000 <= sym 0x34288)%Z}.
  Let rq_34288 : (0x20000 <= sym 0x34288)%Z := @zfact_pf _ RQ_34288.
  Collection ImgHyps := IMG CODE_fmt_fp RB_fmt_fp RO_103c0 RO_10428 RO_103f0 RO_103d8 RO_10420 RN_B_signbitl_1973c RN_B_fpclassifyl_1973c RN_B_frexpl_1973c RN_B_floatsitf_1973c RN_B_multf3_1973c RN_B_letf2_1973c RN_B_extenddftf2_1973c RN_B_scalbn_1973c RN_B_subtf3_1973c RN_B_addtf3_1973c RN_B_memset_1973c RN_B_fwritex_1973c RN_B_fixunstfsi_1973c RN_B_floatunsitf_1973c RN_B_fixtfsi_1973c RN_B_divtf3_1973c RN_B_pad_1973c RN_B_stack_chk_fail_1973c RS_got_ssp RS_K_102ac RS_K_103c0 RS_K_1031d RS_K_10385 RS_K_10326 RS_K_10381 RS_K_10428 RS_K_10b9c RS_K_103f0 RS_K_103d8 RS_K_10420 RS_K_102de RS_102de rp_102de RS_102ac rp_102ac RS_34288 rp_34288 SPEC_pad SPEC_memset SPEC_memcpy SPEC_pad_call SPEC_fwritex_call SPEC_letf2_callv SPEC_letf2_callv0 SPEC_fixunstfsi_callv SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_floatunsitf_callfix SPEC_extenddftf2_callv SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_frexpl_callq SPEC_signbitl_callv SPEC_fpclassifyl_callv RL0_0 rl0_0 RL1_0 rl1_0 RL2_0 rl2_0 RO_dot RO_prefix RQ_34288 rq_34288.



(* [comment removed for export] *)
Definition FMT_FP_DEPTH : Z := 4640.

(* [comment removed for export] *)
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
             Ft (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - FMT_FP_DEPTH, bv_unsigned sp);
              (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ stk img_segs m' (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp)
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
    (5152 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> ((sym 0x34288) + 8 <= bv_unsigned sp - FMT_FP_DEPTH)%Z ->
    (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z -> (length junk0 < 256)%nat ->
    stk img_segs m (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp) ->
    mem_inv img_segs m ->
    frm0 fc ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt img_segs (fmt_fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp fl0 j1 j2 lbfw B o0 o1 junk0 canary ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1973c)) fc None m (seg_rom img_segs)).

Lemma fmt_fp_spec : fmt_fp_stmt.
Proof.
  unfold fmt_fp_stmt. intros until ret. cbv zeta.
  intros HM (YN0 & YN1 & DIGB & E2B & DNB0 & WBA0 & CAR0 & AZR0 & BLA0) SPLO SPHI GLO AF AB Hw Hp Hfl Ht Hta ROOM J256 ST MI FRM WF SSP Ha3 Ha4 Ha5 Ha6 Hps.
  eapply evt_mono.
  { eapply (G_fmt_fp_join.ffp_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a0 F m fl0 j1 j2 lbfw B junk0 canary w p fl t o0 o1 ret);
      eassumption. }
  intros ms' H. exact H.
Qed.

(* [comment removed for export] *)
Definition fmt_fp_contract : Prop := fmt_fp_stmt.
Lemma fmt_fp_contract_ok : fmt_fp_contract.
Proof. exact fmt_fp_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class fmt_fp_contract.
