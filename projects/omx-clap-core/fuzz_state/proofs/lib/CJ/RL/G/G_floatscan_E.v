(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Bytes PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FloatScan.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import FloatScan_split2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require F_scan_calls.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import G_memcpy G_memchr G_fmt_fp_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmt_fp_lib.G_multf3_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmt_fp_lib.G_multf3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import G_divtf3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmodl.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmodl.G_divtf3_main.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_subtf3.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_subtf3.G_addtf3_E.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import G_subtf3 G_letf2 G_getf2 G_floatsitf G_floatunsitf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_pop_arg.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_pop_arg.G_extenddftf2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import G_scalbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_Scan_iface.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_Scan_iface.G_shgetc_A.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_scanexp.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_scanexp.G_shgetc_B.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_scanexp.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_scanexp.G_shgetc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import F_rscan_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_scanexp.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_scanexp.G_rfile.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import G_scalbnl G_fmodl G_scanexp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require F_rscan_model.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import G_floatscan_common.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.ProgAt3.Prog_floatscan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import GRoTab. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.StoreCache.StoreFast.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_floatscan_E : CodeAtT img_segs (sym 0x1e0cc) (floatscan_prog_at IMG)}.
  Context {RB_floatscan_E : RelCode (sym 0x1e0cc) 5768}.
  Context {CODE_floatscan_E_1 : CodeAtT img_segs (sym 0x15f44) (floatscan_prog_r1_at IMG)}.
  Context {RB_floatscan_E_1 : RelCode (sym 0x15f44) 12}.
  Context {RO_10428 : RoB img_segs (sym 0x10428) ([BV 8 83; BV 8 90; BV 8 155; BV 8 160; BV 8 47; BV 8 184; BV 8 68; BV 8 0])}.
  Context {RO_103f0 : RoB img_segs (sym 0x103f0) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 224; BV 8 63])}.
  Context {RO_10400 : RoB img_segs (sym 0x10400) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 208; BV 8 63])}.
  Context {RO_103e0 : RoB img_segs (sym 0x103e0) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 232; BV 8 63])}.
  Context {RO_107c4 : RoB img_segs (sym 0x107c4) ROT_0x107c4}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_shgetc_1e0cc : GLRN 0x1e0cc 0x1df78}.
  Context {RN_B_1f754_1e0cc : GLRN 0x1e0cc 0x1f754}.
  Context {RN_B_floatsitf_1e0cc : GLRN 0x1e0cc 0x1bad0}.
  Context {RN_B_scanexp_1e0cc : GLRN 0x1e0cc 0x1fe6c}.
  Context {RN_B_15f44_1e0cc : GLRN 0x1e0cc 0x15f44}.
  Context {RN_B_shlim_1e0cc : GLRN 0x1e0cc 0x1df40}.
  Context {RN_B_floatunsitf_1e0cc : GLRN 0x1e0cc 0x1c51c}.
  Context {RN_B_multf3_1e0cc : GLRN 0x1e0cc 0x1b3d0}.
  Context {RN_B_extenddftf2_1e0cc : GLRN 0x1e0cc 0x1af98}.
  Context {RN_B_200dc_1e0cc : GLRN 0x1e0cc 0x200dc}.
  Context {RN_B_divtf3_1e0cc : GLRN 0x1e0cc 0x1c6b0}.
  Context {RN_B_addtf3_1e0cc : GLRN 0x1e0cc 0x1bc80}.
  Context {RN_B_scalbn_1e0cc : GLRN 0x1e0cc 0x1bbd8}.
  Context {RN_B_copysignl_1e0cc : GLRN 0x1e0cc 0x20238}.
  Context {RN_B_fmodl_1e0cc : GLRN 0x1e0cc 0x20260}.
  Context {RN_B_subtf3_1e0cc : GLRN 0x1e0cc 0x1bc70}.
  Context {RN_B_letf2_1e0cc : GLRN 0x1e0cc 0x1b24c}.
  Context {RN_B_fabsl_1e0cc : GLRN 0x1e0cc 0x2053c}.
  Context {RN_B_getf2_1e0cc : GLRN 0x1e0cc 0x1b314}.
  Context {RN_B_scalbnl_1e0cc : GLRN 0x1e0cc 0x20548}.
  Context {RN_B_stack_chk_fail_1e0cc : GLRN 0x1e0cc 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_K_107c4 : GLRS 0x107c4}.
  Context {RS_K_10428 : GLRS 0x10428}.
  Context {RS_K_103f0 : GLRS 0x103f0}.
  Context {RS_K_10400 : GLRS 0x10400}.
  Context {RS_K_103e0 : GLRS 0x103e0}.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_341f8 : GLRS 0x341f8}.
  Let rp_341f8 : (0 <= sym 0x341f8 /\ sym 0x341f8 < 2^30)%Z := @rel_sym_pf _ RS_341f8.
  Context {SPEC_getf2 : getf2_contract}.
  Context {SPEC_scalbn : scalbn_contract}.
  Context {SPEC_extenddftf2 : extenddftf2_contract}.
  Context {SPEC_multf3_callq : multf3_callq_c}.
  Context {SPEC_divtf3_callq : divtf3_callq_c}.
  Context {SPEC_divtf3_spec : divtf3_spec_c}.
  Context {SPEC_addtf3_callq : addtf3_callq_c}.
  Context {SPEC_subtf3_callq : subtf3_callq_c}.
  Context {SPEC_letf2_callv : letf2_callv_c}.
  Context {SPEC_fabsl_spec : fabsl_spec_c}.
  Context {SPEC_copysignl_spec : copysignl_spec_c}.
  Context {SPEC_scalbnl_spec : scalbnl_spec_c}.
  Context {SPEC_rfmodl_spec : rfmodl_spec_c}.
  Context {SPEC_floatsitf_callv : floatsitf_callv_c}.
  Context {SPEC_floatsitf_callp : floatsitf_callp_c}.
  Context {SPEC_floatunsitf_callv : floatunsitf_callv_c}.
  Context {SPEC_extenddftf2_callv : extenddftf2_callv_c}.
  Context {SPEC_scanexp_rspec : scanexp_rspec_c}.
  Context {SPEC_shlim_spec : shlim_spec_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 172 <= sym 0x341f8)%Z}.
  Let rl0_0 : (sym 0x22e18 + 172 <= sym 0x341f8)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x341f8 + 0 <= sym 0x34288)%Z}.
  Let rl0_1 : (sym 0x341f8 + 0 <= sym 0x34288)%Z := @zfact_pf _ RL0_1.
  Collection ImgHyps := IMG CODE_floatscan_E RB_floatscan_E CODE_floatscan_E_1 RB_floatscan_E_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.
  Local Ltac clear_img := clear - IMG CODE_floatscan_E RB_floatscan_E CODE_floatscan_E_1 RB_floatscan_E_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI rp_34288 rp_341f8 rl0_0 rl0_1; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
Section Floatscan.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
            (fR : shfile) (yR : Z).
  Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
  Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
  Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis Hp : (0 <= p < zlength txt)%Z.
  Hypothesis Hnul : znth txt p = 0%Z.
  Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
  Hypothesis HP30 : (p < 2^31)%Z.
  Hypothesis T0 : (4096 <= T)%Z.
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
  Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
  Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
  Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
  Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
  Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
  Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
  Hypothesis Q1 : (q < 2^63)%Z.
  Hypothesis FRM : frm0 fc.
  Hypothesis NSTD : sh_stdio f0 = false.
  (* [comment removed for export] *)
  Local Ltac lia ::= first [ zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
                           | zify_prune_fast; Zify.zify; xlia zchecker
                           | Zify.zify; xlia zchecker ].
  (* [comment removed for export] *)
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                           clear - HI SPT SEP SE_T SG1 SG2 SG3 SPLO SPF SPF2 Q1 T0 T1 Hp HP30 rp_34288 rp_341f8 rl0_0 rl0_1;
                           unfold G_floatscan_common.hide, G_floatscan_common.hide2, sf_hide in *; Zify.zify; xlia zchecker ].
  Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | sec_tier | tlia | split; [ tlia | exact I ] ].
  (* [comment removed for export] *)
  Local Ltac solve_load_base ::=
    match goal with
    | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      match goal with
      | H : rw_cells segs m ?A ?cs0 |- _ =>
          let k := addr_diff E A in
          lazymatch k with Zneg _ => fail | _ => idtac end;
          let kn := eval vm_compute in (Z.to_nat k) in
          split_for_access H segs m A cs0 kn n;
          let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
          let c := eval_cell_at cs kn in
          lazymatch c with Some ?c0 =>
            rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
          end
      | H : ro_cells segs m ?A ?cs0 |- _ =>
          let k := addr_diff E A in
          lazymatch k with Zneg _ => fail | _ => idtac end;
          let kn := eval vm_compute in (Z.to_nat k) in
          split_for_access H segs m A cs0 kn n;
          let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
          let c := eval_cell_at cs kn in
          lazymatch c with Some ?c0 =>
            rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
          end
      | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
          cbv delta [wa] in HR;
          first [ rewrite HR
                | replace (ov_read_bytes segs m a n) with (Some bs)
                    by (rewrite <- HR; f_equal; word_eq_tac) ]
      end
    end;
    load_post.
  Local Ltac solve_store ::=
    match goal with
    | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let E := addr_expr a in
      match goal with
      | H : rw_cells segs m ?A ?cs0 |- _ =>
          let k := addr_diff E A in
          lazymatch k with Zneg _ => fail | _ => idtac end;
          let kn := eval vm_compute in (Z.to_nat k) in
          split_for_access H segs m A cs0 kn n;
          let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
          let c := eval_cell_at cs kn in
          lazymatch c with Some ?c0 =>
            rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
            cbv beta iota;
            match goal with
            | |- context [write_to_mem m a ?bs] =>
                replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
            end
          end
      | HS : store_ok segs m ?a' n = true |- _ =>
          cbv delta [wa] in HS;
          first [ rewrite HS
                | replace (store_ok segs m a n) with true
                    by (rewrite <- HS; f_equal; word_eq_tac);
                  try replace (write_to_mem m a) with (write_to_mem m a')
                    by (f_equal; word_eq_tac) ];
          cbv beta iota
      end
    end.
  Notation TPv := (Z_to_bv 64 RATP).
  Notation SPv := (Z_to_bv 64 (q + -8416)).
  Notation XA := (q + -8312)%Z.
  Notation RFJ' := (RFJ T txt p true J).
  (* [comment removed for export] *)
  Local Notation GLRUN1 f := (f ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR) (only parsing). Local Notation ctx_all := ((GLRUN1 G_floatscan_common.ctx_all)).
  Local Notation Wfs := (G_floatscan_common.Wfs q Fp).
  Local Notation FokR := (G_floatscan_common.FokR F).
  Local Notation Fok := (G_floatscan_common.Fok F).
  Local Notation Fok_refl := (G_floatscan_common.Fok_refl F).
  Local Notation Fok_set := (G_floatscan_common.Fok_set F).
  Local Notation Fok_trans10 := (G_floatscan_common.Fok_trans10 F).
  Local Notation GLRUN2 f := (f s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F) (only parsing). Local Notation GLRUN3 f := (f Fp T p J txt canary) (only parsing). Local Notation fs_post := ((GLRUN3 (GLRUN2 (G_floatscan_common.fs_post ra q gp))) fR yR).
  Local Notation hi_cells := ((GLRUN2 (G_floatscan_common.hi_cells ra)) canary).
  Local Notation finv := ((GLRUN2 (G_floatscan_common.finv ra q)) m0 Fp T txt canary).
  Local Notation zbytes_len := (G_floatscan_common.zbytes_len txt).
  Local Notation framL := (G_floatscan_common.framL q).
  Local Notation txt_char := (G_floatscan_common.txt_char txt BYT).
  Local Notation numch_nz := (G_floatscan_common.numch_nz p txt Hnum).
  Local Notation frame_release := ((GLRUN2 (G_floatscan_common.frame_release ra q)) m0 Fp T txt pre canary).
  Local Notation GLRUN4 f := (f Hp SEP SE_T SPF SPT SG1 SG3) (only parsing). Local Notation post_tail := ((GLRUN4 ((GLRUN2 (G_floatscan_common.post_tail ra q gp)) m0 Fp T p J txt pre canary fR yR))).
  Local Notation L_RET34 := ((GLRUN4 (GLRUN1 G_floatscan_common.L_RET34))).
  Local Notation L_RET1 := ((GLRUN4 (GLRUN1 G_floatscan_common.L_RET1))).
  Local Notation L_RET30 := ((GLRUN4 (GLRUN1 G_floatscan_common.L_RET30))).
  Local Notation L_SCL := ((GLRUN1 G_floatscan_common.L_SCL) Hp SEP SE_T SPLO SPF SPT SG1 SG3 Q1).
  Local Notation dfinv := ((GLRUN3 ((GLRUN2 (G_floatscan_common.dfinv ra q)) m0)) pok).
  Local Notation dfinvG := ((GLRUN3 ((GLRUN2 (G_floatscan_common.dfinvG ra q)) m0)) pok).
  Local Notation dfinvG_dfinv := ((GLRUN3 ((GLRUN2 (G_floatscan_common.dfinvG_dfinv ra q)) m0)) pok).
  Local Notation S_F3 := ((GLRUN1 G_floatscan_common.S_F3)).
  Local Notation S_F2 := ((GLRUN1 G_floatscan_common.S_F2)).
  Local Notation S_F1 := ((GLRUN1 G_floatscan_common.S_F1)).
  Local Notation S_A69C := ((GLRUN1 G_floatscan_common.S_A69C)).
  Local Notation S_A62C := ((GLRUN1 G_floatscan_common.S_A62C)).
  Local Notation S_A5C4 := ((GLRUN1 G_floatscan_common.S_A5C4)).
  Local Notation S_A568 := ((GLRUN1 G_floatscan_common.S_A568)).
  Local Notation S_A534 := ((GLRUN1 G_floatscan_common.S_A534)).
  Local Notation SN324 := ((GLRUN1 G_floatscan_common.SN324)).
  Local Notation S_N324 := ((GLRUN1 G_floatscan_common.S_N324)).
  Local Notation S_N2D4 := ((GLRUN1 G_floatscan_common.S_N2D4)).
  Local Notation S_U1A8 := ((GLRUN1 G_floatscan_common.S_U1A8)).
  Local Notation S_NK := ((GLRUN3 ((GLRUN2 (G_floatscan_common.S_NK ra q gp)) m0)) pok fR yR).
  Local Notation S_N484 := ((GLRUN1 G_floatscan_common.S_N484)).
  Local Notation S_N3E8 := ((GLRUN1 G_floatscan_common.S_N3E8)).
  Local Notation S_UK := ((GLRUN1 G_floatscan_common.S_UK)).
  Local Notation SU1C4 := ((GLRUN1 G_floatscan_common.SU1C4)).
  Local Notation S_U1C4 := ((GLRUN1 G_floatscan_common.S_U1C4)).
  Local Notation S_T := ((GLRUN1 G_floatscan_common.S_T)).
  Local Notation S_DD0 := ((GLRUN1 G_floatscan_common.S_DD0)).
  Local Notation S_DD24 := ((GLRUN1 G_floatscan_common.S_DD24)).
  Local Notation S_M := ((GLRUN1 G_floatscan_common.S_M)).
  Local Notation S_P := ((GLRUN1 G_floatscan_common.S_P)).
  Local Notation S_R := ((GLRUN1 G_floatscan_common.S_R)).
  Local Notation S_C38 := ((GLRUN1 G_floatscan_common.S_C38)).
  Local Notation S_C2C := ((GLRUN1 G_floatscan_common.S_C2C)).
  Local Notation S_E := ((GLRUN1 G_floatscan_common.S_E)).
  Local Notation SDn := ((GLRUN1 G_floatscan_common.SDn)).
  Local Notation S_D := ((GLRUN1 G_floatscan_common.S_D)).
  Local Notation winv := ((GLRUN3 ((GLRUN2 (G_floatscan_common.winv ra q)) m0))).
  Local Notation winv_dfinvG := ((GLRUN3 ((GLRUN2 (G_floatscan_common.winv_dfinvG ra q)) m0)) pok).
  Local Notation S_B0C := ((GLRUN1 G_floatscan_common.S_B0C)).
  Local Notation S_A9C := ((GLRUN1 G_floatscan_common.S_A9C)).
  Local Notation S_A44 := ((GLRUN1 G_floatscan_common.S_A44)).
  Local Notation SRZn := ((GLRUN1 G_floatscan_common.SRZn)).
  Local Notation S_RZ := ((GLRUN1 G_floatscan_common.S_RZ)).
  Local Notation S_9EC := ((GLRUN1 G_floatscan_common.S_9EC)).
  Local Notation S_A64 := ((GLRUN1 G_floatscan_common.S_A64)).
  Local Notation S_7F4 := ((GLRUN1 G_floatscan_common.S_7F4)).
  Local Notation S_9C8 := ((GLRUN1 G_floatscan_common.S_9C8)).
  Local Notation SLZn := ((GLRUN1 G_floatscan_common.SLZn)).
  Local Notation S_LZ := ((GLRUN1 G_floatscan_common.S_LZ)).
  Local Notation S_990 := ((GLRUN1 G_floatscan_common.S_990)).
  Local Notation S_848 := ((GLRUN1 G_floatscan_common.S_848)).
  Local Notation S_6F8 := ((GLRUN1 G_floatscan_common.S_6F8)).
  Local Notation FS_tail := (G_floatscan_common.FS_tail pok fuelc).
  Local Notation S_618 := ((GLRUN1 G_floatscan_common.S_618)).
  (* [comment removed for export] *)
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    (nelim H 8%nat; intros MI MU WM FRhi ST TXT SSP1 SSP2); unfold G_floatscan_common.Wfs, FS_DEPTH, RERRNO in MU; unfold G_floatscan_common.hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
    unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
    try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    unfold zlength in *.
  Ltac mk_finv := unfold G_floatscan_common.finv, G_floatscan_common.Wfs, G_floatscan_common.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
  Ltac mk_framL := unfold G_floatscan_common.framL, RERRNO; split; hyp.
  Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.
  Ltac lo96b H := apply (proj1 (rw_cells_C8_CB8 _ _ [_; _; _; _; _; _; _; _; _; _; _; _] _ [])) in H; cbn [app] in H.
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.
  Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
  Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac unstash := unfold hide in *.
  Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.
  (* [comment removed for export] *)
  Ltac lia_goal P := lazymatch P with
    | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
    | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
    | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
    | ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
    | ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
    end.
  Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
  Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
  Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
  Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
  (* [comment removed for export] *)
  Ltac predi := repeat match goal with H : @eq nat ?a ?l |- _ => natlit_z l ltac:(fun z p => change (@eq nat a (natZ z)) in H; note_natZ z p) end.
  Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok; predi.
  Ltac unbury := unfold hide2 in *.
  Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
  (* [comment removed for export] *)
  Ltac brsf K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
    repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
    first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac].
  Ltac br10 K := brf K; [ exfalso; lia | ].
  Ltac br01 K := brf K; [ | exfalso; lia ].
  (* [comment removed for export] *)
  Ltac zsimp_in_w H :=
    try (match type of H with
         | context [v_sltu _ _] => idtac | context [v_slt _ _] => idtac
         | context [v_sltiu _ _] => idtac | context [v_slti _ _] => idtac end;
         rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H);
    try (match type of H with context [zxb] => cbv delta [zxb] in H end);
    zb_fold_lits_in H;
    repeat match type of H with
    | context [bv_unsigned (Z_to_bv 64 ?e)] => zs_wrap_in e H
    | _ => progress (zs_idioms_in H)
    end; zb_fold_lits_in H.
  Ltac brfw K := if_cases K; rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in K;
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K; zsimp_in_w K; zify_bool K;
    try (rewrite ?signed_of_Z in K by lia).
  Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    (nelim H 5%nat; intros FI FL XW LW FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_dfinv := unfold G_floatscan_common.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Ltac mk_dfinvG := unfold G_floatscan_common.dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Ltac fixk := rewrite ?land2047, ?landW_mod2048 in *.
  Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.
  Tactic Notation "call_split" constr(K) tactic3(tac) :=
    lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
      let ST1 := fresh "ST1" in
      destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
      callw tac;
      lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
        lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
        pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
    end.
  Ltac eval_lands := repeat match goal with |- context [Z.land ?a ?b] =>
    lazymatch isZcst a with true => lazymatch isZcst b with true =>
      let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v end end end.
  Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
  Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    (nelim H 5%nat; intros FI FL XW LW FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_winv := unfold G_floatscan_common.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Notation POST := (fs_post m0).

  (* [comment removed for export] *)

  Hypothesis HS_R : S_R.

  (* [comment removed for export] *)
  Ltac ufc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac site_facts FC RJ k c f :=
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; (nelim RJ2 6%nat; intros OK Rc CC KM NS SS); (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst);
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; flia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
  Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
  Proof. clear_img. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
  Lemma stdio_lim0 : forall f, sh_stdio (sh_lim0 f) = sh_stdio f.
  Proof. clear_img. intros f. reflexivity. Qed.

  Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
  Proof.
    clear_img. intros kmin c f (OK & Rc & CC & KM & NS & SS). (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
    split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
    - intros E. (nelim (NS E) 3%nat; intros N1 N2 N3). split; [reflexivity|]. split; [exact N2 | exact N3].
    - intros E. (nelim (SS E) 5%nat; intros N1 N2 N3 N4 N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
  Qed.

  (* [comment removed for export] *)
  Lemma dfK_dn_f : forall sg f rp a z e2 x f' y, dfK_dn 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
  Proof.
    clear_img. intros until y. unfold dfK_dn. destruct (df_dn_loop _ _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate].
    destruct (df_final _ _ _ _ _ _ _ _ _ _); [|discriminate]. intros H. injection H as <- _. reflexivity.
  Qed.
  Lemma dfK_up_f : forall sg f rp a z e2 x f' y, dfK_up 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
  Proof. clear_img. intros until y. unfold dfK_up. destruct (df_up_loop _ _) as [[rp2 a2 z2 e22 x2]|]; [|discriminate]. apply dfK_dn_f. Qed.
  Lemma dfK_al_f : forall sg f rp z x f' y, dfK_al 53 (-1074) sg f rp z x = Some (f', y) -> f' = f.
  Proof.
    clear_img. intros until y. unfold dfK_al.
    destruct (if nz (Z.rem rp 9) then _ else _) as [[[[a2 z2] rp2] x2]|]; [|discriminate]. apply dfK_up_f.
  Qed.
  Lemma dfK_tz_f : forall sg f rp k x f' y, dfK_tz 53 (-1074) sg f rp k x = Some (f', y) -> f' = f.
  Proof. clear_img. intros until y. unfold dfK_tz. destruct (df_tz_loop _ _ _); [|discriminate]. apply dfK_al_f. Qed.
  Lemma dfK_mid_f : forall sg f rp lnz k x f' y, dfK_mid 53 (-1074) sg f rp lnz k x = Some (f', y) -> f' = f.
  Proof.
    clear_img. intros until y. unfold dfK_mid.
    destruct (_ && _ && _)%Z; cbv beta iota zeta; [|apply dfK_tz_f].
    destruct (rp =? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
    destruct (rp <? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
    destruct (_ || _); cbv beta iota. { intros H; injection H as <- _; reflexivity. }
    apply dfK_tz_f.
  Qed.
  Lemma dfK_pad_f : forall sg f lrp lnz j k x f' y, dfK_pad 53 (-1074) sg f lrp lnz j k x = Some (f', y) -> f' = f.
  Proof.
    clear_img. intros until y. unfold dfK_pad. destruct (if nz j then _ else _) as [[k2 x2]|]; [|discriminate]. apply dfK_mid_f.
  Qed.
  Lemma dfK_rng_f : forall sg f lrp dc lnz j k x f' y, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f', y) -> f' = f.
  Proof.
    clear_img. intros until y. unfold dfK_rng.
    destruct (znth x 0 =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
    destruct (_ && _ && _); [intros H; injection H as <- _; reflexivity|].
    destruct (_ <? lrp)%Z; [intros H; injection H as <- _; reflexivity|].
    destruct (lrp <? _)%Z; [intros H; injection H as <- _; reflexivity|].
    apply dfK_pad_f.
  Qed.

  (* [comment removed for export] *)
  Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
  Proof.
    clear_img. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [flia|]. apply in_seq. flia.
  Qed.
  Lemma and33_iff : forall c, (-1 <= c < 256)%Z ->
    (Z.land (Z.land c 18446744073709551615) 18446744073709551583 = 69 <-> Z.lor c 32 = 101)%Z.
  Proof.
    clear_img. intros c Hc. destruct (Z.eq_dec c (-1)) as [->|Hne].
    { cbn. split; intros H; discriminate H. }
    rewrite (land_W64_small c) by flia.
    pose proof (forallb_range (fun c => Bool.eqb (Z.land c 18446744073709551583 =? 69) (Z.lor c 32 =? 101))%Z 256 ltac:(vm_compute; reflexivity) c ltac:(flia)) as E.
    cbv beta in E. destruct (Z.eqb_spec (Z.land c 18446744073709551583) 69); destruct (Z.eqb_spec (Z.lor c 32) 101); cbn in E; try discriminate E; tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma L_C48 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) b96 ev ws sign kmin c (f : shfile),
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> Fok Ft -> frm0 fct ->
    fR = sh_lim0 f -> yR = f128_of_i32 0 ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2020)) fct None m (seg_rom img_segs)).
  Proof.
    intros until f. intros DI RJ FOK FRM' HfR Hy. pose proof DI as DI0. dest_dfinv DI.
    site_facts FC RJ kmin c f.
    assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
    { destruct FC as [[Hwf _] _]. cbn in Hwf. clear - Hwf. tauto. }
    destruct L0 as [L0 L1].
    pose proof FC as FC0. rewrite rf_cells_raw_eq in FC0.
    pose proof SPEC_shlim_spec as SL. unfold shlim_stmt in SL.
    zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (f := f) (J := J);
      [exact FC0 | exact (RFI_ok T txt p J _ _ _ RJ) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
    match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- HfR in FC2.
    zs. zs. callx (eapply SPEC_floatsitf_callp; [eassumption | flia]).
    zs. eapply L_RET1; try eassumption; try flia; try mk_finv; try mk_framL.
    all: try (rewrite HfR; eapply RFJ_lim0; exact RJ). all: flia.
  Qed.


  (* [comment removed for export] *)
  Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (f : shfile) (kmin c : Z) (fS : shfile) (e10 : Z),
    scanexp fuelc f pok = Some (fS, e10) ->
    rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z ->
    (sh_stdio f = true -> rtext T txt pre post /\ p = zlength pre) -> sh_stdio f = false ->
    bytes_at img_segs m T (zbytes txt) -> ssp_cells m canary ->
    stk img_segs m (q' - 240) q' -> (4096 <= q' - 240)%Z -> (q' <= Fp)%Z ->
    (T + zlength txt <= q' - 240 \/ q' <= T)%Z -> (ssp_guard + 8 <= q' - 240)%Z -> (0 <= q')%Z -> (q' < 2^63)%Z ->
    mem_inv img_segs m ->
    evt img_segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' k' c',
        ms' = MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0' t1' t2' s0 s1 (Z_to_bv 64 e10) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (ret_pc ra') fc' None m' (seg_rom img_segs)
        /\ munch [(q' - 240, q'); (Fp, Fp + 232)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
        /\ stk img_segs m' (q' - 240) q'
        /\ rw_cells img_segs m' Fp (rf_cells T p true fS J)
        /\ RFJ' k' c' fS /\ (1 <= k')%Z
        /\ bytes_at img_segs m' T (zbytes txt)
        /\ ssp_cells m' canary)
      (MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F' (Z_to_bv 64 SCANEXP) fc' None m (seg_rom img_segs)).
  Proof.
    intros until e10. intros HS FC RJ Hk Hc STX NS BY SSP ST Q1' Q2 Q3 Q4 Q5 Q6 MI.
    pose proof SPEC_scanexp_rspec as SX. unfold scanexp_rstmt in SX.
    eapply evt_mono.
    { eapply SX with (pre := pre) (post := post); try eassumption; unfold SCANEXP_DEPTH; try flia; clear -Hpok; unfold hide2 in *; flia. }
    intros ms' P. unfold scanexp_rpost, SCANEXP_DEPTH in P. exact P.
  Qed.
  Ltac eplia := unfold SCANEXP_DEPTH, zlength, got_ssp, ssp_guard in *; unfold hide2 in *; flia.
  Ltac some_pair H := let E1 := fresh "Ef" in injection H as E1 H.

  Lemma L_C38 : S_C38.
  Proof.
    intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    (nelim DF 10%nat; intros XR X31H Rj Rk Rdc Rlnz Hlnz Hxk Hkj Hkj45).
    unfold nz in HK.
    destruct (Z.eqb_spec gotdig 0) as [Eg|Ng]; cbn [Z.b2z negb] in Hng, HK; subst ng.
    - (* [comment removed for export] *)
      some_pair HK.
      zs. br10 K1.
      zs. callx (eapply errno_loc_spec; eassumption).
      zs. unfold RERRNO. zs0.
      eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
    - pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. symmetry in Ef. subst f.
      zs. br01 K1.
      stmt HS_R. eapply NX; try eassumption; try flia.
  Qed.

  Lemma L_C2C : S_C2C.
  Proof.
    intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst Hsn DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    site_facts FC RJ kmin c f.
    pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
    rewrite (rf_unget_eq f Hsn) in HK, RJu.
    ufc FC. rewrite Hsn in FC.
    zs. zs. zs0.
    pose proof L_C38 as NX. unfold G_floatscan_common.S_C38 in NX. eapply NX with (f := mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)); try eassumption; try flia.
    unfold G_floatscan_common.dfinvG. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
    unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?Hsn; unfold M64; hyp_cells.
  Qed.

  Lemma L_E : S_E.
  Proof.
    intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Rgr Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    pose proof DF as DF0. (nelim DF 10%nat; intros XR X31H Rj Rk Rdc Rlnz Hlnz Hxk Hkj Hkj45).
    site_facts FC RJ kmin c f.
    unfold dfK_exp in HK. cbv beta iota zeta in HK.
    set (lrp' := (if nz gotrad then lrp else dc)%Z) in HK.
    assert (Rlrp' : (- 2^31 <= lrp' < 2^31)%Z) by (subst lrp'; destruct (nz gotrad); flia).
    (* [comment removed for export] *)
    assert (GAC0 :
      evt img_segs POST
        (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 (sym 0x1e0cc + 1628)) fct None m (seg_rom img_segs))).
    2:{ zs. zs. brf K1.
        - replace lrp' with dc in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity.
        - zs. replace lrp' with lrp in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia). reflexivity. }
    clearbody lrp'.
    (* [comment removed for export] *)
    assert (GC1C : forall (x11' x12' : word),
      (nz gotdig && (Z.lor c 32 =? 101))%Z = false ->
      evt img_segs POST
        (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11' x12' x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 (sym 0x1e0cc + 1976)) fct None m (seg_rom img_segs))).
    { intros x11' x12' Hne. rewrite Hne in HK.
      assert (Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z).
      { clear_img. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; flia. }
      zs. rewrite (Eng gotdig Rg). zs. brsf K2.
      - (* [comment removed for export] *)
        replace (0 <=? c)%Z with false in HK by (symmetry; apply Z.leb_gt; flia).
        pose proof L_C38 as NX. unfold G_floatscan_common.S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
      - replace (0 <=? c)%Z with true in HK by (symmetry; apply Z.leb_le; flia).
        pose proof FC as FC0. ufc FC.
        destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
        + (* [comment removed for export] *)
          rewrite (rf_unget_nop f SN) in HK.
          zs. zs. br01 K3.
          pose proof L_C38 as NX. unfold G_floatscan_common.S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
        + zs. zs. br10 K3.
          pose proof L_C2C as NX. unfold G_floatscan_common.S_C2C in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity. }
    (* [comment removed for export] *)
    zs. brf K2.
    { (* [comment removed for export] *) apply GC1C. unfold nz. replace (gotdig =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity. }
    zs. zs. zs. brf K3.
    { (* [comment removed for export] *) apply GC1C. replace (Z.lor c 32 =? 101)%Z with false; [apply Bool.andb_false_r|].
      symmetry. apply Z.eqb_neq. intros E. apply K3. apply (proj2 (and33_iff c ltac:(flia))). exact E. }
    assert (He : Z.lor c 32 = 101%Z) by (apply (proj1 (and33_iff c ltac:(flia))); exact K3).
    unfold nz in HK at 1. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).
    rewrite He in HK. cbn [negb andb Z.eqb Pos.eqb] in HK.
    destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
    assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in He; discriminate He).
    pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.
    (* [comment removed for export] *)
    zs. zs. zs. zs.
    callx (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
      [ exact HSX | exact FC | exact RJ | eplia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | rewrite Hst; exact NSTD | exact BY | exact (conj SSP1 SSP2)
      | replace (q + -8416 - 240)%Z with (q - 8656)%Z by flia; exact ST
      | eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
    match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end.
    match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
    match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
    match goal with H : stk _ ?m' (q + -8416 - 240)%Z _ |- _ => replace (q + -8416 - 240)%Z with (q - 8656)%Z in H by flia end.
    match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
    pose proof RJ2 as RJ3. (nelim RJ3 6%nat; intros OK2 Rc2 CC2 KM2 NS2 SS2). (nelim OK2 6%nat; intros Hbuf2 Rl2 Rr2 Rc02 Rn2 Rst2).
    assert (RR2 : (0 <= rf_rend T p true fS <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fS); unfold zlength in *; flia). unfold M64 in RR2.
    assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
    unfold nz in HK. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).
    (* [comment removed for export] *)
    zs. zs. zs. brfw K4; rewrite ?land_W64 in K4.
    - (* [comment removed for export] *)
      assert (Hne : e10 <> LLONG_MIN_).
      { intros E. apply K4. rewrite E. vm_compute. reflexivity. }
      replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbn [negb] in HK. cbv beta iota in HK.
      pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. subst fS.
      assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
      zs.
      let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + e10)%Z) by (first [ f_equal; ring | apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia ]).
      stmt HS_R. eapply NX with (lrp := (lrp' + e10)%Z); try eassumption; try flia. mk_dfinvG.
    - assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear -K4 R; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; flia]).
      rewrite Ee, Z.eqb_refl in HK.
      zs. brfw K5; rewrite ?land_W64 in K5.
      + (* [comment removed for export] *)
        assert (Ep : pok = 0%Z) by (clear -K5 Hpok; unfold hide2 in *; mlia).
        rewrite Ep in HK. cbn [Z.eqb negb] in HK. cbv beta iota in HK. some_pair HK.
        eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
      + assert (Ep : pok <> 0%Z) by (clear -K5 Hpok; unfold hide2 in *; mlia).
        replace (pok =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Ep). cbn [negb] in HK. cbv beta iota in HK.
        pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef.
        pose proof (RFI_unget T txt p J Hp _ _ fS RJ2 ltac:(flia)) as RJu.
        pose proof FC2 as FC3. ufc FC3.
        destruct (sh_shlim_neg fS) eqn:SN; unfold M64 in FC3.
        * (* [comment removed for export] *)
          rewrite (rf_unget_nop fS SN) in HK, Ef, RJu. subst fS.
          zs. zs. br01 K6. zs. zs.
          let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (first [ f_equal; ring | apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia ]).
          stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
        * rewrite (rf_unget_eq fS SN) in HK, Ef, RJu.
          zs. zs. br10 K6. zs. zs. zs. zs1. zs. zs.
          let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (first [ f_equal; ring | apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia ]).
          rewrite <- Ef in RJu, HK.
          assert (Hst3 : sh_stdio fR = sh_stdio f0) by (rewrite Ef; cbn [sh_stdio]; exact Hst2).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            assert (FC4 : rw_cells img_segs mm Fp (rf_cells T p true fR J))
              by (rewrite Ef; unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells) end.
          stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
  Qed.

End Floatscan.

End Img.
