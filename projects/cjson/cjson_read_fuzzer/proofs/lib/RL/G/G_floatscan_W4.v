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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan_split2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memcpy G_memchr G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_divtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmodl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_subtf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_subtf3.G_addtf3_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_subtf3 G_letf2 G_getf2 G_floatsitf G_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pop_arg.G_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_scalbn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_scalbnl G_fmodl G_scanexp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_floatscan_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_floatscan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import GRoTab. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.

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
  Context {CODE_floatscan_W4 : CodeAtT img_segs (sym 0x1e0cc) (floatscan_prog_at IMG)}.
  Context {RB_floatscan_W4 : RelCode (sym 0x1e0cc) 5768}.
  Context {CODE_floatscan_W4_1 : CodeAtT img_segs (sym 0x15f44) (floatscan_prog_r1_at IMG)}.
  Context {RB_floatscan_W4_1 : RelCode (sym 0x15f44) 12}.
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
  Context {SPEC_shgetc_callJ : shgetc_callJ_c}.
  Context {SPEC_scanexp_rspec : scanexp_rspec_c}.
  Context {SPEC_shlim_spec : shlim_spec_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 172 <= sym 0x341f8)%Z}.
  Let rl0_0 : (sym 0x22e18 + 172 <= sym 0x341f8)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x341f8 + 0 <= sym 0x34288)%Z}.
  Let rl0_1 : (sym 0x341f8 + 0 <= sym 0x34288)%Z := @zfact_pf _ RL0_1.
  Collection ImgHyps := IMG CODE_floatscan_W4 RB_floatscan_W4 CODE_floatscan_W4_1 RB_floatscan_W4_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_shgetc_callJ SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.
  Local Ltac clear_img := clear - IMG CODE_floatscan_W4 RB_floatscan_W4 CODE_floatscan_W4_1 RB_floatscan_W4_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_shgetc_callJ SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI rp_34288 rp_341f8 rl0_0 rl0_1; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

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
  Hypothesis HP64 : (p <= 64)%Z.
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
  (* [comment removed for export] *)
  Local Ltac lia ::= first [ zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
                           | zify_prune_fast; Zify.zify; xlia zchecker
                           | Zify.zify; xlia zchecker ].
  (* [comment removed for export] *)
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                           clear - HI SPT SEP SE_T SG1 SG2 SG3 SPLO SPF SPF2 Q1 T0 T1 Hp HP64 rp_34288 rp_341f8 rl0_0 rl0_1;
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
  Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
  Ltac unbury := unfold hide2 in *.
  Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
  (* [comment removed for export] *)
  Ltac glia := lazymatch goal with |- ?G => lia_goal G end; lia.
  (* [comment removed for export] *)
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

  Hypothesis HS_618 : S_618.

  (* [comment removed for export] *)
  Ltac ufc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
  Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
  Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
    lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
      replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
  Ltac mk_winv2 := norm_m1074; unfold G_floatscan_common.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
    split; [first [assumption | rewrite ?upd_length; assumption]|];
    first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
  Proof. clear_img. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
  Lemma getc_rpos2 : forall f, sh_buf f = txt ->
    (sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
  Proof.
    clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
    destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
  Qed.
  Ltac site_facts FC RJ k c f :=
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; (nelim RJ2 6%nat; intros OK Rc CC KM NS SS); (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst);
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
  Ltac call_shgetc FC0 RJ SLOW Hst :=
    let STD := fresh "STD" in let EJ := fresh "EJ" in let Hn := fresh "Hn" in let Hrpe := fresh "Hrpe" in let Hc00 := fresh "Hc00" in
    let STD0 := fresh "STD0" in let TXT := fresh "TXT" in let Hpre := fresh "Hpre" in
    lazymatch type of RJ with RFJ _ _ _ _ _ ?kmin ?c ?f =>
    (nelim (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) 5%nat; intros STD EJ Hn Hrpe Hc00);
    assert (STD0 : sh_stdio f0 = true) by (first [rewrite <- Hst; exact STD | exact STD]); destruct (ST0 STD0) as [TXT Hpre];
    call_split 160%Z (eapply SPEC_shgetc_callJ with (pre := pre) (post := post);
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp
        | eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]);
    match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H end;
    match goal with H : ssp_cells ?m' _ |- _ => let S1 := fresh "SSP1'" in let S2 := fresh "SSP2'" in destruct H as [S1 S2]; unfold got_ssp, ssp_guard in S1, S2 end
    end.
  Ltac read_char f :=
    let RDb := fresh "RDb" in
    lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    pose proof (u8ro_read (@img_segs _) _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
    zs; cbv beta; try rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.
  (* [comment removed for export] *)
  Lemma getc_fch : forall kmin c f, RFJ' kmin c f -> c <> 0%Z -> fch (fst (sh_getc f)).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    unfold fch, sh_getc. rewrite Hbuf.
    destruct (sh_stdio f) eqn:ES; cbn [negb].
    - (nelim (SS eq_refl) 5%nat; intros N1 N2 N3 N4 N5). rewrite N1. destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE]; cbn [negb fst].
      + right; right; reflexivity.
      + left. apply Hnum. lia.
    - (nelim (NS eq_refl) 3%nat; intros N1 N2 N3). specialize (N3 Hc). cbn [fst].
      destruct (Z.eq_dec (sh_rpos f) p) as [E|NE]; [right; left; rewrite E; exact Hnul | left; apply Hnum; lia].
  Qed.
  Definition fch_ok (c : Z) : bool :=
    (negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 73) &&
     negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 78) &&
     negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 88) &&
     negb (Z.land c 18446744073709551583 =? 73) && negb (Z.land c 18446744073709551583 =? 78) && negb (Z.land c 18446744073709551583 =? 88) &&
     negb (Z.lor c 32 =? 105) && negb (Z.lor c 32 =? 110) && negb (Z.lor c 32 =? 120) &&
     negb (m_isspace c) && negb (c =? 32) && (5 <=? (c + -9) mod 2 ^ 64))%Z.
  Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
  Proof.
    clear_img. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
  Qed.
  Lemma numch_range : forall c, is_numch c = true -> (0 <= c < 256)%Z.
  Proof.
    clear_img. intros c N. unfold is_numch in N.
    repeat (apply Bool.orb_true_iff in N; destruct N as [N|N]); try (apply Z.eqb_eq in N; lia).
    apply andb_true_iff in N. destruct N as [N1 N2]. apply Z.leb_le in N1. apply Z.leb_le in N2. lia.
  Qed.
  Lemma fch_ok_true : forall c, fch c -> fch_ok c = true.
  Proof.
    clear_img. intros c [N | [-> | ->]]; [| reflexivity | reflexivity].
    pose proof (numch_range c N) as Rc.
    pose proof (forallb_range (fun c => implb (is_numch c) (fch_ok c)) 256 ltac:(vm_compute; reflexivity) c Rc) as E.
    cbv beta in E. rewrite N in E. exact E.
  Qed.
  Lemma fch_facts : forall c, fch c ->
    (Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 73 /\ Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 78 /\
     Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 88 /\
     Z.land c 18446744073709551583 <> 73 /\ Z.land c 18446744073709551583 <> 78 /\ Z.land c 18446744073709551583 <> 88 /\
     Z.lor c 32 <> 105 /\ Z.lor c 32 <> 110 /\ Z.lor c 32 <> 120 /\ m_isspace c = false /\ c <> 32 /\ 5 <= (c + -9) mod 2 ^ 64)%Z.
  Proof.
    clear_img. intros c H. pose proof (fch_ok_true c H) as E. unfold fch_ok in E.
    repeat (apply andb_true_iff in E; destruct E as [E ?X]).
    repeat match goal with H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H end.
    repeat match goal with H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H end.
    apply Z.leb_le in X.
    repeat split; assumption.
  Qed.
  Lemma fch_range : forall c, fch c -> (-1 <= c < 256)%Z.
  Proof. clear_img. intros c [N | [-> | ->]]; [pose proof (numch_range c N); lia | lia | lia]. Qed.


  (* [comment removed for export] *)
  Lemma floatscan_front : forall (n : nat) (f : shfile) (sg c2 : Z) (f2 : shfile),
      m_isspace (fst (sh_getc f)) = false ->
      (if ((fst (sh_getc f) =? 43) || (fst (sh_getc f) =? 45))%Z
       then ((1 - 2 * b2z (fst (sh_getc f) =? 45))%Z, fst (sh_getc (snd (sh_getc f))), snd (sh_getc (snd (sh_getc f))))
       else (1%Z, fst (sh_getc f), snd (sh_getc f))) = (sg, c2, f2) ->
      (Z.lor c2 32 <> 105)%Z -> (Z.lor c2 32 <> 110)%Z ->
      floatscan (S n) f 1 pok =
        (if (c2 =? 48)%Z then let '(c3, f3) := sh_getc f2 in if (Z.lor c3 32 =? 120)%Z then None else decfloat (S n) (sh_unget f3) 48 53 (-1074) sg pok
         else decfloat (S n) f2 c2 53 (-1074) sg pok).
  Proof.
    clear_img. intros n f sg c2 f2 Hsp Hsg L105 L110.
    unfold floatscan. change (1 =? 0)%Z with false. change (1 =? 1)%Z with true. cbv beta iota.
    change (fs_ws_loop (S n) f) with (let '(c, f') := sh_getc f in if m_isspace c then fs_ws_loop n f' else Some (c, f')).
    rewrite (surjective_pairing (sh_getc f)). rewrite Hsp. cbv beta iota.
    rewrite (surjective_pairing (sh_getc (snd (sh_getc f)))). cbv beta iota.
    replace (if ((fst (sh_getc f) =? 43) || (fst (sh_getc f) =? 45))%Z
             then ((1 - 2 * b2z (fst (sh_getc f) =? 45))%Z, fst (sh_getc (snd (sh_getc f))), snd (sh_getc (snd (sh_getc f))))
             else (1%Z, fst (sh_getc f), snd (sh_getc f))) with (sg, c2, f2).
    cbv beta iota.
    change (fs_inf_loop 9 (0%Z, c2, f2)) with (if fs_inf_cond (0%Z, c2, f2) then fs_inf_loop 8 (fs_inf_body (0%Z, c2, f2)) else Some (0%Z, c2, f2)).
    unfold fs_inf_cond at 1. change (znth str_infinity 0) with 105%Z.
    replace (Z.lor c2 32 =? 105)%Z with false by (symmetry; apply Z.eqb_neq; exact L105).
    rewrite Bool.andb_false_r. cbv iota beta.
    cbn [Z.ltb Z.eqb Z.compare Pos.compare Pos.compare_cont andb orb].
    change (fs_nan_loop 4 (0%Z, c2, f2)) with (if fs_nan_cond (0%Z, c2, f2) then fs_nan_loop 3 (fs_nan_body (0%Z, c2, f2)) else Some (0%Z, c2, f2)).
    unfold fs_nan_cond. change (znth str_nan 0) with 110%Z.
    replace (Z.lor c2 32 =? 110)%Z with false by (symmetry; apply Z.eqb_neq; exact L110).
    rewrite Bool.andb_false_r. cbv iota beta.
    cbn [Z.ltb Z.eqb Z.compare Pos.compare Pos.compare_cont andb orb nz negb].
    reflexivity.
  Qed.

  Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let rec go pre l := lazymatch l with
       | [CB 8 _] => fail
       | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
       | ?c :: ?l' => go constr:(pre ++ [c]) l' end in
    lazymatch cs with ?c0 :: ?l => go constr:([c0]) l end end.

  (* [comment removed for export] *)
  Lemma L_5D0 : forall m3 (x1' x5' x6' x7' x8' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
      j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (av sg c : Z) (f : shfile) (kmin : Z),
    let _ := ctx_all in
    winv m3 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> (sg = 1 \/ sg = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= av < 2^64)%Z -> av <> 78%Z ->
    FS_tail sg c f = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sg) (Z_to_bv 64 c) (Z_to_bv 64 av) x12' x13' x14' x15' x16' x17'
               (Z_to_bv 64 53) x19' (Z_to_bv 64 (sym 0x34288)) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
          F (Z_to_bv 64 (sym 0x1e0cc + 364)) fc None m3 (seg_rom img_segs)).
  Proof.
    intros until kmin. intros _ WI3 RJ3 Hk3 Hsg3 Hst3 Hr3 Rav Hav HK3.
    pose proof WI3 as WI4. dest_winv WI4.
    zs. zs. br01 K.
    stmt HS_618. eapply NX; try eassumption; try glia. apply Fok_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma L_564 : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
      j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (c1 : Z) (f1 : shfile) (k1 : Z),
    let _ := ctx_all in
    winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f1 ->
    RFJ' k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 -> (c1 = 43%Z \/ c1 = 45%Z) ->
    FS_tail (1 - 2 * b2z (c1 =? 45))%Z (fst (sh_getc f1)) (snd (sh_getc f1)) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 32) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
               (Z_to_bv 64 53) x19' (Z_to_bv 64 (sym 0x34288)) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
          F (Z_to_bv 64 (sym 0x1e0cc + 256)) fc None m2 (seg_rom img_segs)).
  Proof.
    intros until k1. intros _ WI2 RK Hk2 Hst2 Hc1 HK2.
    dest_winv WI2. bury_disj.
    site_facts FC RK k1 c1 f1.
    assert (Hc10 : c1 <> 0%Z) by lia.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k1 c1 f1 RK Hc10) as RJ3.
    pose proof (getc_fch k1 c1 f1 RK Hc10) as FCH.
    pose proof (getc_stdio f1) as Hst3. rewrite Hst2 in Hst3.
    assert (Rc3 : (-1 <= fst (sh_getc f1) < 256)%Z) by ((nelim RJ3 3%nat; intros _ R _); exact R).
    pose proof (getc_rpos2 f1 Hbuf) as [Rrp3 Rrp4].
    set (sg := (1 - 2 * b2z (c1 =? 45))%Z) in HK2.
    assert (Hsg : (sg = 1 \/ sg = -1)%Z) by (subst sg; destruct (c1 =? 45)%Z; cbn; lia).
    destruct (Z.eq_dec (T + sh_rpos f1)%Z (rf_rend T p true f1)) as [SLOW|FAST].
    - pose proof FC as FC0. ufc2 FC.
      zs. zs. zs. zs. zs. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc1 as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
      clearbody sg.
      zs. br01 K1.
      zs. zs. call_shgetc FC0 RK SLOW Hst2.
      set (c2 := fst (sh_getc f1)) in *.
      zs. zs. zs. brf K2.
      + exfalso. clear -K2 FCH. (nelim (fch_facts _ FCH) 7%nat; intros A73 A78 A88 B73 B78 B88 _). first [exact (A73 K2) | exact (B73 K2)].
      + zs. eapply L_5D0; try eassumption; try glia.
        * mk_winv2.
        * pose proof (land_mask_range (Z.land c2 18446744073709551615) 18446744073709551583 ltac:(lia)). try pose proof (land_mask_range c2 18446744073709551583 ltac:(lia)). lia.
        * clear -FCH. (nelim (fch_facts _ FCH) 7%nat; intros A73 A78 A88 B73 B78 B88 _). first [exact A78 | exact B78].
    - pose proof (rf_getc_fast_lt T txt p J Hp k1 c1 f1 RK Hc10 FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k1 c1 f1 RK FAST) in *. cbn [fst snd] in *.
      pose proof (txt_char (sh_rpos f1) ltac:(unfold zlength in *; lia)) as Rch.
      ufc2 FC.
      zs. zs. zs. zs. zs. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc1 as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
      clearbody sg.
      zs. br10 K1.
      zs. zs0. read_char f1.
      set (c2 := znth txt (sh_rpos f1)) in *.
      zs. zs. zs. brf K2.
      + eapply L_5D0; try eassumption; try glia.
        * mk_winv2.
        * pose proof (land_mask_range (Z.land c2 18446744073709551615) 18446744073709551583 ltac:(lia)). try pose proof (land_mask_range c2 18446744073709551583 ltac:(lia)). lia.
        * clear -FCH. (nelim (fch_facts _ FCH) 7%nat; intros A73 A78 A88 B73 B78 B88 _). first [exact A78 | exact B78].
      + exfalso. clear -K2 FCH. (nelim (fch_facts _ FCH) 7%nat; intros A73 A78 A88 B73 B78 B88 _). first [exact (A73 K2) | exact (B73 K2)].
  Qed.
  (* [comment removed for export] *)
  Lemma L_554 : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
      j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (c1 : Z) (f1 : shfile) (k1 : Z),
    let _ := ctx_all in
    winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f1 ->
    RFJ' k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 -> fch c1 -> (c1 <> (-1)%Z -> 1 <= sh_rpos f1)%Z ->
    (forall sg c2 f2,
        (if ((c1 =? 43) || (c1 =? 45))%Z then ((1 - 2 * b2z (c1 =? 45))%Z, fst (sh_getc f1), snd (sh_getc f1)) else (1%Z, c1, f1)) = (sg, c2, f2) ->
        FS_tail sg c2 f2 = Some (fR, yR)) ->
    evt img_segs POST
      (MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 32) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
               (Z_to_bv 64 53) x19' (Z_to_bv 64 (sym 0x34288)) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
          F (Z_to_bv 64 (sym 0x1e0cc + 240)) fc None m2 (seg_rom img_segs)).
  Proof.
    intros until k1. intros _ WI2 RK Hk2 Hst2 FCH1 Hr1 HT.
    pose proof WI2 as WI3. dest_winv WI3. bury_disj.
    assert (Rc1 : (-1 <= c1 < 256)%Z) by ((nelim RK 3%nat; intros _ R _); exact R).
    zs. zs. brfw Ka.
    - assert (E45 : c1 = 45%Z) by (clear -Ka Rc1; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
      eapply L_564; try eassumption; try glia.
      apply HT. rewrite E45. reflexivity.
    - assert (N45 : c1 <> 45%Z) by (clear -Ka Rc1; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
      zs. zs. brfw Kb.
      + (* [comment removed for export] *)
        assert (N43 : c1 <> 43%Z) by (clear -Kb Rc1; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
        specialize (HT 1%Z c1 f1). 
        replace ((c1 =? 43) || (c1 =? 45))%Z with false in HT by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N43), (proj2 (Z.eqb_neq _ _) N45); reflexivity).
        specialize (HT eq_refl).
        zs. zs. zs. zs. brf Kc.
        * exfalso. clear -Kc FCH1. (nelim (fch_facts _ FCH1) 7%nat; intros A73 A78 A88 B73 B78 B88 _). first [exact (A73 Kc) | exact (B73 Kc)].
        * eapply L_5D0; try eassumption; try glia.
          -- pose proof (land_mask_range (Z.land c1 18446744073709551615) 18446744073709551583 ltac:(lia)). try pose proof (land_mask_range c1 18446744073709551583 ltac:(lia)). lia.
          -- clear -FCH1. (nelim (fch_facts _ FCH1) 7%nat; intros A73 A78 A88 B73 B78 B88 _). first [exact A78 | exact B78].
      + assert (E43 : c1 = 43%Z) by (clear -Kb Rc1; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
        eapply L_564; try eassumption; try glia.
        apply HT. rewrite E43. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma L_ENTRY : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
    let _ := ctx_all in
    stk img_segs m0 (q - FS_DEPTH) q -> mem_inv img_segs m0 ->
    rw_cells img_segs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
    bytes_at img_segs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells img_segs m0 RERRNO [C4 ev] ->
    evt img_segs POST
      (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
               s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom img_segs)).
  Proof.
    intros until ev. intros _ ST MI FC RJ Hk0 Hc0 Hst BY [SSP1 SSP2] ERR.
    pose proof (munch_refl Wfs m0) as MU. pose proof (wmono_refl img_segs m0) as WM. unfold G_floatscan_common.Wfs, FS_DEPTH, RERRNO in MU. unfold FS_DEPTH in ST.
    unfold got_ssp, ssp_guard in SSP1, SSP2. unfold RERRNO in ERR.
    unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T.
    pose proof zbytes_len as LTX. unfold zlength in *. bury_disj.
    site_facts FC RJ kmin0 c0 f0.
    (* [comment removed for export] *)
    pose proof HM as HM'. destruct fuelc as [|fu] eqn:Efu in HM'; [discriminate HM'|].
    pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0) as RJ1.
    pose proof (getc_fch kmin0 c0 f0 RJ Hc0) as FCH1.
    pose proof (getc_stdio f0) as Hst1.
    assert (Rc1 : (-1 <= fst (sh_getc f0) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    pose proof (getc_rpos2 f0 Hbuf) as [Rrp1 Rrp2].
    unfold FLOATSCAN.
    (* [comment removed for export] *)
    zs.
    carve_frame 120%nat ST. rename FR into FRhi.
    do 14 zs.
    lazymatch type of FRhi with rw_cells _ _ _ (CB 8 ?b :: _) => set (jc := b) in FRhi; clearbody jc end.
    zs. zs.
    replace (Z_to_bv 64 (q + -2032 - 4096))%Z with (Z_to_bv 64 (q + -6128))%Z by (f_equal; lia).
    (* [comment removed for export] *)
    assert (Hcv1 : (q - 8656 <= q + -120 - Z.of_nat (Z.to_nat 6000))%Z) by lia;
    (nelim (stk_carve img_segs _ _ _ (Z.to_nat 6000) ST Hcv1) 3%nat; intros ST' junka XBa); clear ST Hcv1; rename ST' into ST;
    replace (q + -120 - Z.of_nat (Z.to_nat 6000))%Z with (q + -6120)%Z in ST, XBa by lia.
    assert (Hcv2 : (q - 8656 <= q + -6120 - Z.of_nat 8)%Z) by lia;
    (nelim (stk_carve img_segs _ _ _ 8%nat ST Hcv2) 3%nat; intros ST' junkb XBb); clear ST Hcv2; rename ST' into ST;
    replace (q + -6120 - Z.of_nat 8)%Z with (q + -6128)%Z in ST, XBb by lia.
    assert (Hcv3 : (q - 8656 <= q + -6128 - Z.of_nat (Z.to_nat 2184))%Z) by lia;
    (nelim (stk_carve img_segs _ _ _ (Z.to_nat 2184) ST Hcv3) 3%nat; intros ST' junkc XBc); clear ST Hcv3; rename ST' into ST;
    replace (q + -6128 - Z.of_nat (Z.to_nat 2184))%Z with (q + -8312)%Z in ST, XBc by lia.
    zs.
    release_frame XBc ST (q + -6128)%Z. release_frame XBb ST (q + -6120)%Z. release_frame XBa ST (q + -120)%Z.
    sc_clear; clear junka junkb junkc.
    let n := eval vm_compute in (Z.to_nat 8192) in
    assert (Hcv : (q - 8656 <= q + -120 - Z.of_nat n)%Z) by (change (Z.of_nat n) with 8192%Z; lia);
    (nelim (stk_carve img_segs _ _ _ n ST Hcv) 3%nat; intros ST' junkx XB2); clear ST Hcv; rename ST' into ST;
    change (Z.of_nat n) with 8192%Z in ST, XB2.
    replace (q + -120 - 8192)%Z with (q + -8312)%Z in ST, XB2 by lia.
    pose proof XB2 as XB0. destruct XB0 as [[[LB _] _] _]. cbn in LB.
    apply u8arr_of_rw_cells in XB2.
    (nelim (u32arr_of_u8arr img_segs _ _ _ 2048%nat XB2 ltac:(rewrite LB; reflexivity)) 3%nat; intros ws0 LW0 XW). clear XB2 LB junkx.
    zs. zs.
    replace (Z_to_bv 64 (q + -6128 + -2048 + -240))%Z with SPv by (f_equal; lia).
    carve_frame 104%nat ST. rename FR into LOW.
    apply (rw_cells_split_CB _ _ _ [] 104 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in LOW; [|reflexivity]. cbn [mk_CB_cells app] in LOW.
    do 11 (c8ify LOW).
    lazymatch type of LOW with rw_cells _ _ _ [CB 8 ?a; C8 ?b1; C8 ?b2; C8 ?b3; C8 ?b4; C8 ?b5; C8 ?b6; C8 ?b7; C8 ?b8; C8 ?b9; C8 ?b10; C8 ?b11; CB 8 ?c] =>
      set (j0 := a) in LOW; set (w8 := b1) in LOW; set (w16 := b2) in LOW; set (w24 := b3) in LOW; set (w32 := b4) in LOW;
      set (w40 := b5) in LOW; set (w48 := b6) in LOW; set (w56 := b7) in LOW; set (w64 := b8) in LOW; set (w72 := b9) in LOW;
      set (w80 := b10) in LOW; set (w88 := b11) in LOW; set (b96 := c) in LOW;
      clearbody j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 end.
    match goal with H : list byte |- _ => try clear H end.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    (* [comment removed for export] *)
    zs. br10 K1. zs. zs. br10 K2. zs. zs. br10 K3. zs. zs. zs. zs. zs. zs.
    clear K1 K2 K3.
    (* [comment removed for export] *)
    assert (HT : forall sg c2 f2,
      (if ((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z then ((1 - 2 * b2z (fst (sh_getc f0) =? 45))%Z, fst (sh_getc (snd (sh_getc f0))), snd (sh_getc (snd (sh_getc f0)))) else (1%Z, fst (sh_getc f0), snd (sh_getc f0))) = (sg, c2, f2) ->
      FS_tail sg c2 f2 = Some (fR, yR)).
    { intros sg c2 f2 E.
      assert (FC2 : fch c2).
      { destruct ((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z eqn:Eb; injection E as E1 E2 E3; subst c2; [|exact FCH1].
        apply (getc_fch (kmin0 + 1) (fst (sh_getc f0))); [exact RJ1|].
        intros E0. rewrite E0 in Eb. discriminate Eb. }
      (nelim (fch_facts _ FCH1) 11%nat; intros _ _ _ _ _ _ _ _ _ NSP _).
      (nelim (fch_facts _ FC2) 9%nat; intros _ _ _ _ _ _ M105 M110 _).
      unfold G_floatscan_common.FS_tail. rewrite Efu. rewrite <- (floatscan_front fu f0 sg c2 f2 NSP E M105 M110). exact HM'. }
    clear HM'.
    (nelim (fch_facts _ FCH1) 12%nat; intros _ _ _ _ _ _ _ _ _ _ N32 N9).
    (* [comment removed for export] *)
    destruct (Z.eq_dec (T + sh_rpos f0)%Z (rf_rend T p true f0)) as [SLOW|FAST].
    - pose proof FC as FC0. ufc2 FC.
      zs. zs. zs. br01 K1.
      zs. zs.
      (nelim (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) 5%nat; intros STD EJ Hn Hrpe Hc00).
      destruct (ST0 STD) as [TXT Hpre].
      call_split 160%Z (eapply SPEC_shgetc_callJ with (pre := pre) (post := post);
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp
        | eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
      match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H end.
      match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
      set (c1 := fst (sh_getc f0)) in *.
      zs. zs. brfw K2.
      + zs. brfw K3.
        * exfalso. clear -K3 N32 Rc1. rewrite ?land_W64 in K3. Z.div_mod_to_equations; lia.
        * eapply L_554; try eassumption; try glia. mk_winv2.
      + exfalso. clear -K2 N9 Rc1. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
    - pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ Hc0 FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
      pose proof (txt_char (sh_rpos f0) ltac:(unfold zlength in *; lia)) as Rch.
      ufc2 FC.
      zs. zs. zs. br10 K1.
      zs. zs0. read_char f0.
      set (c1 := znth txt (sh_rpos f0)) in *.
      zs. zs. brfw K2.
      + exfalso. clear -K2 N9 Rch. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
      + zs. brf K3.
        * exfalso. clear -K3 N32 Rch. rewrite ?land_W64 in K3. Z.div_mod_to_equations; lia.
        * eapply L_554; try eassumption; try glia. mk_winv2.
  Qed.

End Floatscan.

End Img.
