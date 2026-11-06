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
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import GRoTab. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt2.
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
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_floatscan_T : CodeAtT img_segs (sym 0x1e0cc) (floatscan_prog_at IMG)}.
  Context {RB_floatscan_T : RelCode (sym 0x1e0cc) 5768}.
  Context {CODE_floatscan_T_1 : CodeAtT img_segs (sym 0x15f44) (floatscan_prog_r1_at IMG)}.
  Context {RB_floatscan_T_1 : RelCode (sym 0x15f44) 12}.
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
  Collection ImgHyps := IMG CODE_floatscan_T RB_floatscan_T CODE_floatscan_T_1 RB_floatscan_T_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_shgetc_callJ SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.
  Local Ltac clear_img := clear - IMG CODE_floatscan_T RB_floatscan_T CODE_floatscan_T_1 RB_floatscan_T_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_shgetc_callJ SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.


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
  Ltac nlia := first [ assumption | apply not_eq_sym; assumption | lia ].
  (* [comment removed for export] *)
  Ltac br10 K := brf K; [ exfalso; lia | ].
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

  Hypothesis HS_U1A8 : S_U1A8.

  (* [comment removed for export] *)
  Lemma lor_shl32 : forall k, (0 <= k < 2^31)%Z -> (Z.lor (Z.land (Z.shiftl k 32) 18446744073709551615) 4294967295 + 1 = (k + 1) * 4294967296)%Z.
  Proof.
    clear_img. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
    rewrite land_W64, (Z.mod_small (k * 4294967296)) by lia.
    rewrite <- Z.lxor_lor. 2:{ change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. rewrite Z.mod_mul. reflexivity. lia. }
    rewrite <- Z.add_nocarry_lxor. { lia. }
    change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. apply Z.mod_mul. lia.
  Qed.
  Lemma tz_dec32 : forall j, Z_to_bv 64 ((j + 1) * 4294967296 + 18446744069414584320) = Z_to_bv 64 (j * 4294967296).
  Proof. clear_img. intros j. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
  Lemma df_tz_loop_step : forall n x z, df_tz_loop (S n) x z = if (znth x (z - 1) =? 0)%Z then df_tz_loop n x (z - 1) else Some z.
  Proof. reflexivity. Qed.
  Lemma df_al_loop_step : forall n p10 z s, df_al_loop (S n) p10 z s = if negb (al_k s =? z)%Z then df_al_loop n p10 z (df_al_body p10 s) else Some s.
  Proof. reflexivity. Qed.
  Lemma divuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
    v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
  Proof.
    clear_img. intros v i Hv Hi. unfold v_divuw. rewrite !unsigned_lit by lia.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
    rewrite (Z.mod_small i), (Z.mod_small v) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
    assert (0 <= v / i < 2147483648)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite swrap32_eq. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma magic_q9 : forall rp, (-2^20 <= rp <= 2^20)%Z ->
    (Z.shiftr (bv_signed (Z_to_bv 64 (Z.land rp 18446744073709551615 * 954437177))) 33
     + Z.shiftr (Z.land (Z.land rp 18446744073709551615 * 954437177) 18446744073709551615) 63 = Z.quot rp 9)%Z.
  Proof.
    clear_img. intros rp Hrp.
    rewrite (Z_to_bv_eqm (Z.land rp 18446744073709551615 * 954437177) (rp * 954437177)).
    2:{ rewrite land_W64. apply Z.mul_mod_idemp_l. lia. }
    rewrite signed_of_Z by lia. rewrite !land_W64. rewrite Z.mul_mod_idemp_l by lia.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^33)%Z with 8589934592%Z. change (2^63)%Z with 9223372036854775808%Z. change (2^64)%Z with 18446744073709551616%Z.
    pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
    assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (intros; apply Z.rem_nonneg; lia).
    assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (intros; apply Z.rem_nonpos; lia).
    set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma rem9_fix : forall rp, (-2^20 <= rp <= 2^20)%Z ->
    bv_swrap 32 (Z.land (bv_swrap 32 (Z.land rp 18446744073709551615 - Z.land (Z.quot rp 9) 18446744073709551615)) 18446744073709551615
                 - Z.land (Z.shiftl (Z.land (Z.quot rp 9) 18446744073709551615) 3) 18446744073709551615) = Z.rem rp 9.
  Proof.
    clear_img. intros rp Hrp. rewrite !land_W64, !swrap32_eq, Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. change (2^64)%Z with 18446744073709551616%Z.
    pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
    set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma shr63_neg : forall v, (-2^63 <= v < 0)%Z -> Z.shiftr v 63 = (-1)%Z.
  Proof. clear_img. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
  Lemma shr63_nonneg : forall v, (0 <= v < 2^63)%Z -> Z.shiftr v 63 = 0%Z.
  Proof. clear_img. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
  Lemma shr30_4z : forall z, (0 <= z)%Z -> Z.shiftr (z * 4294967296) 30 = (4 * z)%Z.
  Proof. clear_img. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. change (2^30)%Z with 1073741824%Z. Z.div_mod_to_equations. lia. Qed.
  Lemma zext32_small : forall v, (0 <= v < 2^32)%Z -> Z.land v 4294967295 = v.
  Proof. clear_img. intros v Hv. change 4294967295%Z with (2^32 - 1)%Z. apply land_mask_small; lia. Qed.

  (* [comment removed for export] *)
  Lemma L_TZL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign (x : list Z) (rp kz j z : Z),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
    xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 41)%Z -> znth x 0 <> 0%Z -> (1 <= j <= kz)%Z ->
    df_tz_loop n x j = Some z ->
    (forall x15', (1 <= z <= j)%Z -> znth x (z - 1) <> 0%Z ->
       evt img_segs POST
         (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 (kz - z + 1)) (Z_to_bv 64 (XA + 4 * (z - 2))) (Z_to_bv 64 z) (Z_to_bv 64 18446744069414584320) x15' x16 x17
                  x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
             Ft (Z_to_bv 64 (sym 0x1e0cc + 3088)) fct None m (seg_rom img_segs))) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 ((j + 1) * 4294967296)) (Z_to_bv 64 (kz - j)) (Z_to_bv 64 (XA + 4 * (j - 1))) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 18446744069414584320) x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3064)) fct None m (seg_rom img_segs)).
  Proof.
    induction n as [|n IH]; intros until z; intros DI XR X31H Rkz Hx0 Rj HL CONT; [discriminate HL|].
    pose proof DI as DI'. dest_dfinv DI'. (nelim XR 3%nat; intros LW' LX REL). bury_disj.
    rewrite df_tz_loop_step in HL.
    assert (Kin : inring 0 kz (j - 1)) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
    pose proof (X31H (j - 1)%Z) as Rt. pose proof (REL (j - 1)%Z ltac:(lia) Kin) as Et.
    pose proof (u32arr_read img_segs _ _ _ (j - 1)%Z _ _ XW (nth_error_wnth ws (j - 1)%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. rewrite (sx32_wval ws (j - 1)%Z (znth x (j - 1)) (eq_sym Et) Rt). set (t := znth x (j - 1)) in *. clear RD.
    zs. zs. rewrite tz_dec32. zs. replace (j + 1 + -1)%Z with j by lia. zs. replace (XA + 4 * (j - 1) + -4)%Z with (XA + 4 * (j - 1 - 1))%Z by lia.
    zs. brf K1.
    - (* [comment removed for export] *)
      replace (t =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
      assert (Hj1 : j <> 1%Z) by (intros E; apply Hx0; subst t; rewrite E in K1; exact K1).
      replace (kz - j + 1)%Z with (kz - (j - 1))%Z by lia. replace (j * 4294967296)%Z with ((j - 1 + 1) * 4294967296)%Z by (f_equal; lia).
      replace (Z_to_bv 64 j) with (Z_to_bv 64 (j - 1 + 1)) by (f_equal; lia).
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz (j - 1)%Z z);
        [exact DI | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HL | ].
      intros x15' Rz Hnz. eapply CONT; [lia | exact Hnz].
    - replace (t =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). injection HL as <-.
      replace (j - 1 - 1)%Z with (j - 2)%Z by lia.
      eapply CONT; [lia | subst t; exact K1].
  Qed.

  (* [comment removed for export] *)
  Lemma L_UPI : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (rp a z : Z),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z ->
    xrel ws x (inring 0 z) -> X31 x -> (0 <= a < z)%Z -> (1 <= z <= 42)%Z -> (-2^16 <= rp <= 2^16)%Z ->
    dfK_up 53 (-1074) sign fR rp a z 0 x = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3356)) fct None m (seg_rom img_segs)).
  Proof.
    intros until z. intros DI RJ Hk FOK FRM' Hsg XR X31H Ra Rz Rrp HK.
    unfold dfK_up in HK. destruct (df_up_loop FUEL_SCALE _) as [[rp' a' z' e2' x']|] eqn:HL; [|discriminate HK].
    pose proof DI as DI'. dest_dfinv DI'. bury_disj.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    stmt HS_U1A8. eapply (NX 2000%nat) with (h := false) (x := x) (s' := mkUS rp' a' z' e2' x');
      [exact DI | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | lia | | exact X31H | lia | intros _; lia | lia | lia | cbn; lia | unfold FUEL_SCALE in HL; exact HL | ].
    - eapply xrel_iff; [| exact XR]. intros i Hi [Hr | [Hr _]]; [| discriminate Hr]. unfold inring in Hr |- *. clear -Hr Hi Ra Rz. Z.div_mod_to_equations. nia.
    - unfold up_K, fin_K0. cbn [us_rp us_a us_z us_e2 us_x]. unfold dfK_dn in HK.
      destruct (df_dn_loop FUEL_SCALE _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate HK]. cbn [ds_a ds_z ds_x ds_e2].
      cbv beta zeta in HK. change (- (-1074) - 53 + 3)%Z with 1024%Z in HK. fold zero0 in HK.
      destruct (df_final _ _ _ _ _ _ _ _ _ _) as [y|]; [|discriminate HK]. injection HK as <-. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma L_ALK : forall (n : nat) m (x1 x6 x7 x8 x9 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign (x : list Z) (k carry a rp z p10 j10 rpm9 kz rp0 : Z) (s1 : st_al),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
    xrel ws x (inring 0 z) -> X31 x ->
    (1 <= z <= 41)%Z -> (0 <= k < z)%Z -> (0 <= a <= k)%Z -> (a = k -> carry <> 0%Z \/ (k = 0%Z /\ znth x 0 <> 0%Z)) ->
    (0 <= carry < 2^30)%Z -> (0 <= j10 <= 7)%Z -> p10 = znth p10s j10 -> (rp0 - 9 * k <= rp <= rp0)%Z -> (-2^15 <= rp0 <= 2^15)%Z ->
    (1 <= rpm9 <= 8)%Z -> (1 <= kz <= 41)%Z ->
    df_al_loop n p10 z (mkAL k a rp carry x) = Some s1 ->
    (forall m' ws' (x6' x7' x28' : word),
       dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
       xrel ws' (al_x s1) (inring 0 z) -> X31 (al_x s1) -> al_k s1 = z ->
       (0 <= al_a s1 <= z)%Z -> (al_a s1 = z -> al_carry s1 <> 0%Z) -> (0 <= al_carry s1 < 2^30)%Z -> (rp0 - 9 * z <= al_rp s1 <= rp0)%Z ->
       evt img_segs POST
         (MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * z)) x6' x7' x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) (Z_to_bv 64 (al_carry s1)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
                  (Z_to_bv 64 z) (Z_to_bv 64 (al_a s1)) x20 x21 x22 (Z_to_bv 64 (al_rp s1)) (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
             Ft (Z_to_bv 64 (sym 0x1e0cc + 3304)) fct None m' (seg_rom img_segs))) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 carry) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3264)) fct None m (seg_rom img_segs)).
  Proof.
    induction n as [|n IH]; intros until s1; intros DI FOK FRM' XR X31H Rz Rk Ra Hak Rc Rj Hp10 Rrp Rrp0 Rrpm9 Rkz HL CONT; [discriminate HL|].
    pose proof DI as DI'. dest_dfinv DI'. (nelim XR 3%nat; intros LW' LX REL). bury_disj.
    rewrite df_al_loop_step in HL. cbn [al_k] in HL.
    replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in HL.
    unfold df_al_body in HL. cbn [al_k al_x al_a al_rp al_carry] in HL.
    destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10]. rewrite <- Hp10 in Rp10, Dp10.
    assert (Kin : inring 0 z k) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
    pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) Kin) as Et.
    pose proof (u32arr_read img_segs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
    zs. rewrite divuw_small by lia.
    pose proof (Z.mod_pos_bound t p10 ltac:(lia)) as Rtm.
    assert (Rtq : (0 <= t / p10 < 214748365)%Z) by (clear -Rt Rp10; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | nia]]).
    zs. fixw3. fixw.
    set (v := (t / p10 + carry)%Z) in *.
    assert (Rv : (0 <= v < 2^31)%Z) by (clear -Rtq Rc; subst v; lia).
    zs. zs.
    pose proof (u32arr_store_ok img_segs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
    zs.
    pose proof (u32arr_write img_segs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
    assert (Rc' : (0 <= t mod p10 * (1000000000 / p10) < 1000000000)%Z).
    { clear -Rtm Rp10 Dp10. set (u := (t mod p10)%Z) in *. set (w := (1000000000 / p10)%Z) in *. clearbody u w. nia. }
    set (carry' := (t mod p10 * (1000000000 / p10))%Z) in *.
    rewrite (u32_id v) in HL by (clear -Rv; lia). rewrite (Z.mul_comm (1000000000 / p10) (t mod p10)) in HL. fold carry' in HL. rewrite (u32_id carry') in HL by (clear -Rc'; lia).
    set (x' := zupd x k v) in *.
    assert (Exk : znth x' k = v) by (clear -LX Rk Rz; subst x'; rewrite znth_zupd_eq by (unfold zlength; lia); reflexivity). rewrite Exk in HL.
    assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (inring 0 z)).
    { clear -LW' LX REL Rk Rz Rv. split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
      intros q0 Hq Hr. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne].
      - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
      - rewrite znth_zupd_neq by nlia. rewrite wval_upd_other by nlia. apply REL; [lia | exact Hr]. }
    assert (X31' : X31 x').
    { clear -X31H LX Rk Rz Rv. intros q0. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); exact Rv | rewrite znth_zupd_neq by nlia; apply X31H]. }
    pose proof (lor_lxor_nonneg k a v ltac:(lia) ltac:(lia) ltac:(lia)) as Rw.
    (* [comment removed for export] *)
    assert (G0FC : forall (cb : bool),
      cb = (0 <? Z.lor (Z.lxor k a) v)%Z ->
      evt img_segs POST
        (MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 t) (Z_to_bv 64 (t / p10)) x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
                 (Z_to_bv 64 z) (Z_to_bv 64 (if cb then a else a + 1)%Z) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 (Z_to_bv 64 v) x29 x30 x31)
            Ft (Z_to_bv 64 (sym 0x1e0cc + 3224)) fct None m1 (seg_rom img_segs))).
    { intros cb Hcb.
      assert (Ecb : cb = negb ((k =? a) && (v =? 0))%Z).
      { rewrite Hcb. clear -Rw Rk Ra Rv. destruct ((k =? a) && (v =? 0))%Z eqn:Eb; cbn [negb].
        - apply andb_prop in Eb. destruct Eb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
          apply Z.ltb_ge. rewrite (proj2 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia)) (conj E1 E2)). lia.
        - apply Z.ltb_lt. assert (Hne : Z.lor (Z.lxor k a) v <> 0%Z); [|lia].
          intros E0. apply (proj1 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia))) in E0. destruct E0 as [E1 E2].
          apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; apply Z.eqb_neq in Eb; lia. }
      zs. zs. rewrite <- Hcb. zs. zs. fixw3. fixw. replace (t - t / p10 * p10)%Z with (t mod p10)%Z by (rewrite Zmod_eq_full by lia; lia).
      zs. zs. try rewrite (land_W64_small (t mod p10)) by (clear -Rtm; lia). try rewrite (swrap32_small (t mod p10 * (1000000000 / p10))) by (clear -Rc'; lia). fold carry'.
      zs. zs. rewrite rp_upd. zs. replace (XA + 4 * k + 4)%Z with (XA + 4 * (k + 1))%Z by lia.
      set (a2 := (if cb then a else a + 1)%Z) in *. set (rp2 := (if cb then rp else rp - 9)%Z) in *.
      assert (Ea2 : (if (k =? a) && (v =? 0) then (Z.land (a + 1) MASK, rp - 9) else (a, rp))%Z = (a2, rp2)).
      { subst a2 rp2. rewrite Ecb. destruct ((k =? a) && (v =? 0))%Z; cbn [negb]; [|reflexivity]. change MASK with 2047%Z. rewrite land2047, Z.mod_small by lia. reflexivity. }
      rewrite Ea2 in HL. clear Ea2.
      assert (Ra2 : (0 <= a2 <= k + 1)%Z) by (subst a2; destruct cb; lia).
      assert (Hak2 : (a2 = k + 1 -> carry' <> 0)%Z).
      { subst a2. rewrite Ecb. destruct (Z.eqb_spec k a) as [Eka|Hka]; destruct (Z.eqb_spec v 0) as [Ev|Hv]; cbn [andb negb]; try lia.
        intros _. destruct (Hak (eq_sym Eka)) as [Hc | [Hk0 Hx0]]; [exfalso; subst v; lia|].
        assert (Ht0 : t <> 0%Z) by (subst t; rewrite Hk0; exact Hx0).
        assert (Htp : (t < p10)%Z). { subst v. assert (t / p10 = 0)%Z by lia. destruct (Z.lt_ge_cases t p10); [assumption|]. exfalso. assert (1 <= t / p10)%Z by (apply Z.div_le_lower_bound; lia). lia. }
        subst carry'. rewrite Z.mod_small by lia. assert (10 <= 1000000000 / p10)%Z by (apply Z.div_le_lower_bound; lia).
        (* [comment removed for export] *)
        first [ apply Z.neq_mul_0; split; [ exact Ht0 | lia ] | nia ]. }
      assert (Rrp2 : (rp0 - 9 * (k + 1) <= rp2 <= rp0)%Z) by (subst rp2; destruct cb; lia).
      clearbody a2 rp2. clear Hcb Ecb.
      zs. brf K3.
      - (* [comment removed for export] *)
        destruct n as [|n']; [discriminate HL|]. rewrite df_al_loop_step in HL. cbn [al_k] in HL.
        replace (k + 1 =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in HL. injection HL as <-.
        replace (Z_to_bv 64 (XA + 4 * (k + 1))) with (Z_to_bv 64 (XA + 4 * z)) by (f_equal; lia).
        replace (Z_to_bv 64 (k + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
        eapply CONT; [mk_dfinv | exact XR' | exact X31' | cbn; lia | cbn; lia | cbn; intros E; apply Hak2; lia | cbn; lia | cbn; lia].
      - (* [comment removed for export] *)
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev _ sign x' (k + 1)%Z carry' a2 rp2 z p10 j10 rpm9 kz rp0 s1);
          [mk_dfinv | exact FOK | exact FRM' | exact XR' | exact X31' | lia | lia | lia | intros E; left; exact (Hak2 E) | lia | lia | exact Hp10 | lia | lia | lia | lia | exact HL | exact CONT]. }
    zs. brf K2.
    - (* [comment removed for export] *)
      eapply (G0FC true). symmetry. apply Z.ltb_lt. lia.
    - (* [comment removed for export] *)
      zs. zs. rewrite land2047, (Z.mod_small (a + 1) 2048) by lia. zs.
      eapply (G0FC false). symmetry. apply Z.ltb_ge. lia.
  Qed.

  Lemma L_T : S_T.
  Proof.
    intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    (nelim XR 3%nat; intros LW' LX REL).
    unfold dfK_tz in HK. destruct (df_tz_loop FUEL_RING x kz) as [z|] eqn:HTZ; [|discriminate HK]. unfold FUEL_RING in HTZ.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    rewrite lor_shl32 by lia. replace (Z.shiftl kz 2 + XA + -4)%Z with (XA + 4 * (kz - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (kz - kz)) by (f_equal; lia).
    eapply (L_TZL 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz kz z);
      [exact DI0 | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HTZ | ].
    intros x15' Rz Hnz. clear HTZ.
    unfold dfK_al in HK. unfold nz in HK.
    (* [comment removed for export] *)
    zs. fixw3. fixw. replace (kz - (kz - z + 1))%Z with (z - 1)%Z by lia.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite magic_q9 by lia. rewrite rem9_fix by lia.
    pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as Rrem.
    assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (clear; intros; apply Z.rem_nonneg; lia).
    assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (clear; intros; apply Z.rem_nonpos; lia).
    set (r9 := Z.rem rp 9) in *. assert (Rr9 : (-8 <= r9 <= 8)%Z) by (clear -Rrem; lia). clearbody r9. clear Rrem.
    zs. fixw3. fixw. replace (z - 1 + 1)%Z with z by lia.
    (* [comment removed for export] *)
    assert (G178 : forall m' ws' x' (a' rp' z' rpm9 : Z) (x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' : word),
      dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
      xrel ws' x' (inring 0 z') -> X31 x' -> (0 <= a' < z')%Z -> (1 <= z' <= 42)%Z -> (-2^15 - 9 * 42 <= rp' <= 2^15)%Z -> (1 <= rpm9 <= 8)%Z ->
      dfK_up 53 (-1074) sign fR (rp' + (9 - rpm9)) a' z' 0 x' = Some (fR, yR) ->
      evt img_segs POST
        (MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 x10' (Z_to_bv 64 rpm9) x12' x13' x14' x15'' x16' x17'
                 (Z_to_bv 64 z') (Z_to_bv 64 a') x20 x21 x22 (Z_to_bv 64 rp') (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
            Ft (Z_to_bv 64 (sym 0x1e0cc + 3348)) fct None m' (seg_rom img_segs))).
    { intros m' ws' x' a' rp' z' rpm9 x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' DI2 XR2 X312 Ra' Rz' Rrp' Rrpm9 HK2.
      clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HK. pose proof DI2 as DI'. dest_dfinv DI'.
      zs. fixw3. fixw. zs. replace (rp' - rpm9 + 9)%Z with (rp' + (9 - rpm9))%Z by lia.
      eapply L_UPI; [exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | exact XR2 | exact X312 | lia | lia | lia | exact HK2]. }
    zs. brfw K1; rewrite ?land_W64 in K1.
    - (* [comment removed for export] *)
      assert (E0 : r9 = 0%Z) by (clear -K1 Rr9; mlia).
      rewrite E0, Z.eqb_refl in HK. cbv beta iota in HK.
      zs. zs.
      eapply L_UPI; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | lia | lia | exact HK].
      eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
    - (* [comment removed for export] *)
      assert (Hne0 : r9 <> 0%Z) by (clear -K1 Rr9; mlia).
      replace (r9 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0). cbv beta iota in HK.
      (* [comment removed for export] *)
      assert (G0B4 : forall rpm9 (x14' : word), rpm9 = (if 0 <=? rp then r9 else r9 + 9)%Z -> (1 <= rpm9 <= 8)%Z ->
        evt img_segs POST
          (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) x14' x15' x16 x17
                   (Z_to_bv 64 z) x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
              Ft (Z_to_bv 64 (sym 0x1e0cc + 3152)) fct None m (seg_rom img_segs))).
      { intros rpm9 x14' Hrpm9 Rrpm9. rewrite <- Hrpm9 in HK.
        set (j10 := (8 - rpm9)%Z) in *.
        (* [comment removed for export] *)
        assert (G0E4 : forall (x16' : word),
          evt img_segs POST
            (MS (mkR x1 SPv gp TPv (Z_to_bv 64 (z - 1 + 1)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (znth p10s j10)) x16' (Z_to_bv 64 1000001536)
                     (Z_to_bv 64 z) (Z_to_bv 64 0) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
                Ft (Z_to_bv 64 (sym 0x1e0cc + 3200)) fct None m (seg_rom img_segs))).
        { intros x16'.
          destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10].
          destruct (df_al_loop FUEL_RING _ z _) as [[k1 a1 rp1 c1 x1']|] eqn:HAL; [|discriminate HK]. unfold FUEL_RING in HAL.
          zs. zs. zs. rewrite zext32_small by lia. zs. rewrite divw_small by lia. zs. zs.
          replace (Z_to_bv 64 (z - 1 + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
          replace (Z_to_bv 64 XA) with (Z_to_bv 64 (XA + 4 * 0))%Z by (f_equal; lia).
          eapply (L_ALK 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x 0%Z 0%Z 0%Z rp z (znth p10s j10) j10 rpm9 kz rp (mkAL k1 a1 rp1 c1 x1'));
            [exact DI0 | exact FOK | exact FRM' | | exact X31H | lia | lia | lia | intros _; right; split; [reflexivity | exact Hx0] | lia | lia | reflexivity | lia | lia | lia | lia | exact HAL | ].
          { eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia. }
          intros m' ws' x6' x7' x28' DI2 XR2 X312 Hk1 Ra1 Hac1 Rc1 Rrp1. cbn [al_x al_k al_a al_carry al_rp] in DI2, XR2, X312, Hk1, Ra1, Hac1, Rc1, Rrp1 |- *. subst k1.
          clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HAL LW' LX REL X31H.
          pose proof DI2 as DI'. dest_dfinv DI'. (nelim XR2 3%nat; intros LW2 LX2 REL2).
          unfold nz in HK.
          zs. brf K4.
          + (* [comment removed for export] *)
            replace (negb (c1 =? 0)) with false in HK by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia). cbv beta iota in HK.
            eapply (G178 m' ws' x1' a1 rp1 z rpm9); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | lia | lia | lia | lia | exact HK].
          + (* [comment removed for export] *)
            replace (negb (c1 =? 0)) with true in HK by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv beta iota in HK.
            zs. fixw3. fixw. replace (z - 1 + 2)%Z with (z + 1)%Z by lia.
            zs. try rewrite signed_of_Z by lia. rewrite shr30_4z by lia. zs. zs.
            pose proof (u32arr_store_ok img_segs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
            zs.
            pose proof (u32arr_write img_segs _ _ _ z (Z_to_bv 64 c1) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
            zs.
            eapply (G178 _ (upd ws' (Z.to_nat z) (Z_to_bv 64 c1)) (zupd x1' z c1) a1 rp1 (z + 1)%Z rpm9); [mk_dfinv | | | lia | lia | lia | lia | exact HK].
            * split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
              intros q0 Hq Hr. destruct (Z.eq_dec q0 z) as [->|Hne].
              -- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
              -- rewrite znth_zupd_neq by nlia. rewrite wval_upd_other by nlia. apply REL2; [lia|].
                 unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
            * intros q0. destruct (Z.eq_dec q0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by nlia; apply X312]. }
        (* [comment removed for export] *)
        zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
        assert (Hc : (rpm9 = 1 \/ rpm9 = 2 \/ rpm9 = 3 \/ rpm9 = 4 \/ rpm9 = 5 \/ rpm9 = 6 \/ rpm9 = 7 \/ rpm9 = 8)%Z) by lia.
        clear HK Hrpm9. subst j10.
        destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rpm9; (zs; eapply G0E4). }
      (* [comment removed for export] *)
      zs. try rewrite (signed_of_Z rp) by lia.
      destruct (Z.lt_ge_cases rp 0) as [Hneg|Hpos].
      + rewrite (shr63_neg rp) by lia. zs. zs. fixw3. fixw. zs. br10 K2.
        eapply G0B4; [|lia]. replace (0 <=? rp) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + rewrite (shr63_nonneg rp) by lia. zs. zs. fixw3. fixw. zs. br10 K2.
        eapply G0B4; [|lia]. replace (0 <=? rp) with true by (symmetry; apply Z.leb_le; lia). lia.
  Qed.

End Floatscan.

End Img.
