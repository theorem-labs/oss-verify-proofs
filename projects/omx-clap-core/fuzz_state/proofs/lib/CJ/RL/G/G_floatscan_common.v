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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.ProgAt3.Prog_floatscan. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require Import GRoTab.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Constr. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import NElim.
Set Default Proof Mode "Classic".

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
Section Img.
  Context {IMG : RImg}.
  Context {CODE_floatscan_common : CodeAtT img_segs (sym 0x1e0cc) floatscan_prog_std}.
  Context {RB_floatscan_common : RelCode (sym 0x1e0cc) 5768}.
  Context {CODE_floatscan_common_1 : CodeAtT img_segs (sym 0x15f44) floatscan_prog_r1_std}.
  Context {RB_floatscan_common_1 : RelCode (sym 0x15f44) 12}.
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
  Collection ImgHyps := IMG CODE_floatscan_common RB_floatscan_common CODE_floatscan_common_1 RB_floatscan_common_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.
  Local Ltac clear_img := clear - IMG CODE_floatscan_common RB_floatscan_common CODE_floatscan_common_1 RB_floatscan_common_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.


Ltac2 rec zt_plain_arith' (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
          else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
          else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
          else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
          else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
          else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
  | _ => false
  end.
Ltac2 rec zt_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => zt_codomain b
  | Constr.Unsafe.LetIn _ _ b => zt_codomain b
  | Constr.Unsafe.Cast c _ _ => zt_codomain c
  | _ => t
  end.
Ltac2 rec zt_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => zt_head f
  | Constr.Unsafe.Cast c _ _ => zt_head c
  | _ => t
  end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
  lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
  | _ => false
  end.
Ltac2 zt_is_local' (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith' ty then None
                          else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).

(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
(* [comment removed for export] *)

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Lemma land_mask_range : forall a m, (0 <= m)%Z -> (0 <= Z.land a m <= m)%Z.
Proof.
  intros a m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
  pose proof (Z.sub_land_same_l m a) as E. rewrite (Z.land_comm a m).
  assert (0 <= Z.land m (Z.lnot a))%Z by (apply Z.land_nonneg; left; exact Hm). lia.
Qed.

(* [comment removed for export] *)
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

(* [comment removed for export] *)
Lemma sx32_wval : forall ws i t, wval ws i = t -> (0 <= t < 2^31)%Z -> sx32 (wnth ws i) = Z_to_bv 64 t.
Proof.
  intros ws i t Hw Ht. unfold sx32. f_equal. unfold wval in Hw. rewrite swrap32_eq.
  pose proof (bv_unsigned_in_range 64 (wnth ws i)) as R.
  rewrite <- Hw. rewrite <- Hw in Ht. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof. intros. unfold zx32, wval. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srlw_small : forall t sh, (0 <= t < 2^31)%Z -> (0 <= sh < 32)%Z ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 t) (sh mod 32)) = Z.shiftr t sh.
Proof.
  intros t sh Ht Hsh. rewrite (Z.mod_small sh 32) by lia.
  replace (bv_wrap 32 t) with t by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
  assert (0 <= Z.shiftr t sh <= t)%Z.
  { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ sh)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia). nia. }
  apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

(* [comment removed for export] *)
Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.
Lemma remu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (Z.mod_pos_bound a b ltac:(lia)) as R.
  apply bv_eq. rewrite bv_modu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Section DivW.
  Local Open Scope Z_scope.
Lemma divw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z -> v_divw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
  intros v i Hv Hi. unfold v_divw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite (Z.mod_small i) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
  rewrite (swrap32_small v), (swrap32_small i) by lia. rewrite Z.quot_div_nonneg by lia.
  assert (0 <= v / i <= v)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia|]; nia]).
  apply swrap32_small. lia.
Qed.
Lemma p10s_range : forall j, 0 <= j <= 7 -> 10 <= znth p10s j <= 100000000 /\ (znth p10s j * (1000000000 / znth p10s j) = 1000000000)%Z.
Proof.
  intros j Hj.
  assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    match goal with |- context [znth p10s ?j] => let v := eval vm_compute in (znth p10s j) in change (znth p10s j) with v end; (split; [lia | reflexivity]).
Qed.
End DivW.

(* [comment removed for export] *)
Definition RATP : Z := (sym 0x341f8).
Definition RERRNO : Z := (sym 0x341f8 - 164).
Definition ERRNO_LOC : Z := (sym 0x15f44).

(* [comment removed for export] *)
Lemma errno_loc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (fun ms' => exists m', ms' = MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                            F (ret_pc ra) fc None m' (seg_rom img_segs)
                        /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m')
    (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ERRNO_LOC) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI. unfold ERRNO_LOC, RATP, RERRNO.
  zs. zs. zs.
  apply evt_done. eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact MI].
Qed.

(* [comment removed for export] *)
Section CallE.
  Local Open Scope Z_scope.
  Definition DS : divtf3_stmt := SPEC_divtf3_spec.
  Lemma mul_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
    stk img_segs m (q - 80) q -> mem_inv img_segs m -> (4096 <= q < 2^64)%Z ->
    al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1b3d0)) fc None m (seg_rom img_segs)).
  Proof. intros until Y. intros ST MI Hq -> -> -> ->. apply SPEC_multf3_callq; assumption. Qed.
  Lemma div_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
    stk img_segs m (q - 112) q -> mem_inv img_segs m -> (4096 <= q < 2^64)%Z ->
    al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0)) fc None m (seg_rom img_segs)).
  Proof. intros until Y. intros ST MI Hq -> -> -> ->. apply (SPEC_divtf3_callq DS); assumption. Qed.
  Lemma add_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
    stk img_segs m (q - 48) q -> mem_inv img_segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
    al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1bc80)) fc None m (seg_rom img_segs)).
  Proof. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply SPEC_addtf3_callq; assumption. Qed.
  Lemma sub_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
    stk img_segs m (q - 48) q -> mem_inv img_segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
    al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1bc70)) fc None m (seg_rom img_segs)).
  Proof. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply SPEC_subtf3_callq; assumption. Qed.
  Lemma letf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
    mem_inv img_segs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1b24c)) fc None m (seg_rom img_segs)).
  Proof. intros until Y. intros MI -> -> -> ->. apply SPEC_letf2_callv; assumption. Qed.
  Lemma getf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
    mem_inv img_segs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_ge X Y) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1b314)) fc None m (seg_rom img_segs)).
  Proof.
    intros until Y. intros MI -> -> -> ->. eapply evt_mono. { eapply SPEC_getf2. exact MI. }
    intros ms' P. unfold getf2_post in P. unfold leaf1_post. rewrite !ulit_lo64, !ulit_hi64 in P.
    change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
    rewrite F_scan_calls.f128_ge_canon in P. exact P.
  Qed.
  (* [comment removed for export] *)
  Lemma scalbn_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
    mem_inv img_segs m -> frm0 fc -> (-2^31 <= n < 2^31)%Z ->
    evt img_segs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (f15 : word) fc' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 (bvmap_set 10 (scalbn_model (reg_get F 10) n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom img_segs)
        /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m' /\ frm0 fc')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1bbd8)) fc None m (seg_rom img_segs)).
  Proof.
    intros until n. intros MI FRM Hn. eapply evt_mono. { eapply SPEC_scalbn; [exact MI | exact FRM | | exact Hn]. apply signed_of_Z; lia. }
    intros ms' P. unfold scalbn_post in P. exact P.
  Qed.
  Lemma fabsl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (al ah X : Z),
    mem_inv img_segs m -> al = lo64 X -> ah = hi64 X ->
    evt img_segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FABSL) fc None m (seg_rom img_segs)).
  Proof. intros until X. intros MI -> ->. apply SPEC_fabsl_spec; assumption. Qed.
  Lemma copysignl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
    mem_inv img_segs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    evt img_segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom img_segs)).
  Proof. intros until Y. intros MI -> -> -> ->. apply SPEC_copysignl_spec; assumption. Qed.
  (* [comment removed for export] *)
  Lemma fmodl_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (q lo al ah bl bh X Y r : Z),
    stk img_segs m lo q -> mem_inv img_segs m -> (lo <= q - 192) -> (4288 <= q < 2^63) ->
    al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
    m_fmodl X Y = Some r ->
    evt img_segs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
        ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (ret_pc ra) fc None m' (seg_rom img_segs)
        /\ munch [(q - 192, q)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
        /\ stk img_segs m' lo q /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k))
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FMODL) fc None m (seg_rom img_segs)).
  Proof.
    intros until r. intros ST MI Hlo Hq -> -> -> -> HMr.
    destruct (stk_split _ _ _ (q - 192) _ ST ltac:(lia)) as [ST1 ST2].
    eapply evt_mono. { eapply (SPEC_rfmodl_spec ra q); unfold RFMODL_DEPTH; eauto; lia. }
    intros ms' P. unfold rfmodl_post, RFMODL_DEPTH in P.
    (nelim P 21%nat; intros t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' -> MU WM MI' ST' FOK).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [|exact FOK].
    eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ].
  Qed.
End CallE.

Definition FS_DEPTH : Z := 8656.    (* [comment removed for export] *)
Definition FLOATSCAN : Z := (sym 0x1e0cc).

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
  Definition ctx_all : unit :=
    let _ := (ra, q, gp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0,
              Fp, T, p, J, txt, pre, post, canary, pok, fuelc, f0, kmin0, c0, fR, yR) in tt.

  Definition Wfs : list (Z * Z) := [(q - FS_DEPTH, q); (Fp, Fp + 232); (RERRNO, RERRNO + 4)]%Z.
  Notation TPv := (Z_to_bv 64 RATP).
  Notation SPv := (Z_to_bv 64 (q + -8416)).
  Notation XA := (q + -8312)%Z.
  Notation RFJ' := (RFJ T txt p true J).
  Definition zero0 : Z := f128_of_i32 0.

  (* [comment removed for export] *)
  Definition FokR (F' : bvmap 5 word) : Prop :=
    forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
  (* [comment removed for export] *)
  Definition Fok (F' : bvmap 5 word) : Prop :=
    forall k : bv 5, bv_unsigned k <> 8%Z -> bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
  Lemma Fok_refl : Fok F. Proof. intros k _ _ _ _. reflexivity. Qed.
  Lemma Fok_set : forall F' (r : bv 5) v, Fok F' -> (bv_unsigned r = 8 \/ bv_unsigned r = 10 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15)%Z -> Fok (bvmap_set r v F').
  Proof.
    intros F' r v H Hr k H8 H10 H14 H15. rewrite reg_get_set_other. { apply H; assumption. }
    intros E. rewrite <- E in *. lia.
  Qed.
  Lemma Fok_trans10 : forall F1 F2, Fok F1 -> (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
  Proof. intros F1 F2 H1 H2 k H8 H10 H14 H15. rewrite H2 by exact H10. apply H1; assumption. Qed.

  Definition fs_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' k' c' (ev' : word),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom img_segs)
      /\ munch Wfs m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
      /\ stk img_segs m' (q - FS_DEPTH) q
      /\ rw_cells img_segs m' Fp (rf_cells T p true fR J)
      /\ RFJ' k' c' fR /\ (0 <= k')%Z
      /\ bytes_at img_segs m' T (zbytes txt)
      /\ ssp_cells m' canary
      /\ rw_cells img_segs m' RERRNO [C4 ev']
      /\ FokR F' /\ frm0 fc'.

  (* [comment removed for export] *)
  Definition hi_cells : list cell :=
    [C8 canary; C8 (reg_get F 8); C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) : Prop :=
    mem_inv img_segs m /\ munch Wfs m0 m /\ wmono img_segs m0 m
    /\ rw_cells img_segs m (q + -120) hi_cells
    /\ stk img_segs m (q - FS_DEPTH) (q + -8416)
    /\ bytes_at img_segs m T (zbytes txt)
    /\ rw_cells img_segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells img_segs m ssp_guard [C8 canary].
  Lemma zbytes_len : length (zbytes txt) = length txt.
  Proof. unfold zbytes. apply length_map. Qed.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    (nelim H 8%nat; intros MI MU WM FRhi ST TXT SSP1 SSP2); unfold Wfs, FS_DEPTH, RERRNO in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
    unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
    try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    unfold zlength in *.
  Ltac mk_finv := unfold finv, Wfs, hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

  (* [comment removed for export] *)
  Definition framL (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word) (m : word -> option byte) : Prop :=
    rw_cells img_segs m (q + -8416) [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; CB 8 b96]
    /\ rw_cells img_segs m RERRNO [C4 ev].
  Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
  Ltac mk_framL := unfold framL, RERRNO; split; hyp.
  (* [comment removed for export] *)
  Lemma rw_cells_C8_CB8 : forall m A pre (v : word) post,
    rw_cells img_segs m A (pre ++ C8 v :: post) <-> rw_cells img_segs m A (pre ++ CB 8 (le8 v) :: post).
  Proof.
    clear_img. intros m A pre v post. unfold rw_cells, cells_at.
    rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
    rewrite length_le8. tauto.
  Qed.
  Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
  Proof.
    clear_img. intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
    pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
    rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
  Qed.
  Lemma cb8_c8_in : forall m A pre post bs, rw_cells img_segs m A (pre ++ CB 8 bs :: post) -> rw_cells img_segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
  Proof.
    clear_img. intros m A pre post bs [[Hwf Hb] Hw].
    apply cells_wf_app in Hwf. (nelim Hwf 3%nat; intros H1 H2 H3). cbn in H2.
    split; [split|].
    - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
    - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
    - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
  Qed.
  (* [comment removed for export] *)
  Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.
  Ltac lo96b H := apply (proj1 (rw_cells_C8_CB8 _ _ [_; _; _; _; _; _; _; _; _; _; _; _] _ [])) in H; cbn [app] in H.

  (* [comment removed for export] *)
  Definition xrel (ws : list word) (x : list Z) (P : Z -> Prop) : Prop :=
    length ws = 2048%nat /\ length x = 2048%nat /\ forall i, (0 <= i < 2048)%Z -> P i -> znth x i = wval ws i.

  (* [comment removed for export] *)
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

  Notation POST := (fs_post m0).

  (* [comment removed for export] *)
  Lemma txt_char : forall i, (0 <= i < zlength txt)%Z -> (0 <= znth txt i < 256)%Z.
  Proof.
    intros i Hi. pose proof (proj1 (Forall_forall _ _) BYT (znth txt i) (Shgetc_lemmas.znth_In' txt i Hi)) as R. exact R.
  Qed.
  Lemma numch_nz : forall i, (0 <= i < p)%Z -> (43 <= znth txt i <= 101)%Z.
  Proof.
    intros i Hi. pose proof (Hnum i Hi) as E. unfold is_numch in E.
    repeat (apply Bool.orb_true_iff in E; destruct E as [E|E]);
      try (apply Z.eqb_eq in E; lia). apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_release : forall m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws,
    finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr img_segs m XA ws -> length ws = 2048%nat ->
    stk img_segs m (q - FS_DEPTH) q.
  Proof.
    intros until ws. intros FI FL XW LW. dest_finv FI. dest_framL FL.
    apply u8arr_of_u32arr in XW. apply rw_cells_of_u8arr in XW. rewrite u32s_length, LW in XW.
    release_frame LOW ST (q + -8312)%Z.
    release_frame XW ST (q + -120)%Z.
    release_frame FRhi ST q.
    unfold FS_DEPTH. exact ST.
  Qed.

  (* [comment removed for export] *)
  Lemma post_tail : forall m m' K F' fc' k c ev,
    finv m -> rw_cells img_segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> rw_cells img_segs m RERRNO [C4 ev] ->
    FokR F' -> frm0 fc' -> (0 <= K <= FS_DEPTH)%Z ->
    munch [(q - K, q)]%Z m m' -> wmono img_segs m m' -> mem_inv img_segs m' ->
    stk img_segs m' (q - FS_DEPTH) q ->
    forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom img_segs)).
  Proof.
    intros until ev. intros FI FC RJ Hk ERR FOK FRM' HK MU2 WM2 MI2 ST2. intros. dest_finv FI. unfold FS_DEPTH in HK, SPLO, SPT, SG1. unfold RERRNO in *.
    unfold got_ssp, ssp_guard in SG1, SG2, SG3.
    pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
    unfold fs_post, Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
    split; [exact RJ|]. split; [exact Hk|].
    split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
    split. { split.
      - eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
      - eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
    split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
    split; [exact FOK | exact FRM'].
  Qed.

  (* [comment removed for export] *)
  Lemma L_RET34 : forall m (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
    let _ := ctx_all in
    finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr img_segs m XA ws -> length ws = 2048%nat ->
    rw_cells img_segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    yR = r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) canary x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2768)) fct None m (seg_rom img_segs)).
  Proof.
    intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
    pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. pose proof (lo64_range r). pose proof (hi64_range r).
    zs. zs. zs. zs. br K.
    zs. zs. zs. zs. do 14 zs. zs.
    pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK.
    subst r. apply evt_done. eapply (post_tail _ _ 0%Z); try eassumption.
    - intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
      + rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
      + rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
    - unfold FS_DEPTH; lia.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma L_RET1 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 b96 ev ws k c (r : Z),
    let _ := ctx_all in
    finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 ssp_guard) b96 ev m -> u32arr img_segs m XA ws -> length ws = 2048%nat ->
    rw_cells img_segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    yR = r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2416)) fct None m (seg_rom img_segs)).
  Proof.
    intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
    pose proof FI as FI0. dest_finv FI. pose proof FL as FL0. dest_framL FL. unfold ssp_guard in LOW.
    zs. zs. zs.
    eapply L_RET34; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma L_RET30 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
    let _ := ctx_all in
    finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr img_segs m XA ws -> length ws = 2048%nat ->
    rw_cells img_segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    yR = r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2764)) fct None m (seg_rom img_segs)).
  Proof.
    intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
    pose proof FI as FI0. dest_finv FI. unfold ssp_guard.
    zs.
    eapply L_RET34; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma L_SCL : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (Y e2 : Z),
    let _ := ctx_all in
    finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr img_segs m XA ws -> length ws = 2048%nat ->
    rw_cells img_segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (-2^31 <= e2 < 2^31)%Z ->
    yR = m_scalbnl Y e2 ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 5572)) fct None m (seg_rom img_segs)).
  Proof.
    intros until e2. intros _ FI FL XW LW FC RJ Hk FOK FRM' He2 Hy.
    pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. unfold ssp_guard.
    pose proof (lo64_range Y). pose proof (hi64_range Y).
    zs. zs. zs. zs. zs. br K.
    zs. zs. zs.
    zs. zs. zs. zs. do 14 zs. zs.
    pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK. unfold FS_DEPTH in STK.
    destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
    pose proof SPEC_scalbnl_spec as SS. unfold scalbnl_stmt in SS.
    eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
    intros ms' P. unfold scalbnl_post in P.
    (nelim P 19%nat; intros t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU2 WM2 MI2 ST3).
    rewrite <- Hy. eapply (post_tail m m' 112%Z); try eassumption.
    - intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
      destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
      + rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
      + rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
    - unfold FS_DEPTH; lia.
    - unfold FS_DEPTH. eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST3 | lia ].
  Qed.

  Lemma b2z_land : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b). Proof. clear_img. destruct a, b; reflexivity. Qed.
  Lemma b2z_lt1 : forall c, (Z.b2z c <? 1) = negb c. Proof. clear_img. destruct c; reflexivity. Qed.
  Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.
  Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].

  (* [comment removed for export] *)
  Definition hide (P : Prop) := P.
  Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac unstash := unfold hide in *.
  (* [comment removed for export] *)
  Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.
  (* [comment removed for export] *)
  Ltac flia := first [ solve [stash_mods; stash_disj; lia] | lia ].
  (* [comment removed for export] *)
  Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
  Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

  Lemma swrap32_landW_r : forall a c, bv_swrap 32 (c + Z.land a 18446744073709551615) = bv_swrap 32 (c + a).
  Proof. clear_img. intros. rewrite (Z.add_comm c (Z.land a _)), swrap32_landW. f_equal. lia. Qed.
  Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

  (* [comment removed for export] *)
  Definition hide2 (P : Prop) := P.
  Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
  Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
  Ltac unbury := unfold hide2 in *.
  (* [comment removed for export] *)
  Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
  (* [comment removed for export] *)
  Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  (* [comment removed for export] *)
  Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dfinv (m : word -> option byte) (j0 : list byte) (w16 w24 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
    finv m
    /\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
             (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 18396) (Z_to_bv 64 ssp_guard) b96 ev m
    /\ u32arr img_segs m XA ws /\ length ws = 2048%nat /\ rw_cells img_segs m Fp (rf_cells T p true f J).
  Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    (nelim H 5%nat; intros FI FL XW LW FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_dfinv := unfold dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  (* [comment removed for export] *)
  Definition dfinvG (m : word -> option byte) (j0 : list byte) (w16 w24 w80 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
    finv m
    /\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
             (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev m
    /\ u32arr img_segs m XA ws /\ length ws = 2048%nat /\ rw_cells img_segs m Fp (rf_cells T p true f J).
  Lemma dfinvG_dfinv : forall m j0 w16 w24 b96 ev ws sign f,
    dfinvG m j0 w16 w24 (Z_to_bv 64 18396) b96 ev ws sign f = dfinv m j0 w16 w24 b96 ev ws sign f.
  Proof. reflexivity. Qed.
  Ltac mk_dfinvG := unfold dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

  (* [comment removed for export] *)
  Definition inring (a z i : Z) : Prop := ((i - a) mod 2048 < (z - a) mod 2048)%Z.
  Lemma land2047 : forall v, Z.land v 2047 = (v mod 2048)%Z.
  Proof. clear_img. intros. change 2047%Z with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. Qed.
  Lemma landW_mod2048 : forall v, ((Z.land v 18446744073709551615) mod 2048 = v mod 2048)%Z.
  Proof. clear_img. intros. rewrite land_W64. apply Z.mod_mod_divide. exists (2^53)%Z. reflexivity. Qed.
  Ltac fixk := rewrite ?land2047, ?landW_mod2048 in *.
  Lemma inring_plus : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> (d <= (z - a) mod 2048)%Z -> Z.land (a + d) 2047 <> z ->
    inring a z (Z.land (a + d) 2047) /\ (d + 1 <= (z - a) mod 2048)%Z.
  Proof. clear_img.
    intros a z d Hz Hd Hle Hne. rewrite land2047 in *. unfold inring.
    rewrite Zminus_mod_idemp_l. replace (a + d - a)%Z with d by lia. rewrite (Z.mod_small d 2048) by lia.
    pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)).
    assert ((z - a) mod 2048 <> d)%Z; [|lia].
    intros Ed. apply Hne. rewrite <- (Z.mod_small z 2048) by lia.
    rewrite <- Ed. rewrite Zplus_mod_idemp_r. f_equal. lia.
  Qed.
  Lemma inring_hit : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> Z.land (a + d) 2047 = z -> ((z - a) mod 2048 = d)%Z.
  Proof. clear_img.
    intros a z d Hz Hd E. rewrite land2047 in E. rewrite <- E. rewrite Zminus_mod_idemp_l.
    replace (a + d - a)%Z with d by lia. apply Z.mod_small. lia.
  Qed.
  Lemma inring_grow : forall a z i, (0 <= z)%Z -> ((z - a) mod 2048 < 2047)%Z ->
    inring a (z + 1) i <-> (inring a z i \/ (i - a) mod 2048 = (z - a) mod 2048)%Z.
  Proof. clear_img.
    intros a z i Hz Hlt. unfold inring.
    replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)).
    pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)). pose proof (Z.mod_pos_bound (i - a) 2048 ltac:(lia)).
    rewrite (Z.mod_small ((z - a) mod 2048 + 1)) by lia. lia.
  Qed.
  Lemma mod_eq_idx : forall a z i, (0 <= z < 2048)%Z -> (0 <= i < 2048)%Z -> ((i - a) mod 2048 = (z - a) mod 2048)%Z -> i = z.
  Proof. clear_img.
    intros a z i Hz Hi E.
    rewrite <- (Z.mod_small i 2048), <- (Z.mod_small z 2048) by lia.
    transitivity (((i - a) mod 2048 + a) mod 2048)%Z. { rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite E. rewrite Zplus_mod_idemp_l. f_equal. lia.
  Qed.
  Lemma inring_mod : forall a z i, inring a (z mod 2048) i <-> inring a z i.
  Proof. clear_img. intros. unfold inring. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
  Lemma xrel_iff : forall ws x (P Q : Z -> Prop), (forall i, (0 <= i < 2048)%Z -> Q i -> P i) -> xrel ws x P -> xrel ws x Q.
  Proof. clear_img. intros ws x P Q HPQ (L1 & L2 & R). split; [exact L1|]. split; [exact L2|]. intros i Hi Hq. apply R; [exact Hi | apply HPQ; [exact Hi | exact Hq]]. Qed.
  (* [comment removed for export] *)
  Definition zone (h w : bool) (a z : Z) (i : Z) : Prop := inring a z i \/ (h = true /\ (z <= i)%Z) \/ (w = true /\ (a <= i)%Z).
  Lemma zone_in : forall h w a z i, inring a z i -> zone h w a z i.
  Proof. clear_img. intros. left. assumption. Qed.
  Lemma xrel_window : forall ws x h w a z, xrel ws x (zone h w a z) -> xrel ws x (inring a z).
  Proof. clear_img. intros until z. apply xrel_iff. intros i _ Hi. left. exact Hi. Qed.
  Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.
  (* [comment removed for export] *)
  Definition X31 (x : list Z) : Prop := forall i, (0 <= znth x i < 2^31)%Z.

  (* [comment removed for export] *)
  Definition S_F3 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
      j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
    let _ := ctx_all in
    dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
    fin_K3 1024 Y FR BI e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
               (Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 5296)) fct None m (seg_rom img_segs)).

  Lemma f128_ge_range : forall a b, (-1 <= f128_ge a b <= 1)%Z.
  Proof.
    clear_img. intros a b. unfold f128_ge.
    repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => fail end; try (cbn; lia)).
    all: try (unfold nez64, b2z; destruct (negb _); cbn; lia).
  Qed.
  (* [comment removed for export] *)
  Tactic Notation "call_split" constr(K) tactic3(tac) :=
    lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
      let ST1 := fresh "ST1" in
      destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
      callw tac;
      lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
        lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
        pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
    end.

  (* [comment removed for export] *)
  Lemma extenddftf2_callF : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F' : bvmap 5 word) fc' (m : word -> option byte) (D : Z),
    mem_inv img_segs m -> bv_unsigned (reg_get F' 10) = D ->
    evt img_segs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_d D) m)
      (MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F' (Z_to_bv 64 (sym 0x1af98)) fc' None m (seg_rom img_segs)).
  Proof.
    clear_img. intros until D. intros MI HD. eapply evt_mono. { eapply SPEC_extenddftf2. exact MI. }
    intros ms' P. unfold extenddftf2_post in P. rewrite HD in P. exact P.
  Qed.

  (* [comment removed for export] *)
  Definition S_F2 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (a z Y FR BI e2 bits' : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
    xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
    (Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
    fin_K2 sign 1024 a z x 4 bits' Y FR BI e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
               (Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 5000)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Lemma floatsitf_callsg : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F' : bvmap 5 word) fc' (m : word -> option byte) (sg : Z),
    mem_inv img_segs m -> (sg = 1 \/ sg = -1)%Z ->
    evt img_segs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_i32 sg) m)
      (MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 sg) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F' (Z_to_bv 64 (sym 0x1bad0)) fc' None m (seg_rom img_segs)).
  Proof.
    clear_img. intros until sg. intros MI [-> | ->].
    - apply SPEC_floatsitf_callp; [exact MI | lia].
    - replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      apply SPEC_floatsitf_callv; [exact MI | lia | rewrite sext32_eq; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition S_F1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (a z Y e2 : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z ->
    xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
    (Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
    fin_K1 53 (-1074) sign 1024 zero0 a z x 4 Y e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x24
               x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4764)) fct None m (seg_rom img_segs)).

  Lemma lxor_sign_small : forall e, (-2^62 <= e < 2^62)%Z ->
    Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 = (e + 2^63)%Z.
  Proof.
    clear_img. intros e He. rewrite land_W64. change 9223372036854775808%Z with (2^63)%Z.
    rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma clamp0_idiom : forall v, (-2^62 <= v < 2^62)%Z ->
    Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land v 18446744073709551615) 9223372036854775808)) 18446744073709551615)
           (Z.land v 18446744073709551615) = (if v <? 0 then 0 else v)%Z.
  Proof.
    clear_img. intros v Hv. rewrite lxor_sign_small by lia.
    destruct (Z.ltb_spec 9223372036854775808 (v + 2^63)); destruct (Z.ltb_spec v 0); try lia; cbn [Z.b2z].
    - change (Z.land (0 - 1) 18446744073709551615)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite land_W64, Z.mod_mod by lia. apply Z.mod_small. lia.
    - change (Z.land (0 - 0) 18446744073709551615)%Z with 0%Z. apply Z.land_0_l.
    - assert (E : v = 0%Z) by lia. rewrite E. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Ltac eval_lands := repeat match goal with |- context [Z.land ?a ?b] =>
    lazymatch isZcst a with true => lazymatch isZcst b with true =>
      let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v end end end.
  Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].

  (* [comment removed for export] *)
  Lemma cb44_merge : forall m A pre (bs : list byte) (w : word),
    rw_cells img_segs m A (pre ++ [CB 4 bs; C4 w]) -> rw_cells img_segs m A (pre ++ [CB 8 (bs ++ le4 w)]).
  Proof.
    clear_img. intros m A pre bs w [[Hwf Hb] Hw].
    apply cells_wf_app in Hwf. (nelim Hwf 3%nat; intros H1 H2 _). cbn in H2.
    split; [split|].
    - apply cells_wf_app. split; [exact H1|]. split; [|exact I]. cbn -[le4]. rewrite length_app, H2, length_le4. reflexivity.
    - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite <- app_assoc, app_nil_r in *. exact Hb.
    - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
  Qed.
  Definition C1E9HI : Z := 0x401cdcd650000000.

  (* [comment removed for export] *)
  Definition ainv (ws : list word) (x : list Z) (h w : bool) (a z i : Z) : Prop :=
    xrel ws x (zone h w a z) /\ X31 x /\ (0 <= z < 2048)%Z /\ (h = false -> z + (4 - i) <= 2052)%Z /\ (i <= (z - a) mod 2048)%Z /\ (w = false -> a <= 60)%Z.

  (* [comment removed for export] *)
  Definition S_A69C : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
    ainv ws x h w a z 3 ->
    df_asm_loop f a (mkAS 3 Y z x) = Some sres -> (2 <= f)%nat ->
    fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
               x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4664)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_A62C : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
    ainv ws x h w a z 2 ->
    df_asm_loop f a (mkAS 2 Y z x) = Some sres -> (3 <= f)%nat ->
    fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) (Z_to_bv 64 XA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
               x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4552)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_A5C4 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
    ainv ws x h w a z 1 ->
    df_asm_loop f a (mkAS 1 Y z x) = Some sres -> (4 <= f)%nat ->
    fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
               x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4448)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition fin_K0 (sign a z : Z) (x : list Z) (e2 : Z) : option Z := df_final a z x e2 53 (-1074) sign 1024 zero0 zero0.

  (* [comment removed for export] *)
  Definition S_A568 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 xa : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
    ainv ws x h w a z 0 -> a <> z -> xa = znth x a ->
    fin_K0 sign a z x e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 xa) x23 x24
               x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4356)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_A534 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 S1 : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
    ainv ws x h w a z 0 -> a = z -> S1 = (4 * ((z + 1) mod 2048))%Z ->
    fin_K0 sign a z x e2 = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 ((z + 1) mod 2048)) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 x23 x24
               x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4304)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition SN324 (fo : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 Z0 S1 A6 : Z) s',
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
    xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
    (-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
    Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
    df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
    fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3776)) fct None m (seg_rom img_segs)).
  Definition S_N324 : Prop := forall fo, SN324 fo.

  (* [comment removed for export] *)
  Definition S_N2D4 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 : Z) s',
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
    xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
    (-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
    df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
    fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3696)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition up_K (sign rp a z e2 : Z) (x : list Z) : option Z :=
    match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
    | None => None
    | Some s' => fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s')
    end.
  Definition MAGIC : Z := 19342813113834067.

  (* [comment removed for export] *)
  Definition S_U1A8 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
    xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
    (-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
    df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
    up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3396)) fct None m (seg_rom img_segs)).

  Lemma df_dn_loop_step : forall n s, df_dn_loop (S n) s = match df_dn_body s with None => None | Some (inl s') => df_dn_loop n s' | Some (inr s') => Some s' end.
  Proof. reflexivity. Qed.
  Lemma df_dni_loop_step : forall n a z x i, df_dni_loop (S n) a z x i =
    if (i <? LD_B1B_DIG)%Z then match df_dni_body a z x i with inl i' => df_dni_loop n a z x i' | inr i' => Some i' end else Some i.
  Proof. reflexivity. Qed.
  Lemma df_dnk_loop_step : forall n z sh s, df_dnk_loop (S n) z sh s = if negb (dk_k s =? z)%Z then df_dnk_loop n z sh (df_dnk_body z sh s) else Some s.
  Proof. reflexivity. Qed.
  Lemma dn_carry_bound : forall sh tmp, (sh = 1 \/ sh = 9)%Z -> (0 <= tmp <= 2^sh - 1)%Z -> (0 <= Z.shiftr 1000000000 sh * tmp < 2^30)%Z.
  Proof. clear_img. intros sh tmp [-> | ->] H; [change (Z.shiftr 1000000000 1) with 500000000%Z | change (Z.shiftr 1000000000 9) with 1953125%Z]; cbn in H; lia. Qed.
  Lemma shr_half : forall t sh, (0 <= t)%Z -> (1 <= sh)%Z -> (0 <= Z.shiftr t sh <= t / 2)%Z.
  Proof.
    clear_img. intros t sh Ht Hsh. split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_le_compat_l; [lia|]. split; [lia|]. change 2%Z with (2^1)%Z at 1. apply Z.pow_le_mono_r; lia.
  Qed.
  Lemma lor_lxor_zero : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z ->
    Z.lor (Z.lxor k a) v = 0%Z <-> (k = a /\ v = 0%Z).
  Proof.
    clear_img. intros k a v Hk Ha Hv. split.
    - intros H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2]. split; [|exact H2]. apply Z.lxor_eq_0_iff. exact H1.
    - intros [-> ->]. rewrite Z.lxor_nilpotent. reflexivity.
  Qed.
  Lemma lor_lxor_nonneg : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z -> (0 <= Z.lor (Z.lxor k a) v)%Z.
  Proof. clear_img. intros. apply Z.lor_nonneg. split; [apply Z.lxor_nonneg; lia | lia]. Qed.
  Lemma rp_upd : forall rp (c : bool),
    Z_to_bv 64 (rp + Z.land (Z.land (Z.b2z c + -1) 18446744073709551615) 18446744073709551607) = Z_to_bv 64 (if c then rp else rp - 9)%Z.
  Proof.
    clear_img. intros rp [|].
    - change (Z.land (Z.land (Z.b2z true + -1) 18446744073709551615) 18446744073709551607) with 0%Z. rewrite Z.add_0_r. reflexivity.
    - change (Z.land (Z.land (Z.b2z false + -1) 18446744073709551615) 18446744073709551607) with 18446744073709551607%Z.
      apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma dn_az_none : forall fo rp z e2 x i0, (0 <= z < 2048)%Z -> rp <> 36%Z -> df_dn_loop fo (mkDS rp z z e2 x i0) = None.
  Proof.
    clear_img. induction fo as [|fo IH]; intros rp z e2 x i0 Hz Hrp; [reflexivity|].
    rewrite df_dn_loop_step. unfold df_dn_body. cbn [ds_a ds_z ds_x ds_rp ds_e2].
    change (df_dni_loop 6 z z x 0) with (if (0 <? LD_B1B_DIG)%Z then match df_dni_body z z x 0 with inl i' => df_dni_loop 5 z z x i' | inr i' => Some i' end else Some 0%Z).
    change (0 <? LD_B1B_DIG)%Z with true. unfold df_dni_body. rewrite Z.add_0_r. change MASK with 2047%Z. rewrite land2047, Z.mod_small, Z.eqb_refl by lia. cbn [orb].
    change LD_B1B_DIG with 4%Z. change (4 =? 4)%Z with true. replace (rp =? 9 * 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    cbv zeta. unfold FUEL_RING. rewrite df_dnk_loop_step. cbn [dk_k]. rewrite Z.eqb_refl. cbn [negb nz Z.eqb].
    apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition S_NK : Prop := forall (fi : nat) m (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x20 x22 x24 x25 x26 x27 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a i rp z sh e2 B : Z) (s1 : st_dnk),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
    xrel ws x (zone h w a z) -> X31 x ->
    (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> ((k - a) mod 2048 <= (z - a) mod 2048)%Z -> k <> z ->
    (0 <= carry < 2^30)%Z -> (sh = 1 \/ sh = 9)%Z -> (B + 9 * Z.of_nat fi <= rp <= 560)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^27 <= B)%Z -> (-2^21 <= e2 <= 2^21)%Z ->
    df_dnk_loop fi z sh (mkDK k carry a i rp x) = Some s1 ->
    (forall m' ws' b96' (x17' x28' x29' x30' x31' : word) (w' : bool),
       dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
       xrel ws' (dk_x s1) (zone h w' (dk_a s1) z) -> X31 (dk_x s1) ->
       (0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> (B <= dk_rp s1 <= 560)%Z -> (w' = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> dk_k s1 = z ->
       evt img_segs POST
         (MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17'
                  (Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28' x29' x30' x31')
             Ft (Z_to_bv 64 (sym 0x1e0cc + 4128)) fct None m' (seg_rom img_segs))) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 carry) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4076)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_N484 : Prop := forall (fo : nat), SN324 fo ->
    forall (s1 : st_dnk) m (x1 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (h w : bool) (rp z e2 Z0 S1 A6 sh : Z) s',
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z ->
    xrel ws (dk_x s1) (zone h w (dk_a s1) z) -> X31 (dk_x s1) ->
    (0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> dk_k s1 = z -> (sh = 1 \/ sh = 9)%Z ->
    (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
    (-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (rp - 18450 <= dk_rp s1 <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
    Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
    (let 'mkDK _ carry a1 i rp1 xx := s1 in
     let '(z', x') := if nz carry then
                        if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
                        else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
                      else (z, xx) in
     df_dn_loop fo (mkDS rp1 a1 z' (e2 + sh) x' i) = Some s') ->
    fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
               (Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 (e2 + sh)) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 4128)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_N3E8 : Prop := forall (fo : nat), SN324 fo ->
    forall (iq : Z) m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 Z0 S1 A6 : Z) s',
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
    xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
    (-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
    Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z -> a <> z ->
    match
      match df_dnk_loop FUEL_RING z (if 45 <? rp then 9%Z else 1%Z) (mkDK a 0 a iq rp x) with
      | Some (mkDK _ carry a1 i rp1 xx) =>
          let '(z', x') := (if nz carry then
                              if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
                              else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
                            else (z, xx)) in
          Some (inl (mkDS rp1 a1 z' (e2 + (if 45 <? rp then 9%Z else 1%Z)) x' i))
      | None => None
      end
    with
    | Some (inl s'') => df_dn_loop fo s''
    | Some (inr s'') => Some s''
    | None => None
    end = Some s' ->
    fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3972)) fct None m (seg_rom img_segs)).

  Lemma df_up_loop_step : forall n s, df_up_loop (S n) s = if df_up_cond s then match df_up_body s with None => None | Some s' => df_up_loop n s' end else Some s.
  Proof. reflexivity. Qed.
  Lemma df_upk_loop_step : forall n a s, df_upk_loop (S n) a s = match df_upk_body a s with inl s' => df_upk_loop n a s' | inr s' => Some s' end.
  Proof. reflexivity. Qed.
  Lemma mod_add2047 : forall u, ((u + 2047) mod 2048 = (u - 1) mod 2048)%Z.
  Proof. clear_img. intros u. rewrite <- (Z.mod_add (u - 1) 1 2048) by lia. f_equal. lia. Qed.
  (* [comment removed for export] *)
  Lemma magic_div_1e9 : forall tmp, (0 <= tmp < 2^61)%Z ->
    (Z.shiftr ((Z.shiftr tmp 9 * MAGIC) / 2^64) 11 = tmp / 1000000000)%Z.
  Proof.
    clear_img. intros tmp Ht. unfold MAGIC. rewrite !Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by lia. change (2^64 * 2^11)%Z with (2^75)%Z.
    replace (tmp / 1000000000)%Z with ((tmp / 2^9) / 1953125)%Z by (rewrite Z.div_div by lia; f_equal).
    set (u := (tmp / 2^9)%Z). assert (Hu : (0 <= u < 2^52)%Z) by (subst u; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    clearbody u. clear Ht tmp. Z.div_mod_to_equations. nia.
  Qed.
  (* [comment removed for export] *)
  Lemma magic_div_1e9_reg : forall tmp, (0 <= tmp < 2^61)%Z ->
    Z.shiftr (Z.land (Z.shiftr (Z.shiftr tmp 9 * Z.land MAGIC 18446744073709551615) 64) 18446744073709551615) 11 = (tmp / 1000000000)%Z.
  Proof.
    clear_img. intros tmp Ht. change (Z.land MAGIC 18446744073709551615) with MAGIC.
    assert (R1 : (0 <= Z.shiftr tmp 9 < 2^52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (R2 : (0 <= Z.shiftr (Z.shiftr tmp 9 * MAGIC) 64 < 2^64)%Z).
    { unfold MAGIC. rewrite (Z.shiftr_div_pow2 _ 64) by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. nia. }
    rewrite land_W64, (Z.mod_small _ _ R2). rewrite (Z.shiftr_div_pow2 _ 64) by lia. apply magic_div_1e9. exact Ht.
  Qed.
  Lemma u32_id : forall v, (0 <= v < 2^32)%Z -> u32 v = v.
  Proof. clear_img. intros. unfold u32. apply Z.mod_small. lia. Qed.
  Lemma inring_front : forall a z i, (0 <= a < 2048)%Z -> (0 <= i < 2048)%Z -> (0 <= z < 2048)%Z ->
    inring ((a - 1) mod 2048) z i -> i <> ((a - 1) mod 2048)%Z -> z <> ((a - 1) mod 2048)%Z -> inring a z i.
  Proof. clear_img. intros a z i Ha Hi Hz H Hne Hzne. unfold inring in *. Z.div_mod_to_equations. nia. Qed.

  (* [comment removed for export] *)
  Definition S_UK : Prop := forall (n : nat) m (x1 x5 x6 x8 x9 x11 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a z : Z) (s1 : st_upk),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
    xrel ws x (zone h w a z) -> X31 x ->
    (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> inring a z k ->
    (0 <= carry < 2^31)%Z ->
    df_upk_loop n a (mkUK k carry z x) = Some s1 ->
    (forall m' ws' (x7' x18' x29' x30' x31' : word) (h' : bool),
       dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
       xrel ws' (uk_x s1) (zone h' w a (uk_z s1)) -> X31 (uk_x s1) ->
       uk_k s1 = a -> (0 <= uk_carry s1 < 2^31)%Z -> (0 <= uk_z s1 < 2048)%Z -> (h' = false -> h = false /\ uk_z s1 <= z)%Z -> a <> uk_z s1 ->
       evt img_segs POST
         (MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 (uk_z s1)) x7' x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 (uk_carry s1)) x17
                  x18' (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 ((uk_z s1 - 1) mod 2048)) x29' x30' x31')
             Ft (Z_to_bv 64 (sym 0x1e0cc + 3412)) fct None m' (seg_rom img_segs))) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry) x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3464)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition SU1C4 (fo : nat) : Prop := forall m (x1 x6 x7 x8 x9 x16 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
    xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
    (-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
    df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
    up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 (Z_to_bv 64 (XA + 4 * a))
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3424)) fct None m (seg_rom img_segs)).
  Definition S_U1C4 : Prop := forall fo, SU1C4 fo.

  (* [comment removed for export] *)
  Definition S_T : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (rp kz : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z ->
    xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (-2^15 <= rp <= 537)%Z ->
    dfK_tz 53 (-1074) sign fR rp kz x = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 3016)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_DD0 : Prop := forall m (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (X Y : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    yR = f128_mul X Y ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2412)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_DD24 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (X u : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (0 <= u < 2^31)%Z -> yR = f128_mul X (f128_of_u32 u) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 u) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2240)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_M : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (rp lnz kz : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z ->
    xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= rp <= 537)%Z ->
    dfK_mid 53 (-1074) sign fR rp lnz kz x = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2552)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition digz (k j : Z) (i : Z) : Prop := (i < k)%Z \/ i = 0%Z \/ (i = k /\ j <> 0%Z).

  (* [comment removed for export] *)
  Definition S_P : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 ev ws sign k c (x : list Z) (lrp lnz j kz : Z),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z ->
    xrel ws x (digz kz j) -> X31 x ->
    (0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= lrp <= 537)%Z ->
    (j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) ->
    dfK_pad 53 (-1074) sign fR lrp lnz j kz x = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2428)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_R : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) ev ws sign k c (x : list Z) (lrp dc lnz j kz : Z),
    let _ := ctx_all in
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z ->
    xrel ws x (digz kz j) -> X31 x ->
    (0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> (0 <= dc < 2^31)%Z -> (0 <= lnz < 2^31)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z ->
    (j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) -> (-2^62 <= lrp < 2^62)%Z ->
    (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
    dfK_rng 53 (-1074) sign fR lrp dc lnz j kz x = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2176)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition dig_facts (ws : list word) (x : list Z) (j kz dc lnz : Z) : Prop :=
    xrel ws x (digz kz j) /\ X31 x /\
    (0 <= j <= 8)%Z /\ (0 <= kz <= 2045)%Z /\ (0 <= dc < 2^31)%Z /\ (0 <= lnz < 2^31)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\
    (j <> 0%Z -> znth x kz < 10 ^ j)%Z /\ (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\ (kz = 2045%Z -> j = 0%Z).

  (* [comment removed for export] *)
  Definition S_C38 : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
    let _ := ctx_all in
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (0 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
    (0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
    (if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0) else dfK_rng 53 (-1074) sign f lrp dc lnz j kz x) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 2004)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_C2C : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
    let _ := ctx_all in
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> sh_shlim_neg f = false ->
    dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
    (0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
    (if negb (nz gotdig) then Some (sh_lim0 (sh_unget f), f128_of_i32 0) else dfK_rng 53 (-1074) sign (sh_unget f) lrp dc lnz j kz x) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1992)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_E : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig gotrad : Z),
    let _ := ctx_all in
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
    (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (- 2^31 <= lrp < 2^31)%Z ->
    dfK_exp fuelc 53 (-1074) sign pok (mkDL f c j kz lrp dc lnz gotdig gotrad x) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1616)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition digI (ws : list word) (x : list Z) (f : shfile) (c j k lrp dc lnz gotdig gotrad : Z) : Prop :=
    xrel ws x (digz k j) /\ X31 x /\ (0 <= j <= 8)%Z /\ (0 <= k)%Z /\ (9 * k + j <= dc)%Z /\
    (0 <= dc <= sh_rpos f)%Z /\ (c <> (-1)%Z -> dc + 1 <= sh_rpos f)%Z /\
    (0 <= lnz <= dc)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\ (j <> 0%Z -> znth x k < 10 ^ j)%Z /\ (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\
    (- 2^31 <= lrp < 2^31)%Z /\ (0 <= gotdig <= 1)%Z /\ (0 <= gotrad <= 1)%Z /\
    (k <= 2045)%Z /\ (k = 2045%Z -> j = 0%Z).

  (* [comment removed for export] *)
  Definition SDn (n : nat) : Prop := forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
      j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
    let _ := ctx_all in
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    digI ws x f c j k lrp dc lnz gotdig gotrad ->
    (isdigitc c || (c =? 46))%Z = true ->
    df_dig_loop n (mkDL f c j k lrp dc lnz gotdig gotrad x) = Some s' ->
    dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) (Z_to_bv 64 (Z.b2z (c =? 46)%Z)) x13 x14 x15 x16 x17
               (Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1800)) fct None m (seg_rom img_segs)).
  Definition S_D : Prop := forall n, SDn n.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition winv (m : word -> option byte) (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word)
             (ws : list word) (f : shfile) : Prop :=
    finv m /\ framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m
    /\ u32arr img_segs m XA ws /\ length ws = 2048%nat /\ rw_cells img_segs m Fp (rf_cells T p true f J).
  Lemma winv_dfinvG : forall m j0 w16 w24 w80 b96 ev ws sign f,
    winv m j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f
    = dfinvG m j0 w16 w24 w80 b96 ev ws sign f.
  Proof. reflexivity. Qed.
  Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    (nelim H 5%nat; intros FI FL XW LW FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_winv := unfold winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  (* [comment removed for export] *)
  Definition X0 : list Z := zupd (zrepeat 0 KMAX) 0 0.
  (* [comment removed for export] *)
  Definition fch (c : Z) : Prop := is_numch c = true \/ c = 0%Z \/ c = (-1)%Z.

  (* [comment removed for export] *)
  Definition S_B0C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
    let _ := ctx_all in
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
    (isdigitc c || (c =? 46))%Z = true ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1704)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_A9C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
    let _ := ctx_all in
    dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
    c <> 46%Z ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1592)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_A44 : Prop := forall m (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig : Z),
    let _ := ctx_all in
    winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> c <> 48%Z ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig 1 X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 gotdig) x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1504)) fct None m (seg_rom img_segs)).

  Lemma df_dig_loop_step : forall n s, df_dig_loop (S n) s = if df_dig_cond s then match df_dig_body s with inl s' => df_dig_loop n s' | inr s' => Some s' end else Some s.
  Proof. reflexivity. Qed.
  Lemma df_rz_loop_step : forall n g l c f, df_rz_loop (S n) (g, l, c, f) =
    (if c =? 48 then df_rz_loop n (1, l - 1, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f))%Z.
  Proof. clear_img. intros. cbn [df_rz_loop df_rz_body]. destruct (sh_getc f). reflexivity. Qed.
  Lemma df_lz_loop_step : forall n g c f, df_lz_loop (S n) (g, c, f) =
    (if c =? 48 then df_lz_loop n (1, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f))%Z.
  Proof. clear_img. intros. cbn [df_lz_loop df_lz_body]. destruct (sh_getc f). reflexivity. Qed.

  (* [comment removed for export] *)
  Definition SRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (lrp g : Z) (g' lrp' c' : Z) (f' : shfile),
    let _ := ctx_all in
    winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
    RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (1 - sh_rpos f <= lrp <= 0)%Z ->
    df_rz_loop n (g, lrp, 48, f)%Z = Some (g', lrp', c', f') ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1468)) fct None m (seg_rom img_segs)).
  Definition S_RZ : Prop := forall n, SRZn n.

  (* [comment removed for export] *)
  Definition S_9EC : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (gotdig : Z) (g' lrp' c' : Z) (f' : shfile),
    let _ := ctx_all in
    winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= gotdig <= 1)%Z ->
    df_rz_loop fuelc (gotdig, 0, c, f)%Z = Some (g', lrp', c', f') ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) (Z_to_bv 64 gotdig) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1416)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_A64 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
    let _ := ctx_all in
    winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 1 0 X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1536)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_7F4 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
    let _ := ctx_all in
    winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
    dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 0 0 X0) = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 912)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_9C8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
    let _ := ctx_all in
    winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
    dfK_rz fuelc 53 (-1074) sign pok 1 c f = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1380)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition SLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (g : Z) (g' c' : Z) (f' : shfile),
    let _ := ctx_all in
    winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    df_lz_loop n (g, 48, f)%Z = Some (g', c', f') ->
    dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1352)) fct None m (seg_rom img_segs)).
  Definition S_LZ : Prop := forall n, SLZn n.

  (* [comment removed for export] *)
  Definition S_990 : Prop := forall (n : nat) m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (g' c' : Z) (f' : shfile),
    let _ := ctx_all in
    winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
    df_lz_loop n (1, c, f)%Z = Some (g', c', f') ->
    dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 1324)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_848 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
    let _ := ctx_all in
    winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    decfloat fuelc (sh_unget f) 48 53 (-1074) sign pok = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 996)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition S_6F8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
    let _ := ctx_all in
    winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
    decfloat fuelc f c 53 (-1074) sign pok = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 660)) fct None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition FS_tail (sign c : Z) (f : shfile) : option (shfile * Z) :=
    if (c =? 48)%Z then
      let '(c2, f2) := sh_getc f in
      if (Z.lor c2 32 =? 120)%Z then None else decfloat fuelc (sh_unget f2) 48 53 (-1074) sign pok
    else decfloat fuelc f c 53 (-1074) sign pok.

  (* [comment removed for export] *)
  Definition S_618 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
    let _ := ctx_all in
    winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
    RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
    (c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
    FS_tail sign c f = Some (fR, yR) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 (sym 0x1e0cc + 436)) fct None m (seg_rom img_segs)).
End Floatscan.

End Img.
(* [comment removed for export] *)
Ltac2 rec zt_plain_arith' (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
          else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
          else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
          else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
          else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
          else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
  | _ => false
  end.
Ltac2 rec zt_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => zt_codomain b
  | Constr.Unsafe.LetIn _ _ b => zt_codomain b
  | Constr.Unsafe.Cast c _ _ => zt_codomain c
  | _ => t
  end.
Ltac2 rec zt_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => zt_head f
  | Constr.Unsafe.Cast c _ _ => zt_head c
  | _ => t
  end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
  lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
  | _ => false
  end.
Ltac2 zt_is_local' (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith' ty then None
                          else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.
