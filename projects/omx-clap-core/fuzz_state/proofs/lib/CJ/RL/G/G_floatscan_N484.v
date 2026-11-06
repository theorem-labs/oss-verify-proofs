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
  Context {CODE_floatscan_N484 : CodeAtT img_segs (sym 0x1e0cc) (floatscan_prog_at IMG)}.
  Context {RB_floatscan_N484 : RelCode (sym 0x1e0cc) 5768}.
  Context {CODE_floatscan_N484_1 : CodeAtT img_segs (sym 0x15f44) (floatscan_prog_r1_at IMG)}.
  Context {RB_floatscan_N484_1 : RelCode (sym 0x15f44) 12}.
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
  Collection ImgHyps := IMG CODE_floatscan_N484 RB_floatscan_N484 CODE_floatscan_N484_1 RB_floatscan_N484_1 RO_10428 RO_103f0 RO_10400 RO_103e0 RO_107c4 RN_B_shgetc_1e0cc RN_B_1f754_1e0cc RN_B_floatsitf_1e0cc RN_B_scanexp_1e0cc RN_B_15f44_1e0cc RN_B_shlim_1e0cc RN_B_floatunsitf_1e0cc RN_B_multf3_1e0cc RN_B_extenddftf2_1e0cc RN_B_200dc_1e0cc RN_B_divtf3_1e0cc RN_B_addtf3_1e0cc RN_B_scalbn_1e0cc RN_B_copysignl_1e0cc RN_B_fmodl_1e0cc RN_B_subtf3_1e0cc RN_B_letf2_1e0cc RN_B_fabsl_1e0cc RN_B_getf2_1e0cc RN_B_scalbnl_1e0cc RN_B_stack_chk_fail_1e0cc RS_got_ssp RS_K_107c4 RS_K_10428 RS_K_103f0 RS_K_10400 RS_K_103e0 RS_34288 rp_34288 RS_341f8 rp_341f8 SPEC_getf2 SPEC_scalbn SPEC_extenddftf2 SPEC_multf3_callq SPEC_divtf3_callq SPEC_divtf3_spec SPEC_addtf3_callq SPEC_subtf3_callq SPEC_letf2_callv SPEC_fabsl_spec SPEC_copysignl_spec SPEC_scalbnl_spec SPEC_rfmodl_spec SPEC_floatsitf_callv SPEC_floatsitf_callp SPEC_floatunsitf_callv SPEC_extenddftf2_callv SPEC_scanexp_rspec SPEC_shlim_spec RL0_0 rl0_0 RL0_1 rl0_1.


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


  (* [comment removed for export] *)
  Lemma L_N484 : S_N484.
  Proof.
    intros fo IH [kk carry a1 i rp1 xx] m'; intros until s'. intros _ DI2 RJ Hk FOK FRM' Hsg XR2 X312 Ra1 Rc1 Hkk Hsh Rz Rzf Rw Hfo Rrp Rrp1 Re2 HZ0 HS1 HA6 HL2 HK.
    assert (RZ0 : (0 <= Z0 < 2048)%Z) by (rewrite HZ0; apply Z.mod_pos_bound; lia). assert (RS1 : (0 <= S1 < 8192)%Z) by (rewrite HS1; lia).
    assert (RA6 : (XA <= A6 < XA + 8192)%Z) by (rewrite HA6; pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(lia)); lia).   (* [comment removed for export] *)
    cbn [dk_x dk_a dk_carry dk_rp dk_k] in *. subst kk.
    (* [comment removed for export] *)
    assert (Hshb : (1 <= sh <= 9)%Z) by (clear -Hsh; lia).
    pose proof DI2 as DI'. dest_dfinv DI'. (nelim XR2 3%nat; intros LW2 LX2 REL2).
      pose proof (Z.mod_pos_bound (z - a1) 2048 ltac:(flia)) as Rrs1.
      zs. brf K1.
      - (* [comment removed for export] *)
        unfold nz in HL2. replace (negb (carry =? 0))%Z with false in HL2 by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
        eapply IH with (h := h) (x := xx) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try (lazymatch goal with |- context [Z.shiftl _ _] => fail | _ => first [ hlia Rzf | flia ] end); try mk_dfinv.
        1: exact (conj LW2 (conj LX2 REL2)).
        all: try hlia Rzf.
      - (* [comment removed for export] *)
        unfold nz in HL2. replace (negb (carry =? 0))%Z with true in HL2 by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).
        zs. brf K2.
        + (* [comment removed for export] *)
          replace ((z + 1) mod 2048 =? a1)%Z with false in HL2 by (symmetry; apply Z.eqb_neq; first [ rewrite <- HZ0; exact K2 | flia ]). cbn [negb] in HL2.
          assert (Hrs : ((z - a1) mod 2048 < 2047)%Z).
          { clear -K2 Ra1 Rz HZ0. subst Z0. Z.div_mod_to_equations. flia. }
          zs. zs. zs. fix_idx.
          pose proof (u32arr_store_ok img_segs _ _ _ z _ XW ltac:(flia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write img_segs _ _ _ z (Z_to_bv 64 carry) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
          zs.
          assert (X31' : X31 (zupd xx z carry)).
          { intros ii. destruct (Z.eq_dec ii z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }
          (* [comment removed for export] *)
          stash_mods. stash_disj. do 20 zs. unstash. rewrite ?land2047. fix_idx.
          destruct (Z.eq_dec z 2047) as [Ez|Hz47].
          * (* [comment removed for export] *)
            subst Z0. subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL2 |- *.
            eapply IH with (h := false) (x := zupd xx 2047 carry) (z := 0%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try (lazymatch goal with |- context [Z.shiftl _ _] => fail | _ => first [ hlia Rzf | flia ] end); try mk_dfinv.
            1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
               intros ii Hq Hr.
               destruct (Z.eq_dec ii 2047) as [->|Hne].
               ++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
               ++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
                  destruct Hr as [Hr | [[Hr _] | Hr]]; [left | discriminate Hr | right; right; exact Hr].
                  unfold inring in Hr |- *. clear -Hr Hne Hq Ra1 K2. Z.div_mod_to_equations. flia. }
            all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
          * rewrite (Z.mod_small (z + 1) 2048) in HL2, HZ0 by flia. subst Z0.
            eapply IH with (h := h) (x := zupd xx z carry) (z := (z + 1)%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try (lazymatch goal with |- context [Z.shiftl _ _] => fail | _ => first [ hlia Rzf | flia ] end); try mk_dfinv.
            1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
               intros ii Hq Hr. destruct (Z.eq_dec ii z) as [->|Hne].
               ++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
               ++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
                  destruct Hr as [Hr | [[Hh Hzq] | Hr]]; [| right; left; split; [exact Hh | flia] | right; right; exact Hr].
                  apply (proj1 (inring_grow a1 z ii ltac:(flia) Hrs)) in Hr.
                  destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a1 z ii); flia. }
            all: try hlia Rzf.
            all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
            all: try (replace (z + 1 + -1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; replace (z + 1 - 1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; reflexivity).
        + (* [comment removed for export] *)
          replace ((z + 1) mod 2048 =? a1)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; first [ rewrite <- HZ0; exact K2 | flia ]). cbn [negb] in HL2.
          assert (Hrs : ((z - a1) mod 2048 = 2047)%Z).
          { clear -K2 Ra1 Rz HZ0. subst Z0. Z.div_mod_to_equations. flia. }
          pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
          assert (Kin : inring a1 z km).
          { unfold inring. subst km. rewrite Zminus_mod_idemp_l. clear -Hrs Ra1 Rz. Z.div_mod_to_equations. flia. }
          pose proof (X312 km) as Rt. pose proof (REL2 km ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
          pose proof (u32arr_read img_segs _ _ _ km _ _ XW (nth_error_wnth ws km ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(unfold wa; f_equal; flia)) as RD.
          zs. rewrite (sx32_wval ws km (znth xx km) (eq_sym Et) Rt). set (t := znth xx km) in *.
          zs.
          assert (Rt1 : (0 <= Z.lor t 1 < 2^31)%Z).
          { split; [apply Z.lor_nonneg; flia|]. apply (Bytes.lor_lt_pow2 t 1 31); flia. }
          pose proof (u32arr_store_ok img_segs _ _ _ km _ XW ltac:(flia) ltac:(unfold wa; f_equal; flia)) as SOK.
          zs.
          pose proof (u32arr_write img_segs _ _ _ km (Z_to_bv 64 (Z.lor t 1)) XW ltac:(flia)) as XW'. clear XW.
          replace (A6 + 0)%Z with (q + -8312 + 4 * km)%Z by flia.
          store_done'. rename XW' into XW.
          zs.
          eapply IH with (h := h) (x := zupd xx km (Z.lor t 1)) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try (lazymatch goal with |- context [Z.shiftl _ _] => fail | _ => first [ hlia Rzf | flia ] end); try mk_dfinv.
          1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
            intros ii Hq Hr. destruct (Z.eq_dec ii km) as [->|Hne].
            -- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
            -- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia | exact Hr]. }
          1:{ intros ii. destruct (Z.eq_dec ii km) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }
          all: try hlia Rzf.
  Qed.

End Floatscan.

End Img.
