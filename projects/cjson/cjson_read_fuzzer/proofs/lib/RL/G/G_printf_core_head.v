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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memset G_memcpy G_memchr G_strnlen G_fwritex G_pad G_fmt_fp_lib G_fmt_fp G_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Exit Printf_model Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_printf_core_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_printf_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import GRoTab. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
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
  Context {CODE_printf_core_head : CodeAtT img_segs (sym 0x18704) (printf_core_prog_at IMG)}.
  Context {RB_printf_core_head : RelCode (sym 0x18704) 3632}.
  Context {RO_10884 : RoB img_segs (sym 0x10884) ROT_0x10884}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_fwritex_18704 : GLRN 0x18704 0x17d50}.
  Context {RN_B_pop_arg_18704 : GLRN 0x18704 0x19534}.
  Context {RN_B_fmt_fp_18704 : GLRN 0x18704 0x1973c}.
  Context {RN_B_errno_location_18704 : GLRN 0x18704 0x15f44}.
  Context {RN_B_strerror_18704 : GLRN 0x18704 0x1ae04}.
  Context {RN_B_strnlen_18704 : GLRN 0x18704 0x21920}.
  Context {RN_B_wctomb_18704 : GLRN 0x18704 0x1ae48}.
  Context {RN_B_pad_18704 : GLRN 0x18704 0x19668}.
  Context {RN_B_memset_18704 : GLRN 0x18704 0x21738}.
  Context {RN_B_stack_chk_fail_18704 : GLRN 0x18704 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_K_109cc : GLRS 0x109cc}.
  Context {RS_K_10884 : GLRS 0x10884}.
  Context {RS_K_1029e : GLRS 0x1029e}.
  Context {RS_K_103b3 : GLRS 0x103b3}.
  Context {RS_K_10964 : GLRS 0x10964}.
  Context {RS_K_10b9c : GLRS 0x10b9c}.
  Context {RS_1029e : GLRS 0x1029e}.
  Let rp_1029e : (0 <= sym 0x1029e /\ sym 0x1029e < 2^30)%Z := @rel_sym_pf _ RS_1029e.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_35000 : GLRS 0x35000}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {SPEC_pop_arg : pop_arg_contract}.
  Context {SPEC_strnlen : strnlen_contract}.
  Context {SPEC_memset : memset_contract}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Context {RL1_0 : ZFact (sym 0x22e18 + 240 <= sym 0x34288)%Z}.
  Let rl1_0 : (sym 0x22e18 + 240 <= sym 0x34288)%Z := @zfact_pf _ RL1_0.
  Context {RO_states0 : RoB img_segs (sym 0x109cc) (zb STATES0)}.
  Context {RO_pfx : RoB img_segs (sym 0x1029e) (zb [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z)}.
  Context {RQ_pfx : ZFact (sym 0x1029e + 9 <= 0x20000)%Z}.
  Let rq_pfx : (sym 0x1029e + 9 <= 0x20000)%Z := @zfact_pf _ RQ_pfx.
  Context {RO_xdigits : RoB img_segs (sym 0x10b9c) (zb XDIGITS)}.
  Context {RQ_22e18 : ZFact (0x20000 <= sym 0x22e18)%Z}.
  Let rq_22e18 : (0x20000 <= sym 0x22e18)%Z := @zfact_pf _ RQ_22e18.
  Collection ImgHyps := IMG CODE_printf_core_head RB_printf_core_head RO_10884 RN_B_fwritex_18704 RN_B_pop_arg_18704 RN_B_fmt_fp_18704 RN_B_errno_location_18704 RN_B_strerror_18704 RN_B_strnlen_18704 RN_B_wctomb_18704 RN_B_pad_18704 RN_B_memset_18704 RN_B_stack_chk_fail_18704 RS_got_ssp RS_K_109cc RS_K_10884 RS_K_1029e RS_K_103b3 RS_K_10964 RS_K_10b9c RS_1029e rp_1029e RS_34288 rp_34288 RS_35000 rp_35000 SPEC_pop_arg SPEC_strnlen SPEC_memset RL0_0 rl0_0 RL0_1 rl0_1 RL1_0 rl1_0 RO_states0 RO_pfx RQ_pfx rq_pfx RO_xdigits RQ_22e18 rq_22e18.


Local Ltac step ::= astep2_fast. Local Ltac stepz ::= astep2_fast.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^63)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 131072)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : (((sym 0x34288 + 8) <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  (* [comment removed for export] *)
  Local Notation GLRUN1 f := (f ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt) (only parsing). Local Notation ctx_all := ((GLRUN1 G_printf_core_common.ctx_all)).
  Local Notation W := (G_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (G_printf_core_common.Fok F).
  Local Notation Fok_refl := (G_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (G_printf_core_common.Fok_trans F).
  Local Notation GLRUN2 f := (f s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) (only parsing). Local Notation POST := ((GLRUN2 (G_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp)) F m0 lo canary AP).
  Local Notation hi_cells := ((GLRUN2 (G_printf_core_common.hi_cells ra)) canary).
  Local Notation lo_cells := (G_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := ((GLRUN2 (G_printf_core_common.finv Fp B BS ra q)) m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (G_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (G_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (G_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (G_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (G_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (G_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (G_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (G_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (G_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (G_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (G_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (G_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (G_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (G_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (G_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := ((GLRUN1 (G_printf_core_common.S_EXIT (St:=St) Fp B BS SINK))).
  Local Notation S_SCAN := ((GLRUN1 (G_printf_core_common.S_SCAN Fp B BS))).
  Local Notation S_FLAGS := ((GLRUN1 (G_printf_core_common.S_FLAGS Fp B BS))).
  Local Notation S_WLOOP := ((GLRUN1 (G_printf_core_common.S_WLOOP Fp B BS))).
  Local Notation S_WIDTH := ((GLRUN1 (G_printf_core_common.S_WIDTH Fp B BS))).
  Local Notation S_PLOOP := ((GLRUN1 (G_printf_core_common.S_PLOOP Fp B BS))).
  Local Notation S_PREC := ((GLRUN1 (G_printf_core_common.S_PREC Fp B BS))).
  Local Notation S_STATE := ((GLRUN1 (G_printf_core_common.S_STATE Fp B BS))).
  Local Notation S_DIR := ((GLRUN1 (G_printf_core_common.S_DIR Fp B BS))).
  Local Notation S_END := ((GLRUN1 (G_printf_core_common.S_END (St:=St) Fp B BS SINK))).
  Local Notation S_HEAD := ((GLRUN1 (G_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_CONV := ((GLRUN1 (G_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation body_loc := (G_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := ((GLRUN1 (G_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation tregs := (G_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := ((GLRUN2 (G_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q)) m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := ((GLRUN1 (G_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_T5 := ((GLRUN1 (G_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_T4 := ((GLRUN1 (G_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_T3 := ((GLRUN1 (G_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_T2 := ((GLRUN1 (G_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_T1 := ((GLRUN1 (G_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_INTC2 := ((GLRUN1 (G_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_INTC := ((GLRUN1 (G_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation dloop_post := (G_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := ((GLRUN1 G_printf_core_common.S_DLOOP)).
  Local Notation S_FMTU2 := ((GLRUN1 (G_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_FMTU := ((GLRUN1 (G_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_D := ((GLRUN1 (G_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_U := ((GLRUN1 (G_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation xloop_post := (G_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := ((GLRUN1 G_printf_core_common.S_XLOOP)).
  Local Notation S_CV_X := ((GLRUN1 (G_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_S := ((GLRUN1 (G_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_FP := ((GLRUN1 (G_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP))).
  Local Notation POST1 := ((GLRUN2 (G_printf_core_common.POST1 ra q gp tp)) F fc0 m0 lo canary).
  Local Notation S_EXIT1 := ((GLRUN1 (G_printf_core_common.S_EXIT1 Fp B BS))).
  Local Notation S_P1 := ((GLRUN1 (G_printf_core_common.S_P1 Fp B BS))).
  Local Notation S_PRO := ((GLRUN1 (G_printf_core_common.S_PRO Fp B BS))).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    (nelim H 9%nat; intros MI MU WM FRhi ST BY VAA SSP1 SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl end | progress f_equal | zl ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RPre. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RPre.rl_zify_pre_hook.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
Local Ltac brff K := brf K.
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ (sym 0x22e18) _ |- _ => exact H end
        | match goal with H : rw_cells _ _ (sym 0x34288) _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call (@img_segs IMG) m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_sym; arel_side) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl end | progress f_equal | zl ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    (nelim H 25%nat; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      repeat (split; [first [assumption | reflexivity | (lazymatch goal with |- context [INT_MAX] => unfold INT_MAX in *; zl end) | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | (lazymatch goal with |- context [INT_MAX] => unfold INT_MAX in *; zl end) | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_CONV : S_CONV.
  Hypothesis HS_END : S_END.

  (* [comment removed for export] *)
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI ImgHyps.
    induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
        FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
    { cbn [printf_loop]. apply implM_unr. }
    rewrite printf_loop_S. rewrite fp_calls_S in FPC.
    destruct (sfx i) as [|c s'] eqn:Es. { apply implM_unr. }
    (nelim (sfx_cons_inv fmt i c s' Hi Es) 3%nat; intros Hilt Ec Es').
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (fmt_rng i ltac:(zl)) as RGi.
    destruct (Z.eqb_spec c 0) as [C0|C0].
    { (* [comment removed for export] *)
      apply implM_ret.
      zs. zs. zs. br10 K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
      stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
    rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
    (nelimp (lit_run_sfx fmt i Hi) 4%nat; intros Hn Hs1 LIT Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
    rewrite Hs1. rewrite Hs1 in FPC.
    assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
    destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implM_unr. }
    (nelim (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) 3%nat; intros Hin Ec1 Es2). unfold zlength in Hin.
    match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implM_unr|] end.
    (* [comment removed for export] *)
    assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
    { pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
      destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
      rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
      (nelim (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) 3%nat; intros Hin1 Ec2 Es2q).
      split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
    stmt HS_SCAN as NXS.
    destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implM_unr|].
      ienter.
      zs. zs. zs. br10 K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br10 K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. br10 K1.
      (nelim (SFL _ _ HS) 3%nat; intros fb FLC FB). zs. zs. zs. br10 K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI.
        - rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
        - rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
        - unfold n, zlength. reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. }
      cbv beta. intros [] st'. post_call (@img_segs IMG) m. rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 (sym 0x18704 + 328))) with (Z_to_bv 64 (sym 0x18704 + 328)) by (symmetry; apply ret_pc_sym; arel_side).
      zs. zs. br10 K3.
      (* [comment removed for export] *)
      rewrite <- Es1. rewrite <- Es1 in FPC.
      stmt IH as NXH.
      jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
        | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - (* [comment removed for export] *)
      assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
      assert (C37 : znth fmt i = 37%Z).
      { destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
      replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
      destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implM_unr].
      destruct args as [|a args']; [apply implM_unr|].
      ienter.
      zs. zs. zs. br10 K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br10 K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. br10 K1.
      (nelim (SFL _ _ HS) 3%nat; intros fb FLC FB). zs. zs. zs. br10 K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI.
        - apply bytes_at_nil; zl.
        - constructor.
        - reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia. }
      cbv beta. intros [] st'. post_call (@img_segs IMG) m. rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 (sym 0x18704 + 328))) with (Z_to_bv 64 (sym 0x18704 + 328)) by (symmetry; apply ret_pc_sym; arel_side).
      zs. zs. br01 K3.
      (* [comment removed for export] *)
      stmt HS_DIR as NXD.
      jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
      intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.
      (* [comment removed for export] *)
      stmt (HS_CONV fuel IH) as NXC.
      jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
        | | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
      + destruct a; try exact I. exact (Forall_inv FPC).
      + destruct a; try exact FPC. exact (Forall_inv_tail FPC).
      + exact (parse_dir_conv_type _ _ _ PD).
  Qed.
End PrintfCore.

End Img.
