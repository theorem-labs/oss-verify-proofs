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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_monadx BM_syscalls BM_memset BM_memcpy BM_memchr BM_strnlen BM_stdio_lib BX_file BM_fwrite BI_shadow BI_globals2 BI_region_is_poisoned BI_memset_icp BI_strnlen_icp BP_policy BP_mjx BP_fwritex BP_fwritex_gen BP_pop_arg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BP_printf_iface BP_mlibA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require BP_printf_core_exit BP_printf_core_end BP_printf_core_exit1 BP_printf_core_scan BP_printf_core_flags BP_printf_core_width BP_printf_core_prec BP_printf_core_state BP_printf_core_dir BP_printf_core_t6 BP_printf_core_t5 BP_printf_core_t4 BP_printf_core_t3 BP_printf_core_t2 BP_printf_core_t1 BP_printf_core_tail BP_printf_core_intc2 BP_printf_core_intc BP_printf_core_dloop BP_printf_core_fmtu2 BP_printf_core_fmtu BP_printf_core_cvd BP_printf_core_cvu BP_printf_core_xloop BP_printf_core_cvx BP_printf_core_cvs BP_printf_core_cvfp BP_printf_core_conv BP_printf_core_head BP_printf_core_p1 BP_printf_core_pro.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Export BP_printf_core_common.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variable P : acc -> Prop.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis PSTK : POL_STACK P.
  Hypothesis PIMG : POL_IMG P.
  Hypothesis PHSH : POL_HSH P.
  Hypothesis PLSH : POL_LSH P.
  Hypothesis PNUL : POL_NUL P.
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis SMJ : sink_mjx_stmt SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis THI : topok_hi_stmt TOPOK.
  Hypothesis HOUT : out_stmt P Fp B BS SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 0x800000000000)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 0x21000)%Z.          (* [comment removed for export] *)
  Hypothesis SEP_F : ((0xa99f8 <= Fp /\ Fp + 232 <= 0xaa000) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((0x601598 <= B /\ B + BS <= 0x603000) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.   (* [comment removed for export] *)
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (65536 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= A_STK_HI)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Let QSTK : (q <= 0x800000000000)%Z := THI q TQ.
  Let VAHI' : (VA + 8 * zlength slots <= 0x800000000000)%Z := VAHI.

  (* [comment removed for export] *)
  Local Notation ctx_all := (BP_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (BP_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (BP_printf_core_common.Fok F).
  Local Notation Fok_refl := (BP_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (BP_printf_core_common.Fok_trans F).
  Local Notation POST := (BP_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (BP_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (BP_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (BP_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (BP_printf_core_common.fmt_rng fmt HF).
  Local Notation implMA_eq_ms := (BP_printf_core_common.implMA_eq_ms (St:=St) P).
  Local Notation sink_store := (BP_printf_core_common.sink_store (St:=St) Fp B BS SINK TOPOK SFR THI q lo AP VA GLO TQ SEP_F SEP_B HAP).
  Local Notation sink_call := (BP_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation mjx_ok_stack := (BP_printf_core_common.mjx_ok_stack lo fmt VA slots GLO VAHI).
  Local Notation mjx_ok_F := (BP_printf_core_common.mjx_ok_F Fp TOPOK THI q lo fmt AP VA slots LO GLO TQ SEP_F HAP VAHI).
  Local Notation mjx_ok_B := (BP_printf_core_common.mjx_ok_B B BS TOPOK THI q lo fmt AP VA slots LO GLO TQ SEP_B HAP VAHI).
  Local Notation pol_F := (BP_printf_core_common.pol_F P Fp TOPOK PSTK PIMG THI q lo fmt AP VA slots LO GLO TQ SEP_F HAP VAHI).
  Local Notation arg_ok_W := (BP_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (BP_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (BP_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (BP_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (BP_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (BP_printf_core_common.pop_arg_callq P TOPOK PSTK PIMG THI q gp tp lo fmt AP VA slots LO GLO QHI TQ HAP HVA VAHI).
  Local Notation strnlen_callq := (BP_printf_core_common.strnlen_callq (St:=St) P Fp B BS SINK TOPOK PSTK PIMG PHSH PLSH SFR SMJ THI q gp tp lo fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP HVA VAHI BS0).
  Local Notation memset_postZ := (BP_printf_core_common.memset_postZ q gp tp lo).
  Local Notation memset_callZ := (BP_printf_core_common.memset_callZ (St:=St) P SINK TOPOK PSTK PIMG PHSH SMJ THI q gp tp lo LO GLO QHI TQ).
  Local Notation out_postq := (BP_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (BP_printf_core_common.out_callq (St:=St) P Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (BP_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (BP_printf_core_common.fp_callq (St:=St) P Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (BP_printf_core_common.S_EXIT (St:=St) P Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (BP_printf_core_common.S_SCAN P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (BP_printf_core_common.S_FLAGS P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (BP_printf_core_common.S_WLOOP P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (BP_printf_core_common.S_WIDTH P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (BP_printf_core_common.S_PLOOP P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (BP_printf_core_common.S_PREC P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (BP_printf_core_common.S_STATE P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (BP_printf_core_common.S_DIR P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (BP_printf_core_common.S_END (St:=St) P Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation FPK := (BP_printf_core_common.FPK (St:=St) P Fp B BS SINK TOPOK OUTFP).
  Local Notation S_HEAD := (BP_printf_core_common.S_HEAD (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (BP_printf_core_common.S_CONV (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (BP_printf_core_common.body_loc Fp B BS q lo).
  Local Notation body_loc_src := (BP_printf_core_common.body_loc_src Fp B BS TOPOK THI q lo LO GLO TQ).
  Local Notation S_TAIL := (BP_printf_core_common.S_TAIL (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (BP_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (BP_printf_core_common.tinv (St:=St) P Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (BP_printf_core_common.S_T6 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (BP_printf_core_common.S_T5 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (BP_printf_core_common.S_T4 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (BP_printf_core_common.S_T3 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (BP_printf_core_common.S_T2 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (BP_printf_core_common.S_T1 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (BP_printf_core_common.S_INTC2 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (BP_printf_core_common.S_INTC (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (BP_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (BP_printf_core_common.S_DLOOP P ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (BP_printf_core_common.S_FMTU2 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (BP_printf_core_common.S_FMTU (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (BP_printf_core_common.S_CV_D (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (BP_printf_core_common.S_CV_U (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (BP_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (BP_printf_core_common.S_XLOOP P ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (BP_printf_core_common.S_CV_X (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (BP_printf_core_common.S_CV_S (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (BP_printf_core_common.S_CV_FP (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (BP_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (BP_printf_core_common.S_EXIT1 P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (BP_printf_core_common.S_P1 P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (BP_printf_core_common.S_PRO P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  (* [comment removed for export] *)
  Let PFILE : forall (a : Z) (k : nat), (Fp <= a)%Z -> (a + Z.of_nat k <= Fp + 232)%Z -> P (Z_to_bv 64 a, k) := pol_F.

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
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
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
  Ltac at_pc p := lazymatch goal with |- evtA _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtA _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl end | progress f_equal | zl ].   (* [comment removed for export] *)
  Tactic Notation "jump" tactic3(tac) := eapply evtA_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end);
    eapply implMA_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia | tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ first [ apply mjx_ok_F | apply mjx_ok_B | apply mjx_ok_stack; [ tslia | unfold zlength; tslia ] ] | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  (* [comment removed for export] *)
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  Ltac out_call :=
    ileave; eapply implMA_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 680488 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6296976 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | first [ solve [ unfold src_loc, in_stackw, A_CEIL, A_STK_HI in *; unfold zlength, zrepeat in *;
                        rewrite ?repeat_length, ?Z2Nat.id by lia; lia ] | idtac ] ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [bsegs bsegs] in *; fold bsegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl end | progress f_equal | zl ].   (* [comment removed for export] *)
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
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
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.


  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
  Proof using LO PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply BP_printf_core_exit.L_EXIT; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_END : S_END.
  Proof using GLO HAP LO SEP_F VAHI PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF QHI TQ FRM0 HA SEP_B HVA A0 BS0.
    first [ apply BP_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply BP_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply BP_printf_core_exit1.L_EXIT1; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using A0 HA HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 SEP_F SEP_B HAP HVA VAHI BS0.
    first [ apply BP_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply BP_printf_core_scan.L_SCAN; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply BP_printf_core_flags.L_FLAGS; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply BP_printf_core_width.L_WLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ intro; apply BP_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply BP_printf_core_width.L_WIDTH; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply BP_printf_core_prec.L_PLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ intro; apply BP_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply BP_printf_core_prec.L_PREC; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply BP_printf_core_state.L_STATE; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply BP_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0 VAHI.
    first [ apply BP_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply BP_printf_core_t6.L_T6; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply BP_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply BP_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply BP_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply BP_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply BP_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply BP_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply BP_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply BP_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply BP_printf_core_dloop.L_DLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply BP_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply BP_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply BP_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply BP_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    first [ apply BP_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply BP_printf_core_xloop.L_XLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply BP_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI HF FRM0 A0.
    first [ apply BP_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply BP_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_FP : S_CV_FP.
  Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ THI HOUT HF FRM0 A0 VAHI BS0.
    first [ apply BP_printf_core_cvfp.L_CV_FP; first [eassumption]
          | intros; eapply BP_printf_core_cvfp.L_CV_FP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI FRM0 A0.
    first [ apply BP_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP]
          | intros; eapply BP_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SMJ THI FRM0.
    first [ intro; apply BP_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply BP_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using A0 HA HF LO PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT GLO QHI TQ FRM0 SEP_F SEP_B HAP HVA VAHI BS0.
    first [ apply BP_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply BP_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using BS0 GLO HA HAP HVA LO QHI SEP_F PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF TQ FRM0 SEP_B A0 VAHI.
    first [ apply BP_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply BP_printf_core_pro.L_PRO; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk bsegs m0 lo q -> mem_inv bsegs m0 -> bytes_at bsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells bsegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      FPK (length fmt) fmt args ->
      (0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
      implMA bsegs P (printf_model OUT OUTFP fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x98da8) fc0 None m0 (seg_rom bsegs)).
  Proof using FRM0 HS_HEAD HS_PRO PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF LO GLO QHI TQ HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); [ apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] | apply Forall_cons; [apply mjx_ok_stack; unfold zlength in *; lia | apply Forall_nil] ]. }
    assert (APC : rw_cells bsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk bsegs m0 lo q -> mem_inv bsegs m0 -> bytes_at bsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evtA bsegs P (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x98da8) fc0 None m0 (seg_rom bsegs)).
  Proof using HS_P1 HS_PRO PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    stmt HS_P1 as NX1.
    jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
  Qed.

End PrintfCore.


(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (P : acc -> Prop) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
  POL_STACK P -> POL_IMG P -> POL_HSH P -> POL_LSH P -> POL_NUL P ->
  sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> sink_mjx_stmt SINK -> topok_stmt TOPOK -> topok_hi_stmt TOPOK ->
  out_stmt P Fp B BS SINK TOPOK OUT ->
  printf_core_stmt P Fp B BS SINK TOPOK OUT OUTFP.
Proof.
  intros St P Fp B BS SINK TOPOK OUT OUTFP PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK FPC SPC ST LO GLO SPHI TQ SSP MI FRM HA0 HA BS0 SEPF SEPB HAP HVA VAHI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2. unfold STATIC_SPLIT in HA.
  pose proof (THI _ TQ) as SPTOP. unfold A_STK_HI in SPTOP.
  pose proof (L_CORE2 P Fp B BS SINK TOPOK OUT OUTFP PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM HA SEPF SEPB HAP HVA HA0 VAHI BS0
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK (conj FPC SPC)) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implMA_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, A_STK_HI, zlength in *; destruct SEPF; lia. }
  cbv beta. intros r st' ms' PO. unfold POST, W in PO. unfold printf_core_post, SR.
  destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : forall P : acc -> Prop,
  POL_STACK P -> POL_IMG P -> POL_HSH P -> POL_LSH P -> POL_NUL P -> printf_core1_stmt P.
Proof.
  intros P PSTK PIMG PHSH PLSH PNUL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SPTOP SSP MI FRM HA0 HA HAP A2HI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, A_STK_HI in LO, GLO, HA, SPTOP, A2HI.
  (* [comment removed for export] *)
  pose proof (L_CORE1 (St:=unit) P 0xa99f8 0x601598 0 (fun _ _ => False) TOPOK_stk (fun _ => munr) PSTK PIMG PHSH PLSH PNUL
                      ltac:(unfold sink_frame_stmt; intros; match goal with H : _ |- _ => exact (False_rect _ H) end)
                      ltac:(unfold sink_flags_stmt; intros; match goal with H : _ |- _ => exact (False_rect _ H) end)
                      ltac:(unfold sink_mjx_stmt; intros; match goal with H : _ |- _ => exact (False_rect _ H) end)
                      topok_stk
                      ltac:(unfold topok_hi_stmt, TOPOK_stk; intros; assumption)
                      ltac:(unfold out_stmt; intros; match goal with H : _ |- _ => exact (False_rect _ H) end)
                      ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI ltac:(unfold TOPOK_stk, A_STK_HI; lia) FRM HA
                      ltac:(left; lia) ltac:(left; lia) HAP ltac:(lia) HA0 ltac:(unfold A_STK_HI, zlength; cbn [length Z.of_nat]; lia) ltac:(lia)
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evtA_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' PO. unfold POST1 in PO. unfold printf_core1_post.
  destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.
End RC__1.
