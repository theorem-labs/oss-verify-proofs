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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BP_printf_core_common.
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


  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_CONV : S_CONV.
  Hypothesis HS_END : S_END.

  (* [comment removed for export] *)
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI PSTK PIMG PHSH PLSH PNUL SFR SMJ THI FRM0.
    induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
        FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
    { cbn [printf_loop]. apply implMA_unr. }
    rewrite printf_loop_S. unfold FPK in FPC. destruct FPC as [FPC SPC]. rewrite fp_calls_S in FPC. rewrite sp_ok_S in SPC.
    destruct (sfx i) as [|c s'] eqn:Es. { apply implMA_unr. }
    destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (fmt_rng i ltac:(zl)) as RGi.
    destruct (Z.eqb_spec c 0) as [C0|C0].
    { (* [comment removed for export] *)
      apply implMA_ret.
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
      stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
    rewrite <- Es in *. cbv zeta. cbv zeta in FPC. cbv zeta in SPC.
    pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
    rewrite Hs1. rewrite Hs1 in FPC. rewrite Hs1 in SPC.
    assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
    destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implMA_unr. }
    destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implMA_unr|] end.
    (* [comment removed for export] *)
    assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
    { pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
      destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
      rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
    stmt HS_SCAN as NXS.
    destruct (0 <? n) eqn:En; try rewrite En in FPC; try rewrite En in SPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implMA_unr|].
      ienter.
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. br K1.
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implMA_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI.
        - rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
        - rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
        - unfold n, zlength. reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. - right. unfold zlength in *. lia. }
      cbv beta. intros [] st'. post_call bsegs m. rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 626416)) with (Z_to_bv 64 626416) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. br K3.
      (* [comment removed for export] *)
      rewrite <- Es1. rewrite <- Es1 in FPC. rewrite <- Es1 in SPC.
      stmt IH as NXH.
      jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | split; [exact FPC | exact SPC]
        | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - (* [comment removed for export] *)
      assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
      assert (C37 : znth fmt i = 37%Z).
      { destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
      replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
      destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implMA_unr].
      destruct args as [|a args']; [apply implMA_unr|].
      ienter.
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. br K1.
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implMA_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI.
        - apply bytes_at_nil; zl.
        - constructor.
        - reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia. - right. change (zlength (@nil Z)) with 0%Z. unfold zlength in *. lia. }
      cbv beta. intros [] st'. post_call bsegs m. rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 626416)) with (Z_to_bv 64 626416) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. br K3.
      (* [comment removed for export] *)
      stmt HS_DIR as NXD.
      jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
      intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.
      (* [comment removed for export] *)
      stmt (HS_CONV fuel IH) as NXC.
      jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
        | | | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
      + destruct a; try exact I. exact (Forall_inv FPC).
      + exact (proj1 SPC).
      + split; [| exact (proj2 SPC)]. destruct a; try exact FPC. exact (Forall_inv_tail FPC).
      + exact (parse_dir_conv_type _ _ _ PD).
  Qed.
End PrintfCore.

End RC__1.
