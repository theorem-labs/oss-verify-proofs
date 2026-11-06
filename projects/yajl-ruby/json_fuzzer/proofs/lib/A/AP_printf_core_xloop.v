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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_monadx AM_syscalls AM_memset AM_memcpy AM_memchr AM_strnlen AM_stdio_lib AX_file AM_fwrite
  AI_shadow AI_globals2 AI_region_is_poisoned AI_memset_icp AI_strnlen_icp AP_policy AP_mjx AP_fwritex AP_fwritex_gen AP_pop_arg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_printf_iface AP_mlibA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_printf_core_common.
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
  Hypothesis SEP_F : ((0xa8e18 <= Fp /\ Fp + 232 <= 0xa9420) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((0x600b58 <= B /\ B + BS <= 0x603000) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.   (* [comment removed for export] *)
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (65536 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= A_STK_HI)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Let QSTK : (q <= 0x800000000000)%Z := THI q TQ.
  Let VAHI' : (VA + 8 * zlength slots <= 0x800000000000)%Z := VAHI.

  (* [comment removed for export] *)
  Local Notation ctx_all := (AP_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (AP_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (AP_printf_core_common.Fok F).
  Local Notation Fok_refl := (AP_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (AP_printf_core_common.Fok_trans F).
  Local Notation POST := (AP_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (AP_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (AP_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (AP_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (AP_printf_core_common.fmt_rng fmt HF).
  Local Notation implMA_eq_ms := (AP_printf_core_common.implMA_eq_ms (St:=St) P).
  Local Notation sink_store := (AP_printf_core_common.sink_store (St:=St) Fp B BS SINK TOPOK SFR THI q lo AP VA GLO TQ SEP_F SEP_B HAP).
  Local Notation sink_call := (AP_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation mjx_ok_stack := (AP_printf_core_common.mjx_ok_stack lo fmt VA slots GLO VAHI).
  Local Notation mjx_ok_F := (AP_printf_core_common.mjx_ok_F Fp TOPOK THI q lo fmt AP VA slots LO GLO TQ SEP_F HAP VAHI).
  Local Notation mjx_ok_B := (AP_printf_core_common.mjx_ok_B B BS TOPOK THI q lo fmt AP VA slots LO GLO TQ SEP_B HAP VAHI).
  Local Notation pol_F := (AP_printf_core_common.pol_F P Fp TOPOK PSTK PIMG THI q lo fmt AP VA slots LO GLO TQ SEP_F HAP VAHI).
  Local Notation arg_ok_W := (AP_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (AP_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (AP_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (AP_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (AP_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (AP_printf_core_common.pop_arg_callq P TOPOK PSTK PIMG THI q gp tp lo fmt AP VA slots LO GLO QHI TQ HAP HVA VAHI).
  Local Notation strnlen_callq := (AP_printf_core_common.strnlen_callq (St:=St) P Fp B BS SINK TOPOK PSTK PIMG PHSH PLSH SFR SMJ THI q gp tp lo fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP HVA VAHI BS0).
  Local Notation memset_postZ := (AP_printf_core_common.memset_postZ q gp tp lo).
  Local Notation memset_callZ := (AP_printf_core_common.memset_callZ (St:=St) P SINK TOPOK PSTK PIMG PHSH SMJ THI q gp tp lo LO GLO QHI TQ).
  Local Notation out_postq := (AP_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (AP_printf_core_common.out_callq (St:=St) P Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (AP_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (AP_printf_core_common.fp_callq (St:=St) P Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (AP_printf_core_common.S_EXIT (St:=St) P Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (AP_printf_core_common.S_SCAN P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (AP_printf_core_common.S_FLAGS P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (AP_printf_core_common.S_WLOOP P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (AP_printf_core_common.S_WIDTH P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (AP_printf_core_common.S_PLOOP P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (AP_printf_core_common.S_PREC P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (AP_printf_core_common.S_STATE P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (AP_printf_core_common.S_DIR P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (AP_printf_core_common.S_END (St:=St) P Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation FPK := (AP_printf_core_common.FPK (St:=St) P Fp B BS SINK TOPOK OUTFP).
  Local Notation S_HEAD := (AP_printf_core_common.S_HEAD (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (AP_printf_core_common.S_CONV (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (AP_printf_core_common.body_loc Fp B BS q lo).
  Local Notation body_loc_src := (AP_printf_core_common.body_loc_src Fp B BS TOPOK THI q lo LO GLO TQ).
  Local Notation S_TAIL := (AP_printf_core_common.S_TAIL (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (AP_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (AP_printf_core_common.tinv (St:=St) P Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (AP_printf_core_common.S_T6 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (AP_printf_core_common.S_T5 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (AP_printf_core_common.S_T4 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (AP_printf_core_common.S_T3 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (AP_printf_core_common.S_T2 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (AP_printf_core_common.S_T1 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (AP_printf_core_common.S_INTC2 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (AP_printf_core_common.S_INTC (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (AP_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (AP_printf_core_common.S_DLOOP P ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (AP_printf_core_common.S_FMTU2 (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (AP_printf_core_common.S_FMTU (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (AP_printf_core_common.S_CV_D (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (AP_printf_core_common.S_CV_U (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (AP_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (AP_printf_core_common.S_XLOOP P ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (AP_printf_core_common.S_CV_X (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (AP_printf_core_common.S_CV_S (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (AP_printf_core_common.S_CV_FP (St:=St) P Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (AP_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (AP_printf_core_common.S_EXIT1 P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (AP_printf_core_common.S_P1 P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (AP_printf_core_common.S_PRO P Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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
        [ match goal with H : rw_cells _ _ 677432 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6294352 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | first [ solve [ unfold src_loc, in_stackw, A_CEIL, A_STK_HI in *; unfold zlength, zrepeat in *;
                        rewrite ?repeat_length, ?Z2Nat.id by lia; lia ] | idtac ] ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call asegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [asegs asegs] in *; fold asegs in *.
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
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI PSTK PIMG PHSH PLSH PNUL SFR SFL SMJ TOK THI HOUT HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
    intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (hex_digits_step l x ltac:(lia)) as DS.
    pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
    pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
    assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
    assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
    pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
    zs. zs. zs. zs.
    replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
    pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
    zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
    zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
    set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    - (* [comment removed for export] *)
      eapply evtA_mono.
      { eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' PO. destruct PO as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
      unfold xloop_post. exists a2', a3', m'. cbv zeta.
      assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
      rewrite EL.
      split; [ mseq | ].
      split; [ eapply munch_trans; [exact MU | exact MU'] | ].
      split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
      split; [ exact MI' | ].
      split.
      { replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
          with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
        rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
        replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
        rewrite DS, zb_app, <- !app_assoc. reflexivity. }
      unfold zlength in *. lia.
    - (* [comment removed for export] *)
      apply evtA_done. unfold xloop_post. eexists _, _, _. cbv zeta.
      assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
      assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
      rewrite EL.
      split; [ mseq | ].
      split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
      split.
      { replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
        rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
      lia.
  Qed.
End PrintfCore.

End RC__1.
