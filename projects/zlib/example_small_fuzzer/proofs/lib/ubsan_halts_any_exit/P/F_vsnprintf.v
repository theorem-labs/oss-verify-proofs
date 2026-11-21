(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib F_printf_iface.

Module F_printf_core_exit.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_EXIT : S_EXIT.
  Proof using LO.
    intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
    dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 14 zstep.
    zstep. zstep.
    release_frame LOW ST (q + -392)%Z.
    release_frame DIG ST (q + -368)%Z.
    release_frame PAD ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evt_done. unfold POST.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
    split; [exact ST|]. split; [exact HS|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
  Qed.
End PrintfCore.
End F_printf_core_exit.

Module F_printf_core_end.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_EXIT : S_EXIT.

  Lemma L_END : S_END.
  Proof using GLO HAP HS_EXIT LO SEP_F VAHI.
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
           FI LOW DIG PAD HS APC FRM FOK Hr.
    pose proof FI as FI'. dest_finv FI.
    zs. br K.
    stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
  Qed.
End PrintfCore.
End F_printf_core_end.

Module F_printf_core_exit1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO.
    intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
    dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 14 zstep.
    zstep. zstep.
    release_frame LOW ST (q + -392)%Z.
    release_frame DIG ST (q + -368)%Z.
    release_frame PAD ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evt_done. unfold POST1.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST|]. unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
  Qed.
End PrintfCore.
End F_printf_core_exit1.

Module F_printf_core_scan.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
      finv m ->
      k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
      (0 <= i)%Z -> (i + n < zlength fmt)%Z ->
      (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
      (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
      (forall a0, evt psegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0x22dcc else 0x22dd4)) fc None m (seg_rom psegs))) ->
      evt psegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x22dbc) fc None m (seg_rom psegs)).
  Proof using HF.
    intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
    -
      assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
      dest_finv FI. unfold INT_MAX in *.
      zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
    - destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
      pose proof (LIT j ltac:(lia)) as [NZ N37].
      pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
      pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
      zs. br K.
      rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
      destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
      +
        pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
        br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z FI'); try lia; try assumption.
      + assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
        replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
        destruct TERM as [T0 | (T37 & Hn1 & T1)].
        * rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
        * br K1. eapply (IH n FI'); try lia; try assumption.
  Qed.

  Lemma L_SCAN : S_SCAN.
  Proof using A0 HA HF.
    intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
           FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    assert (NZ0 : znth fmt i <> 0%Z).
    { destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
    pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
    zs. zs. br K.
    eapply evt_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
    { cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
    { destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
    intros a0.
    assert (TL : forall a1 a2, evt psegs Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x22e00) fc None m (seg_rom psegs))).
    { intros a1 a2. zs. replace (A + i + n - (A + i))%Z with n by lia. zs. fixr. zs. br K1. zs. fixr. apply HK. }
    destruct TERM as [T0 | (T37 & Hn1 & T1)].
    - rewrite T0, Z.eqb_refl. zs. zs. apply TL.
    - rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
  Qed.
End PrintfCore.
End F_printf_core_scan.

Module F_printf_core_flags.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_FLAGS : S_FLAGS.
  Proof using HF.
    intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
           FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
    remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
    revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
    induction kk as [|kk IH]; intros.
    { rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
    assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
    pose proof FI as FI'. dest_finv FI.
    zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
    -
      assert (NF : flag_bit (znth fmt (p + k)) = None).
      { destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
        pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
        pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
      rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
      injection PF as EFL Es1.
      rewrite Z.lor_comm, EFL.
      jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
      { rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
      rewrite <- EFL. apply lor_bound17; lia.
    - assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
      rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
      zs. zs. zs. zs. brf K2.
      +
        change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
        destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
        2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
        pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
        rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
        replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
        rewrite Z.lor_comm.
        eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
        { rewrite unsigned_lit_land. exact Hfw. }
        { apply lor_bound17; lia. }
        { replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
        { intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
        all: unfold zlength in *; lia.
      +
        change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
        assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
        rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
        injection PF as EFL Es1.
        rewrite Z.lor_comm, EFL.
        jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
        { rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
        rewrite <- EFL. apply lor_bound17; lia.
  Qed.
End PrintfCore.
End F_printf_core_flags.

Module F_printf_core_width.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_WLOOP : S_WLOOP.
  Proof using HF.
    intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hpos Hacc DG G NE HK.
    remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
    revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
    induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
    pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    pose proof (proj1 (digit_range _) DG) as DGR.
    rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
    destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
    apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
    assert (Hnx : (pos + 1 < zlength fmt)%Z).
    { destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
      rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
    zs. zs. br K.
    zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
    zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
    rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
    zs. try rewrite (lxor_imax (acc * 10)) by lia.
    zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
    zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
    zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
    zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
    -
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. br K3.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    -
      assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
  Qed.

  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF.
    intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk1 G NE HK.
    pose proof FI as FI'. dest_finv FI.
    pose proof (fmt_rng k1 ltac:(zl)) as RG1.
    zs. zs. zs. zs. brf K.
    -
      assert (ND : is_digit (znth fmt k1) = false).
      { destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
      rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
      subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
      rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
    - assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
      zs. zs.
      stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
      intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
  Qed.
End PrintfCore.
End F_printf_core_width.

Module F_printf_core_prec.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_PLOOP : S_PLOOP.
  Proof using HF.
    intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hpos Hacc DG G NE HK.
    remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
    revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
    induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
    pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    pose proof (proj1 (digit_range _) DG) as DGR.
    rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
    destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
    apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
    assert (Hnx : (pos + 1 < zlength fmt)%Z).
    { destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
      rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
    zs. zs. br K.
    zs. try rewrite (swrap32_small (acc * 10)) by lia.
    zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
    zs. try rewrite (lxor_imax (acc * 10)) by lia.
    zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
    zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
    zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
    zs. try rewrite Z.lor_0_l.
    rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
    -
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. zs. zs. zs.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    - assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
  Qed.

  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF.
    intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk2 PX HK.
    pose proof FI as FI'. dest_finv FI.
    rd_fmt k2. zs. fix_u8 k2. zs. zs.
    destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
    - br K. subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
    - br K. rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. br K1.
      subst xp. zsto 0x23080%Z.
      pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
      zs. brf K3.
      +
        assert (ND : is_digit (znth fmt (k2 + 1)) = false).
        { destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
        rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
        injection G as Ep Es. subst p.
        assert (k3 = k2 + 1)%Z.
        { pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
          rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
        subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
      + assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
        zs. zs.
        stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
        { intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
        intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
        assert (k3' = k3)%Z.
        { pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
        subst k3'. apply HK. lia.
  Qed.
End PrintfCore.
End F_printf_core_prec.

Module F_printf_core_state.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Lemma L_STATE : S_STATE.
  Proof using HF.
    intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 ty ps n _ FI Hk3 CS HK.
    pose proof FI as FI'. dest_finv FI.
    destruct (conv_state_cases _ _ _ _ CS) as [(t & s' & Es & NE & CT & -> & ->) | (t2 & s' & Es & CZ & -> & ->)].
    -
      destruct (sfx_cons_inv fmt k3 t s' ltac:(lia) Es) as (_ & Et & Es'). subst t.
      pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
      zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
      { exfalso. rewrite land_M64_neg in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
      zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
      clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
      clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
      clear K4. zs. br K5.
      jump (apply HK).
    -
      destruct (sfx_cons_inv fmt k3 122 (t2 :: s') ltac:(lia) Es) as (Hk3' & Ez & Es').
      destruct (sfx_cons_inv fmt (k3 + 1) t2 s' ltac:(lia) (eq_sym Es')) as (Hk31 & Et2 & Es''). subst t2.
      destruct (conv_type_z_inv _ _ CZ) as [Eu Ety].
      zs. zs. rd_fmt k3. zs. fix_u8 k3. rewrite <- Ez. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs.
      pose proof (states0_read_z m 122 MI eq_refl) as RD2.
      pose proof RD2 as RD2'. replace (122 + 78148 + -65)%Z with 78205%Z in RD2' by reflexivity.
      zs. cbv beta. change (bv_unsigned (Z_to_bv 8 ZTPRE)) with 6%Z. clear RD2 RD2'.
      zs. zs. zs. if_lit.
      rd_fmt (k3 + 1)%Z. zs. fix_u8 (k3 + 1)%Z. rewrite Eu. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs.
      assert (CZ' : conv_type_z 117 = Some ty) by (rewrite <- Eu; exact CZ).
      pose proof (states6_read m 117 _ _ MI CZ' eq_refl) as RD3.
      pose proof RD3 as RD3'. replace (117 + 78496 + -65)%Z with 78548%Z in RD3' by reflexivity.
      zs. cbv beta. rewrite Ety. change (bv_unsigned (Z_to_bv 8 PrintfModel.T_SIZET)) with 20%Z. clear RD3 RD3'.
      zs. zs. zs. if_lit. zs. zs. if_lit. zs. if_lit. zs. if_lit.
      rewrite Ety in HK. unfold PrintfModel.T_SIZET, ZTPRE in HK.
      jump (apply HK).
  Qed.
End PrintfCore.
End F_printf_core_state.

Module F_printf_core_dir.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_FLAGS : S_FLAGS.
  Hypothesis HS_WIDTH : S_WIDTH.
  Hypothesis HS_PREC : S_PREC.
  Hypothesis HS_STATE : S_STATE.

  Lemma L_DIR : S_DIR.
  Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH.
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
           FI LOW Hi Hi1 PD HK.
    pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
    destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
    destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & ps & nn & PX).
    destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
    rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
    destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
    rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
    assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
    rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.
    assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
      evt psegs Q
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x22f10) fc None m (seg_rom psegs))).
    { intros t0 t1 a3 a4 a5 a6 a7.
      pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
      stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
      intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
      assert (k2' = k2).
      { pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
      subst k2'.
      stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (if d_xp d then k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - Z.of_nat nn else k2)%Z);
              [exact FI' | exact LOW' | lia | | ]).
      { destruct PX as [(N46 & Hp & Hxp & CS & Ht & Hrest) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & CS & Ht & Hrest)].
        - left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity.
        - right. rewrite Hxp. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
          destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
          rewrite Hs3 in CS, Hrest.
          assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
          destruct (conv_state_at fmt _ d _ _ Hk30 CS) as (Hk3 & Hnn1 & _ & Eskip & _).
          assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - Z.of_nat nn = k2 + 1 + Z.of_nat n3)%Z).
          { rewrite Es2b, Hrest, Eskip. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + Z.of_nat nn) ltac:(zl)). unfold zlength in *. lia. }
          rewrite EK. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
          split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
      intros a1q a3q a4q Hp.
      destruct PX as [(N46 & Hpq & Hxp & CS & Ht & Hrest) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & CS & Ht & Hrest)].
      - rewrite Hxp. cbn [Z.b2z]. rewrite Hs2 in CS, Ht, Hrest.
        assert (Hk20 : (0 <= k2)%Z) by (subst k1 k2; lia).
        destruct (conv_state_at fmt _ d _ _ Hk20 CS) as (Hk3n & Hnn1 & Enth & Eskip & Eps).
        stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k2) (ty := d_ty d) (ps := ps) (n := nn); [exact FI' | zl | exact CS | ]).
        intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK. rewrite Eps in HK.
        jump (apply (HK (k2 + Z.of_nat nn)%Z); [zl | rewrite Hrest, Eskip; reflexivity | rewrite Ht, Enth; f_equal; lia | lia | lia | lia]).
      - rewrite Hxp. cbn [Z.b2z]. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
        destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
        rewrite Hs3 in CS, Ht, Hrest.
        assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
        destruct (conv_state_at fmt _ d _ _ Hk30 CS) as (Hk3 & Hnn1 & Enth & Eskip & Eps).
        assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - Z.of_nat nn = k2 + 1 + Z.of_nat n3)%Z).
        { rewrite Es2b, Hrest, Eskip. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + Z.of_nat nn) ltac:(zl)). unfold zlength in *. lia. }
        rewrite EK.
        stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 1 + Z.of_nat n3)%Z) (ty := d_ty d) (ps := ps) (n := nn); [exact FI' | zl | exact CS | ]).
        intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK. rewrite Eps in HK.
        jump (apply (HK (k2 + 1 + Z.of_nat n3 + Z.of_nat nn)%Z); [zl | rewrite Hrest, Eskip; reflexivity | rewrite Ht, Enth; f_equal; lia | lia | lia | lia]). }
    assert (FL34 : forall (a3 a4 a5 : word), evt psegs Q
      (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
               x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x22e80) fc None m (seg_rom psegs))).
    { intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.
      assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
      { intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
        pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
        rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
      zs. zs. zs. brf K2.
      -
        assert (NF : flag_bit (znth fmt (i + 1)) = None).
        { destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
          pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
        destruct (NOFLAG NF) as [Efl0 Ek1].
        zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
        jump (apply POSTFLAGS).
      - assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
        rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
        zs. zs. zs. zs. zs. brf K3.
        +
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
          destruct (NOFLAG NF) as [Efl0 Ek1].
          zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
        +
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
          2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
          pose proof (flag_some _ _ Hc E) as [Hfw Hb].
          rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
          zs.
          stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
                 [exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
          intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
          assert (Ek1 : k' = k1).
          { pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
          subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
          zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
          jump (apply POSTFLAGS). }
    rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
    - zs. zs. apply FL34.
    - assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      assert (Hi2 : (i + 2 < zlength fmt)%Z).
      { destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
        rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
      replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
      rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
      rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
  Qed.
End PrintfCore.
End F_printf_core_dir.

Module F_printf_core_t6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_T6 : S_T6.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw.
    dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
    ienter. zs. zs. brf K1.
    -
      rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
      stmt HH as NXH.
      jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
        | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite K1, Z.eqb_refl. cbn [negb orb].
      zs. zs. brf K2.
      +
        rewrite (proj2 (Z.leb_le _ _)) by lia.
        stmt HH as NXH.
        jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
          [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
          | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
      + rewrite (proj2 (Z.leb_gt _ _)) by lia.
        destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
        set (n4 := (wq - (pl + pq))%Z) in *.
        zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
        zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
        zs. zs.
        apply (rw_cells_split_CB psegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
        cbn [mk_CB_cells app] in PAD.
        apply (proj1 (rw_cells_app psegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
        cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
        zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
        fix_rsegs. rename MI0 into MI.
        match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
        rewrite (Z.mod_small 32 256) in PADa by lia.
        zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
        destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
        zs. zs. zs. zs.
        pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
        out_call.
        1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
        1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
        1:{ lia. } 1:{ lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
        match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
        zs.
        match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
          assert (PAD : rw_cells psegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app psegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
          | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
            replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
        end.
        stmt HH as NXH.
        jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
          [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
          | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
End PrintfCore.
End F_printf_core_t6.

Module F_printf_core_t5.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_T6 : S_T6.

  Lemma L_T5 : S_T5.
  Proof using BS0 GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    ienter.
    destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
    zs. zs. zs. zs.
    out_call.
    1:{ exact BODY. }
    1:{ exact BRNG. }
    1:{ rewrite Hn. reflexivity. }
    1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
    match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
    stmt (HS_T6 fuel HH) as NX6.
    jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
      [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End F_printf_core_t5.

Module F_printf_core_t3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | clear_big; repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Local Ltac lia ::= clear_big; lia3.
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_T4 : S_T4.

  Lemma L_T3 : S_T3.
  Proof using BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 65536) by reflexivity.
    ienter. zs. zs. brf K1.
    -
      rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
      stmt (HS_T4 fuel HH) as NX4.
      jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite K1, Z.eqb_refl. cbn [negb orb].
      zs. zs. brf K2.
      + rewrite (proj2 (Z.leb_le _ _)) by lia.
        stmt (HS_T4 fuel HH) as NX4.
        jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
          [ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
      + rewrite (proj2 (Z.leb_gt _ _)) by lia.
        destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
        set (n4 := (wq - (pl + pq))%Z) in *.
        zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
        zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
        zs. zs.
        apply (rw_cells_split_CB psegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
        cbn [mk_CB_cells app] in PAD.
        apply (proj1 (rw_cells_app psegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
        cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
        zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
        fix_rsegs. rename MI0 into MI.
        match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
        rewrite (Z.mod_small 48 256) in PADa by lia.
        zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
        destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
        zs. zs. zs. zs.
        pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
        out_call.
        1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
        1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
        1:{ lia. } 1:{ lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
        match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
          assert (PAD : rw_cells psegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app psegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
          | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
            replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
        end.
        stmt (HS_T4 fuel HH) as NX4.
        jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
          [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End F_printf_core_t3.

Module F_printf_core_t2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_T3 : S_T3.

  Lemma L_T2 : S_T2.
  Proof using BS0 GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    ienter.
    destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
    zs. zs. zs. zs.
    out_call.
    1:{ apply HPFX. exact MI. }
    1:{ exact PRNG. }
    1:{ rewrite Hpl. reflexivity. }
    1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
    match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
    stmt (HS_T3 fuel HH) as NX3.
    jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
      [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End F_printf_core_t2.

Module F_printf_core_t1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | clear_big; repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Local Ltac lia ::= clear_big; lia3.
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_T2 : S_T2.

  Lemma L_T1 : S_T1.
  Proof using BS0 GLO HA HAP HOUT HS_T2 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw Hfl0.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
    replace (Z.land fl 73728 =? 0)%Z with true by (rewrite Hfl0; reflexivity). cbn [negb orb].
    ienter. zs. zs. brf K2.
    -
      rewrite (proj2 (Z.leb_le _ _)) by lia.
      stmt (HS_T2 fuel HH) as NX2.
      jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
      set (n4 := (wq - (pl + pq))%Z) in *.
      zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
      zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
      zs. zs.
      apply (rw_cells_split_CB psegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
      cbn [mk_CB_cells app] in PAD.
      apply (proj1 (rw_cells_app psegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
      cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
      zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
      fix_rsegs. rename MI0 into MI.
      match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
      rewrite (Z.mod_small 32 256) in PADa by lia.
      zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
      zs. zs. zs. zs.
      pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      out_call.
      1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
      1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
      1:{ lia. } 1:{ lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
      match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
        assert (PAD : rw_cells psegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app psegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
        | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
          replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
      end.
      stmt (HS_T2 fuel HH) as NX2.
      jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End F_printf_core_t1.

Module F_printf_core_intc2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_TAIL : S_TAIL.

  Lemma L_INTC2 : S_INTC2.
  Proof using GLO HAP HS_TAIL LO QHI SEP_B SEP_F.
    intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (zb_length body) as LB.
    set (n := Z.of_nat (length body)) in *.
    stmt (HS_TAIL fuel HH) as NX.
    ienter.
    zs. zs. brf K1.
    -
      replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
      zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
      zs. brf K2; [ | zs ]; zs; zs.
      all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
        | unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
    -
      replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
      zs. brf K3.
      +
        assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
        replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        zs. brf K2; [ | zs ]; zs; zs.
        all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
          | unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      +
        assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
        replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | apply bytes_at_nil; lia | apply Forall_nil
          | unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End F_printf_core_intc2.

Module F_printf_core_intc.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_INTC2 : S_INTC2.

  Lemma L_INTC : S_INTC.
  Proof using HS_INTC2.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_INTC2 fuel HH) as NX.
    unfold conv_int.
    ienter.
    destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
    -
      replace (false && (-1 <? 0))%bool with false by reflexivity.
      zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
    -
      replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
      zs. zs.
      replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
        by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
      cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
      pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
      rewrite (nzmask_eq fl) in FLB |- * by lia.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
  Qed.
End PrintfCore.
End F_printf_core_intc.

Module F_printf_core_dloop.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI.
    intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (dec_digits_step x ltac:(lia)) as DS.
    pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
    pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
    assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
    assert (LD : (2 <= zlength (dec_digits x))%Z).
    { rewrite DS. unfold zlength. rewrite length_app. cbn [length].
      destruct (Z.lt_ge_cases (x / 10) 10).
      - rewrite dec_digits_small by lia. cbn. lia.
      - rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    zs. zs. zs. zs. zs.
    rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite div10_magic by lia. zs. zs. zs.
    replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
    rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
    set (c := (48 + x mod 10)%Z) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
    pose proof (u8arr_store_ok psegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write psegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    -
      eapply evt_mono.
      { eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
      unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
      assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
      rewrite EL.
      split; [ mseq | ].
      split; [ eapply munch_trans; [exact MU | exact MU'] | ].
      split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
      split; [ exact MI' | ].
      split.
      { replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
          with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
        rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
        replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
        rewrite zb_app, <- !app_assoc. reflexivity. }
      split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
    -
      zs. apply evt_done.
      unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
      split; [ mseq | ].
      split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
      split.
      { replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
        rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
        replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
      split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
  Qed.
End PrintfCore.
End F_printf_core_dloop.

Module F_printf_core_fmtu2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_INTC : S_INTC.

  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR.
    intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad _
           FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
    pose proof (dec_digits_length x) as LDX.
    stmt (HS_INTC fuel HH) as NX.
    ienter.
    zs. zs. brf K1.
    -
      destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
      rewrite app_nil_r in DIG.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    -
      destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
      assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
      zs. rewrite lor48_digit by lia. zs.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
      pose proof (u8arr_store_ok psegs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
      pose proof (u8arr_write psegs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
      assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
      { rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
        rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
        replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      rewrite EU in DA2.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
      replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
        by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
      pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
      rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
      zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
End PrintfCore.
End F_printf_core_fmtu2.

Module F_printf_core_fmtu.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_FMTU2 : S_FMTU2.
  Hypothesis HS_DLOOP : S_DLOOP.

  Lemma L_FMTU : S_FMTU.
  Proof using BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR.
    intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    pose proof (dec_digits_length x) as LDX.
    stmt (HS_FMTU2 fuel HH) as NX.
    ienter.
    zs. zs. zs. brf K.
    -
      zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
        [ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
        | destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
        | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    -
      zs.
      stmt HS_DLOOP as NL.
      callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
        | right; split; [assumption | assumption]
        | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
End PrintfCore.
End F_printf_core_fmtu.

Module F_printf_core_cvd.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_FMTU : S_FMTU.

  Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
    (Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
  Proof using .
    clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
    change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    split; intros H; Z.div_mod_to_equations; nia.
  Qed.

  Lemma L_CV_D : S_CV_D.
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
    set (argi := (i mod 2^64)%Z) in *.
    unfold INTMAX_MAX, MARK_POS, PAD_POS.
    ienter.
    zs. zs. brf K1.
    -
      zs. zs. zs. zs. zs. zs. zs. zs.
      replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
      replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 66213%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zs. zs. zs. zs. zs. brf K2.
      +
        assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
        replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 66214%Z));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      + assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
        replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
        zs. zs. zs. zs. zs.
        pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
        assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
        { pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
          pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
        destruct C1 as [E1 | E1]; rewrite E1 in *.
        *
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 66213%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        *
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 66215%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
End PrintfCore.
End F_printf_core_cvd.

Module F_printf_core_cvu.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_FMTU : S_FMTU.

  Lemma L_CV_U : S_CV_U.
  Proof using GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    ienter.
    zs. zs. zs. zs. zs. zs.
    jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := 66213%Z));
      [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
      | intros m' MI'; exact (pfx_sub m' 0 0 MI' ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
End PrintfCore.
End F_printf_core_cvu.

Module F_printf_core_xloop.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI.
    intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
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
    pose proof (u8arr_store_ok psegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write psegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    -
      eapply evt_mono.
      { eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' P. destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
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
    -
      apply evt_done. unfold xloop_post. eexists _, _, _. cbv zeta.
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
End F_printf_core_xloop.

Module F_printf_core_cvx.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Hypothesis HS_INTC : S_INTC.
  Hypothesis HS_XLOOP : S_XLOOP.

  Lemma L_CV_X : S_CV_X.
  Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    stmt (HS_INTC fuel HH) as NX.
    unfold ALT_FORM.
    assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
    pose proof (hex_digits_length (Z.land t 32) u) as LH.
    assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
    { eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
    ienter.
    zs. zs. zs. zs. brf K0.
    -
      replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
      zs. zs. zs. zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 66213%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
      zs. zs.
      replace (Z.land t 32) with (Z.land t 32) by reflexivity.
      stmt HS_XLOOP as NL.
      callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
             [ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST. cbv zeta in *.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
        rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
      apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
      replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
      zs. zs. brf K1.
      +
        replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
        zs. zs. zs. zs. zs. zs. zs. zs.
        destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 66220%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 66218%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
      +
        replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
                               (BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 66213%Z));
          [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | exact BODY | exact HRNG | unfold zlength in *; lia | zl
          | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
End PrintfCore.
End F_printf_core_cvx.

Module F_printf_core_cvfp.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_CV_FP : S_CV_FP.
  Proof.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp y t pfx s2s za pl plp ylo yhi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Hfl Hw Hc XP CT.
    exfalso. exact (conv_type_dbl t CT).
  Qed.
End PrintfCore.
End F_printf_core_cvfp.

Module F_printf_core_p1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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
  Hypothesis HS_EXIT1 : S_EXIT1.

  Lemma L_P1 : S_P1.
  Proof using HF HS_DIR HS_EXIT1 HS_SCAN.
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
           FI MU1 LOW DIG PAD P1.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
    unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
    pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
    cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (n := Z.of_nat (length (lit_run fmt))) in *.
    rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
    destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
    destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
    assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
            /\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
    { rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
      destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
      split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
      intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
    destruct TERM as [TERM PDX].
    zs. zs. zs. br K. zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
    -
      assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
      zs. if_lit. zs. zs. if_lit. zs. zs.
      jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
    -
      jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
              [ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
              | destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
              | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2. rewrite !Z.add_0_r.
      zs. if_lit. zs. brf K1.
      +
        assert (N0 : n = 0%Z) by lia.
        destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
        destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
        rewrite N0 in PD.
        jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
        intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
        zs. if_lit. zs. zs.
        jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
      +
        zs. zs. zs. br K2. zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
        *
          zs. if_lit. zs. zs. if_lit. zs. zs.
          jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
        *
          destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
          destruct (PDX K3) as (d & rest & PD).
          jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
                  [ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
                  | right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
          intros a1' a2''. rewrite !Z.add_0_r.
          zs. if_lit. zs. if_lit.
          jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
          intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
          zs. if_lit. zs. zs.
          jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
  Qed.
End PrintfCore.
End F_printf_core_p1.

Module F_printf_core_pro.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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


  Lemma L_PRO : S_PRO.
  Proof using BS0 GLO HA HAP HVA LO QHI SEP_F.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
    destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
    pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
    pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl psegs m0) as WM.
    pose proof ST0 as ST.
    carve_frame 544%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 544 junk [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 320; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    do 43 zs.
    lazymatch type of FR with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in FR; clearbody jA end.
    lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in FR; clearbody jB end.
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
    apply (rw_cells_split_CB psegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB psegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB psegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    do 7 c8ify LOWa.
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
    apply (proj1 (rw_cells_app psegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
    replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
    replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
    eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
    unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
    split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
    split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
  Qed.
End PrintfCore.
End F_printf_core_pro.

Module F_printf_core.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib Printf_zfacts F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_memchr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.F_strnlen OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_zfacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_core_conv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_core_conv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_core_conv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_core_conv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_core_conv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Export F_printf_core_common.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.
Local Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

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
  Hypothesis HA : (A + zlength fmt <= 163840)%Z.
  Hypothesis SEP_F : ((0x29108 <= Fp /\ Fp + 232 <= 370424) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((370432 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 168192 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 370424 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call psegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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

  Lemma L_EXIT : S_EXIT.
  Proof using LO.
    first [ apply F_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply F_printf_core_exit.L_EXIT; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_END : S_END.
  Proof using GLO HAP LO SEP_F VAHI.
    first [ apply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO.
    first [ apply F_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply F_printf_core_exit1.L_EXIT1; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using A0 HA HF.
    first [ apply F_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply F_printf_core_scan.L_SCAN; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF.
    first [ apply F_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply F_printf_core_flags.L_FLAGS; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF.
    first [ apply F_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply F_printf_core_width.L_WLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF.
    first [ intro; apply F_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply F_printf_core_width.L_WIDTH; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF.
    first [ apply F_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply F_printf_core_prec.L_PLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF.
    first [ intro; apply F_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply F_printf_core_prec.L_PREC; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF.
    first [ apply F_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply F_printf_core_state.L_STATE; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF.
    first [ apply F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
    first [ apply F_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply F_printf_core_t6.L_T6; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply F_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply F_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply F_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply F_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI.
    first [ apply F_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply F_printf_core_dloop.L_DLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI.
    first [ apply F_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply F_printf_core_xloop.L_XLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_FP : S_CV_FP.
  Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ.
    first [ apply F_printf_core_cvfp.L_CV_FP; first [eassumption]
          | intros; eapply F_printf_core_cvfp.L_CV_FP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ apply F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP]
          | intros; eapply F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
    first [ intro; apply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_core_conv.F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using A0 HA HF LO.
    first [ apply F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using BS0 GLO HA HAP HVA LO QHI SEP_F.
    first [ apply F_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply F_printf_core_pro.L_PRO; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk psegs m0 lo q -> mem_inv psegs m0 -> bytes_at psegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells psegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
      (0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
      implM psegs (printf_model OUT OUTFP fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x22ce8) fc0 None m0 (seg_rom psegs)).
  Proof using FRM0 HS_HEAD HS_PRO.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]). }
    assert (APC : rw_cells psegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk psegs m0 lo q -> mem_inv psegs m0 -> bytes_at psegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evt psegs (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x22ce8) fc0 None m0 (seg_rom psegs)).
  Proof using HS_P1 HS_PRO.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    stmt HS_P1 as NX1.
    jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
  Qed.

End PrintfCore.


Theorem printf_core_proof : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
  sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
  printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof.
  intros St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA BS0 SEPF SEPB HAP HVA VAHI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM HA SEPF SEPB HAP HVA (proj1 Ra1) VAHI BS0
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implM_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
  pose proof (L_CORE1 0x29108 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI HA ltac:(lia) HAP ltac:(lia) (proj1 Ra1) ltac:(lia)
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evt_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.
End F_printf_core.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_vsnprintf.F_printf_core.

Module F_printf_snsink.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy F_fwritex Printf_mlib F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma bytes_at_func : forall m a (bs1 bs2 : list byte), bytes_at psegs m a bs1 -> bytes_at psegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite <- H1 by exact Hi. rewrite <- H2 by lia. reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.
Lemma C8_func : forall m a (v w : word), rw_cells psegs m a [C8 v] -> rw_cells psegs m a [C8 w] -> v = w.
Proof.
  intros m a v w [[_ H1] _] [[_ H2] _]. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
  pose proof (bytes_at_func _ _ _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity.
Qed.

Section SnProofs.
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

  Lemma sn_sink_frame : sink_frame_stmt Fp B 80 SINK.
  Proof.
    unfold sink_frame_stmt. intros W m m' o (junk & WF & FR & FRL & LEN & SEPB & T1 & T2) MU WM D1 D2.
    exists junk. split; [|split; [|split; [exact FRL | split; [exact LEN | split; [exact SEPB | split; assumption]]]]].
    - destruct WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
      pose proof (zb_length o) as LZ. unfold zlength, SN_CAP in LEN.
      split; [|split; [|repeat split; assumption]].
      + eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size FILE_cells csize Nat.add]; lia | cbn [cells_size FILE_cells csize Nat.add]; lia].
      + eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; rewrite LZ; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | lia | lia].
  Qed.

  Lemma sn_sink_flags : sink_flags_stmt Fp SINK.
  Proof.
    unfold sink_flags_stmt. intros m o (junk & (FC & BUF & FL & _) & _).
    exists fl0. split; [|exact FL].
    apply (proj1 (rw_cells_app psegs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  Lemma sn_topok : topok_stmt (TOPOK_sn TOP).
  Proof. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  Lemma sn_out : out_stmt Fp B 80 SINK (TOPOK_sn TOP) OUT_sn.
  Proof.
    unfold out_stmt. intros until canary. intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 D5. rename st into o.
    destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. unfold OUT_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZb. rewrite LZo in *. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LZb in SB.
    assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; lia).
    unfold OUT_sn. apply implM_get_l. unfold zlength, SN_CAP.
    destruct (Z.leb_spec0 (Z.of_nat (length o) + Z.of_nat (length bs)) 80) as [FIT|NOFIT]; [|apply implM_unr].
    apply implM_put.
    destruct (stk_split _ _ _ (bv_unsigned sp - 64) _ ST ltac:(lia)) as [ST1 ST2].
    eapply evt_mono.
    { eapply (fwritex_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fl0 j1 j2 lbfw B (zb o) junk (zb bs));
        rewrite ?EFp, ?LZo, ?LZb.
      - exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by lia. reflexivity. - lia. - exact ST2. - exact MI.
      - lia. - lia. - lia. - lia. - lia. - lia. }
    cbv beta. intros ms' P. unfold fwritex_post in P. rewrite ?EFp, ?LZo, ?LZb in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
    unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
    split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split. { exists (skipn (length bs) junk). split; [rewrite zb_app; exact WF2|].
             split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
             split; [exact FRL|]. unfold zlength, SN_CAP. rewrite length_app, length_skipn. split; [lia|]. split; [lia|]. split; assumption. }
    split. { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
             - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
             - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    exact SRC'.
  Qed.

End SnProofs.
End F_printf_snsink.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_sn_write.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.

Module F_vfprintf.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset F_memcpy F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_mlib F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.F_pop_arg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_mlib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_vsnprintf.F_printf_core.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_sn_write.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_sn_write OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.F_towrite.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Definition zpk__ (P : Prop) : Prop := P.
Local Ltac zpk1__ H := let T := type of H in change (zpk__ T) in H.
Local Ltac zpk_nf__ H A q := lazymatch A with context [q] => fail | _ => zpk1__ H end.
Local Ltac zidleF__ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q, q + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : ro_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : u8arr segs m ?A _ |- _ => zpk_nf__ H A q
    | H : bytes_at segs m ?A _ |- _ => zpk_nf__ H A q
    end
  end.
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact D4].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells psegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
  rw_cells psegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post [[Hwf Hb] Hw] WF.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells psegs m A cs -> A = A' -> rw_cells psegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells psegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition VF_FRAME : Z := 368.

End F_vfprintf.


Module Printf_sn.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_printf_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = ITree.Ret (Ok (tt, o ++ bs)).
Proof.
  intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
  replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
  pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
  mpad OUT_sn c w l fl o = ITree.Ret (Ok (tt, o ++ concat ps)).
Proof.
  intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
    apply OUT_sn_eq. exact H.
Qed.

Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
  pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
  pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
  pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
  pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
  pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
  pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
  pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
  pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
  rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
    destruct (d_t d =? 117); [|discriminate]. eapply conv_int_sn; eassumption.
  - discriminate.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  printf_loop OUT_sn OUTFP_sn fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
    pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
    pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
    pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
    rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, concat ps)).
Proof.
  intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
  exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

End Printf_sn.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_sn_write OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.F_towrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_vsnprintf.F_vfprintf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_vsnprintf.Printf_sn.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call psegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma rw_cells_recast : forall m A cs cs', rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells psegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells psegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells psegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

Lemma arg_ok_relayout : forall Fp' B' BS' m lo sp ap' sp' w a,
  arg_ok 0 0 0 m lo sp 0 w a -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  arg_ok Fp' B' BS' m lo sp' ap' w a.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' w a H H1 H2 H3 H4 H5 H6 H7. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  repeat (split; [first [assumption | lia]|]). lia.
Qed.
Lemma args_ok_relayout : forall Fp' B' BS' m lo sp ap' sp' ws args,
  args_ok 0 0 0 m lo sp 0 ws args -> lo <= Fp' -> Fp' + 232 <= sp -> lo <= B' -> B' + BS' <= sp -> lo <= ap' -> ap' + 8 <= sp -> sp' <= sp ->
  args_ok Fp' B' BS' m lo sp' ap' ws args.
Proof.
  intros Fp' B' BS' m lo sp ap' sp' ws args. revert ws. induction args as [|a args IH]; intros ws H H1 H2 H3 H4 H5 H6 H7; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [Ha Hr].
  split; [eapply arg_ok_relayout; eassumption | apply IH; assumption].
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv psegs m -> ro_bytes_b psegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at psegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at psegs m A _ (ro_cells_image psegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
