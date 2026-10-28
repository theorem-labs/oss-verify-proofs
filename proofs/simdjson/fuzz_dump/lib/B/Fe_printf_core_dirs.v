(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import SFModel Arr SysStep ImageA FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Printf_zfacts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import FX_lib F_memset F_memcpy F_memchr I_strnlen F_fwritex Fe_pop_arg Fe_printf_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Fe_printf_core_common.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import R_m2s I_consts F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
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

  Hypothesis HA : (A + zlength fmt <= 1474560 \/ (VA + 8 * zlength slots <= A /\ A + zlength fmt <= 2^62))%Z.

  Hypothesis SEP_F : ((1517296 <= Fp /\ Fp + 232 <= 1526144) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((7123888 <= B /\ B + BS <= lo /\ B + BS <= 7131136) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Hypothesis RIP : rip_stmt.
  Hypothesis HA0 : aext m0 lo q A fmt B BS.

  Local Notation ctx_all := (Fe_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (Fe_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (Fe_printf_core_common.Fok F).
  Local Notation Fok_refl := (Fe_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (Fe_printf_core_common.Fok_trans F).
  Local Notation POST := (Fe_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (Fe_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (Fe_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (Fe_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (Fe_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (Fe_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (Fe_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (Fe_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (Fe_printf_core_common.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation args_ok_W := (Fe_printf_core_common.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation lo_cells14 := (Fe_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (Fe_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (Fe_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (Fe_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (Fe_printf_core_common.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation out_postq := (Fe_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (Fe_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
  Local Notation memset_callq := (Fe_printf_core_common.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation memset_postq := (Fe_printf_core_common.memset_postq q gp tp lo).
  Local Notation chkr_W := (Fe_printf_core_common.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation ictx_W := (Fe_printf_core_common.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation hsh := (Fe_printf_core_common.hsh B BS q m0 lo A fmt HA0).
  Local Notation chkr_stack0 := (Fe_printf_core_common.chkr_stack0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_fmt0 := (Fe_printf_core_common.chkr_fmt0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_pfx0 := (Fe_printf_core_common.chkr_pfx0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_xdig0 := (Fe_printf_core_common.chkr_xdig0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_nulls0 := (Fe_printf_core_common.chkr_nulls0 B BS q m0 lo A fmt HA0).
  Local Notation arg_ok_chk := (Fe_printf_core_common.arg_ok_chk Fp B BS).
  Local Notation chkr_buf0 := (Fe_printf_core_common.chkr_buf0 B BS q m0 lo A fmt HA0).
  Local Notation fp_postq := (Fe_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (Fe_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp m0 lo canary A fmt AP VA LO GLO QHI TQ SEP_F SEP_B HAP HA0).
  Local Notation S_EXIT := (Fe_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (Fe_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (Fe_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (Fe_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (Fe_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (Fe_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (Fe_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRECS1 := (Fe_printf_core_common.S_PRECS1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRECS2 := (Fe_printf_core_common.S_PRECS2 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (Fe_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (Fe_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIRS2 := (Fe_printf_core_common.S_DIRS2 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (Fe_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (Fe_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (Fe_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (Fe_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (Fe_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (Fe_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (Fe_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (Fe_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (Fe_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (Fe_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (Fe_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (Fe_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (Fe_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (Fe_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (Fe_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (Fe_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (Fe_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (Fe_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (Fe_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (Fe_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (Fe_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (Fe_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (Fe_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (Fe_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (Fe_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (Fe_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (Fe_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (Fe_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (Fe_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (Fe_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (Fe_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (Fe_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
  Ltac chk0_tac :=
    first [ apply chkr_stack0; try unfold zrepeat; unfold zlength in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia
          | apply chkr_fmt0; unfold zlength in *; lia
          | apply chkr_pfx0; unfold PFX_A, zlength in *; lia
          | apply chkr_xdig0; unfold XDIG_A, zlength in *; lia
          | match goal with H : chkr m0 ?b ?n |- chkr m0 _ _ => apply (chkr_sub m0 b n _ _ H); unfold zlength in *; lia end ].
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : ro_cells _ _ 1503080 _ |- _ => exact H end
        | match goal with H : ro_cells _ _ 7123880 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | chk0_tac ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp & BCHK);
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
  Hypothesis HS_PRECS2 : S_PRECS2.
  Hypothesis HS_STATE : S_STATE.

  Lemma L_DIRS2 : S_DIRS2.
  Proof using HF HA HAP HVA LO GLO QHI HS_FLAGS HS_PRECS2 HS_STATE HS_WIDTH.
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest k p w pfx s2s za pl plp alo ahi j128 _
           FI LOW Hi Hi1 PD STR APC Hk NTH Hp Hsl HK.
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
      evt bsegs Q
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
                 x18 x19 FPv (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x158474) fc None m (seg_rom bsegs))).
    { intros t0 t1 a3 a4 a5 a6 a7.
      pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
      stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
      intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
      assert (k2' = k2).
      { pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
      subst k2'.
      destruct PX as [PX1 | [PX2 | PX3]].
      { exfalso. destruct PX1 as (_ & _ & _ & NS & _). rewrite NS in STR. discriminate. }
      { exfalso. destruct PX2 as (_ & _ & NS & _). rewrite NS in STR. discriminate. }

      destruct PX3 as (E46 & Hxp & _ & Hp0 & s3 & Es2bq & NPOS & CS & Ht & Hrest).
      rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) 42%Z s3 ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3).
      symmetry in Es3. rewrite <- Es3 in CS, Ht, Hrest.
      assert (Hk30 : (0 <= k2 + 2)%Z) by (subst k1 k2; lia).
      replace (k2 + 1 + 1)%Z with (k2 + 2)%Z in CS, Ht, Hrest by lia.
      destruct (conv_state_at fmt _ d _ _ Hk30 CS) as (Hk3 & Hnn1 & Enth & Eskip & Eps).
      stmt HS_PRECS2 as NXP. jump (eapply NXP with (k2 := k2) (ty := d_ty d) (ps := ps) (n := nn) (k := k) (p := p) (w := w);
        [exact FI' | exact LOW' | lia | zl | congruence | rewrite <- Ec3; reflexivity | exact CS | exact APC | exact Hk | exact NTH | exact Hp | exact Hsl | ]).
      intros a1q a3q a4q m' FIm LOWm APCm MUm WMm.
      stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 2)%Z) (ty := d_ty d) (ps := ps) (n := nn); [exact FIm | zl | exact CS | ]).
      intros a2q a3q2. rewrite Eps in HK.
      jump (apply (HK (k2 + 2 + Z.of_nat nn)%Z); [zl | rewrite Hrest, Eskip; reflexivity | rewrite Ht, Enth; f_equal; lia | lia | lia | exact FIm | exact LOWm | exact APCm | exact MUm | exact WMm]). }

    assert (FL34 : forall (a3 a4 a5 : word), evt bsegs Q
      (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
               x18 x19 FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x1583e4) fc None m (seg_rom bsegs))).
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
    -   zs. zs. apply FL34.
    - assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      assert (Hi2 : (i + 2 < zlength fmt)%Z).
      { destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
        rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
      replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
      rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
      rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
  Qed.
End PrintfCore.
