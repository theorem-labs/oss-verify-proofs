(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr SysStep FP ITree Nodes Decode. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_mlib Printf_zfacts Printf_xfacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import FX_lib F_memset F_memcpy F_memchr I_strnlen F_fwritex F_snpf_pop_arg F_snpf_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel PrintfModelX. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import F_snpf_common.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_m2s I_consts F_achk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Definition zpk (P : Prop) : Prop := P.
Local Ltac zpark H := let T := type of H in change (zpk T) in H.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].
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
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 5451776)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((5958088 <= Fp /\ Fp + 232 <= 6748160) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((12358712 <= B /\ B + BS <= lo /\ B + BS <= 12365824) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Hypothesis RIP : rip_stmt.
  Hypothesis HA0 : aext m0 lo q A fmt B BS.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_snpf_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_snpf_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_snpf_common.Fok F).
  Local Notation Fok_refl := (F_snpf_common.Fok_refl F).
  Local Notation Fok_trans := (F_snpf_common.Fok_trans F).
  Local Notation POST := (F_snpf_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_snpf_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_snpf_common.lo_cells AP nla nlt).
  Local Notation finv := (F_snpf_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_snpf_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_snpf_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_snpf_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_snpf_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_snpf_common.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation arg_okx_W := (F_snpf_common.arg_okx_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation args_ok_W := (F_snpf_common.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation lo_cells14 := (F_snpf_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_snpf_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_snpf_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_snpf_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_snpf_common.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation out_postq := (F_snpf_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_snpf_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
  Local Notation memset_callq := (F_snpf_common.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation memset_postq := (F_snpf_common.memset_postq q gp tp lo).
  Local Notation chkr_W := (F_snpf_common.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation ictx_W := (F_snpf_common.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation hsh := (F_snpf_common.hsh B BS q m0 lo A fmt HA0).
  Local Notation chkr_stack0 := (F_snpf_common.chkr_stack0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_fmt0 := (F_snpf_common.chkr_fmt0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_pfx0 := (F_snpf_common.chkr_pfx0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_xdig0 := (F_snpf_common.chkr_xdig0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_nulls0 := (F_snpf_common.chkr_nulls0 B BS q m0 lo A fmt HA0).
  Local Notation arg_ok_chk := (F_snpf_common.arg_ok_chk Fp B BS).
  Local Notation chkr_buf0 := (F_snpf_common.chkr_buf0 B BS q m0 lo A fmt HA0).
  Local Notation fp_postq := (F_snpf_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_snpf_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_snpf_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_snpf_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_snpf_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_snpf_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_snpf_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_snpf_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_snpf_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_snpf_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_snpf_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dir_fp := (F_snpf_common.dir_fp q AP).
  Local Notation dir_post := (F_snpf_common.dir_post Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_C := (F_snpf_common.S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_snpf_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_snpf_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_snpf_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_snpf_common.body_loc Fp B BS q lo).
  Local Notation sarg_at := (F_snpf_common.sarg_at Fp B BS q m0 lo).   (* [comment removed for export] *)
  Local Notation S_TAIL := (F_snpf_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_snpf_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_snpf_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_snpf_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_snpf_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_snpf_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_snpf_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_snpf_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_snpf_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_snpf_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_snpf_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_snpf_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_snpf_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_snpf_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_snpf_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_snpf_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_snpf_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_snpf_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_snpf_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_snpf_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_snpf_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_snpf_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_snpf_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_snpf_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_snpf_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_snpf_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_snpf_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_snpf_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
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
  (* [comment removed for export] *)
  Local Ltac br K ::= brf K; try (exfalso; first [ zify_prune_plain; Zify.zify; xlia zchecker | revert K; sf_unhide; dj_prune; intros K; Zify.zify; xlia zchecker ]).
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
        [ match goal with H : ro_cells _ _ 5943776 _ |- _ => exact H end
        | match goal with H : ro_cells _ _ 12358704 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | chk0_tac ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call ctasegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac. (* [comment removed for export] *)
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
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

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.
  Hypothesis HS_CV_FP : S_CV_FP.
  Hypothesis HS_CV_C : S_CV_C.

  (* [comment removed for export] *)
  Ltac lit_rd H := repeat match type of H with context [wa ?e] =>
    lazymatch e with
    | Z.add _ _ => let v := eval vm_compute in e in replace e with v in H by reflexivity
    end end.

  (* [comment removed for export] *)
  Lemma arg_okx_sarg : forall m (w : word) s (xp : bool) (p : Z),
    arg_okx Fp B BS m0 lo q AP w (PA_s s) (if xp then Some p else None) -> munch W m0 m ->
    sarg_at m (bv_unsigned w) s xp p /\ Forall (fun c => 0 < c < 256)%Z s /\ (0 < bv_unsigned w)%Z.
  Proof.   (* [comment removed for export] *)
    clear SFR SFL TOK HOUT HF. intros m w s xp p H0 MU. cbn [arg_okx] in H0.
    destruct H0 as [H0 | (Hp0 & BY & RNG & NZ & HI & D1 & D2 & D3 & D4)].
    - pose proof (arg_ok_chk _ _ _ _ _ _ H0) as CK0.
      pose proof (arg_ok_W _ _ _ _ H0 MU) as H. cbn [arg_ok] in H.
      destruct H as (slack & BY & RNG & PAD & NZ & D1 & D2 & D3 & D4 & CK).
      split; [left; exists slack; repeat (split; [assumption|]); exact CK0|]. split; assumption.
    - destruct xp; [|destruct Hp0]. destruct Hp0 as [Hp CK0].
      split; [right | split; assumption]. split; [reflexivity|]. split; [exact Hp|].
      split; [| repeat (split; [assumption|]); exact CK0].
      eapply bytes_at_transport; [exact BY | exact MU |].
      unfold W. cbn [disjoint_from]. rewrite zb_length. unfold zlength in *. lia.
  Qed.
  Lemma nullstr_sarg : forall m (w : word) (xp : bool) (p : Z), mem_inv ctasegs m -> bv_unsigned w = 0%Z ->
    sarg_at m A_NULLSTR NULLSTR xp p /\ Forall (fun c => 0 < c < 256)%Z NULLSTR.
  Proof.   (* [comment removed for export] *)
    clear SFR SFL TOK HOUT HF. intros m w xp p MI W0.
    destruct (nullstr_arg_ok m w MI W0) as (slack & STR & RNG & PAD & D1 & D2 & D3).
    split; [left; exists slack; repeat (split; [assumption|]); exact chkr_nulls0 | exact RNG].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HS_CV_C HVA LO QHI SEP_B SEP_F SFL SFR VAHI HA0 RIP.
    intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    assert (FpR : (0 <= Fp < 2^64)%Z) by (clear - SEP_F HVA VAHI HAP QHI LO GLO; unfold zlength, PC_DEPTH, GLOBALS_TOP in *; lia).
    (* [comment removed for export] *)
    cbn [args_okx hd_cov tl] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (dir_tyok_cases _ CT) as CASES.
    assert (TR : (65 <= d_t d <= 122)%Z) by (unfold T_PTR, T_INT, T_UINT, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES; lia).
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    (* [comment removed for export] *)
    pose proof (dir_ps_cases _ CT) as PSC.
    unfold convx. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    (* [comment removed for export] *)
    Ltac conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d TT :=
      let K := fresh "K" in let K1 := fresh "K1" in let K2a := fresh "K2a" in let K2 := fresh "K2" in let K3 := fresh "K3" in
      ienter; zs; br K; zs; zs; zs; zs;
      try zpark ARGC; try zpark APC; try zpark ST;
      callw (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI
                                  | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, F_snpf_pop_arg.T_LONG, F_snpf_pop_arg.T_ULONG,
                                      PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG; lia]);
      try clear ARGC APC ST; try fix_stk;
      match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rewrite ETY in H;
        cbn [pop_arg_lo pop_arg_hi F_snpf_pop_arg.T_PTR F_snpf_pop_arg.T_INT F_snpf_pop_arg.T_UINT F_snpf_pop_arg.T_SIZET F_snpf_pop_arg.T_LONG F_snpf_pop_arg.T_ULONG
             T_PTR T_INT T_UINT T_DBL PrintfModel.T_PTR PrintfModel.T_INT PrintfModel.T_UINT PrintfModel.T_SIZET T_LONG T_ULONG Z.eqb Pos.eqb] in H; rename H into ARGC' end;
      match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end;
      zs;
      (let FLC := fresh "FLC" in let fb := fresh "fb" in let FB := fresh "FB" in
       match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC);
      rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht; try rewrite TT;
      (* [comment removed for export] *)
      zsto 0x5274a0%Z;
      (let r := getreg 10%Z in
       lazymatch r with
       | context [Z.b2z (0 <? 0)%Z] => replace (Z.b2z (0 <? 0)%Z) with 0%Z by reflexivity; rewrite Z.land_0_l
       | Z_to_bv 64 ?e => let v := eval vm_compute in e in replace (Z_to_bv 64 e) with (Z_to_bv 64 v) by reflexivity
       end);
      zs; br K2a;
      (* [comment removed for export] *)
      zsto 0x5274b4%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | let K2' := fresh "K2'" in
        assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (let E := fresh "E" in intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ];
      (* [comment removed for export] *)
      zsto 0x5274c4%Z; zs; br K3; zsto 0x5274d8%Z;
      try replace (Z.shiftl (d_t d + -65) 2 + 1156792)%Z with (1156792 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
    (* [comment removed for export] *)
    destruct a as [sv | | iv | uv | zv | dd].
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l].
      assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
      assert (PS0 : dir_psx d = 0%Z) by (destruct PSC as [(P & _) | [(P & _ & E) | (P & CL)]]; [exact P | exfalso; unfold T_PTR, PrintfModel.T_SIZET in E, ETY; lia | exfalso; destruct (conv_type_l_inv _ _ CL) as [[_ E]|[_ E]]; unfold T_PTR, T_LONG, T_ULONG in E, ETY; lia]).
      rewrite PS0.
      conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d Ht. all: the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
      all: rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
           pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
           match goal with MUc : munch _ m0 ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             destruct (arg_okx_sarg _ _ _ _ _ AOK1 MUc) as (SARG & SRNG & P0) end;   (* [comment removed for export] *)
           stmt (HS_CV_S fuel HH) as NX;
           jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                  (xp := d_xp d) (PV := bv_unsigned slot) (P := bv_unsigned slot) (s := sv));
           [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
           | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact SARG | exact SRNG | left; split; [reflexivity | exact P0]
           | subst fl'; rewrite ?land_land_same; reflexivity ].
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l].
      assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
      assert (PS0 : dir_psx d = 0%Z) by (destruct PSC as [(P & _) | [(P & _ & E) | (P & CL)]]; [exact P | exfalso; unfold T_PTR, PrintfModel.T_SIZET in E, ETY; lia | exfalso; destruct (conv_type_l_inv _ _ CL) as [[_ E]|[_ E]]; unfold T_PTR, T_LONG, T_ULONG in E, ETY; lia]).
      rewrite PS0.
      conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d Ht. all: the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
      all: cbn [arg_okx arg_ok] in AOK1;
           rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
           pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
           match goal with MIc : mem_inv _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             destruct (nullstr_sarg mm slot (d_xp d) (d_p d) MIc AOK1) as (SARG & SRNG) end;
           stmt (HS_CV_S fuel HH) as NX;
           jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                  (xp := d_xp d) (PV := 0%Z) (P := A_NULLSTR) (s := NULLSTR));
           [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
           | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact SARG | exact SRNG | right; split; reflexivity
           | subst fl'; rewrite ?land_land_same; reflexivity ].
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l].
      assert (TDI : (d_t d = 100 \/ d_t d = 105 \/ d_t d = 99)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
      assert (PS0 : dir_psx d = 0%Z) by (destruct PSC as [(P & _) | [(P & _ & E) | (P & CL)]]; [exact P | exfalso; unfold T_INT, PrintfModel.T_SIZET in E, ETY; lia | exfalso; destruct (conv_type_l_inv _ _ CL) as [[_ E]|[_ E]]; unfold T_INT, T_LONG, T_ULONG in E, ETY; lia]).
      rewrite PS0. cbn [arg_okx arg_ok] in AOK1. destruct AOK1 as [Hiv Emod].
      destruct (Z.eqb_spec (d_t d) 99) as [T99 | N99].
      + (* [comment removed for export] *)
        conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d T99. all: the_mi ltac:(fun M => pose proof (jt1_read_c _ _ M T99) as RD1); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
        all: rewrite (sx32_int slot iv Hiv Emod) in ARGC';
             pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
             stmt (HS_CV_C fuel HH) as NX;
             jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536)) (xp := d_xp d) (i := iv));
             [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
             | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv | subst fl'; rewrite ?land_land_same; reflexivity ].
      + (* [comment removed for export] *)
        assert (TDI' : (d_t d = 100 \/ d_t d = 105)%Z) by lia. clear TDI.
        conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d Ht. all: the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI') as RD1); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
        all: rewrite (sx32_int slot iv Hiv Emod) in ARGC';
             pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
             pose proof (Z.mod_pos_bound iv (2^64) ltac:(lia)) as RA;
             stmt (HS_CV_D fuel HH) as NX;
             jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (argi := (iv mod 2^64)%Z));
             [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
             | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact RA ].
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l].
      assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
      assert (PS0 : dir_psx d = 0%Z) by (destruct PSC as [(P & _) | [(P & _ & E) | (P & CL)]]; [exact P | exfalso; unfold T_UINT, PrintfModel.T_SIZET in E, ETY; lia | exfalso; destruct (conv_type_l_inv _ _ CL) as [[_ E]|[_ E]]; unfold T_UINT, T_LONG, T_ULONG in E, ETY; lia]).
      rewrite PS0. cbn [arg_okx arg_ok] in AOK1. destruct AOK1 as [Huv Emod].
      destruct TUX as [T117 | TX];
        [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
      + conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d T117. all: the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1; pose proof RD1 as RD1'; rewrite T117 in RD1'; lit_rd RD1'); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
        all: rewrite (zx32_uint slot uv Emod) in ARGC';
             pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
             stmt (HS_CV_U fuel HH) as NX;
             jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
             [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
             | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      + conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d Ht. all: the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
        all: rewrite (zx32_uint slot uv Emod) in ARGC';
             pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
             stmt (HS_CV_X fuel HH) as NX;
             jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
             [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
             | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia | exact TX ].
    - (* [comment removed for export] *)
      cbn [arg_okx arg_ok] in AOK1.
      pose proof (bv_unsigned_in_range 64 slot) as ZR. unfold bv_modulus in ZR.
      assert (Hzv : (0 <= zv < 2^64)%Z) by (rewrite <- AOK1; change (2^64)%Z with 18446744073709551616%Z; cbn in ZR; lia).
      destruct (Z.eqb_spec (d_ty d) PrintfModel.T_SIZET) as [ETY|NTY]; cbn [orb].
      + (* [comment removed for export] *)
        assert (T117 : d_t d = 117%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
        assert (PS6 : dir_psx d = 6%Z) by (destruct PSC as [(P & CT0 & _) | [(P & _ & _) | (P & CL)]]; [exfalso; pose proof (conv_typex_ty _ _ CT0) as TY0; unfold PrintfModel.T_SIZET in ETY; lia | rewrite P; reflexivity | exfalso; destruct (conv_type_l_inv _ _ CL) as [[_ E]|[_ E]]; unfold PrintfModel.T_SIZET, T_LONG, T_ULONG in E, ETY; lia]).
        rewrite PS6. rewrite (proj2 (Z.eqb_eq _ _) T117).
        conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d T117. all: the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1; pose proof RD1 as RD1'; rewrite T117 in RD1'; lit_rd RD1'); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
        all: rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
             pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
             stmt (HS_CV_U fuel HH) as NX;
             jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv));
             [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
             | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hzv ].
      + destruct (Z.eqb_spec (d_ty d) T_ULONG) as [ETY|NTY2]; cbn [orb].
        * (* [comment removed for export] *)
          assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
          assert (PS1 : dir_psx d = 1%Z) by (unfold dir_psx; rewrite ETY; reflexivity).
          rewrite PS1.
          destruct TUX as [T117 | TX];
            [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia);
              replace ((d_t d =? 120) || (d_t d =? 88))%Z with true by (symmetry; apply orb_true_iff; destruct TX as [E|E]; rewrite E; [left|right]; reflexivity) ].
          -- conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d T117. all: the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1; pose proof RD1 as RD1'; rewrite T117 in RD1'; lit_rd RD1'); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
             all: rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
                  pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
                  stmt (HS_CV_U fuel HH) as NX;
                  jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv));
                  [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
                  | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hzv ].
          -- destruct TX as [TXE | TXE]; try rewrite TXE;
               conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d TXE; (the_mi ltac:(fun M => pose proof (jt1_read_x _ (d_t d) M ltac:(lia)) as RD1; pose proof RD1 as RD1'; rewrite TXE in RD1'; lit_rd RD1'); zs; zs; zs;
      (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
      assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia));
               rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
               pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
               stmt (HS_CV_X fuel HH) as NX;
               lazymatch type of TXE with _ = ?tv =>
               jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv) (t := tv));
               [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
               | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hzv | lia ] end.
        * destruct (Z.eqb_spec (d_ty d) T_LONG) as [ETY|NTY3]; [cbn [negb] | apply implM_unr_l].
          (* [comment removed for export] *)
          assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, T_LONG, T_ULONG in CASES, ETY; lia).
          assert (PS1 : dir_psx d = 1%Z) by (unfold dir_psx; rewrite ETY; reflexivity).
          rewrite PS1.
          destruct TDI as [TDE | TDE].
          all: conv_pre ETY ARGC APC ST VAA NTH MI Hfl Ht i4 d TDE.
          all: the_mi ltac:(fun M => pose proof (jt1_read_d _ (d_t d) M ltac:(lia)) as RD1; pose proof RD1 as RD1'; rewrite TDE in RD1'; lit_rd RD1'); zs; zs; zs;
               (let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end);
               assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
          all: rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
               pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
               stmt (HS_CV_D fuel HH) as NX;
               jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (argi := zv));
               [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
               | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hzv ].
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l].
      exfalso. unfold T_PTR, T_INT, T_UINT, T_DBL, F_snpf_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, PrintfModel.T_DBL, T_LONG, T_ULONG in CASES, ETY; lia.
  Qed.
End PrintfCore.
