(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_mlib Printf_zfacts Printf_xfacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Printf_lib F_memset F_memcpy F_memchr F_strnlen F_fwritex F_pop_arg F_printf_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel PrintfModelX. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import F_printf_core_common.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)

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
  Hypothesis HA : (A + zlength fmt <= 2891776)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((3271984 <= Fp /\ Fp + 232 <= 3486312) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((3486320 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  (* [comment removed for export] *)
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
  Local Notation S_PSTAR := (F_printf_core_common.S_PSTAR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dir_fp := (F_printf_core_common.dir_fp q AP).
  Local Notation dir_post := (F_printf_core_common.dir_post Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_C := (F_printf_core_common.S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 3271976 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 3486312 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call ctusegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac. (* [comment removed for export] *)
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
  Hypothesis HS_PSTAR : S_PSTAR.
  Hypothesis HS_STATE : S_STATE.

  (* [comment removed for export] *)
  Lemma L_DIR : S_DIR.
  Proof using A0 HA HAP HF HS_FLAGS HS_PREC HS_PSTAR HS_STATE HS_WIDTH HVA LO GLO QHI SEP_B SEP_F VAHI.
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i d d' st rest f k args args' covs pfx s2s za pl plp alo ahi j128 _
           FI LOW Hi Hi1 PD Hf P2 P1.
    pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    pose proof (parse_dirx_shape _ _ _ _ PD) as (POSN & SH).
    destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
    destruct SH as (Efl & c1' & s1b & Es1 & s2 & WALT & c2 & s2b & Es2 & ps & nn & PX).
    (* [comment removed for export] *)
    destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
    rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
    assert (K2 : exists k2, (k1 <= k2)%Z /\ s2 = sfx k2).
    { destruct WALT as [(_ & _ & G) | (_ & _ & _ & Es2q & _)].
      - destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & _). exists (k1 + Z.of_nat n2)%Z. split; [lia|]. rewrite Hs2, Hs1. apply sfx_skipn. lia.
      - exists (k1 + 1)%Z. split; [lia|]. rewrite Es2q. exact Es1b. }
    destruct K2 as (k2 & Hk12 & Hs2).
    rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
    assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
    rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.
    pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
    (* [comment removed for export] *)
    assert (DKEEP : d_t d' = d_t d /\ d_ty d' = d_ty d /\ (snd st = false -> d_p d' = d_p d /\ d_xp d' = d_xp d)).
    { destruct (Z.eq_dec f 0) as [F0|F0].
      - rewrite (P1 F0). repeat split; reflexivity.
      - destruct (P2 F0) as (_ & _ & _ & DE). destruct (dir_eff_keeps _ _ _ _ _ DE) as (E1 & E2 & E3 & _). repeat split; try assumption; apply E3; assumption. }
    destruct DKEEP as (DKt & DKty & DKpx).
    (* [comment removed for export] *)
    assert (PSARG : forall (kw : Z) (argsW : list parg) (covsW : list (option Z)) (dW : dir),
      args_okx Fp B BS m0 lo q AP (skipn (Z.to_nat kw) slots) argsW covsW -> (0 <= kw)%Z -> dir_eff_p dW true argsW = Some (d', args') ->
      exists slot, nth_error slots (Z.to_nat kw) = Some slot /\ (bv_unsigned slot mod 2^32 = d_p d' mod 2^32)%Z /\ (0 <= d_p d' < 2^31)%Z /\ d_xp d' = true
                   /\ d_fl d' = d_fl dW /\ d_w d' = d_w dW).
    { intros kw argsW covsW dW AOK Hkw DP.
      destruct (dir_eff_p_true_inv _ _ _ _ DP) as (pv & -> & Hpv & ->). cbn.
      cbn [args_okx arg_okx arg_ok] in AOK. destruct (skipn (Z.to_nat kw) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [[Hiv Emod] _].
      exists slot. split.
      { rewrite <- (Nat.add_0_r (Z.to_nat kw)), <- nth_error_skipn, ESK. reflexivity. }
      split; [exact Emod|]. split; [lia|]. repeat split; reflexivity. }
    (* [comment removed for export] *)
    assert (POSTSTATE : forall (m2 : word -> option byte) (k3 : Z) (t1 a1r a3r a4r : word),
      finv m2 -> rw_cells ctusegs m2 (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      munch (dir_fp st f) m m2 -> wmono ctusegs m m2 ->
      (f <> 0%Z -> rw_cells ctusegs m2 AP [C8 (Z_to_bv 64 (VA + 8 * dir_k st f k))]) ->
      (0 <= d_fl d' < 131072)%Z -> (0 <= d_w d' <= INT_MAX)%Z -> (-1 <= d_p d' <= INT_MAX)%Z ->
      (k2 <= k3)%Z -> conv_statex (sfx k3) = Some (d_ty d, ps, nn) ->
      d_t d = nth (nn - 1)%nat (sfx k3) 0%Z -> rest = skipn nn (sfx k3) ->
      evt ctusegs (dir_post x1 x6 x7 x18 x19 (Z_to_bv 64 f) x23 x26 x28 x29 x30 x31 Ft fc i d' rest st f k pfx s2s za pl plp alo ahi j128 m)
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d'))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) a1r (Z_to_bv 64 (A + k3)) a3r a4r (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 x18 x19 (Z_to_bv 64 f) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (d_w d')) x23 (Z_to_bv 64 (d_fl d')) (Z_to_bv 64 (d_p d')) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2b7e4c) fc None m2 (seg_rom ctusegs))).
    { intros m2 k3 t1 a1r a3r a4r FI2 LOW2 MU2 WM2 APC2 Hfl' Hw' Hp' Hk30 CS Ht Hrest.
      pose proof FI2 as FI2'. destruct FI2 as (MI2 & _).
      destruct (conv_state_at fmt k3 d _ _ ltac:(subst k1; lia) CS) as (Hk3n & Hnn1 & Enth & Eskip & Eps).
      stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k3) (ty := d_ty d) (ps := ps) (n := nn); [exact FI2' | zl | exact CS | ]).
      intros a2q a3q2.
      rewrite <- Eps. replace (dir_psx d) with (dir_psx d') by (unfold dir_psx; rewrite DKty; reflexivity).
      rewrite <- DKty.
      jump (apply evt_done; unfold dir_post; exists (k3 + Z.of_nat nn)%Z; do 5 eexists; split; [reflexivity|]).
      split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact FI2'|]. split; [exact LOW2|]. split; [exact APC2|].
      split; [zl|]. split; [rewrite Hrest, Eskip; reflexivity|]. split; [rewrite DKt, Ht, Enth; f_equal; lia|].
      split; [exact Hfl'|]. split; [exact Hw'|]. exact Hp'. }
    (* [comment removed for export] *)
    assert (POSTWIDTH : forall (mw : word -> option byte) (kw wr flr : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
      finv mw -> rw_cells ctusegs mw (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      munch (dir_fp st f) m mw -> wmono ctusegs m mw ->
      (f <> 0%Z -> rw_cells ctusegs mw AP [C8 (Z_to_bv 64 (VA + 8 * kw))] /\ (0 <= kw)%Z /\ (dir_k st f k = kw + (if snd st then 1 else 0))%Z
                  /\ (snd st = true -> exists slot, nth_error slots (Z.to_nat kw) = Some slot /\ (bv_unsigned slot mod 2^32 = d_p d' mod 2^32)%Z
                                         /\ (0 <= d_p d' < 2^31)%Z /\ d_xp d' = true)) ->
      wr = d_w d' -> flr = d_fl d' ->
      (0 <= d_fl d' < 131072)%Z -> (0 <= d_w d' <= INT_MAX)%Z ->
      evt ctusegs (dir_post x1 x6 x7 x18 x19 (Z_to_bv 64 f) x23 x26 x28 x29 x30 x31 Ft fc i d' rest st f k pfx s2s za pl plp alo ahi j128 m)
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                 x18 x19 (Z_to_bv 64 f) (Z_to_bv 64 (A + i)) (Z_to_bv 64 wr) x23 (Z_to_bv 64 flr) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2b7d14) fc None mw (seg_rom ctusegs))).
    { intros mw kw wr flr t0 t1 a1 a3 a4 a5 a6 a7 FIw LOWw MUw WMw PW -> -> Hfl' Hw'.
      pose proof FIw as FIw'.
      destruct PX as [(N46 & Hp & Hxp & Hps & CS & Ht & Hrest) | [(E46 & Hxp & Hps & c3 & s3b & Es2bq & N42q & s3 & G2 & CS & Ht & Hrest) | (E46 & Hxp & Hps & Hp & s3b & Es2bq & NDG & CS & Ht & Hrest)]].
      - (* [comment removed for export] *)
        destruct (DKpx Hps) as [DKp DKxp].
        stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := k2); [exact FIw' | exact LOWw | lia | | ]).
        { left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity. }
        intros a1q a3q a4q Hpr. rewrite <- DKp, <- DKxp. rewrite Hs2 in CS, Ht, Hrest.
        apply (POSTSTATE mw k2); try assumption.
        + intros F0. destruct (PW F0) as (APC & _ & EK & _). rewrite EK, Hps, Z.add_0_r. exact APC.
        + rewrite DKp. exact Hpr.
        + subst k1; lia.
      - (* [comment removed for export] *)
        destruct (DKpx Hps) as [DKp DKxp].
        rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
        destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
        rewrite Hs3 in CS, Ht, Hrest.
        assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1; lia).
        stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (k2 + 1 + Z.of_nat n3)%Z); [exact FIw' | exact LOWw | lia | | ]).
        { right. rewrite Hxp. destruct (conv_state_at fmt _ d _ _ Hk30 CS) as (Hk3 & Hnn1 & _).
          split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
          split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
        intros a1q a3q a4q Hpr. rewrite <- DKp, <- DKxp.
        apply (POSTSTATE mw (k2 + 1 + Z.of_nat n3)%Z); try assumption.
        + intros F0. destruct (PW F0) as (APC & _ & EK & _). rewrite EK, Hps, Z.add_0_r. exact APC.
        + rewrite DKp. exact Hpr.
        + lia.
      - (* [comment removed for export] *)
        rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) 42%Z s3b ltac:(lia) Es2bq) as (Hk21 & E42 & Es3b).
        assert (Hk22 : (k2 + 2 < zlength fmt)%Z).
        { destruct (Z.lt_ge_cases (k2 + 2) (zlength fmt)); [assumption|]. exfalso.
          rewrite Es3b, (sfx_nil fmt (k2 + 1 + 1)) in NDG by lia. exact NDG. }
        rewrite Es3b in NDG, CS, Ht, Hrest. replace (k2 + 1 + 1)%Z with (k2 + 2)%Z in NDG, CS, Ht, Hrest by lia.
        rewrite (sfx_cons fmt (k2 + 2)) in NDG by zl.
        stmt HS_PSTAR as NXQ.
        jump (eapply NXQ with (k2 := k2) (f := f) (kc := kw) (pv := (if f =? 0 then 0 else d_p d')%Z)
                               (slot := match nth_error slots (Z.to_nat kw) with Some w => w | None => Z_to_bv 64 0 end);
              [exact FIw' | exact LOWw | lia | zl | rewrite <- Ec2; exact E46 | symmetry; exact E42 | exact NDG | exact Hf | | ]).
        { intros F0. destruct (PW F0) as (APC & Hkw & EK & PS). destruct (PS Hps) as (slot & NTH & Emod & Hpv & _).
          rewrite NTH. rewrite (proj2 (Z.eqb_neq f 0) F0). split; [exact APC|]. split; [exact Hkw|]. split; [reflexivity|]. split; [lia | exact Emod]. }
        intros m' a1q a3q a4q MU' WM' FI2 LOW2 APC2.
        (* [comment removed for export] *)
        assert (Exp : Z.b2z (d_xp d') = 1%Z /\ (if f =? 0 then 0 else d_p d')%Z = d_p d' /\ (-1 <= d_p d' <= INT_MAX)%Z).
        { destruct (Z.eq_dec f 0) as [F0|F0].
          - rewrite (P1 F0), Hxp, Hp, F0. cbn. unfold INT_MAX. repeat split; lia.
          - destruct (PW F0) as (_ & _ & _ & PS). destruct (PS Hps) as (slot & _ & _ & Hpv & Exp').
            rewrite Exp', (proj2 (Z.eqb_neq f 0) F0). cbn. unfold INT_MAX. repeat split; lia. }
        destruct Exp as (Exp & Ep & Hp').
        rewrite !Ep. rewrite <- Exp. replace (A + k2 + 2)%Z with (A + (k2 + 2))%Z by lia.
        apply (POSTSTATE m' (k2 + 2)%Z); try assumption.
        + eapply munch_trans; [exact MUw|]. eapply munch_weaken; [|exact MU'].
          unfold sub_fp, dir_fp. intros x Hout. destruct (Z.eqb_spec f 0) as [F0|F0]; [exact I|].
          rewrite Hps, Bool.orb_true_r in Hout. cbn [andb negb outside] in Hout |- *. split; [|exact I]. exact (proj1 (proj2 Hout)).
        + eapply wmono_trans; [exact WMw | exact WM'].
        + intros F0. destruct (PW F0) as (_ & _ & EK & _). rewrite EK, Hps. replace (VA + 8 * (kw + 1))%Z with (VA + 8 * kw + 8)%Z by lia. exact (APC2 F0).
        + lia.
    }
    (* [comment removed for export] *)
    assert (POSTFLAGS_W : znth fmt k1 <> 42%Z -> forall (t0 t1 a3 a4 a5 a6 a7 : word),
      evt ctusegs (dir_post x1 x6 x7 x18 x19 (Z_to_bv 64 f) x23 x26 x28 x29 x30 x31 Ft fc i d' rest st f k pfx s2s za pl plp alo ahi j128 m)
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
                 x18 x19 (Z_to_bv 64 f) (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2b7c2c) fc None m (seg_rom ctusegs))).
    { intros N42 t0 t1 a3 a4 a5 a6 a7.
      destruct WALT as [(_ & Hws & G) | (E42 & _)]; [| exfalso; apply N42; rewrite <- Ec1'; exact E42].
      (* [comment removed for export] *)
      assert (Ed' : d_fl d' = d_fl d /\ d_w d' = d_w d
                    /\ (f <> 0%Z -> snd st = true -> exists slot, nth_error slots (Z.to_nat k) = Some slot /\ (bv_unsigned slot mod 2^32 = d_p d' mod 2^32)%Z
                                                      /\ (0 <= d_p d' < 2^31)%Z /\ d_xp d' = true)).
      { destruct (Z.eq_dec f 0) as [F0|F0]; [rewrite (P1 F0); repeat split; try reflexivity; intros F1; exfalso; exact (F1 F0)|].
        destruct (P2 F0) as (_ & Hk & AOK & DE). destruct (dir_eff_stages _ _ _ _ _ DE) as (d1 & args1 & DW & DP).
        destruct st as [ws0 ps0]; cbn [fst snd] in Hws, DW, DP |- *. subst ws0. rewrite dir_eff_w_false in DW. injection DW as <- <-.
        destruct ps0.
        - destruct (PSARG k args covs d AOK Hk DP) as (slot & NTH & Emod & Hpv & Exp & Efl' & Ew'). split; [exact Efl'|]. split; [exact Ew'|].
          intros _ _. exists slot. repeat split; first [assumption | lia].
        - rewrite dir_eff_p_false in DP. injection DP as <- <-. repeat split; try reflexivity. intros _ X; discriminate X. }
      destruct Ed' as (Efl' & Ew' & PSW).
      stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := sfx k2); [exact FI' | unfold lo_cells, ssp_guard; exact LOW | lia | rewrite <- Hs1, <- Hs2; exact G | rewrite Es2; discriminate | ]).
      intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
      assert (k2' = k2).
      { pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2' in L2. lia. }
      subst k2'.
      jump (apply (POSTWIDTH m k); [exact FI' | unfold lo_cells, ssp_guard; exact LOW | apply munch_refl | apply wmono_refl |
                                   | rewrite Ew'; reflexivity | rewrite Efl', Efl; reflexivity | rewrite Efl', Efl; exact FLR | rewrite Ew'; exact Hw]).
      intros F0. destruct (P2 F0) as (APC & Hk & _). split; [exact APC|]. split; [exact Hk|]. split.
      - unfold dir_k, nstars. rewrite (proj2 (Z.eqb_neq f 0) F0), Hws. cbn [negb fst snd]. destruct (snd st); lia.
      - exact (PSW F0). }
    (* [comment removed for export] *)
    assert (POSTFLAGS_S : znth fmt k1 = 42%Z -> forall (t0 t1 a3 a4 a5 a6 a7 : word),
      evt ctusegs (dir_post x1 x6 x7 x18 x19 (Z_to_bv 64 f) x23 x26 x28 x29 x30 x31 Ft fc i d' rest st f k pfx s2s za pl plp alo ahi j128 m)
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
                 x18 x19 (Z_to_bv 64 f) (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x2b7bec) fc None m (seg_rom ctusegs))).
    { intros E42 t0 t1 a3 a4 a5 a6 a7.
      destruct WALT as [(N42 & _) | (_ & Hws & Hw0 & Es2q & NDG)]; [exfalso; apply N42; rewrite Ec1'; exact E42|].
      rewrite Es1b in NDG. assert (Ek2 : k2 = (k1 + 1)%Z).
      { pose proof (sfx_length fmt k2 ltac:(zl)) as L1. rewrite <- Hs2, Es2q, Es1b, (sfx_length fmt (k1 + 1)) in L1 by zl. lia. }
      rewrite (sfx_cons fmt (k1 + 1)) in NDG by zl.
      pose proof (fmt_rng (k1 + 1) ltac:(zl)) as RG1.
      (* [comment removed for export] *)
      rd_fmt (k1 + 1)%Z. zs. fix_u8 (k1 + 1)%Z. zs. zs. zs. brf K.
      2:{ exfalso. pose proof (proj1 (digit_test _ RG1) K) as DT. rewrite NDG in DT. discriminate DT. }
      clear K.
      (* [comment removed for export] *)
      zs. zs. if_lit. zs.
      (* [comment removed for export] *)
      destruct Hf as [F0 | FF].
      - (* [comment removed for export] *)
        subst f. pose proof (P1 eq_refl) as Ed'.
        pose proof (munch_refl [(q + -456, q + -448)]%Z m) as MU2. pose proof (wmono_refl ctusegs m) as WM2.
        zs. if_lit. zs. zs. zs.
        subst d'.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mw _) =>
          jump (apply (POSTWIDTH mw k);
                [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | unfold dir_fp; rewrite Bool.andb_false_r; exact MU2 | exact WM2
                | intros F0; exfalso; exact (F0 eq_refl) | rewrite Hw0; reflexivity | rewrite Efl; reflexivity | rewrite Efl; exact FLR | rewrite Hw0; unfold INT_MAX; lia ]) end.
      - (* [comment removed for export] *)
        subst f.
        assert (FpR : (0 < Fp < 2^64)%Z) by (clear - SEP_F HVA VAHI HAP QHI LO GLO; unfold zlength in *; lia).
        destruct (P2 ltac:(lia)) as (APC & Hk & AOK & DE).
        destruct (dir_eff_stages _ _ _ _ _ DE) as (dW & argsW & DEW & DEP). rewrite Hws in DEW.
        destruct (dir_eff_w_true_inv _ _ _ _ DEW) as (wv & Eargs & Hwv & EdW). subst args.
        cbn [args_okx arg_okx arg_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [[Hiv Emod] AOK].
        assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
        { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
        assert (IL : (Z.to_nat k < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
        assert (ESK' : slots' = skipn (Z.to_nat (k + 1)) slots).
        { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
        (* [comment removed for export] *)
        assert (EdWfl : d_fl d' = d_fl dW /\ d_w d' = d_w dW
                       /\ (snd st = true -> exists slot1, nth_error slots (Z.to_nat (k + 1)) = Some slot1 /\ (bv_unsigned slot1 mod 2^32 = d_p d' mod 2^32)%Z
                                             /\ (0 <= d_p d' < 2^31)%Z /\ d_xp d' = true)).
        { destruct (snd st).
          - rewrite ESK' in AOK. destruct (PSARG (k + 1)%Z argsW (tl covs) dW AOK ltac:(lia) DEP) as (slot1 & NTH1 & Emod1 & Hpv & Exp & Efl' & Ew').
            split; [exact Efl'|]. split; [exact Ew'|]. intros _. exists slot1. repeat split; first [assumption | lia].
          - rewrite dir_eff_p_false in DEP. injection DEP as <- <-. repeat split; try reflexivity. intros X; discriminate X. }
        destruct EdWfl as (Efl' & Ew' & PSW).
        pose proof (munch_refl [(q + -456, q + -448); (AP, AP + 8)]%Z m) as MU2. pose proof (wmono_refl ctusegs m) as WM2.
        zs. br K. clear K.
        zs. zs. zs. zs.
        try clear RD RG. pose proof (va_read4 _ VA slots k slot _ VAA NTH Hk eq_refl) as RDV.
        zs. clear RDV. rewrite (sx32_int slot wv Hiv Emod), Z_to_bv_mod64.
        zs. zs. brf K.
        + (* [comment removed for export] *)
          assert (Hw0' : (0 <= wv)%Z). { destruct (Z.lt_ge_cases wv 0); [|assumption]. rewrite land_M64_neg in K by lia. exfalso. lia. }
          clear K.
          assert (Ew2 : wv = d_w d') by (rewrite Ew', EdW; cbn [d_w]; lia).
          assert (Efl2 : fl = d_fl d') by (rewrite Efl', EdW; cbn [d_fl]; rewrite (proj2 (Z.ltb_ge wv 0)) by lia; symmetry; exact Efl).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mw _) =>
            jump (apply (POSTWIDTH mw (k + 1)%Z);
                  [ mk_finv | unfold lo_cells, ssp_guard; exact LOW
                  | unfold dir_fp; rewrite (proj2 (Z.eqb_neq Fp 0)), Hws by lia; cbn [andb negb orb fst]; exact MU2 | exact WM2
                  | intros _ | exact Ew2 | exact Efl2
                  | rewrite <- Efl2; exact FLR
                  | rewrite <- Ew2; unfold INT_MAX; lia ]) end.
          split; [replace (VA + 8 * (k + 1))%Z with (VA + 8 * k + 8)%Z by lia; exact APC|]. split; [lia|]. split; [|exact PSW].
          unfold dir_k, nstars. rewrite (proj2 (Z.eqb_neq Fp 0)), Hws by lia. cbn [negb fst]. destruct (snd st); lia.
        + (* [comment removed for export] *)
          assert (Hwn : (wv < 0)%Z). { destruct (Z.lt_ge_cases wv 0); [assumption|]. rewrite land_M64_id in K by lia. exfalso. lia. }
          clear K. zs. zs. zs. zs.
          replace (bv_swrap 32 (0 - Z.land wv 18446744073709551615)) with (- wv)%Z
            by (rewrite land_M64_neg by lia; rewrite swrap32_eq; Z.div_mod_to_equations; lia).
          assert (Ew2 : (- wv)%Z = d_w d') by (rewrite Ew', EdW; cbn [d_w]; lia).
          assert (Efl2 : Z.lor fl LEFT_ADJ = d_fl d') by (rewrite Efl', EdW; cbn [d_fl]; rewrite (proj2 (Z.ltb_lt wv 0)) by lia; rewrite Efl; reflexivity).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mw _) =>
            jump (apply (POSTWIDTH mw (k + 1)%Z);
                  [ mk_finv | unfold lo_cells, ssp_guard; exact LOW
                  | unfold dir_fp; rewrite (proj2 (Z.eqb_neq Fp 0)), Hws by lia; cbn [andb negb orb fst]; exact MU2 | exact WM2
                  | intros _ | exact Ew2 | exact Efl2
                  | rewrite <- Efl2; apply lor_left_adj_range; exact FLR
                  | rewrite <- Ew2; unfold INT_MAX; lia ]) end.
          split; [replace (VA + 8 * (k + 1))%Z with (VA + 8 * k + 8)%Z by lia; exact APC|]. split; [lia|]. split; [|exact PSW].
          unfold dir_k, nstars. rewrite (proj2 (Z.eqb_neq Fp 0)), Hws by lia. cbn [negb fst]. destruct (snd st); lia. }
    (* [comment removed for export] *)
    assert (FL34 : forall (a3 a4 a5 : word), evt ctusegs (dir_post x1 x6 x7 x18 x19 (Z_to_bv 64 f) x23 x26 x28 x29 x30 x31 Ft fc i d' rest st f k pfx s2s za pl plp alo ahi j128 m)
      (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
               x18 x19 (Z_to_bv 64 f) (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x2b7b9c) fc None m (seg_rom ctusegs))).
    { intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.
      (* [comment removed for export] *)
      assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
      { intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
        pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
        rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
      zs. zs. zs. brf K2.
      - (* [comment removed for export] *)
        assert (NF : flag_bit (znth fmt (i + 1)) = None).
        { destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
          pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
        destruct (NOFLAG NF) as [Efl0 Ek1].
        zs. zs. zs. brf K3.
        + jump (apply (POSTFLAGS_S ltac:(rewrite Ek1; exact K3))).
        + jump (apply (POSTFLAGS_W ltac:(rewrite Ek1; exact K3))).
      - assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
        rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
        zs. zs. zs. zs. zs. brf K3.
        + (* [comment removed for export] *)
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
          destruct (NOFLAG NF) as [Efl0 Ek1].
          zs. zs. brf K4; [ jump (apply (POSTFLAGS_W ltac:(rewrite Ek1; exact K4))) | jump (apply (POSTFLAGS_S ltac:(rewrite Ek1; exact K4))) ].
        + (* [comment removed for export] *)
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
          zs. zs. brf K4; [ jump (apply (POSTFLAGS_W K4)) | jump (apply (POSTFLAGS_S K4)) ]. }
    (* [comment removed for export] *)
    rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
    - (* [comment removed for export] *) zs. zs. apply FL34.
    - assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      assert (Hi2 : (i + 2 < zlength fmt)%Z).
      { destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
        rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
      replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
      rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
      rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
  Qed.
End PrintfCore.
