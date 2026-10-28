(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import StoreFast.
Import ListNotations.
Import ITree.Exc.
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
  Hypothesis QHI : (q < 2^47)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 114688)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((117952 <= Fp /\ Fp + 232 <= 320152) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((320160 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
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
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 117944 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 320152 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call usegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [usegs usegs] in *; fold usegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
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

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.
  Hypothesis HS_CV_FP : S_CV_FP.

  (* [comment removed for export] *)
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI.
    intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    (* [comment removed for export] *)
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { Local Ltac2 Set LiaHints.tbl := fun () => "02;0?11229630753.12911820144373.17111820144373.17211820144373.18011820144373.18112298875324.15712298875324.15812502590456.16712502590456.16813347530571.15913347530571.16016250780604.13416488697634.15916488697634.16017659553348.13821220757366.17521220757366.17621296828022.17521296828022.17621334325971.17221334325971.1732201709572.138 22223856449.13624167486042.15624167486042.15724356465969.16124356465969.16225656252822.15625656252822.15725670969163.15925670969163.16026254586835.14826254586835.14926291562981.15726291562981.15826405758020.13926507015092.15726507015092.15826507015092.15926507015092.16026796251706.15626796251706.15727023455567.13827023455567.13933847179382.17433847179382.1753441642428.157 3441642428.158 3585323792.171 3585323792.172 3585323792.180 3585323792.181 36428921553.17136428921553.17236428921553.18036428921553.18139503347734.15639503347734.15739567979968.16439567979968.16541057740263.15641057740263.15741415942347.16541415942347.16641415942347.16741700582261.17241700582261.17341700582263.17341700582263.17441702679423.17641702679423.17741906833264.13743576287364.15843576287364.15946371690579.13646724979512.13447641313415.15647641313415.15748058715768.13649228402294.17449228402294.17551348401117.15751348401117.15851796643714.13851796643714.13953510313882.17253510313882.17353938488849.16953938488849.17056781706523.16956781706523.17056869590439.17156869590439.17256869590439.18056869590439.1815876717075.165 5876717075.166 5876717075.167 5885425297.172 5885425297.173 5885425298.171 5885425298.172 5885425298.173 59308628304.16159308628304.16259308628566.16559308628566.16659308628566.16759310725504.16359310725504.16459314923118.13859314923118.13959314955108.16559314955108.16659925739149.15659925739149.15765531314038.17465531314038.17566184285354.13866184285354.13966979042378.16666979042378.16766979196698.16366979196698.16466979238011.13567270791940.13867463334306.17467463334306.1758134961349.158 8134961349.159 9004798864.162 9004798864.163 9004799261.161 9004799261.162 9004920490.160 9004920490.161 9300351495.165 9300351495.166 9300351495.167 00000;00G00S00_00k01>01Q01a02102A02Q02Y02a02i03103903A03I03Q03Y03a03i04;04\05=05E05M05U05]06306I06Q06Y06Z06[06c06o07;07G07S07n08I08g09E09M09U09h0:;0:F0:Q0:\0:g0;20;=0;H0;S0<40<U0<V0<W0=80=Y0=a0=i0>10>=0>I0>T0>_0>k0?70?B0?C0?D0?V0?b0@=0@X0@j0A20A:0A;0A<0AG0AR0AZ0Ab0Ac0Ad0Al0B40B?0BJ0BU0B`0Bk0C60CA0CL0CW0Cb0Cm0D80Dj0EO0Em0FO0F^0Fj0G60GQ0Gl0H90HF0Ha0I<0ID0IL0IT0I\0Ih0J40J@0JL0JX0J`0Jh0K00K<0KH0KT0K`0Kl0L80LD0LP0LX0L`0LhS2Hk3LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS2LO3GLO3HAP3LZB2LUS2LO3GLO3HAP3LZB2LUS3Hfl3LZB2LU3FLBS3Hfl3LZB2LU3FLBS3HAP3HVA3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU5CASES3ETYS2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU1KS2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU1KS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO2HA3HAP3LZB2LUS2LO3GLO2HA3HAP3LZB2LUS3LZB2LUS3LZB2LUFFS3LZB2LUS3HAP3LZB2LUS3HAP3LZB2LUS3HAP3LZB2LUS3HAP3LZB2LUS2LO3GLO5SEP_F3HAP3LZB2LU1KS2LO3GLO5SEP_F3HAP3LZB2LU1KS2LO3GLO5SEP_F3HAP4VAHI3LZB2LUS2LO3GLO5SEP_F3HAP4VAHI3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3HAP3LZB2LUS2LO3GLO3HAP3LZB2LUS2Hk3LZB2LUS2Hk3LZB2LUS2Hk3LZB2LUS2Hk3LZB2LUS2Hw3LZB2LUS2Hw3LZB2LUS2Hw3LZB2LUS2Hw3LZB2LUS2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU1KS2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU1KFFS2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU1KS2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU1KS3LZB2LUS3LZB2LUS3LZB2LUS3Hfl3LZB2LUS3Hfl3LZB2LUS3LZB2LU2TRS3LZB2LU2TRS3Hfl3LZB2LUS3Hfl3LZB2LUS3LZB2LU2TXFFS3LZB2LU5CASES3ETYS3Hfl3LZB2LUS2LO3GLO5SEP_F3HAP3LZB2LU1KS2LO3GLO5SEP_F3HAP3LZB2LU1KS3LZB2LU5CASES3ETYS3LZB2LUS3LZB2LUFFS2Hk3LZB2LUS2Hk3LZB2LUS3LZB2LUS3LZB2LUFFS3LZB2LUS3LZB2LUS2Hc3LZB2LUS2Hc3LZB2LUS2Hc3LZB2LUS2Hc3LZB2LUS3LZB2LU2TRS3LZB2LU2TRS3LZB2LU2TRS3LZB2LU2TRS3LZB2LU2TRS3LZB2LU2TRS3LZB2LU2TRS3LZB2LU2TRS2LO3GLO5SEP_F3HAP3LZB2LU4T1151K2FB2K13TDI4T1172TXS2LO3GLO5SEP_F3HAP3LZB2LU3TFR1K2FB2K1S3LZB2LU4T1152K33TDI1K4T1172TXS3LZB2LU4T1152K33TDI1K4T1172TX3TFRS3LZB2LU3TFR2K3S3LZB2LU3K2aS3LZB2LU3K2aS2LO3GLO5SEP_F3HAP3LZB2LU1KS2LO3GLO5SEP_F3HAP3LZB2LU1KS3LZB2LU2K21ES3LZB2LU2K21ES2LO3GLO5SEP_F3HAP3LZB2LU1KS2LO3GLO5SEP_F3HAP3LZB2LU1KS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3Hfl3LZB2LUS3Hfl3LZB2LUS3Hfl3LZB2LUS3Hfl3LZB2LUS3Hfl3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3HAP3LZB2LUS3HAP3LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3Hi43LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU".
replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (conv_type_cases _ _ CT) as CASES. pose proof (conv_type_range _ _ CT) as TR.
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    (* [comment removed for export] *)
    destruct a as [sv | iv | uv | dd];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l] ].
    (* [comment removed for export] *)
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    2: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    3: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    4: assert (TFP : conv_type (d_t d) = Some T_DBL) by (rewrite <- ETY; exact CT).
    4: pose proof (proj1 (conv_type_dbl _ TFP)) as TFR.
    3: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    (* [comment removed for export] *)
    all: ienter; zs; br K; zs; zs; zs; zs.
    all: callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL; lia]).
    all: idtac. (* [comment removed for export] *)
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi F_pop_arg.T_PTR F_pop_arg.T_INT F_pop_arg.T_UINT F_pop_arg.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    all: zsto 0x16f30%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a; zsto 0x16f44%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: zsto 0x16f54%Z; zs; br K3; zsto 0x16f68%Z.
    all: replace (Z.shiftl (d_t d + -65) 2 + 66764)%Z with (66764 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_fp _ _ M TFP) as RD1) ].
    all: zs; zs; zs.
    (* [comment removed for export] *)
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch pc with
      | 94220%Z => (* [comment removed for export] *)
          rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          match goal with MUc : munch _ m0 mm |- _ =>
            destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & SD5) end;
          stmt (HS_CV_S fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                 (xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SD1 | exact SD2 | exact SD3 | exact SD5
          | subst fl'; rewrite ?land_land_same; reflexivity ]
      | 94148%Z => (* [comment removed for export] *)
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
      | 94460%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_U fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv ]
      | 94580%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
      | 94068%Z => (* [comment removed for export] *)
          cbn [arg_ok] in AOK1; rewrite AOK1 in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          unfold LEFT_ADJ, ZERO_PAD in FPC1;
          first [ rewrite (proj2 (Z.eqb_eq _ _) K2) in FPC1 | rewrite (proj2 (Z.eqb_neq _ _) K2') in FPC1 ]; rewrite ?ift, ?iff in FPC1;
          stmt (HS_CV_FP fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (y := f128_of_d dd) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | subst fl'; exact FPC1 | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | apply f128_of_d_range | exact TFP ]
      end end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
