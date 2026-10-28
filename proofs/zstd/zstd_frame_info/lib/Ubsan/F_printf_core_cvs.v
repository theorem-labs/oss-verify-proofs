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

  Hypothesis HS_TAIL : S_TAIL.

  (* [comment removed for export] *)
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 SD5 E10.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
    Local Ltac2 Set LiaHints.tbl := fun () => "02V0?10105082325.16110105082325.1631163624459.162 11666457166.14211668961905.14411668962290.14411801586693.16111801586693.16311820177899.16311822584175.16212524393443.16212526607207.1631328334446.172 1328334446.176 14341690004.16216252485563.13916886332493.16318761041880.15919042827563.16919042827563.17220667246060.17220667246060.17621250035837.16121250035837.16321287759467.16321290198767.16221483424549.16221485634465.16322638612785.16323077509607.17123077509607.1752307889141.163 2309513073.162 23145753735.17023145753735.17323191472327.16323193845827.16223417445761.1632460623706.160 2460623706.162 2583290783.163 25905074567.16025905074567.16226131081623.16326313435160.17026313435160.17327060081109.16127060081109.16327474226815.16327475879675.16228908644622.14228922925361.14429258395259.15830101911539.16330351702510.17230351702510.17631165778545.14431165778672.16132410872973.16333263823594.17233263823594.17633928676191.16933928676191.17334305264110.17234305264110.17635827935646.17035827935646.17336194455448.17036194455448.17336297774975.16236299857915.16337631032481.16937631032481.1733849932509.161 3849932509.163 39047133539.17239047133539.1763942199251.167 3942199251.170 40457137823.13940825907496.1584105703320.170 4105703320.173 4113535334.143 41860256368.16343100747103.16343638561891.16344284318572.16144284318572.16344484923210.16144484923210.163445078394.170  445078394.173  4606055276.161 4606055276.163 46386664472.17046386664472.17346898303580.16446898303580.16547917741756.17247917741756.17648881857403.16248883710975.16349376477044.16349378949104.16251184819047.16351678946857.16351680767661.16251721469139.16851721469139.17151792577165.16251794659849.16353199507948.16253595873814.15853595873814.16054121776830.17254121776830.17654429404910.15855223871902.17055223871902.17355537228055.17055537228055.17255537228055.17355537228055.17656368271429.16256369895617.16356867836477.16256869624505.16357897851615.17057897851615.17458665690269.16758665690269.17058963326956.13659308628179.14459308628433.161594016748.172  594016748.176  59650130105.14459652110470.14259959107129.14061756489387.16361993915987.16262438234458.17062438234458.17363053735762.16265227213690.17065227213690.17366201836243.15566388384015.14466402672944.14266829496233.16366831968045.16267281204924.17267281204924.17668360121726.16268362135034.16368500806127.14368500806127.16468585761514.17268585761514.1767355949818.170 7355949818.173 7781616920.163 7783957916.162 9855713917.161 9855713917.163 00001102202G02]03303M03\03k04>04Q04R04S04b05105F05U05V05e06806K06a07707M07c07d07e08708I08J08]0900:C0;P0<Q0=R0=S0=T0=U0>V0?W0?l0@m0An0Ao0BE0B[0Bn0CA0CB0CC0CR0Ca0D60DK0DZ0Di0E;0EM0EN0Eg0F@0FO0F^0Fm0G<0GS0Gj0Hk0Il0J;0JJ0JY0Jh0Ji0Jj0Kk0Ll0M;0MJ0M]0Ml0N?0NR0Nd0O90OL0Od0P=0PV0PW0PX0Pg0Q60QM0Qd0R:0RP0R_0Rn0So0U00U10U20U30U40U50UL0Uc0V50VG0VY0Vk0W>0WM0W\0X]0Y^0Ym0ZF0Z_0[10[C0[U0[g0\:0\M0\_0]10]C0]U0]d0^30^>0^S0^h0_>0_T0`U0aV0ai0b;0bJ0cK0dL0eO0e^0em0f<0fP0fd0fe0ff0g90gL0g[0gj0h;0hL0hc0i:0iI0iX0ig0j60jL0jbS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZS5SMALLS2P03SD53LZB2LU2SB3LZSS2P03SD53LZB2LU2SB3LZSS2P03SD53LZB2LU2SB3LSB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3Hi43LZB2LU2SB3LZSS3Hi43LZB2LU2SB3LZSFFS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZS2K1S3LZB2LU2SB3LZSFS3LZB2LU2SB3LZSS3QHI3LZB2LU2SB3LZSS3QHI3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSFFS2Hw3LZB2LU2SB3LZSS2Hw3LZB2LU2SB3LZSFS3QHI3LZB2LU2SB3LZSS3QHI3LZB2LU2SB3LZSS2LO3GLO3QHI5SEP_F5SEP_B3HAP3BS02Hp4SPAD2P03SD13SD23SD33SD53LZB2LU2SB3LSB3LZS2K02K1S2LO3GLO3QHI5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33SD53LZB2LU2SB3LSB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0FFFS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZS2K12HpS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0FS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSFFS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZS5SMALLS2Hp3LZB2LU2SB3LZS2K1S3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSFS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSFFS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3Hfl3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZS2K1S3SD53LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZS2K12LFS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSFFS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0FFFFFS3Hfl3LZB2LU2SB3LZS3FLBS3Hfl3LZB2LU2SB3LZS3FLBS3LZB2LU2SB3LZS2HBS3LZB2LU2SB3LZS2HBS2Hk3LZB2LU2SB3LZSS2Hk3LZB2LU2SB3LZSS3SD53LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS3E103LZB2LU2SB3LZSS3E103LZB2LU2SB3LZSS2Hc3LZB2LU2SB3LZSS2Hc3LZB2LU2SB3LZSS3LZB2LU2SB3LZS2HBS3LZB2LU2SB3LZS2HBS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SBS2P03LZB2LU2SB3LZS2K0S2Hp3LZB2LU2SB3LZS2K2S2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3Hfl3LZB2LU2SB3LZSS3LZB2LU2SB3LZS2LFS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K05SMALLS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSFFS3HAP3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZS1HS3LZB2LU2SB3LZS1HS3HAP3HVA3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZS".
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
      by (rewrite length_app, zb_length; cbn [length]; lia).
    pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
    pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
    assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
    { intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
    stmt (HS_TAIL fuel HH) as NX.
    set (len := Z.of_nat (length s)) in *.
    unfold ZERO_PAD.
    ienter.
    zs. zs. brf K0; [|exfalso; lia].
    destruct XP as [[-> ->] | [-> Hp]].
    - (* [comment removed for export] *)
      cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
      destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
      rewrite ?ift, ?iff.
      zs. zs. if_lit. zs. zs. zs.
      callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z);
        [ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
        | rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia ]).
      rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
      match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
      zs. zs. if_lit.
      assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read usegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
      zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
      match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
      lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at usegs mm P (zb s)) end.
      { pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
      rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 66200%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
        | unfold body_loc; zl | zl | unfold INT_MAX; zl
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
    - (* [comment removed for export] *)
      replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
      zs. zs. brf K1; [ | zs ].
      (* [comment removed for export] *)
      all: zs; zs.
      all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack);
        [ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
        | rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia ]).
      all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
      all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
      all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
      all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at usegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
        by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
      all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
      all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 66200%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact SUB | apply BRNG
        | unfold body_loc; rewrite LF; lia | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
