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

  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_CONV : S_CONV.
  Hypothesis HS_END : S_END.

  (* [comment removed for export] *)
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI.
    induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
        FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
    { cbn [printf_loop]. apply implM_unr. }
    rewrite printf_loop_S. rewrite fp_calls_S in FPC.
    destruct (sfx i) as [|c s'] eqn:Es. { apply implM_unr. }
    destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    Local Ltac2 Set LiaHints.tbl := fun () => "02V0?10351558129.15810351558129.16310353723845.18911409396336.13711409396336.15511409396336.1601221268319.184 1221268319.185 1221268319.189 1221268319.190 13581894921.18513581894921.19013755488006.16413947147674.15815045133826.16315329670979.15315857370701.18315857370701.18816888394563.18417509446421.13717509446421.15517509446421.16018510977946.14618510977946.14918510977946.16418510977946.16718510977946.16918510977946.17219059271977.18319059271977.18819512137968.13419522540244.13719522540244.15519522540244.16019524751568.13919524751568.15719524751568.16219524752989.13819524752989.15619524752989.16121287064598.18221287064598.18721793880841.16421793880841.16922520717061.15822520717061.16322520769325.14022638504455.15822638504455.16322638583343.14022640680511.18422934309245.16922946084415.18923409711806.1642424904544.158 2426957656.184 24356466096.16524356466096.17024471108001.15824480122789.15824480122789.16325216032964.16925309805616.18425316131910.15525373012370.19925375016359.15825375016359.16325375109519.14025774904127.16326201089273.18426201089273.18926426490254.18526426490254.19027025541745.16127025541745.16627382584830.18427474171209.15827474171209.16327474256225.14027476353393.18427671308048.16928086201690.16428310633487.16432410837907.14032410916795.15832410916795.16332412935043.18434713230823.16436679908750.18536679908750.1903823480469.137 3823480469.155 3823480469.160 39204460529.18439204460529.18939818012962.15839818012962.16339818091786.14040448778119.16941344150998.14241344150998.16041344150998.16541344151002.14941344151002.16741344151002.17242432537837.16443091564065.18443613691756.18443613783124.14644139670747.16948059063793.18448059063793.18948881644785.18448883741921.14048883810505.15848883810505.16350173493704.18450173493704.18951184850041.14051184902225.15851184902225.16351792528647.18451792528650.19952851042612.13952851042612.15752851042612.16252853254960.13752853254960.15552853254960.16053704195668.16453704195668.16955345847750.15855345847750.16356344221874.14056344308890.15856344308890.16356745901367.14256781706523.17456781706523.17959308628179.15859308628179.16359308628304.16159308628304.16659308628433.16559308628433.17059308628566.18359308628566.18859314923118.13759314923118.15559314923118.16060104616754.14061929812503.18362518870618.15263971019882.18465567375239.19966350173012.13966350173012.15766350173012.16266804659468.16366979109500.19967029330540.18467137693457.1847095521617.165 7519430433.164 990943913.184  990943913.189  00000;00F00Q00e01>01W02D02E03903:03B03J03d04104904H04I04J04K04_05805Q05e06706P06g07@07W08>08e09509E09U09e0:50:E0:U0:e0;50;E0;M0;U0;h0<;0<<0<=0<>0<?0<@0<A0<B0<R0<_0=70=D0=Q0=Y0=a0=m0=n0=o0>Y0>Z0>b0?;0?T0?m0@A0@N0A;0Ah0BY0CJ0D30D\0Dd0De0Df0Dg0Dh0E<0Ej0FC0FD0FE0FF0FG0F[0GK0H;0HO0Hh0IA0In0J[0Jc0Jk0K30Kc0L70LP0Li0M;0MR0Mi0N]0N^0O30OC0OK0P80Pe0Pf0Pg0Ph0Pi0Pj0Pk0Pl0Pm0Pn0Q90QD0QV0Qm0RD0RX0S10SJ0SZ0Sj0T=0TQ0TR0TS0TT0T\0Td0Tl0U?0UV0V=0Vd0WQ0XE0XU0X`0Xn0Y<0YJ0YK0Yj0Z:0Z;0ZO0Zc0[<0[U0[a0[m0\:0\O0\Z0\j0\k0\lS2Hi3LZB2LUS2Hi3LZB2LUS2Hi3LZB2LUS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1FS2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K12Ec3C37FS3LZB2LUS3LZB2LUS2HA2A02Hi4Hilt3LZB2LU3HinS3LZB2LU4HnclS3LZB2LUS2Nz3LZB2LU3Hn0FFFS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3LZB2LU1KS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl4Hilt3LZB2LU1KS2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2C02K02K1S2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS3LZB2LUS3LZB2LUS2A02Hi4Hilt3LZB2LUS2A02Hi4Hilt3LZB2LUFFFFFFFS2HA4Hilt3LZB2LUS4Hilt3LZB2LUS3GLO2HA4Hilt3LZB2LU3HinS4Npos3LZB2LUS4Npos3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3HinFFS2LO3GLO2HA5SEP_F3HAP4Hilt3LZB2LU2C02K02K1FS3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl3LZB2LUS4Hilt3LZB2LUS2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F5SEP_B3HAP3HVA4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F5SEP_B3HAP3HVA4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F3HAP4VAHI4Hilt3LZB2LU2C02K0S2LO3GLO5SEP_F3HAP4VAHI4Hilt3LZB2LU2C02K0S3LZB2LUFFFFS3GLO2HA4Hilt3LZB2LUS2LO3GLO2HA5SEP_F3HAP4Hilt3LZB2LU2C03Hin2K02K1S4Npos2Hi4Hilt3LZB2LU3HinFFFFS2HA4Hilt3LZB2LU3HinS2LO3GLO2HA5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO2HA5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO2HA5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS2LO3GLO2HA5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C03Hin2K02K1FS4Npos2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS3LZB2LUS2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F5SEP_B3HAP4Hilt3LZB2LU2C02K02K1FFFFFFFFFS2Hk3LZB2LUS2Hk3LZB2LUS4Hcnt2Hl3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS2HA4Hilt3LZB2LUS2HA4Hilt3LZB2LUS4Hilt2Ec3LZB2LU2RGS4Hilt2Ec3LZB2LU3C37FFFS3LZB2LUS3LZB2LUS3LZB2LUS4Hilt3LZB2LU2C02K0S4Hilt2Ec3LZB2LU3C372K0S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2C02K02K1S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2C02K02K12FB2K2S2LO3GLO5SEP_F3HAP4Hilt2Ec3LZB2LU2C03C372K02K12FB2K2S4Npos3LZB2LU2K3S3LZB2LU2K3S3Hcl3LZB2LU1KS3Hcl3LZB2LU1KS3Hcl3LZB2LU1KFS2HA2A04Npos2Hi4Hilt3LZB2LU3HinS2Hi4Hilt3LZB2LUFS2Hi4Hilt3LZB2LU3Hk4S4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS3Hcl3LZB2LUS3LZB2LU3HflS3LZB2LU4HnclS4Hcnt2Hl4Hilt3LZB2LUS3LZB2LU2HjS2Hi4Hilt3LZB2LUFF".
pose proof (fmt_rng i ltac:(zl)) as RGi.
    destruct (Z.eqb_spec c 0) as [C0|C0].
    { (* [comment removed for export] *)
      apply implM_ret.
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
      stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
    rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
    pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
    rewrite Hs1. rewrite Hs1 in FPC.
    assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
    destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implM_unr. }
    destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implM_unr|] end.
    (* [comment removed for export] *)
    assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
    { pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
      destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
      rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
    stmt HS_SCAN as NXS.
    destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implM_unr|].
      ienter.
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. br K1.
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI.
        - rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
        - rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
        - unfold n, zlength. reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. - zl. (* [comment removed for export] *) }
      cbv beta. intros [] st'. post_call usegs m. rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 93044)) with (Z_to_bv 64 93044) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. br K3.
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
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. br K1.
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI.
        - apply bytes_at_nil; zl.
        - constructor.
        - reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia.
        - change (zlength (@nil Z)) with 0%Z; zl. (* [comment removed for export] *) }
      cbv beta. intros [] st'. post_call usegs m. rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 93044)) with (Z_to_bv 64 93044) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. br K3.
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
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
