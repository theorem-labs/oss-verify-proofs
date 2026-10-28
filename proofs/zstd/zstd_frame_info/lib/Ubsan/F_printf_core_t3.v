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

  Hypothesis HS_T4 : S_T4.

  (* [comment removed for export] *)
  Lemma L_T3 : S_T3.
  Proof using BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
    intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 65536) by reflexivity.
    ienter. zs. zs. Local Ltac2 Set LiaHints.tbl := fun () => "01E0?10726435770.14511100592950.14611801586693.16711801586693.1681221268319.189 1221268319.190 13016802789.16913322526622.14515857370701.18817464659307.14919059271977.18821250035837.16721666894615.1562191606306.169 22150231227.14622940829882.14522940829882.14622940829882.18623193536501.1462366355075.167 2381018386.169 24356466485.16924810027088.14826201089273.18926384366147.14626426490254.18927060081109.16827476353357.14628319366542.1893119449143.149 32412935103.14633481511548.17136301394489.14536301394489.14636301394489.18636679908750.18937539786313.14737980601037.16838672651116.16839204460529.18942006909334.16444284318572.16844484923210.1674451234041.145 44897891915.14545661595064.1644606055276.168 47010499447.14947012739271.16947023242070.18647202075499.14947968598982.14648059063793.18948881644749.14649512169481.19050122415005.18750173493704.18950503057404.16951155802787.15651792528699.18654139525278.14656781706523.17859308628566.14859308628695.16559308628820.16959576979761.1446356423510.165 6356423639.148 6356423639.149 63696756947.15163696756947.15564305442815.14564305442815.14664305442815.18665887914963.17666039000849.16966049535104.16767539865398.16968346602151.16968388294051.14568388294051.14668388294051.1869261986838.186 9855713917.167 990943913.189  00000Q00R00c01101g01h02@02a02b03>03m04E04l05>05O05`06106B06C07507g08508I09809909l0:D0:E0;90;G0;H0;\0;n0<@0<U0=G0=n0=o0>f0?N0?\0@70@E0@Z0@o0A=0AY0An0BC0BX0C40C50Cd0Ce0D30DG0DH0DY0E:0EK0EL0EZ0F00FD0G90GG0G_0HF0H^0Hl0I:0IL0I^0J00J>0K00Kb0L00LH0LY0Lj0M;0MI0Ma0MbS4Hplp2Hc2Hw3Hwq3Hcw3LZB2LU2LB2LPFS3LZB2LU2LB2LP2K3S3LZB2LU2LB2LPS2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K22K43HwqFS2LO3GLO3LZB2LU2LB2LP2K2S2Hn3Hpl3Hnp4Hplp2Hw3LZB2LU2LB2LPFS2LO3GLO3QHI3LZB2LU2LB2LP2K2S2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K2S2LO3GLO3LZB2LU2LB2LP2K2S2Hn3Hpl3Hnp2Hc3Hwq3Hcw3LZB2LU2LB2LP2K2S3QHI3LZB2LU2LB2LPS3LZB2LU2LB2LP2K1S2Hw3LZB2LU2LB2LPS2Hw3LZB2LU2LB2LPS2Hw3LZB2LU2LB2LPFS2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K22K3S2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K22K4S3LZB2LU2LB2LPS3LZB2LU2LB2LP2K22K3S2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K2FS2LO3GLO5SEP_F5SEP_B3HAP3HVA3BS02Hn3LZB2LU2LB2LP2K2S3HAP3LZB2LU2LB2LP2K22K3FS2LO3GLO5SEP_F5SEP_B3HAP3BS04BLOC2Hn3LZB2LU2LB2LP2K2S3LZB2LU2LB2LPFS3LZB2LU2LB2LP2K22HyS3Hwq3LZB2LU2LB2LPS3Hwq3LZB2LU2LB2LPS3Hwq3LZB2LU2LB2LP2K2S2LO3GLO2HA5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K2S2Hn3Hpl3Hnp2Hc3Hwq3Hcw3LZB2LU2LB2LP2K2FS2LO3GLO5SEP_F5SEP_B3HAP3BS04BLOC2Hn3LZB2LU2LB2LP2K22K3S2LO3GLO5SEP_F5SEP_B3HAP3LZB2LU2LB2LP2K2S3LZB2LU2LB2LPS2LO3GLO2HA3LZB2LU2LB2LP2K2S3LZB2LU2LB2LPS3Hwq3LZB2LU2LB2LP2K2S3Hwq3LZB2LU2LB2LP2K2S3LZB2LU2LB2LPS3HAP3HVA3LZB2LU2LB2LP2K22K3S3Hwq3LZB2LU2LB2LP2K2S3Hwq3LZB2LU2LB2LP2K2S3Hwq3LZB2LU2LB2LP2K2S2LO3GLO3QHI3LZB2LU2LB2LP2K2FS2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K2FS3LZB2LU2LB2LPS3LZB2LU2LB2LP2K22K4FS3LZB2LU2LB2LP2K3S2Hn3Hpl3Hnp4Hplp3LZB2LU2LB2LP2K2S2Hk3LZB2LU2LB2LPFS3LZB2LU2LB2LPS3LZB2LU2LB2LP4N2562K3S3LZB2LU2LB2LP2K32K4S2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K22FB2K5S3LZB2LU2LB2LPS3Hwq3LZB2LU2LB2LP2K22K3S2Hn3Hpl3Hnp2Hc3Hwq3Hcw3LZB2LU2LB2LP2K2S3Hwq3LZB2LU2LB2LP2K22K3S3LZB2LU2LB2LPS3LZB2LU2LB2LPS3Hcw3LZB2LU2LB2LPS3Hcw3LZB2LU2LB2LPS3Hcw3LZB2LU2LB2LPS3LZB2LU2LB2LPS2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K22K4S2LO3GLO5SEP_F5SEP_B3HAP3BS02Hn3LZB2LU2LB2LP2K22K3S3LZB2LU2LB2LPS3QHI3LZB2LU2LB2LP2K22K4S2Hc3LZB2LU2LB2LPS2Hc3LZB2LU2LB2LPS2Hc3LZB2LU2LB2LPS3LZB2LU2LB2LPS2LO3GLO3LZB2LU2LB2LP2K2F".
brf K1.
    - (* [comment removed for export] *)
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
        apply (rw_cells_split_CB usegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
        cbn [mk_CB_cells app] in PAD.
        apply (proj1 (rw_cells_app usegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
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
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }   (* [comment removed for export] *)
        match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
        match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
          assert (PAD : rw_cells usegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
          | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
            replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
        end.
        stmt (HS_T4 fuel HH) as NX4.
        jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
          [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
