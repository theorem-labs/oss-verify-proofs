(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require F_printf_core_exit F_printf_core_end F_printf_core_exit1 F_printf_core_scan F_printf_core_flags F_printf_core_width F_printf_core_prec F_printf_core_state F_printf_core_dir F_printf_core_t6 F_printf_core_t5 F_printf_core_t4 F_printf_core_t3 F_printf_core_t2 F_printf_core_t1 F_printf_core_tail F_printf_core_intc2 F_printf_core_intc F_printf_core_dloop F_printf_core_fmtu2 F_printf_core_fmtu F_printf_core_cvd F_printf_core_cvu F_printf_core_xloop F_printf_core_cvx F_printf_core_cvs F_printf_core_cvfp F_printf_core_conv F_printf_core_head F_printf_core_p1 F_printf_core_pro.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Export F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
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
Hypothesis QHI : (q < 2^47)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.
Hypothesis HA : (A + zlength fmt <= 118784)%Z.
Hypothesis SEP_F : ((121784 <= Fp /\ Fp + 232 <= 324000) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((324008 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.
Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
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
Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Notation FPv := (Z_to_bv 64 Fp).
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
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
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
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
first [ apply F_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
| intros; eapply F_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
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
first [ apply F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
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
first [ apply F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
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
first [ intro; apply F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
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
SINK m0 st -> stk usegs m0 lo q -> mem_inv usegs m0 -> bytes_at usegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
rw_cells usegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
(0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
implM usegs (printf_model OUT OUTFP fmt args) st POST
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0x17920) fc0 None m0 (seg_rom usegs)).
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
assert (APC : rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
{ eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
stmt (HS_HEAD (length fmt)) as NXH.
jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
[ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
let _ := ctx_all in
stk usegs m0 lo q -> mem_inv usegs m0 -> bytes_at usegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
pass1_ok fmt = true ->
evt usegs (POST1 0)
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0x17920) fc0 None m0 (seg_rom usegs)).
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
{ Local Ltac2 Set LiaHints.tbl := fun () => "0020>55666027475.7963249344829.7900000A00LS2LO3GLO4SEPF3HAPS4SEPF4VAHI".
apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
rewrite Z_to_bv_bv_unsigned.
repeat (split; [assumption || reflexivity|]). exact Hr.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Theorem printf_core1_proof : printf_core1_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>15047389056.5042150813125.5043568463539.5146906054063.5047483984168.5163117987568.5067964195078.5000000100600<00=00B00F00GSS3GLOS4A2HISS3Ra2S2LOS".
pose proof (L_CORE1 121784 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
