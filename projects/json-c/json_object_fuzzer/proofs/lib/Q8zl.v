(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp QvDJ Qu3b QnRU QteI QoBx Qs9x QC9y QcfN QQNJ QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho QFd5 QYyZ QpzM Q0z1 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp QvDJ.Mq3.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QTVW.Mq2 QnRU.Mq5 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QoBx Qu3b.Mq0.
Import Qs9x QC9y QcfN.Mq0.
Import QQNJ.Mq1.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QFd5.Mq0 QYyZ.Mq1 QteI.Mq2.

Export QpzM.Mq1.
Import Q0z1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {BAND : Band}.
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
Hypothesis QHI : (q + 16 <= 140737488355328)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 143488)%Z /\ szone A (Z.of_nat (length fmt)).

Hypothesis SEP_F : ((945072 <= Fp /\ Fp + 232 <= 6565536) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6566104 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation ctx_all := (QpzM.Mq1.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (QpzM.Mq1.W Fp B BS q lo AP).
Local Notation Fok_refl := (QpzM.Mq1.Fok_refl F).
Local Notation POST := (QpzM.Mq1.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (QpzM.Mq1.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (QpzM.Mq1.lo_cells AP nla nlt).
Local Notation finv := (QpzM.Mq1.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (QpzM.Mq1.fmt_rng fmt HF).
Local Notation implM_eq_ms := (QpzM.Mq1.implM_eq_ms (St:=St)).
Local Notation sink_store := (QpzM.Mq1.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (QpzM.Mq1.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (QpzM.Mq1.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (QpzM.Mq1.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (QpzM.Mq1.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (QpzM.Mq1.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (QpzM.Mq1.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (QpzM.Mq1.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (QpzM.Mq1.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (QpzM.Mq1.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (QpzM.Mq1.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (QpzM.Mq1.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (QpzM.Mq1.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (QpzM.Mq1.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (QpzM.Mq1.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (QpzM.Mq1.body_loc Fp B BS q lo).
Local Notation S_TAIL := (QpzM.Mq1.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QpzM.Mq1.tregs Fp q gp tp A).
Local Notation tinv := (QpzM.Mq1.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (QpzM.Mq1.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (QpzM.Mq1.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (QpzM.Mq1.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (QpzM.Mq1.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (QpzM.Mq1.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (QpzM.Mq1.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (QpzM.Mq1.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (QpzM.Mq1.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (QpzM.Mq1.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (QpzM.Mq1.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (QpzM.Mq1.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (QpzM.Mq1.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (QpzM.Mq1.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (QpzM.Mq1.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (QpzM.Mq1.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (QpzM.Mq1.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (QpzM.Mq1.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (QpzM.Mq1.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (QpzM.Mq1.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (QpzM.Mq1.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (QpzM.Mq1.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation FPv := (Z_to_bv 64 Fp).
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
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia | glo_lia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; glo_lia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].

Lemma L_EXIT : S_EXIT.
Proof using LO BAND.
first [ apply QpzM.Mq1.L_EXIT; first [eassumption]
| intros; eapply QpzM.Mq1.L_EXIT; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_END : S_END.
Proof using GLO HAP LO SEP_F VAHI BAND.
first [ apply QpzM.Mq1.L_END; first [eassumption | eexact L_EXIT]
| intros; eapply QpzM.Mq1.L_END; first [eassumption | eexact L_EXIT] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_EXIT1 : S_EXIT1.
Proof using LO BAND.
first [ apply QpzM.Mq1.L_EXIT1; first [eassumption]
| intros; eapply QpzM.Mq1.L_EXIT1; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF BAND.
first [ apply QpzM.Mq1.L_SCAN; first [eassumption]
| intros; eapply QpzM.Mq1.L_SCAN; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FLAGS : S_FLAGS.
Proof using HF BAND.
first [ apply QpzM.Mq1.L_FLAGS; first [eassumption]
| intros; eapply QpzM.Mq1.L_FLAGS; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WLOOP : S_WLOOP.
Proof using HF BAND.
first [ apply QpzM.Mq1.L_WLOOP; first [eassumption]
| intros; eapply QpzM.Mq1.L_WLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF BAND.
first [ intro; apply QpzM.Mq1.L_WIDTH; first [eassumption]
| intros; eapply QpzM.Mq1.L_WIDTH; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PLOOP : S_PLOOP.
Proof using HF BAND.
first [ apply QpzM.Mq1.L_PLOOP; first [eassumption]
| intros; eapply QpzM.Mq1.L_PLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF BAND.
first [ intro; apply QpzM.Mq1.L_PREC; first [eassumption]
| intros; eapply QpzM.Mq1.L_PREC; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATE : S_STATE.
Proof using HF BAND.
first [ apply QpzM.Mq1.L_STATE; first [eassumption]
| intros; eapply QpzM.Mq1.L_STATE; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DIR : S_DIR.
Proof using HF BAND.
first [ apply QpzM.Mq1.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
| intros; eapply QpzM.Mq1.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
first [ apply QpzM.Mq1.L_T6; first [eassumption]
| intros; eapply QpzM.Mq1.L_T6; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_T5; first [eassumption | eexact L_T6]
| intros; eapply QpzM.Mq1.L_T5; first [eassumption | eexact L_T6] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_T4; first [eassumption | eexact L_T5]
| intros; eapply QpzM.Mq1.L_T4; first [eassumption | eexact L_T5] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_T3; first [eassumption | eexact L_T4]
| intros; eapply QpzM.Mq1.L_T3; first [eassumption | eexact L_T4] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_T2; first [eassumption | eexact L_T3]
| intros; eapply QpzM.Mq1.L_T2; first [eassumption | eexact L_T3] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_T1; first [eassumption | eexact L_T2]
| intros; eapply QpzM.Mq1.L_T1; first [eassumption | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply QpzM.Mq1.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC2 : S_INTC2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_INTC2; first [eassumption | eexact L_TAIL]
| intros; eapply QpzM.Mq1.L_INTC2; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC : S_INTC.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_INTC; first [eassumption | eexact L_INTC2]
| intros; eapply QpzM.Mq1.L_INTC; first [eassumption | eexact L_INTC2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI BAND.
first [ apply QpzM.Mq1.L_DLOOP; first [eassumption]
| intros; eapply QpzM.Mq1.L_DLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_FMTU2; first [eassumption | eexact L_INTC]
| intros; eapply QpzM.Mq1.L_FMTU2; first [eassumption | eexact L_INTC] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
| intros; eapply QpzM.Mq1.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_CV_D; first [eassumption | eexact L_FMTU]
| intros; eapply QpzM.Mq1.L_CV_D; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_U : S_CV_U.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_CV_U; first [eassumption | eexact L_FMTU]
| intros; eapply QpzM.Mq1.L_CV_U; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI BAND.
first [ apply QpzM.Mq1.L_XLOOP; first [eassumption]
| intros; eapply QpzM.Mq1.L_XLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
| intros; eapply QpzM.Mq1.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply QpzM.Mq1.L_CV_S; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ BAND BS0.
first [ apply QpzM.Mq1.L_CV_FP; first [eassumption]
| intros; eapply QpzM.Mq1.L_CV_FP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mq1.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP]
| intros; eapply QpzM.Mq1.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ intro; apply QpzM.Mq1.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply QpzM.Mq1.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_P1 : S_P1.
Proof using A0 HA HF LO BAND.
first [ apply QpzM.Mq1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
| intros; eapply QpzM.Mq1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F BAND.
first [ apply QpzM.Mq1.L_PRO; first [eassumption]
| intros; eapply QpzM.Mq1.L_PRO; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.

Let HS_PRO := L_PRO.
Let HS_HEAD := L_HEAD.
Let HS_P1 := L_P1.

Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
let _ := ctx_all in
SINK m0 st -> stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
rw_cells asegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
(0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
implM asegs (printf_model OUT OUTFP fmt args) st POST
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd3a0c) fc0 None m0 (seg_rom asegs)).
Proof using FRM0 HS_HEAD HS_PRO BAND.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
unfold printf_model. ienter.
stmt HS_PRO as NXP.
eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
assert (HS : SINK m st).
{ eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; glo_lia | apply Forall_nil]). }
assert (APC : rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
{ eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
stmt (HS_HEAD (length fmt)) as NXH.
jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
[ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
let _ := ctx_all in
stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
pass1_ok fmt = true ->
evt asegs (POST1 0)
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd3a0c) fc0 None m0 (seg_rom asegs)).
Proof using HS_P1 HS_PRO BAND.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
stmt HS_PRO as NXP.
eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
stmt HS_P1 as NX1.
jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
Qed.

End PrintfCore.

Theorem printf_core_proof {BAND : Band} : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof.
intros St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA HSZ BS0 SEPF SEPB HAP HVA VAHI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
pose proof (L_CORE2 Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
(bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM (conj HA HSZ) SEPF SEPB HAP HVA (proj1 Ra1) VAHI BS0
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

Theorem printf_core1_proof {BAND : Band} : printf_core1_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HSZ HAP A2HI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
pose proof (L_CORE1 945072 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
(bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; exact GLO ) SPHI (conj HA HSZ) ltac:(lia) HAP ltac:(lia) (proj1 Ra1) ltac:(lia)
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
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Qa5v.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QTVW.Mq5. Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0 QQNJ.Mq1 QpzM.Mqc Qa5v.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Ltac ifT := unfold_cond; cond_unsig; if_true.
Ltac ifF := unfold_cond; cond_unsig; if_false.

Definition fwrite_stub : Z := 0x4f980.
Definition fwrite_icpt_entry : Z := 0x529d8.
Definition FWRITE_ICPT_DEPTH : Z := 2128 + FWRITE_DEPTH.

Lemma stderr_wfile0_munch : forall m m' W, stderr_wfile0 m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= RSTDERR \/ RSTDERR + 232 <= fst iv) W -> stderr_wfile0 m'.
Proof.
intros m m' W (flags & mode & e & wend & tail & FC & FL & WE & HE) MU WM HW.
exists flags, mode, e, wend, tail. split; [| split; [exact FL| split; [exact WE| exact HE]]].
eapply rw_cells_apart; [exact FC| exact MU| exact WM|].
eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold file_cells in *. cbn [cells_size csize length Nat.add Nat.mul fst snd] in *. lia.
Qed.

Lemma ssp_cells_munch : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Section Fwrite.
Context {BAND : Band}.
Context {St : Type}.

Definition fwrite_icpt_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
towrite_stmt ->
stderr_wfile0 m ->
bytes_at asegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s <= OUT_MAX ->
a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_ICPT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
ssp_cells m canary -> mem_inv asegs m ->
ISH m -> szone (bv_unsigned a0) (zlength s) ->
(bv_unsigned sp <= 2^47) ->
implM asegs (stderr_fwrite s : M St unit) st
(fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fwrite_stub) fc None m (seg_rom asegs)).

Theorem fwrite_icpt_proof : fwrite_diag_stmt (St:=St) -> fwrite_icpt_stmt.
Proof.
intros FWR. unfold fwrite_icpt_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SEPS1 SEPS2 SSP MI ISH0 SZ SPT.
pose proof GLO as CEIL'. unfold GLOBALS_TOP in CEIL'. unfold FWRITE_ICPT_DEPTH, FWRITE_DEPTH in LO.
assert (CEIL : band_lo <= lo) by (idtac; exact CEIL').
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold zb in BS. rewrite length_map in BS.
pose proof LS as LS'. unfold zlength in LS'.
set (S := bv_unsigned a0) in *. assert (ES : S = bv_unsigned a0) by reflexivity. clearbody S.
assert (EA0 : a0 = wz S) by (rewrite ES; symmetry; apply Z_to_bv_bv_unsigned). rewrite EA0. clear ES EA0.
pose proof ISH0 as (ASH & RC & SB).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
set (BAh := bytes_at) in SRC.
eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.
unfold fwrite_stub. step.
carve_frame 56%nat ST.
do 8 istep.
step. step. step. step. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof RCc as RCc'. pose proof (rt_159bb8 _ RCc) as K16. pose proof (rt_161720 _ RCc) as K18. clear RCc.
step. call_u tryinit_spec7; [exact K18| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => rename H into ST1' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
step. stp. step. step. step. step. step. clear K16 K18 RCc'.

step. apply evt_done.
assert (W0A : stderr_wfile0 mA) by (eapply stderr_wfile0_munch; [exact W0| exact MUs| exact WM| zforalls]).
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (SRCA : bytes_at asegs mA S (zb s)) by (subst BAh; eapply bytes_at_transport; [exact SRC| exact MUs| cbn [disjoint_from]; unfold zb; rewrite length_map; unfold zlength in *; lia]).
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
clear W0 SSP SRC.
eapply implM_post_evt''.
{ eapply (FWR _ _ _ _ _ _ _ _ _ (wz S)) with (lo := lo) (s := s); try reflexivity;
[ exact TW| exact W0A| unsigned_lits; exact SRCA| exact BYT| exact LS| unsigned_lits; exact ST1'
| unsigned_lits; unfold FWRITE_DEPTH; lia| exact GLO| unsigned_lits; lia| unsigned_lits; exact SEPS2| exact SSPA| assumption
| unsigned_lits; lia | unsigned_lits; unfold szone in SZ; lia  ]. }
cbv beta. intros [] st2 ms2 PO.
destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST3 & W02 & SSP2 & ->).
unsigned_lits_in MU2. unsigned_lits_in ST3.
replace (ret_pc (wz 0x52a34)) with (wz 0x52a34) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. lia. }
assert (ST4 : stk asegs m2 (bv_unsigned sp + -2128) (bv_unsigned sp + -56)).
{ eapply stk_transport; [exact ST2| exact MU2| exact WM2|]. cbn. lia. }
assert (ISH2 : ISH m2) by (eapply ISH_munch_zone; [exact ISHA| exact MU2| exact WM2| zforalls]).
clear FR ST2 ISHA W0A SSPA SRCA.
pose proof ISH2 as (ASH2 & RC2 & SB2).
pose proof (rng_ok_of_ash _ _ _ ASH2 SZ ltac:(lia)) as RNG. pose proof RNG as (_ & S47 & SOK & BIG & NB).

assert (MU : munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m2).
{ apply (munch_trans _ m mA m2).
- eapply munch_weaken; [| exact MUs]. unfold sub_fp; cbn; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn; intros; lia. }
pose proof (wmono_trans asegs _ _ _ WM WM2) as WMf. clear MUs MU2 WM WM2.

step. ifF. step. ifF. stp.
match goal with |- context [wz (1 * ?x)] => replace (1 * x) with x by lia | _ => idtac end.
rewrite ?(unsigned_lit (zlength s)) by lia.

step. step. step. step. rewrite (unsigned_lit S), zb_lxor_ones by lia. ifF.

step. step. step.
destruct (Z_le_gt_dec (zlength s) 64) as [N64|N65].
- unfold_cond. fold_lit_ux. rewrite u_nm65 by lia.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (symmetry; apply (proj2 (Bool.negb_false_iff _)); apply Z.ltb_lt; clear - N64 LS; lia) end.
cbv iota.
destruct (NB ltac:(lia)) as [[w1 W1] [w2 W2]]. pose proof (SOK ltac:(lia)) as SO2.
destruct SB2 as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. step. step. step. stp. stp.
rewrite (unsigned_lit S), (unsigned_lit (S + zlength s + -1)) by lia.
replace (2147450880 + S ≫ 3) with (SH S) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (S + zlength s + -1) ≫ 3) with (SH (S + zlength s - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH S /\ SH S <= SH (S + zlength s - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH S)), (unsigned_lit (SH (S + zlength s - 1))) by lia. rewrite !land_m8 by lia.
replace (SH S - SH S mod 8) with (8 * (SH S / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (S + zlength s - 1) - SH (S + zlength s - 1) mod 8) with (8 * (SH (S + zlength s - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ S (zlength s) SO2 ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ S (zlength s) SO2 ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1x a3x a4x a5x : word,
ms1 = MS (@bvmap_set 5 word 11 a1x (@bvmap_set 5 word 13 a3x (@bvmap_set 5 word 14 a4x (@bvmap_set 5 word 15 a5x R)))) FF (wz 0x52a98) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (S + zlength s + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (S + zlength s - 1)) (SH S)) as [X1|X1].
+ ifT. replace (SH S) with (SH (S + zlength s - 1)) by lia. stp. step. ifT. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifF. eapply (qslow_loop_a1 0x52b5c ltac:(right; right; right; reflexivity) (Z.to_nat (SH (S + zlength s - 1) - SH S)) (SH S)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4y. stp. step. ifT. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1x & a3x & a4x & a5x & ->). simp_regs.

do 8 step.
pose proof (stk_merge asegs _ _ _ _ ST3 ST4 ltac:(lia)) as STm.
release_frame FR2 STm (bv_unsigned sp).
step. step.
apply evt_done. unfold fwrite_diag_post. do 14 eexists. exists m2. split; [reflexivity|].
split; [exact MU|]. split; [exact WMf|]. split; [exact MI2|]. split; [exact STm|]. split; [exact W02|]. split; [exact SSP2| reflexivity].
- destruct (BIG ltac:(lia)) as [KS L43]. pose proof (SOK ltac:(lia)) as SO2.
ifT. step. ifT. step. step. step.
pose proof (rt_mem_cells_of _ SB2 RC2) as RTM.
destruct W02 as (fl2 & md2 & e2 & we2 & tl2 & FC2 & FL2 & WE2 & HE2). destruct SSP2 as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
unfold file_cells in FC2.
step. call_u rip_spec7; [exact RTM| exact MI2| unsigned_lits; exact ST3| exact CEIL| unsigned_lits; lia| exact SO2| lia| lia| lia| exact KS|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST5 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
assert (W03 : stderr_wfile0 m3) by (exists fl2, md2, e2, we2, tl2; split; [exact FC2| split; [exact FL2| split; [exact WE2| exact HE2]]]).
assert (SSP3 : ssp_cells m3 canary) by (split; [exact G1| exact G2]).
clear FC2 G1 G2.
step. ifT. step. step.

do 8 step.
match goal with STb : stk asegs m3 (bv_unsigned sp + -2128) _, FRx : rw_cells asegs m3 (bv_unsigned sp + -56) _ |- _ =>
pose proof (stk_merge asegs _ _ _ _ ST5 STb ltac:(lia)) as STm; release_frame FRx STm (bv_unsigned sp) end.
step. step.
apply evt_done. unfold fwrite_diag_post. do 14 eexists. exists m3. split; [reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [exact STm|]. split; [exact W03|]. split; [exact SSP3| reflexivity].
Qed.
End Fwrite.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp Qsn5 QQwg QUxU QmP7 QOJv QOH4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 QYyZ.Mq0 QnRU.Mq0 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QnRU.Mq7 Q9Ho.Mq1 QOJv.Mq5 Qu3b.Mq2 QteI.Mq7 QteI.Mq4 QOH4.
Import QpY2.Mq2.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition refill_entry : Z := 0x43ff0.
Definition REFILL_STACK : Z := 672.

Lemma srliw_form : forall a n, 0 <= a < 2^31 -> 0 <= n -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz a))) n) = Z.shiftr a n.
Proof.
intros a n Ha Hn. rewrite unsigned_lit by lia.
assert (W : bv_wrap 32 a = a) by (unfold bv_wrap; change (bv_modulus 32) with (2^32); apply Z.mod_small; lia). rewrite W.
assert (S : 0 <= Z.shiftr a n <= a) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 n); Z.div_mod_to_equations; nia).
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia.
Qed.

Lemma divuw_word : forall a b, 0 <= a < 2^31 -> 0 < b < 2^31 -> v_divuw (wz a) (wz b) = wz (a / b).
Proof.
intros a b Ha Hb. unfold v_divuw. rewrite !unsigned_lit by lia.
unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite !Z.mod_small by lia.
replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal.
assert (Q : 0 <= a / b <= a) by (Z.div_mod_to_equations; nia).
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia.
Qed.

Lemma bsize_facts : forall c, 1 <= c <= 31 -> 32 <= bsize c <= 65536 /\ bsize c mod 32 = 0.
Proof.
intros c Hc. unfold bsize. destruct (Z.eqb_spec c 31) as [->|NE]; [cbn; lia|].
pose proof (class_size_facts c Hc) as [S1 S2].
assert (class_size c <= 65536); [| lia].
assert (H : forallb (fun c => class_size c <=? 65536) (map Z.of_nat (seq 1 30)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H c). apply Z.leb_le, H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma bmax_formula : forall c, 1 <= c <= 31 -> bmax c = 2 * Z.max 1 (Z.min 8 (1024 / bsize c)).
Proof.
intros c Hc. unfold bmax, bsize, max_count. destruct (Z.eqb_spec c 31) as [->|NE]; [reflexivity|].
pose proof (class_size_facts c Hc) as [S1 _]. replace (class_size c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Definition RPrimI (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : word -> option byte) (i : Z) (K : Z -> pcls) : Prop :=
hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ forall c, 0 <= c < kNumClasses -> class_rep (if c <? i then set_inited a else a) G RE X m c (K c).

Lemma cr_pure_set_inited : forall a G c K, cr_pure a G c K -> cr_pure (set_inited a) G c K.
Proof.
intros a G c K PU. unfold cr_pure in *. replace (cls (set_inited a) c) with (cls a c) by reflexivity.
repeat match goal with |- _ /\ _ => split end; try tauto. cbn. intros H; discriminate.
Qed.

Lemma RPrimI_start : forall a G RE X m K,
hjunk m (rl_T X + 2768) (rl_T X + 2800) -> (forall c, G c <> [] -> 1 <= c < kNumClasses) ->
(forall c, 0 <= c < kNumClasses -> class_rep a G RE X m c (K c)) -> RPrimI a G RE X m 1 K.
Proof.
intros a G RE X m K HJ GNE HC. split; [exact HJ|]. split; [exact GNE|].
intros c Hc. destruct (Z.ltb_spec c 1) as [LT|GE]; [| exact (HC c Hc)].
assert (c = 0) as -> by lia. pose proof (HC 0 Hc) as H0.
destruct H0 as ((RI & PC & CHH) & PU & REG). split; [| split; [apply cr_pure_set_inited; exact PU| exact REG]].
split; [exact RI|]. split; [| exact CHH].

cbn [as_cache_inited set_inited]. unfold pc_cells in *. unfold bmax, bsize. cbn.
replace (cls (set_inited a) 0) with (cls a 0) by reflexivity.
destruct (as_cache_inited a); exact PC.
Qed.

Lemma RPrimI_done : forall a G RE X m K, RPrimI a G RE X m 32 K -> RPrim (set_inited a) G RE X m.
Proof.
intros a G RE X m K (HJ & GNE & HC). exists K. split; [exact HJ|]. split; [exact GNE|].
intros c Hc. pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hc.
specialize (HC c ltac:(rewrite K32; exact Hc)). replace (c <? 32) with true in HC by (symmetry; apply Z.ltb_lt; lia). exact HC.
Qed.

Section Init.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma wz_m16 : forall i, wz (i - 16) = wz (i + 18446744073709551600).
Proof. intros i. apply Z_to_bv_eqm. replace (i + 18446744073709551600) with (i - 16 + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma wz_p64 : forall i, wz (i + 18446744073709551616) = wz i.
Proof. intros i. apply Z_to_bv_eqm. replace (i + 18446744073709551616) with (i + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. Qed.

Lemma init_iter : forall (i : Z) ra sp gp tp s0 s1 a0 a1 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (Q : machine_state -> Prop),
1 <= i <= 31 ->
(forall t5', evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a1 a2 (wz (32 * i)) a4 (wz (i - 16)) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (bsize i)) (wz (Z.min 8 (1024 / bsize i))) t5' t6)
F (wz 0x44070) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a1 a2 (wz (32 * i)) a4 (wz (i - 16)) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x44094) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hi CONT.
pose proof (bsize_facts i Hi) as [B1 B2].
assert (DQ : 0 <= 1024 / bsize i <= 32) by (Z.div_mod_to_equations; nia).
destruct (Z.eq_dec i 31) as [->|N31].
-
step. if_lit.
stp. stp. stp.
step. if_lit.
step. stp. step.
apply (CONT (wz 8)).
- destruct (Z.lt_ge_cases i 16) as [LO16|HI16].
+
rewrite wz_m16.
step. ifz.
step.
rewrite wz_p64.
step.
step. ifz.
assert (E32 : bsize i = 32 * i) by (unfold bsize; replace (i =? 31) with false by (symmetry; apply Z.eqb_neq; lia); apply class_size_lo; lia).
rewrite E32 in CONT, DQ.
stp.
rewrite divuw_word by lia.
stp.
step.
destruct (Z.ltb_spec (1024 / (32 * i)) 8) as [L8|G8]; ifz.
* rewrite <- wz_m16. replace (Z.min 8 (1024 / (32 * i))) with (1024 / (32 * i)) in CONT by lia. apply CONT.
* stp. step. rewrite <- wz_m16. replace (Z.min 8 (1024 / (32 * i))) with 8 in CONT by lia. apply CONT.
+
step. ifz.
step.
replace (i - 16 + 16) with i by lia.
step.
step.
destruct (Z.eq_dec i 16) as [->|N16].
* if_lit.
stp. stp. step. if_lit.
apply (CONT (wz 8)).
* ifz.
step. step. step. step. step. step. step.
get_reg 28%Z ltac:(fun v => replace v with (wz (bsize i)) by (clear - HI16 N16 N31 Hi; unfold bsize; enum_cases i 17 30; vm_compute; reflexivity)).
assert (B768 : 768 <= bsize i).
{ clear - HI16 N16 N31 Hi. unfold bsize. enum_cases i 17 30; vm_compute; discriminate. }
stp.
rewrite divuw_word by lia.
stp. step. ifz.
replace (Z.min 8 (1024 / bsize i)) with (1024 / bsize i) in CONT by (Z.div_mod_to_equations; nia). apply CONT.
Qed.

Definition a5v (i : Z) : Z := if i <? 16 then i + 18446744073709551600 else i - 16.
Lemma a5v_range : forall i, 1 <= i <= 32 -> 0 <= a5v i < 2^64.
Proof. intros i Hi. unfold a5v. destruct (Z.ltb_spec i 16); lia. Qed.
Lemma wz_a5v : forall i, wz (a5v i) = wz (i - 16).
Proof. intros i. unfold a5v. destruct (Z.ltb_spec i 16); [symmetry; apply wz_m16| reflexivity]. Qed.
Lemma wz_a5v_S : forall i, wz (a5v i + 1) = wz (a5v (i + 1)).
Proof.
intros i. unfold a5v. apply Z_to_bv_eqm. destruct (Z.ltb_spec i 16), (Z.ltb_spec (i + 1) 16); try (f_equal; lia).
replace (i + 18446744073709551600 + 1) with (i + 1 - 16 + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma init_loop : forall (n : nat) (i : Z) ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (a : AState) (G : ghost) (K : Z -> pcls) (Q : machine_state -> Prop),
Z.of_nat n = 32 - i -> 1 <= i <= 31 -> rlay_ok RE X -> as_cache_inited a = false ->
RPrimI a G RE X m i K -> mem_inv asegs m ->
(forall m' (t3' t4' t5' : word), mem_inv asegs m' -> munch [(rl_T X + 288, rl_T X + 2768)] m m' -> wmono asegs m m' ->
RPrimI a G RE X m' 32 K ->
evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (rl_T X + 216 + 80 * 32)) a2 (wz (32 * 32)) a4 (wz 16) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (wz 0x440e8) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (rl_T X + 216 + 80 * i)) a2 (wz (32 * i)) a4 (wz (a5v i)) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x44094) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros until Q; intros Hn Hi RL EI0 RPI MI CONT; [lia|].
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
idtac. rewrite ?KHI_eq in TK. clear TA. unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof (reg_geom RE X RL i ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). clear PAL.
pose proof (bsize_facts i ltac:(lia)) as [B1 B2]. pose proof (a5v_range i ltac:(lia)) as A5. pose proof (a5v_range (i + 1) ltac:(lia)) as A5'.
assert (QB : 0 <= Z.min 8 (1024 / bsize i) <= 8) by (Z.div_mod_to_equations; nia).
pose proof (munch_refl [(rl_T X + 288, rl_T X + 2768)] m) as MU. pose proof (wmono_refl asegs m) as WM.

destruct RPI as (HJS & GNE & HCall).
pose proof (HCall i ltac:(rewrite K32; lia)) as HC. replace (i <? i) with false in HC by (symmetry; apply Z.ltb_irrefl).
apply class_rep_split in HC. destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
cbv beta delta [pc_cells] in PC0. rewrite EI0 in PC0. unfold pc_addr in PC0, ACH.
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS). clear RI.
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _). rewrite KS in P13.
assert (LFL : Z.of_nat (length (map (fun i0 : Z => wz (coff i i0)) (pk_fl (K i)))) = c_num_freed (cls a i)) by (rewrite length_map; exact P1).
remember (rl_T X + 216 + 80 * i) as P8 eqn:EP8.
replace (rl_T X + 208 + 80 * i) with (P8 + -8) in PC0 by lia.
pose proof (munch_refl [(P8 + -4, P8 + 8)] m) as MUi.
rewrite wz_a5v. apply init_iter; [lia|]. intros t5'. rewrite <- wz_a5v.
step.
step. step.
rewrite wz_a5v_S. replace (32 * i + 32) with (32 * (i + 1)) by lia.
step. step.
get_reg 29%Z ltac:(fun v => replace v with (wz (bmax i))).
2:{ unfold v_sltiu. rewrite (unsigned_lit (Z.min 8 (1024 / bsize i))) by lia. change (bv_wrap 64 1) with 1.
rewrite bmax_formula by lia.
destruct (Z.ltb_spec (Z.min 8 (1024 / bsize i)) 1); rewrite (unsigned_lit 1) || rewrite (unsigned_lit 0); try lia;
rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia. }
stf.
stf.
step.
replace (P8 + 80) with (rl_T X + 216 + 80 * (i + 1)) by lia.
step.

assert (FWc : Forall (wc_ok RE X i) [(P8 + -4, P8 + 8)]).
{ constructor; [| constructor]. cbn -[fp_cls]. do 2 right. intros z Hz. right; left. unfold pc_addr. lia. }
epose proof (agree_other_classes RE X i _ m _ RL ltac:(lia) MUi WM FWc) as AGo.
assert (AGi : agree_on asegs (fun z => fp_cls RE X i z /\ ~ (P8 + -4 <= z < P8 + 8)) m _)
by (eapply agree_on_of_munch; [exact MUi| exact WM|]; intros z [_ Nz] Hz; cbn; split; [exact Nz| exact I]).
pose proof (HCall i ltac:(rewrite K32; lia)) as HC0. replace (i <? i) with false in HC0 by (symmetry; apply Z.ltb_irrefl).
destruct HC0 as (((k1 & k2 & k3 & k4 & RI0) & _ & _) & _ & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RPI' : RPrimI a G RE X mm (i + 1) K) end.
{ split; [eapply hjunk_wmono; [exact HJS| exact WM]|]. split; [exact GNE|].
intros c Hc. destruct (Z.eq_dec c i) as [->|NE].
- replace (i <? i + 1) with true by (symmetry; apply Z.ltb_lt; lia).
apply class_rep_split. split; [| split; [apply cr_pure_set_inited; exact PU|]].
+ split; [| split].
* exists k1, k2, k3, k4. replace (cls (set_inited a) i) with (cls a i) by reflexivity.
eapply rw_cells_agree; [exact AGi| exact RI0|]. intros z Hz. cbn [ri_cells cells_size csize Nat.add] in Hz. unfold ri_addr in Hz.
split; [left; unfold ri_addr; lia| rewrite EP8; clear - Hz TD RIq PK Hi; lia].
* cbv beta delta [pc_cells]. cbn [as_cache_inited set_inited]. replace (cls (set_inited a) i) with (cls a i) by reflexivity.
unfold pc_addr. replace (rl_T X + 208 + 80 * i) with (P8 + -8) by lia. exact PC0.
* exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
+ intros _. replace (cls (set_inited a) i) with (cls a i) by reflexivity. split; [exact FA|].
split; [eapply hjunk_wmono; [exact FJ| exact WM]|]. split; [| eapply hjunk_wmono; [exact FS| exact WM]].
apply (cr_user_ext a). 2: reflexivity. 2: reflexivity.
eapply cr_user_agree; [exact PU| exact HU| lia|]. eapply agree_on_mono; [exact AGi|].
intros z Uz. apply (uzone_bounds RE X i z RL ltac:(lia)) in Uz. split.
{ destruct Uz as [Uz|Uz]; [do 4 right; left; rewrite KO; exact Uz| do 5 right; split; cbn [fst snd]; [lia| rewrite KO; change (3758096384 / 8) with 469762048; lia]]. }
rewrite EP8. rewrite RB in Uz. unfold SH, A_SHADOW_OFS in Uz. clear - Uz TD PK PCH PH TK Hi. Z.div_mod_to_equations. lia.
- replace (c <? i + 1) with (c <? i) by (destruct (Z.ltb_spec c (i + 1)), (Z.ltb_spec c i); try reflexivity; lia).
eapply class_rep_agree; [exact (HCall c Hc)| rewrite K32 in Hc; exact Hc| apply AGo; [exact Hc| exact NE]]. }
destruct (Z.eq_dec i 31) as [->|N31].
- if_lit. eapply CONT; [exact MI| exact MU| exact WM| exact RPI'].
- unfold_cond. rewrite (unsigned_lit (a5v (i + 1))) by lia.
replace (a5v (i + 1) =? bv_unsigned (wz 16)) with false by (symmetry; apply Z.eqb_neq; change (bv_unsigned (wz 16)) with 16; unfold a5v; destruct (Z.ltb_spec (i + 1) 16); lia).
eapply (IH (i + 1)); [lia| lia| exact RL| exact EI0| exact RPI'| exact MI|].
intros m' t3'' t4'' t5'' MI' MU' WM' RPI''. eapply CONT; [exact MI'| eapply munch_trans; [exact MU| exact MU']| eapply wmono_trans; [exact WM| exact WM']| exact RPI''].
Qed.
End Init.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition refill_W (sp c au : Z) : list (Z * Z) :=
[ (sp - REFILL_STACK, sp); (rl_T X + 208, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition refill_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (refill_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ gstep RE X a (snd r) G G1
/\ a0 = wz (if fst r then 1 else 0)
/\ RPrim (snd r) G1 RE X m'.

Definition refill_mid (ra sp gp s0 s1 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(a : AState) (G : ghost) (c lo : Z) (m : word -> option byte) (ms1 : machine_state) : Prop :=
exists (a3' a5' a6' a7' t0' t1' t2' t3' t4' t5' : word) m1,
ms1 = MS (mkR ra (wz (bv_unsigned sp + -32)) gp (wz A_TP) t0' t1' t2' (wz (pc_addr X c)) s1 (wz (rl_T X + 208)) (wz (max_count c)) (wz A_INSTANCE)
a3' (wz c) a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
F (wz 0x44010) fc None m1 (seg_rom asegs)
/\ munch [(bv_unsigned sp + -32, bv_unsigned sp); (rl_T X + 288, rl_T X + 2768)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (bv_unsigned sp + -32)
/\ (exists j8, rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra])
/\ RPrim (set_inited a) G RE X m1.

Lemma refill_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c lo : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
1 <= c <= 30 -> c_count (cls a c) = 0 ->
aimplT atn (refill (ae_L RE) a c) s
(refill_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (rl_T X + 208)) (wz (pc_addr X c)) (wz A_INSTANCE) (wz c) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz refill_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL RS RP MI ST CEIL LO Hc CNT0.
pose proof CEIL as CEIL'. idtac. unfold REFILL_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. hide TA.
pose proof (max_count_facts c ltac:(lia)) as [MC1 MC2]. hide MC2.
pose proof (bmax_eq c ltac:(lia)) as BMX.
unfold refill_entry. apply aimplT_from_evt.

apply (evt_cut asegs (refill_mid ra sp gp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t6 F fc a G c lo m)).
{ destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. destruct HC as ((_ & PC0 & _) & _ & _).
cbv beta delta [pc_cells] in PC0. rewrite CNT0, BMX in PC0. unfold pc_addr in PC0.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (rl_T X + 288, rl_T X + 2768)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MUs.
carve_frame 32%nat ST.
step. step. step. step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RP0 : RPrim a G RE X mm) by (eapply RPrim_stack; [exact RP| exact RL| exact MUs| exact WM| constructor; [cbn [fst]; idtac; lia| constructor]]) end.
clear MUs.
unfold pc_addr. step.
step.
destruct (as_cache_inited a) eqn:EI; rewrite sx32_small by lia.
-
ifz. apply evt_done. unfold refill_mid. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eexists; exact FR|].
eapply (Q9Ho.Mq1.RPrim_ext a); [exact RP0| intros; reflexivity| cbn; rewrite EI; reflexivity| apply same_len_refl| apply same_tags_refl].
-
if_lit.
do 8 step. step.
replace (wz (-15)) with (wz (a5v 1)) by (apply Z_to_bv_eqm; reflexivity).
replace (rl_T X + 296) with (rl_T X + 216 + 80 * 1) by lia. replace (wz 32) with (wz (32 * 1)) by reflexivity.
destruct (RPrim_open _ _ _ _ _ RP0) as (K0 & HJS0 & GNE0 & HCall0).
eapply (init_loop RE X 31 1) with (K := K0); [reflexivity| lia| exact RL| exact EI| apply RPrimI_start; [exact HJS0| exact GNE0| exact HCall0]| exact MI|].
intros m1 t3' t4' t5' MI1 MU1 WM1 RPI. apply RPrimI_done in RPI.
clear PC0. hide MU. transport_after_call asegs m0 m1 MU1 WM1. unhide MU.
assert (MU' : munch _ m m1) by (eapply munch_chain; [exact MU| exact MU1| sub_fp_solve]). clear MU MU1 MI; rename MU' into MU; rename MI1 into MI.

destruct (RPrim_open _ _ _ _ _ RPI) as (K1 & _ & _ & HCall1).
pose proof (HCall1 c ltac:(rewrite K32; lia)) as HC1. destruct HC1 as ((_ & PC1 & _) & _ & _).
cbv beta delta [pc_cells] in PC1. cbn [as_cache_inited set_inited] in PC1. rewrite BMX in PC1.
replace (cls (set_inited a) c) with (cls a c) in PC1 by reflexivity. rewrite CNT0 in PC1. unfold pc_addr in PC1.
step.
rewrite sx32_small by lia.
step.
apply evt_done. unfold refill_mid. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eexists; exact FR|]. exact RPI. }
intros ms1 (a3' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & m1 & -> & MU1 & WM1 & MI1 & ST1 & [j8 FR1] & RP1).
clear MI ST.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & _ & HCall). pose proof (HCall c ltac:(rewrite K32; lia)) as (_ & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _). rewrite KO in G4.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL HCall.
assert (RT1 : RTconst RE X m1).
{ eapply RTconst_munch; [exact RT| exact MU1| exact WM1|].
apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]|]. apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. repeat (apply Forall_cons; [st_avoid_solve|]). apply Forall_nil. }
unfold pc_addr.
step.
rewrite srliw_form by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
step. step.
replace (rl_T X + 208 + 2047 + 513) with (rl_T X + 2768) by lia.
step.
step. step. step.
step.
apply evt_done. unfold refill.
eapply aimplT_bind.
{ eapply (getfrom_spec L RE X) with (a := set_inited a); try eassumption.
- rewrite unsigned_lit by lia. exact ST1.
- rewrite unsigned_lit by lia. unfold GETFROM_STACK. lia.
- reflexivity.
- reflexivity. }
intros [ok a1] s' ms' POST. unfold gfa_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & G1 & -> & -> & MU2 & WM2 & MI2 & ST2 & RT2 & RS2 & GS & A0 & REST).
cbn [fst snd] in A0, GS, REST. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
replace (ret_pc (wz 278576)) with (wz 278576) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold gfa_W, GETFROM_STACK, pc_addr, ri_addr in MU2. rewrite ?KS, ?KO in MU2.
change (536870912 / 8) with 67108864 in MU2. change (3758096384 / 8) with 469762048 in MU2.
change (cls (set_inited a) c) with (cls a c) in MU2.
hide MU1. transport_after_call asegs m1 m2 MU2 WM2. unhide MU1.
assert (MU : munch (refill_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m2).
{ unfold refill_W, REFILL_STACK, pc_addr, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
eapply munch_chain; [| exact MU2| sub_fp_solve]. eapply munch_weaken; [| exact MU1]. sub_fp_solve. }
unfold refill_W, REFILL_STACK, pc_addr, ri_addr in MU. rewrite ?KS, ?KO in MU. change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
clear MU1 MU2 MI1. try clear ST1.
assert (GSa : gstep RE X a (set_inited a) G G) by (apply gstep_ext; intros; reflexivity).
destruct ok.
-
destruct REST as [PCz WAND]. unfold pc_addr in PCz, WAND.
apply aimplT_ret.
step. ifz.
pose proof (munch_refl [(rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 4)] m2) as MUw. pose proof (wmono_refl asegs m2) as WMw.
remember (rl_T X + 208 + 80 * c) as PCa eqn:EPCa.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (WAND mm MUw WMw PCz) as RPF end.
subst PCa.
step. step. step. step. step.
release_frame FR1 ST2 (bv_unsigned sp).
apply evt_done. unfold refill_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold refill_W, REFILL_STACK, pc_addr, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM1|]. split; [assumption|]. split; [exact ST2|].
split. { eapply RTconst_munch; [exact RT2| exact MUw| exact WMw|]. apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS2| exact MUw| exact WMw|]. apply Forall_cons; [st_avoid_solve| apply Forall_nil]. }
split. { cbn [snd]. eapply gstep_trans; [exact GSa|]. eapply gstep_trans; [exact GS|].
apply gstep_ext; [intros c0| intros c0| reflexivity| reflexivity];
unfold upd_cls; (destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]). }
split; [reflexivity|]. exact RPF.
-
apply aimplT_ret.
step. if_lit.
step. step. step. step. step.
release_frame FR1 ST2 (bv_unsigned sp).
apply evt_done. unfold refill_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold refill_W, REFILL_STACK, pc_addr, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM1|]. split; [assumption|]. split; [exact ST2|].
split; [exact RT2|]. split; [exact RS2|].
split. { cbn [snd]. eapply gstep_trans; [exact GSa| exact GS]. }
split; [reflexivity|]. exact REST.
Qed.
End S.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg Q61C QbcP_c1 QWRO QFQR QKBN QN4c QjIq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QTVW.Mqc. Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QTVW.Mq8 Qu3b.Mq5 QnRU.Mqf QnRU QteI.Mqb Qu3b.Mq4 QQNJ.Mq8 QpzM.Mqo QjIq.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Ltac ifT := unfold_cond; cond_unsig; if_true.
Ltac ifF := unfold_cond; cond_unsig; if_false.

Definition fwrite_stub : Z := 0x4fd58.
Definition fwrite_icpt_entry : Z := 0x52db0.
Definition FWRITE_ICPT_DEPTH : Z := 2128 + FWRITE_DEPTH.

Lemma stderr_wfile0_munch : forall m m' W, stderr_wfile0 m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= RSTDERR \/ RSTDERR + 232 <= fst iv) W -> stderr_wfile0 m'.
Proof.
intros m m' W (flags & mode & e & wend & tail & FC & FL & WE & HE) MU WM HW.
exists flags, mode, e, wend, tail. split; [| split; [exact FL| split; [exact WE| exact HE]]].
eapply rw_cells_apart; [exact FC| exact MU| exact WM|].
eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold file_cells in *. cbn [cells_size csize length Nat.add Nat.mul fst snd] in *. lia.
Qed.

Lemma ssp_cells_munch : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Section Fwrite.
Context {BAND : Band}.
Context {St : Type}.

Definition fwrite_icpt_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
towrite_stmt ->
stderr_wfile0 m ->
bytes_at asegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s <= OUT_MAX ->
a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_ICPT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
ssp_cells m canary -> mem_inv asegs m ->
ISH m -> szone (bv_unsigned a0) (zlength s) ->
(bv_unsigned sp <= 2^47) ->
implM asegs (stderr_fwrite s : M St unit) st
(fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fwrite_stub) fc None m (seg_rom asegs)).

Theorem fwrite_icpt_proof : fwrite_diag_stmt (St:=St) -> fwrite_icpt_stmt.
Proof.
intros FWR. unfold fwrite_icpt_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SEPS1 SEPS2 SSP MI ISH0 SZ SPT.
pose proof GLO as CEIL'. unfold GLOBALS_TOP in CEIL'. unfold FWRITE_ICPT_DEPTH, FWRITE_DEPTH in LO.
assert (CEIL : band_lo <= lo) by (idtac; exact CEIL').
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold zb in BS. rewrite length_map in BS.
pose proof LS as LS'. unfold zlength in LS'.
set (S := bv_unsigned a0) in *. assert (ES : S = bv_unsigned a0) by reflexivity. clearbody S.
assert (EA0 : a0 = wz S) by (rewrite ES; symmetry; apply Z_to_bv_bv_unsigned). rewrite EA0. clear ES EA0.
pose proof ISH0 as (ASH & RC & SB).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
set (BAh := bytes_at) in SRC.
eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.
unfold fwrite_stub. step.
carve_frame 56%nat ST.
do 8 istep.
step. step. step. step. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof RCc as RCc'. pose proof (rt_159bb8 _ RCc) as K16. pose proof (rt_161720 _ RCc) as K18. clear RCc.
step. call_u tryinit_spec7; [exact K18| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => rename H into ST1' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
step. stp. step. step. step. step. step. clear K16 K18 RCc'.

step. apply evt_done.
assert (W0A : stderr_wfile0 mA) by (eapply stderr_wfile0_munch; [exact W0| exact MUs| exact WM| zforalls]).
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (SRCA : bytes_at asegs mA S (zb s)) by (subst BAh; eapply bytes_at_transport; [exact SRC| exact MUs| cbn [disjoint_from]; unfold zb; rewrite length_map; unfold zlength in *; lia]).
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
clear W0 SSP SRC.
eapply implM_post_evt''.
{ eapply (FWR _ _ _ _ _ _ _ _ _ (wz S)) with (lo := lo) (s := s); try reflexivity;
[ exact TW| exact W0A| unsigned_lits; exact SRCA| exact BYT| exact LS| unsigned_lits; exact ST1'
| unsigned_lits; unfold FWRITE_DEPTH; lia| exact GLO| unsigned_lits; lia| unsigned_lits; exact SEPS2| exact SSPA| assumption
| unsigned_lits; lia | unsigned_lits; unfold szone in SZ; lia  ]. }
cbv beta. intros [] st2 ms2 PO.
destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST3 & W02 & SSP2 & ->).
unsigned_lits_in MU2. unsigned_lits_in ST3.
replace (ret_pc (wz 0x52e0c)) with (wz 0x52e0c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. lia. }
assert (ST4 : stk asegs m2 (bv_unsigned sp + -2128) (bv_unsigned sp + -56)).
{ eapply stk_transport; [exact ST2| exact MU2| exact WM2|]. cbn. lia. }
assert (ISH2 : ISH m2) by (eapply ISH_munch_zone; [exact ISHA| exact MU2| exact WM2| zforalls]).
clear FR ST2 ISHA W0A SSPA SRCA.
pose proof ISH2 as (ASH2 & RC2 & SB2).
pose proof (rng_ok_of_ash _ _ _ ASH2 SZ ltac:(lia)) as RNG. pose proof RNG as (_ & S47 & SOK & BIG & NB).

assert (MU : munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m2).
{ apply (munch_trans _ m mA m2).
- eapply munch_weaken; [| exact MUs]. unfold sub_fp; cbn; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn; intros; lia. }
pose proof (wmono_trans asegs _ _ _ WM WM2) as WMf. clear MUs MU2 WM WM2.

step. ifF. step. ifF. stp.
match goal with |- context [wz (1 * ?x)] => replace (1 * x) with x by lia | _ => idtac end.
rewrite ?(unsigned_lit (zlength s)) by lia.

step. step. step. step. rewrite (unsigned_lit S), zb_lxor_ones by lia. ifF.

step. step. step.
destruct (Z_le_gt_dec (zlength s) 64) as [N64|N65].
- unfold_cond. fold_lit_ux. rewrite u_nm65 by lia.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (symmetry; apply (proj2 (Bool.negb_false_iff _)); apply Z.ltb_lt; clear - N64 LS; lia) end.
cbv iota.
destruct (NB ltac:(lia)) as [[w1 W1] [w2 W2]]. pose proof (SOK ltac:(lia)) as SO2.
destruct SB2 as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. step. step. step. stp. stp.
rewrite (unsigned_lit S), (unsigned_lit (S + zlength s + -1)) by lia.
replace (2147450880 + S ≫ 3) with (SH S) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (S + zlength s + -1) ≫ 3) with (SH (S + zlength s - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH S /\ SH S <= SH (S + zlength s - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH S)), (unsigned_lit (SH (S + zlength s - 1))) by lia. rewrite !land_m8 by lia.
replace (SH S - SH S mod 8) with (8 * (SH S / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (S + zlength s - 1) - SH (S + zlength s - 1) mod 8) with (8 * (SH (S + zlength s - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ S (zlength s) SO2 ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ S (zlength s) SO2 ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1x a3x a4x a5x : word,
ms1 = MS (@bvmap_set 5 word 11 a1x (@bvmap_set 5 word 13 a3x (@bvmap_set 5 word 14 a4x (@bvmap_set 5 word 15 a5x R)))) FF (wz 0x52e70) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (S + zlength s + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (S + zlength s - 1)) (SH S)) as [X1|X1].
+ ifT. replace (SH S) with (SH (S + zlength s - 1)) by lia. stp. step. ifT. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifF. eapply (qslow_loop_a1 0x52f34 ltac:(right; right; right; reflexivity) (Z.to_nat (SH (S + zlength s - 1) - SH S)) (SH S)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4y. stp. step. ifT. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1x & a3x & a4x & a5x & ->). simp_regs.

do 8 step.
pose proof (stk_merge asegs _ _ _ _ ST3 ST4 ltac:(lia)) as STm.
release_frame FR2 STm (bv_unsigned sp).
step. step.
apply evt_done. unfold fwrite_diag_post. do 14 eexists. exists m2. split; [reflexivity|].
split; [exact MU|]. split; [exact WMf|]. split; [exact MI2|]. split; [exact STm|]. split; [exact W02|]. split; [exact SSP2| reflexivity].
- destruct (BIG ltac:(lia)) as [KS L43]. pose proof (SOK ltac:(lia)) as SO2.
ifT. step. ifT. step. step. step.
pose proof (rt_mem_cells_of _ SB2 RC2) as RTM.
destruct W02 as (fl2 & md2 & e2 & we2 & tl2 & FC2 & FL2 & WE2 & HE2). destruct SSP2 as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
unfold file_cells in FC2.
step. call_u rip_spec7; [exact RTM| exact MI2| unsigned_lits; exact ST3| exact CEIL| unsigned_lits; lia| exact SO2| lia| lia| lia| exact KS|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST5 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
assert (W03 : stderr_wfile0 m3) by (exists fl2, md2, e2, we2, tl2; split; [exact FC2| split; [exact FL2| split; [exact WE2| exact HE2]]]).
assert (SSP3 : ssp_cells m3 canary) by (split; [exact G1| exact G2]).
clear FC2 G1 G2.
step. ifT. step. step.

do 8 step.
match goal with STb : stk asegs m3 (bv_unsigned sp + -2128) _, FRx : rw_cells asegs m3 (bv_unsigned sp + -56) _ |- _ =>
pose proof (stk_merge asegs _ _ _ _ ST5 STb ltac:(lia)) as STm; release_frame FRx STm (bv_unsigned sp) end.
step. step.
apply evt_done. unfold fwrite_diag_post. do 14 eexists. exists m3. split; [reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [exact STm|]. split; [exact W03|]. split; [exact SSP3| reflexivity].
Qed.
End Fwrite.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g QAdh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 QYyZ.Mq8 QnRU.Mqc QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QnRU.Mqi Q9Ho.Mq3 QOJv.Mqc Qu3b QteI.Mqg QteI.Mqd QAdh.
Import QpY2.Mqc.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition refill_entry : Z := 0x4421c.
Definition REFILL_STACK : Z := 672.

Lemma srliw_form : forall a n, 0 <= a < 2^31 -> 0 <= n -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz a))) n) = Z.shiftr a n.
Proof.
intros a n Ha Hn. rewrite unsigned_lit by lia.
assert (W : bv_wrap 32 a = a) by (unfold bv_wrap; change (bv_modulus 32) with (2^32); apply Z.mod_small; lia). rewrite W.
assert (S : 0 <= Z.shiftr a n <= a) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 n); Z.div_mod_to_equations; nia).
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia.
Qed.

Lemma divuw_word : forall a b, 0 <= a < 2^31 -> 0 < b < 2^31 -> v_divuw (wz a) (wz b) = wz (a / b).
Proof.
intros a b Ha Hb. unfold v_divuw. rewrite !unsigned_lit by lia.
unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite !Z.mod_small by lia.
replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal.
assert (Q : 0 <= a / b <= a) by (Z.div_mod_to_equations; nia).
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia.
Qed.

Lemma bsize_facts : forall c, 1 <= c <= 31 -> 32 <= bsize c <= 65536 /\ bsize c mod 32 = 0.
Proof.
intros c Hc. unfold bsize. destruct (Z.eqb_spec c 31) as [->|NE]; [cbn; lia|].
pose proof (class_size_facts c Hc) as [S1 S2].
assert (class_size c <= 65536); [| lia].
assert (H : forallb (fun c => class_size c <=? 65536) (map Z.of_nat (seq 1 30)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H c). apply Z.leb_le, H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma bmax_formula : forall c, 1 <= c <= 31 -> bmax c = 2 * Z.max 1 (Z.min 8 (1024 / bsize c)).
Proof.
intros c Hc. unfold bmax, bsize, max_count. destruct (Z.eqb_spec c 31) as [->|NE]; [reflexivity|].
pose proof (class_size_facts c Hc) as [S1 _]. replace (class_size c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Definition RPrimI (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : word -> option byte) (i : Z) (K : Z -> pcls) : Prop :=
hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ forall c, 0 <= c < kNumClasses -> class_rep (if c <? i then set_inited a else a) G RE X m c (K c).

Lemma cr_pure_set_inited : forall a G c K, cr_pure a G c K -> cr_pure (set_inited a) G c K.
Proof.
intros a G c K PU. unfold cr_pure in *. replace (cls (set_inited a) c) with (cls a c) by reflexivity.
repeat match goal with |- _ /\ _ => split end; try tauto. cbn. intros H; discriminate.
Qed.

Lemma RPrimI_start : forall a G RE X m K,
hjunk m (rl_T X + 2768) (rl_T X + 2800) -> (forall c, G c <> [] -> 1 <= c < kNumClasses) ->
(forall c, 0 <= c < kNumClasses -> class_rep a G RE X m c (K c)) -> RPrimI a G RE X m 1 K.
Proof.
intros a G RE X m K HJ GNE HC. split; [exact HJ|]. split; [exact GNE|].
intros c Hc. destruct (Z.ltb_spec c 1) as [LT|GE]; [| exact (HC c Hc)].
assert (c = 0) as -> by lia. pose proof (HC 0 Hc) as H0.
destruct H0 as ((RI & PC & CHH) & PU & REG). split; [| split; [apply cr_pure_set_inited; exact PU| exact REG]].
split; [exact RI|]. split; [| exact CHH].

cbn [as_cache_inited set_inited]. unfold pc_cells in *. unfold bmax, bsize. cbn.
replace (cls (set_inited a) 0) with (cls a 0) by reflexivity.
destruct (as_cache_inited a); exact PC.
Qed.

Lemma RPrimI_done : forall a G RE X m K, RPrimI a G RE X m 32 K -> RPrim (set_inited a) G RE X m.
Proof.
intros a G RE X m K (HJ & GNE & HC). exists K. split; [exact HJ|]. split; [exact GNE|].
intros c Hc. pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hc.
specialize (HC c ltac:(rewrite K32; exact Hc)). replace (c <? 32) with true in HC by (symmetry; apply Z.ltb_lt; lia). exact HC.
Qed.

Section Init.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma wz_m16 : forall i, wz (i - 16) = wz (i + 18446744073709551600).
Proof. intros i. apply Z_to_bv_eqm. replace (i + 18446744073709551600) with (i - 16 + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma wz_p64 : forall i, wz (i + 18446744073709551616) = wz i.
Proof. intros i. apply Z_to_bv_eqm. replace (i + 18446744073709551616) with (i + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. Qed.

Lemma init_iter : forall (i : Z) ra sp gp tp s0 s1 a0 a1 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (Q : machine_state -> Prop),
1 <= i <= 31 ->
(forall t5', evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a1 a2 (wz (32 * i)) a4 (wz (i - 16)) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (bsize i)) (wz (Z.min 8 (1024 / bsize i))) t5' t6)
F (wz 0x4429c) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a1 a2 (wz (32 * i)) a4 (wz (i - 16)) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x442c0) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hi CONT.
pose proof (bsize_facts i Hi) as [B1 B2].
assert (DQ : 0 <= 1024 / bsize i <= 32) by (Z.div_mod_to_equations; nia).
destruct (Z.eq_dec i 31) as [->|N31].
-
step. if_lit.
stp. stp. stp.
step. if_lit.
step. stp. step.
apply (CONT (wz 8)).
- destruct (Z.lt_ge_cases i 16) as [LO16|HI16].
+
rewrite wz_m16.
step. ifz.
step.
rewrite wz_p64.
step.
step. ifz.
assert (E32 : bsize i = 32 * i) by (unfold bsize; replace (i =? 31) with false by (symmetry; apply Z.eqb_neq; lia); apply class_size_lo; lia).
rewrite E32 in CONT, DQ.
stp.
rewrite divuw_word by lia.
stp.
step.
destruct (Z.ltb_spec (1024 / (32 * i)) 8) as [L8|G8]; ifz.
* rewrite <- wz_m16. replace (Z.min 8 (1024 / (32 * i))) with (1024 / (32 * i)) in CONT by lia. apply CONT.
* stp. step. rewrite <- wz_m16. replace (Z.min 8 (1024 / (32 * i))) with 8 in CONT by lia. apply CONT.
+
step. ifz.
step.
replace (i - 16 + 16) with i by lia.
step.
step.
destruct (Z.eq_dec i 16) as [->|N16].
* if_lit.
stp. stp. step. if_lit.
apply (CONT (wz 8)).
* ifz.
step. step. step. step. step. step. step.
get_reg 28%Z ltac:(fun v => replace v with (wz (bsize i)) by (clear - HI16 N16 N31 Hi; unfold bsize; enum_cases i 17 30; vm_compute; reflexivity)).
assert (B768 : 768 <= bsize i).
{ clear - HI16 N16 N31 Hi. unfold bsize. enum_cases i 17 30; vm_compute; discriminate. }
stp.
rewrite divuw_word by lia.
stp. step. ifz.
replace (Z.min 8 (1024 / bsize i)) with (1024 / bsize i) in CONT by (Z.div_mod_to_equations; nia). apply CONT.
Qed.

Definition a5v (i : Z) : Z := if i <? 16 then i + 18446744073709551600 else i - 16.
Lemma a5v_range : forall i, 1 <= i <= 32 -> 0 <= a5v i < 2^64.
Proof. intros i Hi. unfold a5v. destruct (Z.ltb_spec i 16); lia. Qed.
Lemma wz_a5v : forall i, wz (a5v i) = wz (i - 16).
Proof. intros i. unfold a5v. destruct (Z.ltb_spec i 16); [symmetry; apply wz_m16| reflexivity]. Qed.
Lemma wz_a5v_S : forall i, wz (a5v i + 1) = wz (a5v (i + 1)).
Proof.
intros i. unfold a5v. apply Z_to_bv_eqm. destruct (Z.ltb_spec i 16), (Z.ltb_spec (i + 1) 16); try (f_equal; lia).
replace (i + 18446744073709551600 + 1) with (i + 1 - 16 + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma init_loop : forall (n : nat) (i : Z) ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (a : AState) (G : ghost) (K : Z -> pcls) (Q : machine_state -> Prop),
Z.of_nat n = 32 - i -> 1 <= i <= 31 -> rlay_ok RE X -> as_cache_inited a = false ->
RPrimI a G RE X m i K -> mem_inv asegs m ->
(forall m' (t3' t4' t5' : word), mem_inv asegs m' -> munch [(rl_T X + 288, rl_T X + 2768)] m m' -> wmono asegs m m' ->
RPrimI a G RE X m' 32 K ->
evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (rl_T X + 216 + 80 * 32)) a2 (wz (32 * 32)) a4 (wz 16) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (wz 0x44314) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (rl_T X + 216 + 80 * i)) a2 (wz (32 * i)) a4 (wz (a5v i)) (wz 15) (wz 1024)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x442c0) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros until Q; intros Hn Hi RL EI0 RPI MI CONT; [lia|].
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
idtac. rewrite ?KHI_eq in TK. clear TA. unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof (reg_geom RE X RL i ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). clear PAL.
pose proof (bsize_facts i ltac:(lia)) as [B1 B2]. pose proof (a5v_range i ltac:(lia)) as A5. pose proof (a5v_range (i + 1) ltac:(lia)) as A5'.
assert (QB : 0 <= Z.min 8 (1024 / bsize i) <= 8) by (Z.div_mod_to_equations; nia).
pose proof (munch_refl [(rl_T X + 288, rl_T X + 2768)] m) as MU. pose proof (wmono_refl asegs m) as WM.

destruct RPI as (HJS & GNE & HCall).
pose proof (HCall i ltac:(rewrite K32; lia)) as HC. replace (i <? i) with false in HC by (symmetry; apply Z.ltb_irrefl).
apply class_rep_split in HC. destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
cbv beta delta [pc_cells] in PC0. rewrite EI0 in PC0. unfold pc_addr in PC0, ACH.
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS). clear RI.
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _). rewrite KS in P13.
assert (LFL : Z.of_nat (length (map (fun i0 : Z => wz (coff i i0)) (pk_fl (K i)))) = c_num_freed (cls a i)) by (rewrite length_map; exact P1).
remember (rl_T X + 216 + 80 * i) as P8 eqn:EP8.
replace (rl_T X + 208 + 80 * i) with (P8 + -8) in PC0 by lia.
pose proof (munch_refl [(P8 + -4, P8 + 8)] m) as MUi.
rewrite wz_a5v. apply init_iter; [lia|]. intros t5'. rewrite <- wz_a5v.
step.
step. step.
rewrite wz_a5v_S. replace (32 * i + 32) with (32 * (i + 1)) by lia.
step. step.
get_reg 29%Z ltac:(fun v => replace v with (wz (bmax i))).
2:{ unfold v_sltiu. rewrite (unsigned_lit (Z.min 8 (1024 / bsize i))) by lia. change (bv_wrap 64 1) with 1.
rewrite bmax_formula by lia.
destruct (Z.ltb_spec (Z.min 8 (1024 / bsize i)) 1); rewrite (unsigned_lit 1) || rewrite (unsigned_lit 0); try lia;
rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia. }
stf.
stf.
step.
replace (P8 + 80) with (rl_T X + 216 + 80 * (i + 1)) by lia.
step.

assert (FWc : Forall (wc_ok RE X i) [(P8 + -4, P8 + 8)]).
{ constructor; [| constructor]. cbn -[fp_cls]. do 2 right. intros z Hz. right; left. unfold pc_addr. lia. }
epose proof (agree_other_classes RE X i _ m _ RL ltac:(lia) MUi WM FWc) as AGo.
assert (AGi : agree_on asegs (fun z => fp_cls RE X i z /\ ~ (P8 + -4 <= z < P8 + 8)) m _)
by (eapply agree_on_of_munch; [exact MUi| exact WM|]; intros z [_ Nz] Hz; cbn; split; [exact Nz| exact I]).
pose proof (HCall i ltac:(rewrite K32; lia)) as HC0. replace (i <? i) with false in HC0 by (symmetry; apply Z.ltb_irrefl).
destruct HC0 as (((k1 & k2 & k3 & k4 & RI0) & _ & _) & _ & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RPI' : RPrimI a G RE X mm (i + 1) K) end.
{ split; [eapply hjunk_wmono; [exact HJS| exact WM]|]. split; [exact GNE|].
intros c Hc. destruct (Z.eq_dec c i) as [->|NE].
- replace (i <? i + 1) with true by (symmetry; apply Z.ltb_lt; lia).
apply class_rep_split. split; [| split; [apply cr_pure_set_inited; exact PU|]].
+ split; [| split].
* exists k1, k2, k3, k4. replace (cls (set_inited a) i) with (cls a i) by reflexivity.
eapply rw_cells_agree; [exact AGi| exact RI0|]. intros z Hz. cbn [ri_cells cells_size csize Nat.add] in Hz. unfold ri_addr in Hz.
split; [left; unfold ri_addr; lia| rewrite EP8; clear - Hz TD RIq PK Hi; lia].
* cbv beta delta [pc_cells]. cbn [as_cache_inited set_inited]. replace (cls (set_inited a) i) with (cls a i) by reflexivity.
unfold pc_addr. replace (rl_T X + 208 + 80 * i) with (P8 + -8) by lia. exact PC0.
* exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
+ intros _. replace (cls (set_inited a) i) with (cls a i) by reflexivity. split; [exact FA|].
split; [eapply hjunk_wmono; [exact FJ| exact WM]|]. split; [| eapply hjunk_wmono; [exact FS| exact WM]].
apply (cr_user_ext a). 2: reflexivity. 2: reflexivity.
eapply cr_user_agree; [exact PU| exact HU| lia|]. eapply agree_on_mono; [exact AGi|].
intros z Uz. apply (uzone_bounds RE X i z RL ltac:(lia)) in Uz. split.
{ destruct Uz as [Uz|Uz]; [do 4 right; left; rewrite KO; exact Uz| do 5 right; split; cbn [fst snd]; [lia| rewrite KO; change (3758096384 / 8) with 469762048; lia]]. }
rewrite EP8. rewrite RB in Uz. unfold SH, A_SHADOW_OFS in Uz. clear - Uz TD PK PCH PH TK Hi. Z.div_mod_to_equations. lia.
- replace (c <? i + 1) with (c <? i) by (destruct (Z.ltb_spec c (i + 1)), (Z.ltb_spec c i); try reflexivity; lia).
eapply class_rep_agree; [exact (HCall c Hc)| rewrite K32 in Hc; exact Hc| apply AGo; [exact Hc| exact NE]]. }
destruct (Z.eq_dec i 31) as [->|N31].
- if_lit. eapply CONT; [exact MI| exact MU| exact WM| exact RPI'].
- unfold_cond. rewrite (unsigned_lit (a5v (i + 1))) by lia.
replace (a5v (i + 1) =? bv_unsigned (wz 16)) with false by (symmetry; apply Z.eqb_neq; change (bv_unsigned (wz 16)) with 16; unfold a5v; destruct (Z.ltb_spec (i + 1) 16); lia).
eapply (IH (i + 1)); [lia| lia| exact RL| exact EI0| exact RPI'| exact MI|].
intros m' t3'' t4'' t5'' MI' MU' WM' RPI''. eapply CONT; [exact MI'| eapply munch_trans; [exact MU| exact MU']| eapply wmono_trans; [exact WM| exact WM']| exact RPI''].
Qed.
End Init.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition refill_W (sp c au : Z) : list (Z * Z) :=
[ (sp - REFILL_STACK, sp); (rl_T X + 208, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition refill_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (refill_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ gstep RE X a (snd r) G G1
/\ a0 = wz (if fst r then 1 else 0)
/\ RPrim (snd r) G1 RE X m'.

Definition refill_mid (ra sp gp s0 s1 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(a : AState) (G : ghost) (c lo : Z) (m : word -> option byte) (ms1 : machine_state) : Prop :=
exists (a3' a5' a6' a7' t0' t1' t2' t3' t4' t5' : word) m1,
ms1 = MS (mkR ra (wz (bv_unsigned sp + -32)) gp (wz A_TP) t0' t1' t2' (wz (pc_addr X c)) s1 (wz (rl_T X + 208)) (wz (max_count c)) (wz A_INSTANCE)
a3' (wz c) a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
F (wz 0x4423c) fc None m1 (seg_rom asegs)
/\ munch [(bv_unsigned sp + -32, bv_unsigned sp); (rl_T X + 288, rl_T X + 2768)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (bv_unsigned sp + -32)
/\ (exists j8, rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra])
/\ RPrim (set_inited a) G RE X m1.

Lemma refill_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c lo : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
1 <= c <= 30 -> c_count (cls a c) = 0 ->
aimplT atn (refill (ae_L RE) a c) s
(refill_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (rl_T X + 208)) (wz (pc_addr X c)) (wz A_INSTANCE) (wz c) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz refill_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL RS RP MI ST CEIL LO Hc CNT0.
pose proof CEIL as CEIL'. idtac. unfold REFILL_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. hide TA.
pose proof (max_count_facts c ltac:(lia)) as [MC1 MC2]. hide MC2.
pose proof (bmax_eq c ltac:(lia)) as BMX.
unfold refill_entry. apply aimplT_from_evt.

apply (evt_cut asegs (refill_mid ra sp gp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t6 F fc a G c lo m)).
{ destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. destruct HC as ((_ & PC0 & _) & _ & _).
cbv beta delta [pc_cells] in PC0. rewrite CNT0, BMX in PC0. unfold pc_addr in PC0.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (rl_T X + 288, rl_T X + 2768)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MUs.
carve_frame 32%nat ST.
step. step. step. step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RP0 : RPrim a G RE X mm) by (eapply RPrim_stack; [exact RP| exact RL| exact MUs| exact WM| constructor; [cbn [fst]; idtac; lia| constructor]]) end.
clear MUs.
unfold pc_addr. step.
step.
destruct (as_cache_inited a) eqn:EI; rewrite sx32_small by lia.
-
ifz. apply evt_done. unfold refill_mid. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eexists; exact FR|].
eapply (Q9Ho.Mq3.RPrim_ext a); [exact RP0| intros; reflexivity| cbn; rewrite EI; reflexivity| apply same_len_refl| apply same_tags_refl].
-
if_lit.
do 8 step. step.
replace (wz (-15)) with (wz (a5v 1)) by (apply Z_to_bv_eqm; reflexivity).
replace (rl_T X + 296) with (rl_T X + 216 + 80 * 1) by lia. replace (wz 32) with (wz (32 * 1)) by reflexivity.
destruct (RPrim_open _ _ _ _ _ RP0) as (K0 & HJS0 & GNE0 & HCall0).
eapply (init_loop RE X 31 1) with (K := K0); [reflexivity| lia| exact RL| exact EI| apply RPrimI_start; [exact HJS0| exact GNE0| exact HCall0]| exact MI|].
intros m1 t3' t4' t5' MI1 MU1 WM1 RPI. apply RPrimI_done in RPI.
clear PC0. hide MU. transport_after_call asegs m0 m1 MU1 WM1. unhide MU.
assert (MU' : munch _ m m1) by (eapply munch_chain; [exact MU| exact MU1| sub_fp_solve]). clear MU MU1 MI; rename MU' into MU; rename MI1 into MI.

destruct (RPrim_open _ _ _ _ _ RPI) as (K1 & _ & _ & HCall1).
pose proof (HCall1 c ltac:(rewrite K32; lia)) as HC1. destruct HC1 as ((_ & PC1 & _) & _ & _).
cbv beta delta [pc_cells] in PC1. cbn [as_cache_inited set_inited] in PC1. rewrite BMX in PC1.
replace (cls (set_inited a) c) with (cls a c) in PC1 by reflexivity. rewrite CNT0 in PC1. unfold pc_addr in PC1.
step.
rewrite sx32_small by lia.
step.
apply evt_done. unfold refill_mid. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eexists; exact FR|]. exact RPI. }
intros ms1 (a3' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & m1 & -> & MU1 & WM1 & MI1 & ST1 & [j8 FR1] & RP1).
clear MI ST.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & _ & HCall). pose proof (HCall c ltac:(rewrite K32; lia)) as (_ & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _). rewrite KO in G4.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL HCall.
assert (RT1 : RTconst RE X m1).
{ eapply RTconst_munch; [exact RT| exact MU1| exact WM1|].
apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]|]. apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. repeat (apply Forall_cons; [st_avoid_solve|]). apply Forall_nil. }
unfold pc_addr.
step.
rewrite srliw_form by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
step. step.
replace (rl_T X + 208 + 2047 + 513) with (rl_T X + 2768) by lia.
step.
step. step. step.
step.
apply evt_done. unfold refill.
eapply aimplT_bind.
{ eapply (getfrom_spec L RE X) with (a := set_inited a); try eassumption.
- rewrite unsigned_lit by lia. exact ST1.
- rewrite unsigned_lit by lia. unfold GETFROM_STACK. lia.
- reflexivity.
- reflexivity. }
intros [ok a1] s' ms' POST. unfold gfa_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & G1 & -> & -> & MU2 & WM2 & MI2 & ST2 & RT2 & RS2 & GS & A0 & REST).
cbn [fst snd] in A0, GS, REST. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -32)) in * by lia.
replace (ret_pc (wz 279132)) with (wz 279132) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold gfa_W, GETFROM_STACK, pc_addr, ri_addr in MU2. rewrite ?KS, ?KO in MU2.
change (536870912 / 8) with 67108864 in MU2. change (3758096384 / 8) with 469762048 in MU2.
change (cls (set_inited a) c) with (cls a c) in MU2.
hide MU1. transport_after_call asegs m1 m2 MU2 WM2. unhide MU1.
assert (MU : munch (refill_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m2).
{ unfold refill_W, REFILL_STACK, pc_addr, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
eapply munch_chain; [| exact MU2| sub_fp_solve]. eapply munch_weaken; [| exact MU1]. sub_fp_solve. }
unfold refill_W, REFILL_STACK, pc_addr, ri_addr in MU. rewrite ?KS, ?KO in MU. change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
clear MU1 MU2 MI1. try clear ST1.
assert (GSa : gstep RE X a (set_inited a) G G) by (apply gstep_ext; intros; reflexivity).
destruct ok.
-
destruct REST as [PCz WAND]. unfold pc_addr in PCz, WAND.
apply aimplT_ret.
step. ifz.
pose proof (munch_refl [(rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 4)] m2) as MUw. pose proof (wmono_refl asegs m2) as WMw.
remember (rl_T X + 208 + 80 * c) as PCa eqn:EPCa.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (WAND mm MUw WMw PCz) as RPF end.
subst PCa.
step. step. step. step. step.
release_frame FR1 ST2 (bv_unsigned sp).
apply evt_done. unfold refill_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold refill_W, REFILL_STACK, pc_addr, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM1|]. split; [assumption|]. split; [exact ST2|].
split. { eapply RTconst_munch; [exact RT2| exact MUw| exact WMw|]. apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS2| exact MUw| exact WMw|]. apply Forall_cons; [st_avoid_solve| apply Forall_nil]. }
split. { cbn [snd]. eapply gstep_trans; [exact GSa|]. eapply gstep_trans; [exact GS|].
apply gstep_ext; [intros c0| intros c0| reflexivity| reflexivity];
unfold upd_cls; (destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]). }
split; [reflexivity|]. exact RPF.
-
apply aimplT_ret.
step. if_lit.
step. step. step. step. step.
release_frame FR1 ST2 (bv_unsigned sp).
apply evt_done. unfold refill_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold refill_W, REFILL_STACK, pc_addr, ri_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM1|]. split; [assumption|]. split; [exact ST2|].
split; [exact RT2|]. split; [exact RS2|].
split. { cbn [snd]. eapply gstep_trans; [exact GSa| exact GS]. }
split; [reflexivity|]. exact REST.
Qed.
End S.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoBx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoBx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWHo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFd5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QpzM.Mqe.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {BAND : Band}.
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
Hypothesis QHI : (q + 16 <= 140737488355328)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 143552)%Z /\ szone A (Z.of_nat (length fmt)).

Hypothesis SEP_F : ((954304 <= Fp /\ Fp + 232 <= 6575456) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6576024 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation ctx_all := (QpzM.Mqe.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (QpzM.Mqe.W Fp B BS q lo AP).
Local Notation Fok_refl := (QpzM.Mqe.Fok_refl F).
Local Notation POST := (QpzM.Mqe.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (QpzM.Mqe.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (QpzM.Mqe.lo_cells AP nla nlt).
Local Notation finv := (QpzM.Mqe.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (QpzM.Mqe.fmt_rng fmt HF).
Local Notation implM_eq_ms := (QpzM.Mqe.implM_eq_ms (St:=St)).
Local Notation sink_store := (QpzM.Mqe.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (QpzM.Mqe.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (QpzM.Mqe.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (QpzM.Mqe.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (QpzM.Mqe.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (QpzM.Mqe.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (QpzM.Mqe.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (QpzM.Mqe.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (QpzM.Mqe.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (QpzM.Mqe.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (QpzM.Mqe.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (QpzM.Mqe.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (QpzM.Mqe.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (QpzM.Mqe.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (QpzM.Mqe.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (QpzM.Mqe.body_loc Fp B BS q lo).
Local Notation S_TAIL := (QpzM.Mqe.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QpzM.Mqe.tregs Fp q gp tp A).
Local Notation tinv := (QpzM.Mqe.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (QpzM.Mqe.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (QpzM.Mqe.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (QpzM.Mqe.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (QpzM.Mqe.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (QpzM.Mqe.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (QpzM.Mqe.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (QpzM.Mqe.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (QpzM.Mqe.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (QpzM.Mqe.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (QpzM.Mqe.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (QpzM.Mqe.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (QpzM.Mqe.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (QpzM.Mqe.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (QpzM.Mqe.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (QpzM.Mqe.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (QpzM.Mqe.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (QpzM.Mqe.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (QpzM.Mqe.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (QpzM.Mqe.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (QpzM.Mqe.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (QpzM.Mqe.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation FPv := (Z_to_bv 64 Fp).
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
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia | glo_lia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; glo_lia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].

Lemma L_EXIT : S_EXIT.
Proof using LO BAND.
first [ apply QpzM.Mqe.L_EXIT; first [eassumption]
| intros; eapply QpzM.Mqe.L_EXIT; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_END : S_END.
Proof using GLO HAP LO SEP_F VAHI BAND.
first [ apply QpzM.Mqe.L_END; first [eassumption | eexact L_EXIT]
| intros; eapply QpzM.Mqe.L_END; first [eassumption | eexact L_EXIT] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_EXIT1 : S_EXIT1.
Proof using LO BAND.
first [ apply QpzM.Mqe.L_EXIT1; first [eassumption]
| intros; eapply QpzM.Mqe.L_EXIT1; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF BAND.
first [ apply QpzM.Mqe.L_SCAN; first [eassumption]
| intros; eapply QpzM.Mqe.L_SCAN; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FLAGS : S_FLAGS.
Proof using HF BAND.
first [ apply QpzM.Mqe.L_FLAGS; first [eassumption]
| intros; eapply QpzM.Mqe.L_FLAGS; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WLOOP : S_WLOOP.
Proof using HF BAND.
first [ apply QpzM.Mqe.L_WLOOP; first [eassumption]
| intros; eapply QpzM.Mqe.L_WLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF BAND.
first [ intro; apply QpzM.Mqe.L_WIDTH; first [eassumption]
| intros; eapply QpzM.Mqe.L_WIDTH; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PLOOP : S_PLOOP.
Proof using HF BAND.
first [ apply QpzM.Mqe.L_PLOOP; first [eassumption]
| intros; eapply QpzM.Mqe.L_PLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF BAND.
first [ intro; apply QpzM.Mqe.L_PREC; first [eassumption]
| intros; eapply QpzM.Mqe.L_PREC; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATE : S_STATE.
Proof using HF BAND.
first [ apply QpzM.Mqe.L_STATE; first [eassumption]
| intros; eapply QpzM.Mqe.L_STATE; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DIR : S_DIR.
Proof using HF BAND.
first [ apply QpzM.Mqe.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
| intros; eapply QpzM.Mqe.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
first [ apply QpzM.Mqe.L_T6; first [eassumption]
| intros; eapply QpzM.Mqe.L_T6; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_T5; first [eassumption | eexact L_T6]
| intros; eapply QpzM.Mqe.L_T5; first [eassumption | eexact L_T6] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_T4; first [eassumption | eexact L_T5]
| intros; eapply QpzM.Mqe.L_T4; first [eassumption | eexact L_T5] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_T3; first [eassumption | eexact L_T4]
| intros; eapply QpzM.Mqe.L_T3; first [eassumption | eexact L_T4] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_T2; first [eassumption | eexact L_T3]
| intros; eapply QpzM.Mqe.L_T2; first [eassumption | eexact L_T3] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_T1; first [eassumption | eexact L_T2]
| intros; eapply QpzM.Mqe.L_T1; first [eassumption | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply QpzM.Mqe.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC2 : S_INTC2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_INTC2; first [eassumption | eexact L_TAIL]
| intros; eapply QpzM.Mqe.L_INTC2; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC : S_INTC.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_INTC; first [eassumption | eexact L_INTC2]
| intros; eapply QpzM.Mqe.L_INTC; first [eassumption | eexact L_INTC2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI BAND.
first [ apply QpzM.Mqe.L_DLOOP; first [eassumption]
| intros; eapply QpzM.Mqe.L_DLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_FMTU2; first [eassumption | eexact L_INTC]
| intros; eapply QpzM.Mqe.L_FMTU2; first [eassumption | eexact L_INTC] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
| intros; eapply QpzM.Mqe.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_CV_D; first [eassumption | eexact L_FMTU]
| intros; eapply QpzM.Mqe.L_CV_D; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_U : S_CV_U.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_CV_U; first [eassumption | eexact L_FMTU]
| intros; eapply QpzM.Mqe.L_CV_U; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI BAND.
first [ apply QpzM.Mqe.L_XLOOP; first [eassumption]
| intros; eapply QpzM.Mqe.L_XLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
| intros; eapply QpzM.Mqe.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply QpzM.Mqe.L_CV_S; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ BAND BS0.
first [ apply QpzM.Mqe.L_CV_FP; first [eassumption]
| intros; eapply QpzM.Mqe.L_CV_FP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply QpzM.Mqe.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP]
| intros; eapply QpzM.Mqe.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ intro; apply QpzM.Mqe.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply QpzM.Mqe.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_P1 : S_P1.
Proof using A0 HA HF LO BAND.
first [ apply QpzM.Mqe.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
| intros; eapply QpzM.Mqe.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F BAND.
first [ apply QpzM.Mqe.L_PRO; first [eassumption]
| intros; eapply QpzM.Mqe.L_PRO; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.

Let HS_PRO := L_PRO.
Let HS_HEAD := L_HEAD.
Let HS_P1 := L_P1.

Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
let _ := ctx_all in
SINK m0 st -> stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
rw_cells asegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
(0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
implM asegs (printf_model OUT OUTFP fmt args) st POST
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd60d0) fc0 None m0 (seg_rom asegs)).
Proof using FRM0 HS_HEAD HS_PRO BAND.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
unfold printf_model. ienter.
stmt HS_PRO as NXP.
eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
assert (HS : SINK m st).
{ eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; glo_lia | apply Forall_nil]). }
assert (APC : rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
{ eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
stmt (HS_HEAD (length fmt)) as NXH.
jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
[ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
let _ := ctx_all in
stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
pass1_ok fmt = true ->
evt asegs (POST1 0)
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0xd60d0) fc0 None m0 (seg_rom asegs)).
Proof using HS_P1 HS_PRO BAND.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
stmt HS_PRO as NXP.
eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
stmt HS_P1 as NX1.
jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
Qed.

End PrintfCore.

Theorem printf_core_proof {BAND : Band} : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof.
intros St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA HSZ BS0 SEPF SEPB HAP HVA VAHI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
pose proof (L_CORE2 Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
(bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM (conj HA HSZ) SEPF SEPB HAP HVA (proj1 Ra1) VAHI BS0
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

Theorem printf_core1_proof {BAND : Band} : printf_core1_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HSZ HAP A2HI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
pose proof (L_CORE1 954304 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
(bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; exact GLO ) SPHI (conj HA HSZ) ltac:(lia) HAP ltac:(lia) (proj1 Ra1) ltac:(lia)
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
