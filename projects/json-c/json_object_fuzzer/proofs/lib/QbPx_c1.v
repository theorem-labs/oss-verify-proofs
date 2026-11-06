(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp QvDJ Qu3b QnRU QteI QMPy QIG5 QC9y QJwx Qr5k QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho QFd5 QYyZ Qi1S Q0z1 QlES QXE1.
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
Import QMPy. Import Qu3b.Mq0.
Import QIG5. Import QC9y. Import QJwx.Mq0.
Import Qr5k.Mq0.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QFd5.Mq0 QYyZ.Mq1 QteI.Mq2.

Export Qi1S.Mq0.
Import Q0z1.
Import QlES.
Import QXE1.Mq0. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
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

Hypothesis HA : (A + zlength fmt <= 147392)%Z /\ szone A (Z.of_nat (length fmt)).

Hypothesis SEP_F : ((945072 <= Fp /\ Fp + 232 <= 6565536) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6566104 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation ctx_all := (Qi1S.Mq0.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (Qi1S.Mq0.W Fp B BS q lo AP).
Local Notation Fok_refl := (Qi1S.Mq0.Fok_refl F).
Local Notation POST := (Qi1S.Mq0.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (Qi1S.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (Qi1S.Mq0.lo_cells AP nla nlt).
Local Notation finv := (Qi1S.Mq0.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (Qi1S.Mq0.fmt_rng fmt HF).
Local Notation implM_eq_ms := (Qi1S.Mq0.implM_eq_ms (St:=St)).
Local Notation sink_store := (Qi1S.Mq0.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (Qi1S.Mq0.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (Qi1S.Mq0.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (Qi1S.Mq0.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (Qi1S.Mq0.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (Qi1S.Mq0.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (Qi1S.Mq0.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (Qi1S.Mq0.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (Qi1S.Mq0.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (Qi1S.Mq0.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (Qi1S.Mq0.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATEL := (Qi1S.Mq0.S_STATEL Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (Qi1S.Mq0.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (Qi1S.Mq0.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (Qi1S.Mq0.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (Qi1S.Mq0.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (Qi1S.Mq0.body_loc Fp B BS q lo).
Local Notation S_TAIL := (Qi1S.Mq0.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (Qi1S.Mq0.tregs Fp q gp tp A).
Local Notation tinv := (Qi1S.Mq0.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (Qi1S.Mq0.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (Qi1S.Mq0.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (Qi1S.Mq0.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (Qi1S.Mq0.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (Qi1S.Mq0.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (Qi1S.Mq0.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (Qi1S.Mq0.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (Qi1S.Mq0.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (Qi1S.Mq0.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (Qi1S.Mq0.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (Qi1S.Mq0.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (Qi1S.Mq0.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (Qi1S.Mq0.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (Qi1S.Mq0.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (Qi1S.Mq0.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (Qi1S.Mq0.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (Qi1S.Mq0.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_C := (Qi1S.Mq0.S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (Qi1S.Mq0.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (Qi1S.Mq0.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (Qi1S.Mq0.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (Qi1S.Mq0.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
first [ apply Qi1S.Mq0.L_EXIT; first [eassumption]
| intros; eapply Qi1S.Mq0.L_EXIT; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_END : S_END.
Proof using GLO HAP LO SEP_F VAHI BAND.
first [ apply Qi1S.Mq0.L_END; first [eassumption | eexact L_EXIT]
| intros; eapply Qi1S.Mq0.L_END; first [eassumption | eexact L_EXIT] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_EXIT1 : S_EXIT1.
Proof using LO BAND.
first [ apply Qi1S.Mq0.L_EXIT1; first [eassumption]
| intros; eapply Qi1S.Mq0.L_EXIT1; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF BAND.
first [ apply Qi1S.Mq0.L_SCAN; first [eassumption]
| intros; eapply Qi1S.Mq0.L_SCAN; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FLAGS : S_FLAGS.
Proof using HF BAND.
first [ apply Qi1S.Mq0.L_FLAGS; first [eassumption]
| intros; eapply Qi1S.Mq0.L_FLAGS; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WLOOP : S_WLOOP.
Proof using HF BAND.
first [ apply Qi1S.Mq0.L_WLOOP; first [eassumption]
| intros; eapply Qi1S.Mq0.L_WLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF BAND.
first [ intro; apply Qi1S.Mq0.L_WIDTH; first [eassumption]
| intros; eapply Qi1S.Mq0.L_WIDTH; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PLOOP : S_PLOOP.
Proof using HF BAND.
first [ apply Qi1S.Mq0.L_PLOOP; first [eassumption]
| intros; eapply Qi1S.Mq0.L_PLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF BAND.
first [ intro; apply Qi1S.Mq0.L_PREC; first [eassumption]
| intros; eapply Qi1S.Mq0.L_PREC; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATE : S_STATE.
Proof using HF BAND.
first [ apply Qi1S.Mq0.L_STATE; first [eassumption]
| intros; eapply Qi1S.Mq0.L_STATE; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATEL : S_STATEL.
Proof using HF BAND.
first [ apply Qi1S.Mq0.L_STATEL; first [eassumption]
| intros; eapply Qi1S.Mq0.L_STATEL; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DIR : S_DIR.
Proof using HF BAND.
first [ apply Qi1S.Mq0.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL]
| intros; eapply Qi1S.Mq0.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
first [ apply Qi1S.Mq0.L_T6; first [eassumption]
| intros; eapply Qi1S.Mq0.L_T6; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_T5; first [eassumption | eexact L_T6]
| intros; eapply Qi1S.Mq0.L_T5; first [eassumption | eexact L_T6] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_T4; first [eassumption | eexact L_T5]
| intros; eapply Qi1S.Mq0.L_T4; first [eassumption | eexact L_T5] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_T3; first [eassumption | eexact L_T4]
| intros; eapply Qi1S.Mq0.L_T3; first [eassumption | eexact L_T4] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_T2; first [eassumption | eexact L_T3]
| intros; eapply Qi1S.Mq0.L_T2; first [eassumption | eexact L_T3] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_T1; first [eassumption | eexact L_T2]
| intros; eapply Qi1S.Mq0.L_T1; first [eassumption | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply Qi1S.Mq0.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC2 : S_INTC2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_INTC2; first [eassumption | eexact L_TAIL]
| intros; eapply Qi1S.Mq0.L_INTC2; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC : S_INTC.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_INTC; first [eassumption | eexact L_INTC2]
| intros; eapply Qi1S.Mq0.L_INTC; first [eassumption | eexact L_INTC2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI BAND.
first [ apply Qi1S.Mq0.L_DLOOP; first [eassumption]
| intros; eapply Qi1S.Mq0.L_DLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_FMTU2; first [eassumption | eexact L_INTC]
| intros; eapply Qi1S.Mq0.L_FMTU2; first [eassumption | eexact L_INTC] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
| intros; eapply Qi1S.Mq0.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_CV_D; first [eassumption | eexact L_FMTU]
| intros; eapply Qi1S.Mq0.L_CV_D; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_U : S_CV_U.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_CV_U; first [eassumption | eexact L_FMTU]
| intros; eapply Qi1S.Mq0.L_CV_U; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI BAND.
first [ apply Qi1S.Mq0.L_XLOOP; first [eassumption]
| intros; eapply Qi1S.Mq0.L_XLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
| intros; eapply Qi1S.Mq0.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply Qi1S.Mq0.L_CV_S; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ BAND BS0.
first [ apply Qi1S.Mq0.L_CV_FP; first [eassumption]
| intros; eapply Qi1S.Mq0.L_CV_FP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_C : S_CV_C.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_CV_C; first [eassumption | eexact L_TAIL]
| intros; eapply Qi1S.Mq0.L_CV_C; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.Mq0.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C]
| intros; eapply Qi1S.Mq0.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ intro; apply Qi1S.Mq0.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply Qi1S.Mq0.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_P1 : S_P1.
Proof using A0 HA HF LO BAND.
first [ apply Qi1S.Mq0.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
| intros; eapply Qi1S.Mq0.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F BAND.
first [ apply Qi1S.Mq0.L_PRO; first [eassumption]
| intros; eapply Qi1S.Mq0.L_PRO; first [eassumption] ].

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMPy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFy3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJwx.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k.Mq3.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Qi1S.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXE1. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
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

Hypothesis HA : (A + zlength fmt <= 147360)%Z /\ szone A (Z.of_nat (length fmt)).

Hypothesis SEP_F : ((954304 <= Fp /\ Fp + 232 <= 6575456) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6576024 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation ctx_all := (Qi1S.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (Qi1S.W Fp B BS q lo AP).
Local Notation Fok_refl := (Qi1S.Fok_refl F).
Local Notation POST := (Qi1S.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (Qi1S.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (Qi1S.lo_cells AP nla nlt).
Local Notation finv := (Qi1S.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (Qi1S.fmt_rng fmt HF).
Local Notation implM_eq_ms := (Qi1S.implM_eq_ms (St:=St)).
Local Notation sink_store := (Qi1S.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (Qi1S.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (Qi1S.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (Qi1S.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (Qi1S.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (Qi1S.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (Qi1S.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (Qi1S.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (Qi1S.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (Qi1S.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (Qi1S.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATEL := (Qi1S.S_STATEL Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (Qi1S.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (Qi1S.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (Qi1S.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (Qi1S.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (Qi1S.body_loc Fp B BS q lo).
Local Notation S_TAIL := (Qi1S.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (Qi1S.tregs Fp q gp tp A).
Local Notation tinv := (Qi1S.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (Qi1S.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (Qi1S.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (Qi1S.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (Qi1S.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (Qi1S.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (Qi1S.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (Qi1S.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (Qi1S.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (Qi1S.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (Qi1S.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (Qi1S.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (Qi1S.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (Qi1S.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (Qi1S.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (Qi1S.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (Qi1S.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (Qi1S.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_C := (Qi1S.S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (Qi1S.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (Qi1S.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (Qi1S.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (Qi1S.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
first [ apply Qi1S.L_EXIT; first [eassumption]
| intros; eapply Qi1S.L_EXIT; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_END : S_END.
Proof using GLO HAP LO SEP_F VAHI BAND.
first [ apply Qi1S.L_END; first [eassumption | eexact L_EXIT]
| intros; eapply Qi1S.L_END; first [eassumption | eexact L_EXIT] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_EXIT1 : S_EXIT1.
Proof using LO BAND.
first [ apply Qi1S.L_EXIT1; first [eassumption]
| intros; eapply Qi1S.L_EXIT1; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF BAND.
first [ apply Qi1S.L_SCAN; first [eassumption]
| intros; eapply Qi1S.L_SCAN; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FLAGS : S_FLAGS.
Proof using HF BAND.
first [ apply Qi1S.L_FLAGS; first [eassumption]
| intros; eapply Qi1S.L_FLAGS; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WLOOP : S_WLOOP.
Proof using HF BAND.
first [ apply Qi1S.L_WLOOP; first [eassumption]
| intros; eapply Qi1S.L_WLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF BAND.
first [ intro; apply Qi1S.L_WIDTH; first [eassumption]
| intros; eapply Qi1S.L_WIDTH; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PLOOP : S_PLOOP.
Proof using HF BAND.
first [ apply Qi1S.L_PLOOP; first [eassumption]
| intros; eapply Qi1S.L_PLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF BAND.
first [ intro; apply Qi1S.L_PREC; first [eassumption]
| intros; eapply Qi1S.L_PREC; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATE : S_STATE.
Proof using HF BAND.
first [ apply Qi1S.L_STATE; first [eassumption]
| intros; eapply Qi1S.L_STATE; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATEL : S_STATEL.
Proof using HF BAND.
first [ apply Qi1S.L_STATEL; first [eassumption]
| intros; eapply Qi1S.L_STATEL; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DIR : S_DIR.
Proof using HF BAND.
first [ apply Qi1S.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL]
| intros; eapply Qi1S.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ BAND.
first [ apply Qi1S.L_T6; first [eassumption]
| intros; eapply Qi1S.L_T6; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_T5; first [eassumption | eexact L_T6]
| intros; eapply Qi1S.L_T5; first [eassumption | eexact L_T6] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_T4; first [eassumption | eexact L_T5]
| intros; eapply Qi1S.L_T4; first [eassumption | eexact L_T5] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_T3; first [eassumption | eexact L_T4]
| intros; eapply Qi1S.L_T3; first [eassumption | eexact L_T4] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_T2; first [eassumption | eexact L_T3]
| intros; eapply Qi1S.L_T2; first [eassumption | eexact L_T3] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_T1; first [eassumption | eexact L_T2]
| intros; eapply Qi1S.L_T1; first [eassumption | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply Qi1S.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC2 : S_INTC2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_INTC2; first [eassumption | eexact L_TAIL]
| intros; eapply Qi1S.L_INTC2; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC : S_INTC.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_INTC; first [eassumption | eexact L_INTC2]
| intros; eapply Qi1S.L_INTC; first [eassumption | eexact L_INTC2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI BAND.
first [ apply Qi1S.L_DLOOP; first [eassumption]
| intros; eapply Qi1S.L_DLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_FMTU2; first [eassumption | eexact L_INTC]
| intros; eapply Qi1S.L_FMTU2; first [eassumption | eexact L_INTC] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
| intros; eapply Qi1S.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_CV_D; first [eassumption | eexact L_FMTU]
| intros; eapply Qi1S.L_CV_D; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_U : S_CV_U.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_CV_U; first [eassumption | eexact L_FMTU]
| intros; eapply Qi1S.L_CV_U; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI BAND.
first [ apply Qi1S.L_XLOOP; first [eassumption]
| intros; eapply Qi1S.L_XLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
| intros; eapply Qi1S.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply Qi1S.L_CV_S; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ BAND BS0.
first [ apply Qi1S.L_CV_FP; first [eassumption]
| intros; eapply Qi1S.L_CV_FP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_C : S_CV_C.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_CV_C; first [eassumption | eexact L_TAIL]
| intros; eapply Qi1S.L_CV_C; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ apply Qi1S.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C]
| intros; eapply Qi1S.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI BAND.
first [ intro; apply Qi1S.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply Qi1S.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_P1 : S_P1.
Proof using A0 HA HF LO BAND.
first [ apply Qi1S.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
| intros; eapply Qi1S.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F BAND.
first [ apply Qi1S.L_PRO; first [eassumption]
| intros; eapply Qi1S.L_PRO; first [eassumption] ].

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
