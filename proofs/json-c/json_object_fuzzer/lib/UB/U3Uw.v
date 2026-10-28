(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3 QWxq Qc3B QlEo Lib.GwApply QsjA QZAi Ql2m QqdR QYTG Lib.SepCache QnDM UjdK U4l4 UzHs UTIW UxrO Um2h UDgQ Q8Ie UzOj QSCw Qbz7 Qqmw UTru UEQM UPX7 UoQb Uop2 UPsF Ubgs Uvqc UvpC ULNO UOlm U7TP UjBD UelO UWtF UbQl UndM UqnK UwkO U8ql U0UD UvII UvEw U7u1 UBnL UDkt UG5K Uvf1 UImA UpXF Uk39 UoJQ UmjR U68U US6h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM.
Import UjdK U4l4 UzHs UTIW UxrO Um2h UDgQ.
Import Q8Ie.
Import UzOj.
Import QSCw Qbz7 Qqmw.
Import UTru.
Import UEQM.

Export US6h.
Import Qfw3.Mq1.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
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

Hypothesis HA : (A + zlength fmt <= 401408)%Z.

Hypothesis SEP_F : ((416216 <= Fp /\ Fp + 232 <= 622192) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((622200 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation ctx_all := (US6h.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (US6h.W Fp B BS q lo AP).
Local Notation Fok_refl := (US6h.Fok_refl F).
Local Notation POST := (US6h.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (US6h.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (US6h.lo_cells AP nla nlt).
Local Notation finv := (US6h.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (US6h.fmt_rng fmt HF).
Local Notation implM_eq_ms := (US6h.implM_eq_ms (St:=St)).
Local Notation sink_store := (US6h.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (US6h.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (US6h.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (US6h.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (US6h.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (US6h.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (US6h.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (US6h.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (US6h.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (US6h.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (US6h.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATEL := (US6h.S_STATEL Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (US6h.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (US6h.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (US6h.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (US6h.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (US6h.body_loc Fp B BS q lo).
Local Notation S_TAIL := (US6h.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (US6h.tregs Fp q gp tp A).
Local Notation tinv := (US6h.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (US6h.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (US6h.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (US6h.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (US6h.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (US6h.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (US6h.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (US6h.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (US6h.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (US6h.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (US6h.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (US6h.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (US6h.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (US6h.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (US6h.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (US6h.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (US6h.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (US6h.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_C := (US6h.S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (US6h.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (US6h.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (US6h.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (US6h.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
first [ apply UPX7.L_EXIT; first [eassumption]
| intros; eapply UPX7.L_EXIT; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_END : S_END.
Proof using GLO HAP LO SEP_F VAHI.
first [ apply UoQb.L_END; first [eassumption | eexact L_EXIT]
| intros; eapply UoQb.L_END; first [eassumption | eexact L_EXIT] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_EXIT1 : S_EXIT1.
Proof using LO.
first [ apply Uop2.L_EXIT1; first [eassumption]
| intros; eapply Uop2.L_EXIT1; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF.
first [ apply UPsF.L_SCAN; first [eassumption]
| intros; eapply UPsF.L_SCAN; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FLAGS : S_FLAGS.
Proof using HF.
first [ apply Ubgs.L_FLAGS; first [eassumption]
| intros; eapply Ubgs.L_FLAGS; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WLOOP : S_WLOOP.
Proof using HF.
first [ apply Uvqc.L_WLOOP; first [eassumption]
| intros; eapply Uvqc.L_WLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF.
first [ intro; apply Uvqc.L_WIDTH; first [eassumption]
| intros; eapply Uvqc.L_WIDTH; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PLOOP : S_PLOOP.
Proof using HF.
first [ apply UvpC.L_PLOOP; first [eassumption]
| intros; eapply UvpC.L_PLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF.
first [ intro; apply UvpC.L_PREC; first [eassumption]
| intros; eapply UvpC.L_PREC; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATE : S_STATE.
Proof using HF.
first [ apply ULNO.L_STATE; first [eassumption]
| intros; eapply ULNO.L_STATE; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_STATEL : S_STATEL.
Proof using HF.
first [ apply ULNO.L_STATEL; first [eassumption]
| intros; eapply ULNO.L_STATEL; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DIR : S_DIR.
Proof using HF.
first [ apply UOlm.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL]
| intros; eapply UOlm.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
first [ apply U7TP.L_T6; first [eassumption]
| intros; eapply U7TP.L_T6; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UjBD.L_T5; first [eassumption | eexact L_T6]
| intros; eapply UjBD.L_T5; first [eassumption | eexact L_T6] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UelO.L_T4; first [eassumption | eexact L_T5]
| intros; eapply UelO.L_T4; first [eassumption | eexact L_T5] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UWtF.L_T3; first [eassumption | eexact L_T4]
| intros; eapply UWtF.L_T3; first [eassumption | eexact L_T4] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UbQl.L_T2; first [eassumption | eexact L_T3]
| intros; eapply UbQl.L_T2; first [eassumption | eexact L_T3] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UndM.L_T1; first [eassumption | eexact L_T2]
| intros; eapply UndM.L_T1; first [eassumption | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UqnK.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply UqnK.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC2 : S_INTC2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UwkO.L_INTC2; first [eassumption | eexact L_TAIL]
| intros; eapply UwkO.L_INTC2; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_INTC : S_INTC.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply U8ql.L_INTC; first [eassumption | eexact L_INTC2]
| intros; eapply U8ql.L_INTC; first [eassumption | eexact L_INTC2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI.
first [ apply U0UD.L_DLOOP; first [eassumption]
| intros; eapply U0UD.L_DLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UvII.L_FMTU2; first [eassumption | eexact L_INTC]
| intros; eapply UvII.L_FMTU2; first [eassumption | eexact L_INTC] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UvEw.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
| intros; eapply UvEw.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply U7u1.L_CV_D; first [eassumption | eexact L_FMTU]
| intros; eapply U7u1.L_CV_D; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_U : S_CV_U.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UBnL.L_CV_U; first [eassumption | eexact L_FMTU]
| intros; eapply UBnL.L_CV_U; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI.
first [ apply UDkt.L_XLOOP; first [eassumption]
| intros; eapply UDkt.L_XLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UG5K.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
| intros; eapply UG5K.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply Uvf1.L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply Uvf1.L_CV_S; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ.
first [ apply UImA.L_CV_FP; first [eassumption]
| intros; eapply UImA.L_CV_FP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CV_C : S_CV_C.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply UpXF.L_CV_C; first [eassumption | eexact L_TAIL]
| intros; eapply UpXF.L_CV_C; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ apply Uk39.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C]
| intros; eapply Uk39.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI.
first [ intro; apply UoJQ.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply UoJQ.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_P1 : S_P1.
Proof using A0 HA HF LO.
first [ apply UmjR.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
| intros; eapply UmjR.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F.
first [ apply U68U.L_PRO; first [eassumption]
| intros; eapply U68U.L_PRO; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.

Let HS_PRO := L_PRO.
Let HS_HEAD := L_HEAD.
Let HS_P1 := L_P1.

Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
let _ := ctx_all in
SINK m0 st -> stk rsegs m0 lo q -> mem_inv rsegs m0 -> bytes_at rsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
rw_cells rsegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
(0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
implM rsegs (printf_model OUT OUTFP fmt args) st POST
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0x55624) fc0 None m0 (seg_rom rsegs)).
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
assert (APC : rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
{ eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
stmt (HS_HEAD (length fmt)) as NXH.
jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
[ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
let _ := ctx_all in
stk rsegs m0 lo q -> mem_inv rsegs m0 -> bytes_at rsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
pass1_ok fmt = true ->
evt rsegs (POST1 0)
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 0x55624) fc0 None m0 (seg_rom rsegs)).
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
{ apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
rewrite Z_to_bv_bv_unsigned.
repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
pose proof (L_CORE1 416216 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
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
Qed.
End Mq0.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC00.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1ti. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UCd0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UCd0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNQl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uhxl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uhxl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKaC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKaC.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x524d8%Z.
Definition w_21 := 0xfffc4717%Z.
Definition w_23 := 0x01470713%Z.
Definition w_64 := 0x00046717%Z.
Definition w_71 := 0x8bb74883%Z.
Definition w_85 := 0x00046597%Z.
Definition w_86 := 0x94c58593%Z.
Definition w_89 := 0x7150d0ef%Z.
Definition w_95 := 0x00046517%Z.
Definition w_96 := 0x92450513%Z.
Definition w_97 := 0x17c0e0ef%Z.
Definition w_99 := 0xcfcfe0ef%Z.
Definition w_104 := 0x59d010ef%Z.
Definition hi_21 := (Z_to_bv 20 1048516).
Definition hi_64 := (Z_to_bv 20 70).
Definition hi_85 := (Z_to_bv 20 70).
Definition hi_95 := (Z_to_bv 20 70).
Definition lo_23 := (Z_to_bv 12 20).
Definition lo_71 := (Z_to_bv 12 2235).
Definition lo_86 := (Z_to_bv 12 2380).
Definition lo_96 := (Z_to_bv 12 2340).
Definition joff_89 := (Z_to_bv 21 57108).
Definition joff_97 := (Z_to_bv 21 57724).
Definition joff_99 := (Z_to_bv 21 2090236).
Definition joff_104 := (Z_to_bv 21 7580).
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rsysret_entry := UKNz.rsysret_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Definition rlock_entry := UKNz.rlock_entry.
Definition runlock_entry := UKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x524d8 (Qy8Z.Mq3.free_code 0xfffc4717%Z 0x01470713%Z 0x00046717%Z 0x8bb74883%Z 0x00046597%Z 0x94c58593%Z 0x7150d0ef%Z 0x00046517%Z 0x92450513%Z 0x17c0e0ef%Z 0xcfcfe0ef%Z 0x59d010ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x524d8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x524d8 /\ 0x524d8 + 460 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q5m9.Mqa.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition rmunmap_spec := ltac:(pose proof (@rmunmap_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition roracle_ok_pres := @roracle_ok_pres.
Definition rfree_fp_lt := @rfree_fp_lt.
Definition rntf_implT := @rntf_implT.
Definition sllw1_word' := ltac:(pose proof (@sllw1_word') as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition rget_meta_spec := ltac:(pose proof (@rget_meta_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition runlock_spec := ltac:(pose proof (@runlock_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mqa.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mqa.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
(st' : mstate) (s' : PState) : machine_state -> Prop :=
fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st' m'
/\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 490332 <= a < 490336) m m'
/\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
/\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
/\ c_brk (ctx st') = c_brk (ctx st)
/\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

#[using="Type"] Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> 490332 <= a < 490336 -> ~ rfree_fp st lo sp a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.rerrno_not_free_fp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.rerrno_not_free_fp)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q5m9.Mqa.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Q5m9.Mqa.rimplT) (@Uv2Y.rimplT) Q6nq.gwt_nil)))).
#[using="Type"] Lemma rmrep_after_munmap : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mqa.rmrep_after_munmap) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([490332; 490336]%Z : list Z) '(Q6nq.gwt_unf (@RERRNO) (Q6nq.gwt_def (@Q5m9.Mqa.rfree_end) (@rfree_end) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.rmrep_after_munmap) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.rmrep_after_munmap)]. Qed.

#[using="Type"] Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.byte_zero_list) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.byte_zero_list)]. Qed.

#[using="Type"] Lemma bytes4_range : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mqa.bytes4_range) [] '([256; 65536; 16777216]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_def (@Q5m9.Mqa.rfree_end) (@rfree_end) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.bytes4_range) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.bytes4_range)]. Qed.

#[using="Type"] Lemma le4_of_bytes : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mqa.le4_of_bytes) [] '([256; 65536; 16777216]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_def (@Q5m9.Mqa.rfree_end) (@rfree_end) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.le4_of_bytes) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.le4_of_bytes)]. Qed.

#[using="Type"] Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.shiftr5_ge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.shiftr5_ge)]. Qed.
#[using="Type"] Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.shiftr5_lt) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.shiftr5_lt)]. Qed.
#[using="Type"] Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.shiftr5_range) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.shiftr5_range)]. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mqa.rlibc_free_implT) [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([(-8192)]%Z : list Z) '(Q6nq.gwt_zc rfree_entry (Q6nq.gwt_zc UNIT (Q6nq.gwt_def (@Q5m9.Mqa.rfree_end) (@rfree_end) gwt_X)))).
Proof using LO TP. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.rlibc_free_implT) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mqa.rlibc_free_implT)]. Qed.
End FREE.

End RC__1.
