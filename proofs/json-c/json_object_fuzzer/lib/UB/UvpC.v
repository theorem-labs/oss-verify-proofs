(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTIW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTIW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8Ie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Ie.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzOj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbz7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qqmw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqmw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTru.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require US6h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import US6h.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq1.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x55624%Z.
Definition w_22 := 0x00010517%Z.
Definition w_25 := 0x35453603%Z.
Definition w_81 := 0xfb8ff0ef%Z.
Definition w_281 := 0xfffc1697%Z.
Definition w_282 := 0xc9068693%Z.
Definition w_332 := 0xfffc1597%Z.
Definition w_333 := 0xa7c58593%Z.
Definition w_360 := 0xfffbb597%Z.
Definition w_362 := 0x92f58593%Z.
Definition w_371 := 0xfffbb517%Z.
Definition w_372 := 0x90350513%Z.
Definition w_378 := 0xfffbd517%Z.
Definition w_379 := 0x76f50b93%Z.
Definition w_381 := 0xf49fa0ef%Z.
Definition w_383 := 0xf4dfa0ef%Z.
Definition w_389 := 0x1ec0a0ef%Z.
Definition w_395 := 0xfffbb617%Z.
Definition w_396 := 0x8a360613%Z.
Definition w_412 := 0xfffbb597%Z.
Definition w_413 := 0x85f58593%Z.
Definition w_426 := 0xfffc1597%Z.
Definition w_427 := 0x9e458593%Z.
Definition w_438 := 0xfffba597%Z.
Definition w_439 := 0x7f758893%Z.
Definition w_453 := 0xfffba517%Z.
Definition w_454 := 0x7bb50513%Z.
Definition w_467 := 0xfffba597%Z.
Definition w_468 := 0x78358713%Z.
Definition w_473 := 0xfffbd697%Z.
Definition w_474 := 0x71868693%Z.
Definition w_530 := 0x8b4ff0ef%Z.
Definition w_533 := 0xfffba597%Z.
Definition w_534 := 0x67b58593%Z.
Definition w_543 := 0xfffba597%Z.
Definition w_545 := 0x65358893%Z.
Definition w_627 := 0x1c9090ef%Z.
Definition w_639 := 0xf01fe0ef%Z.
Definition w_648 := 0xeddfe0ef%Z.
Definition w_655 := 0xec1fe0ef%Z.
Definition w_668 := 0x125090ef%Z.
Definition w_680 := 0xe5dfe0ef%Z.
Definition w_689 := 0xe39fe0ef%Z.
Definition w_701 := 0x0a1090ef%Z.
Definition w_713 := 0xdd9fe0ef%Z.
Definition w_722 := 0xdb5fe0ef%Z.
Definition w_729 := 0xd99fe0ef%Z.
Definition w_742 := 0x7fc090ef%Z.
Definition w_754 := 0xd35fe0ef%Z.
Definition w_762 := 0xd15fe0ef%Z.
Definition w_798 := 0x8c5fa0ef%Z.
Definition w_883 := 0xf70fa0ef%Z.
Definition w_907 := 0xbd5fa0ef%Z.
Definition hi_22 := (Z_to_bv 20 16).
Definition hi_281 := (Z_to_bv 20 1048513).
Definition hi_332 := (Z_to_bv 20 1048513).
Definition hi_360 := (Z_to_bv 20 1048507).
Definition hi_371 := (Z_to_bv 20 1048507).
Definition hi_378 := (Z_to_bv 20 1048509).
Definition hi_395 := (Z_to_bv 20 1048507).
Definition hi_412 := (Z_to_bv 20 1048507).
Definition hi_426 := (Z_to_bv 20 1048513).
Definition hi_438 := (Z_to_bv 20 1048506).
Definition hi_453 := (Z_to_bv 20 1048506).
Definition hi_467 := (Z_to_bv 20 1048506).
Definition hi_473 := (Z_to_bv 20 1048509).
Definition hi_533 := (Z_to_bv 20 1048506).
Definition hi_543 := (Z_to_bv 20 1048506).
Definition lo_25 := (Z_to_bv 12 852).
Definition lo_282 := (Z_to_bv 12 3216).
Definition lo_333 := (Z_to_bv 12 2684).
Definition lo_362 := (Z_to_bv 12 2351).
Definition lo_372 := (Z_to_bv 12 2307).
Definition lo_379 := (Z_to_bv 12 1903).
Definition lo_396 := (Z_to_bv 12 2211).
Definition lo_413 := (Z_to_bv 12 2143).
Definition lo_427 := (Z_to_bv 12 2532).
Definition lo_439 := (Z_to_bv 12 2039).
Definition lo_454 := (Z_to_bv 12 1979).
Definition lo_468 := (Z_to_bv 12 1923).
Definition lo_474 := (Z_to_bv 12 1816).
Definition lo_534 := (Z_to_bv 12 1659).
Definition lo_545 := (Z_to_bv 12 1619).
Definition joff_81 := (Z_to_bv 21 2095032).
Definition joff_381 := (Z_to_bv 21 2076488).
Definition joff_383 := (Z_to_bv 21 2076492).
Definition joff_389 := (Z_to_bv 21 41452).
Definition joff_530 := (Z_to_bv 21 2093236).
Definition joff_627 := (Z_to_bv 21 39368).
Definition joff_639 := (Z_to_bv 21 2092800).
Definition joff_648 := (Z_to_bv 21 2092764).
Definition joff_655 := (Z_to_bv 21 2092736).
Definition joff_668 := (Z_to_bv 21 39204).
Definition joff_680 := (Z_to_bv 21 2092636).
Definition joff_689 := (Z_to_bv 21 2092600).
Definition joff_701 := (Z_to_bv 21 39072).
Definition joff_713 := (Z_to_bv 21 2092504).
Definition joff_722 := (Z_to_bv 21 2092468).
Definition joff_729 := (Z_to_bv 21 2092440).
Definition joff_742 := (Z_to_bv 21 38908).
Definition joff_754 := (Z_to_bv 21 2092340).
Definition joff_762 := (Z_to_bv 21 2092308).
Definition joff_798 := (Z_to_bv 21 2074820).
Definition joff_883 := (Z_to_bv 21 2074480).
Definition joff_907 := (Z_to_bv 21 2075604).
Definition G_102fd := 0x104f3%Z.
Definition G_10741 := 0x1337b%Z.
Definition G_107e0 := 0x134a0%Z.
Definition G_11778 := 0x165d0%Z.
Definition G_11858 := 0x166b0%Z.
Definition G_118c0 := 0x16718%Z.
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_194bc := 0x50b60%Z.
Definition e_194c8 := 0x50b6c%Z.
Definition e_197bc := 0x51024%Z.
Definition e_fwritex := 0x54f20%Z.
Definition e_memset := 0x5f9b8%Z.
Definition e_2596c := 0x5fe24%Z.
Definition e_memchr := 0x5f33c%Z.
Definition jt_11778_o1504 := 259636%Z.
Definition jt_11778_o1432 := 259564%Z.
Definition jt_11778_o1800 := 259932%Z.
Definition jt_11778_o1744 := 259876%Z.
Definition jt_11778_o1864 := 259996%Z.
Definition jt_11778_o1352 := 259484%Z.
Lemma CODE : CodeAt.code_at rsegs 0x55624 (Q8l1.Mq1.printf_core_code 0x00010517%Z 0x35453603%Z 0xfb8ff0ef%Z 0xfffc1697%Z 0xc9068693%Z 0xfffc1597%Z 0xa7c58593%Z 0xfffbb597%Z 0x92f58593%Z 0xfffbb517%Z 0x90350513%Z 0xfffbd517%Z 0x76f50b93%Z 0xf49fa0ef%Z 0xf4dfa0ef%Z 0x1ec0a0ef%Z 0xfffbb617%Z 0x8a360613%Z 0xfffbb597%Z 0x85f58593%Z 0xfffc1597%Z 0x9e458593%Z 0xfffba597%Z 0x7f758893%Z 0xfffba517%Z 0x7bb50513%Z 0xfffba597%Z 0x78358713%Z 0xfffbd697%Z 0x71868693%Z 0x8b4ff0ef%Z 0xfffba597%Z 0x67b58593%Z 0xfffba597%Z 0x65358893%Z 0x1c9090ef%Z 0xf01fe0ef%Z 0xeddfe0ef%Z 0xec1fe0ef%Z 0x125090ef%Z 0xe5dfe0ef%Z 0xe39fe0ef%Z 0x0a1090ef%Z 0xdd9fe0ef%Z 0xdb5fe0ef%Z 0xd99fe0ef%Z 0x7fc090ef%Z 0xd35fe0ef%Z 0xd15fe0ef%Z 0x8c5fa0ef%Z 0xf70fa0ef%Z 0xbd5fa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x55624 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x55624 /\ 0x55624 + 3632 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

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

Local Notation W := (US6h.W Fp B BS q lo AP).
Local Notation hi_cells := (US6h.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (US6h.lo_cells AP nla nlt).
Local Notation finv := (US6h.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (US6h.fmt_rng fmt HF).
Local Notation implM_eq_ms := (US6h.implM_eq_ms (St:=St)).
Local Notation sink_store := (US6h.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (US6h.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (US6h.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_PLOOP := (US6h.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (US6h.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (US6h.body_loc Fp B BS q lo).
Local Notation tregs := (US6h.tregs Fp q gp tp A).
Local Notation tinv := (US6h.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Ltac zlg := lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => idtac | nat => idtac | N => idtac | _ => fail end | _ => idtac end; zl.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zlg | progress f_equal ].
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
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zlg | progress f_equal ].

Lemma L_PLOOP : S_PLOOP.
Proof using HF. ltac2:(GwEq.gw_rw [[@gw_eq_S_PLOOP__3; @gw_eq_S_PLOOP__2; @gw_eq_S_PLOOP]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mqb.L_PLOOP) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mqb.L_PLOOP)]. Qed.

Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF. ltac2:(GwEq.gw_rw [[@gw_eq_S_PLOOP__3; @gw_eq_S_PLOOP__2; @gw_eq_S_PLOOP]; [@gw_eq_S_PREC__3; @gw_eq_S_PREC__2; @gw_eq_S_PREC]]); first [GwApply.gw_by_name GwI.segs (@QZxv.Mqb.L_PREC) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QZxv.Mqb.L_PREC)]. Qed.
End PrintfCore.
