(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefAllow PmRefNonneg PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA PsoInstXB PsoSemXB PsoKnXB ParseSomeChkXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import SmallPtXBW PsoInstXBW RelObsXB PsoWTabXB PsoBaseXBW PsoXiXBW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSOWK.
Section K.
Context {SCFG_P : ScfgP}.
Variable I : PSOIW.inst.
Local Abbreviation L := (PSOIW.iL I).
Local Abbreviation CLA := (PSOIW.iCLA I).
Local Abbreviation gx := (PSOIW.ig1 I).
Local Abbreviation eg0 := (PSOIW.ieg I).

(* [comment removed for export] *)
Lemma wroom_bind : forall g q k, PMXAW.wroom CLA g (PMR.q_evs (PMR.bind q k)) (PMR.q_al (PMR.bind q k)) ->
  (PMR.q_code q = 0 -> 0 <= PMR.q_al (k (PMR.q_c q) (PMR.q_w q))) -> PMXAW.wroom CLA g (PMR.q_evs q) (PMR.q_al q).
Proof.
  intros g q k H Hk. unfold PMR.bind in H. destruct (Z.eqb_spec (PMR.q_code q) 0) as [Hc|Hc]; cbn [negb] in H; [|exact H].
  cbn [PMR.q_evs PMR.q_al] in H. apply (PMXAW.wroom_app CLA g _ _ _ _ H); [apply PMXAW.ind_run_nonneg | exact (Hk Hc)].
Qed.

(* [comment removed for export] *)
Lemma room_loop : forall c w evs al, PMRF.hreach (PSOX.c0 I) (PSOX.w0 I) c w evs al -> PSOX.SYNC I evs al -> PMRN.SIq c ->
  forall F, Z.of_nat F > PMRF.phi c w -> PMXAW.wroom CLA gx (PMR.q_evs (PMR.loop F c w)) (PMR.q_al (PMR.loop F c w)).
Proof.
  intros c w evs al [SOK HR] [Hes (pay & Hpay & Hlen)] SI F HF.
  pose proof (PSOIW.iHW4 I) as W4. unfold PMXAW.wroomr in W4. cbn [PMW.rm_step PMRXA.the_rmA PMR.rstep] in W4. unfold PMW.inp_win in W4.
  unfold PSOX.c0, PSOX.w0 in HR. rewrite (HR F HF) in W4. unfold PMR.r_of, PMRF.pre in W4. cbn [PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in W4.
  exact (PMXAW.wroom_shift CLA eg0 gx evs _ al _ pay W4 Hes Hlen Hpay).
Qed.

(* [comment removed for export] *)
Lemma room_iter : forall c b r evs al, PMRF.hreach (PSOX.c0 I) (PSOX.w0 I) c (b :: r) evs al -> PSOX.SYNC I evs al -> PMRN.SIq c -> PMR.c_more c = true ->
  PMXAW.wroom CLA gx (PMR.q_evs (PMR.iter c b r)) (PMR.q_al (PMR.iter c b r)).
Proof.
  intros c b r evs al HR SY SI Hm.
  set (F := Datatypes.S (Z.to_nat (PMRF.phi c (b :: r)))).
  assert (HF : Z.of_nat (Datatypes.S F) > PMRF.phi c (b :: r)) by (unfold F; pose proof (PMRF.phi_nonneg c (b :: r)); rewrite Nat2Z.inj_succ, Nat2Z.inj_succ, Z2Nat.id; lia).
  pose proof (room_loop c (b :: r) evs al HR SY SI (Datatypes.S F) HF) as W. rewrite (PMRF.loop_step F c b r Hm) in W.
  apply (wroom_bind gx _ _ W). intros _. exact (proj1 (PMRN.loop_alnn F _ _ (proj2 (PMRN.iter_alnn c b r SI Hm)))).
Qed.

(* [comment removed for export] *)
Lemma room_lit : forall c b r evs al (ev : PMES.eev),
  PMRF.hreach (PSOX.c0 I) (PSOX.w0 I) c (b :: r) evs al -> PSOX.SYNC I evs al -> PMRN.SIq c -> PMR.c_more c = true ->
  PMR.dispatch (PMR.c_st c) (PMR.top c) b = PMR.ALitDone -> (ev = PMES.EvNull \/ exists bb, ev = PMES.EvBool bb) ->
  (PSOIW.ieroomA I) gx ev.
Proof.
  intros c b r evs al ev HR SY SI Hm HD Hev.
  pose proof (room_iter c b r evs al HR SY SI Hm) as W. unfold PMR.iter in W. rewrite HD in W. cbn [PMR.act_run] in W. unfold PMR.lit_done in W. cbn [PMR.q_evs PMR.q_al] in W.
  apply (SPTAW.room_first (PSOIW.ieroomA I) CLA gx PMW.EkLit [] PMR.AL_LIT ev (PSOIW.iROOMW I) W);
    [destruct Hev as [-> | [bb ->]]; reflexivity | destruct Hev as [-> | [bb ->]]; [pose proof PMXAW.pay_hi_null | pose proof (PMXAW.pay_hi_bool bb)]; unfold PMR.AL_LIT; lia].
Qed.
End K.
End PSOWK.
