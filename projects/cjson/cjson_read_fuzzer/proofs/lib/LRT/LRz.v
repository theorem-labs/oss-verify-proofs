(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cfg.
Module LNodes.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition jself (ms : machine_state) : Prop :=
  ms_svc_pending ms = None /\ fetch_word segs (ms_pc ms) = Some (Z_to_bv 32 0x6f).

Lemma jself_MS : forall R F pc fc rv m ro,
  fetch_word segs pc = Some (Z_to_bv 32 0x6f) -> jself (MS R F pc fc rv m ro).
Proof. intros. split; [reflexivity| exact H]. Qed.

Lemma to_jself_jself : forall ms mo, jself ms -> to_jself segs ms mo.
Proof. intros ms mo [Hsvc Hf]. apply tj_here; [exact Hsvc| exact Hf]. Qed.

Lemma to_spin_jself : forall ms mo, jself ms -> to_spin segs ms mo.
Proof. intros ms mo Hj. apply to_jself_to_spin. apply to_jself_jself. exact Hj. Qed.

(* [comment removed for export] *)
Lemma lspin_of_msteps : forall ms ms', msteps segs ms ms' -> forall g mo mat mr,
  LINV segs g mo mat (ms_mem ms) mr -> jself ms' ->
  to_jself segs (msw ms mr) (real mo mat).
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intros g mo mat mr HI Hj.
  - apply to_jself_jself. destruct Hj as [A B]. split; [rewrite ms_svc_pending_msw; exact A| rewrite ms_pc_msw; exact B].
  - destruct (laccount_step segs g mo mat ms mr ms1 HI Hstep) as (mr1 & acc & _ & Hacc & HI1). cbv zeta in Hacc, HI1.
    eapply tj_step; [rewrite ms_svc_pending_msw; exact Hsvc| exact Hacc| eapply IH; [exact HI1| exact Hj]].
Qed.

Lemma lspin_of_evt : forall ms g mo mat mr,
  evt segs jself ms -> LINV segs g mo mat (ms_mem ms) mr ->
  jspinning segs (mkCfg (msw ms mr) (real mo mat)).
Proof.
  intros ms g mo mat mr (ms' & Hms & Hj) HI. split; cbn.
  - eapply lspin_of_msteps; eassumption.
  - rewrite real_halted. exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nret_msw : forall ms mr eff,
  nret (msw ms mr) eff = msw (nret ms eff) (ms_mem (nret (msw ms mr) eff)).
Proof. intros [] mr eff; reflexivity. Qed.

Lemma ms_regs_nret_msw : forall ms mr eff, ms_regs (nret (msw ms mr) eff) = ms_regs (nret ms eff).
Proof. intros [] mr eff; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mem_nret : forall ms eff,
  ms_mem (nret ms eff) =
  apply_writes (apply_copies (ms_mem ms) (apply_zeros (apply_unmaps (ms_mem ms) (eff_unmaps eff)) (eff_zeros eff)) (eff_copies eff))
               (eff_writes eff).
Proof.
  intros [] eff. unfold nret, advance_past_svc, apply_effect, set_reg.
  assert (E : bv_eqb (10 : bv 5) 0 = false) by reflexivity. rewrite E. reflexivity.
Qed.

Lemma mem_nret_plain : forall ms r, ms_mem (nret ms (mkEffect r [] [])) = ms_mem ms.
Proof. intros. rewrite mem_nret. reflexivity. Qed.

Lemma mem_nret_zeros : forall ms r z zs, ms_mem (nret ms (mkEffect r [] (z :: zs))) = apply_zeros (ms_mem ms) (z :: zs).
Proof. intros. rewrite mem_nret. reflexivity. Qed.

Lemma mem_nret_unmaps : forall ms r u us, ms_mem (nret ms (mkEffectU r [] [] (u :: us) [] [])) = apply_unmaps (ms_mem ms) (u :: us).
Proof. intros. rewrite mem_nret. reflexivity. Qed.

Lemma mem_nret_zeros_U : forall ms r z zs, ms_mem (nret ms (mkEffectU r [] (z :: zs) [] [] [])) = apply_zeros (ms_mem ms) (z :: zs).
Proof. intros. rewrite mem_nret. reflexivity. Qed.

Lemma msw_nret_self : forall ms eff, msw (nret ms eff) (ms_mem (nret ms eff)) = nret ms eff.
Proof. intros. apply msw_self. Qed.

Lemma a0_nret : forall ms eff, reg_get (ms_regs (nret ms eff)) 10 = eff_ret eff.
Proof.
  intros [] eff. unfold nret, advance_past_svc, apply_effect, set_reg.
  assert (E : bv_eqb (10 : bv 5) 0 = false) by reflexivity. rewrite E. cbn.
  unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
Definition outcome_ok (P : machine_state -> Model -> lghost -> Prop) (sp : word -> bool)
    (ms : machine_state) (mo : Model) (mr : mem) (o : outcome SyscallEffect) : Prop :=
  exists eff mo' g' mv' mat',
    o = Ok eff (real mo' mat') [] /\
    syscall_effect_accesses eff = [] /\
    vm_only mo mo' /\
    LINV segs g' mo' mat' mv' (ms_mem (nret (msw ms mr) eff)) /\
    ((sp (eff_ret eff) = true /\ evt segs jself (msw (nret ms eff) mv'))
     \/ (sp (eff_ret eff) = false /\ LSCPS segs P (msw (nret ms eff) mv') mo' g')).

Definition spur_ok (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists eff mo' evs, o = Ok eff mo' evs /\ spurious_refusal_cfg ACFG i m eff /\ m_halted mo' = None.

Theorem lscps_sysnode : forall (P : machine_state -> Model -> lghost -> Prop) (sp : word -> bool) ms mo g x8,
  ms_svc_pending ms = Some x8 ->
  (forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
     (forall o, syscall_spec (sys_input segs (msw ms mr) x8) (real mo mat) o ->
        outcome_ok P sp ms mo mr o \/ spur_ok (sys_input segs (msw ms mr) x8) (real mo mat) o)
     /\ (exists eff mo1 evs, syscall_spec (sys_input segs (msw ms mr) x8) (real mo mat) (Ok eff mo1 evs)
                          /\ ~ spurious_refusal_cfg ACFG (sys_input segs (msw ms mr) x8) (real mo mat) eff
                          /\ sp (eff_ret eff) = false)) ->
  LSCPS segs P ms mo g.
Proof.
  intros P sp ms mo g x8 Hsvc H mr mat HI T K.
  destruct (H mr mat HI) as [Hall (eff0 & mo10 & evs0 & Hspec0 & Hns0 & Hsp0)].
  pose proof (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI)) as Hh.
  assert (Hhr : m_halted (real mo mat) = None) by (rewrite real_halted; exact Hh).
  assert (Hsvc' : ms_svc_pending (msw ms mr) = Some x8) by (rewrite ms_svc_pending_msw; exact Hsvc).
  (* [comment removed for export] *)
  set (c := mkCfg (msw ms mr) (real mo mat)).
  (* [comment removed for export] *)
  assert (STEP : forall eff mo' mat', syscall_spec (sys_input segs (msw ms mr) x8) (real mo mat) (Ok eff (real mo' mat') []) ->
            ~ spurious_refusal_cfg ACFG (sys_input segs (msw ms mr) x8) (real mo mat) eff ->
            syscall_effect_accesses eff = [] -> m_halted mo' = None ->
            sstep_cfg segs ACFG c [] (SNext (mkCfg (nret (msw ms mr) eff) (real mo' mat')))).
  { intros eff mo' mat' Hs Hns Ha Hh'. unfold c, nret.
    eapply sstep_cfg_syscall; [exact Hhr| exact Hsvc'| exact Hs| exact Hns| rewrite real_halted; exact Hh'|].
    rewrite Ha. apply materialize_model_accesses_nil. }
  (* [comment removed for export] *)
  assert (INV : forall e X, sstep_cfg segs ACFG c e X ->
            e = [] /\ exists eff mo' g' mv' mat', X = SNext (mkCfg (nret (msw ms mr) eff) (real mo' mat')) /\
              vm_only mo mo' /\ LINV segs g' mo' mat' mv' (ms_mem (nret (msw ms mr) eff)) /\
              ((sp (eff_ret eff) = true /\ evt segs jself (msw (nret ms eff) mv'))
               \/ (sp (eff_ret eff) = false /\ LSCPS segs P (msw (nret ms eff) mv') mo' g'))).
  { intros e X Hss.
    destruct (sstep_cfg_sys_inv segs ACFG (msw ms mr) (real mo mat) x8 e X Hsvc' Hss)
      as [(eff & mo1 & evs1 & Hs & Hns & Hh1 & Hm)
         | [(eff & mo1 & evs1 & code & Hs & Hh1 & _ & -> & ->)
         | [(eff & mo1 & evs1 & sig & Hs & Hk & -> & ->) | (Hs & -> & ->)]]].
    - destruct (Hall _ Hs) as [(eff' & mo' & g' & mv' & mat' & Heq & Ha & HV & HI' & HK) | (eff' & mo' & evs' & Heq & Hsp & _)].
      + apply Ok_inj in Heq as (<- & -> & ->). rewrite Ha, materialize_model_accesses_nil in Hm. cbv beta iota in Hm.
        destruct Hm as [-> ->]. split; [reflexivity|]. exists eff, mo', g', mv', mat'. auto.
      + exfalso. apply Ok_inj in Heq as (<- & _ & _). exact (Hns Hsp).
    - exfalso. destruct (Hall _ Hs) as [(eff' & mo' & g' & mv' & mat' & Heq & _ & _ & HI' & _) | (eff' & mo' & evs' & Heq & _ & Hh')].
      + apply Ok_inj in Heq as (<- & -> & ->). rewrite real_halted, (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI')) in Hh1. discriminate.
      + apply Ok_inj in Heq as (<- & -> & ->). rewrite Hh' in Hh1. discriminate.
    - exfalso. destruct (Hall _ Hs) as [(eff' & mo' & g' & mv' & mat' & Heq & _ & _ & HI' & _) | (eff' & mo' & evs' & Heq & _ & Hh')].
      + apply Ok_inj in Heq as (<- & -> & ->).
        assert (Hh2 : m_halted (real mo' mat') = None) by (rewrite real_halted; exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI'))).
        rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
      + apply Ok_inj in Heq as (<- & -> & ->). rewrite (m_killed_of_m_halted_none _ Hh') in Hk. discriminate.
    - exfalso. destruct (Hall _ Hs) as [(eff' & mo' & g' & mv' & mat' & Heq & _) | (eff' & mo' & evs' & Heq & _)]; discriminate. }
  (* [comment removed for export] *)
  destruct (Hall _ Hspec0) as [(eff0' & mo0' & g0' & mv0' & mat0' & Heq0 & Ha0 & HV0 & HI0 & _) | (eff0' & mo0' & evs0' & Heq0 & Hsp0' & _)];
    [| exfalso; apply Ok_inj in Heq0 as (<- & _ & _); exact (Hns0 Hsp0')].
  apply Ok_inj in Heq0 as (<- & -> & ->).
  pose (I := {X : config | sstep_cfg segs ACFG c [] (SNext X)}).
  assert (i0 : I).
  { exists (mkCfg (nret (msw ms mr) eff0) (real mo0' mat0')). apply STEP; [exact Hspec0| exact Hns0| exact Ha0|].
    exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI0)). }
  apply (srz_silent_spin segs c I (fun i => proj1_sig i)
           (fun i => sp (reg_get (ms_regs (cfg_ms (proj1_sig i))) 10)) T
           (exist _ (mkCfg (nret (msw ms mr) eff0) (real mo0' mat0')) (STEP _ _ _ Hspec0 Hns0 Ha0 (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI0))))).
  - (* [comment removed for export] *)
    split.
    + intros [X HX]. exact HX.
    + intros e X Hss. destruct (INV e X Hss) as (-> & eff & mo' & g' & mv' & mat' & -> & _).
      exists (exist _ (mkCfg (nret (msw ms mr) eff) (real mo' mat')) Hss). split; reflexivity.
  - (* [comment removed for export] *)
    cbn [proj1_sig cfg_ms]. rewrite ms_regs_nret_msw, a0_nret. exact Hsp0.
  - (* [comment removed for export] *)
    intros [X HX] HspX. cbn [proj1_sig] in *.
    destruct (INV _ _ HX) as (_ & eff & mo' & g' & mv' & mat' & HeqX & HV & HI' & HK). injection HeqX as ->.
    cbn [cfg_ms] in HspX. rewrite ms_regs_nret_msw, a0_nret in HspX.
    destruct HK as [[_ He] | [Hf _]]; [| congruence].
    rewrite nret_msw, <- (msw_msw (nret ms eff) mv'). eapply lspin_of_evt; [exact He|]. cbn [ms_mem msw]. exact HI'.
  - (* [comment removed for export] *)
    intros [X HX] HspX. cbn [proj1_sig] in *.
    destruct (INV _ _ HX) as (_ & eff & mo' & g' & mv' & mat' & HeqX & HV & HI' & HK). injection HeqX as ->.
    cbn [cfg_ms] in HspX. rewrite ms_regs_nret_msw, a0_nret in HspX.
    destruct HK as [[Ht _] | [_ HL]]; [congruence|].
    rewrite nret_msw, <- (msw_msw (nret ms eff) mv'). apply (HL _ mat'); [cbn [ms_mem msw]; exact HI'|].
    intros ms2 mo2 g2 mr2 mat2 HP HI2 HV2. eapply K; [exact HP| exact HI2| eapply vm_only_trans; eassumption].
Qed.

End WithSegs.
End LNodes.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ExitSim ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil PropExec MState Mem Exec Frame ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
Import LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Strategy 1000 [path_max].
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LRZ (ms : machine_state) (mo : Model) (g : lghost) (T : TSet) : Prop :=
  forall mr mat, LINV segs g mo mat (ms_mem ms) mr -> srealizes segs (mkCfg (msw ms mr) (real mo mat)) T.

Lemma lrz_conseq : forall ms mo g T T', LRZ ms mo g T -> t_eq T T' -> LRZ ms mo g T'.
Proof. intros ms mo g T T' H Heq mr mat HI. eapply srz_conseq; [apply H; exact HI| exact Heq]. Qed.

Lemma lrz_eq : forall ms ms' mo g T, ms = ms' -> LRZ ms' mo g T -> LRZ ms mo g T.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma lrz_evt : forall (Q : machine_state -> Prop) ms mo g T,
  evt segs Q ms -> (forall ms', Q ms' -> LRZ ms' mo g T) -> LRZ ms mo g T.
Proof.
  intros Q ms mo g T (ms' & Hms & HQ) K mr mat HI.
  eapply srz_lmsteps; [exact Hms| exact HI|]. intros mr' mat' HI'. apply (K ms' HQ mr' mat' HI').
Qed.

Lemma lrz_step_evt : forall ms mo g T, evt segs (fun ms' => LRZ ms' mo g T) ms -> LRZ ms mo g T.
Proof. intros ms mo g T He. eapply lrz_evt; [exact He|]. intros ms' H; exact H. Qed.

(* [comment removed for export] *)
Lemma lrz_lscps : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g T,
  LSCPS segs P ms mo g -> (forall ms' mo' g', P ms' mo' g' -> LRZ ms' mo' g' T) -> LRZ ms mo g T.
Proof.
  intros P ms mo g T H K mr mat HI. apply (H mr mat HI T). intros ms' mo' g' mr' mat' HP HI' _. apply (K _ _ _ HP _ _ HI').
Qed.

(* [comment removed for export] *)
Lemma lrz_assume : forall ms mo g T,
  (no_wx segs -> LOK segs mo -> BINV mo g -> LRZ ms mo g T) -> LRZ ms mo g T.
Proof.
  intros ms mo g T H mr mat HI.
  apply (H (LINV_no_wx _ _ _ _ _ _ HI) (LINV_LOK _ _ _ _ _ _ HI) (LINV_BINV _ _ _ _ _ _ HI) mr mat HI).
Qed.

(* [comment removed for export] *)
Theorem lrz_srealizes : forall ms mo g T mr mat,
  LRZ ms mo g T -> LINV segs g mo mat (ms_mem ms) mr -> srealizes segs (mkCfg (msw ms mr) (real mo mat)) T.
Proof. intros ms mo g T mr mat H HI. exact (H mr mat HI). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lfamily ms mo g x8 (I : Type) (evs : I -> list event) (T : I -> TSet) : Prop :=
  forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
     exists (eff : I -> resp) (mo' : I -> Model) (g' : I -> lghost) (mv' : I -> mem) (mat' : I -> list word),
       (forall o, syscall_spec (sys_input segs (msw ms mr) x8) (real mo mat) o <-> exists i, o = Ok (eff i) (real (mo' i) mat) (evs i))
       /\ forall i, m_halted (mo' i) = None
          /\ materialize_model_accesses (real (mo' i) mat) (syscall_effect_accesses (eff i)) = Some (real (mo' i) (mat' i))
          /\ LINV segs (g' i) (mo' i) (mat' i) (mv' i) (ms_mem (nret (msw ms mr) (eff i)))
          /\ LRZ (msw (nret ms (eff i)) (mv' i)) (mo' i) (g' i) (T i).

(* [comment removed for export] *)
Lemma lfamily_node_ok : forall ms mo g x8 (I : Type) (evs : I -> list event) (T : I -> TSet),
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false -> lfamily ms mo g x8 I evs T ->
  forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
    exists nx, node_ok segs (mkCfg (msw ms mr) (real mo mat)) I evs nx /\ forall i, srealizes segs (nx i) (T i).
Proof.
  intros ms mo g x8 I evs T Hsvc Hb H mr mat HI.
  destruct (H mr mat HI) as (eff & mo' & g' & mv' & mat' & Hiff & Hall).
  pose proof (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI)) as Hh.
  assert (Hsvc' : ms_svc_pending (msw ms mr) = Some x8) by (rewrite ms_svc_pending_msw; exact Hsvc).
  exists (fun i => mkCfg (nret (msw ms mr) (eff i)) (real (mo' i) (mat' i))). split.
  - split.
    + intros i. destruct (Hall i) as (Hh' & Hm & _ & _). cbn.
      eapply sstep_cfg_syscall; [rewrite real_halted; exact Hh| exact Hsvc'| apply Hiff; exists i; reflexivity
        | exact (nsp_no segs (msw ms mr) x8 _ _ _ eq_refl Hb) | rewrite real_halted; exact Hh'| exact Hm].
    + intros e X Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_svc_inv segs (msw ms mr) (real mo mat) x8 e X Hsvc' Hss)
        as [(ef & mo1 & mo2 & Hs & Hh1 & Hm & ->) | [(ef & mo1 & evs1 & Hs & Hh1 & Hm & -> & ->) | [(ef & mo1 & evs1 & code & Hs & Hh1 & -> & ->) | (Hs & -> & ->)]]].
      * apply Hiff in Hs as (i & E). apply Ok_inj in E as (-> & -> & ->).
        destruct (Hall i) as (_ & Hm' & _). rewrite Hm' in Hm. injection Hm as <-.
        exists i. split; reflexivity.
      * exfalso. apply Hiff in Hs as (i & E). apply Ok_inj in E as (-> & -> & ->).
        destruct (Hall i) as (_ & Hm' & _). rewrite Hm' in Hm. discriminate.
      * exfalso. apply Hiff in Hs as (i & E). apply Ok_inj in E as (-> & -> & ->).
        destruct (Hall i) as (Hh' & _). rewrite real_halted, Hh' in Hh1. discriminate.
      * exfalso. apply Hiff in Hs as (i & E). discriminate.
  - intros i. destruct (Hall i) as (_ & _ & HI' & HK). cbn.
    rewrite nret_msw, <- (msw_msw (nret ms (eff i)) (mv' i)). apply HK. cbn [ms_mem msw]. exact HI'.
Qed.

Theorem lrz_node : forall ms mo g x8 (I : Type) (i0 : I) (evs : I -> list event) (T : I -> TSet),
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  lfamily ms mo g x8 I evs T ->
  LRZ ms mo g (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros ms mo g x8 I i0 evs T Hsvc Hb H mr mat HI.
  destruct (lfamily_node_ok ms mo g x8 I evs T Hsvc Hb H mr mat HI) as (nx & Hnode & HK).
  exact (srz_node segs _ I evs nx T i0 Hnode HK).
Qed.

(* [comment removed for export] *)
Lemma lrz_node_silent : forall ms mo g x8 (I : Type) (i0 : I) (K : TSet),
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  lfamily ms mo g x8 I (fun _ => []) (fun _ => K) ->
  LRZ ms mo g K.
Proof.
  intros ms mo g x8 I i0 K Hsvc Hb H mr mat HI.
  destruct (lfamily_node_ok ms mo g x8 I _ _ Hsvc Hb H mr mat HI) as (nx & Hnode & HK).
  exact (srz_silent segs _ I nx K i0 Hnode HK).
Qed.

(* [comment removed for export] *)
Lemma lrz_node_alt2 : forall ms mo g x8 (IA IB : Type) (a0 : IA) (b0 : IB) (KA KB : TSet),
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  lfamily ms mo g x8 (IA + IB)%type (fun _ => []) (fun i => match i with inl _ => KA | inr _ => KB end) ->
  LRZ ms mo g (t_alt2 KA KB).
Proof.
  intros ms mo g x8 IA IB a0 b0 KA KB Hsvc Hb H mr mat HI.
  destruct (lfamily_node_ok ms mo g x8 (IA + IB)%type _ _ Hsvc Hb H mr mat HI) as (nx & Hnode & HK).
  apply (srz_alt2 segs _ IA IB nx KA KB a0 b0 Hnode); intros i; [exact (HK (inl i))| exact (HK (inr i))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msw_MSsvc : forall R F pc x8 fc rv m ro mr, msw (MSsvc R F pc x8 fc rv m ro) mr = MSsvc R F pc x8 fc rv mr ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mrd_real : forall g mo mat mv mr x b,
  LINV segs g mo mat mv mr -> mrd segs mv x = Some b -> mrd segs mr x = Some b.
Proof.
  intros g mo mat mv mr x b HI H. destruct (LINV_lrel _ _ _ _ _ _ HI) as [Hm _].
  unfold mrd in *. destruct (mv x) as [c|] eqn:E.
  - rewrite (magree_some _ _ _ _ _ _ _ Hm E). exact H.
  - assert (Hs : ~ noseg segs x) by (intros Hn; rewrite (seg_rom_noseg segs x Hn) in H; discriminate).
    rewrite (magree_seg _ _ _ _ _ _ Hm Hs). unfold lmem. rewrite E.
    destruct (lzf mo x) eqn:Ez; [| exact H].
    exfalso. exact (Hs (proj1 (lok_zf_noseg _ _ (LINV_LOK _ _ _ _ _ _ HI) x Ez))).
Qed.

Lemma bytes_in_real : forall g mo mat mv mr a bs,
  LINV segs g mo mat mv mr -> bytes_at segs mv a bs -> bytes_in (mrd segs mr) a bs.
Proof.
  intros g mo mat mv mr a bs HI (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H i Hi) as Hb. destruct (nth_error bs i) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
  eapply mrd_real; eassumption.
Qed.

Lemma wview_real : forall g mo mat mv mr x,
  LINV segs g mo mat mv mr -> wview segs mv x <> None -> wview segs mr x <> None.
Proof.
  intros g mo mat mv mr x HI H. destruct (LINV_lrel _ _ _ _ _ _ HI) as [Hm _].
  pose proof (LINV_LOK _ _ _ _ _ _ HI) as HO.
  exact (proj1 (wview_ext segs (lzf mo) (lexc mo (g_win g)) (lok_zf_noseg _ _ HO) mv mr x Hm H)).
Qed.

Lemma vis_of_mrd : forall mv x b, mrd segs mv x = Some b -> vis segs mv x.
Proof.
  intros mv x b H. unfold mrd in H. destruct (mv x) eqn:E; [left; congruence|].
  right. intros Hn. rewrite (seg_rom_noseg segs x Hn) in H. discriminate.
Qed.

Lemma vis_of_wview : forall mv x, wview segs mv x <> None -> vis segs mv x.
Proof.
  intros mv x H. unfold wview in H. destruct (mv x) eqn:E; [left; congruence|].
  right. intros Hn. rewrite (find_segment_noseg segs x 1 Hn ltac:(lia)) in H. exact (H eq_refl).
Qed.

(* [comment removed for export] *)
Lemma LINV_with_fds : forall g mo mat mv mr fds,
  LINV segs g mo mat mv mr -> LINV segs g (with_fds fds mo) mat mv mr.
Proof.
  intros g mo mat mv mr fds ([HWX HO] & HB & HL & HM). destruct HO.
  split; [split; [exact HWX| constructor; assumption]|]. split; [exact HB|]. split; [exact HL| exact HM].
Qed.

Lemma real_with_fds : forall fds mo mat, with_fds fds (real mo mat) = real (with_fds fds mo) mat.
Proof. reflexivity. Qed.
Lemma m_fds_real : forall mo mat, m_fds (real mo mat) = m_fds mo. Proof. reflexivity. Qed.
Lemma m_fs_real : forall mo mat, m_fs (real mo mat) = m_fs mo. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_exit_svc : forall R F pc x8 fc rv m mo g,
  is_exit_no x8 ->
  LRZ (MSsvc R F pc x8 fc rv m (seg_rom segs)) mo g (t_exit (bv_and (reg_get R 10) (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros R F pc x8 fc rv m mo g Hx8 mr mat HI. rewrite msw_MSsvc, <- (m_fs_real mo mat).
  apply srealizes_of_realizes. apply rz_exit_svc; [rewrite real_halted; exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))| exact Hx8].
Qed.

Lemma lrz_exit_group_lit : forall R F pc fc rv m mo g (code : Z),
  reg_get R 10 = Z_to_bv 64 code -> 0 <= code < 256 ->
  LRZ (MSsvc R F pc (Z_to_bv 64 94) fc rv m (seg_rom segs)) mo g (t_exit (Z_to_bv 64 code) (m_fs mo)).
Proof.
  intros R F pc fc rv m mo g code H10 Hc mr mat HI. rewrite msw_MSsvc, <- (m_fs_real mo mat).
  apply srealizes_of_realizes. apply rz_exit_group_lit; [rewrite real_halted; exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))| exact H10| exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_close : forall R F pc fc rv m mo g (fd : word) e K,
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some e ->
  LRZ (nret (MSsvc R F pc (Z_to_bv 64 57) fc rv m (seg_rom segs)) (eff0 (Z_to_bv 64 0))) (with_fds (fd_remove (m_fds mo) fd) mo) g K ->
  LRZ (MSsvc R F pc (Z_to_bv 64 57) fc rv m (seg_rom segs)) mo g K.
Proof.
  intros R F pc fc rv m mo g fd e K H10 Hfd Hlk HK.
  apply (lrz_node_silent (MSsvc R F pc (Z_to_bv 64 57) fc rv m (seg_rom segs)) mo g (Z_to_bv 64 57) unit tt K eq_refl eq_refl).
  intros mr mat HI. exists (fun _ => eff0 (Z_to_bv 64 0)), (fun _ => with_fds (fd_remove (m_fds mo) fd) mo), (fun _ => g), (fun _ => m), (fun _ => mat).
  split.
  - intros o. rewrite msw_MSsvc. rewrite (syscall_spec_57 _ _ o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite svc_a0, H10, (fd32_id fd Hfd). rewrite (close_outcome fd _ (real mo mat) e o) by (rewrite m_fds_real; exact Hlk).
    rewrite m_fds_real, real_with_fds. split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [apply materialize_model_accesses_nil|]. split.
    + rewrite msw_MSsvc. unfold eff0. rewrite mem_nret_plain. cbn [ms_mem MSsvc]. apply LINV_with_fds. exact HI.
    + unfold eff0 in *. rewrite <- (mem_nret_plain (MSsvc R F pc (Z_to_bv 64 57) fc rv m (seg_rom segs)) (Z_to_bv 64 0)) at 1.
      rewrite msw_nret_self. exact HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_ioctl_tty : forall R F pc fc rv m mo g (fd : word) e K,
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some e ->
  e <> FdUrandom ->     (* [comment removed for export] *)
  reg_get R 11 = TIOCGWINSZ ->
  LRZ (nret (MSsvc R F pc (Z_to_bv 64 29) fc rv m (seg_rom segs)) (efferr ENOTTY)) mo g K ->
  LRZ (MSsvc R F pc (Z_to_bv 64 29) fc rv m (seg_rom segs)) mo g K.
Proof.
  intros R F pc fc rv m mo g fd e K H10 Hfd Hlk Hnd H11 HK.
  apply (lrz_node_silent (MSsvc R F pc (Z_to_bv 64 29) fc rv m (seg_rom segs)) mo g (Z_to_bv 64 29) unit tt K eq_refl eq_refl).
  intros mr mat HI. exists (fun _ => efferr ENOTTY), (fun _ => mo), (fun _ => g), (fun _ => m), (fun _ => mat).
  split.
  - intros o. rewrite msw_MSsvc. rewrite (syscall_spec_29 _ _ o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite svc_a0, svc_a1, H10, H11, (fd32_id fd Hfd).
    rewrite (ioctl_tty_outcome fd _ _ (real mo mat) e o); [| rewrite m_fds_real; exact Hlk| exact Hnd| vm_compute; reflexivity].
    split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [apply materialize_model_accesses_nil|]. split.
    + rewrite msw_MSsvc. unfold efferr, eff0. rewrite mem_nret_plain. cbn [ms_mem MSsvc]. exact HI.
    + unfold efferr, eff0 in *. rewrite <- (mem_nret_plain (MSsvc R F pc (Z_to_bv 64 29) fc rv m (seg_rom segs)) (errno_ret ENOTTY)) at 1.
      rewrite msw_nret_self. exact HK.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_at_real : forall g mo mat mv mr a n,
  LINV segs g mo mat mv mr -> wr_at segs mv a n -> wr_at segs mr a n.
Proof.
  intros g mo mat mv mr a n HI (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. eapply wview_real; [exact HI| apply H; exact Hi].
Qed.

Lemma LINV_write : forall g mo mat mv mr (A : Z) (bs : list byte),
  LINV segs g mo mat mv mr -> wr_at segs mv A (Z.of_nat (length bs)) ->
  LINV segs g mo mat (write_to_mem mv (wa A) bs) (write_to_mem mr (wa A) bs).
Proof.
  intros g mo mat mv mr A bs HI Hw. pose proof HI as ([HWX HO] & HB & [Hm Hhid] & [HM HVD]).
  pose proof Hw as (HA0 & HA1 & HW).
  assert (WS : forall m x, write_to_mem m (wa A) bs x =
            (if ((A <=? bv_unsigned x) && (bv_unsigned x <? A + Z.of_nat (length bs)))%bool
             then nth_error bs (Z.to_nat (bv_unsigned x - A)) else m x)).
  { intros m0 x. apply write_to_mem_spec; lia. }
  split; [split; [exact HWX| exact HO]|]. split; [exact HB|]. split; [split|split; [exact HM|]].
  - apply magree_write_to_mem. exact Hm.
  - intros x Hl Hwn. rewrite (WS mv x).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + Z.of_nat (length bs))); cbn [andb];
      try (apply Hhid; assumption).
    exfalso. pose proof (HW (bv_unsigned x - A) ltac:(lia)) as Hv.
    replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hv by lia. unfold wa in Hv. rewrite Z_to_bv_bv_unsigned in Hv.
    apply Hv. apply wview_noseg; [apply (lok_lazy_noseg _ _ HO); exact Hl| apply Hhid; assumption].
  - intros x Hx. rewrite (WS mv x) in Hx.
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + Z.of_nat (length bs))); cbn [andb] in Hx;
      try (apply HVD; exact Hx).
    pose proof (HW (bv_unsigned x - A) ltac:(lia)) as Hv.
    replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hv by lia. unfold wa in Hv. rewrite Z_to_bv_bv_unsigned in Hv.
    destruct (vis_of_wview mv x Hv) as [Hv'|Hs]; [apply HVD; exact Hv'| right; left; exact Hs].
Qed.

Lemma mem_nret_delivered : forall ms r a bs,
  ms_mem (nret ms (mkEffect r (delivered_writes a bs) [])) = write_to_mem (ms_mem ms) a bs.
Proof. intros ms r a bs. rewrite mem_nret. destruct bs; reflexivity. Qed.

(* [comment removed for export] *)
Lemma vis_write : forall mv (A : Z) (bs : list byte) k,
  0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> (k < length bs)%nat ->
  vis segs (write_to_mem mv (wa A) bs) (boff (wa A) k).
Proof.
  intros mv A bs k HA0 HA1 Hk. left. unfold boff. rewrite wa_add_nat, wa_unsigned by lia.
  rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 A (A + Z.of_nat k)); destruct (Z.ltb_spec0 (A + Z.of_nat k) (A + Z.of_nat (length bs))); cbn [andb]; try lia.
  replace (Z.to_nat (A + Z.of_nat k - A)) with k by lia.
  destruct (nth_error bs k) eqn:E; [discriminate|]. apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lrz_read_file : forall R F pc fc rv m mo g (fd : word) p off data (buf cnt : Z) K,
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
  fs_lookup (m_fs mo) p = Some data ->
  reg_get R 11 = Z_to_bv 64 buf -> reg_get R 12 = Z_to_bv 64 cnt ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->      (* [comment removed for export] *)
  wr_at segs m buf cnt ->
  let bs := file_read data off (Z_to_bv 64 cnt) in
  LRZ (nret (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs))
            (mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []))
      (with_fds (fd_insert (m_fds mo) fd (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo) g K ->
  LRZ (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) mo g K.
Proof.
  intros R F pc fc rv m mo g fd p off data buf cnt K H10 Hfd Hlk Hfs H11 H12 Hcnt Hnw Hwr bs HK.
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  pose proof (length_file_read_le data off cnt ltac:(lia)) as Hlen. fold bs in Hlen.
  set (svc := MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) in *.
  set (eff := mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []) in *.
  set (mo' := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo) in *.
  apply (lrz_node_silent svc mo g (Z_to_bv 64 63) unit tt K eq_refl eq_refl).
  intros mr mat HI. cbn [ms_mem svc MSsvc] in HI.
  pose proof (wr_at_real _ _ _ _ _ _ _ HI Hwr) as Hwr'.
  destruct (read_bytes_map_wr_at segs mr buf cnt Hwr' ltac:(lia)) as [w Hw].
  assert (HI1 : LINV segs g mo' mat (write_to_mem m (wa buf) bs) (write_to_mem mr (wa buf) bs)).
  { unfold mo'. apply LINV_with_fds. apply LINV_write; [exact HI|]. pose proof Hwr as (A0 & A1 & AW). split; [lia|]. split; [lia|]. intros i Hi. apply AW. lia. }
  assert (ACC : forall a n, In (a, n) (syscall_effect_accesses eff) -> forall k, (k < n)%nat -> vis segs (write_to_mem m (wa buf) bs) (boff a k)).
  { intros a n Hin k Hk. unfold eff in Hin. cbn [syscall_effect_accesses eff_copyins eff_writes app] in Hin.
    destruct bs as [|b bs'] eqn:Ebs; cbn [delivered_writes write_accesses] in Hin; [destruct Hin|].
    destruct Hin as [Hin|[]]. injection Hin as <- <-. change (Z_to_bv 64 buf) with (wa buf). apply vis_write; cbn [length] in *; lia. }
  destruct (lmaterialize segs g mo' mat _ _ (syscall_effect_accesses eff) HI1 ACC) as [Hmat HI2].
  exists (fun _ => eff), (fun _ => mo'), (fun _ => g), (fun _ => write_to_mem m (wa buf) bs),
    (fun _ => newly_materialized_pages (m_vm_lazy mo') mat (syscall_effect_accesses eff) ++ mat).
  split.
  - intros o. unfold svc. rewrite msw_MSsvc.
    unshelve epose proof (read_file_outcome_i (sys_input segs (MSsvc R F pc (Z_to_bv 64 63) fc rv mr (seg_rom segs)) (Z_to_bv 64 63))
               (real mo mat) fd (Z_to_bv 64 buf) (Z_to_bv 64 cnt) p off data w _ _ _ _ _ _ _ _ _ _ o) as RW.
    all: try (first [ rewrite svc_sysno; apply u64_lit; lia
                    | rewrite svc_a0; exact H10
                    | exact Hfd
                    | rewrite svc_a1; exact H11
                    | rewrite svc_a2; exact H12
                    | rewrite m_fds_real; exact Hlk
                    | rewrite m_fs_real; exact Hfs
                    | rewrite svc_wmem; exact Hw
                    | rewrite u64_lit by lia; rewrite rw_bytes_max_val; lia
                    | rewrite !u64_lit by lia; rewrite TASK_SIZE_val; lia ]).
    cbv zeta in RW. rewrite RW. unfold eff, mo'. rewrite real_with_fds, m_fds_real. fold bs. rewrite <- len_word_of by lia.
    split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|]. split.
    + unfold svc. rewrite msw_MSsvc. unfold eff. rewrite mem_nret_delivered. cbn [ms_mem MSsvc]. exact HI2.
    + replace (write_to_mem m (wa buf) bs) with (ms_mem (nret svc eff)).
      * rewrite msw_nret_self. exact HK.
      * unfold eff, svc. rewrite mem_nret_delivered. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lrz_read_dir : forall R F pc fc rv m mo g (fd : word) (buf cnt : Z) K,
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some FdDir ->
  reg_get R 11 = Z_to_bv 64 buf -> reg_get R 12 = Z_to_bv 64 cnt ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->      (* [comment removed for export] *)
  wr_at segs m buf cnt ->
  LRZ (nret (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) (efferr EISDIR)) mo g K ->
  LRZ (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) mo g K.
Proof.
  intros R F pc fc rv m mo g fd buf cnt K H10 Hfd Hlk H11 H12 Hcnt Hnw Hwr HK.
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  apply (lrz_node_silent (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) mo g (Z_to_bv 64 63) unit tt K eq_refl eq_refl).
  intros mr mat HI. cbn [ms_mem MSsvc] in HI.
  exists (fun _ => efferr EISDIR), (fun _ => mo), (fun _ => g), (fun _ => m), (fun _ => mat).
  split.
  - intros o. rewrite msw_MSsvc. rewrite (syscall_spec_63 _ _ o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite svc_a0, svc_a1, svc_a2, H10, H11, H12, (fd32_id fd Hfd).
    rewrite (read_dir_outcome fd _ _ _ (real mo mat) o); [| rewrite m_fds_real; exact Hlk|].
    + split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
    + apply access_okb_intro. rewrite !u64_lit by lia. rewrite TASK_SIZE_val. lia.
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [apply materialize_model_accesses_nil|]. split.
    + rewrite msw_MSsvc. unfold efferr, eff0. rewrite mem_nret_plain. cbn [ms_mem MSsvc]. exact HI.
    + unfold efferr, eff0 in *. rewrite <- (mem_nret_plain (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) (errno_ret EISDIR)) at 1.
      rewrite msw_nret_self. exact HK.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cstr_len_prefix : forall (p : list byte) mp a fuel,
  (length p <= fuel)%nat ->
  (forall i, (i < length p)%nat -> exists b, mp (boff a i) = Some b /\ b <> Z_to_bv 8 0) ->
  cstr_access_len_aux mp a fuel = (length p + cstr_access_len_aux mp (boff a (length p)) (fuel - length p))%nat.
Proof.
  induction p as [|c p IH]; intros mp a fuel Hlen Hb.
  - cbn [length Nat.add]. rewrite boff_0, Nat.sub_0_r. reflexivity.
  - destruct fuel as [|fuel]; [cbn in Hlen; lia|]. cbn [cstr_access_len_aux length].
    destruct (Hb 0%nat ltac:(cbn; lia)) as (b & Hb0 & Hnz). rewrite boff_0 in Hb0. rewrite Hb0.
    rewrite (bv_eqb_neq _ _ Hnz). rewrite (IH mp (a + 1)%bv fuel); [| cbn in Hlen; lia|].
    + rewrite <- boff_S. reflexivity.
    + intros i Hi. rewrite <- boff_S. apply Hb. cbn. lia.
Qed.

Lemma bytes_in_boff : forall mp a bs i, bytes_in mp a bs -> (i < length bs)%nat ->
  mp (boff (wa a) i) = nth_error bs i.
Proof.
  intros mp a bs i (H0 & H1 & H) Hi. unfold boff. rewrite wa_add_nat, wa_unsigned by lia. apply H. exact Hi.
Qed.

Section Openat.
  Variables (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m : mem) (mo : Model) (g : lghost).
  Hypothesis H10 : reg_get R 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (reg_get R 12)) open_ignored_flags = 0.

  Let svc := MSsvc R F pc (Z_to_bv 64 56) fc rv m (seg_rom segs).
  Let pathp := reg_get R 11.
  Let fds := m_fds mo.

  Definition lpath_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p /\ bytes_at segs m (bv_unsigned pathp) (p ++ [Z_to_bv 8 0]).

  (* [comment removed for export] *)
  Let rin (mr : mem) := sys_input segs (MSsvc R F pc (Z_to_bv 64 56) fc rv mr (seg_rom segs)) (Z_to_bv 64 56).

  Lemma openat_head_r : forall mr mat o,
    syscall_spec (rin mr) (real mo mat) o <->
    openat_spec AT_FDCWD32 pathp (reg_get R 12) (rin mr) (real mo mat) o.
  Proof.
    intros mr mat o. unfold rin, pathp. rewrite (syscall_spec_56 _ _ o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite svc_a0, svc_a1, svc_a2, H10. reflexivity.
  Qed.

  Lemma path_at_cstr_r : forall p mr mat, LINV segs g mo mat m mr -> lpath_at p ->
    read_cstr (in_mem (rin mr)) pathp = CstrOk p.
  Proof.
    intros p mr mat HI (H1 & H2 & H3). unfold rin. rewrite svc_mem. unfold read_cstr.
    rewrite <- (wa_unsigned_id pathp). apply read_cstr_aux_bytes_in; [unfold path_max; lia | exact H2 |].
    eapply bytes_in_real; [exact HI| exact H3].
  Qed.

  (* [comment removed for export] *)
  Lemma open_reads_vis : forall p mr mat, LINV segs g mo mat m mr -> lpath_at p ->
    forall a n, In (a, n) (open_reads (rin mr) pathp) -> forall k, (k < n)%nat -> vis segs m (boff a k).
  Proof.
    intros p mr mat HI (H1 & H2 & H3) a n [Hin|[]] k Hk.
    pose proof (f_equal fst Hin) as Ha. pose proof (f_equal snd Hin) as Hn. cbn [fst snd] in Ha, Hn. subst a n. clear Hin.
    unfold rin in Hk. rewrite svc_mem in Hk.
    pose proof (bytes_in_real _ _ _ _ _ _ _ HI H3) as HB.
    rewrite <- (wa_unsigned_id pathp) in Hk |- *.
    rewrite (cstr_len_prefix p) in Hk.
    - assert (E : cstr_access_len_aux (mrd segs mr) (boff (wa (bv_unsigned pathp)) (length p)) (path_max - length p) = 1%nat).
      { unfold path_max. destruct (4096 - length p)%nat eqn:En; [lia|]. cbn [cstr_access_len_aux].
        rewrite (bytes_in_boff _ _ _ (length p) HB) by (rewrite length_app; cbn; lia).
        rewrite nth_error_app2, Nat.sub_diag by lia. cbn. reflexivity. }
      rewrite E in Hk.
      destruct H3 as (A0 & A1 & A3). rewrite length_app in A1. cbn [length] in A1.
      pose proof (A3 k ltac:(rewrite length_app; cbn; lia)) as Hr.
      destruct (nth_error (p ++ [Z_to_bv 8 0]) k) eqn:En; [| apply nth_error_None in En; rewrite length_app in En; cbn in En; lia].
      apply (vis_of_mrd m (boff (wa (bv_unsigned pathp)) k) b). unfold boff. rewrite wa_add_nat, wa_unsigned by lia. exact Hr.
    - unfold path_max. lia.
    - intros i Hi. exists (nth i p (Z_to_bv 8 0)). split.
      + rewrite (bytes_in_boff _ _ _ i HB) by (rewrite length_app; cbn; lia). rewrite nth_error_app1 by lia.
        apply nth_error_nth'. exact Hi.
      + intros E. apply H2. rewrite <- E. apply nth_In. exact Hi.
  Qed.

  Lemma nret_copyins' : forall ms r reads, nret ms (with_copyins reads (mkEffect r [] [])) = nret ms (eff0 r).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_det : forall r K,
    (forall mr mat, LINV segs g mo mat m mr ->
       (forall o, syscall_spec (rin mr) (real mo mat) o <->
                  o = Ok (with_copyins (open_reads (rin mr) pathp) (mkEffect r [] [])) (real mo mat) [])
       /\ (forall a n, In (a, n) (open_reads (rin mr) pathp) -> forall k, (k < n)%nat -> vis segs m (boff a k))) ->
    LRZ (nret svc (eff0 r)) mo g K ->
    LRZ svc mo g K.
  Proof.
    intros r K H HK.
    apply (lrz_node_silent svc mo g (Z_to_bv 64 56) unit tt K eq_refl eq_refl).
    intros mr mat HI. cbn [ms_mem svc MSsvc] in HI. destruct (H mr mat HI) as [Hiff Hvis].
    set (eff := with_copyins (open_reads (rin mr) pathp) (mkEffect r [] [])).
    assert (ACC : forall a n, In (a, n) (syscall_effect_accesses eff) -> forall k, (k < n)%nat -> vis segs m (boff a k)).
    { intros a n Hin. unfold eff in Hin. cbv beta iota delta [syscall_effect_accesses with_copyins eff_copyins eff_writes eff_ret eff_zeros eff_unmaps eff_copies write_accesses] in Hin.
      rewrite app_nil_r in Hin. exact (Hvis a n Hin). }
    destruct (lmaterialize segs g mo mat m mr (syscall_effect_accesses eff) HI ACC) as [Hmat HI2].
    exists (fun _ => eff), (fun _ => mo), (fun _ => g), (fun _ => m), (fun _ => newly_materialized_pages (m_vm_lazy mo) mat (syscall_effect_accesses eff) ++ mat).
    split.
    - intros o. unfold svc. rewrite msw_MSsvc. fold (rin mr). rewrite Hiff.
      split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
    - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|]. split.
      + unfold svc. rewrite msw_MSsvc. unfold eff. rewrite nret_copyins'. unfold eff0. rewrite mem_nret_plain. cbn [ms_mem MSsvc]. exact HI2.
      + unfold eff. rewrite nret_copyins'. unfold eff0 in *.
        eapply lrz_eq; [| exact HK].
        transitivity (msw (nret svc (mkEffect r [] [])) (ms_mem (nret svc (mkEffect r [] [])))); [rewrite mem_nret_plain; reflexivity| apply msw_nret_self].
  Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_toolong : forall bs K,
    length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs -> bytes_at segs m (bv_unsigned pathp) bs ->
    LRZ (nret svc (efferr ENAMETOOLONG)) mo g K ->
    LRZ svc mo g K.
  Proof.
    intros bs K Hlen Hnz Hb HK. apply (lrz_openat_det (errno_ret ENAMETOOLONG)); [| exact HK].
    intros mr mat HI. pose proof (bytes_in_real _ _ _ _ _ _ _ HI Hb) as HB. split.
    - intros o. rewrite openat_head_r. apply (openat_toolong_outcome _ _ _ _ (real mo mat) (modeled_open_flags_rd _ Hfl)).
      unfold rin. rewrite svc_mem. unfold read_cstr. rewrite <- (wa_unsigned_id pathp).
      apply (read_cstr_aux_toolong_bytes_in path_max bs); [unfold path_max; lia | exact Hnz | exact HB].
    - intros a n [Hin|[]] k Hk.
      pose proof (f_equal fst Hin) as Ha. pose proof (f_equal snd Hin) as Hn. cbn [fst snd] in Ha, Hn. subst a n. clear Hin.
      unfold rin in Hk. rewrite svc_mem in Hk.
      rewrite <- (wa_unsigned_id pathp) in Hk |- *. rewrite (cstr_len_prefix bs) in Hk.
      + replace (path_max - length bs)%nat with 0%nat in Hk by (unfold path_max; lia). cbn [cstr_access_len_aux Nat.add] in Hk.
        rewrite Nat.add_0_r in Hk.
        destruct Hb as (A0 & A1 & A3). pose proof (A3 k ltac:(lia)) as Hr.
        destruct (nth_error bs k) eqn:En; [| apply nth_error_None in En; lia].
        apply (vis_of_mrd m _ b). unfold boff. rewrite wa_add_nat, wa_unsigned by lia. exact Hr.
      + unfold path_max. lia.
      + intros i Hi. exists (nth i bs (Z_to_bv 8 0)). split.
        * rewrite (bytes_in_boff _ _ _ i HB) by lia. apply nth_error_nth'. exact Hi.
        * intros E. apply Hnz. rewrite <- E. apply nth_In. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_empty : forall K,
    lpath_at [] ->
    LRZ (nret svc (efferr ENOENT)) mo g K ->
    LRZ svc mo g K.
  Proof.
    intros K Hp HK. apply (lrz_openat_det (errno_ret ENOENT)); [| exact HK].
    intros mr mat HI. split.
    - intros o. rewrite openat_head_r. apply (openat_empty_outcome _ _ _ _ (real mo mat) (modeled_open_flags_rd _ Hfl)).
      exact (path_at_cstr_r [] mr mat HI Hp).
    - exact (open_reads_vis [] mr mat HI Hp).
  Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_absent : forall p K,
    lpath_at p -> p <> [] -> p <> dot_path -> p <> dotdot_path -> path_has_slash p = false ->   (* [comment removed for export] *)
    fs_lookup (m_fs mo) p = None ->
    LRZ (nret svc (efferr ENOENT)) mo g K ->
    LRZ svc mo g K.
  Proof.
    intros p K Hp Hne Hnd Hndd Hsl Hfs HK. apply (lrz_openat_det (errno_ret ENOENT)); [| exact HK].
    intros mr mat HI. split.
    - intros o. rewrite openat_head_r.
      apply (openat_absent_outcome _ _ _ _ (real mo mat) (modeled_open_flags_rd _ Hfl) eq_refl Hfl p);
        [exact (path_at_cstr_r p mr mat HI Hp) | exact Hne | exact Hnd | exact Hndd | exact Hsl | rewrite m_fs_real; exact Hfs].
    - exact (open_reads_vis p mr mat HI Hp).
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma ENOMEM_in_openat_errnos' : In ENOMEM openat_errnos.
  Proof. left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_open : forall (p : list byte) (mk : word -> Model -> Model) KA KB,
    lpath_at p ->
    (forall mr mat, LINV segs g mo mat m mr -> forall o,
        syscall_spec (rin mr) (real mo mat) o <->
        open_out (open_reads (rin mr) pathp) (real mo mat) (fun fd => mk fd (real mo mat)) o) ->
    (forall fd mo1 mat1, mk fd (real mo1 mat1) = real (mk fd mo1) mat1) ->
    (forall fd mo1, m_halted (mk fd mo1) = m_halted mo1) ->
    (forall fd mo1 mat1 mv1 mr1 g1, LINV segs g1 mo1 mat1 mv1 mr1 -> LINV segs g1 (mk fd mo1) mat1 mv1 mr1) ->
    (forall e, In e openat_errnos -> LRZ (nret svc (efferr e)) mo g KA) ->
    LRZ (nret svc (eff0 (alloc_fd fds))) (mk (alloc_fd fds) mo) g KB ->
    LRZ svc mo g (t_alt2 KA KB).
  Proof.
    intros p mk KA KB Hp Hiff Hmk Hmkh HmkI HA HB.
    apply (lrz_node_alt2 svc mo g (Z_to_bv 64 56) {e : Z | In e openat_errnos} unit
             (exist _ ENOMEM ENOMEM_in_openat_errnos') tt KA KB eq_refl eq_refl).
    intros mr mat HI. cbn [ms_mem svc MSsvc] in HI.
    set (rd := open_reads (rin mr) pathp).
    pose (effs := fun i : {e : Z | In e openat_errnos} + unit =>
                    match i with inl (exist _ e _) => with_copyins rd (efferr e) | inr _ => with_copyins rd (eff0 (alloc_fd fds)) end).
    pose (mos := fun i : {e : Z | In e openat_errnos} + unit => match i with inl _ => mo | inr _ => mk (alloc_fd fds) mo end).
    assert (ACC : forall i a n, In (a, n) (syscall_effect_accesses (effs i)) -> forall k, (k < n)%nat -> vis segs m (boff a k)).
    { intros i a n Hin. assert (Hin' : In (a, n) rd).
      { destruct i as [[e He]|[]]; cbv beta iota delta [effs syscall_effect_accesses with_copyins eff_copyins eff_writes eff_ret eff_zeros eff_unmaps eff_copies write_accesses efferr eff0] in Hin;
          rewrite app_nil_r in Hin; exact Hin. }
      exact (open_reads_vis p mr mat HI Hp a n Hin'). }
    assert (HIi : forall i, LINV segs g (mos i) mat m mr).
    { intros [[e He]|[]]; cbn [mos]; [exact HI| apply HmkI; exact HI]. }
    exists effs, mos, (fun _ => g), (fun _ => m),
      (fun i => newly_materialized_pages (m_vm_lazy (mos i)) mat (syscall_effect_accesses (effs i)) ++ mat).
    split.
    - intros o. unfold svc. rewrite msw_MSsvc. fold (rin mr). rewrite (Hiff mr mat HI o). unfold open_out. fold rd.
      rewrite m_fds_real. fold fds. split.
      + intros [(e & He & ->)|(_ & ->)]; [exists (inl (exist _ e He)); reflexivity| exists (inr tt)].
        cbn [effs mos]. rewrite Hmk. reflexivity.
      + intros [[[e He]|[]] ->]; cbn [effs mos]; [left; exists e; split; [exact He| reflexivity]| right].
        split; [exact Hfree|]. rewrite Hmk. reflexivity.
    - intros i. destruct (lmaterialize segs g (mos i) mat m mr (syscall_effect_accesses (effs i)) (HIi i) (ACC i)) as [Hmat HI2].
      split; [destruct i as [[e He]|[]]; cbn [mos]; [| rewrite Hmkh]; exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|].
      split; [exact Hmat|].
      assert (Em : forall ms0, ms_mem (nret ms0 (effs i)) = ms_mem ms0).
      { intros ms0. destruct i as [[e He]|[]]; cbn [effs]; unfold efferr, eff0; rewrite nret_copyins'; apply mem_nret_plain. }
      split.
      + rewrite Em. unfold svc. rewrite msw_MSsvc. cbn [ms_mem MSsvc]. exact HI2.
      + apply (lrz_eq _ (nret svc (effs i))).
        { transitivity (msw (nret svc (effs i)) (ms_mem (nret svc (effs i)))); [rewrite Em; reflexivity| apply msw_nret_self]. }
        destruct i as [[e He]|[]]; cbn [effs mos]; unfold efferr, eff0; rewrite nret_copyins'; [apply HA; exact He| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_dot : forall KA KB,
    lpath_at dot_path ->
    (forall e, In e openat_errnos -> LRZ (nret svc (efferr e)) mo g KA) ->
    LRZ (nret svc (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) FdDir) mo) g KB ->
    LRZ svc mo g (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB.
    apply (lrz_openat_open dot_path (fun fd mo1 => with_fds (fd_insert (m_fds mo1) fd FdDir) mo1));
      [exact Hp| | reflexivity| reflexivity| intros; apply LINV_with_fds; assumption| exact HA| exact HB].
    intros mr mat HI o. rewrite openat_head_r.
    apply (openat_dot_outcome _ _ _ _ (real mo mat) (modeled_open_flags_rd _ Hfl) eq_refl Hfl). exact (path_at_cstr_r _ mr mat HI Hp).
  Qed.

  (* [comment removed for export] *)
  Lemma lrz_openat_file : forall p d KA KB,
    lpath_at p -> p <> [] -> p <> dot_path -> p <> dotdot_path -> path_has_slash p = false ->   (* [comment removed for export] *)
    fs_lookup (m_fs mo) p = Some d ->
    (forall e, In e openat_errnos -> LRZ (nret svc (efferr e)) mo g KA) ->
    LRZ (nret svc (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) mo) g KB ->
    LRZ svc mo g (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hnd Hndd Hsl Hfs HA HB.
    apply (lrz_openat_open p (fun fd mo1 => with_fds (fd_insert (m_fds mo1) fd (FdFile p (Z_to_bv 64 0))) mo1));
      [exact Hp| | reflexivity| reflexivity| intros; apply LINV_with_fds; assumption| exact HA| exact HB].
    intros mr mat HI o. rewrite openat_head_r.
    apply (openat_file_outcome _ _ _ _ (real mo mat) (modeled_open_flags_rd _ Hfl) eq_refl Hfl p d);
      [exact (path_at_cstr_r p mr mat HI Hp)| exact Hne| exact Hnd| exact Hndd| exact Hsl| rewrite m_fs_real; exact Hfs].
  Qed.

End Openat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma boff_add : forall a i k, boff (boff a i) k = boff a (i + k).
Proof.
  intros a i k. apply bv_eq. unfold boff. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Nat2Z.inj_add.
  set (M := bv_modulus 64). set (ua := bv_unsigned a). set (zi := Z.of_nat i). set (zk := Z.of_nat k).
  assert (HM : 0 < M) by (unfold M, bv_modulus; lia).
  rewrite <- (Z.add_mod _ _ M) by lia.
  replace (ua + zi mod M + zk) with (zi mod M + (ua + zk)) by lia. rewrite Z.add_mod_idemp_l by lia.
  replace (ua + (zi + zk) mod M) with ((zi + zk) mod M + ua) by lia. rewrite Z.add_mod_idemp_l by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_iovecs_accesses_in : forall mp k a x n,
  In (x, n) (copy_iovecs_accesses mp a k) -> n = 16%nat /\ exists j, (j < k)%nat /\ x = boff a (16 * j).
Proof.
  intros mp k. induction k as [|k IH]; intros a x n Hin; [destruct Hin|].
  cbn [copy_iovecs_accesses] in Hin. destruct Hin as [E|Hin].
  - pose proof (f_equal fst E) as Ex. pose proof (f_equal snd E) as En. cbn [fst snd] in Ex, En. subst x n.
    split; [reflexivity|]. exists 0%nat. split; [lia|]. rewrite Nat.mul_0_r, boff_0. reflexivity.
  - destruct (read_iovec_entry mp a) as [b len| |]; [| destruct Hin | destruct Hin].   (* [comment removed for export] *)
    destruct (IH _ _ _ Hin) as (-> & j & Hj & ->). split; [reflexivity|]. exists (S j). split; [lia|].
    change (a + 16)%bv with (boff a 16). rewrite boff_add. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma iov_prefix_accesses_in : forall iovs left x n,
  In (x, n) (iov_prefix_accesses iovs left) -> exists len, In (x, len) iovs /\ (n <= word_to_nat len)%nat.
Proof.
  induction iovs as [|[b len] iovs IH]; intros left x n Hin.
  - destruct left; destruct Hin.
  - destruct left as [|left']; [destruct Hin|]. cbn [iov_prefix_accesses] in Hin.
    rewrite word_to_nat_bounded_eq_min in Hin.   (* [comment removed for export] *)
    set (q := Nat.min (word_to_nat len) (S left')) in Hin.
    destruct (Nat.eqb q 0) eqn:Eq.
    + destruct (IH _ _ _ Hin) as (len' & Hin' & Hle). exists len'. split; [right; exact Hin'| exact Hle].
    + destruct Hin as [E|Hin].
      * pose proof (f_equal fst E) as Ex. pose proof (f_equal snd E) as En. cbn [fst snd] in Ex, En. subst x n.
        exists len. split; [left; reflexivity|]. unfold q. lia.
      * destruct (IH _ _ _ Hin) as (len' & Hin' & Hle). exists len'. split; [right; exact Hin'| exact Hle].
Qed.

Lemma Forall2_In_l' : forall {A B} (P : A -> B -> Prop) l1 l2 x,
  Forall2 P l1 l2 -> In x l1 -> exists y, In y l2 /\ P x y.
Proof.
  intros A B P l1 l2 x H. induction H as [|a b l1 l2 Hab H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists b; split; [left; reflexivity| exact Hab]|].
  destruct (IH Hin) as (y & Hy & HP). exists y. split; [right; exact Hy| exact HP].
Qed.

Lemma Forall2_iov_ok_real : forall g mo mat mv mr iovs bss,
  LINV segs g mo mat mv mr -> Forall2 (iov_ok (mrd segs mv)) iovs bss -> Forall2 (iov_ok (mrd segs mr)) iovs bss.
Proof.
  intros g mo mat mv mr iovs bss HI H. induction H as [|iv bs iovs bss (H1 & H2 & H3) H IH]; constructor; [| exact IH].
  split; [exact H1|]. split; [exact H2|]. eapply bytes_in_real; [exact HI| exact H3].
Qed.

(* [comment removed for export] *)
Lemma writev_accesses_vis : forall (m : mem) (iovp : word) iovs bss mp k x n,
  bytes_at segs m (bv_unsigned iovp) (iovec_bytes iovs) ->
  Forall2 (iov_ok (mrd segs m)) iovs bss ->
  In (x, n) (copy_iovecs_accesses mp iovp (length iovs) ++ iov_prefix_accesses iovs k) ->
  forall kk, (kk < n)%nat -> vis segs m (boff x kk).
Proof.
  intros m iovp iovs bss mp k x n Harr Hbufs Hin kk Hkk. apply in_app_or in Hin as [Hin|Hin].
  - apply copy_iovecs_accesses_in in Hin as (-> & j & Hj & ->). rewrite boff_add.
    rewrite <- (wa_unsigned_id iovp).
    pose proof (bytes_in_boff _ _ _ (16 * j + kk) Harr ltac:(rewrite length_iovec_bytes; lia)) as Hb.
    destruct (nth_error (iovec_bytes iovs) (16 * j + kk)) as [b|] eqn:E; [| apply nth_error_None in E; rewrite length_iovec_bytes in E; lia].
    exact (vis_of_mrd m _ b Hb).
  - apply iov_prefix_accesses_in in Hin as (len & Hin & Hle).
    destruct (Forall2_In_l' _ _ _ _ Hbufs Hin) as (bsj & _ & (L1 & L2 & L3)). cbn [fst snd] in L1, L3.
    assert (HL : word_to_nat len = length bsj). { subst len. unfold word_to_nat. rewrite u64_lit by lia. lia. }
    rewrite <- (wa_unsigned_id x).
    pose proof (bytes_in_boff _ _ _ kk L3 ltac:(lia)) as Hb.
    destruct (nth_error bsj kk) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    exact (vis_of_mrd m _ b Hb).
Qed.

Section Writev.
  Variables (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m : mem) (mo : Model) (g : lghost).
  Variables (fd : Z) (iovs : list (word * word)) (bss : list (list byte)).
  Hypothesis Hfd : 0 < fd < 2^31.
  Hypothesis H10 : reg_get R 10 = Z_to_bv 64 fd.
  Hypothesis Hlk : fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis H12 : reg_get R 12 = Z_to_bv 64 (Z.of_nat (length iovs)).
  Hypothesis Hcnt : (1 <= length iovs <= 1024)%nat.
  Hypothesis Harr : bytes_at segs m (bv_unsigned (reg_get R 11)) (iovec_bytes iovs).
  Hypothesis Hbufs : Forall2 (iov_ok (mrd segs m)) iovs bss.
  (* [comment removed for export] *)
  Hypothesis Htask : bv_unsigned (reg_get R 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE.
  Hypothesis Hbtask : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs.

  Let svc := MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs).
  Let bs := concat bss.
  Let rin (mr : mem) := sys_input segs (MSsvc R F pc (Z_to_bv 64 66) fc rv mr (seg_rom segs)) (Z_to_bv 64 66).

  (* [comment removed for export] *)
  Lemma lrz_writev : forall (T : nat -> TSet),
    1 <= Z.of_nat (length bs) <= 67108864 ->   (* [comment removed for export] *)
    (forall k, (1 <= k <= length bs)%nat -> LRZ (nret svc (eff0 (Z_to_bv 64 (Z.of_nat k)))) mo g (T k)) ->
    LRZ svc mo g (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
  Proof.
    intros T [Hb1 Hbmax] HK.
    assert (Hnb : (1 <= length bs)%nat) by lia.
    apply (lrz_node svc mo g (Z_to_bv 64 66) (wr_index bs) (wr_full bs Hnb)
             (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (fun i => T (proj1_sig i)) eq_refl eq_refl).
    intros mr mat HI. cbn [ms_mem svc MSsvc] in HI.
    pose proof (bytes_in_real _ _ _ _ _ _ _ HI Harr) as Harr'.
    pose proof (Forall2_iov_ok_real _ _ _ _ _ _ _ HI Hbufs) as Hbufs'.
    pose proof (writev_outcome_i (rin mr) (real mo mat) fd (reg_get R 11) iovs bss
                  eq_refl H10 Hfd Hlk eq_refl H12 Hcnt Harr' Hbufs' Htask Hbtask Hb1 Hbmax) as Hiff.
    cbv zeta in Hiff. fold bs in Hiff.
    set (CA := copy_iovecs_accesses (in_mem (rin mr)) (reg_get R 11) (length iovs)) in Hiff.
    pose (effs := fun i : wr_index bs =>
            mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
    assert (ACC : forall i x n, In (x, n) (syscall_effect_accesses (effs i)) -> forall kk, (kk < n)%nat -> vis segs m (boff x kk)).
    { intros [k Hk] x n Hin. cbv beta iota delta [effs proj1_sig syscall_effect_accesses eff_copyins eff_writes write_accesses] in Hin.
      rewrite app_nil_r in Hin. exact (writev_accesses_vis m (reg_get R 11) iovs bss _ k x n Harr Hbufs Hin). }
    exists effs, (fun _ => mo), (fun _ => g), (fun _ => m),
      (fun i => newly_materialized_pages (m_vm_lazy mo) mat (syscall_effect_accesses (effs i)) ++ mat).
    split.
    - intros o. unfold svc. rewrite msw_MSsvc. fold (rin mr). rewrite Hiff. split.
      + intros (k & Hk & ->). exists (exist _ k Hk). reflexivity.
      + intros [[k Hk] ->]. exists k. split; [exact Hk| reflexivity].
    - intros i. destruct (lmaterialize segs g mo mat m mr (syscall_effect_accesses (effs i)) HI (ACC i)) as [Hmat HI2].
      split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|].
      assert (Em : forall ms0, nret ms0 (effs i) = nret ms0 (eff0 (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) by (intros ms0; reflexivity).
      rewrite !Em. split.
      + unfold svc. rewrite msw_MSsvc. unfold eff0. rewrite mem_nret_plain. cbn [ms_mem MSsvc]. exact HI2.
      + apply (lrz_eq _ (nret svc (eff0 (Z_to_bv 64 (Z.of_nat (proj1_sig i)))))).
        { unfold eff0. transitivity (msw (nret svc (mkEffect (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] []))
                                        (ms_mem (nret svc (mkEffect (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] []))));
            [rewrite mem_nret_plain; reflexivity| apply msw_nret_self]. }
        destruct i as [k Hk]. apply HK. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma lrz_writev_wall : forall (K : TSet),
    1 <= Z.of_nat (length bs) <= 67108864 ->   (* [comment removed for export] *)
    K [] ->
    (forall k, (1 <= k <= length bs)%nat ->
       LRZ (nret svc (eff0 (Z_to_bv 64 (Z.of_nat k)))) mo g (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)) ->
    LRZ svc mo g (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs) K).
  Proof.
    intros K Hb HK0 HK. eapply lrz_conseq.
    - apply (lrz_writev (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K) Hb HK).
    - apply t_alt_wall; [exact HK0| lia].
  Qed.
End Writev.

(* [comment removed for export] *)
Lemma lrz_writev_zero : forall R F pc fc rv m mo g (fd : Z) iovs bss K,
  0 < fd < 2^31 ->
  reg_get R 10 = Z_to_bv 64 fd ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length iovs)) -> (1 <= length iovs <= 1024)%nat ->
  bytes_at segs m (bv_unsigned (reg_get R 11)) (iovec_bytes iovs) ->
  Forall2 (iov_ok (mrd segs m)) iovs bss ->
  bv_unsigned (reg_get R 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->                           (* [comment removed for export] *)
  Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs ->
  concat bss = [] ->
  LRZ (nret (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) (eff0 (Z_to_bv 64 0))) mo g K ->
  LRZ (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) mo g K.
Proof.
  intros R F pc fc rv m mo g fd iovs bss K Hfd H10 Hlk H12 Hcnt Harr Hbufs Htask Hbtask Hnil HK.
  set (svc := MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) in *.
  pose proof (iovs_total_ok _ _ _ Hbufs) as Htot. rewrite Hnil in Htot. cbn in Htot.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  apply (lrz_node_silent svc mo g (Z_to_bv 64 66) unit tt K eq_refl eq_refl).
  intros mr mat HI. cbn [ms_mem svc MSsvc] in HI.
  pose proof (bytes_in_real _ _ _ _ _ _ _ HI Harr) as Harr'.
  pose proof (Forall2_iov_ok_real _ _ _ _ _ _ _ HI Hbufs) as Hbufs'.
  set (rin := sys_input segs (MSsvc R F pc (Z_to_bv 64 66) fc rv mr (seg_rom segs)) (Z_to_bv 64 66)).
  set (eff := with_copyins (copy_iovecs_accesses (in_mem rin) (reg_get R 11) (length iovs)) (mkEffect (Z_to_bv 64 0) [] [])).
  assert (ACC : forall x n, In (x, n) (syscall_effect_accesses eff) -> forall kk, (kk < n)%nat -> vis segs m (boff x kk)).
  { intros x n Hin. unfold eff in Hin.
    cbv beta iota delta [syscall_effect_accesses with_copyins eff_copyins eff_writes eff_ret eff_zeros eff_unmaps eff_copies write_accesses] in Hin.
    apply (writev_accesses_vis m (reg_get R 11) iovs bss (in_mem rin) 0%nat x n Harr Hbufs).
    apply in_app_or in Hin as [Hin|[]]. apply in_or_app. left. exact Hin. }
  destruct (lmaterialize segs g mo mat m mr (syscall_effect_accesses eff) HI ACC) as [Hmat HI2].
  exists (fun _ => eff), (fun _ => mo), (fun _ => g), (fun _ => m),
    (fun _ => newly_materialized_pages (m_vm_lazy mo) mat (syscall_effect_accesses eff) ++ mat).
  split.
  - intros o. unfold svc. rewrite msw_MSsvc. rewrite (syscall_spec_66 _ _ o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite svc_a0, svc_a1, svc_a2, H10, H12, fd32_id by (rewrite u64_lit; lia).
    rewrite (writev_chan_zero_outcome _ _ _ _ (real mo mat) o (Z_to_bv 64 fd) iovs).
    + unfold eff. rewrite Hwn. fold rin. split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
    + rewrite m_fds_real. exact Hlk.
    + apply w_is0_pos. rewrite u64_lit; lia.
    + unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
    + apply w_is0_pos. rewrite u64_lit; lia.
    + unfold IOV_MAX. rewrite u64_lit; lia.
    + rewrite Hwn. fold rin. change (in_mem rin) with (mrd segs mr). rewrite <- (wa_unsigned_id (reg_get R 11)).
      apply copy_iovecs_aux_bytes_in; [exact Harr'|].
      eapply Forall_impl; [|exact (Forall2_iov_ok_lens _ _ _ Hbufs)]. intros [b l] Hb. cbn [snd] in *. rewrite Hnil in Hb. cbn in Hb. lia.
    + apply access_okb_intro_Z; rewrite u64_lit by lia; lia.
    + unfold iovs_access_okb. apply forallb_forall. intros [b l] Hin.
      rewrite Forall_forall in Hbtask. specialize (Hbtask _ Hin). cbn [fst snd] in *.
      apply access_okb_intro. exact Hbtask.
    + exact Htot.
    + vm_compute. discriminate.
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|]. split.
    + unfold svc. rewrite msw_MSsvc. unfold eff. rewrite nret_copyins'. unfold eff0. rewrite mem_nret_plain. cbn [ms_mem MSsvc]. exact HI2.
    + unfold eff. rewrite nret_copyins'.
      eapply lrz_eq; [| exact HK].
      transitivity (msw (nret svc (mkEffect (Z_to_bv 64 0) [] [])) (ms_mem (nret svc (mkEffect (Z_to_bv 64 0) [] []))));
        [rewrite mem_nret_plain; reflexivity| apply msw_nret_self].
Qed.

End WithSegs.

Arguments LRZ segs {ACEIL} ms mo g T /.   (* [comment removed for export] *)
