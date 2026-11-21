(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from RealizesEqv.v: realizes_cfg_eqv and the corollaries the start-up junction uses, restated over BudgetWit.Rzb.rzb, with their released proofs; the node case also carries the grant check across ms_eqv. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: both sections take the hypothesis vdso_image segs = None that RealizesEqv.v's node_ok_xfer takes there, and pass it on; rzb_cfg_eqv carries a node's RomBase.sys_rob by RealizesEqv.sys_rob_eqv. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RealizesEqv.
Import RegsEqv0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
(* RealizesEqv.v's [node_ok_xfer] takes it at this model: a binary's own segment list has no
   vDSO text, so the vDSO arms of [sstep_cfg] never fire on it. *)
Hypothesis Hvi : vdso_image segs = None.

Theorem rzb_cfg_eqv : forall c T,
  rzb segs c T -> forall c', cfg_eqv c c' -> rzb segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hrob Hg Hk IH | c Hh | c T T' H IH Heq];
    intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [Hms Hmo]; simpl in Hms, Hmo; subst mo'.
    destruct (node_ok_xfer segs Hvi ms ms' mo I evs nx Hms Hnode) as [Hnode' Hx].
    apply (rzb_node segs (mkCfg ms' mo) I evs (fun i => xfer segs ms' mo (nx i)) T i0 Hnode').
    + eapply sys_rob_eqv; [exact Hms | exact Hrob].
    + intros x8 Hx8. apply (Hg x8). cbn [cfg_ms] in Hx8 |- *.
      destruct Hms as (_ & _ & _ & Hsv & _). rewrite Hsv. exact Hx8.
    + intros i. apply (IH i). apply Hx.
  - apply rzb_halt. destruct Heqv as [_ <-]. exact Hh.
  - apply (rzb_conseq segs c' T T'); [apply IH; exact Heqv | exact Heq].
Qed.

Theorem rzb_ms_eqv : forall ms1 ms2 mo T,
  ms_eqv ms1 ms2 ->
  rzb segs (mkCfg ms1 mo) T -> rzb segs (mkCfg ms2 mo) T.
Proof.
  intros ms1 ms2 mo T Heqv H. apply (rzb_cfg_eqv _ _ H). split; [exact Heqv | reflexivity].
Qed.

Theorem rzb_eqv_iff : forall ms1 ms2 mo T,
  ms_eqv ms1 ms2 ->
  rzb segs (mkCfg ms1 mo) T <-> rzb segs (mkCfg ms2 mo) T.
Proof.
  intros ms1 ms2 mo T Heqv. split; apply rzb_ms_eqv; [exact Heqv | apply ms_eqv_sym; exact Heqv].
Qed.

Corollary rzb_regs_eqv : forall (regs1 regs2 F : bvmap 5 word) (pc : word) svc rv fc
    (mem rom : word -> option byte) mo T,
  (forall r, is_x0 r = false -> reg_get regs1 r = reg_get regs2 r) ->
  rzb segs (mkCfg {| ms_regs := regs1; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := svc;
                     ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} mo) T <->
  rzb segs (mkCfg {| ms_regs := regs2; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := svc;
                     ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} mo) T.
Proof.
  intros * Hr. apply rzb_eqv_iff. split; [exact Hr|]. split; [apply regs_eqv_refl|]. repeat split; reflexivity.
Qed.

Corollary rzb_mkst_of_MS : forall (regs R : bvmap 5 word) (pc : word)
    (mem : word -> option byte) mo T,
  (forall r : reg, is_x0 r = false -> OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.getr regs r = reg_get R r) ->
  rzb segs (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS R bvmap_empty pc (Z_to_bv 32 0) None mem
                     (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)) mo) T ->
  rzb segs (mkCfg (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.fx0 regs pc mem
                     (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)) mo) T.
Proof.
  intros regs R pc mem mo T Hr H.
  assert (Hr' : forall r : reg, is_x0 r = false -> reg_get regs r = reg_get R r).
  { intros r E. rewrite <- (getr_reg_get regs r E). apply Hr. exact E. }
  change (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)
    with (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs).
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst.
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS in H.
  exact (proj2 (rzb_regs_eqv regs R bvmap_empty pc None None (Z_to_bv 32 0) mem _ mo T Hr') H).
Qed.

End WithSegs.

Section Junction.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Corollary rzb_mkst_of_mkR : forall (regs : bvmap 5 word) (pc : word)
    (mem : word -> option byte) mo T,
  rzb segs (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (mkR_of regs) bvmap_empty pc (Z_to_bv 32 0) None mem
                     (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom segs)) mo) T ->
  rzb segs (mkCfg (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.mkst OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.fx0 regs pc mem
                     (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.seg_rom segs)) mo) T.
Proof.
  intros regs pc mem mo T H. apply (rzb_mkst_of_MS segs Hvi regs (mkR_of regs)); [|exact H].
  intros r Hr. apply getr_mkR_of. exact Hr.
Qed.
End Junction.
