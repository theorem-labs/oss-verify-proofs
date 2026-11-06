(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WalkB2; integrator ReallocPrimary).
   rule 24: no function proved here (instance lemmas for an interface; the free interceptor walk itself is A2's
   WrapFreeA* text, to be relocated from its sha of record).

   The call-site relation of the free composition at fuzz_reply image A is F2a's ARXq_cf at IOK := (fun i => i =
   as_inst B) (YGcfInstBase.ARXq_cf; a Theorem Labs lane's Deallocate instance, through YGcfMallocComposeE's
   afree_realizes_cf_of_parts_m, which takes one ARX for both premises).  A2's free-interceptor walk is generic in that
   relation (WrapFreeATop.v Section k: Variable ARX; Hypotheses HXI / HXA / HXF; WrapFreeARet.wf_ret_gen over
   ARX_ARcf + HXF).  This file gives the instance lemmas at ARXq_cf.

   HXA and HXF are here; HXF is stated against A2's type at f6c2b01c2457 (WrapFreeATop.v:86-90), which has the
   view-equality premise (A2's alc_xs rebase keeps it).  HXI is NOT stated yet, on purpose: on this base ARXq_cf's
   conjuncts exh_cell_cf / errb_cells_cf (YGcfInstBase.v:95-98) are memory-cell facts that ARcf does not give
   (region_cells_cf drops the exhausted byte; the errbuf cells are ARX_cf's own), and acall_pre_cf
   (Reusable/YG0dcf.v:57-80) carries neither, so HXI's ARX at Deallocate's entry would be unprovable.  Main's decision
   (2026-10-30, option (i)): the two cells become ARcf / ALedger_cf fields (AbudgetRestate's field round 2),
   acall_pre_cf unchanged; HXI's statement does not change and becomes a projection on that base. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK0j YK15 YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfXsMapped.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The unit's instance-object predicate (preset's and F2a's IOK). *)
Definition IOK_reply (B : asyms) : Z -> Prop := fun i => i = as_inst B.

(* HXA: the call-site relation gives ARcf (A2's WrapFreeATop.v:85 / WrapFreeARet.wf_ret_gen's ARX_ARcf premise). At
   AImg_reply, im_segs is tfibsegs by delta, so ARXq_cf is an ARXh_t tfibsegs. *)
Lemma ARXq_reply_HXA : forall (B : asyms) (IOK : Z -> Prop),
  ARX_ARcf tfibsegs B (YGcfInstBase.ARXq_cf B IOK).
Proof. intros B IOK Hp inst ly S W mem md [[_ [A _]] _]. exact A. Qed.

(* HXF: the call-site relation survives a view-equal memory and the materialization (A2's WrapFreeATop.v:86-90 at
   f6c2b01c2457, the second premise being the view equality, the third ARcf at the new memory).  IOK and qtight do not
   read memory; ARcf is given; xs_mapped_cf moves through with_vm_backing (YGcfXsMapped.xs_mapped_cf_wvb).  On fu1
   b70f01ca629 ARX_cf has no cell conjuncts (they are ARcf's fields amc_exh_cell / amc_errb_cells, YGcfInstBase.v:72-79),
   so the given ARcf carries them. *)
Lemma ARXq_reply_HXF : forall (B : asyms) (IOK : Z -> Prop) Hp inst ly S W mem md mem' mat,
  YGcfInstBase.ARXq_cf B IOK Hp inst ly S W mem md ->
  (forall a, aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  YGcfInstBase.ARXq_cf B IOK Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros B IOK Hp inst ly S W mem md mem' mat [[I [_ X]] Q] VEQ A'.
split; [| exact Q].
split; [exact I|]. split; [exact A'|].
exact (YGcfXsMapped.xs_mapped_cf_wvb ly S md (m_vm_lazy md) mat X).
Qed.

End a.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check ARXq_reply_HXA.
Print Assumptions ARXq_reply_HXA.
Check ARXq_reply_HXF.
Print Assumptions ARXq_reply_HXF.
