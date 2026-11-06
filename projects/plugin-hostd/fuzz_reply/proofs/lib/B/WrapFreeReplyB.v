(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/WrapFreeReplyA.v at commit bdc582aa2c4 as lib/B/WrapFreeReplyB.v, with its module paths changed (lib.A to lib.B, except the image-free ADIfaceImgA and the one params file CfParamsReply; the image twins A<r> to Y<r>, CfImgA / CfImg_A to CfImgB / CfImg_B; the walk modules WrapFreeA<x> to WrapFreeB<x>, WrapAKit to WrapBKit, WrapFreeReplyA to WrapFreeReplyB; the three exported names wrap_free_call_reply_A, wrap_free_ret_reply_A_rh, wrap_free_walk_rh_reply_A to _B), and no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WFree; image B twin a Theorem Labs lane WFREE-B): AFREE_CF premise #13 at plugin-hostd/fuzz_reply
   image B (asan-ubsan, pin 10ffb5f9202a, unstripped twin 3389287e1d61): the free interceptor's call segment and its PRIMED
   return segment. rule 24: no released proof (RULE24-wrapfree.md sha256 a048293a91fe; internal record); the walk is lib/A's WrapFreeA*.v (A2's
   fuzz_preset family relocated to image A by a Theorem Labs lane) relocated A -> B by alreloc a5c53bb2bed4 (WrapFreeB*.v; the nine
   walk functions are byte-equal modulo pc-relative words between the two images, every code address +0x58).

   The instances (agreed with a Theorem Labs lane 18:21Z): segs := im_segs (AImg_reply, = tfibsegs), B := TfibB (YD2l.v),
   atpD := atp_cf (= 1, asan_free's FROM_MALLOC), ARX := YGcfInstBase.ARXq_cf TfibB (fun i => i = as_inst TfibB),
   K := K_reply (WrapFreeBK.v, A2's K_A relocated).
   - wrap_free_call_reply_B: the type of field wf_call of YGcfMallocCompose.wrap_free_walk_cf (YGcfMallocCompose.v:492-500)
     at those instances, no extra premise.
   - wrap_free_ret_reply_B_rh: field wf_ret's text (YGcfMallocCompose.v:502-515) at those instances with ONE change: the
     Deallocate post free_dpost_cf (:511-512) is the primed YGcfRehidePost.dealloc_post_raw_rh (YGcfRehidePost.v:402).
   The primed record wrap_free_walk_rh_reply_B (YGcfMallocComposeRh.wrap_free_walk_cf_rh, YGcfMallocComposeRh.v:90; the
   three files cited are lib/B's at fu2-mp d4ca4d1e070a) is assembled from the two (a Theorem Labs lane's decision 2026-10-30); no
   unprimed record or theorem is exported (the unprimed fit is a Check). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK0j YK15 YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGtop DeallocG YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import WrapFreeBK.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require WrapFreeBRXq WrapFreeBTop WrapFreeBRet.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocComposeRh.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.

(* HXI (WrapFreeBTop.v Section k) at the reply's call-site relation: a projection. IOK by as_inst TfibB = TFIB_INST
   (YD2l.v:18), ARcf given, xs_mapped_cf from that ARcf (YGcfXs.ARcf_xsm: the ledger's alc_xs; on fu1 ARX_cf carries no
   cell conjunct, the cells being ARmcf's fields amc_exh_cell / amc_errb_cells), qtight from acall_pre_cf's qmeter_cf
   (its first conjunct; finit_cf changes no field qtight reads). *)
Lemma ARXq_reply_HXI : forall ly S Hp W regs mem md ch memD mat,
  acall_pre_cf tfibsegs TfibB ly S Hp W regs mem md ch ->
  ARcf tfibsegs TfibB ly (finit_cf S) Hp W memD (with_vm_backing (m_vm_lazy md) mat md) ->
  ARXq_cf TfibB (fun i => i = as_inst TfibB) Hp TFIB_INST ly (finit_cf S) W memD (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S Hp W regs mem md ch memD mat PRE AR.
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QM & _).
split; [split; [reflexivity | split; [exact AR | exact (YGcfXs.ARcf_xsm _ _ _ _ _ _ _ _ AR)]] | exact (proj1 QM)].
Qed.

(* F1 at fuzz_reply image A. *)
Lemma wrap_free_call_reply_B : forall ly S Hp W regs mem md p n ch,
  fentry_cf im_segs TfibB ly S Hp W regs mem md p n ch -> rpreD_free_cf TfibB (finit_cf S) n ->
  SRr im_segs W (cfg_at im_segs (pc_wrap_free (as_code TfibB)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at im_segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf im_segs TfibB atp_cf (ARXq_cf TfibB (fun i => i = as_inst TfibB)) Hp inst so bp ly (finit_cf S) W1
      regsD memD mdD p n (ftr_cf TfibB ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_cf im_segs TfibB ly S regs W mem W1 memD /\ errno_kept_cf TfibB mem memD /\
    K_reply ly S Hp W regs mem md p n ch W1 regsD memD mdD).
Proof.
intros ly S Hp W regs mem md p n ch ENT RP.
pose proof (proj1 ENT) as (_ & _ & _ & _ & BOT & _).
exact (WrapFreeBTop.wf_call_FIX_A TfibB TfibB_syms (ARXq_cf TfibB (fun i => i = as_inst TfibB)) ARXq_reply_HXI eq_refl
  ly S Hp W regs mem md p n ch ENT RP ltac:(clear - BOT; lia)).
Qed.

(* F2 at fuzz_reply image A over the primed Deallocate post. *)
Lemma wrap_free_ret_reply_B_rh : forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf im_segs TfibB ly S Hp W regs mem md p n ch ->
  K_reply ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf im_segs TfibB atp_cf (ARXq_cf TfibB (fun i => i = as_inst TfibB)) Hp inst so bp ly (finit_cf S) W1
    regsD memD mdD p n (ftr_cf TfibB ly regs ch) ->
  YGcfRehidePost.dealloc_post_raw_rh im_segs TfibB (ARXq_cf TfibB (fun i => i = as_inst TfibB) Hp) (aowned TfibB) inst ly
    (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr TfibB ly p <= a < sptr_addr TfibB ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf TfibB ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr im_segs W2 (cfg_at im_segs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at im_segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARXq_cf TfibB (fun i => i = as_inst TfibB) Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep im_segs TfibB regs W2 mem2 W' mem' /\ RGtop.rwin im_segs regs W' mem' /\
    errno_kept_cf TfibB mem2 mem').
Proof.
exact (WrapFreeBRet.wf_ret_gen_rh TfibB TfibB_syms (ARXq_cf TfibB (fun i => i = as_inst TfibB))
  (WrapFreeBRXq.ARXq_reply_HXA TfibB (fun i => i = as_inst TfibB))
  (WrapFreeBRXq.ARXq_reply_HXF TfibB (fun i => i = as_inst TfibB))).
Qed.

(* The fit check: wrap_free_call_reply_B is field wf_call of the record at these instances (no record is defined). *)
Check (fun Hret => {| wf_call := wrap_free_call_reply_B; wf_ret := Hret |}
  : wrap_free_walk_cf im_segs TfibB atp_cf (ARXq_cf TfibB (fun i => i = as_inst TfibB)) K_reply).

(* The primed walk record at fuzz_reply image B (YGcfMallocComposeRh.v:90; fields wfr_call :91, wfr_ret :100). *)
Theorem wrap_free_walk_rh_reply_B :
  wrap_free_walk_cf_rh im_segs TfibB atp_cf (ARXq_cf TfibB (fun i => i = as_inst TfibB)) K_reply.
Proof.
exact {| wfr_call := wrap_free_call_reply_B; wfr_ret := wrap_free_ret_reply_B_rh |}.
Qed.

End r.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check wrap_free_call_reply_B.
Print Assumptions wrap_free_call_reply_B.
Check wrap_free_ret_reply_B_rh.
Print Assumptions wrap_free_ret_reply_B_rh.
Check wrap_free_walk_rh_reply_B.
Print Assumptions wrap_free_walk_rh_reply_B.
