(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane B2, ASM rows; integrator ReallocPrimary).
   rule 24: no function proved here (instance discharge): this file takes the fs_iface-form contracts of
   __asan_stack_malloc_0 (lib/A/RT_asan_stack_malloc_0_x.v, a Theorem Labs lane, at commit 6b4f6082575) and
   __asan_stack_malloc_1 (lib/A/RT_asan_stack_malloc_1_x.v, lane B2) to fuzz_reply's top relation.
   Reuse search for the two functions: `proof-index __asan_stack_malloc_0 __asan_stack_malloc_1`
   exit 0, the frame note LOOKUP-ASM-stackmalloc.txt (sha256 531e6f2a43ce; internal record); rule-24 check
   AsmLookupCheck (sonic): SEND BACK for class 0 (already done, in flight, at fuzz_reply), CONFIRM for class 1.

   The rows ASM0 / ASM1 (TOPX-HYPS.md (sha256 47b88854dcb3; internal record) table, rows ASM0 and ASM1) ask for
   `astack_malloc_pres_x segs TfibB ARX cid` at top_x's relation
     ARX := fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []
   (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:87-88; segs = pa_segs PB_fr = tfibsegs by reflexivity, Rt/Bcmp.v:44).
   The class walks are proved for ANY relation with FCiface.fs_iface; FCifaceCf.fs_iface_ARcf gives it for ARcf
   from AR_laws_cf, and YG0lawscf.AR_laws_ok_cf discharges AR_laws_cf unconditionally.  The one step this file adds
   is the Hp = [] conjunct ([fs_iface_and_hp]): every field of fs_iface is either a projection of the relation (read
   at the pre state only) or a law whose post is the relation at the SAME Hp (fi_malloc_law, fi_frame), so the
   conjunct rides through unchanged.  [ARX_asm] is top_x's ARX written out over tfibsegs; AsmTopXEq.v shows the two
   are equal by reflexivity and restates the rows at top_x's own ARX. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0s YG0q YG0t YF0v YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf YGcfPres.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyRelroGeoA ReplyKeptAroA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FCifaceCf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_frame_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_asan_stack_malloc_0_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_asan_stack_malloc_1_x.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module FCI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Module FCC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FCifaceCf.
Module WFX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_frame_x.
Module SM0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_asan_stack_malloc_0_x.
Module SM1 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_asan_stack_malloc_1_x.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the Hp = [] conjunct rides through fs_iface ---- *)
Lemma fs_iface_and_hp : forall (segs : list Segment) (B : asyms)
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
  FCI.fs_iface segs B ARx ->
  FCI.fs_iface segs B (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ Hp = []).
Proof.
intros segs B ARx FI.
destruct FI as [Fh Fl Fi Ft Fc Ffc Ffl FaF FaS Fo Fos FoF Fm Fs Ff Ffr].
unfold FCI.astack_malloc_law_x, FCI.AR_stack_law_x, FCI.AR_frame_law_x, FCI.AR_frames_law_x in *.
constructor; unfold FCI.astack_malloc_law_x, FCI.AR_stack_law_x, FCI.AR_frame_law_x, FCI.AR_frames_law_x.
- intros ly S Hp W mem md [HA _]. exact (Fh ly S Hp W mem md HA).
- intros ly S Hp W mem md [HA _]. exact (Fl ly S Hp W mem md HA).
- intros ly S Hp W mem md sg [HA _]. exact (Fi ly S Hp W mem md sg HA).
- intros ly S Hp W mem md [HA _]. exact (Ft ly S Hp W mem md HA).
- intros ly S Hp W mem md [HA _]. exact (Fc ly S Hp W mem md HA).
- intros ly S Hp W mem md [HA _]. exact (Ffc ly S Hp W mem md HA).
- intros ly S Hp W mem md [HA _]. exact (Ffl ly S Hp W mem md HA).
- intros ly S Hp W mem md [HA _]. exact (FaF ly S Hp W mem md HA).
- intros ly S Hp W mem md [HA _]. exact (FaS ly S Hp W mem md HA).
- intros ly S Hp W mem md cid pos a [HA _]. exact (Fo ly S Hp W mem md cid pos a HA).
- intros ly S Hp W mem md cid pos a [HA _]. exact (Fos ly S Hp W mem md cid pos a HA).
- intros ly S Hp W mem md a [HA _]. exact (FoF ly S Hp W mem md a HA).
- (* the malloc law: its post is the relation at the same Hp *)
  intros ly S Hp W mem md mem' md' cid pos hint' [HA HH] Hc Hprobe. cbv zeta.
  intros H1 H2 H3 H4 H5 H6 H7 H8.
  split; [exact (Fm ly S Hp W mem md mem' md' cid pos hint' HA Hc Hprobe H1 H2 H3 H4 H5 H6 H7 H8) | exact HH].
- intros ly S Hp W mem md a [HA _]. exact (Fs ly S Hp W mem md a HA).
- (* the frame law: its post is the relation at the same Hp *)
  intros ly S Hp W mem md mem' md' [HA HH] H1 H2 H3 H4 H5 H6.
  split; [exact (Ff ly S Hp W mem md mem' md' HA H1 H2 H3 H4 H5 H6) | exact HH].
- intros ly S Hp W mem md cid pos [HA _]. exact (Ffr ly S Hp W mem md cid pos HA).
Qed.

(* ---- the relation the class walks are proved at: top_x's ARX before QMm W1, ARcf /\ Hp = [] ---- *)
Definition ARX_asm0 : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) tfibsegs TfibB ly S Hp W mem md /\ Hp = [].

Lemma fs_iface_ARX_asm0 : FCI.fs_iface tfibsegs TfibB ARX_asm0.
Proof.
unfold ARX_asm0. apply fs_iface_and_hp.
exact (FCC.fs_iface_ARcf (cp := CfParams_reply) tfibsegs TfibB (AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)).
Qed.

(* ---- QMm W1 (image A by a Theorem Labs lane, 2026-10-31; token for token a Theorem Labs lane's image-B text, B/AsmTopX.v at
   80b0ca840db6, with CfImg_B -> CfImg_A and ReplyRelroGeoB.relro_seg_reply_B -> ReplyRelroGeoA.relro_seg_reply_A):
   top_x's ARX gains the read-only bytes arodata_ok_cf as its last conjunct. fs_iface's malloc / frame laws keep only
   OWNED views, so that conjunct does not ride through fs_iface; it comes from astack_malloc_pres_x's own post instead
   (A/W_frame_x.v astack_malloc_pres_x: W' = W, and every byte owned neither before nor after and off the call's stack
   window keeps its view). astack_malloc_pres_x_and lifts a class walk proved at `R /\ Hp = []` to
   `R /\ Hp = [] /\ Q mem` for any memory fact Q that such a view frame keeps. ---- *)
Lemma astack_malloc_pres_x_and : forall (segs : list Segment) (B : asyms)
  (R : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
  (Q : (word -> option byte) -> Prop) (cid : Z),
  (forall ly S S' Hp W mem md mem' md' sp, R ly S Hp W mem md -> R ly S' Hp W mem' md' -> ly_stk_lo ly + ESTACK <= sp ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (sp - ESTACK <= a < sp) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     Q mem -> Q mem') ->
  WFX.astack_malloc_pres_x segs B (fun ly S Hp W mem md => R ly S Hp W mem md /\ Hp = []) cid ->
  WFX.astack_malloc_pres_x segs B (fun ly S Hp W mem md => R ly S Hp W mem md /\ Hp = [] /\ Q mem) cid.
Proof.
intros segs B R Q cid QK H ly S Hp W regs mem md pos S' HPRE Hcnt Hpath.
destruct HPRE as ((HA & HH & HQ) & Hret & Hal & Hlo & Hhi & Hpres & Hgp & Htp).
eapply SRr_mono; [exact (H ly S Hp W regs mem md pos S'
  (conj (conj HA HH) (conj Hret (conj Hal (conj Hlo (conj Hhi (conj Hpres (conj Hgp Htp))))))) Hcnt Hpath)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & (HA' & HH') & Hrest).
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [|exact Hrest].
split; [exact HA'|]. split; [exact HH'|].
destruct Hrest as (_ & _ & _ & _ & _ & _ & Hview & _).
exact (QK ly S S' Hp W mem md mem' md' (spZ regs) HA HA' Hlo Hview HQ).
Qed.

(* the view frame keeps arodata_ok_cf at image A: a non-owned RELRO byte is no aowned byte at either state
   (relro_apart_cf, from ARcf and ReplyRelroGeoA.relro_seg_reply_A), and it lies in the image, below kImgEnd =
   0x677000, while the stack starts at kHighMemBeg = 0x10007fff8000 or above (layout_ok's lo_top) *)
Lemma aro_keep_asm : forall ly S S' Hp (W : world tfibsegs) mem md mem' md' sp,
  ARcf (ci := CfImg_A) (cp := CfParams_reply) tfibsegs TfibB ly S Hp W mem md ->
  ARcf (ci := CfImg_A) (cp := CfParams_reply) tfibsegs TfibB ly S' Hp W mem' md' -> ly_stk_lo ly + ESTACK <= sp ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned TfibB ly S a -> ~ aowned TfibB ly S' a -> ~ (sp - ESTACK <= a < sp) ->
     aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  @YG0dcf.arodata_ok_cf CfImg_A tfibsegs TfibB mem -> @YG0dcf.arodata_ok_cf CfImg_A tfibsegs TfibB mem'.
Proof.
intros ly S S' Hp W mem md mem' md' sp HA HA' Hlo HV AR a b E Ha NO.
destruct (YG0dcf.relro_apart_cf tfibsegs TfibB ly S Hp W mem md a HA ReplyRelroGeoA.relro_seg_reply_A Ha NO)
  as (RI & _ & NA & _).
destruct (YG0dcf.relro_apart_cf tfibsegs TfibB ly S' Hp W mem' md' a HA' ReplyRelroGeoA.relro_seg_reply_A Ha NO)
  as (_ & _ & NA' & _).
destruct (ReplyKeptAroA.aro_kept_A a Ha NO) as (Hb & HKx).
assert (HK : kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top _ (amc_layout _ _ _ _ _ (proj1 HA))) as T.
  repeat match type of T with _ /\ _ => destruct T as [_ T] end. exact T. }
assert (HS : ~ (sp - ESTACK <= a < sp)) by (unfold kHighMemBeg, kImgEnd, ESTACK in *; lia).
pose proof (HV a Hb NA NA' HS) as X.
assert (Hi : in_img tfibsegs a) by exact (proj1 HKx).
unfold aview, mbyte, mrestrict in X.
rewrite (YGcfPres.cfp_img_unhidden tfibsegs W a Hb Hi), E in X. cbn [option_map] in X.
destruct (mem (Z_to_bv 64 a)) as [b0|] eqn:E0; cbn [option_map] in X.
- rewrite (AR a b0 E0 Ha NO). injection X as X. f_equal. apply bv_eq. symmetry. exact X.
- destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [r|] eqn:Er; cbn [option_map] in X; [|discriminate X].
  injection X as X. f_equal. apply bv_eq. symmetry. exact X.
Qed.

(* ---- top_x's relation, over tfibsegs: lib/A/W_LLVMFuzzerTestOneInput_top_x.v's Definition ARX with segs := tfibsegs,
   in its own association (ARcf /\ Hp = [] /\ arodata_ok_cf; QMm W1) ---- *)
Definition ARX_asm : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) tfibsegs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A tfibsegs TfibB mem.

(* ---- ASM0: __asan_stack_malloc_0 at top_x's relation ---- *)
Theorem asm0_pres_ARX : WFX.astack_malloc_pres_x tfibsegs TfibB ARX_asm 0.
Proof.
apply (astack_malloc_pres_x_and tfibsegs TfibB _ _ 0 aro_keep_asm).
exact (SM0.stack_malloc0_contract_pres_x TfibB ARX_asm0 fs_iface_ARX_asm0 TfibB_syms).
Qed.

(* ---- ASM1: __asan_stack_malloc_1 at top_x's relation ---- *)
Theorem asm1_pres_ARX : WFX.astack_malloc_pres_x tfibsegs TfibB ARX_asm 1.
Proof.
apply (astack_malloc_pres_x_and tfibsegs TfibB _ _ 1 aro_keep_asm).
exact (SM1.stack_malloc1_contract_pres_x TfibB ARX_asm0 fs_iface_ARX_asm0 TfibB_syms).
Qed.

End a.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check fs_iface_and_hp.
Print Assumptions fs_iface_and_hp.
Check asm0_pres_ARX.
Print Assumptions asm0_pres_ARX.
Check asm1_pres_ARX.
Print Assumptions asm1_pres_ARX.
Print Assumptions aro_keep_asm.
