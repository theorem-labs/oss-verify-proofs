(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: the trace premise in the P'' form, `admits (as_universe B) tr S` (YG01.v), replacing the In-form. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: batch_room_cf added to rpreD_free_cf and to its realloc old-block free twin (YGcfReallocCompose.v RDF2); nmax_cf_ok's comment updated (c5's walk covers n < SEC_NMAX since 84ee52cd012). *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocCompose.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocCompose.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocCompose.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfMallocCompose.v, with its module paths and module names changed; 103 of its 151 lines of code are new or changed and 342 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WalkB2; integrator ReallocPrimary).
   rule 24: no function proved here (a restatement: the walk of ___interceptor_malloc's body is the relocated
   lib/A/WrapMallocABodyM1.v (call field) and lib/A/WrapMallocABodyRet.v (return field), composed as
   omx-clap-core/fuzz_preset's lib/A/WrapMallocABodyTop.v (commit 9e87119fcf60, sha256 10c632c6a817; internal record) composes them).
   The malloc interceptor BODY contract at plugin-hostd/fuzz_reply image A (asan), at the call-site relation of every
   reply instance, YGcfInstBase.ARXq_cf B (fun i => i = as_inst B), in place of preset's ARXh_A (ARXs_cf's body,
   WrapMallocADefs.v:36-39): aalloc_realizes_cf_em names its ARX in both its pre and its post, so Allocate's
   contract at ARXq_cf does not convert to one at ARXh_A. The free wrapper's precedent is lib/A/WrapFreeARXq.v.
   - amalloc_body_L_cf: WrapMallocABodyDefs.amalloc_body_realizes_L (A1's local copy of the layer text) IS the layer's
     amalloc_body_realizes_cf (Reusable/YG0dcf.v): the same conjuncts in the same order, and equal window constants
     (MALLOC_IN_STK_L = MALLOC_IN_STK_CF = 14208, MALLOC_BODY_FRAME_L = MALLOC_BODY_FRAME_CF = 2144), by conversion.
   - Section Q, over any B: preset's WrapMallocABodyTop.amalloc_body_A's proof with ARX := ARXq_cf. What the proof reads from
     ARX is ARcf (q_HXA, the return field's HXA, and the post's first conjunct) and xs_placed_cf (q_xs, from ARcf). The
     return field is generic in ARX (WrapMallocABodyRet.wm_ret_B, Section b) and takes q_HXA / q_HXF. The call field
     (WrapMallocABodyM1.wm_call_B) states Allocate's pre at ARXh_A; apre_q_of_h weakens it to ARXq_cf (the instance
     object from `inst = as_inst B`, ARcf, xs_mapped_cf from ARcf by YGcfXs.ARcf_xsm, qtight from qmeter_cf's first
     conjunct). No conjunct that only ARXh_A has is read at Allocate's post.
   - amalloc_body_reply_A: Section Q at B := TfibB, at image A's CfImg (CfImg_A) and reply's CfParams (CfParams_reply),
     at every FP state and RunCeil, as lib/A/ReplyAllocTargets.v states reply's allocator targets. Its three Section
     hypotheses are discharged: TfibSyms TfibB (AD2l.TfibB_syms), tfib_unwind_spec (AFl4.tfib_unwind_ok) and
     cf_pc_allocate = PC_ALLOCATE (both Allocator::Allocate's entry, 0x31bd8: CfImg_A's field and AB1wMalloc's
     constant). ONE premise is left: Allocate's contract at ARXq_cf (YGcfMallocCompose.aalloc_realizes_cf_em, nmax
     cf_malloc_max, al 8, atp 1, acf 1), which reply's malloc instance concludes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG RGtop YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YAkMemnorm YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0l AF0m AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import WrapMallocADefs WrapMallocABodyDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require WrapMallocAConsts WrapMallocABodyM1 WrapMallocABodyRet.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AD2l AFl4 CfImgA CfParamsReply ReplyRelroGeoA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma amalloc_body_L_cf : forall segs B pc_ra0,
  amalloc_body_realizes_L segs B pc_ra0 -> amalloc_body_realizes_cf segs B pc_ra0.
Proof. intros segs B pc_ra0 H. exact H. Qed.

Section Q.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis Hpc : cf_pc_allocate = WrapMallocAConsts.PC_ALLOCATE.
(* part 3c: Allocate's contract takes arodata_ok_cf at its entry memory; the unit's two image rows carry it from the
   body's entry over the body's raw frame (as YGcfMallocCompose.amalloc_realizes_cf_of_parts) *)
Hypothesis RS : relro_seg_t tfibsegs.
Hypothesis ER0 : errno_relro_t B.

(* the call-site relation of every reply instance, at the instance object as_inst B; at AImg_reply, im_segs is
   tfibsegs by delta, so it is an ARXh_t tfibsegs *)
Local Notation ARXq := (YGcfInstBase.ARXq_cf B (fun i => i = as_inst B)).

(* HXA: the relation gives ARcf *)
Lemma q_HXA : ARX_ARcf tfibsegs B ARXq.
Proof. intros Hp inst ly S W mem md H. exact (YGcfInstBase.ARXq_cf_ARcf B _ Hp inst ly S W mem md H). Qed.

(* HXF, the return field's form: the relation survives a memory at which ARcf holds (with the materialization). The
   instance object and qtight read no memory; ARcf is given; xs_mapped_cf follows from it. *)
Lemma q_HXF : forall Hp inst ly S W mem md mem' mat,
  ARXq Hp inst ly S W mem md ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARXq Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros Hp inst ly S W mem md mem' mat H A'.
apply YGcfInstBase.ARXq_cf_intro; [|exact (YGcfInstBase.ARXq_cf_qtight B _ Hp inst ly S W mem md H)].
unfold YGcfInstBase.ARX_cf.
split; [exact (YGcfInstBase.ARXq_cf_iok B _ Hp inst ly S W mem md H)|].
split; [exact A' | exact (ARcf_xsm tfibsegs B ly S Hp W mem' _ A')].
Qed.

(* the relation gives the errbuf slot's placement *)
Lemma q_xs : ARX_xs tfibsegs ARXq.
Proof. intros Hp inst ly S W mem md H. exact (YGcfInstBase.ARXq_cf_xs B _ Hp inst ly S W mem md H). Qed.

(* preset's ARXh_A (the call field's relation) gives the call-site relation *)
Lemma q_of_h : forall Hp inst ly S W mem md, ARXh_A B Hp inst ly S W mem md -> ARXq Hp inst ly S W mem md.
Proof.
intros Hp inst ly S W mem md (I & A & QM & _).
apply YGcfInstBase.ARXq_cf_intro; [|exact (proj1 QM)].
unfold YGcfInstBase.ARX_cf.
split; [exact I|]. split; [exact A | exact (ARcf_xsm tfibsegs B ly S Hp W mem md A)].
Qed.

(* ... so Allocate's pre at ARXh_A is its pre at ARXq_cf (AllocG.alloc_pre names ARX in its first conjunct only) *)
Lemma apre_q_of_h : forall nmax al atp acf Hp inst so bp ly S W regs mem md n tr,
  malloc_apre_cf tfibsegs B nmax al atp acf (ARXh_A B) Hp inst so bp ly S W regs mem md n tr ->
  malloc_apre_cf tfibsegs B nmax al atp acf ARXq Hp inst so bp ly S W regs mem md n tr.
Proof.
intros nmax al atp acf Hp inst so bp ly S W regs mem md n tr [X R].
exact (conj (q_of_h Hp inst ly S W mem md X) R).
Qed.

(* preset's WrapMallocABodyTop.amalloc_body_A at ARX := ARXq_cf: the same proof, with the call field's pre weakened by
   apre_q_of_h and the return field taken at ARXq_cf (q_HXA / q_HXF) *)
Theorem amalloc_body_q_L :
  aalloc_realizes_cf_em tfibsegs B cf_malloc_max 8 1 1 ARXq ->
  amalloc_body_realizes_L tfibsegs B (pc_malloc_ra0 (as_code B)).
Proof.
intros HAL.
pose proof q_HXA as HAR.
pose proof q_xs as HXS.
intros ly S Hp W regs mem md n ch PREL Hn Hrange Hlive Htr.
assert (PRE : bpre_w tfibsegs B 14208 2144 ly S Hp W regs mem md ch) by exact PREL.
assert (ENT : bentry_w tfibsegs B 14208 2144 ly S Hp W regs mem md n ch) by exact (conj PRE (conj Hn (conj Hrange (conj Hlive Htr)))).
assert (RP : YGcfRmodel.rpre_cfr B S n).
{ pose proof PRE as (ARp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL & ER & _ & BR & HO & _).
  destruct ARp as (M & _).
  split; [exact (amc_universe _ _ _ _ _ M)|]. split; [exact (amc_wf _ _ _ _ _ M)|].
  (* round-3 re-fit: rpre_cfr's last conjunct, the hull admission, is the pre's cf_hull_ok conjunct *)
  exact (conj (conj SL (conj ER BR)) HO). }
eapply amreal_SRr_pre; [exact (WrapMallocABodyM1.wm_call_B B TB U1 Hpc ly S Hp W regs mem md n ch ENT RP Hrange)|].
intros W1 c1 WLE1 (inst & so & bp & regsA & memA & mdA & -> & APREh & IO1 & RIN & KP1 & ER1 & KK).
pose proof (apre_q_of_h cf_malloc_max 8 1 1 Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) APREh) as APRE.
assert (ROA : arodata_ok_cf tfibsegs B memA).
{ pose proof PRE as (ARp & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
  apply (arodata_keep_cf tfibsegs B ly S Hp W mem md ly S Hp W1 memA mdA
    (fun a => aowned B ly S a \/ ascratch B 14208 regs a) ARp (HAR Hp inst ly S W1 memA mdA (proj1 APRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly 14208 regs a (amc_layout _ _ _ _ _ (proj1 ARp)) HSTK ER0 Ha R X).
  - intros x NX. apply (proj1 (proj2 KP1)); intros Y; apply NX; tauto.
  - exact HRO. }
eapply RGtop.rg_then_SRr; [exact (HAL Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) APRE ROA)|].
intros [q S2] W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & PATH & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA MNA].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
eapply SRr_mono; [exact (WrapMallocABodyRet.wm_ret_B B TB cf_malloc_max 8 1 1 ARXq q_HXA q_HXF ly S Hp W regs mem md n ch W1
  inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2 ENT KK APRE APO A02 LP2 PATH OOM)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & A0' & ARX' & IO' & [KV KR] & WN' & MN' & ER' & NUL').
unfold malloc_leaf_cf_w_L. exists ly2, regs', mem', md'. cbn [fst snd].
assert (XO : forall a, ~ aowned B ly S a -> ~ aowned B ly2 S2 a ->
  ~ ((q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly2 S2)) ->
  ~ AOXm_cf B ly S a /\ ~ AOXm_cf B ly2 S2 a /\ ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
{ intros a NA NA2 NE. split; [|split].
  - intros [X|X]; [exact (NA X)|]. apply NE. right. apply Exists_app. left. exact X.
  - intros [X|X]; [exact (NA2 X)|]. apply NE. right. apply Exists_app. right. exact X.
  - intros X. apply NE. left. exact X. }
assert (XS : forall a, ~ ascratch B MALLOC_IN_STK_L regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a).
{ intros a NS X. apply NS. destruct RIN as [R1 R2]. unfold MALLOC_IN_STK_L.
  destruct X as [X|X]; [left; lia | right; exact X]. }
split; [reflexivity|].
split.
{ unfold acall_post_cf.
  split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE2|].
  split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
  split; [exact CS'|].
  split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split; [|exact WN'].
  intros a Ha NA NA2 NS NE. destruct (XO a NA NA2 NE) as (X1 & X2 & X3).
  rewrite (KV a Ha NS), (FR2 a Ha X1 X2 (XS a NS) X3). exact (proj1 KP1 a Ha NA NS). }
split; [exact A0'|]. split; [exact LP2|]. split; [exact NUL'|].
split; [exact (HXS _ _ _ _ _ _ _ ARX2)|].
split.
{ intros Hq i Hi. rewrite (ER' Hq i Hi), (ERA Hq i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. destruct (XO _ NA NA2 NE) as (X1 & X2 & X3).
rewrite (KR x NS), (FR2w x X1 X2 (XS _ NS) X3). exact (proj1 (proj2 KP1) x NA NS).
Qed.

(* ... in the layer's text *)
Corollary amalloc_body_q :
  aalloc_realizes_cf_em tfibsegs B cf_malloc_max 8 1 1 ARXq ->
  amalloc_body_realizes_cf tfibsegs B (pc_malloc_ra0 (as_code B)).
Proof. intros HAL. exact (amalloc_body_L_cf _ _ _ (amalloc_body_q_L HAL)). Qed.

End Q.
End G.

(* image A's CfImg and reply's CfParams, as lib/A/ReplyAllocTargets.v takes them: the statements below are about
   image A by design *)
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsReply.CfParams_reply.

Lemma pc_allocate_reply_A : cf_pc_allocate = WrapMallocAConsts.PC_ALLOCATE.
Proof. reflexivity. Qed.

Theorem amalloc_body_reply_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  aalloc_realizes_cf_em (fx := fx) tfibsegs AD2l.TfibB cf_malloc_max 8 1 1
    (YGcfInstBase.ARXq_cf (rc := rc) AD2l.TfibB (fun i => i = as_inst AD2l.TfibB)) ->
  amalloc_body_realizes_cf (fx := fx) (rc := rc) tfibsegs AD2l.TfibB (pc_malloc_ra0 (as_code AD2l.TfibB)).
Proof.
intros fx rc HAL.
exact (amalloc_body_q AD2l.TfibB AD2l.TfibB_syms AFl4.tfib_unwind_ok pc_allocate_reply_A
  ReplyRelroGeoA.relro_seg_reply_A (ReplyRelroGeoA.errno_relro_reply_A AD2l.TfibB AD2l.TfibB_syms) HAL).
Qed.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check amalloc_body_L_cf. Print Assumptions amalloc_body_L_cf.
Check amalloc_body_q. Print Assumptions amalloc_body_q.
Check amalloc_body_reply_A. Print Assumptions amalloc_body_reply_A.
