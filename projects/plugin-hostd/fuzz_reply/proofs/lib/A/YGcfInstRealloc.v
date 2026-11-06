(* CARRIED from commit 886368392e934bec75bf4485ad77505063da7c16,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstRealloc.v, sha256 6de2709b644711ddea8b3ffc8c6f03561ac1f3ae42ca70011f2c994077dd391a (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree name lib/A; a sentence is split at a directory change, the module order kept.
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken back by path from commit 2d97a7029501,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfInstRealloc.v (the P'' text), with this unit's module prefixes and
   no other change.  The preset text itself was taken from this layer's commit bbe791f0bb0 with THREE changes:
   - room_br and the realloc(p, n) end rule arealloc_realizes_cf_inst that used it are DROPPED: room_br
     (YGcfReallocCompose.ARX_br at ARXq_cf) is not satisfiable as a closed statement (the source's own header). The
     realloc(p, n) end rule is YGcfInstReallocK.arealloc_realizes_cf_k_inst, with the caller's room at the entry.
   - acall_prefix is no longer a named premise: on this base acall_pre_cf carries ly_bot ly + ACALL_PREFIX < spZ regs
     (YG0dcf.v:52, ACALL_PREFIX := 4096, YG0d.v:21), so acall_prefix_cf is its projection (acall_prefix_cf_ok).
   - the named premises adealloc_realizes_raw_cf_em_m_cf and errno_word are not used by the null end rule, so they are
     not stated here; YGcfInstReallocK.v states them for realloc(p, n).

   The parts of YGcfReallocCompose.v at the layer's CALL-SITE relation ARXq_cf B IOK (YGcfInstBase.v: the walk's
   relation ARX_cf with the quarantine tight, the relation the Allocate interfaces are stated at) over ImgBase's
   segment list im_segs, with every premise that is a fact of the relation or of the call form proved here.

   PROVED here:
   - ARX_qm_cfq: ARXq_cf gives qmeter_cf (YGcfInstBase.ARXq_cf_qm), the bridge's ARX_qm;
   - acall_xs_cf_ok: the errbuf placement at the interceptor's entry, from acall_pre_cf's first conjunct ARcf
     (YG0ncf.xs_placed_of_ARcf);
   - acall_prefix_cf_ok: the stack room at the interceptor's entry, acall_pre_cf's ACALL_PREFIX conjunct;
   - the size bound nmax := cf_malloc_max (YGcfMallocComposeE.nmax_cf_ok_of_w), ARX_ARcf / ARX_xs (ARXq_cf_ARcf /
     ARXq_cf_xs).
   NAMED (Section hypothesis, with the exact name its owner proves it under; segs := im_segs):
   - aalloc_realizes_cf_em_m_cf: YGcfInstAllocTop.aalloc_realizes_cf_em_m_cf (lib/A), YGcfMallocComposeE's
     aalloc_realizes_cf_em_m at ARXq_cf B IOK, nmax := cf_malloc_max, al := al_cf, atp := atp_cf.
   The realloc(NULL, n) walk record (YGcfReallocCompose.wrap_realloc_null_walk_cf at ARXq_cf) is the unit's walk of the
   realloc interceptor; it decodes the unit's bytes, so it is a premise of the theorem. Allocate's call-site argument
   can_fill (acf) is a Section variable: each unit's walk passes its own.
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0f YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfReallocCompose.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.

(* The stack room at the interceptor's entry: acall_pre_cf's fifth conjunct (YG0dcf.v:52), at any segment list. *)
Lemma acall_prefix_cf_ok : forall (segs : list Segment) (B : asyms), YGcfReallocCompose.acall_prefix_cf segs B.
Proof.
intros segs B ly S Hp W regs mem md ch PRE.
destruct PRE as (_ & _ & _ & _ & HB & _). exact HB.
Qed.

Section J.
Variable B : asyms.
(* the unit's instance-object predicate (YGcfInstBase's IOK) *)
Variable IOK : Z -> Prop.
(* Allocate's can_fill argument at realloc's Allocate call (the unit's walk passes it). *)
Variable acf : Z.

Local Abbreviation segs := im_segs.
Local Abbreviation ARX := (ARXq_cf B IOK).

(* ---------------------------------------------------------------------------- *)
(* 1. The facts of the call-site relation and of the call form the bridges take. *)

(* qmeter_cf at a state of the relation where the unit's hull admission holds (YGcfInstBase.ARXq_cf_qm). *)
Lemma ARX_qm_cfq : forall Hp inst ly S W mem md, ARX Hp inst ly S W mem md -> cf_hull_ok S -> qmeter_cf S.
Proof. exact (ARXq_cf_qm B IOK). Qed.

(* acall_pre_cf's first conjunct is ARcf, whose last field is the errbuf placement. *)
Lemma acall_xs_cf_ok : YGcfReallocCompose.acall_xs_cf segs B.
Proof.
intros ly S Hp W regs mem md ch PRE.
exact (YG0ncf.xs_placed_of_ARcf segs B ly S Hp W mem md (proj1 PRE)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The named premise (see the header).                                        *)
Hypothesis aalloc_realizes_cf_em_m_cf : aalloc_realizes_cf_em_m segs B cf_malloc_max al_cf atp_cf acf ARX.
(* field round 3 part 3b: the unit's two image rows (YG0ncf.v) the bridge reads at Allocate's entry *)
Hypothesis relro_seg : relro_seg_t segs.
Hypothesis errno_relro : errno_relro_t B.

(* ---------------------------------------------------------------------------- *)
(* 3. realloc(NULL, n): YGcfRealloc.arealloc_null_realizes_cf at every ghost set, at the interceptor's entry.      *)
Theorem arealloc_null_realizes_cf_inst : forall (Kn : YGcfReallocCompose.Knr_t segs),
YGcfReallocCompose.wrap_realloc_null_walk_cf segs B cf_malloc_max al_cf atp_cf acf ARX Kn ->
forall Hp, YGcfRealloc.arealloc_null_realizes_cf segs B Hp cf_pc_wrap_realloc.
Proof.
intros Kn HW.
exact (YGcfReallocCompose.arealloc_null_realizes_cf_of_parts segs B cf_malloc_max al_cf atp_cf acf ARX Kn
  (acall_prefix_cf_ok segs B) acall_xs_cf_ok nmax_cf_ok_of_w (ARXq_cf_ARcf B IOK) (ARXq_cf_xs B IOK)
  relro_seg errno_relro aalloc_realizes_cf_em_m_cf HW).
Qed.
End J.
End G.

Print Assumptions arealloc_null_realizes_cf_inst.
