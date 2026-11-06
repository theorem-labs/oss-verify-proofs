(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLCallocA.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* reac-pw/fuzz_segconf image B: the Allocate contract at asan_calloc's call, in the form the calloc closing consumes
   (lib/A/Rt/RtLCallocR.v aseg_aalloc_calloc), from the closed primary-size Allocate of the AG family
   (lib/A/AGtopcgifC.v aalloc_prim_realizes_cgif_closed, relocated from omx-clap-core/fuzz_state at origin/ossv/recipes
   501c0d516c69; record in provenance/evidence/interceptors/calloc/ag/) at can_fill 0.

   Rule 24: Allocator::Allocate (0x331a4) is proved by the relocated AG family; this file only restates that theorem.
   aalloc_prim_realizes_cgif B 0 (lib/A/AllocGcgif.v) is, by conversion, aseg_aalloc_calloc tfibsegs B TFIB_INST
   TFIB_OOM 0x331a4: the same YGAlloc.aalloc_prim_realizes at the same segments, the trace predicate tr_admit, the
   model malloc, the instance relation (AllocGcgif.ARX_cgif B = YGCalloc.ARX_cgif tfibsegs B TFIB_INST, both
   `inst = TFIB_INST /\ AR tfibsegs B ..`), aowned B, rpre_cgif (aregime /\ qmeter in both), MALLOC_MAX, LIVE_MAX,
   qtight, Allocate 0x331a4, the out-of-memory byte TFIB_OOM, alignment 8 = ALLOC_ALIGN, AllocType 1 = AT_FROM_MALLOC,
   can_fill 0 = CF_CALLOC.  TFIB_INST = 0xa9158 is __asan::instance and TFIB_OOM = 0x12ea20 is
   __sanitizer::allocator_out_of_memory in fuzz_segconf.asan's .symtab (unstripped twin 4362701197e4); both are the
   frame's constants (lib/A/AF0m.v).  The AG family's premise on the depot callee is lib/A/AFl0.v tfib_depot_spec:
   [seg_aalloc_calloc_of_depot] keeps it as a premise, and [seg_aalloc_calloc_closed] discharges it by the frame's
   lib/A/AFem.v tfib_depot_ok from the record and its depot hash (the record's ts_hash fixes the hash of two traces
   only, so the hash premise stays).  Remaining premises of seg_aalloc_calloc_closed: SegBSyms B and the depot hash. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YM05 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YGAlloc YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YFem AllocGcgif AGtopcgifC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtLCallocR.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem seg_aalloc_calloc_of_depot : forall B, SegBSyms B -> tfib_depot_spec B ->
RtLCallocR.aseg_aalloc_calloc tfibsegs B TFIB_INST TFIB_OOM 0x331a4.
Proof.
intros B TS HD1.
pose proof (AGtopcgifC.aalloc_prim_realizes_cgif_closed B TS HD1 YGCalloc.CF_CALLOC (or_introl eq_refl)) as H.
unfold AllocGcgif.aalloc_prim_realizes_cgif in H. unfold RtLCallocR.aseg_aalloc_calloc.
exact H.
Qed.

Theorem seg_aalloc_calloc_closed : forall B, SegBSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
RtLCallocR.aseg_aalloc_calloc tfibsegs B TFIB_INST TFIB_OOM 0x331a4.
Proof.
intros B TS HDH.
exact (seg_aalloc_calloc_of_depot B TS (YFem.tfib_depot_ok B TS HDH)).
Qed.

End a.

Print Assumptions seg_aalloc_calloc_closed.
