(* reac-pw/fuzz_segconf, ASan images: the two intermediate forms the calloc closing (lib/A/Rt/RtLCalloc.v) composes
   to reach interface row 13 (lib/A/Rt/RtSegCalloc.v aseg_calloc04_rule). Statement text only: no function of the
   binary is proved here.

   [aseg_acalloc_realizes] is lib/Reusable/YGCalloc.v acalloc_realizesP at this unit's own predicates (the
   instantiation YGCalloc.v acalloc_realizes_cgif writes: acall_pre, amreal, malloc, malloc_leaf), with one change:
   its trace premise is this kernel's `In (call_trace ..) (as_universe B) \/ st_nev S < EV_MAX`, the form of
   lib/Reusable/YG0d.v amalloc_realizes, in place of `In (call_trace ..) U` (this kernel's malloc and free rules
   take no trace membership; YGCalloc's form is fuzz_decode's kernel's).

   [aseg_aalloc_calloc] is the Allocate contract (lib/Reusable/YGAlloc.v aalloc_prim_realizes) at calloc's call
   site: the trace predicate is this kernel's tr_admit (lib/Reusable/YG01.v), as omx-clap-core/fuzz_state's
   lib/A/AllocGcgif.v aalloc_prim_realizes_cgif states it, with YGCalloc.v's instance relation ARX_cgif, the
   alignment 8, AllocType FROM_MALLOC and can_fill 0 (YGCalloc.v ALLOC_ALIGN, AT_FROM_MALLOC, CF_CALLOC).

   [aseg_acalloc_of_allocate] is YGCalloc.v acalloc_of_allocateP in these two forms: the claim the calloc thin
   walk (the interceptor and asan_calloc over an abstract Allocate) proves. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YM05 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YGAlloc YGCalloc.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Definition aseg_acalloc_realizes (pc pc0 cmax cdepth : Z) : Prop :=
forall ly S W regs mem md nm sz ch,
acall_pre segs B ly S W regs mem md ch ->
ly_bot ly + cdepth < spZ regs ->
getr regs 10 = w64 nm -> getr regs 11 = w64 sz ->
0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX -> nm * sz <= cmax -> blocks_bytes S + nm * sz <= LIVE_MAX ->
In (call_trace ly pc0 regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
amreal segs (malloc (nm * sz) (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(YGCalloc.calloc_leaf_with segs (malloc_leaf segs B) ly S W regs mem md (nm * sz)).

Definition aseg_aalloc_calloc (inst oomb alloc_pc : Z) : Prop :=
YGAlloc.aalloc_prim_realizes segs B (fun tr S => tr_admit (as_universe B) S tr) malloc
(YGCalloc.ARX_cgif segs B inst) (aowned B) YGCalloc.rpre_cgif MALLOC_MAX LIVE_MAX qtight alloc_pc oomb
YGCalloc.ALLOC_ALIGN YGCalloc.AT_FROM_MALLOC YGCalloc.CF_CALLOC.

Definition aseg_acalloc_of_allocate (inst oomb pc pc0 alloc_pc cmax cdepth : Z) : Prop :=
cmax <= YGCalloc.PRIM_MAX -> aseg_aalloc_calloc inst oomb alloc_pc -> aseg_acalloc_realizes pc pc0 cmax cdepth.
End d.
