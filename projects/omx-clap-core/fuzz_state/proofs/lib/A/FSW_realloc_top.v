(* fs program part, group ALLOC, a Theorem Labs lane: fuzz_realloc_spec (lib/A/FSH_Fn_alloc.v, A 0x829e8, alloc.c:75-94) from its
   walk's pieces: FSW_realloc.fsr_p0 (p = 0), FSW_realloc_pn.fsr_pn0_fail (p <> 0, failing()), FSW_realloc_pn.fsr_segAB
   (SEG-A + SEG-B: entry to the realloc call), SEG-C (the realloc call to the poison call), FSW_realloc_segD
   (the poison call to the post), composed by FSW_realloc_pn.fsr_of_segs. The two ASan poison helpers are
   a Theorem Labs lane's proved FSpoisonW.tfib_poison16 / tfib_unpoison16 (at PO_ENTRY / UP_ENTRY = PC_poison / PC_unpoison).
   port-from: none (composition only). No rename. Relocated files: none.

   NAMED SECTION HYPOTHESES (Print Assumptions shows them as the theorem's arguments):
   - IMG : fs_img_facts tfibsegs B, SHS : FsShadowSyms B, FS_ENV : api_env tfibsegs B, TB : TfibSyms B: facts of fs's
     TfibB; owner RELOC / the S0 start-up layer (the final instance).
   - FS_AREALLOC_AU : FSupoisonRealloc.FS_AREALLOC_AU tfibsegs B (as_universe B), the any-U __wrap_realloc contract at
     0x53078 in its C5 form; owner a Theorem Labs lane (plain arealloc_realizes_all) via a Theorem Labs lane (the U form).
   - FS_FUZZ_MALLOC : fuzz_malloc_spec (the p = 0 tail call); owner a Theorem Labs lane (fuzz_malloc_holds discharges it).
   SEG-C is a Theorem Labs lane's FSW_realloc_segC.fsr_segC (a working branch 05a38a5494b), SEG-D its
   FSW_realloc_segD.fsr_segD (a working branch bb6609fc77b). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YM05 YG00 YG0a YG01 YG0d YG0f YG0n YG0q YCbq YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0m FSupoison FSupoisonU FSH_Gen FSH_Base FSH_Rt FSH_Fn_alloc FSupoisonRealloc FSpoisonS FSpoisonR FSpoisonW
FSW_K FSW_realloc FSW_realloc_pn FSW_realloc_segC FSW_realloc_segD.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SHS : FsShadowSyms B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis FS_AREALLOC_AU_H : FS_AREALLOC_AU tfibsegs B (as_universe B).
Hypothesis FS_FUZZ_MALLOC : @fuzz_malloc_spec fx rc SK tfibsegs B.

Theorem fuzz_realloc_of_segC : fsr_segC_stmt B -> @fuzz_realloc_spec fx rc SK tfibsegs B.
Proof.
intros SEGC.
exact (fsr_of_segs B IMG SHS FS_ENV SEGC (fsr_segD B) FS_AREALLOC_AU_H (tfib_poison16 B LAWS TB)
  (tfib_unpoison16 B LAWS TB) FS_FUZZ_MALLOC).
Qed.

Theorem fuzz_realloc_holds : @fuzz_realloc_spec fx rc SK tfibsegs B.
Proof. exact (fuzz_realloc_of_segC (fsr_segC B)). Qed.
End t.
