(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (image B): THE COMPOSITION. encode_proof proves
   lib/B/FSH_Fn_writer.v's encode_spec at image B from the parts of the walk, with the Section hypotheses every fs
   function proof takes: the shadow-cell pair (HSS : FsShadowSyms B), the image facts (IMG : fs_img_facts tfibsegs B)
   and the callee contract (HMALLOC : fuzz_malloc_spec tfibsegs B).

   What it proves: encode_proof : encode_spec B tfibsegs, by lib/B/FSW_preset_base64_encode_entry.v's encE_encode_spec
   (the entry 0x84700, the fuzz_malloc call 0x8474c, the refused arm, the len < 3 dispatch and the round-0 set-up), whose
   two continuations are discharged here:
   - encE_KLOOP (3 <= len, the loop head 0x84788 at round 0): lib/B/FSW_preset_base64_encode_loop.v's encR_loop (the
     induction on len - 3r) with its one hypothesis RS = lib/B/FSW_preset_base64_encode_round.v's encR_round_step; the
     loop's exit continuation KEXIT (0x849b8 after R rounds, 3R <= len <= 3R + 2) is
     lib/B/FSW_preset_base64_encode_tail.v's encR_loop_exit, passed as it is (its binders are KEXIT's, in KEXIT's
     order): the exit test `bgeu a3,s0` 0x849b8 to lib/B/FSW_preset_base64_encode_R.v's encR_nul (the NUL store
     0x84b24 .. the ret 0x84b54) when len = 3R, else to the tail encR_tail (0x849bc .. 0x84b24, then encR_nul);
   - encE_KTAIL (len in {1, 2}, the tail entry 0x849bc with R = 0): the tail file's encR_tail at R = 0 (the tail, then
     encR_nul).
   No branch is decided here: every UBSan decider (to the `unimp` 0x84b58) and every ASan report branch is refuted in
   the part that steps it (round: the 13 round deciders and the 11 round report rows; tail: the 11 tail deciders and the
   9 tail report rows; R's encR_nul: the NUL report row; entry: none lies in 0x84700 .. 0x84784 or 0x849a0 .. 0x849ac).

   rule 24: proves function preset_base64_encode (top; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1)
   Port-from: image A's composition is not written at 402eb5565fc (lib/A/FSW_preset_base64_encode.v has no
   encode_proof; HANDOFF2.md lists it as still moving); the names and shapes of the exit glue and the tail are A's
   (a working branch 0a3016aa4bf lib/A/FSW_preset_base64_encode.v: encR_loop_exit 3536-3612, the exit
   block, and encR_tail 2731-2749); the split into entry / loop / exit / tail / NUL is the old-B
   donor's, a working branch b96980d72d1 lib/B/Prog/preset_base64_encode_blocks.v:1249-1296 (enc_body_B: the
   len < 3 arm to enc_tail at k = 0, the loop enc_loop from k = 0, its exit test to enc_finish or enc_tail) and
   lib/B/Prog/preset_base64_encode.v:155-805 (preset_base64_encode_holds, from fuzz_malloc's contract); the Section
   application by binder name is lib/B/FSW_preset_base64_encode_round.v's encI (reused, not copied). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl
FSW_preset_base64_encode_W FSW_preset_base64_encode_R FSW_preset_base64_encode_loop
FSW_preset_base64_encode_round FSW_preset_base64_encode_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_preset_base64_encode_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the round and tail files load Ltac2, whose Require switches the default proof mode *)
Set Default Proof Mode "Classic".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* The part files close their sections, so each of their lemmas takes the section variables and hypotheses it uses.
   The round file's encI applies a lemma to those, by the names of its leading binders, from the proof context; each
   continuation below names its context as Section R of lib/B/FSW_preset_base64_encode_R.v does (ly0 St0 U0 W0 mem0
   md0 regs0 lyc Sc Wc memc mdc data len q live peak cnt fail kd bs, HLN .. HRA0: encE_Rhyps in that order). *)
Section E. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (lib/B/FSH_Base.v FsShadowSyms) and the image facts (lib/B/FSH_Rt.v fs_img_facts), as in
   lib/B/FSW_preset_base64_encode_W.v's Section W *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
(* fuzz_malloc's contract (lib/B/FSH_Fn_alloc.v fuzz_malloc_spec; B's FSW_fuzz_malloc.v fuzz_malloc_holds discharges
   it), as in lib/B/FSW_preset_base64_encode_entry.v's Section E *)
Hypothesis HMALLOC : fuzz_malloc_spec tfibsegs B.

Theorem encode_proof : encode_spec B tfibsegs.
Proof.
apply (encE_encode_spec B HSS IMG HMALLOC).
- (* 3 <= len: the loop from round 0, its exit, the tail when 3R < len, the NUL *)
  intros ly0 St0 U0 W0 regs0 mem0 md0 data len bs live peak cnt fail. unfold encE_KLOOP.
  intros lyc Sc Wc q kd ms mdc HR _ HL3 HINV HLR HPRE.
  unfold encE_Rhyps, encE_frame in HR.
  destruct HR as (HLN & HBS & HBSL & HDLO & HDHI & HARUc & HHEADS & HQB & HAB & HQ16 & HDB & HRBc & HGLOBc & HTABc &
    HRATc & HDATc & HKEEPc & HFRAMEc & HSP0 & HRA0).
  pose (memc := ms_mem ms).
  refine (ltac:(encI (@FSW_preset_base64_encode_loop.encR_loop))
    ltac:(encI (@FSW_preset_base64_encode_round.encR_round_step)) ms mdc 0 _ ltac:(lia) HL3 HINV HLR HPRE _).
  encI (@FSW_preset_base64_encode_tail.encR_loop_exit).
- (* len in {1, 2}: the tail from its entry with R = 0, the NUL *)
  intros ly0 St0 U0 W0 regs0 mem0 md0 data len bs live peak cnt fail. unfold encE_KTAIL.
  intros lyc Sc Wc q kd ms mdc HR H00 HLT HLE HINV HX HPC HPRE.
  unfold encE_Rhyps, encE_frame in HR.
  destruct HR as (HLN & HBS & HBSL & HDLO & HDHI & HARUc & HHEADS & HQB & HAB & HQ16 & HDB & HRBc & HGLOBc & HTABc &
    HRATc & HDATc & HKEEPc & HFRAMEc & HSP0 & HRA0).
  pose (memc := ms_mem ms).
  exact (ltac:(encI (@FSW_preset_base64_encode_tail.encR_tail)) ms mdc 0 HINV HX HPC HPRE H00 ltac:(lia)).
Qed.
End E.
