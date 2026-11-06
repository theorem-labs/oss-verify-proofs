(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the caller-side journal steps of cgif_rgb_fuzzer's size-dependent fake-stack
   calls, for libreac/fuzz_scene, restated over cgif_file_fuzzer's journal. STATEMENTS ONLY (rule 24): each step is a
   Prop `<name>_stmt`; the lemma `<name> : <name>_stmt segs B` is proved in this Section under its hypotheses, as
   cgif_rgb_fuzzer proves it. *)

(*   Source text (c8557374ad2e, proofs/cgif/cgif_rgb_fuzzer/lib/):
     - YC05.v:143-160 aj_stack_malloc_sz_at   -> aj_stack_malloc_sz_at_stmt
     - YC05.v:206-221 aj_set_shadow_at        -> aj_set_shadow_at_stmt
     - YC05.v:21-29   the Section context     -> Section h below (rgb's hypotheses, same names and order)
   The one change to the statement text: rgb's journal counts events in `vev` (YC05.v:157 `vev S2 = vev Sc`);
   cgif_file_fuzzer's journal counts them in `st_nev` (lib/YCbq.v:355 `st_nev S' <= st_nev S + k`), so the malloc
   step's post says `st_nev S2 = st_nev Sc`. The set-shadow step keeps rgb's text unchanged: its journal count `k` is
   unchanged and it names no event counter. `ajournal`, `acall_kept`, `ecall_pre`, `frame_flag_lawP`,
   `stack_malloc_progressP` and `api_env` are cgif_file_fuzzer's (lib/YCbq.v:348-370, :822, YG0d.v:277-283,
   YCbq.v:797, :803, :806), which a Theorem Labs lane relocates to this unit's lib/Reusable.

   THE THIRD STEP IS NOT HERE.  rgb YC05.v:260-276 aj_stack_free_at is, for this tree, lib/AU/StackFreeJournal.v,
   the asan-ubsan twin (Requires lib.AU.YCbq) of lib/Reusable/StackFreeJournal.v, which a Theorem Labs lane proved
   (a working branch c3bfa00452c) and a Theorem Labs lane landed in this tree, over lib/Reusable/StackFreeDef.v
   astack_free_realizes.  I diffed that lemma against the text this file used to carry
   (rgb YC05.v:260-276 over `st_nev`): the premises, the journal, the post's four clauses and the own-list head
   `(cid, pos) :: own'` are the same, and the two differences do not touch this walk:
     - the released shadow span is `sf_span cid n` (StackFreeDef.v:16) in place of `n / 8`.  `sf_span cid n` is
       `fs_frame_bytes cid / 8` for cid <= 6 and `n / 8` above, so for scene's class 8 the two spans are equal.
     - the lemma takes no `frame_flag_law` hypothesis: it derives the flag byte's facts from `AR_laws`
       (al_flag, al_client_img).  The hypothesis below is therefore unused by the free step and is kept only
       because the malloc step's rgb context declares it.
   The three runtime contracts are lib/Reusable/AsStackSz.v (astack_malloc_sz_realizes), lib/Reusable/SetShadowDef.v
   (aset_shadow_realizes) and lib/Reusable/StackFreeDef.v (astack_free_realizes).  This file names no image value: the
   runtime entry pc and the frame class are arguments.

   This is the asan-ubsan tree's copy: the text of lib/A/J_StackSz.v, except that YCbq (a module that differs between
   the two images) and the free step's StackFreeJournal are Required from lib.AU (gate 6o, a Theorem Labs lane).  Every other
   module, and the three shared contract types, come from lib.Reusable.  The statement names and text are the same. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
(* A Theorem Labs lane: the size-dependent stack-malloc contract astack_malloc_sz_realizes (AsStackSz.v:30), which this file's malloc step consumes. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz.
(* A Theorem Labs lane (at 798447a1772, proofs/libreac/fuzz_grant/lib/A/Rt/SetShadowDef.v:19) at scene's
   relocated path: aset_shadow_realizes, which the set-shadow step below consumes. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import SetShadowDef.
(* Proved by one Theorem Labs lane and landed through another: astack_free_realizes and its journal step aj_stack_free_at. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import StackFreeJournal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable segs : list Segment.
Variable B : asyms.
(* rgb YC05.v:25-29, the framework laws the two proofs use; cgif_file_fuzzer's YC85.v:231-237 takes the same. *)
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
(* rgb YC05.v:259.  StackFreeJournal.v's aj_stack_free_at does not take it (see the header). *)
Hypothesis frame_flag_law : frame_flag_lawP segs B.
Local Notation ajournal := (ajournal segs B).
Local Notation acall_kept := (acall_kept segs B).
(* rgb YC05.v:143-160, `vev` -> `st_nev`. *)
Definition aj_stack_malloc_sz_at_stmt : Prop :=
forall pc cid, astack_malloc_sz_realizes segs B pc cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw n,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) n /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
(* rgb YC05.v:206-221, unchanged. *)
Definition aj_set_shadow_at_stmt : Prop :=
forall pc v, SetShadowDef.aset_shadow_realizes segs B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
End h.
End j.
