(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/ErrnoGcf.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/ErrnoGcf.v, with its module paths changed; 14 of its 47 lines of code are new or changed and 123 lines of the source are left out. *)
(* copied from proofs/cgif/cgif_file_fuzzer/lib/AllocGtop.v @ 57e82b93d43 (a working branch: the fs install head of record, to be byte-checked against the ~20:30Z installed sha), module paths changed only. *)
(* The whole Allocate contract (AllocG.aalloc_realizes, every size n < nmax) from its two cases: the primary sizes
   (AllocG.aalloc_prim_realizes, n <= 64512) and the secondary sizes ([aalloc_sec_realizes], 64513 <= n).

   Image-free: the statement and the proof only read AllocG's definitions, so every image and instance (cgif_file,
   the shared preset / reply instance, fuzz_state) composes its two cases with this one lemma.  The secondary case
   of the walk on the cgif_file image is AGio.alloc_sec_w (any size bound NMAXW with NMAXW + 4 * 4096 <= 2 ^ 29);
   its cgif instance at MALLOC_MAX is AGio.alloc_sec. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
(* AllocG's section variables, in AllocG's order. *)
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable pcA : Z.
Variable oomb : Z.
Variable al : Z.
Variable atp : Z.
Variable cf : Z.

(* The secondary sizes: the twin of AllocG.aalloc_prim_realizes for 64513 <= n. *)
Definition aalloc_sec_realizes : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> 64513 <= n ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr).

Lemma aalloc_realizes_of_prim_sec :
aalloc_prim_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf ->
aalloc_sec_realizes ->
aalloc_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros HP HS inst so bp ly S W regs mem md n tr PRE.
destruct (Z_le_gt_dec n 64512) as [Hn|Hn].
- exact (HP inst so bp ly S W regs mem md n tr PRE Hn).
- exact (HS inst so bp ly S W regs mem md n tr PRE ltac:(lia)).
Qed.

End b.
End a.
