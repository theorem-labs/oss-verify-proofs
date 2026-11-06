(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/ErrnoG.v, with its module names changed; 16 of its 48 lines of code are new or changed and 378 lines of the source are left out. *)
(* copy of cgif/cgif_file_fuzzer lib/AllocGtopE.v (file sha256 4427ec51925d; donor not released); do not edit. Only this line is added, the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable, the module ErrnoG is this unit's ErrnoGcf (lib/Reusable/ErrnoGcf.v, whose Section a, :39-211, the AllocG / DeallocG part of cgif's ErrnoG.v, is byte for byte lib/Reusable/ErrnoG.v:59-231, cgif's ErrnoG.v at e8a7dd66acf2, file sha256 27b3f11ecf13, :58-230, as history; this file does not Require lib/Reusable/ErrnoG.v, the whole copy of cgif's ErrnoG.v) in the code lines, not in the comment, and the comment adds the parentheses after AllocGtop (line 2) and after AGioE.alloc_sec_w_e (line 5), as this unit has no AllocGtop.v and no AGioE. *)
(* The errno-kept twin of AllocGtop (cgif's; on this tree projects/omx-clap-core/fuzz_state/proofs/lib/Reusable/AllocGtop.v:49, aalloc_realizes_of_prim_sec): ErrnoG.aalloc_realizes_e (every size n < nmax) from its two cases, the
   primary (ErrnoG.aalloc_prim_realizes_e, n <= 64512) and the secondary ([aalloc_sec_realizes_e], 64513 <= n).
   Image-free, like AllocGtop: the case split is on n alone.  The secondary case on the cgif_file image is
   AGioE.alloc_sec_w_e (cgif's; this unit proves the secondary case only in the memnorm-kept form AllocGtopM.aalloc_sec_realizes_em, by AGioMB.alloc_sec_w_em_realizes, lib/AU/AGioMB.v:225, and AGioM.alloc_sec_w_em_realizes, lib/A/AGioM.v:229). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoGcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
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

Definition aalloc_sec_realizes_e : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> 64513 <= n ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(ErrnoGcf.alloc_leaf_e segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr).

Lemma aalloc_realizes_e_of_prim_sec_e :
ErrnoGcf.aalloc_prim_realizes_e segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf ->
aalloc_sec_realizes_e ->
ErrnoGcf.aalloc_realizes_e segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros HP HS inst so bp ly S W regs mem md n tr PRE.
destruct (Z_le_gt_dec n 64512) as [Hn|Hn].
- exact (HP inst so bp ly S W regs mem md n tr PRE Hn).
- exact (HS inst so bp ly S W regs mem md n tr PRE ltac:(lia)).
Qed.
End b.
End a.
