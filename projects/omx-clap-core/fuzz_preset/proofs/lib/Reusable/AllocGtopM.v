(* copy of proofs/cgif/cgif_file_fuzzer/lib/AllocGtopM.v@5c60b06ed1c4 (blob 88ebe8781a78); do not edit. Only this line is added, the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable, and the comment adds the parentheses after AGioM.alloc_sec_w_em (line 7), as this unit's AGioM is lib/A/AGioM.v, not cgif's. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (task MEMNORM, full Allocate): the memnorm-kept twin of AllocGtopE: MemnormT.aalloc_realizes_em
   (every size n < nmax) from its two cases, the primary (MemnormT.aalloc_prim_realizes_em, n <= 64512) and the
   secondary ([aalloc_sec_realizes_em], 64513 <= n).  Image-free, like AllocGtopE: the case split is on n alone.  The
   secondary case on the cgif_file image is AGioM.alloc_sec_w_em (cgif's; this unit proves [aalloc_sec_realizes_em] by AGioMB.alloc_sec_w_em_realizes, lib/AU/AGioMB.v:225, and AGioM.alloc_sec_w_em_realizes, lib/A/AGioM.v:229).
   rule 24: no function proved (kind: top-level composition).  AllocGtopE is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
(* AllocG's section variables, in AllocG's order (copy of AllocGtopE.v:22-37). *)
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
(* field round 3 part 3b: MemnormT's Allocate memory precondition; the secondary contract does not need it *)
Variable MP : (word -> option byte) -> Prop.

Definition aalloc_sec_realizes_em : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> 64513 <= n ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(MemnormT.alloc_leaf_em segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr).

(* copy of AllocGtopE.v:45-54, at the memnorm-kept forms; part 3b: the prim case reads MP, the sec case drops it *)
Lemma aalloc_realizes_em_of_prim_sec_em :
MemnormT.aalloc_prim_realizes_em segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf MP ->
aalloc_sec_realizes_em ->
MemnormT.aalloc_realizes_em segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf MP.
Proof.
intros HP HS inst so bp ly S W regs mem md n tr PRE HMP.
destruct (Z_le_gt_dec n 64512) as [Hn|Hn].
- exact (HP inst so bp ly S W regs mem md n tr PRE HMP Hn).
- exact (HS inst so bp ly S W regs mem md n tr PRE ltac:(lia)).
Qed.
End b.
End a.
