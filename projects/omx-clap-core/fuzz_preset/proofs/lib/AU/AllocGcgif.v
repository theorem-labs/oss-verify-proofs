(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AllocGcgif.v (cold/c-asan-realloc-c5 ced28ed2383, file sha256 5f1bf80d9059) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* The cgif_file instance of the generic Allocate statement (AllocG.v): its image (tfibsegs, Allocate at 0x326a4,
   the OOM byte TFIB_OOM), model (malloc) and predicates.  AllocG.v itself is image-free; consumers relocate it, and
   instantiate it with their own image and predicates in place of this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Export AllocG.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The default instantiation: cgif_file's image, model and predicates. *)
Definition ARX_cgif (B : asyms) (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs)
(mem : word -> option byte) (md : Model) : Prop :=
inst = TFIB_INST /\ AR tfibsegs B ly S W mem md.
Definition rpre_cgif (S : astate) (n : Z) : Prop := aregime S /\ qmeter S.
Definition aalloc_prim_realizes_cgif (B : asyms) (cf : Z) : Prop :=
aalloc_prim_realizes tfibsegs B (fun tr _ => In tr (as_universe B)) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX qtight
0x326a4 TFIB_OOM 8 1 cf.
Definition aalloc_realizes_cgif (B : asyms) (cf : Z) : Prop :=
aalloc_realizes tfibsegs B (fun tr _ => In tr (as_universe B)) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX qtight
0x326a4 TFIB_OOM 8 1 cf.
End a.
