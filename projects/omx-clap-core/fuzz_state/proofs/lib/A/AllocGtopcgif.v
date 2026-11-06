(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AllocGtopcgif.v (a working branch 86aa4177b94, file sha256 dd1d36ce64cb) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: the secondary arm's instance line takes fs's instance U `fun tr S => tr_admit (as_universe B) S tr` (the U of AGif1.iface_cgif / AGif5.ifaceS_cgif at fs, FS-INSTANCE.md 1.4, and of AllocGcgif.aalloc_realizes_cgif). *)
(* The whole cgif_file Allocate contract, closed: AllocGcgif.aalloc_realizes_cgif for can_fill in {0, 1}, with no
   premise beyond the image's symbols and the depot's callee contract.
   - primary sizes (n <= 64512): AGtopcgifC.aalloc_prim_realizes_cgif_closed;
   - secondary sizes (64513 <= n < MALLOC_MAX): AGio.alloc_sec at cgif's interfaces AGif1.iface_cgif (AIface) and
     AGif5.ifaceS_cgif (AIfaceS);
   composed by AllocGtop.aalloc_realizes_of_prim_sec. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG AllocGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AGtopcgifC AGio AGif1 AGif5.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem aalloc_realizes_cgif_closed : forall (B : asyms) (cf : Z), TfibSyms B -> tfib_depot_spec B ->
cf = 0 \/ cf = 1 -> aalloc_realizes_cgif B cf.
Proof.
intros B cf TS HD1 HCF. unfold aalloc_realizes_cgif.
apply aalloc_realizes_of_prim_sec.
- exact (AGtopcgifC.aalloc_prim_realizes_cgif_closed B TS HD1 cf HCF).
- exact (AGio.alloc_sec B (fun tr S => tr_admit (as_universe B) S tr) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX
    LIVE_MAX qtight (AGif1.dpost_cgif B) 3 12 (AGif1.iface_cgif B TS HD1) (AGif5.ifaceS_cgif B cf TS HD1) TS
    (Z.le_refl _) cf HCF).
Qed.
End a.
