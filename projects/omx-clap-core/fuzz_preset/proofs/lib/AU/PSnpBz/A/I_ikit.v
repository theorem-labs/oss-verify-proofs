(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/I_ikit.v, with its module paths and addresses changed; 2 of its 34 lines of code are new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 4 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_ikit.v: module paths (lib/A/Bz -> lib/AU/PSnpBz), the image binding Asan -> AsanUbsan, and 4 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-B). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_ikit.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A Require Import Shadow R_small R_thread.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition try_init_entry : Z := 0x5a828.

Lemma try_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells asegs m 0xac3d8 [C1 (Z_to_bv 8 1)] ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x601000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [(bv_unsigned sp - 16, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a828) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AI ST LO LOLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 9 lstep. if_false.
  do 3 lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  unfold frame_post. sys_finish.
Qed.
