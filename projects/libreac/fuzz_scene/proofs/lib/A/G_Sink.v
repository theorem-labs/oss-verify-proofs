(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: scene's closed sink in the form of a Theorem Labs lane's release text (a working branch
   4d244de18f0, in a Theorem Labs lane c8e8b0fa5ec): the record YE00.v:32 asink_syms and its laws YE01.v:28-40
   asink_img_laws are taken BY PATH; this file only binds scene's measured values, the way fuzz_grant's
   A/AE2k.v:9-46 binds its own. Module paths changed. *)
(* fuzz_scene.asan: every cell MEASURED in the pinned image's unstripped twin (.symtab / 8-byte reads, read with
   a Theorem Labs lane's sceref over pyelftools; cells6j.tsv (sha256 90401c4f5730; internal record), leaf h).
   The owned cells are a Theorem Labs lane's aenv_core (YE00.v:132-134): the threaded byte, the need_locks byte, the 4-byte
   ofl_lock and the 8-byte canary; the 8-byte ofl head is NOT owned (YE01.v:32 ail_env_static). *)
From Stdlib Require Import ZArith List.
(* Gate 6h: no sink-head or sink_syms instance is in scope (lib/Reusable/SinkGuard.v removes the released src0 ones). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK04 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
(* musl's stdio hooks, the FILE operations of the sink that is never opened. *)
Definition A_stdio_read : Z := 0x90614.
Definition A_stdio_write : Z := 0x90734.
Definition A_stdio_seek : Z := 0x9072c.
Definition A_stdio_close : Z := 0x905e8.
(* __libc + 1 / + 3, musl's `threaded` and `need_locks` bytes. *)
Definition A_threaded : Z := 0x5f6a29.
Definition A_need_locks : Z := 0x5f6a2b.
Definition A_ofl_lock : Z := 0x5f6e88.
(* __stack_chk_guard and the GOT word that holds its address. *)
Definition A_canary : Z := 0x5f67d8.
Definition A_got_canary : Z := 0x9c3a0.
(* The interceptors' metadata map pointer and its storage (__sanitizer's interceptor_metadata_map). *)
Definition A_meta_ptr : Z := 0xa3040.
Definition A_meta_mem : Z := 0xa3048.
(* The GOT cells of the interceptors the sink's laws name, each holding the real function's address (MEASURED). *)
Definition A_got_fflush : Z := 0x9d4c0.  Definition A_real_fflush : Z := 0x90a84.
Definition A_got_fwrite : Z := 0x9d458.  Definition A_real_fwrite : Z := 0x90ff0.
Definition A_got_strchr : Z := 0x9d428.  Definition A_real_strchr : Z := 0x94f38.
Definition scene_icells : list (Z * Z) :=
  [(A_got_fflush, A_real_fflush); (A_got_fwrite, A_real_fwrite); (A_got_strchr, A_real_strchr)].
(* A Theorem Labs lane's ak_owned: the aenv_core cells, and not the overflow head. *)
Definition scene_owned : list (Z * Z) :=
  [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (A_canary, 8)].
(* The path / mode / rwa / trailer strings are 0: scene's harness opens no file, so no statement reads them
   (fuzz_grant AE2k.v:41 does the same). *)
Definition scene_K : asink_syms :=
  mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock
    A_meta_ptr A_meta_mem A_got_canary A_canary scene_icells scene_owned.
Lemma scene_K_head : ak_ofl_head scene_K = 0x5f6e90.
Proof. reflexivity. Qed.
(* The one-clause form a Theorem Labs lane's entry walk takes (A/P_LLVMFuzzerTestOneInput.v AIL): for every byte of the cells
   the entry contract reads as 0, cgif YE01.v:29 ail_env. G_Top.v derives it from asink_img_laws at scene_K. *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition sink_img_laws (segs : list Segment) (B : asyms) (SINK_OWNED : list (Z * Z)) : Prop :=
  forall a, Exists (in_zr a) SINK_OWNED ->
    in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
End s.
