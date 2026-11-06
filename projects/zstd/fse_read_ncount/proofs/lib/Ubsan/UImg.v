(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.zstd.fse_read_ncount.images Require Export Ubsan.
Import ListNotations.
Open Scope Z_scope.
Definition usegs : list Segment := Ubsan.M.loaded_segments.
Definition u_init_pc : N := Ubsan.M.init_pc.
Definition u_phdrs : PhdrInfo := Ubsan.M.phdrs.
Lemma segments_reserved_ubsan :
segments_reserved usegs =
[(Z_to_bv 64 0x10000, Z_to_bv 64 0x2000); (Z_to_bv 64 0x12000, Z_to_bv 64 0xb000);
(Z_to_bv 64 0x1d000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x1e000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.
Lemma reserved_top_ubsan : reserved_top (segments_reserved usegs) = 0x50000.
Proof. vm_compute. reflexivity. Qed.
