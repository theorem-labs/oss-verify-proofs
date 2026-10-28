(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2 X1bn X1cc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gj X1fl X1ea X1fr X1no X1nl.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Notation rsegs := X1gj.rsegs.

Definition stderr_cells0 : list cell :=
file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x6db18 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80).

Lemma stderr_cells0_image : forall (m : word -> option byte),
(forall a : word, (0x3b000 <= bv_unsigned a < 0x6e000)%Z -> outside rcrt_written (bv_unsigned a) -> m a = None) ->
rw_cells rsegs m RSTDERR stderr_cells0.
Proof.
intros m NONE.
apply (rw_cells_recast rsegs m RSTDERR [CB (length (cells_bytes stderr_cells0)) (cells_bytes stderr_cells0)] stderr_cells0).
- apply (rw_cells_image0 rsegs m RSTDERR (cells_bytes stderr_cells0)).
+ intros a Ha. change (Z.of_nat (length (cells_bytes stderr_cells0))) with 232%Z in Ha.
apply NONE; [lia|]. cbn [outside rcrt_written]. lia.
+ vm_compute. reflexivity.
+ lia.
+ change (Z.of_nat (length (cells_bytes stderr_cells0))) with 232%Z. lia.
- cbn. repeat split; exact I.
- vm_compute. reflexivity.
- reflexivity.
Qed.

Theorem stderr_wfile0_init : forall (m : word -> option byte),
(forall a : word, (0x3b000 <= bv_unsigned a < 0x6e000)%Z -> outside rcrt_written (bv_unsigned a) -> m a = None) ->
stderr_wfile0 m.
Proof.
intros m NONE. first [ unshelve sf_eexists 5%nat; [ exact ((Z_to_bv 64 5)) | exact ((Z_to_bv 64 0)) | exact (0) | exact (0) | exact ((repeat (Z_to_bv 8 0) 80)) | ] | sf_fb; exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80) ].
split; [exact (stderr_cells0_image m NONE)|].
split; [reflexivity|]. split; [left; reflexivity|]. lia.
Qed.
