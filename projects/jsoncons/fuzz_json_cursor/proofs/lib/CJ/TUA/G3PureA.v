(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP Image.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TU Require G3Pure.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUA Require Import DgWalkA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition PT_BASE : Z := 0x26140.   Definition PE_BASE : Z := 0x27c00.

Lemma PT_ro : ro_bytes_b rsegs PT_BASE G3Pure.PT_BYTES = true.
Proof. vmc_refl. Qed.
Lemma PE_ro : ro_bytes_b rsegs PE_BASE G3Pure.PE_BYTES = true.
Proof. vmc_refl. Qed.

Lemma pt_read : forall m i, mem_inv rsegs m -> 0 <= i < 687 ->
  ov_read_bytes rsegs m (wa (PT_BASE + 8 * i)) 8 = Some (firstn 8 (skipn (Z.to_nat (8 * i)) G3Pure.PT_BYTES)).
Proof.
  intros m i MI Hi. pose proof (ro_cells_image rsegs m PT_BASE G3Pure.PT_BYTES MI PT_ro ltac:(unfold PT_BASE; lia) ltac:(rewrite G3Pure.PT_len; unfold PT_BASE, G3Pure.NPOW; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  apply bytes_at_read; [exact RO | lia | rewrite G3Pure.PT_len; unfold G3Pure.NPOW; lia].
Qed.
Lemma pe_read : forall m i, mem_inv rsegs m -> 0 <= i < 687 ->
  ov_read_bytes rsegs m (wa (PE_BASE + 4 * i)) 4 = Some (firstn 4 (skipn (Z.to_nat (4 * i)) G3Pure.PE_BYTES)).
Proof.
  intros m i MI Hi. pose proof (ro_cells_image rsegs m PE_BASE G3Pure.PE_BYTES MI PE_ro ltac:(unfold PE_BASE; lia) ltac:(rewrite G3Pure.PE_len; unfold PE_BASE, G3Pure.NPOW; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  apply bytes_at_read; [exact RO | lia | rewrite G3Pure.PE_len; unfold G3Pure.NPOW; lia].
Qed.
