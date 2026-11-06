(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step Image.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA RT_iface Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma ro_cells_C8s : forall (m : mem) A (ws : list word),
  mem_inv asegs m -> ro_bytes_b asegs A (cells_bytes (map C8 ws)) = true -> 0 <= A -> A + 8 * Z.of_nat (length ws) <= 2^64 ->
  ro_cells asegs m A (map C8 ws).
Proof.
  intros m A ws MI RB HA HL. split.
  - clear. induction ws as [|w ws IH]; cbn; [exact I|]. split; [exact I| exact IH].
  - apply ro_bytes_at; [exact MI| lia| | apply ro_bytes_b_sound; exact RB].
    assert (L : forall ws', Z.of_nat (length (cells_bytes (map C8 ws'))) = 8 * Z.of_nat (length ws')).
    { induction ws' as [|w' ws' IH]; [reflexivity|]. cbn [map].
      change (cells_bytes (C8 w' :: map C8 ws')) with (cbytes (C8 w') ++ cells_bytes (map C8 ws')).
      rewrite length_app, Nat2Z.inj_add, IH, (cbytes_length (C8 w') I). cbn [csize length]. lia. }
    rewrite L. lia.
Qed.

Lemma ed_ro_facts : forall m : mem, mem_inv asegs m -> ED_RO m.
Proof.
  intros m MI. unfold ED_RO. split.
  - apply (ro_cells_C8s m RO_SIGN_TAB [D_ONE; D_MONE] MI); [vm_compute; reflexivity| unfold RO_SIGN_TAB; lia| cbn; unfold RO_SIGN_TAB; lia].
  - apply (ro_cells_C8s m RO_HALF [D_HALF] MI); [vm_compute; reflexivity| unfold RO_HALF; lia| cbn; unfold RO_HALF; lia].
Qed.
