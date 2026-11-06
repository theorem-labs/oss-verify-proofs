(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA RT_iface Gq_numa Ed_statics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RO_RMCW : Z := 0x25970.
Definition W_BLUEW : word := Z_to_bv 64 0x3e4ccccd.   (* [comment removed for export] *)
Definition W_RMCX : word := Z_to_bv 64 0x2014181c.    (* [comment removed for export] *)
Definition W_RMCX2 : word := Z_to_bv 64 0xcf000001.   (* [comment removed for export] *)
Definition W_REDW : word := Z_to_bv 64 0x3e99999a.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RO_CASTLO : Z := 0x10300.
Definition RO_CASTHI : Z := 0x10340.
Definition D_CASTLO : word := Z_to_bv 64 0xbff0000000000000.   (* [comment removed for export] *)
Definition D_CASTHI : word := Z_to_bv 64 0x41f0000000000000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ro_cells_C4s : forall (m : mem) A (ws : list word),
  mem_inv asegs m -> ro_bytes_b asegs A (cells_bytes (map C4 ws)) = true -> 0 <= A -> A + 4 * Z.of_nat (length ws) <= 2^64 ->
  ro_cells asegs m A (map C4 ws).
Proof.
  intros m A ws MI RB HA HL. split.
  - clear. induction ws as [|w ws IH]; cbn; [exact I|]. split; [exact I| exact IH].
  - apply ro_bytes_at; [exact MI| lia| | apply ro_bytes_b_sound; exact RB].
    assert (L : forall ws', Z.of_nat (length (cells_bytes (map C4 ws'))) = 4 * Z.of_nat (length ws')).
    { induction ws' as [|w' ws' IH]; [reflexivity|]. cbn [map].
      change (cells_bytes (C4 w' :: map C4 ws')) with (cbytes (C4 w') ++ cells_bytes (map C4 ws')).
      rewrite length_app, Nat2Z.inj_add, IH, (cbytes_length (C4 w') I). cbn [csize length]. lia. }
    rewrite L. lia.
Qed.

Definition RMC_RO (m : mem) : Prop :=
  ro_cells asegs m RO_RMCW [C4 W_BLUEW; C4 W_RMCX; C4 W_RMCX2; C4 W_REDW]
  /\ ro_cells asegs m RO_CASTLO [C8 D_CASTLO] /\ ro_cells asegs m RO_CASTHI [C8 D_CASTHI].

Lemma rmc_ro_facts : forall m : mem, mem_inv asegs m -> RMC_RO m.
Proof.
  intros m MI. unfold RMC_RO. split; [| split].
  - apply (ro_cells_C4s m RO_RMCW [W_BLUEW; W_RMCX; W_RMCX2; W_REDW] MI); [vm_compute; reflexivity| unfold RO_RMCW; lia| cbn; unfold RO_RMCW; lia].
  - apply (ro_cells_C8s m RO_CASTLO [D_CASTLO] MI); [vm_compute; reflexivity| unfold RO_CASTLO; lia| cbn; unfold RO_CASTLO; lia].
  - apply (ro_cells_C8s m RO_CASTHI [D_CASTHI] MI); [vm_compute; reflexivity| unfold RO_CASTHI; lia| cbn; unfold RO_CASTHI; lia].
Qed.
