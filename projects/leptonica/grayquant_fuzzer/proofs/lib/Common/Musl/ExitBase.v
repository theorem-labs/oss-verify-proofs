(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Export AgentNodesG.   (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Export RelocKit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Export RelocRW MuslTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := rl_segs.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[export] Ltac norm_pc_r ::=
  try lazymatch goal with
      | |- CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => first [ rl_pc_s p | wlit p ]
      end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section G.
  Context {RL : Reloc} {RD : RelocData RL}.

  Lemma store_ok_data : forall m (a : word) n,
    (rl_data_lo <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= rl_img_hi)%Z ->
    store_ok RSEGS m a n = true.
  Proof. exact rl_store_ok_data. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
    rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
    /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
    /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
    /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

  (* [comment removed for export] *)
  Definition stdio_globals (mem : word -> option byte) : Prop :=
    rdn RSEGS mem (rl dA_2f848 0x2f86b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
    /\ rdn RSEGS mem (rl dA_2fc88 0x2fc98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
    /\ rdn RSEGS mem (rl dA_2fc88 0x2fc88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
    /\ rdn RSEGS mem (rl dA_1f440 0x1f618) 8%nat = Some (word_to_le_bytes 8 (rl dA_1f440 0x1f530)) (* [comment removed for export] *)
    /\ rdn RSEGS mem (rl dA_1f440 0x1f528) 8%nat = Some (word_to_le_bytes 8 (rl dA_1f440 0x1f440)). (* [comment removed for export] *)
End G.

(* [comment removed for export] *)
Ltac sok_data :=
  store_ok_peel; apply store_ok_data; rl_dwin_bounds; rl_bounds; rl_unorm; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
