(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export SumWalkTac RefNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma ref_wseg_1c : wseg_ok RSEGS (0xb5000 : word) 212992%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma store_ok_data : forall m (a : word) n,
(0xb5000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0xe9000)%Z ->
store_ok RSEGS m a n = true.
Proof.
intros m a n Hlo Hhi.
eapply (store_ok_window RSEGS m (0xb5000 : word) a 212992%nat n 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.
End FPX_1.
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.
Ltac sok_frame SOK :=
store_ok_peel;
eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.
Section FPX_2. Context {fx : PropExec.FPState}.
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
/\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
/\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
/\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).
Definition stdio_globals (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0xe7ef3) 1%nat = Some [Z_to_bv 8 0]
/\ rdn RSEGS mem (Z_to_bv 64 0xe8438) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xe8428) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0xb61b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb60d0))
/\ rdn RSEGS mem (Z_to_bv 64 0xb60c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb5fe0)).
End FPX_2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
