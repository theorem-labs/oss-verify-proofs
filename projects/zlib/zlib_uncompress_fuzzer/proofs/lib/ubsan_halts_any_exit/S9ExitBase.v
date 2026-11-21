(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import
  WsegFast PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require S9Wseg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.


Lemma ref_wseg_1c {RCa1 : RunCtx}  : wseg_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (0x22000 : word) 466944%nat = true.
Proof.
  exact (eq_ind (Z_to_bv 64 0x22000) (fun a : word => wseg_ok (run_segments RSEGS rc_inp rc_sp rc_mb) a 466944%nat = true) S9Wseg.data_window_wseg (0x22000%bv : word)
           ltac:(apply bv_eq; vm_compute; reflexivity)).
Qed.

Lemma store_ok_data {RCa1 : RunCtx}  : forall m (a : word) n,
  (0x22000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x94000)%Z ->
  store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window (run_segments RSEGS rc_inp rc_sp rc_mb) m (0x22000 : word) a 466944%nat n 0x22000 0x94000);
    [reflexivity | vm_cast_no_check (@eq_refl Z 0x94000%Z) | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.

Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.


Definition file_clean {RCa1 : RunCtx}  (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

Definition stdio_globals {RCa1 : RunCtx}  (mem : word -> option byte) : Prop :=
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x931eb) 1%nat = Some [Z_to_bv 8 0]
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93618) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93608) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22d18))
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22c28)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
