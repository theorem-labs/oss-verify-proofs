(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA El_defsA El_armkitA El_callsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section W30.
  Lemma w30_walk1 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q node P L i g a : Z)
      (ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells asegs m (q + 24) [C8 (wz P); C8 (wz L); C8 (wz i); C8 (wz g); C8 (wz a)] -> 0 <= q -> q + 128 < 2^64 ->
    K (lvl_entry ATKCI_FN_A (wz 0xb1df0) q gp t0 t1 t2 s0 (wz q) (q + 96) node P L a4 a5 a6 a7 s2 s3 s4 s5 (wz node) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m) ->
    evt asegs K (MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 s0 (wz q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz node) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0xb1ddc) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros C24 Q0 QH HK.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    zstep. zstep. step. step. zstep. apply evt_done. exact HK.
  Qed.

End W30.
