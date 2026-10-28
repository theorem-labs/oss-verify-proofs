(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_elemwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Section RootWalk.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma relem_walk1 : forall (ptr : list Z) (i j q out node P : Z)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    ptr_atA E P ptr -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 ->
    AINV_A E m ->
    rw_cells asegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> 0 < node -> node + 16 <= ae_lo E ->
    rw_cells asegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> (node + 16 <= out \/ out + 24 <= node) ->
    mem_inv asegs m -> stk asegs m (ae_lo E) q -> ae_lo E + 80 <= q -> q mod 16 = 0 -> shb_cells m ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' (q + -64) 16) ->
    (ptr <> [] -> forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> acc asegs m' (ae_PB E) (ae_NPB E)) ->
    evt asegs (elem_x1 E d ptr i q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (lvl_entry ATP_ELEM_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until jo. intros PAT EL I0 JN AI NODE N0 NB OUT QO OB O8 NO MI ST LO Q16 SHB SHZN SHZD SHZT _ ACCP.
    pose proof (ok_hi E OK) as [HL _].
    exact (elem_walk1 E OK d ptr i j q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
             PAT EL I0 JN AI NODE N0 ltac:(lia) ltac:(right; lia) OUT QO OB O8 NO MI ST LO Q16 SHB SHZN SHZD SHZT ACCP).
  Qed.
End RootWalk.
