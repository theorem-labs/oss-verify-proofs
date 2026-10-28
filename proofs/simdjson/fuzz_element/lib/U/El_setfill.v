(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit El_os_defs El_ins_iface El_os_pad.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac lit_reg e := let v := eval vm_compute in e in replace e with v by (vm_compute; reflexivity).

Lemma le4_byte : forall c, (0 <= c < 256)%Z -> le4 (Z_to_bv 64 c) = [Z_to_bv 8 c; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros c Hc. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite (Z.shiftr_div_pow2 c 8) by lia. rewrite (Z.div_small c (2^8)) by lia. reflexivity.
Qed.

Lemma fill4_retype : forall m A cs c, (0 <= c < 256)%Z ->
  rw_cells usegs m A cs ->
  firstn 4 (skipn 30 cs) = [C1 (Z_to_bv 8 c); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m A (firstn 30 cs ++ [C4 (Z_to_bv 64 c)] ++ skipn 4 (skipn 30 cs)).
Proof.
  intros m A cs c Hc H E. apply (rw_cells_retype_at usegs m A cs 30 4 [C4 (Z_to_bv 64 c)] H).
  - cbn. repeat split; exact I.
  - rewrite E. cbn [cells_bytes cbytes app]. rewrite le4_byte by lia. reflexivity.
  - rewrite E. reflexivity.
Qed.

Theorem setfill_proof : setfill_stmt.
Proof.
  unfold setfill_stmt. intros until j284. intros ST LO LOLO OSF FOK RO RO2 AL8 CPC RC RCP RCP2 SEPC DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (OS + 280, OS + 284)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct DCC as (VT & _ & _ & _ & _ & _).
  unfold os_cellsX, sb_cells, ios_cellsX in OSF. cbn [app] in OSF.
  destruct FOK as [-> | ->];
    [ retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x20); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    | retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x30); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ];
    carve_frame 48%nat ST;
    do 12 lstep;
    [ br_is false ltac:(rewrite (land7_al8' _ 136 AL8 eq_refl); reflexivity)
    | br_is false ltac:(rewrite (land7_al8' _ 136 AL8 eq_refl); reflexivity) ];
    do 12 lstep;
    (lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => lit_reg (Z.lor a b) end);
    lstep;
    [ bru true | bru true ];
    lstep;
    try sbZ;
    do 3 lstep;
    do 8 lstep;
    release_frame FR ST (bv_unsigned sp);
    replace (bv_unsigned (Z_to_bv 8 c)) with c in OSF
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256%Z; symmetry; apply Z.mod_small; lia);
    (apply (fill4_retype _ _ _ c RC) in OSF; [| reflexivity]);
    cbv [firstn skipn app] in OSF;
    unfold setfill_post, os_cellsX, sb_cells, ios_cellsX; sys_finish; cbn [app]; exact OSF.
Qed.
