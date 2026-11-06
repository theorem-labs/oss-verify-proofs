(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_defs Pj_os_kit.
From OSSVerify.simdjson.fuzz_print_json.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.
Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.

Theorem os_put_proof : os_xsputn_stmt -> os_put_stmt.
Proof.
  intros XSP. unfold os_put_stmt. intros until bs. intros ST LO LOLO OSF LB RO RO2 BUFC RN RB RB2 SEP VT WS GCT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (OS, OS + 288)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (OS, OS + 288)]%Z m) as MUF.
  pose proof (wmono_refl psegs m) as WMF.
  destruct OSF as (dum & j148 & j284 & OSF). unfold os_cells, sb_cells, ios_cells in OSF. cbn [app] in OSF.
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & LBC). unfold locb_cells in LBC.

  retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].
  retype_at OSF 11%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  carve_frame 96%nat ST.
  do 22 lstep.
  if_true.
  do 2 lstep.
  if_true.
  do 5 lstep.
  if_false.
  do 17 lstep.
  if_false.
  do 3 lstep.
  carve_frame 16%nat ST.
  do 9 lstep.
  if_true.
  do 4 lstep.
  release_frame FR0 ST (bv_unsigned sp + -96)%Z.
  do 3 lstep.
  lstep.
  takeZ FR 4%nat (bv_unsigned sp + -72)%Z F0. takeZ FR 1%nat (bv_unsigned sp + -64)%Z LTMP.
  call_sp (use_facet_ctype_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -72)%Z);
    [exact ST | lia | lia | (exists l1, l2, l3, l4, l5, l6; exact LBC) | exact LTMP | lia | assumption |].
  rename PC into ST. clear POST.
  glueZ LTMP FR. glueZ F0 LTMP. rename F0 into FR.
  do 13 lstep.
  if_true.
  do 10 lstep.
  if_false.
  do 6 lstep.
  carve_frame 96%nat ST.
  do 11 lstep.
  br_is false ltac:(rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; lia).
  do 9 lstep.
  replace (BUF - BUF)%Z with 0%Z by lia.
  if_true.
  do 6 lstep.
  replace (BUF + N - BUF)%Z with N by lia.
  replace (Z.lxor N 9223372036854775808 <? 9223372036854775808)%Z with false
    by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_pow2_small by lia; lia).
  cbn [Z.b2z]. change ((0 - 0) mod 18446744073709551616)%Z with 0%Z. rewrite Z.land_0_l.
  if_true.
  do 2 lstep.
  replace (BUF + N - BUF)%Z with N by lia.
  destruct (Z.eq_dec N 0) as [N0|N1].
  -
    subst N. if_true.
    do 14 lstep.
    release_frame FR0 ST (bv_unsigned sp + -96)%Z.
    lstep.
    br_is true ltac:(rewrite bv_eqb_Z; cbn [negb]; apply negb_true_iff, Z.eqb_neq; rewrite unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; lia).
    do 2 lstep.
    carve_frame 16%nat ST.
    do 9 lstep.
    br_is false ltac:(rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; lia).
    do 2 lstep.
    if_false.
    do 3 lstep.
    if_true.
    do 4 lstep.
    release_frame FR0 ST (bv_unsigned sp + -96)%Z.
    do 11 lstep.
    release_frame FR ST (bv_unsigned sp).
    retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    retype_at OSF 11%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
    lazymatch type of OSF with rw_cells _ ?mf _ _ =>
      assert (OSU : OSUSED mf OS) by (unfold OSUSED, os_cells, sb_cells, ios_cells; cbn [app]; do 6 eexists; exact OSF);
      assert (LBF : LOCB mf) by (exists l1, l2, l3, l4, l5, l6; exact LBC)
    end.
    unfold os_put_post. sys_finish.
  -
    br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
    do 5 lstep.
    lstep.
    takeZ OSF 9%nat (OS + 128)%Z SBF.
    call_sp (XSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OS BUF N CAP);
      [exact ST | lia | lia | exact SBF | lia | lia | exact BUFC | lia | lia | lia | lia | exact VT | assumption |].
    rename PC into ST. rename POST into SBF. unfold sb_cells in SBF.
    glueZ SBF OSF. rename SBF into OSF.
    lstep.
    br_is false ltac:(rewrite bv_eqb_Z, Z.eqb_refl; reflexivity).
    do 14 lstep.
    release_frame FR0 ST (bv_unsigned sp + -96)%Z.
    lstep.
    br_is true ltac:(rewrite bv_eqb_Z; cbn [negb]; apply negb_true_iff, Z.eqb_neq; rewrite unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; lia).
    do 2 lstep.
    carve_frame 16%nat ST.
    do 9 lstep.
    br_is false ltac:(rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; lia).
    do 2 lstep.
    if_false.
    do 3 lstep.
    if_true.
    do 4 lstep.
    release_frame FR0 ST (bv_unsigned sp + -96)%Z.
    do 11 lstep.
    release_frame FR ST (bv_unsigned sp).
    retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    retype_at OSF 11%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
    lazymatch type of OSF with rw_cells _ ?mf _ _ =>
      assert (OSU : OSUSED mf OS) by (unfold OSUSED, os_cells, sb_cells, ios_cells; cbn [app]; do 6 eexists; exact OSF);
      assert (LBF : LOCB mf) by (exists l1, l2, l3, l4, l5, l6; exact LBC)
    end.
    unfold os_put_post. sys_finish.
Qed.
