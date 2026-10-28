(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
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
Lemma ltu_ZZ : forall x y, (0 <= x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y mod 2^64)%Z.
Proof. intros x y Hx. rewrite bv_ltu_Z, unsigned_lit_wrap, unsigned_lit_wrap, (Z.mod_small x) by lia. reflexivity. Qed.
Lemma eqb_ZZ : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2^64 =? y mod 2^64)%Z.
Proof. intros x y. rewrite bv_eqb_Z, !unsigned_lit_wrap. reflexivity. Qed.
Lemma land7_of_al8 : forall x : Z, (x mod 8 = 0)%Z -> Z.land x 7 = 0%Z.
Proof. intros x H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact H. Qed.
Lemma land7_al8' : forall x c : Z, (x mod 8 = 0)%Z -> (c mod 8 = 0)%Z -> Z.land (x + c) 7 = 0%Z.
Proof. intros x c Hx Hc. apply land7_of_al8. rewrite Z.add_mod, Hx, Hc by lia. reflexivity. Qed.
Lemma lts_small : forall x y, (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor, !unsigned_lit by lia. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec x y), (Z.ltb_spec (x + 2^63) (y + 2^63)); lia.
Qed.
Ltac bru b := br_is b ltac:(rewrite ?ltu_ZZ, ?eqb_ZZ by lia; cbn [negb Z.modulo Z.pow Z.pow_pos Pos.iter Z.mul];
                             first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
                                   | apply negb_true_iff; first [apply Z.ltb_ge; lia | apply Z.eqb_neq; lia]
                                   | apply negb_false_iff; first [apply Z.ltb_lt; lia | apply Z.eqb_eq; lia]]).

Theorem os_put_proof : os_xsputn_stmt -> os_put_stmt.
Proof.
  intros XSP. unfold os_put_stmt. intros until bs. intros ST LO LOLO OSF LB RO RO2 AL8 BUFC RN RB RB2 SEP VT WS GCT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (OS, OS + 288)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (OS, OS + 288)]%Z m) as MUF.
  pose proof (wmono_refl usegs m) as WMF.
  destruct OSF as (dum & j148 & j284 & OSF). unfold os_cells, sb_cells, ios_cells in OSF. cbn [app] in OSF.
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & LBC). unfold locb_cells in LBC.

  retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].
  retype_at OSF 11%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  carve_frame 96%nat ST.
  do 22 lstep.
  if_true.
  do 2 lstep.
  if_true.
  do 6 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 5 lstep.
  br_is false ltac:(rewrite (land7_al8' _ 136 AL8 eq_refl); reflexivity).
  do 7 lstep.
  if_true.
  do 3 lstep.
  br_is false ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply Z.ltb_ge; lia).
  do 3 lstep.
  replace (0 <? BUF)%Z with true by (symmetry; apply Z.ltb_lt; lia). replace (BUF + N <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
  if_false.
  do 12 lstep.
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
  lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 13 lstep.
  if_true.
  do 12 lstep.
  carve_frame 96%nat ST.
  do 11 lstep.
  br_is false ltac:(rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; lia).
  do 5 lstep.
  lstep.
  lstep.
  replace (BUF + N - BUF)%Z with N by lia.
  lstep.
  br_is true ltac:(rewrite (lts_small N 0) by lia; cbn [negb]; apply negb_true_iff, Z.ltb_ge; lia).
  lstep.
  lstep.
  replace (BUF - BUF)%Z with 0%Z by lia.
  lstep.
  rewrite (land7_of_al8 OS AL8).
  lstep.
  if_true.
  lstep.
  if_true.
  lstep.
  replace (BUF + N - BUF)%Z with N by lia.
  lstep.
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
    lstep.
    bru false.
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
