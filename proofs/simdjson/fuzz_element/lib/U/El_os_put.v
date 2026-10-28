(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_defs Pj_os_kit El_os_defs El_ins_iface El_os_xsputn El_os_pad.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.

Ltac step_until n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 n) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => lstep; step_until n
  end.

Section Put.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS BUF N CAP fill : Z) (bs j148 j284 : list byte) (m0 : word -> option byte).
Hypothesis LO : (lo <= bv_unsigned sp - 256)%Z.
Hypothesis LOLO : (0x111000 <= lo)%Z.
Hypothesis RO : (bv_unsigned sp <= OS)%Z.
Hypothesis RO2 : (OS + 288 < 2^62)%Z.
Hypothesis RN : (0 <= N <= CAP)%Z.
Hypothesis RB : (0 < BUF)%Z.
Hypothesis AL8 : (OS mod 8 = 0)%Z.
Hypothesis RB2 : (BUF + CAP < 2^62)%Z.
Hypothesis SEP : (BUF + CAP <= lo \/ OS + 288 <= BUF \/ (bv_unsigned sp <= BUF /\ BUF + CAP <= OS))%Z.

Notation POST := (os_putX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS fill j148 j284 m0).
Notation WQ := [(bv_unsigned sp - 256, bv_unsigned sp); (OS, OS + 288)]%Z.

Lemma put_tail : forall (fill' : Z) (pb : word) (pp ep : Z) (dum j0 j1 jl : list byte) (m : word -> option byte)
    (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : list byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  (0 <= fill' < 256)%Z -> fill_after fill = fill' -> PUTINV OS pp ep ->
  munch WQ m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp + -96) ->
  rw_cells usegs m (bv_unsigned sp + -96)
    [CB 8 j0; C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); CB 8 jl; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m OS
    ([C8 (Z_to_bv 64 0xd6878); C8 (Z_to_bv 64 0xee3c8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep); CB 64 dum] ++ [C8 (Z_to_bv 64 0xd6900)] ++
     [C8 (Z_to_bv 64 0xd6928); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148; C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 OS); C8 (Z_to_bv 64 0xee3c8);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fill'); CB 4 j284]) ->
  rw_cells usegs m 0xeddc8 (locb_cells l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  bytes_at usegs m BUF bs -> Z.of_nat (length bs) = CAP ->
  rw_cells usegs m 0xd68d8 [C8 (Z_to_bv 64 0x82530); C8 (Z_to_bv 64 0x3fdcc); C8 (Z_to_bv 64 8)] ->
  evt usegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 BUF) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 OS) (Z_to_bv 64 (BUF + N)) (Z_to_bv 64 BUF) (Z_to_bv 64 fill') s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x408bc) fc None m (seg_rom usegs)).
Proof using LO LOLO RO RO2 RN RB RB2 SEP AL8.
  intros until t6. intros RF' FA PI MU WM MI ST FR OSF LBC BUFC LBU VT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  cbn [app] in OSF. unfold locb_cells in LBC.
  lstep.
  replace (Z.land fill' 255)%Z with fill'%Z
    by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  do 5 lstep.
  lstep.

  replace (Z_to_bv 64 BUF) with (Z_to_bv 64 (BUF + 0)) at 4 by (f_equal; lia).
  takeZ OSF 9%nat (OS + 128)%Z SBF. takeZ OSF 1%nat (OS + 136)%Z V2.
  retype_at OSF 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_sub mm BUF bs 0 N BUFC ltac:(lia) ltac:(lia) ltac:(lia)) as SRCN end.
  replace (BUF + 0)%Z with BUF in SRCN by lia.
  call_sp (os_pad_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo OS BUF N 0%Z 0%Z 0x1002%Z fill' pp ep);
    [exact ST | lia | lia | exact SBF | exact PI | exact OSF | lia | lia | exact AL8 | exact SRCN | rewrite firstn_length_le by (rewrite length_skipn; lia); lia
    | lia | lia | lia | lia | lia | lia | lia | exact VT | assumption |].
  try clear SRCN.
  rename PC into ST. rename PC0 into SBF. rename PC1 into PI'. rename POST into OSF. unfold sb_cells in SBF. unfold ios_cellsX in OSF.
  retype_at OSF 1%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  glueZ V2 OSF. glueZ SBF V2. rename SBF into OSF.
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
  retype_at OSF 11%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  rewrite <- FA in OSF.
  unfold os_putX_post. sys_finish; [exact OSF | exact PI' | do 15 eexists; exact LBC].
Qed.
End Put.

Ltac put_prologue ST AL8 BUF N :=
  carve_frame 96%nat ST;
  do 22 lstep;
  if_true;
  do 2 lstep;
  if_true;
  do 6 lstep;
  if_false;
  do 2 lstep;
  if_false;
  do 5 lstep;
  br_is false ltac:(rewrite (land7_al8' _ 136 AL8 eq_refl); reflexivity);
  do 7 lstep;
  if_true;
  do 3 lstep;
  br_is false ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply Z.ltb_ge; lia);
  do 3 lstep;
  replace (0 <? BUF)%Z with true by (symmetry; apply Z.ltb_lt; lia); replace (BUF + N <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z Z.lxor];
  if_false;
  do 12 lstep.

Ltac lit_reg e := let v := eval vm_compute in e in replace e with v by (vm_compute; reflexivity).

Theorem os_putX_proof : os_putX_stmt.
Proof.
  unfold os_putX_stmt. intros until j284. intros ST LO LOLO OSF PI FOK LB RO RO2 AL8 BUFC LBU RN RB RB2 SEP DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (OS, OS + 288)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (conj BUFC I) as BUFbox. clear BUFC.
  destruct DCC as (VT & WS & _ & _ & _ & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  unfold os_cellsX, sb_cells, ios_cellsX in OSF. cbn [app] in OSF.
  retype_at OSF 11%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  destruct FOK as [-> | FNE].
  -
    retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].
    put_prologue ST AL8 BUF N.
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
      [exact ST | lia | lia | (exists l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15; exact LBC) | exact LTMP | lia | assumption |].
    rename PC into ST. clear POST.
    glueZ LTMP FR. glueZ F0 LTMP. rename F0 into FR.
    lstep.
    if_false.
    do 2 lstep.
    if_false.
    do 13 lstep.
    if_true.
    do 5 lstep.
    retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    merge_at FR 4%nat 1%nat.
    eapply put_tail with (fill' := 0x20%Z); try eassumption; try reflexivity; try lia; [cbn [app]; exact OSF | eapply bytes_at_transport; [exact (proj1 BUFbox) | exact MU | cbv [disjoint_from fst snd]; repeat split; lia]].
  -
    destruct FNE as [-> | ->];
      [ retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x20); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      | retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x30); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ];
      put_prologue ST AL8 BUF N;
      (lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => lit_reg (Z.lor a b) end);
      bru true;
      [ retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)]; eapply put_tail with (fill' := 0x20%Z)
      | retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x30)]; eapply put_tail with (fill' := 0x30%Z) ];
      try eassumption; try reflexivity; try lia; [cbn [app]; exact OSF | eapply bytes_at_transport; [exact (proj1 BUFbox) | exact MU | cbv [disjoint_from fst snd]; repeat split; lia] | cbn [app]; exact OSF | eapply bytes_at_transport; [exact (proj1 BUFbox) | exact MU | cbv [disjoint_from fst snd]; repeat split; lia]].
Qed.
