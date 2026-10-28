(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image RzCPS FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Printf_mlib El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_m2s I_consts I_qck D_kit D_clx RT_iface RT_iface2 RT_iface3 F_achk Fe_icalls I_pchead I_vprintfw I_vfsn6 I_vsn6 Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA Pj_os_defsA Pj_loc_getA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import El_os_xsputnA El_np_wgiA El_np_intA El_ins_ifaceA El_os_insA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Section InsU.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS fill v : Z) (j148 j284 : list byte) (canary : word) (m0 : word -> option byte).
Variables (pb : word) (pp ep : Z) (dum : list byte).
Hypothesis LO : (lo <= bv_unsigned sp - INS_DEPTH)%Z.
Hypothesis LOLO : (0x6ce000 <= lo)%Z.
Hypothesis SPH : (bv_unsigned sp <= 2^47)%Z.
Hypothesis TP : tp = Z_to_bv 64 (0x6abdb8 + 48).
Hypothesis RO : (0x6ce000 <= OS)%Z.
Hypothesis RO2 : (OS + 288 <= lo)%Z.
Hypothesis RV : (0 <= v < 2^64)%Z.
Hypothesis FRM : frm0 fc.

Notation POST := (ins_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS 0x1002 (fill_after fill) j148 j284 canary m0).
Notation POST1 := (ins1_post EL_NP_UL 0x1120e8 sp gp tp s6 s7 s8 s9 s10 s11 F fc lo OS fill (v mod 4294967296)%Z pb pp ep dum j148 j284 canary ra s0 s1 s2 s3 s4 s5 v m0).
Notation WI := [(lo, bv_unsigned sp); (OS, OS + 288); (0x6abdb8, 0x6abdb8 + 8)]%Z.

Lemma ins_u_t1 : forall (fill' : Z) (j1 : list byte) (m : word -> option byte)
    (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : list byte)
    (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word),
  (0 <= fill' < 256)%Z -> fill_after fill = fill' -> PUTINV OS pp ep ->
  munch WI m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp + -80) ->
  rw_cells bsegs m (bv_unsigned sp + -80)
    [C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m OS
    ([C8 (Z_to_bv 64 0x168da8); C8 (Z_to_bv 64 0x6aac28); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep); CB 64 dum] ++ [C8 (Z_to_bv 64 0x168e30)] ++
     [C8 (Z_to_bv 64 0x168e58); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148; C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 OS); C8 (Z_to_bv 64 0x6aac28);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fill'); CB 4 j284]) ->
  rw_cells bsegs m 0x6aa628 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  rw_cells bsegs m 0x6abdb8 [C8 (Z_to_bv 64 0x6cc0b0)] -> ssp_cells m canary -> el_dccA m ->
  evt bsegs POST1
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) a0 a1 (Z_to_bv 64 (OS + 136)) a3 a4 a5 a6 a7
             (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 fill') x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1120c8) fc None m (seg_rom bsegs)).
Proof using LO LOLO SPH TP RO RO2 RV FRM.
  intros until t6. intros RF' FA PI MU WM MI ST FR OSF LBC TPC SSP DCC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  cbn [app] in OSF. unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  do 7 lstep.
  replace (Z.land fill' 255)%Z with fill'%Z
    by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  replace (Z.land v 4294967295) with (v mod 2^32)%Z by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)) as VL.
  lstep.
  takeZ OSF 9%nat (OS + 128)%Z SBF. takeZ OSF 1%nat (OS + 136)%Z V2.
  retype_at OSF 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  apply evt_done. unfold ins1_post.
  exists fill'. do 10 eexists. exists j1. eexists.
  split; [exact FA|]. split; [exact RF'|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
  split; [exact SBF|]. split; [exact V2|]. split; [exact OSF|]. split; [exact TPC|]. split; [split; [exact SSP1| exact SSP2]| do 15 eexists; exact LBC].
Qed.

Lemma ins_u_seg2 : forall (fill' : Z) (pb2 : word) (pp2 ep2 : Z) (dum2 j1 : list byte) (m : word -> option byte)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32),
  (0 <= fill' < 256)%Z -> fill_after fill = fill' -> PUTINV OS pp2 ep2 ->
  munch WI m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp + -80) ->
  rw_cells bsegs m (bv_unsigned sp + -80)
    [C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m OS (sb_cellsX pb2 (Z_to_bv 64 pp2) (Z_to_bv 64 ep2) dum2) -> rw_cells bsegs m (OS + 128) [C8 (Z_to_bv 64 0x168e30)] ->
  rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x168e58 0x1002 0 fill' j148 j284) ->
  LOCBA m -> rw_cells bsegs m 0x6abdb8 [C8 (Z_to_bv 64 0x6cc0b0)] -> ssp_cells m canary ->
  frm0 fc' -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) -> el_dccA m ->
  evt bsegs POST
    (MS (mkR (Z_to_bv 64 0x1120e8) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 fill') x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ft (Z_to_bv 64 0x1120e8) fc' None m (seg_rom bsegs)).
Proof using LO LOLO SPH TP RO RO2 RV FRM.
  intros until fc'. intros RF' FA PI' MU WM MI ST FR SBF V2 IOS LB TPC' SSP' FRM' FOK DCC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp2 < 2^62 /\ 0 <= ep2 < 2^62)%Z) by (destruct PI' as [[-> ->]|[-> ?]]; lia).
  destruct SSP' as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  destruct LB as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC'). unfold locb_cellsA, PJ_LOC_LO_A in LBC'.
  unfold sb_cellsX in SBF. unfold ios_cellsX in IOS.
  retype_at IOS 1%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  glueZ V2 IOS. glueZ SBF V2. rename SBF into OSF.
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
  release_frame FR0 ST (bv_unsigned sp + -80)%Z.
  do 10 lstep.
  release_frame FR ST (bv_unsigned sp).
  retype_at OSF 11%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  rewrite <- FA in OSF.
  unfold ins_postA, os_cellsX, sb_cellsX, ios_cellsX. sys_finish; [split; [exact SSP1 | exact SSP2] | cbn [app]; exact OSF | exact PI' | do 15 eexists; exact LBC'].
Qed.
End InsU.

Definition ins_u_seg1_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill v pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - INS_DEPTH)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  tp = Z_to_bv 64 (0x6abdb8 + 48) ->
  rw_cells bsegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
  (0x6ce000 <= OS)%Z -> (OS + 288 <= lo)%Z -> (fun v => 0 <= v < 2^64)%Z v ->
  rw_cells bsegs m 0x6abdb8 [C8 (Z_to_bv 64 0x6cc0b0)] -> ssp_cells m canary -> frm0 fc ->
  LOCBA m -> el_dccA m -> mem_inv bsegs m ->
  evt bsegs (ins1_post EL_NP_UL 0x1120e8 sp gp tp s6 s7 s8 s9 s10 s11 F fc lo OS fill (v mod 4294967296)%Z pb pp ep dum j148 j284 canary ra s0 s1 s2 s3 s4 s5 v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_INS_U) fc None m (seg_rom bsegs)).
Theorem ins_u_seg1 : ins_u_seg1_stmt.
Proof.
  unfold ins_u_seg1_stmt. intros until canary. intros ST LO LOLO SPH TP OSF PI FOK RO RO2 RV TPC SSP FRM LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS, OS + 288); (0x6abdb8, 0x6abdb8 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  unfold os_cellsX, sb_cellsX, ios_cellsX in OSF. cbn [app] in OSF.
  retype_at OSF 11%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  carve_frame 80%nat ST.
  destruct FOK as [-> | FNE].
  -
    retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].
    ins_ul_prologue sp ST FR LBC.
    if_false.
    do 4 lstep.
    carve_frame 16%nat ST.
    do 9 lstep. if_true. do 4 lstep.
    release_frame FR0 ST (bv_unsigned sp + -80)%Z.
    do 3 lstep.
    lstep.
    takeZ FR 3%nat (bv_unsigned sp + -64)%Z F0. takeZ FR 1%nat (bv_unsigned sp + -56)%Z LTMP.
    call_sp (use_facet_ctype_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64)%Z);
      [exact ST | lia | lia | (do 15 eexists; exact LBC) | exact LTMP | lia | lia | right; lia | right; lia | assumption |].
    rename PC into ST. clear POST.
    glueZ LTMP FR. glueZ F0 LTMP. rename F0 into FR.
    do 4 lstep.
    do 2 lstep.
    do 3 lstep.
    do 4 lstep. if_true. lstep.
    do 5 lstep.
    retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    eapply ins_u_t1 with (fill' := 0x20%Z); try eassumption; try reflexivity; try lia; first [cbn [app]; exact OSF | split; assumption | (split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]])].
  -
    assert (RF : (0 <= fill < 256)%Z) by lia.
    destruct FNE as [-> | ->];
      [ retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x20); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      | retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x30); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ];
      ins_ul_prologue sp ST FR LBC;
      (lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => lit_reg (Z.lor a b) end);
      bru true;
      [ retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)]; eapply ins_u_t1 with (fill' := 0x20%Z)
      | retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x30)]; eapply ins_u_t1 with (fill' := 0x30%Z) ];
      try eassumption; try reflexivity; try lia; first [cbn [app]; exact OSF | split; assumption | (split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]])].
Qed.

