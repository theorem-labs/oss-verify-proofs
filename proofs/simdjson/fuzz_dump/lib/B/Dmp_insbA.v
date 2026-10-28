(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image RzCPS FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Printf_mlib El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_m2s I_consts I_qck D_kit D_clx RT_iface RT_iface2 RT_iface3 F_achk Fe_icalls I_pchead I_vprintfw I_vfsn6 I_vsn6 Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA Pj_os_defsA Pj_loc_getA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import El_os_xsputnA El_np_wgiA El_np_intA El_ins_ifaceA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import El_os_insA El_os_ins3A El_np_boolA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition ins_b_cpsA (RT : rt_sig) (PMc : Model -> Prop) : Prop := ins_cpsA RT PMc 0x111a40 (fun v => v = 0 \/ v = 1)%Z 0x1002 0 FILLOK EL_INS_STACK_A.

Section InsB.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS fill v : Z) (j148 j284 : list byte) (canary : word) (m0 : word -> option byte).
Variables (pb : word) (pp ep : Z) (dum : list byte).
Hypothesis LO : (lo <= bv_unsigned sp - INS_DEPTH)%Z.
Hypothesis LOLO : (0x6cd000 <= lo)%Z.
Hypothesis SPH : (bv_unsigned sp <= 2^47)%Z.
Hypothesis TP : tp = Z_to_bv 64 (0x6ab338 + 48).
Hypothesis RO : (0x6cd000 <= OS)%Z.
Hypothesis RO2 : (OS + 288 <= lo)%Z.
Hypothesis RV : (v = 0 \/ v = 1)%Z.
Hypothesis FRM : frm0 fc.

Notation POST := (ins_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS 0x1002 (fill_after fill) j148 j284 canary m0).
Notation POST1 := (ins1_post EL_NP_BOOL_A 0x111b5c sp gp tp s6 s7 s8 s9 s10 s11 F fc lo OS fill v pb pp ep dum j148 j284 canary ra s0 s1 s2 s3 s4 s5 v m0).
Notation WI := [(lo, bv_unsigned sp); (OS, OS + 288); (0x6ab338, 0x6ab338 + 8)]%Z.

Lemma ins_b_t1 : forall (fill' : Z) (j1 : list byte) (m : word -> option byte)
    (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : list byte)
    (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word),
  (0 <= fill' < 256)%Z -> fill_after fill = fill' -> PUTINV OS pp ep ->
  munch WI m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp + -80) ->
  rw_cells bsegs m (bv_unsigned sp + -80)
    [C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m OS
    ([C8 (Z_to_bv 64 0x168808); C8 (Z_to_bv 64 0x6aa1a8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep); CB 64 dum] ++ [C8 (Z_to_bv 64 0x168890)] ++
     [C8 (Z_to_bv 64 0x1688b8); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148; C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 OS); C8 (Z_to_bv 64 0x6aa1a8);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fill'); CB 4 j284]) ->
  rw_cells bsegs m 0x6a9ba8 (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  rw_cells bsegs m 0x6ab338 [C8 (Z_to_bv 64 0x6cb630)] -> ssp_cells m canary -> el_dccA m ->
  ro_cells bsegs m 0x16cb98 [C8 (Z_to_bv 64 EL_NP_BOOL_A)] ->
  evt bsegs POST1
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) a0 a1 (Z_to_bv 64 (OS + 136)) a3 a4 a5 a6 a7
             (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 fill') x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x111b40) fc None m (seg_rom bsegs)).
Proof using LO LOLO SPH TP RO RO2 RV FRM.
  intros until t6. intros RF' FA PI MU WM MI ST FR OSF LBC TPC SSP DCC NPB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  cbn [app] in OSF. unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  do 6 lstep.
  replace (Z.land fill' 255)%Z with fill'%Z
    by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  lstep.
  takeZ OSF 9%nat (OS + 128)%Z SBF. takeZ OSF 1%nat (OS + 136)%Z V2.
  retype_at OSF 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  apply evt_done. unfold ins1_post.
  exists fill'. do 10 eexists. exists j1. eexists.
  split; [exact FA|]. split; [exact RF'|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
  split; [exact SBF|]. split; [exact V2|]. split; [exact OSF|]. split; [exact TPC|]. split; [split; [exact SSP1| exact SSP2]| do 15 eexists; exact LBC].
Qed.

Lemma ins_b_seg2 : forall (fill' : Z) (pb2 : word) (pp2 ep2 : Z) (dum2 j1 : list byte) (m : word -> option byte)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32),
  (0 <= fill' < 256)%Z -> fill_after fill = fill' -> PUTINV OS pp2 ep2 ->
  munch WI m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp + -80) ->
  rw_cells bsegs m (bv_unsigned sp + -80)
    [C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m OS (sb_cellsX pb2 (Z_to_bv 64 pp2) (Z_to_bv 64 ep2) dum2) -> rw_cells bsegs m (OS + 128) [C8 (Z_to_bv 64 0x168890)] ->
  rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x1688b8 0x1002 0 fill' j148 j284) ->
  LOCBA m -> rw_cells bsegs m 0x6ab338 [C8 (Z_to_bv 64 0x6cb630)] -> ssp_cells m canary ->
  frm0 fc' -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) -> el_dccA m ->
  evt bsegs POST
    (MS (mkR (Z_to_bv 64 0x111b5c) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 fill') x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ft (Z_to_bv 64 0x111b5c) fc' None m (seg_rom bsegs)).
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
End InsB.

Ltac ins_b_prologue sp ST FR LBC :=
  do 21 lstep;
  if_true;
  do 2 lstep; if_true;
  do 5 lstep; if_false;
  do 5 lstep;
  carve_frame 16%nat ST;
  do 9 lstep; if_true; do 4 lstep;
  match goal with H : rw_cells _ _ (bv_unsigned sp + -96)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -80)%Z end;
  do 3 lstep;
  lstep;
  lazymatch type of FR with rw_cells _ _ _ (_ :: CB 7 ?x :: _) => set (j7 := x) in FR; clearbody j7 end;
  let F0 := fresh "F0" in let LTMP := fresh "LTMP" in
  takeZ FR 3%nat (bv_unsigned sp + -64)%Z F0; takeZ FR 1%nat (bv_unsigned sp + -56)%Z LTMP;
  call_sp (use_facet_nput_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64)%Z);
    [exact ST | lia | lia | (do 15 eexists; exact LBC) | exact LTMP | lia | assumption |];
  clear ST; match goal with H : stk _ _ _ _ |- _ => rename H into ST end; match goal with H : LOCBA _ |- _ => clear H end;
  glueZ LTMP FR; glueZ F0 LTMP; rename F0 into FR;
  do 3 lstep;
  do 4 lstep; if_true; lstep;
  do 16 lstep.

Definition ins_b_seg1_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill v pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - INS_DEPTH)%Z -> (0x6cd000 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  tp = Z_to_bv 64 (0x6ab338 + 48) ->
  rw_cells bsegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
  (0x6cd000 <= OS)%Z -> (OS + 288 <= lo)%Z -> (fun v => v = 0 \/ v = 1)%Z v ->
  rw_cells bsegs m 0x6ab338 [C8 (Z_to_bv 64 0x6cb630)] -> ssp_cells m canary -> frm0 fc ->
  LOCBA m -> el_dccA m -> ro_cells bsegs m 0x16cb98 [C8 (Z_to_bv 64 EL_NP_BOOL_A)] -> mem_inv bsegs m ->
  evt bsegs (ins1_post EL_NP_BOOL_A 0x111b5c sp gp tp s6 s7 s8 s9 s10 s11 F fc lo OS fill v pb pp ep dum j148 j284 canary ra s0 s1 s2 s3 s4 s5 v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x111a40) fc None m (seg_rom bsegs)).
Theorem ins_b_seg1 : ins_b_seg1_stmt.
Proof.
  unfold ins_b_seg1_stmt. intros until canary. intros ST LO LOLO SPH TP OSF PI FOK RO RO2 RV TPC SSP FRM LB DCC NPB MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS, OS + 288); (0x6ab338, 0x6ab338 + 8)]%Z m) as MU.
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
    ins_b_prologue sp ST FR LBC.
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
    eapply ins_b_t1 with (fill' := 0x20%Z); try eassumption; try reflexivity; try lia; first [exact NPB | cbn [app]; exact OSF | split; assumption | (split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]])].
  -
    assert (RF : (0 <= fill < 256)%Z) by lia.
    destruct FNE as [-> | ->];
      [ retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x20); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      | retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x30); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ];
      ins_b_prologue sp ST FR LBC;
      (lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => lit_reg (Z.lor a b) end);
      bru true;
      [ retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)]; eapply ins_b_t1 with (fill' := 0x20%Z)
      | retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x30)]; eapply ins_b_t1 with (fill' := 0x30%Z) ];
      try eassumption; try reflexivity; try lia; first [exact NPB | cbn [app]; exact OSF | split; assumption | (split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]])].
Qed.

Section Lift.
Local Open Scope Z_scope.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> ictx m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> (0 < n)%Z -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.
Hypothesis NPB : forall Σ m, ART RT Σ m -> ro_cells bsegs m 0x16cb98 [C8 (Z_to_bv 64 EL_NP_BOOL_A)].
Hypothesis AF_NP : forall Σ m, ART RT Σ m -> rod_chk m /\ rod_chk_fp m /\ ifx_real m /\ pctx m /\ pfcells6 m.

Local Ltac ul := unfold EL_INS_STACK_A, EL_NP_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *; lia.

Theorem ins_b_okA : ins_b_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC NPB AF_NP.
  unfold ins_b_cpsA, ins_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 OSW FOK HULL LB TPC SSP RV FRM ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FHI2.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO0 : 0 <= lo) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  assert (OSLO : OS + 288 <= lo) by (clear - FHI FTOP LOW; ul).
  destruct OSW as (pb & pp & ep & dum & j148 & j284 & OSF & PI).
  destruct SSP as (canary & SSP1 & SSP2). destruct HULL as [_ SHZ].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (ins_b_seg1 ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo OS fill v pp ep pb dum j148 j284 canary);
      rewrite ?EQ; first [exact ST| exact OSF| exact PI| exact FOK| exact RV| exact TPC| split; [exact SSP1| exact SSP2]| exact FRM| exact LB| exact (DCC Σ m ART0)| exact (NPB Σ m ART0)| exact MI| reflexivity| ul]. }
  cbv beta. intros ms1 PO. unfold ins1_post in PO. rewrite !EQ in PO.
  destruct PO as (fill' & x5 & x6 & x7 & x16 & x17 & x28 & x29 & x30 & x31 & x21 & j1 & m1 & FA & RF' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SB1 & V1 & IOS1 & TPC1 & SSP' & LB1).
  apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [intros Hr; apply Ha; right; right; right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]|].
    split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> (x < lo \/ q <= x) /\ ~ (OS <= x < OS + 288) /\ ~ (0x6ab338 <= x < 0x6ab340)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as (H1 & H2 & H3). cbn [outside]. split; [lia| split; [lia| split; [lia| exact I]]]. }
  assert (SHZ1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. unfold SEGTOP_A in FSEG.
    clear - Hx FLO FHI FTOP LOW SP0W F0 FSEG OSLO FHI2. unfold STACK_WIN in *. split; [| split]; Z.div_mod_to_equations; lia. }

  eapply (np_b_okA RT AF PMc FDO MST DCC (np_ul_okA RT AF RC RC2 PMc FDO MST RIP AF_IC AF_SHW DCC AF_NP) Σ K OS (q + -80) lo fO fill' v kO pb pp ep dum j148 j284);
    [exact FDO| exact MST| exact INF| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16| exact SB1| exact PI| exact V1| exact IOS1| exact SHZ1| exact RF'| exact RV
    | exact TPC1| exists canary; exact SSP'| exact FRM| exact LB1| exact ART1| exact MI1| exact ST1| exact LOW| ul| ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact FRB| exact CRB|].
  intros Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 fc2 m2 pb' pp' ep' dum' ART2 MI2 ST2 SB2 PI2 V2 IOS2 SHZ2 TPC2 LB2 FRM2 LV2 FRS2 SP2 CR2 PRES2.
  rewrite (ret_pc_even 0x111b5c) by lia.

  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> (q + -80 <= x < q) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (0x6cb3a8 <= x < 0x6cb3b0)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [H|[H|H]].
      + left. ul.
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
      + right; left. apply client_static_intro. lia.
    - pose proof (HP _ Ha) as H. clear - H OSLO LOR FSEG FLO. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, EL_INS_STACK_A, RT_STACK, SEGTOP_A in *. split; [lia| split; [lia| split; [lia| exact I]]]. }
  assert (FR2 : rw_cells bsegs m2 (q + -80) [C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (SSPm2 : ssp_cells m2 canary).
  { split; [exact (proj1 (af_got_lib RT AF Σ2 m2 ART2))|]. apply (ro_cells_agree bsegs m1 m2 _ _ (proj2 SSP')). apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    unfold ssp_guard in Hx. lia. }

  apply (aevt_evt RT AF PMc MST).
  replace (q + -80)%Z with (bv_unsigned (Z_to_bv 64 q) + -80)%Z by (rewrite EQ; reflexivity).
  eapply evt_cut.
  { eapply (ins_b_seg2 ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 lo OS fill v j148 j284 canary m2
              ltac:(rewrite EQ; ul) ltac:(ul) ltac:(rewrite EQ; ul) ltac:(reflexivity) ltac:(ul) OSLO RV FRM2 fill' pb' pp' ep' dum' j1 m2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 x21 y3 y4 y5 y6 F2 fc2);
      rewrite ?EQ; first [exact RF'| exact FA| exact PI2| apply munch_refl| apply wmono_refl| exact MI2| exact ST2| exact FR2| exact SB2| exact V2| exact IOS2| exact LB2
                          | exact TPC2| exact SSPm2| exact FRM2| intros k Hk; reflexivity| exact (DCC Σ2 m2 ART2)| exact RV| reflexivity| ul| idtac].
    all: ul. }
  cbv beta. intros ms3 PO3. unfold ins_postA in PO3. rewrite !EQ in PO3.
  destruct PO3 as (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & F3 & fc3 & pb3 & pp3 & ep3 & dum3 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FOK3 & ST3 & SSP3 & OSF3 & PI3 & TPC3 & LB3).
  apply evt_done.
  assert (ART3 : ART RT Σ2 m3).
  { apply (art_client_write RT AF Σ2 m2 m3 lo ART2 ltac:(rewrite SP2; exact LOW)); [| exact WM3]. intros a Ha. apply MU3. rewrite LV2, FRS2 in Ha. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [intros Hr; apply Ha; right; right; right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]|].
    split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (OSW3 : OSXW m3 OS 0x1002 0 (fill_after fill)) by (exists pb3, pp3, ep3, dum3, j148, j284; split; [exact OSF3| exact PI3]).
  assert (HULL3 : os_hullA m3 OS).
  { split; [pose proof OSF3 as H3; apply rw_cells_forget in H3; rewrite os_cellsX_size in H3; exact H3|].
    eapply bytes_at_agree; [exact SHZ2|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. cbn [outside].
    unfold SEGTOP_A in FSEG. clear - Hx FLO FHI FTOP LOW SP0W F0 FSEG OSLO FHI2. unfold STACK_WIN in *. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  eapply (HK Σ2 z0 z1 z2 c1 c2 c3 c4 c5 c6 c7 z3 z4 z5 z6 F3 fc3 m3 ART3 MI3 ST3 OSW3 HULL3 LB3 TPC3 FRM3 LV2 FRS2 SP2); [clear - CR2; lia|].

  intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2 & _).
  assert (OW : outside [(lo, q); (OS, OS + 288); (0x6ab338, 0x6ab338 + 8)] (bv_unsigned a)).
  { cbn [outside]. split; [| split; [exact Ho1| split; [exact Ho2| exact I]]]. intros Hr. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul. }
  rewrite (MU3 a OW). rewrite (PRES2 a); [exact (MU1 a OW)| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]|].
  cbn [outside]. split; [lia|]. split; [lia|]. split; [exact Ho2| exact I].
Qed.
End Lift.
