(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memcmp Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Printf_lib Printf_mlib F_printf_iface El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_os_defs El_ins_iface El_os_xsputn El_os_pad El_os_put El_np_wgi El_np_wgf El_np_dbl El_os_ins.
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
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.
Ltac lit_reg e := let v := eval vm_compute in e in replace e with v by (vm_compute; reflexivity).

Definition ins_d_stmt_if (P : word -> Prop) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill pp ep : Z) (dw pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - INSD_DEPTH)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xef558 + 48) ->
  rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  reg_get F (Z_to_bv 5 10) = dw -> P dw ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (ins_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS 0x1002 (fill_after fill) j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_INS_D) fc None m (seg_rom usegs)).

Lemma ins_d_of_if : ins_d_stmt_if (fun _ => True) -> ins_d_stmt.
Proof. intros H. unfold ins_d_stmt. intros. eapply H; eauto. Qed.

Section InsD.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS fill : Z) (dw : word) (j148 j284 : list byte) (canary : word) (m0 : word -> option byte).
Variable P : word -> Prop.
Hypothesis NPD : np_d_stmt_if P.
Hypothesis PDW : P dw.
Hypothesis LO : (lo <= bv_unsigned sp - INSD_DEPTH)%Z.
Hypothesis LOLO : (0x111000 <= lo)%Z.
Hypothesis SPH : (bv_unsigned sp < 2^62)%Z.
Hypothesis TP : tp = Z_to_bv 64 (0xef558 + 48).
Hypothesis RO : (bv_unsigned sp <= OS)%Z.
Hypothesis RO2 : (OS + 288 < 2^62)%Z.
Hypothesis AL8 : (OS mod 8 = 0)%Z.
Hypothesis FRM : frm0 fc.

Notation POST := (ins_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS 0x1002 (fill_after fill) j148 j284 canary m0).
Notation WI := [(lo, bv_unsigned sp); (OS, OS + 288); (0xef558, 0xef558 + 8)]%Z.

Lemma ins_d_tail : forall (fill' : Z) (pb : word) (pp ep : Z) (dum j1 : list byte) (m : word -> option byte)
    (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : list byte)
    (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fs0v : word),
  (0 <= fill' < 256)%Z -> fill_after fill = fill' -> PUTINV OS pp ep ->
  reg_get Fc (Z_to_bv 5 8) = dw -> (forall k : reg, bv_unsigned k <> 8%Z -> reg_get Fc k = reg_get F k) -> fs0v = reg_get F (Z_to_bv 5 8) ->
  munch WI m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp + -80) ->
  rw_cells usegs m (bv_unsigned sp + -80)
    [C1 (Z_to_bv 8 1); CB 7 j1; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 fs0v; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m OS
    ([C8 (Z_to_bv 64 0xd6878); C8 (Z_to_bv 64 0xee3c8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep); CB 64 dum] ++ [C8 (Z_to_bv 64 0xd6900)] ++
     [C8 (Z_to_bv 64 0xd6928); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148; C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 OS); C8 (Z_to_bv 64 0xee3c8);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fill'); CB 4 j284]) ->
  rw_cells usegs m 0xeddc8 (locb_cells l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> el_dcc m ->
  evt usegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 EL_NPUT_F) a0 a1 (Z_to_bv 64 (OS + 136)) a3 a4 a5 a6 a7
             (Z_to_bv 64 OS) (Z_to_bv 64 fill') x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x830fc) fc None m (seg_rom usegs)).
Proof using NPD PDW LO LOLO SPH TP RO RO2 AL8 FRM.
  intros until fs0v. intros RF' FA PI FC8 FCO FS MU WM MI ST FR OSF LBC TPC SSP DCC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  cbn [app] in OSF. unfold locb_cells in LBC.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & NPT & NPV & GNP & GCT).
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  do 6 lstep.
  replace (Z.land fill' 255)%Z with fill'%Z
    by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  lstep.
  takeZ OSF 9%nat (OS + 128)%Z SBF. takeZ OSF 1%nat (OS + 136)%Z V2.
  retype_at OSF 1%nat 1%nat [C4 (Z_to_bv 64 0x1002)].
  call_sp (NPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo OS fill' pp ep dw);
    [ exact ST | lia | lia | lia | exact TP | exact SBF | exact PI | exact OSF | lia | lia | exact AL8 | lia
    | etransitivity; [apply freg_get_same; reflexivity | exact FC8] | exact PDW | exact TPC
    | split; [exact SSP1 | exact SSP2] | exact FRM | do 15 eexists; exact LBC | exact DCC' | assumption | ].
  rename PC into FRM'. rename PC0 into FOK. rename PC1 into ST. rename PC2 into SSP'. rename PC3 into SBF. rename PC4 into PI'.
  rename PC5 into IOS. rename PC6 into TPC'. rename POST into LB.
  clear SSP1 SSP2. destruct SSP' as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  destruct LB as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC'). unfold locb_cells in LBC'.
  unfold sb_cells in SBF. unfold ios_cellsX in IOS.
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
  unfold ins_post, os_cellsX, sb_cells, ios_cellsX. sys_finish; [ | split; [exact SSP1 | exact SSP2] | cbn [app]; exact OSF | exact PI' | do 15 eexists; exact LBC'].

  intros k Hk. subst fs0v. destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|N8].
  + replace k with (Z_to_bv 5 8 : reg) by (apply bv_eq; rewrite E8; reflexivity). apply freg_get_same. reflexivity.
  + rewrite freg_get_other; [| apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact N8].
    rewrite (FOK k Hk). rewrite freg_get_other; [| apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact Hk].
    apply FCO. exact N8.
Qed.
End InsD.

Ltac ins_d_prologue sp ST FR LBC :=
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
  clear ST; match goal with H : stk _ _ _ _ |- _ => rename H into ST end; match goal with H : LOCB _ |- _ => clear H end;
  glueZ LTMP FR; glueZ F0 LTMP; rename F0 into FR;
  do 3 lstep;
  do 4 lstep; if_true; lstep;
  do 16 lstep.

Theorem ins_d_of_np : forall P : word -> Prop, np_d_stmt_if P -> ins_d_stmt_if P.
Proof.
  intros P NPD. unfold ins_d_stmt_if. intros until canary. intros ST LO LOLO SPH TP OSF PI FOK RO RO2 AL8 HDW PDW TPC SSP FRM LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS, OS + 288); (0xef558, 0xef558 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  unfold os_cellsX, sb_cells, ios_cellsX in OSF. cbn [app] in OSF.
  retype_at OSF 11%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  carve_frame 80%nat ST.
  destruct FOK as [-> | FNE].
  -
    retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255); C1 (Z_to_bv 8 255)].
    ins_d_prologue sp ST FR LBC.
    if_false.
    do 4 lstep.
    carve_frame 16%nat ST.
    do 9 lstep. if_true. do 4 lstep.
    release_frame FR0 ST (bv_unsigned sp + -80)%Z.
    do 3 lstep.
    lstep.
    takeZ FR 3%nat (bv_unsigned sp + -64)%Z F0. takeZ FR 1%nat (bv_unsigned sp + -56)%Z LTMP.
    call_sp (use_facet_ctype_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64)%Z);
      [exact ST | lia | lia | (do 15 eexists; exact LBC) | exact LTMP | lia | assumption |].
    rename PC into ST. clear POST.
    glueZ LTMP FR. glueZ F0 LTMP. rename F0 into FR.
    do 4 lstep.
    do 2 lstep.
    do 3 lstep.
    do 4 lstep. if_true. lstep.
    do 5 lstep.
    retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)].
    eapply ins_d_tail with (fill' := 0x20%Z) (P := P); try eassumption; try reflexivity; try lia.
    all: first [ cbn [app]; eassumption | exact (conj SSP1 SSP2) | exact (conj VT (conj WS (conj NPT (conj NPV (conj GNP GCT))))) | etransitivity; [apply freg_get_same; reflexivity | exact HDW] | intros k Hk; apply freg_get_other; apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact Hk ].
  -
    assert (RF : (0 <= fill < 256)%Z) by lia.
    destruct FNE as [-> | ->];
      [ retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x20); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      | retype_at OSF 30%nat 1%nat [C1 (Z_to_bv 8 0x30); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ];
      ins_d_prologue sp ST FR LBC;
      (lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => lit_reg (Z.lor a b) end);
      bru true;
      [ retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x20)]; eapply ins_d_tail with (fill' := 0x20%Z) (P := P)
      | retype_at OSF 30%nat 4%nat [C4 (Z_to_bv 64 0x30)]; eapply ins_d_tail with (fill' := 0x30%Z) (P := P) ];
      try eassumption; try reflexivity; try lia.
    all: first [ cbn [app]; eassumption | exact (conj SSP1 SSP2) | exact (conj VT (conj WS (conj NPT (conj NPV (conj GNP GCT))))) | etransitivity; [apply freg_get_same; reflexivity | exact HDW] | intros k Hk; apply freg_get_other; apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact Hk ].
Qed.

Theorem ins_d_proof : ins_d_stmt.
Proof. exact (ins_d_of_if (ins_d_of_np _ np_d_proof)). Qed.
