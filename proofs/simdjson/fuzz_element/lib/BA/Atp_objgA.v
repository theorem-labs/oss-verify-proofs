(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA Z67 Atp_objmA Atp_objsA Atp_objuA Z6i Atp_objeA Atp_objfA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjG.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.
  Variables (lg : bool) (D cap Lk sl L0 : Z) (rest : list Z) (Σ2 : rts RT).
  Hypothesis SC : sctx RT Σ Σ1 I lg D cap Lk sl L0 rest Σ2.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -288 - dd) in *.
  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.
  Local Notation SCNUM := (sc_num RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCCLS := (sc_cls RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCEL := (sc_el RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCBUD := (sc_budget RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCLONG := (sc_long RT Σ Σ1 I lg D cap Lk sl L0 rest Σ2 SC).
  Local Notation SCSHORT := (sc_short RT Σ Σ1 I lg D cap Lk sl L0 rest Σ2 SC).

  Lemma esc_unesc : forall (n : nat) (m : mem) (sz esc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (js4 jo j0 jco jt : list byte) (w24 w32 w40 w48 w88 w96 w128 : word),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz -> sz <= Lk -> 0 <= esc < sz -> sz - esc <= Z.of_nat n ->
    rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 (oi_node I)) w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz 49) (wz (shad (oi_f I))) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (oi_f I + 32)) (wz LIT_TILDE_A) (wz (oi_f I + 33)) (wz esc) x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb63c8) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    induction n as [|n IH]; intros until w128; intros OB FRM LS SZK ESC FUEL NODE LOC COUT REC SH OUT; [lia|].
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2.
    pose proof (sh_apart RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as SHAP.
    pose proof (str_apart RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as STAP.
    destruct (str_az RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m js4 ART0 SH) as [ACC SHZ].
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (FHI' : f + 120 < 2^47) by ul.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_u1 E OK _ q b f D cap sz esc (Lk + 1) lg); [exact MI| exact FLO| exact FHI'| exact LS| exact ESC| exact SHZ| lia| |].
    {
      intros cc xa2 N48 N49.
      eapply (esc_bad RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m); [exact OB0| exact FRM| exact LS| exact LOC| exact COUT| exact REC| reflexivity| exact SH| exact OUT]. }

    intros lit LIT E2.
    assert (LIT' : lit = 0x23800 \/ lit = 0x23820) by (unfold LIT_SLASH_A, LIT_TILDE_A in LIT; exact LIT).
    eapply (aevt_str_replace RT AF RC RC2 PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (f + 32) lg D cap sz esc lit (ae_lo E));
      [exact LS| exact CLD| exact CLS| exact ACC| replace (f + 32 + 24) with (f + 56) by lia; exact SEP| lia| exact E2| exact LIT'| exact ART0| exact MI| exact ST| rewrite ES2; exact LWIN| ul| ul| clear - B32; Z.div_mod_to_equations; lia|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 LS2 ACC2 ART2 MI2 ST2 WM2 AG2. rewrite (ret_pc_even 0xb6420) by lia.
    assert (DAP : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m a ART0 Hc)) Hd)).
    assert (AGB : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m2 a = m a).
    { intros a Ha N1 N2. apply AG2; [| clear - N1; lia| exact N2]. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL2| auto| lia]. }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC Σ2 Σ2 m m2 OB0 EF2 EL2 ES2 ART2 MI2 ST2 AGB DAP) as OB2.
    assert (AGS : agree_on (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ (~ (f + 24 <= x < f + 120) /\ ~ (D <= x < D + cap))) m m2).
    { intros a (Ha & N1 & N2). apply AG2; [exact Ha| clear - N1; lia| exact N2]. }
    assert (SH2 : rw_cells asegs m2 (shad f) (obj_sh 0 0 0 js4)).
    { apply (rw_cells_agree_nw asegs m m2 _ _ SH). intros a Ha. cbn [cells_size csize Nat.add length obj_sh pz] in Ha.
      destruct (SHAP (bv_unsigned a) ltac:(clear - Ha; lia)) as [N1 N2].
      apply AG2; [right; right; right; right; exists f, 1%nat; split; [exact HinF| rewrite fs1s; clear - Ha; lia]| clear - N1; lia| exact N2]. }
    clear SH. xport_stack NODE AGS. xport_stack LOC AGS. xport_stack COUT AGS. xport_stack REC AGS. xport_stack OUT AGS.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_u2 _ q b f esc); [lia| lia| exact FLO| exact FHI'|].
    eapply (aevt_str_find RT AF RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m2 b (f + 32) lg D cap (sz - 1) (esc + 1) (ae_lo E));
      [exact LS2| exact CLD| exact CLS| exact ACC2| lia| exact ART2| exact MI2| exact ST2| rewrite ES2; exact LWIN| ul| ul| clear - B32; Z.div_mod_to_equations; lia|].
    intros r t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' m3 HR LS3 ACC3 ART3 MI3 ST3 WM3 PR3. rewrite (ret_pc_even 0xb6430) by lia.
    pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ2 0 0 m2 m3 OB2 EF2 EL2 ES2 ART3 MI3 ST3 PR3 ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OB3.
    pose proof (agree_of_pres_ex _ _ _ _ _ m2 m3 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (0 <= x < 0 + 0)) PR3 (fun x H => H)) as AG3.
    xport_stack NODE AG3. xport_stack LOC AG3. xport_stack COUT AG3. xport_stack REC AG3. xport_shadow SH2 AG3 HinF. xport_stack OUT AG3.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_u3 _ q b f esc r); [clear - HR ESC SZK LKR L0R; lia| exact FLO| exact FHI'| |].
    -
      intros NR. assert (RR : esc + 1 <= r < sz - 1) by (clear - HR NR; lia).
      eapply (IH m3 (sz - 1) r); [exact OB3| exact FRM| exact LS3| lia| lia| lia| exact NODE| exact LOC| exact COUT| exact REC| exact SH2| exact OUT].
    -
      intros ->.
      eapply (esc_after RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m3); [exact OB3| exact FRM| exact LS3| lia| exact NODE| exact LOC| exact COUT| exact REC| exact SH2| exact OUT].
  Qed.

  Definition shdrX (m : mem) (sz : Z) : Prop :=
    if lg then rw_cells asegs m (oi_f I + 32) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 D)] /\ cap mod 2 = 0
    else rw_cells asegs m (oi_f I + 32) [C1 (Z_to_bv 8 (2 * sz))] /\ D = oi_f I + 32 + 1 /\ cap = 23.
  Lemma shdrX_xfer : forall (mA mB : mem) sz, shdrX mA sz -> (forall a : word, oi_f I + 32 <= bv_unsigned a < (if lg then oi_f I + 56 else oi_f I + 33) -> mB a = mA a) -> shdrX mB sz.
  Proof.
    intros mA mB sz H AG. unfold shdrX in *. destruct lg.
    - destruct H as [H EV]. split; [| exact EV]. apply (rw_cells_agree_nw asegs mA mB _ _ H). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG. lia.
    - destruct H as (H & ED & EC). split; [| split; assumption]. apply (rw_cells_agree_nw asegs mA mB _ _ H). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG. lia.
  Qed.

  Lemma esc_common : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w56 w88 w96 w104 w128 : word) (F : bvmap 5 word) (fc : bv 32) (ix : nat) (js4 jo j0 jco jt jD : list byte),
    obase RT E Σ I Σ2 m -> frm0 fc ->
    find_byte 126 (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Some ix -> shdrX m Lk ->
    rw_cells asegs m D [CB (Z.to_nat cap) jD] ->
    rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 w104 (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 (oi_node I)) w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) x20 (wz (oi_P I + 1)) (wz (oi_f I + 32)) (wz L0) (wz Lk) (wz (Z.of_nat ix)) (wz D) (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb637c) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    intros until jD. intros OB FRM FB HDRS DATA NODE LOC COUT REC SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2.
    pose proof (sc_eptr _ _ _ _ _ _ _ _ _ _ _ _ SC) as EPTR. pose proof (sc_zl0 _ _ _ _ _ _ _ _ _ _ _ _ SC) as ZL0.
    pose proof (sh_apart RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as SHAP.
    pose proof (str_apart RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as STAP.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (FHI' : f + 120 < 2^47) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ2 E LV EL2 ltac:(rewrite EF2; intros x Hx; right; exact Hx) ES2) as LV2.
    pose proof (lvl_live_ptr RT E Σ2 P ptr LV2 PAT ltac:(rewrite EPTR; discriminate)) as INPB.
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3). rewrite EPTR, zlength_cons, ZL0 in PB2.
    pose proof (find_byte_Some _ _ _ FB) as (IXL & _). rewrite length_map, firstn_length_le in IXL by (unfold zlength in ZL0; lia).
    pose proof (proj2 DATA) as WRD. cbn [cells_size csize Nat.add] in WRD. rewrite Nat.add_0_r, Z2Nat.id in WRD by lia.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p6bx E OK _ q b P L0 Lk f D); [exact MI| exact LO| lia| lia| lia| exact LOC|].
    intros m1 MU1 WM1 MI1 LOC1.
    assert (OW1 : Forall (ownW I) [(b, b + 136)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
    pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OW1) as OB1.
    pose proof OB1 as (_ & ART1 & ST1 & AI1 & _).
    mport NODE MU1 WM1. mport COUT MU1 WM1. mport REC MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1. mport DATA MU1 WM1.
    assert (HDRS1 : shdrX m1 Lk). { apply (shdrX_xfer m m1 Lk HDRS). intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. destruct lg; cbn in Ha; fold f in Ha; clear - Ha FHI LO DDR; lia. }
    clear HDRS.
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m1 ES2 ST1) as COK1. fold b in COK1.

    pose proof (ptr_atA_facts E P ptr m1 OK PAT (proj1 (proj2 (proj2 AI1)))) as (PTRB & _).
    rewrite EPTR in PTRB. pose proof (bytes_at_skipn _ _ _ 1 PTRB ltac:(cbn; lia)) as KEYB.
    change (skipn 1 (map (Z_to_bv 8) (47 :: rest))) with (map (Z_to_bv 8) rest) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat Lk) KEYB) as KEYL. rewrite firstn_map in KEYL.
    set (kb := firstn (Z.to_nat Lk) rest) in *.
    assert (LKB : length (map (Z_to_bv 8) kb) = Z.to_nat Lk) by (subst kb; rewrite length_map, firstn_length_le; [reflexivity| unfold zlength in ZL0; lia]).

    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat cap) jD [] [Z.to_nat Lk; 1; Z.to_nat (cap - Lk - 1)]%nat) in DATA; [| cbn; lia]. cbn [mk_CB_cells app] in DATA.
    lazymatch type of DATA with rw_cells _ _ _ [CB _ ?xa; CB 1 ?xb; CB _ ?xc] => set (jK := xa) in DATA; set (jn := xb) in DATA; set (j2 := xc) in DATA end. clearbody jK jn j2.
    apply (proj1 (rw_cells_app asegs m1 _ [_] _)) in DATA. destruct DATA as [DK DATA]. cbn [cells_size csize Nat.add] in DATA.
    rewrite Nat.add_0_r in DATA. replace (D + Z.of_nat (Z.to_nat Lk)) with (D + Lk) in DATA by lia.
    apply (proj1 (rw_cells_app asegs m1 _ [_] _)) in DATA. destruct DATA as [DN D2]. cbn [cells_size csize Nat.add] in D2.
    replace (D + Lk + Z.of_nat 1) with (D + Lk + 1) in D2 by lia.
    destruct (str_az RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m1 js4 ART1 SH) as [ACC1 _].
    eapply (aevt_memmoveP RT RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D (P + 1) (map (Z_to_bv 8) kb) (ae_lo E));
      [reflexivity| reflexivity| rewrite LKB, Z2Nat.id by lia; reflexivity| ul| ul| rewrite LKB; lia| exact KEYL| | | exact ART1| exact MI1| exact COK1|].
    { rewrite LKB, Z2Nat.id by lia. apply (checked_src_live RT AF Σ2 m1 _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART1 INPB); [lia| lia| rewrite ES2; exact LWIN]. }
    { rewrite LKB, Z2Nat.id by lia. split; [| split; [intros i0 Hi0; rewrite EU; apply (lstr_cls_client RT Σ2 b D cap (D + i0) CLD); lia| exact (wr_at_sub m1 D cap D Lk (wr_at_transport asegs m m1 _ _ WRD WM1) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros _. split; [apply (acc_sub asegs m1 D cap); [exact ACC1| lia| lia]| apply lstr_cls_rng; apply (lstr_cls_sub RT Σ2 D cap); [exact CLD| lia| lia]]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. rewrite LKB, Z2Nat.id in PR2 by lia. rewrite (ret_pc_even 0xb6394) by lia.
    assert (DAP1 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m1 a ART1 Hc)) Hd)).
    assert (AGB : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m2 a = m1 a).
    { intros a Ha N1 N2. apply PR2; [| clear - N2 LKC LKR; lia]. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL2| auto| lia]. }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC Σ2 Σ2 m1 m2 OB1 EF2 EL2 ES2 ART2 MI2 ST2 AGB DAP1) as OB2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (D <= x < D + Lk)) PR2 (fun x H => H)) as AGD.
    clear KEYB KEYL PTRB. xport_stack NODE AGD. xport_stack LOC1 AGD. xport_stack COUT AGD. xport_stack REC AGD. xport_stack OUT AGD.
    assert (SH2 : rw_cells asegs m2 (shad f) (obj_sh 0 0 0 js4)).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ SH). intros a Ha. cbn [cells_size csize Nat.add length obj_sh pz] in Ha.
      destruct (SHAP (bv_unsigned a) ltac:(clear - Ha; lia)) as [N1 N2].
      apply AGD. split; [right; right; right; right; exists f, 1%nat; split; [exact HinF| rewrite fs1s; clear - Ha; lia]| clear - N2 LKC; lia]. }
    clear SH.
    assert (HDRS2 : shdrX m2 Lk).
    { apply (shdrX_xfer m1 m2 Lk HDRS1). intros a Ha. apply AGD. split; [apply (lstr_cls_client RT Σ2 b _ _ _ CLS); destruct lg; cbn in Ha; fold f in Ha; clear - Ha; lia|].
      pose proof HDRS1 as HX. unfold shdrX in HX. destruct lg; cbn in Ha, HX; fold f in Ha, HX; [destruct SEP as [X|X]; [discriminate X| clear - Ha X LKR LKC; lia]| destruct HX as (_ & ED & _); clear - Ha ED LKR; lia]. }
    assert (DN2 : rw_cells asegs m2 (D + Lk) [CB 1 jn]).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ DN). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AGD. split; [apply (lstr_cls_client RT Σ2 b D cap _ CLD); lia| lia]. }
    assert (D22 : rw_cells asegs m2 (D + Lk + 1) [CB (Z.to_nat (cap - Lk - 1)) j2]).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ D2). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AGD. split; [apply (lstr_cls_client RT Σ2 b D cap _ CLD); lia| lia]. }
    clear DN D2 DK.

    destruct (str_az RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m2 js4 ART2 SH2) as [ACC2 SHZ2].
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p7 _ q b P L0 Lk f D (Z.of_nat ix) D (Lk + 1)); [exact MI2| exact D0| ul| lia| exact FLO| exact FHI'| exact SHZ2| lia| exact DN2|].
    intros m3 MU3 WM3 MI3 NUL3.
    assert (ART3 : ART RT Σ2 m3).
    { apply (art_client_write RT AF Σ2 m2 m3 (ae_lo E) ART2 ltac:(rewrite ES2; exact LWIN)); [| exact WM3].
      intros a NA. apply MU3. cbn [outside]. split; [| exact Logic.I]. intros Hin. apply NA. apply (lstr_cls_client RT Σ2 (ae_lo E) D cap _ CLD). clear - Hin LKC LKR; lia. }
    assert (ST3 : stk asegs m3 (ae_lo E) b).
    { apply (stk_transport _ _ m2 m3 (ae_lo E) b ST2 MU3 WM3). intros x Hx. left. cbn [outside]. split; [clear - Hx DLO LKC; lia| exact Logic.I]. }
    assert (DAP2 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m2 a ART2 Hc)) Hd)).
    assert (AGB3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m3 a = m2 a).
    { intros a _ _ N2. apply MU3. cbn [outside]. split; [clear - N2 LKC LKR; lia| exact Logic.I]. }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC Σ2 Σ2 m2 m3 OB2 EF2 EL2 ES2 ART3 MI3 ST3 AGB3 DAP2) as OB3.
    pose proof (sh_apartI RT E d Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC) as SHDI. fold f in SHDI.
    mport NODE MU3 WM3. mport LOC1 MU3 WM3. mport COUT MU3 WM3. mport REC MU3 WM3. mport OUT MU3 WM3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SH2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_sh pz fst snd]; clear - SHDI LKC LKR; lia)) as SH3.
    assert (HDRS3 : shdrX m3 Lk).
    { apply (shdrX_xfer m2 m3 Lk HDRS2). intros a Ha. apply MU3. cbn [outside]. split; [| exact Logic.I].
      pose proof HDRS2 as HX. unfold shdrX in HX. destruct lg; cbn in Ha, HX; fold f in Ha, HX; [destruct SEP as [X|X]; [discriminate X| clear - Ha X LKR LKC; lia]| destruct HX as (_ & ED & _); clear - Ha ED LKR; lia]. }
    assert (BY3 : bytes_at asegs m3 D (map (Z_to_bv 8) kb)).
    { apply (bytes_at_agree asegs m2 m3 _ _ BY2). intros a Ha. rewrite LKB in Ha. apply MU3. cbn [outside]. split; [lia| exact Logic.I]. }
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ D22 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)) as D23.

    assert (LS3 : lstrA m3 (f + 32) lg D cap Lk).
    { split; [lia|]. split; [exact LKC|]. split; [lia|]. split; [exact D0|]. split; [ul|]. split; [| exact HDRS3].
      exists (map (Z_to_bv 8) kb ++ [Z_to_bv 8 0] ++ j2). split; [split|].
      - apply (proj2 (bytes_at_app asegs m3 D _ _)). split; [exact BY3|]. rewrite LKB, Z2Nat.id by lia.
        apply (proj2 (bytes_at_app asegs m3 (D + Lk) _ _)). split.
        + pose proof (rw_cells_bytes_at asegs m3 _ _ NUL3) as X. cbn [cells_bytes cbytes app le1] in X. rewrite ?app_nil_r in X. exact X.
        + cbn [length Z.of_nat Pos.of_succ_nat]. pose proof (rw_cells_bytes_at asegs m3 _ _ D23) as X. cbn [cells_bytes cbytes app] in X. rewrite ?app_nil_r in X. exact X.
      - rewrite !length_app, LKB. cbn [length]. pose proof (proj1 (proj1 D23)) as WF. cbn [cells_wf cell_wf] in WF.
        replace (Z.of_nat (Z.to_nat Lk + (1 + length j2))) with cap by (destruct WF; lia).
        exact (wr_at_transport asegs m m3 _ _ WRD (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)).
      - split.
        + rewrite !length_app, LKB. cbn [length]. pose proof (proj1 (proj1 D23)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF; lia.
        + rewrite app_nth2 by (rewrite LKB; lia). rewrite LKB, Nat.sub_diag. reflexivity. }
    eapply (esc_unesc (S (Z.to_nat Lk)) m3 Lk (Z.of_nat ix)); [exact OB3| exact FRM| exact LS3| lia| lia| lia| exact NODE| exact LOC1| exact COUT| exact REC| exact SH3| exact OUT].
  Qed.

End ObjG.

Section ObjGTop.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -288 - dd) in *.

  Theorem esc_sso : esc_sso_stmt RT E d PMc Σ Σ1 I.
  Proof using AF RC2 OK HELEM FDO MST CTX.
    unfold esc_sso_stmt. intros until w128. intros OB FRM EPTR ZL0 MIN SLR LK FB NODE LOC COUT REC SH STR FR2 OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof (ptr_atA_facts E (oi_P I) (oi_ptr I) m OK PAT (proj1 (proj2 (proj2 AI)))) as (_ & _ & _ & _ & PL). rewrite EPTR, zlength_cons, ZL0 in PL.
    pose proof (zlength_nonneg rest) as ZLN. rewrite ZL0 in ZLN.
    assert (SC : sctx RT Σ Σ1 I false (oi_f I + 33) 23 Lk sl L0 rest Σ1).
    { constructor; [exact EF1| exact ES1| exact EPTR| exact ZL0| lia| exact MIN| exact SLR| lia| intros _; repeat split; lia| intros X; discriminate X]. }
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in STR. destruct STR as [HDR1 DATA]. cbn [cells_size csize Nat.add] in DATA.
    replace (oi_f I + 32 + Z.of_nat 1) with (oi_f I + 33) in DATA by lia.
    eapply (esc_common RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX false (oi_f I + 33) 23 Lk sl L0 rest Σ1 SC m);
      [exact OB0| exact FRM| exact FB| | exact DATA| exact NODE| exact LOC| exact COUT| exact REC| exact SH| exact OUT].
    unfold shdrX. cbn. split; [exact HDR1| split; [lia| reflexivity]].
  Qed.

  Theorem esc_heap : esc_heap_stmt RT E d PMc Σ Σ1 I.
  Proof using AF RC2 OK HELEM FDO MST CTX.
    unfold esc_heap_stmt. intros until w128. intros OB FRM EPTR ZL0 MIN SLR LK23 FB NODE LOC COUT REC SH STR FR2 OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof (ptr_atA_facts E (oi_P I) (oi_ptr I) m OK PAT (proj1 (proj2 (proj2 AI)))) as (_ & _ & _ & _ & PL). rewrite EPTR, zlength_cons, ZL0 in PL.
    pose proof (zlength_nonneg rest) as ZLN. rewrite ZL0 in ZLN.
    assert (ZL : oi_L I = L0 + 1) by (unfold oi_L; rewrite EPTR, zlength_cons, ZL0; lia).
    assert (LKR : 23 <= Lk <= L0) by (clear - MIN SLR ZLN LK23 PL; lia).
    pose proof (str_sz_bound Lk ltac:(lia)) as SZB. pose proof (mcost_le (str_sz Lk) ltac:(lia)) as MCL.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (HinF1 : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).

    eapply (aevt_opnew RT AF RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (str_sz Lk) (ae_lo E));
      [clear - SZB LKR PL; lia| reflexivity| rewrite EL1; clear - LVB; unfold LIVE_MAX in *; lia| rewrite EC1, ZL in *; unfold obj_costA, LVL_C1, DCOST in *; clear - CRB MCL SZB LKR; nia
      | exact ART0| exact MI| exact ST| rewrite ES1; exact LWIN| ul| ul| clear - B32; Z.div_mod_to_equations; lia|].
    intros Σ2 p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 ART2 MI2 WM2 ST2 PR2 WR2 ACC2 EL2 EF2 ES2 EC2 P0 P16 PTOP.
    rewrite (ret_pc_even 0xb6368) by lia.
    rewrite EL1 in EL2. rewrite EF1 in EF2. rewrite ES1 in ES2. rewrite EC1 in EC2.
    assert (INP : In (p, str_sz Lk) (rt_live RT Σ2)) by (rewrite EL2; left; reflexivity).
    assert (INF2 : In (f, 1%nat) (rt_frames RT Σ2)) by (rewrite EF2; left; reflexivity).
    pose proof (af_live_range RT AF Σ2 m2 p (str_sz Lk) ART2 INP) as (_ & PHI & _). rewrite ES2 in PHI.
    pose proof (af_frames_range RT AF Σ2 m2 f 1%nat ART2 INF2) as (_ & _ & _ & FD). pose proof (FD p (str_sz Lk) INP) as PSEP. rewrite fs1 in PSEP.
    pose proof (af_fshadow_apart RT AF Σ2 m2 f 1%nat ART2 INF2) as [SL _]. pose proof (SL p (str_sz Lk) INP) as DSH. rewrite fs1s in DSH.
    assert (SC : sctx RT Σ Σ1 I true p (str_sz Lk) Lk sl L0 rest Σ2).
    { constructor; [exact EF2| exact ES2| exact EPTR| exact ZL0| lia| exact MIN| exact SLR| lia| intros X; discriminate X|].
      intros _. split; [exact EL2|]. split; [reflexivity|]. split; [lia|]. split; [exact P16|]. split; [lia|]. split; [exact P0|]. split; [exact PHI|]. split; [exact PSEP| exact DSH]. }
    assert (EL2i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; right; exact Hx).
    assert (AGB : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (p <= bv_unsigned a < p + str_sz Lk) -> m2 a = m a).
    { intros a Ha _ _. apply PR2. rewrite EL1, EF1, <- EF2. exact Ha. }
    assert (DAP : forall a, p <= a < p + str_sz Lk -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a).
    { intros a Hd Hc. exact (proj2 (proj2 (str_apart RT AF E OK d Σ Σ1 I CTX true p (str_sz Lk) Lk sl L0 rest Σ2 SC m2 a ART2 Hc)) Hd). }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX true p (str_sz Lk) Lk sl L0 rest Σ2 SC Σ1 Σ2 m m2 OB0 EF2 EL2i ES2 ART2 MI2 ST2 AGB DAP) as OB2.
    assert (AGP : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (0 <= x < 0 + 0)) m m2) by (intros a [Ha _]; exact (PR2 a Ha)).
    xport_stack NODE AGP. xport_stack LOC AGP. xport_stack COUT AGP. xport_stack REC AGP. xport_shadow SH AGP HinF1. xport_frame STR AGP HinF1. xport_stack OUT AGP.
    destruct (wr_at_rw_CB m2 p (str_sz Lk) WR2 ltac:(lia)) as [jD DATA2].

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p6a E OK _ q b P L0 Lk f p (Z.of_nat ix)); [exact MI2| exact FLO| exact FHI| lia| clear - P0 PHI SP0R SZB LKR; ul| exact STR|].
    intros m3 MU3 WM3 MI3 HDR3.
    assert (OW3 : Forall (ownW I) [(f + 32, f + 56)]) by (constructor; [right; left; cbn; fold f; lia| constructor]).
    pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m2 m3 OB2 EF2 EL2i ES2 MU3 WM3 MI3 OW3) as OB3.
    mport NODE MU3 WM3. mport LOC MU3 WM3. mport COUT MU3 WM3. mport REC MU3 WM3. mport OUT MU3 WM3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ SH MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_sh pz fst snd]; clear - FSH; lia)) as SH3.
    pose proof (rw_cells_transport asegs _ m2 m3 _ _ DATA2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - PSEP SZB LKR; lia)) as DATA3.
    eapply (esc_common RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX true p (str_sz Lk) Lk sl L0 rest Σ2 SC m3);
      [exact OB3| exact FRM| exact FB| | exact DATA3| exact NODE| exact LOC| exact COUT| exact REC| exact SH3| exact OUT].
    unfold shdrX. cbn. split; [exact HDR3| exact (str_sz_evenA Lk ltac:(lia))].
  Qed.
End ObjGTop.
