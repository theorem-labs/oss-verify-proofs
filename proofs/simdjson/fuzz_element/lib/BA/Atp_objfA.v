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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA Z67 Atp_objsA Atp_objuA Z6i Atp_objeA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma sso_az : forall (m : mem) f js4, f mod 64 = 0 -> 0 <= f -> rw_cells asegs m (shad f) (obj_sh 0 0 0 js4) -> acc asegs m (f + 32) 24 /\ shz m (f + 32) 24.
Proof.
  intros m f js4 F64 F0 SH.
  pose proof (rw_cells_bytes_at asegs m _ _ SH) as B. unfold obj_sh, pz in B. cbn [cells_bytes cbytes app] in B.
  assert (B3 : bytes_at asegs m (shad (f + 32)) (repeat z8 3)).
  { assert (ES : shad (f + 32) = shad f + Z.of_nat 4) by (unfold shad; replace (f + 32) with (f + 4 * 8) by lia; rewrite Z.div_add by lia; lia). rewrite ES.
    pose proof (bytes_at_firstn _ _ _ 3 (bytes_at_skipn _ _ _ 4 B ltac:(cbn; lia))) as X. cbn [firstn skipn le1] in X.
    rewrite (a_u64_small 0) in X by lia. exact X. }
  assert (A8 : (f + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  split; [exact (acc_zero_run asegs m (f + 32) 3 A8 ltac:(lia) B3)|].
  pose proof (shz_of_zero_run m (f + 32) 3 A8 ltac:(lia) B3) as S. exact S.
Qed.

Section ObjF.
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

  Lemma str_az : forall (m : mem) js4, ART RT Σ2 m -> rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> acc asegs m D cap /\ shz m D (Lk + 1).
  Proof using SC CTX AF OK.
    intros m js4 ART2 SH. pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 F64 _ _ _ _ _ _].
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    destruct lg eqn:LG.
    - destruct (sc_long _ _ _ _ _ _ _ _ _ _ _ _ SC eq_refl) as (EL & ECAP & LK23 & D16 & _).
      split; [exact (proj2 (af_acc_live RT AF Σ2 m D cap ART2 (IND eq_refl)))|].
      pose proof (shz_live RT AF Σ2 m D cap ART2 (IND eq_refl) ltac:(clear - D16; Z.div_mod_to_equations; lia)) as X.
      apply (shz_sub m D (8 * (cap / 8))); [exact X| lia|].
      rewrite ECAP. unfold str_sz. destruct (Z.eqb_spec Lk 23) as [->|NE]; [cbn; lia|]. rewrite (lor7_eqA Lk) by lia.
      clear - NE LKR. Z.div_mod_to_equations. lia.
    - destruct (sc_short _ _ _ _ _ _ _ _ _ _ _ _ SC eq_refl) as (ED & ECAP & LK23 & _).
      destruct (sso_az m (oi_f I) js4 F64 ltac:(lia) SH) as [A S]. rewrite ED, ECAP.
      split; [apply (acc_sub asegs m (oi_f I + 32) 24); [exact A| lia| lia]| apply (shz_sub m (oi_f I + 32) 24); [exact S| lia| lia]].
  Qed.

  Lemma esc_loop2 : forall (n : nat) (it c' : Z) (m : mem) (x1 x5 x10 x11 x12 x13 x14 x15 x16 x20 x21 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sz : Z) (js4 jo j0 jco jt : list byte) (w120 w128 : word),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz -> sz <= Lk ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it (oi_e I) c' -> it <> oi_e I -> 0 <= it -> oi_e I - it <= Z.of_nat n ->
    rw_cells asegs m (oi_b I) (obj_loc2 E j0 (if lg then 1 else 0) L0 (oi_f I) (oi_P I) (Z_to_bv 64 sl) (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 (wz (ae_TAPE E))
               (wz it) (wz (shad (oi_f I))) x20 x21 (wz (oi_f I + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz (oi_e I)) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
          F (wz 0xb65f4) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    induction n as [|n IH]; intros until w128; intros OB FRM LS SZK TI NE IT0 FUEL LOC COUT REC SH OUT.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [WF SBS P1F P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL') PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (a_live_mono RT Σ Σ2 E LV EL2 ltac:(rewrite EF2; intros x Hx; right; exact Hx) ES2) as LV2.
    assert (INS : In (ae_SBUF E, ae_NS E) (rt_live RT Σ2)) by (apply EL2; exact LVS).
    assert (LGV : 0 <= (if lg then 1 else 0) <= 1) by (destruct lg; lia).
    pose proof LS as (SZ0 & SZC & _ & _ & DC & _ & _).
    destruct (object_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE IT0 ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').

    assert (ADV : forall (m2 : mem) (FF : bvmap 5 word) (y1 y5 y10 y11 y12 y13 y14 y15 y16 y21 y29 y30 y31 : word) (w120' : word),
      obase RT E Σ I Σ2 m2 -> lstrA m2 (f + 32) lg D cap sz ->
      rw_cells asegs m2 b (obj_loc2 E j0 (if lg then 1 else 0) L0 f P (wz sl) (wz out) w120' w128) ->
      rw_cells asegs m2 (b + 136) [CB 24 jco] -> rw_cells asegs m2 (b + 160) [C8 (wz 0); C8 (wz 0); C4 (wz 12); CB 4 jt] ->
      rw_cells asegs m2 (shad f) (obj_sh 0 0 0 js4) -> rw_cells asegs m2 out [CB 24 jo] ->
      aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
        (MS (mkR y1 (wz b) gp (wz TPV) y5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) y10 y11 y12 y13 y14 y15 y16 (wz (ae_TAPE E))
                 (wz it) (wz (shad f)) (wz (8 * it)) y21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) y29 y30 y31)
            FF (wz 0xb66b4) fc None m2 (seg_rom asegs))).
    { intros m2 FF y1 y5 y10 y11 y12 y13 y14 y15 y16 y21 y29 y30 y31 w120' OB2 LS2 LOC2 COUT2 REC2 SH2 OUT2.
      pose proof OB2 as (MI2 & ART2 & ST2 & AI2 & _).
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_l2adv E OK d _ q b P L0 (if lg then 1 else 0) f D sz e it j'); [exact MI2| exact LO| lia| lia| lia| exact LGV| exact AI2| exact (lvl_shz_tape RT AF E OK Σ2 m2 ART2 LV2)| exact EL| flia| flia| flia| exact EN| exact LOC2| |].
      - intros xa0 xa1 xa2 NE'.
        eapply (IH j' (c' - 1) m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF); [exact OB2| exact FRM| exact LS2| exact SZK| exact TI'| exact NE'| flia| flia| exact LOC2| exact COUT2| exact REC2| exact SH2| exact OUT2].
      - intros xa2 ->.
        eapply (esc_rec RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m2); [exact OB2| exact FRM| exact LS2| left; reflexivity| flia| flia| | exact COUT2| exact REC2| exact SH2| exact OUT2].
        unfold obj_loc2 in LOC2. exact LOC2. }

    assert (RET : forall (m2 : mem) (FF : bvmap 5 word) (r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      obase RT E Σ I Σ2 m2 -> lstrA m2 (f + 32) lg D cap sz ->
      rw_cells asegs m2 b (obj_loc2 E j0 (if lg then 1 else 0) L0 f P (wz sl) (wz out) (wz it) w128) ->
      rw_cells asegs m2 (b + 136) [CB 24 jco] -> rw_cells asegs m2 (b + 160) [C8 (wz 0); C8 (wz 0); C4 (wz 12); CB 4 jt] ->
      rw_cells asegs m2 (shad f) (obj_sh 0 0 0 js4) -> rw_cells asegs m2 out [CB 24 jo] ->
      aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
        (MS (mkR (wz 0xb6690) (wz b) gp (wz TPV) y5 y6 y7 (wz q) (wz b) r y11 y12 y13 y14 y15 y16 y17
                 (wz D) (wz (shad f)) (wz (8 * it)) (wz (ae_TAPE E)) (wz 2147450880) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz e) (wz sz) (wz 72057594037927935) y28 y29 y30 y31)
            FF (wz 0xb6690) fc None m2 (seg_rom asegs))).
    { intros m2 FF r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 OB2 LS2 LOC2 COUT2 REC2 SH2 OUT2.
      pose proof OB2 as (MI2 & _).
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_l2ret E OK _ q b P L0 (if lg then 1 else 0) f D sz e it r); [exact MI2| exact LO| flia| flia| flia| ul| exact LGV| exact LOC2| |].
      - intros _. eapply (esc_rec RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m2); [exact OB2| exact FRM| exact LS2| | ul| flia| | exact COUT2| exact REC2| exact SH2| exact OUT2].
        + right. split; [reflexivity|]. split; [reflexivity|]. exists j'. split; [exact EL|]. split; [flia| flia].
        + unfold obj_loc2 in LOC2. exact LOC2.
      - intros _. eapply ADV; [exact OB2| exact LS2| exact LOC2| exact COUT2| exact REC2| exact SH2| exact OUT2]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_l2body E OK _ q b P L0 (if lg then 1 else 0) f D sz e it); [exact MI| exact LO| flia| flia| flia| ul| lia| ul| exact AI| exact (lvl_shz_tape RT AF E OK Σ2 m ART0 LV2)| | exact STR| flia| flia| exact EN| exact LOC| |].
    { pose proof (shz_live RT AF Σ2 m _ _ ART0 INS ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
      replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X. }
    2:{ intros l xa1 xa2 xa3 xa4 SA NEQ. eapply ADV; [exact OB0| exact LS| exact LOC| exact COUT| exact REC| exact SH| exact OUT]. }
    intros m1 l xa3 xa4 SA ELK MU1 WM1 MI1 LOC1. unfold obj_loc2 in LOC1.
    assert (OW1 : Forall (ownW I) [(b, b + 136)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
    pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OW1) as OB1.
    pose proof OB1 as (_ & ART1 & ST1 & AI1 & _).
    mport COUT MU1 WM1. mport REC MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
    assert (LS1 : lstrA m1 (f + 32) lg D cap sz).
    { apply (lstrA_agree m m1 _ _ _ _ _ LS). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. clear - Hx DLO FHI LO DDR SEP CAPR. lia. }
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0b & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m1 ES2 ST1) as COK. fold b in COK.
    destruct (Z.eq_dec sz 0) as [S0Z|SZP].
    -
      rewrite S0Z.
      eapply (aevt_memcmp0 RT PMc FDO MST RC2 Σ2); [reflexivity| exact ART1| exact MI1| exact COK|].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (ART' & MI' & WM' & ST') PR'.
      rewrite EU in ST', PR'. rewrite (ret_pc_even 0xb6690) by lia.
      pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ2 0 0 m1 m' OB1 EF2 EL2 ES2 ART' MI' ST' PR' ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBm.
      pose proof (agree_of_pres_ex _ _ _ _ _ m1 m' (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (0 <= x < 0 + 0)) PR' (fun x H => H)) as AG.
      assert (LS' : lstrA m' (f + 32) lg D cap sz).
      { apply (lstrA_agree m1 m' _ _ _ _ _ LS1). intros a Ha. apply AG. split; [| lia].
        destruct Ha as [Ha|Ha]; [exact (lstr_cls_client RT Σ2 b _ _ _ CLS Ha)| exact (lstr_cls_client RT Σ2 b _ _ _ CLD Ha)]. }
      xport_stack LOC1 AG. xport_stack COUT AG. xport_stack REC AG. xport_shadow SH AG HinF. xport_stack OUT AG.
      rewrite <- S0Z. eapply RET; [exact OBm| exact LS'| exact LOC1| exact COUT| exact REC| exact SH| exact OUT].
    -
      pose proof LS1 as (_ & _ & _ & _ & _ & (bs & BS & LBS & NUL) & _).
      pose proof (bytes_at_firstn _ _ _ (Z.to_nat sz) (proj1 BS)) as KEYL.
      assert (LKB : length (firstn (Z.to_nat sz) bs) = Z.to_nat sz) by (rewrite firstn_length_le; [reflexivity| lia]).
      destruct (sbuf_bytesA_at E m1 o sz (proj1 (proj2 AI1)) ltac:(flia) ltac:(flia) ltac:(flia)) as [QB QL].
      destruct (str_az m1 js4 ART1 SH) as [ACC1 _].
      eapply (aevt_memcmpW RT PMc FDO MST RC2 Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D (ae_SBUF E + o + 4) (firstn (Z.to_nat sz) bs) (sbuf_bytesA E o sz) (ae_lo E));
        [reflexivity| reflexivity| rewrite LKB; f_equal; flia| rewrite QL, LKB; reflexivity| ul| ul| rewrite LKB; flia| rewrite LKB; ul| exact KEYL| exact QB| | | exact ART1| exact MI1| exact COK|].
      { rewrite LKB, Z2Nat.id by lia. split; [| left; clear - DLO SZK LKC; lia]. intros _.
        split; [apply (acc_sub asegs m1 D cap); [exact ACC1| lia| lia]| apply lstr_cls_rng; apply (lstr_cls_sub RT Σ2 D cap); [exact CLD| lia| lia]]. }
      { rewrite LKB. apply (checked_src_live RT AF Σ2 m1 _ (ae_lo E) (ae_SBUF E) (ae_NS E) _ _ ART1 INS); [flia| flia| rewrite ES2; exact LWIN]. }
      intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' HR (ART' & MI' & WM' & ST') PR'.
      rewrite EU in ST', PR'. rewrite (ret_pc_even 0xb6690) by lia.
      pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ2 0 0 m1 m' OB1 EF2 EL2 ES2 ART' MI' ST' PR' ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBm.
      pose proof (agree_of_pres_ex _ _ _ _ _ m1 m' (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (0 <= x < 0 + 0)) PR' (fun x H => H)) as AG.
      assert (LS' : lstrA m' (f + 32) lg D cap sz).
      { apply (lstrA_agree m1 m' _ _ _ _ _ LS1). intros a Ha. apply AG. split; [| lia].
        destruct Ha as [Ha|Ha]; [exact (lstr_cls_client RT Σ2 b _ _ _ CLS Ha)| exact (lstr_cls_client RT Σ2 b _ _ _ CLD Ha)]. }
      clear KEYL QB BS. xport_stack LOC1 AG. xport_stack COUT AG. xport_stack REC AG. xport_shadow SH AG HinF. xport_stack OUT AG.
      eapply RET; [exact OBm| exact LS'| exact LOC1| exact COUT| exact REC| exact SH| exact OUT].
  Qed.

  Lemma esc_after : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w88 w96 w128 : word) (F : bvmap 5 word) (fc : bv 32) (sz : Z) (js4 jo j0 jco jt : list byte),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz -> sz <= Lk ->
    rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 (oi_node I)) w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz 49) (wz (shad (oi_f I))) x20 (wz LIT_SLASH_A) (wz (oi_f I + 32)) (wz LIT_TILDE_A) (wz (oi_f I + 33)) (wz 18446744073709551615) x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb6448) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    intros until jt. intros OB FRM LS SZK NODE LOC COUT REC SH OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof SCNUM as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof SCCLS as (CLD & CLS & IND & HinF).
    pose proof (sc_ef _ _ _ _ _ _ _ _ _ _ _ _ SC) as EF2. pose proof (sc_es _ _ _ _ _ _ _ _ _ _ _ _ SC) as ES2. pose proof SCEL as EL2.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (LO : ae_lo E + 304 <= q) by ul.
    pose proof (a_live_mono RT Σ Σ2 E LV EL2 ltac:(rewrite EF2; intros x Hx; right; exact Hx) ES2) as LV2.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    assert (OWL : Forall (ownW I) [(b, b + 136)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
    assert (FPb : fp_ok RT Σ2 (ae_lo E) [(b, b + 136)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
    assert (ARTm : forall m', munch [(b, b + 136)] m m' -> wmono asegs m m' -> ART RT Σ2 m').
    { intros m' MU WM. exact (art_of_munch RT AF Σ2 m m' (ae_lo E) _ ART0 ltac:(rewrite ES2; exact LWIN) FPb MU WM). }
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_v1 E OK _ q b P L0 f D cap sz i e node lg); [exact MI| exact LO| lia| lia| lia| exact FLO| exact FHI| exact LS| exact AI| exact NODE| exact QN| exact NB| exact TY| exact NXT| exact I0| exact EN| exact IE| exact LOC| | | | |].
    - intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ2 m' node 16 (ARTm m' MU WM) LV2); [lia| lia| exact N8| reflexivity| lia].
    - intros m' MU WM. apply (lvl_shz_doc E OK). apply (AINV_A_munch E _ m m' OK AI MU). constructor; [cbn; lia| constructor].
    - intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ2 m' (ARTm m' MU WM) LV2).
    -
      intros xa2 xa3 Ee.
      eapply (esc_rec RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX lg D cap Lk sl L0 rest Σ2 SC m); [exact OB0| exact FRM| exact LS| left; reflexivity| flia| flia| exact LOC| exact COUT| exact REC| exact SH| exact OUT].
    -
      intros m1 xa0 xa1 xa2 xa3 NE1 MU1 WM1 MI1 LOC1.
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OWL) as OB1.
      mport COUT MU1 WM1. mport REC MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      assert (LS1 : lstrA m1 (f + 32) lg D cap sz).
      { apply (lstrA_agree m m1 _ _ _ _ _ LS). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. clear - Hx DLO FHI LO DDR SEP CAPR. lia. }
      eapply (esc_loop2 (S (Z.to_nat (e - (i + 1)))) (i + 1) c m1); [exact OB1| exact FRM| exact LS1| exact SZK| exact TILES| exact NE1| lia| lia| | exact COUT| exact REC| exact SH| exact OUT].
      unfold obj_loc2. exact LOC1.
  Qed.

End ObjF.
