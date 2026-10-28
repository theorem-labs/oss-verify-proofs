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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_elemA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA Z67 Atp_objmA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjQ.
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
  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Hypothesis HSSO : esc_sso_stmt RT E d PMc Σ Σ1 I.
  Hypothesis HHEAP : esc_heap_stmt RT E d PMc Σ Σ1 I.

  Lemma obj_ddc : forall (m : mem) (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x15 x16 x17 x23 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (js4 jo jA jB1 jB2 jF : list byte),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells asegs m (oi_b I) [CB 112 jA; C8 (Z_to_bv 64 (oi_out I)); CB 8 jB1; C8 (Z_to_bv 64 (oi_f I)); CB 48 jB2] ->
    rw_cells asegs m (oi_f I + 24) [CB 96 jF] -> rw_cells asegs m (shad (oi_f I)) (obj_sh (-8) (-8) (-8) js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR (wz OBJ_SM1_RA) (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) (wz (oi_L I)) (wz (oi_P I)) (wz (oi_f I)) x23 (wz (oi_node I)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb5f64) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM HSSO HHEAP.
    intros until jF. intros OB FRM NODE LOC FREST SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [WF SBS P1F P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL') PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    assert (EL1i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL1; auto).
    assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (zlength_nonneg ptr) as ZLN.
    assert (CST : 1 <= obj_costA d (zlength ptr)) by (unfold obj_costA, LVL_C1, DCOST; lia).

    assert (FINW : forall mX, rw_cells asegs mX b [CB 112 jA; C8 (wz out); CB 8 jB1; C8 (wz f); CB 48 jB2] ->
      rw_cells asegs mX b [CB 112 jA; C8 (wz out); CB 8 jB1; C8 (wz f)] /\ exists c1 c2, rw_cells asegs mX (b + 136) [CB 24 c1] /\ rw_cells asegs mX (b + 160) [CB 24 c2]).
    { intros mX H. apply (proj1 (rw_cells_app asegs mX _ [_; _; _; _] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
      split; [exact H1|]. apply (rw_cells_split_CB asegs _ _ [] 48 jB2 [] [24; 24]%nat) in H2; [| reflexivity]. cbn [mk_CB_cells app] in H2.
      apply (proj1 (rw_cells_app asegs mX _ [_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add] in H3.
      do 2 eexists. split; [replace (b + 136) with (b + Z.of_nat 136) by lia; exact H2| replace (b + 160) with (b + Z.of_nat 136 + Z.of_nat 24) by lia; exact H3]. }
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p2b E OK _ q b out node P f ptr); [exact MI| exact LO| lia| lia| lia| ul| lia| exact PTRB| exact PTRF| | | | exact LOC| | | |].
    { intros NE. pose proof (lvl_ptr_range E OK P ptr PAT NE). lia. }
    { intros NE. pose proof (lvl_ptr_range E OK P ptr PAT NE). lia. }
    { intros NE. split; [exact (lvl_acc_ptr RT AF E Σ1 m P ptr ART0 LV1 PAT NE)|]. pose proof (lvl_ptr_range E OK P ptr PAT NE). lia. }
    -
      intros xa3' EP. rewrite EP in *. cbn [zlength length Z.of_nat] in *.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m ES1 ST) as COK. fold b in COK.
      pose proof (rw_cells_bytes_at asegs m _ _ NODE) as NB16. cbn [cells_bytes cbytes app] in NB16. rewrite app_nil_r in NB16.
      set (nbs := le8 (wz (ae_DOC E)) ++ le8 (wz i)) in NB16.
      assert (LNB : length nbs = 16%nat) by (subst nbs; rewrite length_app, !length_le8; reflexivity).
      eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out node nbs (ae_lo E));
        [reflexivity| reflexivity| rewrite LNB; reflexivity| ul| ul| rewrite LNB; cbn; lia| exact NB16| | | rewrite LNB; cbn; lia| exact ART0| exact MI| exact COK|].
      { rewrite LNB. apply (checked_src_stack RT AF Σ1 m _ (ae_lo E) node 16 ART0); [rewrite ES1; ul| ul| rewrite EU; lia]. }
      { rewrite LNB. apply (checked_dst_stack RT AF Σ1 m _ out 16 ART0); [rewrite ES1; ul| ul| rewrite EU; lia| exact (wr_at_sub m out 24 out 16 (proj2 OUT) ltac:(lia) ltac:(lia) ltac:(lia))]. }
      intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
      rewrite EU in ST2, PR2. rewrite LNB in PR2. change (Z.of_nat 16) with 16 in PR2. rewrite (ret_pc_even 0xb5fcc) by lia.
      pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ1 out 16 m m2 OB0 EF1 EL1i ES1 ART2 MI2 ST2 PR2 ltac:(intros a Ha _; clear - Ha; lia)
                    ltac:(right; left; clear - QO; lia) ltac:(right; left; flia)) as OB2.
      pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (out <= x < out + 16)) PR2 (fun x H => H)) as AG.
      apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
      lazymatch type of OUT with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (joA := xa) in OUT; set (joB := xb) in OUT; set (joC := xc) in OUT end. clearbody joA joB joC.
      pose proof (rec_copy16 m m2 out [CB 16 joA] (CB 4 joB) joC nbs _ _ _ OUT eq_refl eq_refl BY2 LNB WM2 PR2 ltac:(lia) ltac:(ul)) as OUT2. clear OUT NB16.
      xport_stack LOC AG. xport_shadow SH AG HinF.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_xcpy E OK _ q b out f); [exact MI2| lia| lia| exact O8| exact (lvl_shz_rec RT AF E OK Σ1 m2 out 24 ART2 LV1 ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia))| exact OUT2|].
      intros m3 xa1' MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OB2 EF1 EL1i ES1 MU3 WM3 MI3 OW3) as OB3.
      mport LOC MU3 WM3. mport SH MU3 WM3.
      destruct (FINW m3 LOC) as (LOCL & cC & cR & COUT3 & REC3).
      destruct (rw_cells_forget _ _ _ _ OUT3) as [jo' OUT3']. cbn [cells_size csize Nat.add] in OUT3'.
      eapply (obj_fin RT AF E OK d PMc FDO MST Σ Σ1 I CTX Σ1 m3); [exact OB3| exact FRM| exact EF1| exact EL1| exact ES1| rewrite EC1; unfold oi_L; fold ptr; clear - CST EP; rewrite ?EP in *; cbn [zlength length Z.of_nat] in *; lia
        | exact LOCL| reflexivity| exact COUT3| reflexivity| exact REC3| reflexivity| exact SH| exact OUT3'].
    -
      intros c0 ptr0 EP NE47.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m ES1 ST) as COK. fold b in COK.
      eapply (aevt_memsetP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out 16 (Z_to_bv 8 0) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| ul| lia| | exact ART0| exact MI| exact COK|].
      { apply (checked_dst_stack RT AF Σ1 m _ out 16 ART0); [rewrite ES1; ul| ul| rewrite EU; lia| exact (wr_at_sub m out 24 out 16 (proj2 OUT) ltac:(lia) ltac:(lia) ltac:(lia))]. }
      intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
      rewrite EU in ST2, PR2. change (Z.to_nat 16) with 16%nat in BY2. rewrite (ret_pc_even 0xb5ffc) by lia.
      pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ1 out 16 m m2 OB0 EF1 EL1i ES1 ART2 MI2 ST2 PR2 ltac:(intros a Ha _; clear - Ha; lia)
                    ltac:(right; left; clear - QO; lia) ltac:(right; left; flia)) as OB2.
      pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (out <= x < out + 16)) PR2 (fun x H => H)) as AG.
      apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
      lazymatch type of OUT with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (joA := xa) in OUT; set (joB := xb) in OUT; set (joC := xc) in OUT end. clearbody joA joB joC.
      pose proof (rec_copy16 m m2 out [CB 16 joA] (CB 4 joB) joC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT eq_refl eq_refl BY2 eq_refl WM2 PR2 ltac:(lia) ltac:(ul)) as OUT2. clear OUT.
      xport_stack LOC AG. xport_shadow SH AG HinF.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_xset E OK _ q b out f); [exact MI2| lia| lia| exact O8| exact (lvl_shz_rec RT AF E OK Σ1 m2 out 24 ART2 LV1 ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia))| exact OUT2|].
      intros m3 xa0' MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m2 m3 OB2 EF1 EL1i ES1 MU3 WM3 MI3 OW3) as OB3.
      mport LOC MU3 WM3. mport SH MU3 WM3.
      destruct (FINW m3 LOC) as (LOCL & cC & cR & COUT3 & REC3).
      destruct (rw_cells_forget _ _ _ _ OUT3) as [jo' OUT3']. cbn [cells_size csize Nat.add] in OUT3'.
      eapply (obj_fin RT AF E OK d PMc FDO MST Σ Σ1 I CTX Σ1 m3); [exact OB3| exact FRM| exact EF1| exact EL1| exact ES1| rewrite EC1; unfold oi_L; fold ptr; clear - CST; lia
        | exact LOCL| reflexivity| exact COUT3| reflexivity| exact REC3| reflexivity| exact SH| exact OUT3'].
    -
      intros m1 EP MU1 WM1 MI1 LOC1.
      assert (OW1 : Forall (ownW I) [(b, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m m1 OB0 EF1 EL1i ES1 MU1 WM1 MI1 OW1) as OB1.
      mport NODE MU1 WM1. mport FREST MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv64_eqm; reflexivity).
      eapply (obj_j94 RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX HSSO HHEAP m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc 18446744073709551615 0 0 []);
        [exact OB1| exact FRM| exact EP| reflexivity| right; lia| left; reflexivity| exact NODE| exact LOC1| exact FREST| exact SH| exact OUT].
    -
      intros m1 ptr0 EP NE0 MU1 WM1 MI1 LOC1.
      assert (OW1 : Forall (ownW I) [(b, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ1 _ m m1 OB0 EF1 EL1i ES1 MU1 WM1 MI1 OW1) as OB1.
      pose proof OB1 as (_ & ART1 & ST1 & AI1 & _).
      mport NODE MU1 WM1. mport FREST MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m1 ES1 ST1) as COK1. fold b in COK1.
      assert (NE : ptr <> []) by (rewrite EP; discriminate).
      pose proof (lvl_ptr_range E OK P ptr PAT NE) as (PB0 & PB1 & PB2 & PB3).
      pose proof (lvl_live_ptr RT E Σ1 P ptr LV1 PAT NE) as INPB.
      pose proof (ptr_atA_facts E P ptr m1 OK PAT (proj1 (proj2 (proj2 AI1)))) as (PTRB1 & _).
      rewrite EP in PTRB1, PB2, PL. rewrite zlength_cons in PB2, PL. pose proof (zlength_nonneg ptr0) as ZL0N.
      pose proof (bytes_at_skipn _ _ _ 1 PTRB1 ltac:(cbn; lia)) as KEYB.
      change (skipn 1 (map (Z_to_bv 8) (47 :: ptr0))) with (map (Z_to_bv 8) ptr0) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
      assert (PTRF0 : Forall (fun c => 0 <= c < 256) ptr0) by (rewrite EP in PTRF; inversion PTRF; assumption).
      eapply (aevt_memchrP RT RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (P + 1) 47 (zlength ptr0) (map (Z_to_bv 8) ptr0) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| ul| lia| ul| exact KEYB| apply memchr_ok_all| left; rewrite length_map; unfold zlength in *; flia| | exact ART1| exact MI1| exact COK1|].
      { pose proof (memchr_chk_le 47 (zlength ptr0) (map (Z_to_bv 8) ptr0) ltac:(lia)). pose proof (memchr_chk_nonneg 47 (zlength ptr0) (map (Z_to_bv 8) ptr0) ltac:(lia)).
        apply (checked_src_live RT AF Σ1 m1 _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART1 INPB); [lia| lia| rewrite ES1; exact LWIN]. }
      intros t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2.
      rewrite EU in ST2, PR2. rewrite (ret_pc_even 0xb5fa4) by lia.
      pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ1 0 0 m1 m2 OB1 EF1 EL1i ES1 ART2 MI2 ST2 PR2 ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OB2.
      pose proof (agree_of_pres_ex _ _ _ _ _ m1 m2 (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (0 <= x < 0 + 0)) PR2 (fun x H => H)) as AG.
      clear KEYB PTRB1. xport_stack NODE AG. xport_stack LOC1 AG. xport_frame FREST AG HinF. xport_shadow SH AG HinF. xport_stack OUT AG.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_p3a _ b P _ ptr0); [exact MI2| exact PTRF0| lia| ul| reflexivity| |].
      + intros ya1 ix IX1 IXC IXN.
        eapply (obj_j94 RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX HSSO HHEAP m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc (Z.of_nat ix) (Z.of_nat ix) (zlength ptr0) ptr0);
          [exact OB2| exact FRM| exact EP| reflexivity| left; unfold zlength; split; [lia| reflexivity]| right; unfold zlength; lia| exact NODE| exact LOC1| exact FREST| exact SH| exact OUT].
      + intros ya1 IXN.
        eapply (obj_j94 RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX HSSO HHEAP m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc 18446744073709551615 (zlength ptr0) (zlength ptr0) ptr0);
          [exact OB2| exact FRM| exact EP| reflexivity| right; split; [ul| reflexivity]| left; reflexivity| exact NODE| exact LOC1| exact FREST| exact SH| exact OUT].
  Qed.
End ObjQ.
