(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes Cells ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Atp_objbA Atp_objgA
     Atp_objkcA Atp_objxA Atp_objcA Atp_objmA Atp_objsA Atp_objuA Atp_objeA Atp_objesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjET.
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
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.

  Lemma ctx_lpos : forall p n, In (p, n) (rt_live RT Σ) -> exists n', In (p, n') (rt_live RT Σ) /\ 0 < n'.
  Proof using CTX. exact (proj2 (oc_lvb RT E d Σ Σ1 I CTX)). Qed.

  Lemma fin_glue : fin_stmtB RT E d PMc Σ I.
  Proof using AF CTX FDO MST OK.
    unfold fin_stmtB. intros until cV. intros OB FRM EF EL ES CR LOC CS SZS CC SZC CV SZV SH OUT.
    assert (CM : rw_cells bsegs m (oi_b I + 72) (cS ++ cC ++ cV)).
    { apply (proj2 (rw_cells_app bsegs m _ cS (cC ++ cV))). split; [exact CS|]. rewrite SZS. replace (oi_b I + 72 + Z.of_nat 24) with (oi_b I + 96) by lia.
      apply (proj2 (rw_cells_app bsegs m _ cC cV)). split; [exact CC|]. rewrite SZC. replace (oi_b I + 96 + Z.of_nat 24) with (oi_b I + 120) by lia. exact CV. }
    replace (repeat (Z_to_bv 8 0) 16) with (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) in OUT by reflexivity. apply rec_node16 in OUT.
    eapply (obj_fin RT AF E OK d PMc FDO MST Σ Σ1 I CTX Σc m); [exact OB| exact FRM| exact EF| exact EL| exact ES| exact CR| exact LOC| exact CM
      | rewrite !cells_size_app, SZS, SZC, SZV; reflexivity| exact SH| exact (out_recA_err E m (oi_out I) _ 0 22 _ OUT ltac:(lia))].
  Qed.

  Lemma atkey_glue : atkey_stmtB RT E d PMc Σ I.
  Proof using AF CTX FDO MST OK RC2.
    unfold atkey_stmtB. intros until cS. intros OB FRM EF ELc ES NODE CS SZS KEY LKB LKR KP0 KPL CKP KEYCL HK.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    pose proof (a_live_mono RT Σ Σc E LV ELc ltac:(rewrite EF; intros x Hx; right; exact Hx) ES) as LVc.

    assert (OBX : forall m', ART RT Σc m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) (oi_b I) -> agree_on (PK RT Σc (oi_b I)) m m' -> obase RT E Σ I Σc m').
    { intros m' ART' MI' ST' AG'.
      assert (PRX : rt_pres_ex (rt_live RT Σc) (rt_frames RT Σc) (oi_b I) (oi_b I + 72) 24 m m').
      { intros a Ha Hn. apply AG'. unfold PK. split; [exact Ha| clear - Hn; lia]. }
      assert (NCL : forall a, oi_b I + 72 <= a < oi_b I + 72 + 24 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24).
      { intros a Ha Hc. exfalso. destruct (obj_split RT AF E d Σ Σ1 I CTX Σc m a ART0 EF ELc ES Hc); clear - H Ha R1 R2 R3 FHI FLO; lia. }
      pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σc (oi_b I) (oi_b I + 72) 24 m m' (proj1 OB0) EF ELc ES ART' MI' ltac:(clear - R2 R3; lia) PRX NCL
                    ltac:(left; lia) ltac:(right; left; clear - FHI R1 R2; lia)) as OBK'.
      exact (obase_of_K RT E Σ I Σc m' OBK' ST'). }

    destruct (rw_cells_forget _ _ _ _ CS) as [jr REC]. rewrite SZS in REC.
    apply (rw_cells_split_CB bsegs _ _ [] 24 jr [] [8; 8; 4; 4]%nat) in REC; [| cbn; lia]. cbn [mk_CB_cells app] in REC.
    lazymatch type of REC with rw_cells _ _ _ [CB _ ?a1; CB _ ?a2; CB _ ?a3; CB _ ?a4] =>
      set (oa := a1) in REC; set (ob := a2) in REC; set (oc := a3) in REC; set (od := a4) in REC end.
    clearbody oa ob oc od.
    eapply (obj_atkeyB RT AF RC2 E OK d PMc FDO MST Σc K m fc (oi_q I) (oi_b I) (oi_node I) (oi_i I) (oi_e I) (oi_c I) Kp Lk' 0xb8acc kb (oi_gp I)
              _ _ _ _ _ _ _ _ _ _ od LVc TY NXT TILES I0 EN);
      [unfold RT_STACK; clear - R1 R2; lia| clear - R3; lia| exact QN| exact NB| exact N8| exact B32| exact LKB| exact KP0| exact KPL| clear - LKR; lia| exact CKP| exact KEYCL
      | clear; lia| reflexivity| | | exact ART0| exact MI| exact ST| exact AI| exact NODE| exact REC| exact KEY].
    -
      intros m' F' it j' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AG' NODE' IS EL' IT JE REC'.
      apply (HK m' (ae_DOC E) (it + 1) 0 od y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 F' (OBX m' ART' MI' ST' AG') MI');
        [intros a Ha Hn; apply AG'; unfold PK; split; [exact Ha| exact Hn]| exact REC'| clear; lia|].
      right. split; [reflexivity|]. split; [reflexivity|]. exists j'. split; [exact EL'|]. split; [clear - IT I0; lia| clear - JE EN; lia].
    -
      intros m' F' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ART' MI' ST' AI' AG' NODE' REC'.
      replace (repeat (Z_to_bv 8 0) 16) with (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) in REC' by reflexivity. apply rec_node16 in REC'.
      apply (HK m' 0 0 20 od y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 F' (OBX m' ART' MI' ST' AG') MI');
        [intros a Ha Hn; apply AG'; unfold PK; split; [exact Ha| exact Hn]| exact REC'| clear; lia| left; reflexivity].
  Qed.

  Section SCtx.
  Variables (lg : bool) (D cap Lk sl L0 : Z) (rest : list Z) (Σ2 : rts RT).
  Hypothesis SC : sctx RT Σ Σ1 I lg D cap Lk sl L0 rest Σ2.

  Lemma tails_glue : tails_stmtB RT E d PMc Σ I Lk sl L0.
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    unfold tails_stmtB. intros until cS. intros OB FRM EF EL ES CR1 CR2 CODE HERR LOC CS SZS CHILD SV SH OUT.
    pose proof (sc_eptr _ _ _ _ _ _ _ _ _ _ _ _ SC) as EPTR. pose proof (sc_zl0 _ _ _ _ _ _ _ _ _ _ _ _ SC) as ZL0.
    pose proof (sc_slr _ _ _ _ _ _ _ _ _ _ _ _ SC) as SLR. pose proof (sc_l0 _ _ _ _ _ _ _ _ _ _ _ _ SC) as L026.
    pose proof (zlength_nonneg rest) as ZLN. rewrite ZL0 in ZLN.
    apply (proj1 (rw_cells_app bsegs m _ [_; _] _)) in SV. destruct SV as [SVK SV2]. cbn [cells_size csize Nat.add] in SV2.
    replace (oi_b I + 120 + Z.of_nat 16) with (oi_b I + 136) in SV2 by lia.
    eapply (obj_tails RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX Σc m);
      [exact OB| exact FRM| exact EF| exact EL| exact ES| exact EPTR| exact ZL0| clear - SLR ZLN L026; lia| exact CODE| |
      | exact LOC| exact CS| exact SZS| exact CHILD| exact SVK| reflexivity| exact SV2| exact SH| exact OUT].
    - intros C0. destruct HERR as [C20|(_ & RD & (j' & EL' & RI & JN))]; [exfalso; clear - C0 C20; lia|]. subst rd.
      split; [reflexivity|]. split; [exact RI|]. exists j'. split; [exact EL'| exact JN].
    - destruct (Z.eq_dec code 0) as [C0|CNZ].
      + destruct SLR as [SN|SLT].
        * left. split; [right; exact SN| exact CR1].
        * right. split; [exact C0|]. split; [exact SLT| exact (CR2 SLT)].
      + left. split; [left; exact CNZ| exact CR1].
  Qed.
  End SCtx.

  Theorem esc_ssoB : esc_sso_stmt RT E d PMc Σ Σ1 I.
  Proof using AF RC2 OK HELEM FDO MST CTX.
    unfold esc_sso_stmt. intros until w32. intros OB FRM EPTR ZL0 SLR LK FB NODE LOC REC CHILD SV SH STR FR2 OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof (ptr_atA_facts E (oi_P I) (oi_ptr I) m OK PAT (proj1 (proj2 (proj2 AI)))) as (_ & _ & _ & _ & PL). rewrite EPTR, zlength_cons, ZL0 in PL.
    pose proof (zlength_nonneg rest) as ZLN. rewrite ZL0 in ZLN.
    assert (SC : sctx RT Σ Σ1 I false (oi_f I + 33) 23 Lk sl L0 rest Σ1).
    { constructor; [exact EF1| exact ES1| exact EPTR| exact ZL0| clear - PL ZLN; lia| clear - SLR ZLN PL LK; lia| clear - SLR ZLN; lia| clear - LK; lia
        | intros _; repeat split; clear - LK; lia| intros X; discriminate X]. }
    apply (proj1 (rw_cells_app bsegs m _ [_] _)) in STR. destruct STR as [HDR1 DATA]. cbn [cells_size csize Nat.add] in DATA.
    replace (oi_f I + 32 + Z.of_nat 1) with (oi_f I + 33) in DATA by lia.
    eapply (esc_common RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX ctx_lpos atkey_glue fin_glue false (oi_f I + 33) 23 Lk sl L0 rest Σ1 SC
              (tails_glue false (oi_f I + 33) 23 Lk sl L0 rest Σ1 SC) m);
      [exact OB0| exact FRM| exact FB| | exact DATA| exact NODE| exact LOC| exact REC| reflexivity| exact CHILD| exact SV| exact SH| exact OUT].
    unfold shdrX. cbn. split; [exact HDR1| split; [lia| reflexivity]].
  Qed.

  Theorem esc_heapB : esc_heap_stmt RT E d PMc Σ Σ1 I.
  Proof using AF RC2 OK HELEM FDO MST CTX.
    unfold esc_heap_stmt. intros until w32. intros OB FRM EPTR ZL0 SLR LK23 FB NODE LOC REC CHILD SV SH STR FR2 OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof (ptr_atA_facts E (oi_P I) (oi_ptr I) m OK PAT (proj1 (proj2 (proj2 AI)))) as (_ & _ & _ & _ & PL). rewrite EPTR, zlength_cons, ZL0 in PL.
    pose proof (zlength_nonneg rest) as ZLN. rewrite ZL0 in ZLN.
    assert (ZL : oi_L I = L0 + 1) by (unfold oi_L; rewrite EPTR, zlength_cons, ZL0; lia).
    assert (LKR : 23 <= Lk <= L0) by (clear - SLR ZLN LK23 PL; lia).
    pose proof (str_sz_bound Lk ltac:(lia)) as SZB. pose proof (mcost_le (str_sz Lk) ltac:(lia)) as MCL.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1. fold q dd b in R1, R2, R3.
    assert (HinF1 : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).

    eapply (aevt_opnew RT AF RC PMc FDO MST Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (str_sz Lk) (ae_lo E));
      [clear - SZB LKR PL; lia| reflexivity| rewrite EL1; clear - LVB; unfold LIVE_MAX in *; lia| rewrite EC1, ZL in *; unfold obj_costA, LVL_C1, DCOST in *; clear - CRB MCL SZB LKR; nia
      | exact ART0| exact MI| exact ST| rewrite ES1; exact LWIN| ul| ul| clear - B32; unfold oi_b in B32; Z.div_mod_to_equations; lia|].
    intros Σ2 p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 ART2 MI2 WM2 ST2 PR2 WR2 ACC2 EL2 EF2 ES2 EC2 P0 P16 PTOP.
    rewrite (ret_pc_even 0xb8948) by lia.
    rewrite EL1 in EL2. rewrite EF1 in EF2. rewrite ES1 in ES2. rewrite EC1 in EC2.
    assert (INP : In (p, str_sz Lk) (rt_live RT Σ2)) by (rewrite EL2; left; reflexivity).
    assert (INF2 : In (f, 1%nat) (rt_frames RT Σ2)) by (rewrite EF2; left; reflexivity).
    pose proof (af_live_range RT AF Σ2 m2 p (str_sz Lk) ART2 INP) as (_ & PHI & _). rewrite ES2 in PHI.
    pose proof (af_frames_range RT AF Σ2 m2 f 1%nat ART2 INF2) as (_ & _ & _ & FD). pose proof (FD p (str_sz Lk) INP) as PSEP. rewrite fs1 in PSEP.
    pose proof (af_fshadow_apart RT AF Σ2 m2 f 1%nat ART2 INF2) as [SL _]. pose proof (SL p (str_sz Lk) INP) as DSH. rewrite fs1s in DSH.
    assert (SC : sctx RT Σ Σ1 I true p (str_sz Lk) Lk sl L0 rest Σ2).
    { constructor; [exact EF2| exact ES2| exact EPTR| exact ZL0| clear - PL ZLN; lia| clear - SLR ZLN PL LK23; lia| clear - SLR ZLN; lia| clear - LK23; lia| intros X; discriminate X|].
      intros _. split; [exact EL2|]. split; [reflexivity|]. split; [lia|]. split; [exact P16|]. split; [exact EC2|]. split; [exact P0|]. split; [exact PHI|]. split; [exact PSEP| exact DSH]. }
    assert (EL2i : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; right; exact Hx).
    assert (AGB : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ2) b (bv_unsigned a) -> ~ (f + 24 <= bv_unsigned a < f + 120) -> ~ (p <= bv_unsigned a < p + str_sz Lk) -> m2 a = m a).
    { intros a Ha _ _. apply PR2. rewrite EL1, EF1, <- EF2. exact Ha. }
    assert (DAP : forall a, p <= a < p + str_sz Lk -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a).
    { intros a Hd Hc. exact (proj2 (proj2 (str_apart RT AF E OK d Σ Σ1 I CTX true p (str_sz Lk) Lk sl L0 rest Σ2 SC m2 a ART2 Hc)) Hd). }
    pose proof (obase_agree RT AF E OK d Σ Σ1 I CTX true p (str_sz Lk) Lk sl L0 rest Σ2 SC Σ1 Σ2 m m2 OB0 EF2 EL2i ES2 ART2 MI2 ST2 AGB DAP) as OB2.
    assert (AGP : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (0 <= x < 0 + 0)) m m2) by (intros a [Ha _]; exact (PR2 a Ha)).
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH.
    xport_stack NODE AGP. xport_stack LOC AGP. xport_stack REC AGP. xport_stack CHILD AGP. xport_stack SV AGP. xport_shadow SH AGP HinF1. xport_frame STR AGP HinF1. xport_stack OUT AGP.
    destruct (wr_at_rw_CB m2 p (str_sz Lk) WR2 ltac:(lia)) as [jD DATA2].

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_p6aB E OK _ q b node L0 f (P + 1) Lk sl (Z.of_nat ix) p); [exact MI2| exact FLO| exact FHI| lia| clear - P0 PHI SP0R SZB LKR; ul| exact STR|].
    intros m3 MU3 WM3 MI3 HDR3.
    assert (OW3 : Forall (ownW I) [(f + 32, f + 56)]) by (constructor; [right; left; cbn; fold f; lia| constructor]).
    pose proof (obase_munchE RT AF E OK d Σ Σ1 I CTX true p (str_sz Lk) Lk sl L0 rest Σ2 SC Σ2 _ m2 m3 OB2 EF2 EL2i ES2 MU3 WM3 MI3 OW3
                  ltac:(constructor; [right; cbn [fst snd]; fold f; clear - FHI; lia| constructor])) as OB3.
    mport NODE MU3 WM3. mport LOC MU3 WM3. mport REC MU3 WM3. mport CHILD MU3 WM3. mport SV MU3 WM3. mport OUT MU3 WM3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SH MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_sh pz fst snd]; clear - FSH; lia)) as SH3.
    pose proof (rw_cells_transport bsegs _ m2 m3 _ _ DATA2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - PSEP SZB LKR; lia)) as DATA3.
    eapply (esc_common RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX ctx_lpos atkey_glue fin_glue true p (str_sz Lk) Lk sl L0 rest Σ2 SC
              (tails_glue true p (str_sz Lk) Lk sl L0 rest Σ2 SC) m3);
      [exact OB3| exact FRM| exact FB| | exact DATA3| exact NODE| exact LOC| exact REC| reflexivity| exact CHILD| exact SV| exact SH3| exact OUT].
    unfold shdrX. cbn. split; [exact HDR3| exact (str_sz_evenB Lk ltac:(lia))].
  Qed.
End ObjET.
