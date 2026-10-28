From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5 El_callsA El_sncA Atp_kitA Atp_objkA El_atkmdA El_atkceA El_atkclA El_atkcwA.
Import ListNotations.
Open Scope Z_scope.

Section AtkcSnc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable E : aenvA.
Hypothesis OK : aenvA_ok E.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis SNCW : sncW_stmt RT.
Hypothesis SNC0 : snc0_stmt RT.

Lemma atkc_snc_call : forall (Σ : rts RT) (K : config -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (sp o P L : Z) (key : list Z)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  a_live RT Σ E -> AINV_A E m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m (ae_lo E) sp -> ae_lo E + RT_STACK <= sp -> sp + 16 <= USTACK_TOP -> sp mod 16 = 0 ->
  ptr_atA E P key -> L = zlength key -> 0 <= o -> o + 4 + L < ae_sn E ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ sp (ae_lo E) m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 L)
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_strncasecmp) fc None m (seg_rom asegs)).
Proof using AF OK FDO MST SNCW SNC0.
  intros Σ K m F fc sp o P L key ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    LV AI ART0 MI0 ST SPL SPT SPA PAT EL O0 OL HK.
  pose proof (ok_lo E OK) as LOW. pose proof (ok_hi E OK) as [HL HT].
  pose proof (ok_sbuf E OK) as (SB16 & NS8 & SN & SS & SL).
  pose proof (call_ok_lvl RT E OK Σ m sp LV ST SPL SPT SPA) as COK.
  assert (SPU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK in *; lia).
  assert (HK' : forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned (Z_to_bv 64 sp)) (ae_lo E) m m' ->
     rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 sp)) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))).
  { intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR. rewrite SPU in RA, PR.
    exact (HK r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR). }
  pose proof (zlength_nonneg key) as KL0.
  destruct (Z.eq_dec L 0) as [L0|LP].
  - eapply (aevt_snc0 RT PMc FDO MST SNC0 Σ); [rewrite L0; reflexivity| exact ART0| exact MI0| exact COK| exact HK'].
  - assert (LPOS : 0 < L) by lia.
    assert (NE : key <> []) by (intros E0; rewrite E0 in EL; unfold zlength in EL; cbn [length] in EL; lia).
    destruct AI as (_ & SBB & PTB & _).
    pose proof (ptr_atA_facts E P key m OK PAT PTB) as (KB & KR & _ & _ & KL26).
    pose proof (lvl_ptr_range E OK P key PAT NE) as (PB0 & PB1 & PB2 & PB3).
    pose proof (lvl_live_ptr RT E Σ P key LV PAT NE) as INPB.
    pose proof LV as (_ & LVS & _ & _ & LWIN).
    assert (QB : bytes_at asegs m (ae_SBUF E + o + 4) (map (Z_to_bv 8) (firstn (Z.to_nat L) (skipn (Z.to_nat (o + 4)) (ae_sbs E))))).
    { rewrite <- firstn_map, <- skipn_map.
      replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact SBB|]. rewrite length_map. lia. }
    eapply (aevt_sncW RT PMc FDO MST SNCW Σ K ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1
              (Z_to_bv 64 P) (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 L) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m P (ae_SBUF E + o + 4) L key (firstn (Z.to_nat L) (skipn (Z.to_nat (o + 4)) (ae_sbs E))) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| unfold USTACK_TOP in *; lia| unfold USTACK_TOP in *; lia| lia
      | exact KB| exact QB| exact KR| apply Forall_firstn_skipn; exact (ok_sbs E OK)
      | unfold zlength in EL; lia| rewrite firstn_length_le; [lia| rewrite length_skipn; lia]
      | | | exact ART0| exact MI0| exact COK| exact HK'].
    + apply (checked_src_live RT AF Σ m _ (ae_lo E) (ae_PB E) (ae_NPB E) _ _ ART0 INPB); [lia| lia| exact LWIN].
    + apply (checked_src_live RT AF Σ m _ (ae_lo E) (ae_SBUF E) (ae_NS E) _ _ ART0 LVS); [lia| lia| exact LWIN].
Qed.

End AtkcSnc.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac kul := unfold EL_CALL_NEED_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Section AtKeyC.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Hypothesis SNCW : sncW_stmt RT.
Hypothesis SNC0 : snc0_stmt RT.

  Definition atkc_st (E : aenvA) (Σ : rts RT) (q out RA : Z) : Prop :=
    a_live RT Σ E /\ ae_lo E + EL_CALL_NEED_A <= q /\ q mod 16 = 0 /\ q <= out /\ out + 24 <= ae_hi E /\ out mod 8 = 0 /\
    0 <= RA < 2^64.

  Definition atkc_inv (E : aenvA) (Σ : rts RT) (q out : Z) (m mx : mem) : Prop :=
    ART RT Σ mx /\ mem_inv asegs mx /\ stk asegs mx (ae_lo E) (q + -128) /\ AINV_A E mx /\
    rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m mx /\ (exists jo, rw_cells asegs mx out [CB 24 jo]).

  Definition atkc_K (E : aenvA) (Σ : rts RT) (PMc : Model -> Prop) (RA q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (out : Z) (m : mem) : config -> Prop :=
    fun c => lvl_postA RT E Σ PMc (wz RA) q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m 0 c /\ cfrm0 c.

  Lemma atkc_rec24 : forall (mx : mem) (a : Z) (c : list cell), rw_cells asegs mx a c -> cells_size c = 24%nat ->
    rw_cells asegs mx a [CB 24 (cells_bytes c)].
  Proof.
    intros mx a c H CS. pose proof H as HW. destruct HW as [[W _] _].
    eapply rw_cells_recastA; [exact H| |cbn [cells_bytes cbytes]; apply app_nil_r].
    cbn [cells_wf cell_wf]. split; [|exact I]. rewrite (cells_bytes_length c W). exact CS.
  Qed.

  Lemma atkc_rx_post : forall (E : aenvA) (Σ : rts RT) PMc (q out RA : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m mx : mem) (c : list cell) (ms : machine_state),
    aenvA_ok E -> atkc_st E Σ q out RA -> atkc_inv E Σ q out m mx -> frm0 fc -> cells_size c = 24%nat ->
    atkc_rx E q out RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mx c ms ->
    aevt RT PMc Σ (atkc_K E Σ PMc RA q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m) ms.
  Proof using AF.
    intros E Σ PMc q out RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mx c ms OK ST INV FRM CS RX.
    destruct ST as (LV & QL & Q16 & QO & OB & O8 & RA0).
    destruct INV as (ARTx & MIx & STx & AIx & PFPx & _).
    destruct RX as (m' & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & MU & WM & MI' & ST' & OUT' & ->).
    destruct (ok_hi E OK) as [HL HT]. pose proof (ok_lo E OK) as LO0.
    assert (FPW : fp_client RT Σ (ae_lo E) [(q + -128, q); (out, out + 24)]) by (apply fp_client_stack2; kul).
    pose proof (lvl_art_munch RT AF E Σ _ mx m' ARTx LV FPW MU WM) as ART'.
    assert (HWlo : Forall (fun r => ae_lo E <= fst r) [(q + -128, q); (out, out + 24)]).
    { constructor; [cbn [fst]; kul|]. constructor; [cbn [fst]; kul| constructor]. }
    pose proof (AINV_A_munch E _ mx m' OK AIx MU HWlo) as AI'.
    pose proof (rt_pres_fp_of_munch RT AF E Σ mx (q + -128) q [(out, out + 24)] mx m' ARTx LV ltac:(kul) MU) as PFP'.
    pose proof (atkc_rec24 m' out c OUT' CS) as OUT24.
    apply aevt_done. intros c0 Hc0. unfold atkc_K. split.
    2: { apply (cfrm0_of_asta RT Σ PMc _ c0 Hc0). intros ms0 <-. exact FRM. }
    eapply (lvl_postA_intro0 RT E Σ Σ PMc c0); [exact Hc0| exact ART'| exact MI'| exact ST'| | exact OUT24| exact AI'| reflexivity| reflexivity| reflexivity| lia].
    exact (rt_pres_fp_trans _ _ _ _ _ _ _ PFPx PFP').
  Qed.

  Lemma atkc_set_post : forall (E : aenvA) (Σ : rts RT) PMc (q out P RA ra' code : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m mx : mem) (j0 j1 : list byte)
      (x5 x6 x7 xs0 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 : word),
    aenvA_ok E -> fdfs_only PMc -> mat_stable PMc -> atkc_st E Σ q out RA -> atkc_inv E Σ q out m mx -> frm0 fc -> atkc_set_site ra' code ->
    rw_cells asegs mx (q + -128) ([CB 8 j0; CB 8 j1; C8 (wz P)] ++ atkm_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    (forall (m2 : mem) (F2 : bvmap 5 word) (u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (zb oc od : list byte),
       rw_cells asegs m2 (q + -128) ([CB 8 j0; CB 8 j1; C8 (wz P)] ++ atkm_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       stk asegs m2 (ae_lo E) (q + -128) -> mem_inv asegs m2 -> rw_cells asegs m2 out [CB 16 zb; CB 4 oc; CB 4 od] -> shz m2 out 24 ->
       evt asegs (atkc_rx E q out RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc m2 [CB 16 zb; C4 (wz code); CB 4 od])
         (MS (mkR (wz ra') (wz (q + -128)) gp (wz TPV) u0 u1 u2 xs0 (wz (out + 16)) v b1 b2 b3 b4 b5 b6 b7
                  xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 u3 u4 u5 u6)
             F2 (wz ra') fc None m2 (seg_rom asegs))) ->
    aevt RT PMc Σ (atkc_K E Σ PMc RA q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m)
      (MS (mkR (wz ra') (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 (wz (out + 16)) (wz out) (wz 0) (wz 16) a3 a4 a5 a6 a7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
          F (wz e_asan_memset) fc None mx (seg_rom asegs)).
  Proof using AF RC.
    intros E Σ PMc q out P RA ra' code gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mx j0 j1
      x5 x6 x7 xs0 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 OK FDO MST ST INV FRM SITE FR RET.
    pose proof ST as ST0. destruct ST as (LV & QL & Q16 & QO & OB & O8 & RA0).
    destruct INV as (ARTx & MIx & STx & AIx & PFPx & (jo & OUTx)).
    destruct (ok_hi E OK) as [HL HT]. pose proof (ok_lo E OK) as LO0.
    pose proof (af_sp0_range RT AF Σ mx ARTx) as SP0R. pose proof LV as (LT & LS & LP & LF & LWIN).
    assert (EU : bv_unsigned (wz (q + -128)) = q + -128) by (apply unsigned_lit; kul).
    assert (Q16' : (q + -128) mod 16 = 0) by (replace (q + -128) with (q + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (RAE : 0 <= ra' < 2^64 /\ ra' mod 2 = 0) by (destruct SITE as [(-> & _)|(-> & _)]; lia).
    assert (CDST : checked_dst RT Σ mx (wz (q + -128)) out 16).
    { apply (checked_dst_stack RT AF Σ mx _ out 16 ARTx); [kul| kul| rewrite EU; lia|].
      apply (wr_at_sub mx out 24 out 16); [| lia| lia| lia]. exact (proj2 OUTx). }
    pose proof (call_ok_lvl RT E OK Σ mx (q + -128) LV STx ltac:(kul) ltac:(kul) Q16') as COK.
    unfold aevt. intros T c Hc Hk.
    apply (rc_asan_memset RT RC Σ PMc (wz ra') (wz (q + -128)) gp (wz TPV) x5 x6 x7 xs0 (wz (out + 16))
             (wz out) (wz 0) (wz 16) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6
             F fc mx out 16 (Z_to_bv 8 0) (ae_lo E) FDO MST eq_refl eq_refl eq_refl ltac:(kul) ltac:(lia) CDST ARTx MIx COK T c).
    { unfold entry_st. exact Hc. }
    intros c4 Hc4. unfold icpt_postF in Hc4.
    destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4) & Hc4'). clear Hc4.
    destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & ->).
    rewrite EU in ST4, PRES4. change (Z.to_nat 16) with 16%nat in BY4.
    rewrite (ret_pc_even ra') in Hc4' by lia.
    assert (FR4 : rw_cells asegs m4 (q + -128) ([CB 8 j0; CB 8 j1; C8 (wz P)] ++ atkm_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree_nw asegs mx m4 _ _ FR). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4).
      intros x Hx. unfold atkm_saved in Hx. cbn [app cells_size csize Nat.add] in Hx. split; [left; kul| lia]. }
    pose proof (AINV_A_pres_ex RT Σ E _ out 16 mx m4 LV OK AIx PRES4 ltac:(kul)) as AI4.
    assert (PFP4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m4).
    { eapply rt_pres_fp_trans; [exact PFPx|].
      eapply (rt_pres_fp_of_ex _ _ (q + -128) q out 16); [exact PRES4| lia|].
      intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia. }
    apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUTx; [| reflexivity]. cbn [mk_CB_cells app] in OUTx.
    lazymatch type of OUTx with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUTx; set (jB := xb) in OUTx; set (jC := xc) in OUTx end.
    clearbody jA jB jC.
    pose proof (rec_copy16 mx m4 out [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ OUTx eq_refl eq_refl BY4 eq_refl WM4 PRES4 ltac:(lia) ltac:(kul)) as OUT4.
    pose proof (lvl_shz_rec RT AF E OK Σ m4 out 24 ART4 LV ltac:(kul) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO4.
    pose proof (RET m4 F4 w0 w1 w2 (wz out) g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 (repeat (Z_to_bv 8 0) 16) jB jC FR4 ST4 MI4 OUT4 SHZO4) as W5.
    refine (aevt_evt RT AF PMc MST Σ _ _ _ T c4 Hc4' Hk).
    eapply evt_mono; [exact W5|]. intros ms5 RX5.
    eapply (atkc_rx_post E Σ PMc q out RA); [exact OK| exact ST0| | exact FRM| | exact RX5]; [| reflexivity].
    split; [exact ART4|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact AI4|]. split; [exact PFP4|].
    exists (cells_bytes [CB 16 (repeat (Z_to_bv 8 0) 16); CB 4 jB; CB 4 jC]). exact (atkc_rec24 m4 out _ OUT4 eq_refl).
  Qed.

  Lemma atkc_nfx_post : forall (E : aenvA) (Σ : rts RT) PMc (q out P RA : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m mz : mem) (ms : machine_state),
    aenvA_ok E -> fdfs_only PMc -> mat_stable PMc -> atkc_st E Σ q out RA -> atkc_inv E Σ q out m mz -> frm0 fc ->
    rw_cells asegs mz (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    atkc_nfx q out gp F fc mz ms ->
    aevt RT PMc Σ (atkc_K E Σ PMc RA q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m) ms.
  Proof using AF RC.
    intros E Σ PMc q out P RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mz ms OK FDO MST ST INV FRM FR X4.
    pose proof ST as (LV & QL & Q16 & QO & OB & O8 & RA0).
    destruct (ok_hi E OK) as [HL HT]. pose proof (ok_lo E OK) as LO0.
    destruct X4 as (z5 & z6 & z7 & z8 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & ->).
    eapply (atkc_set_post E Σ PMc q out P RA); [exact OK| exact FDO| exact MST| exact ST| exact INV| exact FRM| right; split; reflexivity
      | exact (atkc_forget mz (q + -128) (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR)|].
    intros m2 F2 u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 zb oc od FR2 ST2 MI2 OUT2 SHZ2.
    eapply (atkc_set_ret E OK); [exact FR2| exact ST2| exact MI2| kul| exact OUT2| kul| kul| kul| exact SHZ2| kul| right; split; reflexivity].
  Qed.

  Lemma atkc_loop : forall (n : nat) (E : aenvA) (Σ : rts RT) PMc (d : nat) (key : list Z) (q out P RA it e L c : Z)
      (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m mx : mem) (ms : machine_state),
    aenvA_ok E -> fdfs_only PMc -> mat_stable PMc -> atkc_st E Σ q out RA -> atkc_inv E Σ q out m mx -> frm0 fc ->
    ptr_atA E P key -> L = zlength key -> e - it <= Z.of_nat n ->
    rw_cells asegs mx (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    is_str (ae_T E) (ae_S E) (ae_sn E) it -> 0 <= it -> it + 1 <= e -> e + 1 <= ae_n E - 1 -> 0 <= L < 2^40 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c ->
    evt asegs (atkc_headx E d q out P RA it e L c gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mx) ms ->
    aevt RT PMc Σ (atkc_K E Σ PMc RA q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m) ms.
  Proof using AF RC SNCW SNC0.
    induction n as [|n IH]; intros E Σ PMc d key q out P RA it e L c gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mx ms
      OK FDO MST ST INV FRM PAT LK MEAS FR STR IT0 ITE EN L40 TL HS; [exfalso; lia|].
    pose proof ST as ST0. destruct ST as (LV & QL & Q16 & QO & OB & O8 & RA0).
    pose proof INV as (ARTx & MIx & STx & AIx & PFPx & (jo & OUTx)).
    destruct (ok_hi E OK) as [HL HT]. pose proof (ok_lo E OK) as LO0.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ [S16 [NS8 _]] _ _ _ _ _].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    assert (Q16' : (q + -128) mod 16 = 0) by (replace (q + -128) with (q + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (ADV : forall (mz : mem) (F' : bvmap 5 word) (j' : Z) (ms2 : machine_state),
      atkc_inv E Σ q out m mz ->
      rw_cells asegs mz (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      evt asegs (atkc_advx E d q out P RA it j' e L (c - 1) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc mz) ms2 ->
      aevt RT PMc Σ (atkc_K E Σ PMc RA q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m) ms2).
    { intros mz F' j' ms2 INVz FRz HA.
      apply (aevt_evt RT AF PMc MST). eapply evt_mono; [exact HA|]. intros ms3 X3.
      destruct X3 as [(JE & x1 & x5 & x6 & x7 & xs0 & xs1 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xs2 & xs3 & xs5 & xs6 & xs7 & xs8 & xs9 & xs10 & xs11 & x28 & x29 & x30 & x31 & FR3 & ST3 & MI3 & LO3 & ->)
                      |(JNE & MEAS3 & x1 & x5 & x6 & x7 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xs5 & x28 & x29 & x30 & x31 & FR3 & ST3 & MI3 & LO3 & AI3 & SHT3 & SHS3 & STR3 & J0 & JE3 & EN3 & L403 & TL3 & ->)].
      - apply (aevt_evt RT AF PMc MST). eapply evt_mono; [eapply (atkc_nf E OK); [exact FR3| exact ST3| exact MI3| exact LO3]|].
        intros ms4 X4. exact (atkc_nfx_post E Σ PMc q out P RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc m mz ms4 OK FDO MST ST0 INVz FRM FR3 X4).
      - eapply (IH E Σ PMc d key q out P RA j' e L (c - 1) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc m mz);
          [exact OK| exact FDO| exact MST| exact ST0| exact INVz| exact FRM| exact PAT| exact LK| lia| exact FR3| exact STR3| exact J0| exact JE3| exact EN3| exact L403| exact TL3|].
        eapply (atkc_head E OK d); [exact FR3| exact ST3| exact MI3| exact LO3| exact AI3| exact SHT3| exact SHS3| exact STR3| exact J0| exact JE3| exact EN3| exact L403| exact TL3]. }
    apply (aevt_evt RT AF PMc MST). eapply evt_mono; [exact HS|]. intros ms1 X1.
    destruct X1 as [(j' & l & x1 & x5 & x6 & x7 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & STRL & LNE & FR1 & ST1 & MI1 & LO1 & AI1 & SHT1 & ELJ & IT0' & ITJ & JE & EN' & SHS1 & L40' & TLJ & ->)
                    |(x5 & x6 & x7 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & STRL & ->)].
    - eapply (ADV mx F j'); [exact INV| exact FR|].
      eapply (atkc_adv E OK d); [exact FR1| exact ST1| exact MI1| exact LO1| exact AI1| exact SHT1| exact ELJ| exact IT0'| exact ITJ| exact JE| exact EN'| exact SHS1| exact L40'| exact TLJ].
    - destruct STRL as (O0 & L0 & OSN & _).
      eapply (atkc_snc_call RT AF E OK PMc FDO MST SNCW SNC0); [exact LV| exact AIx| exact ARTx| exact MIx| exact STx| kul| kul| exact Q16'| exact PAT| exact LK| exact O0| lia|].
      intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA' PX'.
      destruct RA' as (ART' & MI' & WM' & ST').
      rewrite ret_pc_even by (first [lia | reflexivity]).
      assert (FR' : rw_cells asegs m' (q + -128) (atkm_frame (ae_DOC E) out P (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
      { apply (rw_cells_agree_nw asegs mx m' _ _ FR). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PX').
        intros x Hx. unfold atkm_frame, atkm_saved in Hx. cbn [app cells_size csize Nat.add] in Hx. split; [left; kul| lia]. }
      assert (OUT' : rw_cells asegs m' out [CB 24 jo]).
      { apply (rw_cells_agree_nw asegs mx m' _ _ OUTx). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PX').
        intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; kul| lia]. }
      assert (PX0 : rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (q + -128) (ae_lo E) 0 mx m') by (intros a Ha _; apply PX'; [exact Ha| lia]).
      pose proof (AINV_A_pres_ex RT Σ E _ (ae_lo E) 0 mx m' LV OK AIx PX0 ltac:(lia)) as AI'.
      assert (PFP' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m').
      { eapply rt_pres_fp_trans; [exact PFPx|].
        eapply (rt_pres_fp_of_ex _ _ (q + -128) q 0 0); [exact PX'| lia|]. intros a _. lia. }
      assert (INV' : atkc_inv E Σ q out m m').
      { split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AI'|]. split; [exact PFP'|]. exists jo. exact OUT'. }
      pose proof (lvl_shz_tape RT AF E OK Σ m' ART' LV) as SHT'.
      assert (SHS' : shz m' (ae_SBUF E) (ae_NS E)).
      { assert (S8 : ae_SBUF E mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
        pose proof (shz_live RT AF Σ m' (ae_SBUF E) (ae_NS E) ART' LS S8) as X.
        replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X. }
      pose proof (lvl_shz_rec RT AF E OK Σ m' out 24 ART' LV ltac:(kul) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO'.
      apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [8; 8; 4; 4]%nat) in OUT'; [| reflexivity]. cbn [mk_CB_cells app] in OUT'.
      apply (aevt_evt RT AF PMc MST). eapply evt_mono.
      { eapply (atkc_cmpret E OK d); [exact FR'| exact ST'| exact MI'| kul| exact AI'| exact SHT'| exact SHS'| exact STR| exact IT0| exact ITE| exact EN
          | exact L40| exact TL| exact OUT'| kul| kul| kul| exact SHZO'| kul]. }
      intros ms3 X3.
      destruct X3 as [(R0 & j2 & y1 & y5 & y6 & y7 & ys0 & ys1 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ys3 & ys5 & ys6 & ys7 & ys8 & ys9 & ys10 & ys11 & y28 & y29 & y30 & y31
                       & STR3 & EL3 & IJ3 & JE3 & FR3 & ST3 & MI3 & LO3 & OUT3 & QO3 & OB3 & O83 & SHZ3 & RA3 & IT3 & ITH3 & ->)
                      |(RN & j2 & y1 & y5 & y6 & y7 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31
                       & FR3 & ST3 & MI3 & LO3 & AI3 & SHT3 & EL3 & IT3 & IJ3 & JE3 & EN3 & SHS3 & L403 & TL3 & ->)].
      + apply (aevt_evt RT AF PMc MST). eapply evt_mono.
        { eapply (atkc_found E OK); [exact FR3| exact ST3| exact MI3| exact LO3| exact OUT3| exact QO3| exact OB3| exact O83| exact SHZ3| exact RA3| exact IT3| exact ITH3]. }
        intros ms4 RX4. eapply (atkc_rx_post E Σ PMc q out RA); [exact OK| exact ST0| exact INV'| exact FRM| | exact RX4]. reflexivity.
      + eapply (ADV m' F' j2); [exact INV'| exact FR3|].
        eapply (atkc_adv E OK d); [exact FR3| exact ST3| exact MI3| exact LO3| exact AI3| exact SHT3| exact EL3| exact IT3| exact IJ3| exact JE3| exact EN3| exact SHS3| exact L403| exact TL3].
  Qed.

  Theorem el_atkciA : forall E, aenvA_ok E -> el_atkey_cpsA RT E ATKCI_FN_A.
  Proof using AF RC SNCW SNC0.
    intros E OK Σ PMc d key i j q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
      FDO MST LV AI PAT EL I0 JN PRE FRM.
    destruct PRE as (NODE & N0 & NB & N8 & FO & OUT & QO & OB & O8 & ART0 & MI0 & ST0 & QL & Q16).
    destruct (ok_hi E OK) as [HL HT]. pose proof (ok_lo E OK) as LO0.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ [S16 [NS8 _]] _ _ _ _ _].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    assert (KL : 0 <= zlength key < 2^40).
    { destruct PAT as (pre & EP & _). pose proof (ok_p1len E OK) as PL. rewrite EP in PL. unfold zlength in *. rewrite length_app in PL. lia. }
    pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
    rewrite <- (Z_to_bv_bv_unsigned ra). set (RA := bv_unsigned ra) in *. clearbody RA.
    assert (STA : atkc_st E Σ q out RA) by (unfold atkc_st; split; [exact LV|]; repeat split; kul).
    assert (FPW : fp_client RT Σ (ae_lo E) (atkm_W q)) by (unfold atkm_W; apply fp_client_stack1; kul).
    assert (ARTW : forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> ART RT Σ m').
    { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m m' ART0 LV FPW MU WM). }
    assert (SHZN : forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' node 16).
    { intros m' MU WM. apply (fobj_shz RT AF Σ m' node 16 (ARTW m' MU WM)).
      exact (fobj_munch RT AF Σ m m' (ae_lo E) (atkm_W q) node 16 ART0 LWIN FPW MU FO). }
    assert (SHZT : forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
    { intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ m' (ARTW m' MU WM) LV). }
    assert (SHZS : forall m', munch (atkm_W q) m m' -> wmono asegs m m' -> shz m' (ae_SBUF E) (ae_NS E)).
    { intros m' MU WM. assert (S8 : ae_SBUF E mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
      pose proof (shz_live RT AF Σ m' (ae_SBUF E) (ae_NS E) (ARTW m' MU WM) LS S8) as X.
      replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X. }
    assert (NQ : q <= node \/ node + 16 <= q + -128) by (right; kul).
    pose proof (atkc_walk1 E OK d i j q out node P (zlength key) RA gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
                  EL I0 JN AI NODE N0 ltac:(lia) NQ OUT QO MI0 ST0 ltac:(kul) Q16 (shb_cells_of_art RT AF Σ m ART0) KL RAR
                  SHZN SHZT SHZS) as W1.
    assert (A : aevt RT PMc Σ (atkc_K E Σ PMc RA q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m)
                  (lvl_entry ATKCI_FN_A (wz RA) q gp t0 t1 t2 s0 s1 out node P (zlength key) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)).
    { apply (aevt_evt RT AF PMc MST). eapply evt_mono; [exact W1|]. intros ms1 X1.
      destruct X1 as (m1 & MU1 & WM1 & MI1 & ST1 & LO1 & AI1 & OUT1 & X1).
      pose proof (ARTW m1 MU1 WM1) as ART1.
      pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -128) q [] m m1 ART0 LV ltac:(kul) MU1) as PFP0.
      assert (INV1 : atkc_inv E Σ q out m m1).
      { split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AI1|]. split; [| exists jo; exact OUT1].
        intros a Ha _. apply PFP0; [exact Ha| exact I]. }
      destruct X1 as [XA|[XB|XC]].
      - destruct XA as (j0 & j1 & y5 & y6 & y7 & y8 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & TY & FR1 & ->).
        eapply (atkc_set_post E Σ PMc q out P RA); [exact OK| exact FDO| exact MST| exact STA| exact INV1| exact FRM| left; split; reflexivity| exact FR1|].
        intros m2 F2 u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 zb oc od FR2 ST2 MI2 OUT2 SHZ2.
        eapply (atkc_set_ret E OK); [exact FR2| exact ST2| exact MI2| kul| exact OUT2| kul| kul| kul| exact SHZ2| kul| left; split; reflexivity].
      - destruct XB as (FR1 & x1 & x5 & x6 & x7 & xs0 & xs1 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xs2 & xs3 & xs5 & xs6 & xs7 & xs8 & xs9 & xs10 & xs11
                        & x28 & x29 & x30 & x31 & ->).
        apply (aevt_evt RT AF PMc MST). eapply evt_mono; [eapply (atkc_nf E OK); [exact FR1| exact ST1| exact MI1| exact LO1]|].
        intros ms4 X4. exact (atkc_nfx_post E Σ PMc q out P RA gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 ms4 OK FDO MST STA INV1 FRM FR1 X4).
      - destruct XC as (FR1 & SHT1 & SHS1 & d' & e & c & x1 & x5 & x6 & x7 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xs5 & x28 & x29 & x30 & x31
                        & DS & TN & STR1 & I1 & IE & EN & L40 & TL & ->).
        eapply (atkc_loop (Z.to_nat (e - (i + 1))) E Σ PMc d' key q out P RA (i + 1) e (zlength key) c gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1);
          [exact OK| exact FDO| exact MST| exact STA| exact INV1| exact FRM| exact PAT| reflexivity| lia| exact FR1| exact STR1| exact I1| lia| exact EN| exact L40| exact TL|].
        eapply (atkc_head E OK d'); [exact FR1| exact ST1| exact MI1| exact LO1| exact AI1| exact SHT1| exact SHS1| exact STR1| exact I1| lia| exact EN| exact L40| exact TL]. }
    intros T cc [Hc FC0] Hk. exact (A T cc Hc Hk).
  Qed.
End AtKeyC.
