(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_arrwA Atp_arrxA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma tword_decomp : forall w t, 0 <= w -> ttype w = t -> w = cword t (tnext w) (tcount w).
Proof.
  intros w t W0 TT. unfold cword, tword, ttype, tnext, tcount in *. subst t.
  change (2 ^ 56) with (4294967296 * 16777216). change (2 ^ 32) with 4294967296. change (2 ^ 24) with 16777216.
  rewrite <- (Z.div_div w 4294967296 16777216) by lia.
  pose proof (Z.div_mod w 4294967296 ltac:(lia)) as D1. pose proof (Z.div_mod (w / 4294967296) 16777216 ltac:(lia)) as D2.
  set (a := w / 4294967296) in *. set (b := a / 16777216) in *. lia.
Qed.

Section ArrLevel.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.

  Local Ltac ul := unfold arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Theorem atp_arrA : atp_arr_cpsA RT E d.
  Proof using AF RC OK HELEM.
    intros Σ PMc ptr i e c q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
      FDO MST LV AI PAT TY NXT CLOSE TILES I0 EN PRE FRM.
    destruct PRE as (NODE & QN & NB & N8 & OUT & QO & OB & O8 & NO & ART0 & MI0 & ST0 & LOR & Q16 & FRB & CRB & LVB).
    intros T cc [Hc FC0] Hk.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' (D8 & DF & DL & DS & DT) LOW0 [HL HT]].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    pose proof (zlength_nonneg ptr) as ZL.
    assert (ARR96 : ae_lo E + 65696 <= q) by ul.
    assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (arr_W q out)) by (intros Σx; apply fp_client_stack2; ul).
    assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) (arr_WO out)) by (intros Σx; apply fp_client_stack1; ul).
    assert (ARTW : forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> ART RT Σ m').
    { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m m' ART0 LV (FPW Σ) MU WM). }
    assert (HWlo : Forall (fun r => ae_lo E <= fst r) (arr_W q out)) by (constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]).
    assert (HWOlo : Forall (fun r => ae_lo E <= fst r) (arr_WO out)) by (constructor; [cbn; lia| constructor]).
    assert (SHZN : forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' node 16).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' node 16 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZO : forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' out 24).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' out 24 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZD : forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16).
    { intros m' MU WM. apply (lvl_shz_doc E OK). exact (AINV_A_munch E _ m m' OK AI MU HWlo). }
    assert (SHZT : forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
    { intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ m' (ARTW m' MU WM) LV). }
    assert (ACCP : ptr <> [] -> forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> acc asegs m' (ae_PB E) (ae_NPB E)).
    { intros NE m' MU WM. exact (lvl_acc_ptr RT AF E Σ m' P ptr (ARTW m' MU WM) LV PAT NE). }
    pose proof (shb_cells_of_art RT AF Σ m ART0) as SHB.
    assert (EU : bv_unsigned (Z_to_bv 64 (q + -96)) = q + -96) by (apply unsigned_lit; ul).
    assert (Q16' : (q + -96) mod 16 = 0) by (replace (q + -96) with (q + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (CST0 : 0 <= arr_costA d (zlength ptr)) by (unfold arr_costA, LVL_C1, DCOST; lia).

    pose proof (arr_walk1 E OK d ptr i e c q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
                  PAT TY NXT TILES I0 EN AI NODE QN NB OUT QO OB O8 NO MI0 ST0 ltac:(lia) Q16 SHB SHZN SHZO SHZD SHZT ACCP) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ cc (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j0 & jc & MU1 & WM1 & MI1 & X1) & Hc1'). clear Hc1.
    pose proof (ARTW m1 MU1 WM1) as ART1.
    pose proof (AINV_A_munch E _ m m1 OK AI MU1 HWlo) as AI1.
    pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -96) q [(out, out + 24)] m m1 ART0 LV ltac:(lia) MU1) as PFP1.
    assert (NODE1 : rw_cells asegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)]).
    { apply (rw_cells_agree asegs m m1 _ _ NODE); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold arr_W. cbn [outside]. repeat split; lia. }
    destruct X1 as [XCPY|[XSET|[XRET|XREC]]].
    -
      destruct XCPY as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & -> & ST1 & FR1 & OUT1).
      set (bs := le8 (Z_to_bv 64 (ae_DOC E)) ++ le8 (Z_to_bv 64 i)).
      assert (LBS : length bs = 16%nat) by (subst bs; rewrite length_app, !length_le8; reflexivity).
      assert (NODEB : bytes_at asegs m1 node bs).
      { pose proof (rw_cells_bytes_at asegs m1 node _ NODE1) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
      assert (CSRC : checked_src RT Σ m1 (Z_to_bv 64 (q + -96)) (ae_lo E) node (Z.of_nat (length bs))).
      { rewrite LBS. apply (checked_src_stack RT AF Σ m1 _ (ae_lo E) node 16 ART1); [ul| ul| rewrite EU; lia]. }
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -96)) out (Z.of_nat (length bs))).
      { rewrite LBS. apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -96) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      unfold entry_st in Hc1'.
      apply (rc_asan_memcpy RT RC Σ PMc (Z_to_bv 64 0xb6a64) (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 out) s1
               (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 16) a3' a4' a5' a6' a7' s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
               F fc m1 out node bs (ae_lo E) FDO MST eq_refl eq_refl ltac:(rewrite LBS; reflexivity) ltac:(ul) ltac:(ul) ltac:(rewrite LBS; cbn; lia)
               NODEB CSRC CDST ltac:(rewrite LBS; cbn; lia) ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU in ST2, PRES2. rewrite LBS in PRES2. change (Z.of_nat 16%nat) with 16 in PRES2.
      rewrite (ret_pc_even 0xb6a64) in Hc2' by lia.
      assert (FR2 : rw_cells asegs m2 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc)).
      { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold arr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
      lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC bs _ _ _ OUT1 eq_refl eq_refl BY2 LBS WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
      pose proof (lvl_shz_rec RT AF E OK Σ m2 out 24 ART2 LV ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO2.
      set (K2 := fun ms => exists (m3 : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F2 (ret_pc ra) fc None m3 (seg_rom asegs)
        /\ munch (arr_WO out) m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3 /\ stk asegs m3 (ae_lo E) q
        /\ rw_cells asegs m3 out [CB 16 bs; C4 (Z_to_bv 64 0); CB 4 jC]).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt asegs K2 ms) end.
      { intros ms <-. eapply (arr_after_cpy E OK K2); [exact FR2| exact ST2| exact MI2| lia| exact OUT2| exact QO| exact OB| exact O8| exact SHZO2|].
        intros m' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU3 WM3 MI3 ST3 OUT3. subst K2. cbv beta.
        exists m', y5, y6, y7, y10, y11, y12, y13, y14, y15. exists y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3| exact OUT3]. }
      apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & X3 & Hc3'). clear Hc3. subst K2. cbv beta in X3.
      destruct X3 as (m3 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU3 & WM3 & MI3 & ST3 & OUT3).
      destruct (rw_cells_forget _ _ _ _ OUT3) as [jo' OUT3']. cbn [cells_size csize Nat.add] in OUT3'.
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3'). intros ms <-. cbn. exact FRM. }
      eapply (lvl_postA_intro0 RT E Σ Σ PMc c3); [exact Hc3'| | exact MI3| exact ST3| | exact OUT3'| | reflexivity| reflexivity| reflexivity| lia].
      + exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3).
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * eapply (rt_pres_fp_of_ex _ _ (q + -96) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU3. exact Ho.
      + eapply (AINV_A_munch E _ m2 m3 OK); [| exact MU3| exact HWOlo].
        exact (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)).
    -
      destruct XSET as (ra' & t0' & t1' & t2' & s1' & a3' & a4' & a5' & a6' & a7' & s2' & s4' & s5' & s6' & t3' & t4' & t5' & t6' & -> & SITE & ST1 & FR1 & OUT1).
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -96)) out 16).
      { apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -96) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      assert (RAE : 0 <= ra' < 2^64 /\ ra' mod 2 = 0) by (destruct SITE as [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]]; lia).
      unfold entry_st in Hc1'.
      apply (rc_asan_memset RT RC Σ PMc (Z_to_bv 64 ra') (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 out) s1'
               (Z_to_bv 64 out) (Z_to_bv 64 0) (Z_to_bv 64 16) a3' a4' a5' a6' a7' s2' (Z_to_bv 64 2147450880) s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6'
               F fc m1 out 16 (Z_to_bv 8 0) (ae_lo E) FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CDST ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
      rewrite (ret_pc_even ra') in Hc2' by lia.
      assert (FR2 : rw_cells asegs m2 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc)).
      { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold arr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
      lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT1 eq_refl eq_refl BY2
                    eq_refl WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
      assert (SHZO2 : forall m', munch (arr_WO out) m2 m' -> wmono asegs m2 m' -> shz m' out 24).
      { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' out 24 (lvl_art_munch RT AF E Σ _ m2 m' ART2 LV (FPO Σ) MU WM) LV); first [lia | reflexivity]. }
      set (K2 := fun ms => exists (m3 : mem) (code : Z) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F2 (ret_pc ra) fc None m3 (seg_rom asegs)
        /\ munch (arr_WO out) m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3 /\ stk asegs m3 (ae_lo E) q
        /\ rw_cells asegs m3 out [CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 code); CB 4 jC]).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt asegs K2 ms) end.
      { intros ms <-. eapply (arr_after_set E OK K2); [exact FR2| exact ST2| exact MI2| lia| exact OUT2| exact QO| exact OB| exact O8| exact SHZO2| exact SITE|].
        intros m' code y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU3 WM3 MI3 ST3 OUT3. subst K2. cbv beta.
        exists m', code, y5, y6, y7, y10, y11, y12, y13, y14. exists y15, y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3| exact OUT3]. }
      apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & X3 & Hc3'). clear Hc3. subst K2. cbv beta in X3.
      destruct X3 as (m3 & code & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU3 & WM3 & MI3 & ST3 & OUT3).
      destruct (rw_cells_forget _ _ _ _ OUT3) as [jo' OUT3']. cbn [cells_size csize Nat.add] in OUT3'.
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3'). intros ms <-. cbn. exact FRM. }
      eapply (lvl_postA_intro0 RT E Σ Σ PMc c3); [exact Hc3'| | exact MI3| exact ST3| | exact OUT3'| | reflexivity| reflexivity| reflexivity| lia].
      + exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3).
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * eapply (rt_pres_fp_of_ex _ _ (q + -96) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU3. exact Ho.
      + eapply (AINV_A_munch E _ m2 m3 OK); [| exact MU3| exact HWOlo].
        exact (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)).
    -
      destruct XRET as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jo' & -> & ST1 & OUT1).
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1'). intros ms <-. cbn. exact FRM. }
      eapply (lvl_postA_intro0 RT E Σ Σ PMc c1); [exact Hc1'| exact ART1| exact MI1| exact ST1| exact PFP1| exact OUT1| exact AI1
        | reflexivity| reflexivity| reflexivity| lia].
    -
      destruct XREC as (it & j' & tok & r & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & od & -> & EL & IT0 & JE & PAT2 & TOK0 & ZR
                        & ST1 & FR1 & OUTW).
      pose proof (zlength_nonneg r) as ZLr. rewrite zlength_cons in ZR.

      pose proof FR1 as FR1'. unfold arr_frame in FR1'.
      apply (proj1 (rw_cells_app asegs m1 _ [CB 8 j0] _)) in FR1'. destruct FR1' as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc.
      replace (q + -96 + Z.of_nat 8) with (q + -88) in FRbc by lia.
      apply (proj1 (rw_cells_app asegs m1 _ [CB 24 jc] _)) in FRbc. destruct FRbc as [FRb FRc]. cbn [cells_size csize Nat.add] in FRc.
      replace (q + -88 + Z.of_nat 24) with (q + -64) in FRc by lia.
      pose proof OUTW as OUTW'.
      apply (proj1 (rw_cells_app asegs m1 _ [_; _] _)) in OUTW'. destruct OUTW' as [NODEC OUTT]. cbn [cells_size csize Nat.add] in OUTT.
      assert (CST : elem_costA d (zlength (47 :: r)) <= arr_costA d (zlength ptr)) by (unfold elem_costA, arr_costA; rewrite zlength_cons; lia).
      assert (PRE' : lvl_pre RT E Σ m1 (q + -96) (q + -88) out it jc (elem_needA d) (elem_costA d (zlength (47 :: r))) d).
      { unfold lvl_pre. split; [exact NODEC|]. split; [lia|]. split; [lia|]. split; [exact O8|].
        split; [exact FRb|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [right; lia|].
        split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [ul|]. split; [exact Q16'|].
        split; [exact FRB|]. split; [lia| exact LVB]. }
      pose proof HELEM as HE. unfold atp_elem_cpsA in HE.
      apply (HE Σ PMc (47 :: r) it j' (q + -96) (q + -88) out (P + 1 + tok) (Z_to_bv 64 0xb6dcc) gp t0' t1' t2' (Z_to_bv 64 out) (Z_to_bv 64 (P + 1))
               a4' a5' a6' a7' (Z_to_bv 64 (out + 16)) (Z_to_bv 64 ((out + 16) / 8 + 2147450880)) (Z_to_bv 64 (zlength ptr - 1)) (Z_to_bv 64 47) (Z_to_bv 64 tok)
               s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 jc FDO MST LV AI1 PAT2 EL IT0 ltac:(lia) PRE' FRM T c1).
      { split; [exact Hc1'|]. apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1'). intros ms <-. cbn. exact FRM. }
      clear HE. intros c2 [PO2 FC2].
      destruct PO2 as (Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1).
      destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (v2 & m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & [jo2 OUTC2] & AI2) & FRM2 & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr] in FRM2.
      rewrite (ret_pc_even 0xb6dcc) in Hc2' by lia.
      assert (LVx : a_live RT Σ1 E) by (exact (a_live_eq RT Σ Σ1 E LV LV1 FRS1 SP1)).
      assert (AGR : agree_on (fun x => q + -96 <= x < USTACK_TOP /\ ~ (q + -88 <= x < q + -64)) m1 m2).
      { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x [Hx1 Hx2]. split; [left; exact Hx1| cbn [outside]; split; [lia| exact I]]. }
      assert (FRa2 : rw_cells asegs m2 (q + -96) [CB 8 j0]).
      { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRa). eapply agree_sub; [exact AGR|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (FRc2 : rw_cells asegs m2 (q + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRc). eapply agree_sub; [exact AGR|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (OUTW2 : rw_cells asegs m2 out [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 0); CB 4 od]).
      { apply (rw_cells_agree_nw asegs m1 m2 _ _ OUTW). eapply agree_sub; [exact AGR|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (FR2 : rw_cells asegs m2 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jo2)).
      { unfold arr_frame. change (CB 8 j0 :: ?rest) with ([CB 8 j0] ++ rest).
        apply (proj2 (rw_cells_app asegs m2 _ [CB 8 j0] _)). split; [exact FRa2|]. cbn [cells_size csize Nat.add].
        replace (q + -96 + Z.of_nat 8) with (q + -88) by lia. change (CB 24 jo2 :: ?rest) with ([CB 24 jo2] ++ rest).
        apply (proj2 (rw_cells_app asegs m2 _ [CB 24 jo2] _)). split; [exact OUTC2|]. cbn [cells_size csize Nat.add].
        replace (q + -88 + Z.of_nat 24) with (q + -64) by lia. exact FRc2. }
      pose proof OUTC2 as [[LJ2 _] _]. cbn [cells_wf cell_wf] in LJ2. destruct LJ2 as [LJ2 _].

      set (TGT := MS (mkR (Z_to_bv 64 0xb6ddc) (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 (P + 1))
                            (Z_to_bv 64 out) (Z_to_bv 64 (q + -88)) (Z_to_bv 64 16) b3 b4 b5 b6 b7
                            (Z_to_bv 64 (out + 16)) (Z_to_bv 64 ((out + 16) / 8 + 2147450880)) (Z_to_bv 64 (zlength ptr - 1)) (Z_to_bv 64 47) (Z_to_bv 64 tok)
                            s7 s8 s9 s10 s11 u3 u4 u5 u6) F2 (Z_to_bv 64 e_asan_memcpy) fc2 None m2 (seg_rom asegs)).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt asegs (eq TGT) ms) end.
      { intros ms <-. apply (arr_rec_glue (eq TGT)); [exact MI2| ul| ul| reflexivity]. }
      apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3. subst TGT.

      set (bs := firstn 16 jo2).
      assert (LBS : length bs = 16%nat) by (subst bs; rewrite firstn_length; lia).
      assert (RECB : bytes_at asegs m2 (q + -88) bs).
      { subst bs. apply bytes_at_firstn. pose proof (rw_cells_bytes_at asegs m2 _ _ OUTC2) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
      assert (CSRC : checked_src RT Σ1 m2 (Z_to_bv 64 (q + -96)) (ae_lo E) (q + -88) (Z.of_nat (length bs))).
      { rewrite LBS. apply (checked_src_stack RT AF Σ1 m2 _ (ae_lo E) (q + -88) 16 ART2); [rewrite SP1; ul| ul| rewrite EU; lia]. }
      assert (CDST : checked_dst RT Σ1 m2 (Z_to_bv 64 (q + -96)) out (Z.of_nat (length bs))).
      { rewrite LBS. apply (checked_dst_stack RT AF Σ1 m2 _ out 16 ART2); [rewrite SP1; ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m2 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUTW2). }
      pose proof (call_ok_lvl RT E OK Σ1 m2 (q + -96) LVx ST2 ltac:(ul) ltac:(ul) Q16') as COK2.
      apply (rc_asan_memcpy RT RC Σ1 PMc (Z_to_bv 64 0xb6ddc) (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 (P + 1))
               (Z_to_bv 64 out) (Z_to_bv 64 (q + -88)) (Z_to_bv 64 16) b3 b4 b5 b6 b7
               (Z_to_bv 64 (out + 16)) (Z_to_bv 64 ((out + 16) / 8 + 2147450880)) (Z_to_bv 64 (zlength ptr - 1)) (Z_to_bv 64 47) (Z_to_bv 64 tok)
               s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 out (q + -88) bs (ae_lo E) FDO MST eq_refl eq_refl ltac:(rewrite LBS; reflexivity)
               ltac:(ul) ltac:(ul) ltac:(rewrite LBS; cbn; lia) RECB CSRC CDST ltac:(rewrite LBS; cbn; lia) ART2 MI2 COK2 T c3).
      { unfold entry_st. exact Hc3'. }
      intros c4 Hc4. unfold icpt_postF in Hc4.
      destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4) & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & ->).
      rewrite EU in ST4, PRES4. rewrite LBS in PRES4. change (Z.of_nat 16%nat) with 16 in PRES4.
      rewrite (ret_pc_even 0xb6ddc) in Hc4' by lia.
      rewrite FRS1 in PRES4. rewrite LV1 in PRES4.
      assert (FR4 : rw_cells asegs m4 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jo2)).
      { apply (rw_cells_agree_nw asegs m2 m4 _ _ FR2). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4).
        intros x Hx. unfold arr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      assert (OUTC4 : rw_cells asegs m4 (q + -88) [CB 24 jo2]).
      { apply (rw_cells_agree_nw asegs m2 m4 _ _ OUTC2). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4).
        intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      pose proof (rec_copy16 m2 m4 out [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 it)] (C4 (Z_to_bv 64 0)) od bs _ _ _ OUTW2 eq_refl eq_refl BY4 LBS WM4
                    PRES4 ltac:(lia) ltac:(ul)) as OUT4.
      pose proof (lvl_shz_rec RT AF E OK Σ1 m4 out 24 ART4 LVx ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO4.
      assert (RDE : ov_read_bytes asegs m4 (wa (q + -72)) 4 = Some (firstn 4 (skipn 16 jo2))).
      { pose proof (rw_cells_bytes_at asegs m4 _ _ OUTC4) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
        pose proof (bytes_at_read asegs m4 _ _ 16 4 X ltac:(lia) ltac:(cbn; lia)) as R.
        replace (q + -88 + 16) with (q + -72) in R by lia. exact R. }
      remember (firstn 4 (skipn 16 jo2)) as eb eqn:Eeb.
      assert (LEB : length eb = 4%nat) by (subst eb; rewrite firstn_length; rewrite length_skipn; lia).
      clear Eeb.
      set (K4 := fun ms => exists (m5 : mem) (err : word) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F4 (ret_pc ra) fc2 None m5 (seg_rom asegs)
        /\ munch (arr_WO out) m4 m5 /\ wmono asegs m4 m5 /\ mem_inv asegs m5 /\ stk asegs m5 (ae_lo E) q
        /\ rw_cells asegs m5 out [CB 16 bs; C4 err; CB 4 od]).
      lazymatch type of Hc4' with ASTA _ _ _ (eq ?X) _ =>
        assert (W4 : forall ms, eq X ms -> evt asegs K4 ms) end.
      { intros ms <-. eapply (arr_after_rec E OK K4); [exact FR4| exact ST4| exact MI4| lia| exact OUT4| exact QO| exact OB| exact O8| exact SHZO4| exact RDE| exact LEB|].
        intros m' err y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU5 WM5 MI5 ST5 OUT5. subst K4. cbv beta.
        exists m', err, y5, y6, y7, y10, y11, y12, y13, y14. exists y15, y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|]. split; [exact MI5|]. split; [exact ST5| exact OUT5]. }
      apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W4) Hc4'). clear W4. intros c5 Hc5.
      destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & X5 & Hc5'). clear Hc5. subst K4. cbv beta in X5.
      destruct X5 as (m5 & err & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU5 & WM5 & MI5 & ST5 & OUT5).
      destruct (rw_cells_forget _ _ _ _ OUT5) as [jo' OUT5']. cbn [cells_size csize Nat.add] in OUT5'.
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ1 PMc _ c5 Hc5'). intros ms <-. cbn. exact FRM2. }
      eapply (lvl_postA_intro0 RT E Σ Σ1 PMc c5); [exact Hc5'| | exact MI5| exact ST5| | exact OUT5'| | exact LV1| exact FRS1| exact SP1| lia].
      + exact (lvl_art_munch RT AF E Σ1 _ m4 m5 ART4 LVx (FPO Σ1) MU5 WM5).
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans; [| eapply rt_pres_fp_trans].
        * exact (rt_pres_fp_lower RT AF E Σ m (q + -96) q (q + -88) (q + -88 + 24) [(out, out + 24)] m1 m2 ART0 LV ltac:(lia) ltac:(lia) ltac:(lia) PRES2).
        * eapply (rt_pres_fp_of_ex _ _ (q + -96) q out 16); [exact PRES4| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU5. exact Ho.
      + eapply (AINV_A_munch E _ m4 m5 OK); [| exact MU5| exact HWOlo].
        eapply (AINV_A_pres_ex RT Σ1 E _ out 16 m2 m4 LVx OK AI2); [| lia]. rewrite LV1, FRS1. exact PRES4.
  Qed.
End ArrLevel.
