From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA El_callsA El_atixdA El_atixwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section AtIx.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.

Local Ltac ul := unfold EL_CALL_NEED_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem el_atixA : forall E, aenvA_ok E -> el_atix_cpsA RT E.
Proof using AF RC.
  intros E OK Σ PMc d i j idx q out node ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
    FDO MST LV AI EL I0 JN IDX PRE FRM.
  destruct PRE as (NODE & N0 & NLO & N8 & FO & OUT & QO & OB & O8 & ART0 & MI0 & ST0 & LOR & Q16).
  intros T cc [Hc FC0] Hk.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' (D8 & DF & DL & DS & DT) LOW0 [HL HT]].
  pose proof LV as (LT & LS & LP & LF & LWIN).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (atix_W q out)) by (intros Σx; apply fp_client_stack2; ul).
  assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) [(out, out + 24)]) by (intros Σx; apply fp_client_stack1; ul).
  assert (ARTW : forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> ART RT Σ m').
  { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m m' ART0 LV (FPW Σ) MU WM). }
  assert (HWlo : Forall (fun r => ae_lo E <= fst r) (atix_W q out)) by (unfold atix_W; constructor; [cbn; ul|]; constructor; [cbn; ul| constructor]).
  assert (HWOlo : Forall (fun r => ae_lo E <= fst r) [(out, out + 24)]) by (constructor; [cbn; ul| constructor]).
  assert (SHZN : forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' node 16).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' node 16 (ARTW m' MU WM)).
    exact (fobj_munch RT AF Σ m m' (ae_lo E) _ node 16 ART0 ltac:(ul) (FPW Σ) MU FO). }
  assert (SHZD : forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16).
  { intros m' MU WM. apply (lvl_shz_doc E OK). exact (AINV_A_munch E _ m m' OK AI MU HWlo). }
  assert (SHZT : forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
  { intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ m' (ARTW m' MU WM) LV). }
  assert (SHZO : forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' out 24).
  { intros m' MU WM. exact (lvl_shz_rec RT AF E OK Σ m' out 24 (ARTW m' MU WM) LV ltac:(ul) ltac:(lia) O8 eq_refl ltac:(lia)). }
  pose proof (shb_cells_of_art RT AF Σ m ART0) as SHB.

  pose proof (atix_walk1 E OK d i j idx q out node ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
                EL I0 JN IDX AI NODE N0 NLO N8 OUT QO OB O8 MI0 ST0 ltac:(ul) Q16 SHB SHZN SHZD SHZT SHZO) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cc (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & X1 & Hc1'). clear Hc1.
  destruct X1 as [(m1 & j0 & ra' & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & MU1 & WM1 & MI1 & OUT1 & ST1 & FR1 & -> & SITE)
                 |(m1 & jo1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & MU1 & WM1 & MI1 & OUT1 & ST1 & ->)].
  -
    pose proof (ARTW m1 MU1 WM1) as ART1.
    pose proof (AINV_A_munch E _ m m1 OK AI MU1 HWlo) as AI1.
    pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -32) q [(out, out + 24)] m m1 ART0 LV ltac:(ul) MU1) as PFP1.
    assert (EU : bv_unsigned (Z_to_bv 64 (q + -32)) = q + -32) by (apply unsigned_lit; ul).
    assert (Q16' : (q + -32) mod 16 = 0) by (replace (q + -32) with (q + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    pose proof (call_ok_lvl RT E OK Σ m1 (q + -32) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
    assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -32)) out 16).
    { apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
      apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
    apply (rc_asan_memset RT RC Σ PMc (Z_to_bv 64 ra') (Z_to_bv 64 (q + -32)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 (out + 16)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 out) (Z_to_bv 64 0) (Z_to_bv 64 16) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
             F fc m1 out 16 (Z_to_bv 8 0) (ae_lo E) FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CDST ART1 MI1 COK1 T c1 Hc1').
    intros c2 Hc2. unfold icpt_postF in Hc2.
    destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite EU in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even ra') in Hc2' by (unfold atix_set_site in SITE; lia).
    assert (FR2 : rw_cells asegs m2 (q + -32) (atix_frame ra s0 s1 j0)).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold atix_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
    apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
    lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
    clearbody jA jB jC.
    pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT1 eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
    set (K2 := fun ms => exists (m3 : mem) (jo3 : list byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
              F2 (ret_pc ra) fc None m3 (seg_rom asegs)
      /\ munch [(out, out + 24)] m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3 /\ stk asegs m3 (ae_lo E) q
      /\ rw_cells asegs m3 out [CB 24 jo3]).
    lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
      assert (W2 : forall ms, eq X ms -> evt asegs K2 ms) end.
    { intros ms <-. eapply (atix_after_set E OK K2); [exact FR2| exact ST2| exact MI2| exact OUT2| ul| exact QO| exact OB| exact O8| exact Q16| exact SITE| |].
      - intros m' MU' WM'.
        exact (lvl_shz_rec RT AF E OK Σ m' out 24 (lvl_art_munch RT AF E Σ _ m2 m' ART2 LV (FPO Σ) MU' WM') LV ltac:(ul) ltac:(lia) O8 eq_refl ltac:(lia)).
      - intros m' jo' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU3 WM3 MI3 ST3 OUT3. subst K2. cbv beta.
        exists m', jo', y5, y6, y7, y10, y11, y12, y13, y14. exists y15, y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3| exact OUT3]. }
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & X3 & Hc3'). clear Hc3. subst K2. cbv beta in X3.
    destruct X3 as (m3 & jo3 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU3 & WM3 & MI3 & ST3 & OUT3).
    apply Hk. split.
    2: { apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3'). intros ms <-. exact FRM. }
    eapply (lvl_postA_intro0 RT E Σ Σ PMc c3); [exact Hc3'| | exact MI3| exact ST3| | exact OUT3| | reflexivity| reflexivity| reflexivity| lia].
    + exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3).
    + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
      * eapply (rt_pres_fp_of_ex _ _ (q + -32) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
      * intros a Ha Ho. apply MU3. exact Ho.
    + eapply (AINV_A_munch E _ m2 m3 OK); [| exact MU3| exact HWOlo].
      exact (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(ul)).
  -
    apply Hk. split.
    2: { apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1'). intros ms <-. exact FRM. }
    eapply (lvl_postA_intro0 RT E Σ Σ PMc c1); [exact Hc1'| exact (ARTW m1 MU1 WM1)| exact MI1| exact ST1| | exact OUT1| | reflexivity| reflexivity| reflexivity| lia].
    + exact (rt_pres_fp_of_munch RT AF E Σ m (q + -32) q [(out, out + 24)] m m1 ART0 LV ltac:(ul) MU1).
    + exact (AINV_A_munch E _ m m1 OK AI MU1 HWlo).
Qed.

End AtIx.
