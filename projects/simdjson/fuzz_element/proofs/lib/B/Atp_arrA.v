(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit
     Atp_defsA Atp_kitA Atp_objkA Atp_arrlA Atp_arratA Atp_arrwA Atp_arrxA Atp_arrtA.
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

Lemma arr_node_elem : forall (T S : Z -> Z) (sn : Z) (d : nat) (i e c : Z),
  ttype (T i) = t_arr -> tnext (T i) = e + 1 -> T e = tword t_arr_end i -> tiles (elem T S sn ck_any d) (i + 1) e c -> 0 <= T i ->
  elem T S sn ck_any (Datatypes.S d) i (e + 1).
Proof.
  intros T S sn d i e c TY NXT CLOSE TILES W0.
  apply (elem_array T S sn ck_any d i e c (tcount (T i))); [| rewrite <- NXT; exact (tword_decomp _ _ W0 TY)| exact CLOSE| exact TILES].
  unfold ck_any, tcount, CNT_MAX. change (2 ^ 24) with 16777216. pose proof (Z.mod_pos_bound (T i / 2 ^ 32) 16777216 ltac:(lia)). lia.
Qed.

Section ArrLevel.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.

  Local Ltac lia_prep :=
    repeat match goal with
    | H : forall x : ?T, _ |- _ => lazymatch type of T with Prop => fail | _ => clear H end
    | H : atp_elem_cpsA _ _ _ |- _ => clear H
    | H : rt_contracts _ |- _ => clear H
    | H : art_facts _ |- _ => clear H
    | H : rw_cells _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H
    | H : wmono _ _ _ |- _ => clear H
    | H : mem_inv _ _ |- _ => clear H
    | H : ART _ _ _ |- _ => clear H
    | H : AINV_A _ _ |- _ => clear H
    | H : tiles _ _ _ _ |- _ => clear H
    | H : elem _ _ _ _ _ _ _ |- _ => clear H
    | H : ptr_atA _ _ _ |- _ => clear H
    | H : a_live _ _ _ |- _ => clear H
    | H : agree_on _ _ _ |- _ => clear H
    | H : shz _ _ _ |- _ => clear H
    | H : shb_cells _ |- _ => clear H
    | H : Forall _ _ |- _ => clear H
    | H : aenvA_ok _ |- _ => clear H
    | H : frm0 _ |- _ => clear H
    | H : In _ _ |- _ => clear H
    | H : rt_pres_fp _ _ _ _ _ _ |- _ => clear H
    | H : rt_pres_ex _ _ _ _ _ _ _ |- _ => clear H
    | H : checked_src _ _ _ _ _ _ _ |- _ => clear H
    | H : checked_dst _ _ _ _ _ _ |- _ => clear H
    | H : call_ok _ _ _ _ _ |- _ => clear H
    | H : stk _ _ _ _ |- _ => clear H
    | H : fdfs_only _ |- _ => clear H
    | H : mat_stable _ |- _ => clear H
    end.
  Local Ltac flia := lia_prep; lia.
  Local Ltac ul := lia_prep; unfold arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Theorem atp_arrA : atp_arr_cpsA RT E d.
  Proof using AF RC OK HELEM.
    intros Σ PMc ptr i e c q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
      FDO MST LV AI PAT TY NXT CLOSE TILES I0 EN PRE FRM.
    pose proof PRE as PRE0.
    destruct PRE as (NODE & QN & NB & N8 & OUT & QO & OB & O8 & NO & ART0 & MI0 & ST0 & LOR & Q16 & FRB & CRB & LVB).
    intros T cc [Hc FC0] Hk.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' (D8 & DF & DL & DS & DT) LOW0 [HL HT]].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    pose proof (zlength_nonneg ptr) as ZL.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    pose proof TY as TY'. unfold ty in TY'. pose proof (ttype_range _ _ TY' ltac:(unfold t_arr; lia) ltac:(unfold t_arr; lia)) as TIR.
    pose proof (arr_node_elem (ae_T E) (ae_S E) (ae_sn E) d i e c TY' NXT CLOSE TILES ltac:(lia)) as ELI.
    assert (ARR208 : ae_lo E + 65856 <= q) by ul.
    assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (arr_W q out)) by (intros Σx; apply fp_client_stack2; ul).
    assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) (arr_WO out)) by (intros Σx; apply fp_client_stack1; ul).
    assert (ARTW : forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> ART RT Σ m').
    { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m m' ART0 LV (FPW Σ) MU WM). }
    assert (HWlo : Forall (fun r => ae_lo E <= fst r) (arr_W q out)) by (unfold arr_W; constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]).
    assert (HWOlo : Forall (fun r => ae_lo E <= fst r) (arr_WO out)) by (unfold arr_WO; constructor; [cbn; lia| constructor]).
    assert (SHZN : forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' node 16).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' node 16 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZO : forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' out 24).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' out 24 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZD : forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16).
    { intros m' MU WM. apply (lvl_shz_doc E OK). exact (AINV_A_munch E _ m m' OK AI MU HWlo). }
    assert (SHZT : forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
    { intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ m' (ARTW m' MU WM) LV). }
    assert (SHZF : forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' (q + -96) 96).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' (q + -96) 96 (ARTW m' MU WM) LV); first [lia | reflexivity | Z.div_mod_to_equations; lia]. }
    assert (ACCP : ptr <> [] -> forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> acc bsegs m' (ae_PB E) (ae_NPB E)).
    { intros NE m' MU WM. exact (lvl_acc_ptr RT AF E Σ m' P ptr (ARTW m' MU WM) LV PAT NE). }
    pose proof (shb_cells_of_art RT AF Σ m ART0) as SHB.
    assert (EU : bv_unsigned (Z_to_bv 64 (q + -96)) = q + -96) by (apply unsigned_lit; ul).
    assert (EU192 : bv_unsigned (Z_to_bv 64 (q + -192)) = q + -192) by (apply unsigned_lit; ul).
    assert (Q16' : (q + -96) mod 16 = 0) by (replace (q + -96) with (q + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (Q16'' : (q + -192) mod 16 = 0) by (replace (q + -192) with (q + (-12) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (CST0 : 0 <= arr_costA d (zlength ptr)) by (unfold arr_costA, LVL_C1, DCOST; lia).
    pose proof (munch_refl (arr_W q out) m) as MU0. pose proof (wmono_refl bsegs m) as WM0.

    set (KP := arr_KP RT E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (arr_costA d (zlength ptr))).
    enough (AE : aevt RT PMc Σ KP (lvl_entry ATP_ARR_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m))
      by (exact (AE T cc Hc Hk)).
    pose proof (arr_finA RT E Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q out (arr_costA d (zlength ptr)) m) as FIN. fold KP in FIN.
    apply (aevt_evt RT AF PMc MST).
    eapply (arr_walk1 E OK _ ptr i e c q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
              PAT TY I0 ltac:(lia) AI NODE QN NB OUT QO OB O8 NO MI0 ST0 ltac:(ul) Q16 SHB SHZN SHZO SHZF ACCP).
    -
      intros m1 y5 y6 y7 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 jr E0 MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
      pose proof (ARTW m1 MU1 WM1) as ART1. pose proof (AINV_A_munch E _ m m1 OK AI MU1 HWlo) as AI1.
      pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -208) q [(out, out + 24)] m m1 ART0 LV ltac:(lia) MU1) as PFP1.
      assert (NODE1 : rw_cells bsegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)]).
      { unfold arr_W in MU1. exact (rw_cells_transport bsegs _ m m1 _ _ NODE MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)). }
      set (nbs := le8 (Z_to_bv 64 (ae_DOC E)) ++ le8 (Z_to_bv 64 i)).
      assert (LNB : length nbs = 16%nat) by (subst nbs; rewrite length_app, !length_le8; reflexivity).
      assert (NODEB : bytes_at bsegs m1 node nbs).
      { pose proof (rw_cells_bytes_at bsegs m1 node _ NODE1) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
      assert (CSRC : checked_src RT Σ m1 (Z_to_bv 64 (q + -96)) (ae_lo E) node (Z.of_nat (length nbs))).
      { rewrite LNB. apply (checked_src_stack RT AF Σ m1 _ (ae_lo E) node 16 ART1); [ul| ul| rewrite EU; lia]. }
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -96)) out (Z.of_nat (length nbs))).
      { rewrite LNB. apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -96) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      eapply (aevt_memcpyP RT RC PMc FDO MST Σ KP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 out node nbs (ae_lo E));
        [reflexivity| reflexivity| rewrite LNB; reflexivity| ul| ul| rewrite LNB; cbn; lia| exact NODEB| exact CSRC| exact CDST| rewrite LNB; cbn; lia
        | exact ART1| exact MI1| exact COK1|].
      intros t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2.
      rewrite EU in ST2, PRES2. rewrite LNB in PRES2. change (Z.of_nat 16%nat) with 16 in PRES2.
      rewrite (ret_pc_even 0xb8df8) by (clear; lia).
      assert (FR2 : rw_cells bsegs m2 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 P) (Z_to_bv 64 0) jr)).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold arr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
      lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC nbs _ _ _ OUT1 eq_refl eq_refl BY2 LNB WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
      pose proof (lvl_shz_rec RT AF E OK Σ m2 out 24 ART2 LV ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO2.
      pose proof (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)) as AI2.
      apply (aevt_evt RT AF PMc MST).
      eapply (arr_after_cpy E OK _ m2 F2 fc q out ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [exact FR2| exact ST2| exact MI2| lia| exact OUT2| exact QO| exact OB| exact O8| exact SHZO2|].
      intros m3 y5' y6' y7' y10 y11 y12 y13 y14 y15 y16 y17 y28' y29' y30' y31' MU3 WM3 MI3 ST3 OUT3. unfold arr_WO in MU3.
      eapply FIN; [exact FRM| exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3)| exact MI3| exact ST3| | | | reflexivity| reflexivity| reflexivity| lia].
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * eapply (rt_pres_fp_of_ex _ _ (q + -96) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU3. exact Ho.
      + subst ptr. apply (out_recA_ok E m3 out i jC (S d) (e + 1)); [| exact ELI| exact I0| lia]. apply rec_node16. exact OUT3.
      + eapply (AINV_A_munch E _ m2 m3 OK); [exact AI2| exact MU3| exact HWOlo].
    -
      intros m1 ra' code' y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys5 y28 y29 y30 y31 jr' pw' lw' SITE MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
      pose proof (ARTW m1 MU1 WM1) as ART1. pose proof (AINV_A_munch E _ m m1 OK AI MU1 HWlo) as AI1.
      pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -208) q [(out, out + 24)] m m1 ART0 LV ltac:(lia) MU1) as PFP1.
      assert (CODE : code' = 17 \/ code' = 19 \/ code' = 22) by (clear - SITE; destruct SITE as [(_ & ->)|[(_ & -> & _)|(_ & _ & C)]]; [lia| lia| exact C]).
      assert (RAE : 0 <= ra' < 2^64 /\ ra' mod 2 = 0) by (clear - SITE; destruct SITE as [(-> & _)|[(-> & _)|(-> & _)]]; lia).
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -96)) out 16).
      { apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -96) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      eapply (aevt_memsetP RT RC PMc FDO MST Σ KP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 out 16 (Z_to_bv 8 0) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| ul| lia| exact CDST| exact ART1| exact MI1| exact COK1|].
      intros t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2.
      rewrite EU in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
      rewrite (ret_pc_even ra') by (clear - RAE; lia).
      assert (FR2 : rw_cells bsegs m2 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw' lw' jr')).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold arr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
      lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT1 eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
      pose proof (lvl_shz_rec RT AF E OK Σ m2 out 24 ART2 LV ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO2.
      pose proof (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)) as AI2.
      apply (aevt_evt RT AF PMc MST).
      eapply (arr_after_set E OK _ m2 F2 fc q out ra' code' ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw' lw' ys5 ys2 ys3);
        [exact FR2| exact ST2| exact MI2| lia| exact OUT2| exact QO| exact OB| exact O8| exact SHZO2| exact SITE|].
      intros m3 y5' y6' y7' y10 y11 y12 y13 y14 y15 y16 y17 y28' y29' y30' y31' MU3 WM3 MI3 ST3 OUT3. unfold arr_WO in MU3.
      eapply FIN; [exact FRM| exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3)| exact MI3| exact ST3| | | | reflexivity| reflexivity| reflexivity| lia].
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * eapply (rt_pres_fp_of_ex _ _ (q + -96) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU3. exact Ho.
      + replace (repeat (Z_to_bv 8 0) 16) with (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) in OUT3 by reflexivity.
        apply (out_recA_err E m3 out (Z_to_bv 64 0) 0 code' jC); [apply rec_node16; exact OUT3| clear - CODE; lia].
      + eapply (AINV_A_munch E _ m2 m3 OK); [exact AI2| exact MU3| exact HWOlo].
    -
      intros m1 c1 ptr1 tok y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys3 y28 y29 y30 y31 jr Eptr TOK MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
      apply (arr_tokA RT AF RC E OK d HELEM Σ PMc ptr i e c q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo m1 c1 ptr1 tok
               y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys3 y28 y29 y30 y31 jr FDO MST LV AI PAT TY NXT CLOSE TILES I0 EN PRE0 FRM Eptr TOK MU1 WM1 MI1 ST1 FR1 OUT1).
  Qed.
End ArrLevel.
