(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow Zcn.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Zqc
     Z45 Z5k Z60 Z3v Z3t Z3x Z3y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ArrTok.
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

  Definition arr_KP (Σ : rts RT) (PMc : Model -> Prop) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (out : Z) (m : mem) (cost : Z) : config -> Prop :=
    fun cf => lvl_postA RT E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m cost cf /\ cfrm0 cf.

  Lemma arr_finA : forall (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q out cost : Z) (m : mem)
      (Σ' : rts RT) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
    rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m' -> out_recA E m' out -> AINV_A E m' ->
    rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - cost <= rt_credit RT Σ' ->
    aevt RT PMc Σ' (arr_KP Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m cost)
         (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)).
  Proof.
    intros until y31. intros FRM' HA MI ST PR OREC AI' E1 E2 E3 CR. apply (aevt_done RT PMc). intros cf Hcf. unfold arr_KP. split.
    - eapply (lvl_postA_intro RT E Σ Σ' PMc cf); [exact Hcf| exact HA| exact MI| exact ST| exact PR| exact OREC| exact AI'| exact E1| exact E2| exact E3| exact CR].
    - apply (cfrm0_of_asta RT Σ' PMc _ cf Hcf). intros ms <-. exact FRM'.
  Qed.

  Lemma arr_tokA : forall (Σ : rts RT) PMc (ptr : list Z) (i e c : Z) (q out node P : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte)
      (m1 : mem) (c1 : Z) (ptr1 : list Z) (tok : Z) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys3 y28 y29 y30 y31 : word) (jr : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m -> ptr_atA E P ptr ->
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> ae_T E e = tword t_arr_end i ->
    tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    lvl_pre RT E Σ m q out node i jo (arr_needA d) (arr_costA d (zlength ptr)) d -> frm0 fc ->
    ptr = 47 :: c1 :: ptr1 -> 0 <= tok <= zlength ptr1 + 1 ->
    munch (arr_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
    rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (zlength ptr1 + 1)) jr) -> rw_cells bsegs m1 out [CB 24 jo] ->
    aevt RT PMc Σ (arr_KP Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (arr_costA d (zlength ptr)))
         (MS (mkR (Z_to_bv 64 0x9a330) (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) y5 y6 y7 (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 (q + -96)) (Z_to_bv 64 node) (Z_to_bv 64 16)
                  ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 tok) ys3 (Z_to_bv 64 2147450880) (Z_to_bv 64 22) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (Z_to_bv 64 e_asan_memcpy) fc None m1 (seg_rom bsegs)).
  Proof using AF RC OK HELEM.
    intros until jr. intros FDO MST LV AI PAT TY NXT CLOSE TILES I0 EN PRE FRM Eptr TOK MU1 WM1 MI1 ST1 FR1 OUT1.
    destruct PRE as (NODE & QN & NB & N8 & OUT & QO & OB & O8 & NO & ART0 & MI0 & ST0 & LOR & Q16 & FRB & CRB & LVB).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' (D8 & DF & DL & DS & DT) LOW0 [HL HT]].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    pose proof (zlength_nonneg ptr) as ZL.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    pose proof TY as TY'. unfold ty in TY'. pose proof (ttype_range _ _ TY' ltac:(unfold t_arr; lia) ltac:(unfold t_arr; lia)) as TIR.
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
    set (KP := arr_KP Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (arr_costA d (zlength ptr))).
    pose proof (arr_finA Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q out (arr_costA d (zlength ptr)) m) as FIN. fold KP in FIN.

    clear N8 D8 DF DL DS DT T16 NT8 TN TS TL SBS P1 P1L P0' PTRR HSN NR IE CC TIR TY' SHZN SHZD SHZT MU0 WM0.
    pose proof (ARTW m1 MU1 WM1) as ART1. pose proof (AINV_A_munch E _ m m1 OK AI MU1 HWlo) as AI1.
    pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -208) q [(out, out + 24)] m m1 ART0 LV ltac:(lia) MU1) as PFP1.
    assert (NE : ptr <> []) by (rewrite Eptr; discriminate).
    pose proof (lvl_ptr_range E OK P ptr PAT NE) as (PB0 & PB1 & PB2 & PB3). rewrite Eptr, !zlength_cons in PB2.
    pose proof (zlength_nonneg ptr1) as ZL1. assert (ZLE : zlength ptr = zlength ptr1 + 1 + 1) by (rewrite Eptr, !zlength_cons; reflexivity).
    assert (NODE1 : rw_cells bsegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)]).
    { unfold arr_W in MU1. exact (rw_cells_transport bsegs _ m m1 _ _ NODE MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)). }
    set (nbs := le8 (Z_to_bv 64 (ae_DOC E)) ++ le8 (Z_to_bv 64 i)).
    assert (LNB : length nbs = 16%nat) by (subst nbs; rewrite length_app, !length_le8; reflexivity).
    assert (NODEB : bytes_at bsegs m1 node nbs).
    { pose proof (rw_cells_bytes_at bsegs m1 node _ NODE1) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
    clear NO NODE NODE1.
    destruct (arr_frame_split m1 q ra s0 s1 s2 s3 s4 s5 _ _ jr FR1) as [FRr1 FRt1].
    assert (CSRC : checked_src RT Σ m1 (Z_to_bv 64 (q + -96)) (ae_lo E) node (Z.of_nat (length nbs))).
    { rewrite LNB. apply (checked_src_stack RT AF Σ m1 _ (ae_lo E) node 16 ART1); [ul| ul| rewrite EU; lia]. }
    assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -96)) (q + -96) (Z.of_nat (length nbs))).
    { rewrite LNB. apply (checked_dst_stack RT AF Σ m1 _ (q + -96) 16 ART1); [ul| ul| rewrite EU; lia|].
      apply (wr_at_sub m1 (q + -96) 24 (q + -96) 16); [| lia| lia| lia]. exact (proj2 FRr1). }
    pose proof (call_ok_lvl RT E OK Σ m1 (q + -96) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ KP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (q + -96) node nbs (ae_lo E));
      [reflexivity| reflexivity| rewrite LNB; reflexivity| ul| ul| rewrite LNB; cbn; lia| exact NODEB| exact CSRC| exact CDST| rewrite LNB; cbn; lia
      | exact ART1| exact MI1| exact COK1|].
    intros t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2.
    rewrite EU in ST2, PRES2. rewrite LNB in PRES2. change (Z.of_nat 16%nat) with 16 in PRES2.
    rewrite (ret_pc_even 0x9a330) by (clear; lia).
    assert (AG2 : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (q + -96) x /\ ~ (q + -96 <= x < q + -96 + 16)) m1 m2).
    { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. exact Hx. }
    assert (FRt2 : rw_cells bsegs m2 (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (zlength ptr1 + 1)))).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FRt1). eapply agree_sub; [exact AG2|]. intros x Hx. unfold arr_ftail in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
    assert (OUT2 : rw_cells bsegs m2 out [CB 24 jo]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ OUT1). eapply agree_sub; [exact AG2|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
    apply (rw_cells_split_CB bsegs _ _ [] 24 jr [] [16; 8]%nat) in FRr1; [| reflexivity]. cbn [mk_CB_cells app] in FRr1.
    lazymatch type of FRr1 with rw_cells _ _ _ [CB 16 ?xa; CB 8 ?xb] => set (jA := xa) in FRr1; set (j8 := xb) in FRr1 end. clearbody jA j8.
    apply (proj1 (rw_cells_app bsegs m1 _ [_] _)) in FRr1. destruct FRr1 as [FRa1 FRb1]. cbn [cells_size csize Nat.add] in FRb1.
    replace (q + -96 + Z.of_nat 16) with (q + -80) in FRb1 by lia.
    assert (FRb2 : rw_cells bsegs m2 (q + -80) [CB 8 j8]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FRb1). eapply agree_sub; [exact AG2|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
    assert (NODE16 : rw_cells bsegs m2 (q + -96) [CB 16 nbs]).
    { rewrite <- LNB. apply rw_cells_CB_intro; [exact BY2|]. rewrite LNB. exact (wr_at_transport bsegs m1 m2 _ _ (proj2 FRa1) WM2). }
    assert (FRn2 : rw_cells bsegs m2 (q + -96) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i); CB 8 j8]).
    { apply rec_node16. change (CB 16 (le8 (Z_to_bv 64 (ae_DOC E)) ++ le8 (Z_to_bv 64 i)) :: [CB 8 j8]) with ([CB 16 nbs] ++ [CB 8 j8]).
      apply (proj2 (rw_cells_app bsegs m2 _ [CB 16 nbs] _)). split; [exact NODE16|]. cbn [cells_size csize Nat.add].
      replace (q + -96 + Z.of_nat 16) with (q + -80) by lia. exact FRb2. }
    apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [8; 8; 4; 4]%nat) in OUT2; [| reflexivity]. cbn [mk_CB_cells app] in OUT2.
    lazymatch type of OUT2 with rw_cells _ _ _ [CB 8 ?xa; CB 8 ?xb; CB 4 ?xc; CB 4 ?xd] =>
      set (oa := xa) in OUT2; set (ob := xb) in OUT2; set (oc := xc) in OUT2; set (od := xd) in OUT2 end. clearbody oa ob oc od.
    pose proof (AINV_A_pres_ex RT Σ E _ (q + -96) 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)) as AI2.
    pose proof (munch_refl (arr_W q out) m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2'.
    assert (ARTW2 : forall m', munch (arr_W q out) m2 m' -> wmono bsegs m2 m' -> ART RT Σ m').
    { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m2 m' ART2 LV (FPW Σ) MU WM). }
    assert (PFP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m2).
    { eapply rt_pres_fp_trans; [exact PFP1|].
      exact (rt_pres_fp_of_ex_lower RT AF E Σ m (q + -96) q (q + -96) 16 [(out, out + 24)] m1 m2 ART0 LV ltac:(lia) ltac:(lia) ltac:(lia) PRES2). }
    apply (aevt_evt RT AF PMc MST).
    eapply (arr_walk2 E OK d _ m2 m2 F2 fc i e c q out node P tok (zlength ptr1 + 1) ys3 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j8 oa ob oc od);
      [ exact TY| exact NXT| exact TILES| exact I0| exact EN| exact TOK| lia| ul| exact MU2| exact WM2'| exact MI2| exact ST2| ul| exact Q16
      | exact FRn2| exact FRt2| exact OUT2| exact QO| exact OB| exact O8
      | intros m' MU WM; exact (AINV_A_munch E _ m2 m' OK AI2 MU HWlo)
      | intros m' MU WM; exact (shb_cells_of_art RT AF Σ m' (ARTW2 m' MU WM))
      | intros m' MU WM; apply (lvl_shz_doc E OK); exact (AINV_A_munch E _ m2 m' OK AI2 MU HWlo)
      | intros m' MU WM; exact (lvl_shz_tape RT AF E OK Σ m' (ARTW2 m' MU WM) LV)
      | intros m' MU WM; apply (lvl_shz_rec RT AF E OK Σ m' (q + -96) 96 (ARTW2 m' MU WM) LV); first [lia | reflexivity | Z.div_mod_to_equations; lia]
      | intros m' MU WM; apply (lvl_shz_rec RT AF E OK Σ m' out 24 (ARTW2 m' MU WM) LV); first [lia | reflexivity]
      | | | ].
    +
      intros m3 z5 z6 z7 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs7 zs8 zs9 z28 z29 z30 z31 j0 jr3 MU3 WM3 MI3 ST3 FRA3 FR3 OUT3. apply evt_done.
      pose proof (ARTW2 m3 MU3 WM3) as ART3. pose proof (AINV_A_munch E _ m2 m3 OK AI2 MU3 HWlo) as AI3.
      pose proof (rt_pres_fp_of_munch RT AF E Σ m2 (q + -208) q [(out, out + 24)] m2 m3 ART2 LV ltac:(lia) MU3) as PFP3.
      assert (CDST3 : checked_dst RT Σ m3 (Z_to_bv 64 (q + -192)) out 16).
      { apply (checked_dst_stack RT AF Σ m3 _ out 16 ART3); [ul| ul| rewrite EU192; lia|].
        apply (wr_at_sub m3 out 24 out 16); [| lia| lia| lia]. pose proof (proj2 OUT3) as X. cbn [cells_size csize Nat.add] in X. exact X. }
      pose proof (call_ok_lvl RT E OK Σ m3 (q + -192) LV ST3 ltac:(ul) ltac:(ul) Q16'') as COK3.
      eapply (aevt_memsetP RT RC PMc FDO MST Σ KP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m3 out 16 (Z_to_bv 8 0) (ae_lo E));
        [reflexivity| reflexivity| reflexivity| ul| lia| exact CDST3| exact ART3| exact MI3| exact COK3|].
      intros t0'' t1'' t2'' g1 g2 g3 g4 g5 g6 g7 t3'' t4'' t5'' t6'' F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4.
      rewrite EU192 in ST4, PRES4. change (Z.to_nat 16) with 16%nat in BY4.
      rewrite (ret_pc_even 0x9abb4) by (clear; lia).
      assert (AG4 : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (q + -192) x /\ ~ (out <= x < out + 16)) m3 m4).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4). intros x Hx. exact Hx. }
      assert (FRA4 : rw_cells bsegs m4 (q + -192) (arrat_frame (Z_to_bv 64 0x9a340) (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 tok) ys3 (Z_to_bv 64 2147450880) (Z_to_bv 64 22) s6 s7 s8 s9 j0)).
      { apply (rw_cells_agree_nw bsegs m3 m4 _ _ FRA3). eapply agree_sub; [exact AG4|]. intros x Hx. unfold arrat_frame in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
      assert (FR4 : rw_cells bsegs m4 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (zlength ptr1 + 1)) jr3)).
      { apply (rw_cells_agree_nw bsegs m3 m4 _ _ FR3). eapply agree_sub; [exact AG4|]. intros x Hx. unfold arr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
      pose proof (rec_copy16 m3 m4 out [CB 8 oa; CB 8 ob] (CB 4 oc) od (repeat (Z_to_bv 8 0) 16) _ _ _ OUT3 eq_refl eq_refl BY4 eq_refl WM4 PRES4 ltac:(lia) ltac:(ul)) as OUT4.
      pose proof (AINV_A_pres_ex RT Σ E _ out 16 m3 m4 LV OK AI3 PRES4 ltac:(lia)) as AI4.
      assert (SHZO4 : forall m', munch (arr_WO out) m4 m' -> wmono bsegs m4 m' -> shz m' out 24).
      { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' out 24 (lvl_art_munch RT AF E Σ _ m4 m' ART4 LV (FPO Σ) MU WM) LV); first [lia | reflexivity]. }
      apply (aevt_evt RT AF PMc MST).
      eapply (arr_after_aset E OK _ m4 F4 fc q out node tok ys3 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
        [exact FRA4| exact FR4| exact ST4| exact MI4| ul| exact OUT4| exact QO| exact OB| exact O8| exact SHZO4|].
      intros m5 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU5 WM5 MI5 ST5 OUT5. unfold arr_WO in MU5.
      eapply FIN; [exact FRM| exact (lvl_art_munch RT AF E Σ _ m4 m5 ART4 LV (FPO Σ) MU5 WM5)| exact MI5| exact ST5| | | | reflexivity| reflexivity| reflexivity| lia].
      * eapply rt_pres_fp_trans; [exact PFP2|]. eapply rt_pres_fp_trans; [exact PFP3|]. eapply rt_pres_fp_trans.
        -- eapply (rt_pres_fp_of_ex _ _ (q + -192) q out 16); [exact PRES4| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        -- intros a Ha Ho. apply MU5. exact Ho.
      * replace (repeat (Z_to_bv 8 0) 16) with (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) in OUT5 by reflexivity.
        apply (out_recA_err E m5 out (Z_to_bv 64 0) 0 19 od); [apply rec_node16; exact OUT5| lia].
      * eapply (AINV_A_munch E _ m4 m5 OK); [exact AI4| exact MU5| exact HWOlo].
    +
      intros m3 it j' z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU3 WM3 MI3 ST3 EL IT0 JE OUT3.
      eapply FIN; [exact FRM| exact (ARTW2 m3 MU3 WM3)| exact MI3| exact ST3| | | exact (AINV_A_munch E _ m2 m3 OK AI2 MU3 HWlo)| reflexivity| reflexivity| reflexivity| lia].
      * eapply rt_pres_fp_trans; [exact PFP2|]. exact (rt_pres_fp_of_munch RT AF E Σ m2 (q + -208) q [(out, out + 24)] m2 m3 ART2 LV ltac:(lia) MU3).
      * exact (out_recA_ok E m3 out it od d j' OUT3 EL IT0 ltac:(lia)).
    +
      intros m3 it j' z5 z6 z7 za4 za5 za6 za7 z28 z29 z30 z31 jr3 TOKL MU3 WM3 MI3 ST3 EL IT0 JE FR3 OUT3. apply evt_done.
      pose proof (ARTW2 m3 MU3 WM3) as ART3. pose proof (AINV_A_munch E _ m2 m3 OK AI2 MU3 HWlo) as AI3.
      pose proof (rt_pres_fp_of_munch RT AF E Σ m2 (q + -208) q [(out, out + 24)] m2 m3 ART2 LV ltac:(lia) MU3) as PFP3.
      set (ptr' := skipn (Z.to_nat tok) (c1 :: ptr1)).
      assert (TKN : (Z.to_nat tok <= length (c1 :: ptr1))%nat) by (unfold zlength in TOKL, TOK; cbn [length] in *; lia).
      assert (ZL' : zlength ptr' = zlength ptr1 + 1 - tok).
      { subst ptr'. rewrite zlength_skipn by exact TKN. rewrite zlength_cons. lia. }
      assert (PAT' : ptr_atA E (P + 1 + tok) ptr').
      { subst ptr'. pose proof (ptr_atA_skip E P ptr (S (Z.to_nat tok)) PAT ltac:(rewrite Eptr; cbn [length] in *; lia)) as X.
        rewrite Eptr in X. change (skipn (S (Z.to_nat tok)) (47 :: c1 :: ptr1)) with (skipn (Z.to_nat tok) (c1 :: ptr1)) in X.
        replace (P + Z.of_nat (S (Z.to_nat tok))) with (P + 1 + tok) in X by lia. exact X. }
      assert (CST : elem_costA d (zlength ptr') <= arr_costA d (zlength ptr)) by (unfold elem_costA, arr_costA; rewrite ZL', ZLE; lia).
      pose proof OUT3 as OUT3'. change [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 0); CB 4 od]
        with ([C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 it)] ++ [C4 (Z_to_bv 64 0); CB 4 od]) in OUT3'.
      apply (proj1 (rw_cells_app bsegs m3 _ _ _)) in OUT3'. destruct OUT3' as [NODEC3 OUTT3]. cbn [cells_size csize Nat.add] in OUTT3.
      destruct (arr_frame_split m3 q ra s0 s1 s2 s3 s4 s5 _ _ jr3 FR3) as [FRr3 FRt3].
      assert (PRE' : lvl_pre RT E Σ m3 (q + -96) (q + -96) out it jr3 (elem_needA d) (elem_costA d (zlength ptr')) d).
      { unfold lvl_pre. split; [exact NODEC3|]. split; [lia|]. split; [lia|]. split; [exact O8|].
        split; [exact FRr3|]. split; [lia|]. split; [lia|]. split; [clear - Q16; Z.div_mod_to_equations; lia|]. split; [right; lia|].
        split; [exact ART3|]. split; [exact MI3|]. split; [exact ST3|]. split; [ul|]. split; [exact Q16'|].
        split; [exact FRB|]. split; [lia| exact LVB]. }
      eapply (aevt_rt RT PMc Σ _ _ _); [| exact FRM|].
      { rewrite <- ZL'. exact (HELEM Σ PMc ptr' it j' (q + -96) (q + -96) out (P + 1 + tok) (Z_to_bv 64 0x9a41c) gp z5 z6 z7 (Z_to_bv 64 out) (Z_to_bv 64 (out + 16))
                                     za4 za5 za6 za7 (Z_to_bv 64 0) ys3 (Z_to_bv 64 ((out + 16) / 8 + 2147450880)) (Z_to_bv 64 22) s6 s7 s8 s9 s10 s11 z28 z29 z30 z31
                                     F2 fc m3 jr3 FDO MST LV AI3 PAT' EL IT0 ltac:(lia) PRE' FRM). }
      intros cf (Σ1 & HA & LV1 & FRS1 & SP1 & CR1). eexists Σ1, _. split; [exact HA|].
      intros ms' (v & m4 & RS & (ART4 & MI4 & ST4) & PFP & OREC & AI4) FRM4.
      destruct RS as (u0 & u1 & u2 & a1' & a2' & a3' & a4'' & a5'' & a6'' & a7'' & u3 & u4 & u5 & u6 & F4 & fc4 & ->). cbn in FRM4.
      rewrite (ret_pc_even 0x9a41c) by (clear; lia). rewrite ZL' in CR1, CST.
      assert (LVx : a_live RT Σ1 E) by (exact (a_live_eq RT Σ Σ1 E LV LV1 FRS1 SP1)).

      assert (AG : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (q + -96) x /\ ~ (q + -96 <= x < q + -72)) m3 m4).
      { intros a [Ha Hn]. apply PFP; [exact Ha|]. cbn [outside]. split; [lia| exact Logic.I]. }
      assert (FRt4 : rw_cells bsegs m4 (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (zlength ptr1 + 1)))).
      { apply (rw_cells_agree_nw bsegs m3 m4 _ _ FRt3). eapply agree_sub; [exact AG|]. intros x Hx. unfold arr_ftail in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
      assert (OUT4 : rw_cells bsegs m4 out [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 0); CB 4 od]).
      { apply (rw_cells_agree_nw bsegs m3 m4 _ _ OUT3). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
      destruct OREC as (r0 & jj & code & jn & RREC & CODE & SUCC).
      assert (PFP4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m m4).
      { eapply rt_pres_fp_trans; [exact PFP2|]. eapply rt_pres_fp_trans; [exact PFP3|].
        exact (rt_pres_fp_lower RT AF E Σ m3 (q + -96) q (q + -96) (q + -96 + 24) [(out, out + 24)] m3 m4 ART3 LV ltac:(lia) ltac:(lia) ltac:(lia) PFP). }

      apply (aevt_evt RT AF PMc MST). apply (arr_rec_glue _ m4 F4 fc4 q out); [exact MI4| ul| ul|].

      set (bs := le8 r0 ++ le8 (Z_to_bv 64 jj)).
      assert (LBS : length bs = 16%nat) by (subst bs; rewrite length_app, !length_le8; reflexivity).
      pose proof RREC as RREC'. change [C8 r0; C8 (Z_to_bv 64 jj); C4 (Z_to_bv 64 code); CB 4 jn] with ([C8 r0; C8 (Z_to_bv 64 jj)] ++ [C4 (Z_to_bv 64 code); CB 4 jn]) in RREC'.
      apply (proj1 (rw_cells_app bsegs m4 _ _ _)) in RREC'. destruct RREC' as [RREC16 _].
      assert (RB : bytes_at bsegs m4 (q + -96) bs).
      { pose proof (rw_cells_bytes_at bsegs m4 _ _ RREC16) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
      assert (CSRC4 : checked_src RT Σ1 m4 (Z_to_bv 64 (q + -96)) (ae_lo E) (q + -96) (Z.of_nat (length bs))).
      { rewrite LBS. apply (checked_src_stack RT AF Σ1 m4 _ (ae_lo E) (q + -96) 16 ART4); [rewrite SP1; ul| ul| rewrite EU; lia]. }
      assert (CDST4 : checked_dst RT Σ1 m4 (Z_to_bv 64 (q + -96)) out (Z.of_nat (length bs))).
      { rewrite LBS. apply (checked_dst_stack RT AF Σ1 m4 _ out 16 ART4); [rewrite SP1; ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m4 out 24 out 16); [| lia| lia| lia]. pose proof (proj2 OUT4) as X. cbn [cells_size csize Nat.add] in X. exact X. }
      pose proof (call_ok_lvl RT E OK Σ1 m4 (q + -96) LVx ST4 ltac:(ul) ltac:(ul) Q16') as COK4.
      eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 KP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 out (q + -96) bs (ae_lo E));
        [reflexivity| reflexivity| rewrite LBS; reflexivity| ul| ul| rewrite LBS; cbn; lia| exact RB| exact CSRC4| exact CDST4| rewrite LBS; cbn; lia
        | exact ART4| exact MI4| exact COK4|].
      intros t0'' t1'' t2'' g1 g2 g3 g4 g5 g6 g7 t3'' t4'' t5'' t6'' F5 m5 (ART5 & MI5 & WM5 & ST5) PRES5 BY5.
      rewrite EU in ST5, PRES5. rewrite LBS in PRES5. change (Z.of_nat 16%nat) with 16 in PRES5.
      rewrite (ret_pc_even 0x9a42c) by (clear; lia).
      assert (AG5 : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (q + -96) x /\ ~ (out <= x < out + 16)) m4 m5).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES5). intros x Hx. exact Hx. }
      assert (RREC5 : rw_cells bsegs m5 (q + -96) [C8 r0; C8 (Z_to_bv 64 jj); C4 (Z_to_bv 64 code); CB 4 jn]).
      { apply (rw_cells_agree_nw bsegs m4 m5 _ _ RREC). eapply agree_sub; [exact AG5|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
      assert (FRt5 : rw_cells bsegs m5 (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (zlength ptr1 + 1)))).
      { apply (rw_cells_agree_nw bsegs m4 m5 _ _ FRt4). eapply agree_sub; [exact AG5|]. intros x Hx. unfold arr_ftail in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| lia]. }
      pose proof (rec_copy16 m4 m5 out [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 it)] (C4 (Z_to_bv 64 0)) od bs _ _ _ OUT4 eq_refl eq_refl BY5 LBS WM5
                    PRES5 ltac:(lia) ltac:(ul)) as OUT5.
      pose proof (lvl_shz_rec RT AF E OK Σ1 m5 out 24 ART5 LVx ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO5.
      pose proof (AINV_A_pres_ex RT Σ1 E _ out 16 m4 m5 LVx OK AI4 PRES5 ltac:(lia)) as AI5.
      apply (aevt_evt RT AF PMc MST).
      eapply (arr_after_rec E OK _ m5 F5 fc4 q out code ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ r0 (Z_to_bv 64 jj) jn bs od);
        [exact RREC5| exact FRt5| exact ST5| exact MI5| lia| exact OUT5| exact QO| exact OB| exact O8| exact SHZO5| exact CODE|].
      intros m6 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU6 WM6 MI6 ST6 OUT6. unfold arr_WO in MU6.
      eapply FIN; [exact FRM4| exact (lvl_art_munch RT AF E Σ1 _ m5 m6 ART5 LVx (FPO Σ1) MU6 WM6)| exact MI6| exact ST6| | | | exact LV1| exact FRS1| exact SP1| clear - CR1 CST; lia].
      * eapply rt_pres_fp_trans; [exact PFP4|]. eapply rt_pres_fp_trans.
        -- eapply (rt_pres_fp_of_ex _ _ (q + -96) q out 16); [rewrite <- LV1, <- FRS1; exact PRES5| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        -- intros a Ha Ho. apply MU6. exact Ho.
      * exists r0, jj, code, od. split; [apply rec_node16; exact OUT6|]. split; [exact CODE| exact SUCC].
      * eapply (AINV_A_munch E _ m5 m6 OK); [exact AI5| exact MU6| exact HWOlo].
  Qed.
End ArrTok.
