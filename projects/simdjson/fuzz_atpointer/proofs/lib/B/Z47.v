(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow Zcn.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Z45 Z5k Z48 Z49.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma memchr_chk_le : forall c n buf, 0 <= n -> memchr_chk c n buf <= n.
Proof.
  intros c n buf Hn. unfold memchr_chk. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [ix|] eqn:FB; [| lia].
  pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.
Lemma memchr_chk_nonneg : forall c n buf, 0 <= n -> 0 <= memchr_chk c n buf.
Proof. intros c n buf Hn. unfold memchr_chk. destruct (find_byte c (firstn (Z.to_nat n) buf)); lia. Qed.
Lemma memchr_ok_all : forall A c (l : list Z), memchr_ok A c (zlength l) (map (Z_to_bv 8) l).
Proof.
  intros A c l. unfold memchr_ok, zlength. destruct (find_byte c (firstn (Z.to_nat (Z.of_nat (length l))) (map (Z_to_bv 8) l))); rewrite length_map; lia.
Qed.

Section ElemLevel.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HOBJ : forall d', d = S d' -> atp_obj_cpsA RT E d'.
  Hypothesis HARR : forall d', d = S d' -> atp_arr_cpsA RT E d'.

  Local Ltac ul := unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Theorem atp_elemA : atp_elem_cpsA RT E d.
  Proof using AF RC OK HOBJ HARR.
    intros Σ PMc ptr i j q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
      FDO MST LV AI PAT EL I0 JN PRE FRM.
    destruct PRE as (NODE & QN & NB & N8 & OUT & QO & OB & O8 & NO & ART0 & MI0 & ST0 & LOR & Q16 & FRB & CRB & LVB).
    intros T cc [Hc FC0] Hk.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' (D8 & DF & DL & DS & DT) LOW0 [HL HT]].
    pose proof LV as (LT & LS & LP & LF & LWIN).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
    pose proof (zlength_nonneg ptr) as ZL.
    assert (ELM64 : ae_lo E + 65600 <= q) by ul.
    assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (elem_W q out)) by (intros Σx; apply fp_client_stack2; ul).
    assert (FPO : forall Σx, fp_client RT Σx (ae_lo E) (elem_WO out)) by (intros Σx; apply fp_client_stack1; ul).
    assert (ARTW : forall m', munch (elem_W q out) m m' -> wmono bsegs m m' -> ART RT Σ m').
    { intros m' MU WM. exact (lvl_art_munch RT AF E Σ _ m m' ART0 LV (FPW Σ) MU WM). }
    assert (HWlo : Forall (fun r => ae_lo E <= fst r) (elem_W q out)) by (unfold elem_W; constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]).
    assert (HWOlo : Forall (fun r => ae_lo E <= fst r) (elem_WO out)) by (unfold elem_WO; constructor; [cbn; lia| constructor]).
    assert (SHZN : forall m', munch (elem_W q out) m m' -> wmono bsegs m m' -> shz m' node 16).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' node 16 (ARTW m' MU WM) LV); first [lia | reflexivity]. }
    assert (SHZD : forall m', munch (elem_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16).
    { intros m' MU WM. apply (lvl_shz_doc E OK). exact (AINV_A_munch E _ m m' OK AI MU HWlo). }
    assert (SHZT : forall m', munch (elem_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
    { intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ m' (ARTW m' MU WM) LV). }
    assert (ACCP : ptr <> [] -> forall m', munch (elem_W q out) m m' -> wmono bsegs m m' -> acc bsegs m' (ae_PB E) (ae_NPB E)).
    { intros NE m' MU WM. exact (lvl_acc_ptr RT AF E Σ m' P ptr (ARTW m' MU WM) LV PAT NE). }
    assert (SHZF : forall m', munch (elem_W q out) m m' -> wmono bsegs m m' -> shz m' (q + -64) 16).
    { intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ m' (q + -64) 16 (ARTW m' MU WM) LV); first [lia | reflexivity | Z.div_mod_to_equations; lia]. }
    pose proof (shb_cells_of_art RT AF Σ m ART0) as SHB.
    assert (EU : bv_unsigned (Z_to_bv 64 (q + -64)) = q + -64) by (apply unsigned_lit; ul).
    assert (EU80 : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; ul).
    assert (Q16'' : (q + -80) mod 16 = 0) by (replace (q + -80) with (q + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (Q16' : (q + -64) mod 16 = 0) by (replace (q + -64) with (q + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    assert (CST0 : 0 <= elem_costA d (zlength ptr)) by (unfold elem_costA, LVL_C1, DCOST; lia).

    pose proof (elem_walk1 E OK d ptr i j q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
                  PAT EL I0 JN AI NODE QN NB OUT QO OB O8 NO MI0 ST0 ltac:(lia) Q16 SHB SHZN SHZD SHZT SHZF ACCP) as W1.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ cc (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & jn & MU1 & WM1 & MI1 & OUT1 & X1) & Hc1'). clear Hc1.
    pose proof (ARTW m1 MU1 WM1) as ART1.
    pose proof (AINV_A_munch E _ m m1 OK AI MU1 HWlo) as AI1.
    pose proof (rt_pres_fp_of_munch RT AF E Σ m (q + -80) q [(out, out + 24)] m m1 ART0 LV ltac:(lia) MU1) as PFP1.
    assert (NODE1 : rw_cells bsegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)]).
    { apply (rw_cells_agree bsegs m m1 _ _ NODE); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold elem_W. cbn [outside]. repeat split; lia. }
    set (nbs := le8 (Z_to_bv 64 (ae_DOC E)) ++ le8 (Z_to_bv 64 i)).
    assert (LNB : length nbs = 16%nat) by (subst nbs; rewrite length_app, !length_le8; reflexivity).
    assert (NODEB : bytes_at bsegs m1 node nbs).
    { pose proof (rw_cells_bytes_at bsegs m1 node _ NODE1) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
    assert (CSRCN : checked_src RT Σ m1 (Z_to_bv 64 (q + -64)) (ae_lo E) node (Z.of_nat (length nbs))).
    { rewrite LNB. apply (checked_src_stack RT AF Σ m1 _ (ae_lo E) node 16 ART1); [ul| ul| rewrite EU; lia]. }

    destruct X1 as [XCPY|[XSET|[XCHR|XCHILD]]].
    -
      destruct XCPY as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ST1 & FR1 & -> & ->).
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -64) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -64)) out (Z.of_nat (length nbs))).
      { rewrite LNB. apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
      apply (rc_asan_memcpy RT RC Σ PMc (Z_to_bv 64 0x9772c) (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 out) (Z_to_bv 64 P)
               (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 16) a3' a4' a5' a6' a7' (Z_to_bv 64 0) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
               F fc m1 out node nbs (ae_lo E) FDO MST eq_refl eq_refl ltac:(rewrite LNB; reflexivity) ltac:(ul) ltac:(ul) ltac:(rewrite LNB; cbn; lia)
               NODEB CSRCN CDST ltac:(rewrite LNB; cbn; lia) ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU in ST2, PRES2. rewrite LNB in PRES2. change (Z.of_nat 16%nat) with 16 in PRES2.
      rewrite (ret_pc_even 0x9772c) in Hc2' by lia.
      assert (FR2 : rw_cells bsegs m2 (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn)).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold elem_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
      lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC nbs _ _ _ OUT1 eq_refl eq_refl BY2 LNB WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
      pose proof (lvl_shz_rec RT AF E OK Σ m2 out 24 ART2 LV ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO2.
      set (K2 := fun ms => exists (m3 : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F2 (ret_pc ra) fc None m3 (seg_rom bsegs)
        /\ munch (elem_WO out) m2 m3 /\ wmono bsegs m2 m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 (ae_lo E) q
        /\ rw_cells bsegs m3 out [CB 16 nbs; C4 (Z_to_bv 64 0); CB 4 jC]).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt bsegs K2 ms) end.
      { intros ms <-. eapply (elem_after_cpy E OK K2); [exact FR2| exact ST2| exact MI2| lia| exact OUT2| exact QO| exact OB| exact O8| exact SHZO2|].
        intros m' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU3 WM3 MI3 ST3 OUT3. subst K2. cbv beta.
        exists m', y5, y6, y7, y10, y11, y12, y13, y14, y15. exists y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3| exact OUT3]. }
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & X3 & Hc3'). clear Hc3. subst K2. cbv beta in X3.
      destruct X3 as (m3 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU3 & WM3 & MI3 & ST3 & OUT3).
      assert (OUT3' : out_recA E m3 out).
      { apply (out_recA_ok E m3 out i jC d j); [| exact EL| exact I0| exact JN]. apply rec_node16. exact OUT3. }
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3'). intros ms <-. exact FRM. }
      eapply (lvl_postA_intro RT E Σ Σ PMc c3); [exact Hc3'| | exact MI3| exact ST3| | exact OUT3'| | reflexivity| reflexivity| reflexivity| lia].
      + exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3).
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * eapply (rt_pres_fp_of_ex _ _ (q + -64) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU3. exact Ho.
      + eapply (AINV_A_munch E _ m2 m3 OK); [| exact MU3| exact HWOlo].
        exact (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)).
    -
      destruct XSET as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ST1 & FR1 & ->).
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -64) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -64)) out 16).
      { apply (checked_dst_stack RT AF Σ m1 _ out 16 ART1); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m1 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT1). }
      apply (rc_asan_memset RT RC Σ PMc (Z_to_bv 64 0x97760) (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 out) (Z_to_bv 64 (out + 16))
               (Z_to_bv 64 out) (Z_to_bv 64 0) (Z_to_bv 64 16) a3' a4' a5' a6' a7' (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
               F fc m1 out 16 (Z_to_bv 8 0) (ae_lo E) FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CDST ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
      rewrite (ret_pc_even 0x97760) in Hc2' by lia.
      assert (FR2 : rw_cells bsegs m2 (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn)).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2).
        intros x Hx. unfold elem_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT1; [| reflexivity]. cbn [mk_CB_cells app] in OUT1.
      lazymatch type of OUT1 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT1; set (jB := xb) in OUT1; set (jC := xc) in OUT1 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m1 m2 out [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT1 eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
      pose proof (lvl_shz_rec RT AF E OK Σ m2 out 24 ART2 LV ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO2.
      set (K2 := fun ms => exists (m3 : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F2 (ret_pc ra) fc None m3 (seg_rom bsegs)
        /\ munch (elem_WO out) m2 m3 /\ wmono bsegs m2 m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 (ae_lo E) q
        /\ rw_cells bsegs m3 out [CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 22); CB 4 jC]).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt bsegs K2 ms) end.
      { intros ms <-. eapply (elem_after_set E OK K2); [exact FR2| exact ST2| exact MI2| lia| exact OUT2| exact QO| exact OB| exact O8| exact SHZO2| left; split; reflexivity|].
        intros m' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU3 WM3 MI3 ST3 OUT3. subst K2. cbv beta.
        exists m', y5, y6, y7, y10, y11, y12, y13, y14, y15. exists y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3| exact OUT3]. }
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & X3 & Hc3'). clear Hc3. subst K2. cbv beta in X3.
      destruct X3 as (m3 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU3 & WM3 & MI3 & ST3 & OUT3).
      assert (OUT3' : out_recA E m3 out).
      { replace (repeat (Z_to_bv 8 0) 16) with (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) in OUT3 by reflexivity.
        apply (out_recA_err E m3 out (Z_to_bv 64 0) 0 22 jC); [| lia]. apply rec_node16. exact OUT3. }
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3'). intros ms <-. exact FRM. }
      eapply (lvl_postA_intro RT E Σ Σ PMc c3); [exact Hc3'| | exact MI3| exact ST3| | exact OUT3'| | reflexivity| reflexivity| reflexivity| lia].
      + exact (lvl_art_munch RT AF E Σ _ m2 m3 ART2 LV (FPO Σ) MU3 WM3).
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * eapply (rt_pres_fp_of_ex _ _ (q + -64) q out 16); [exact PRES2| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU3. exact Ho.
      + eapply (AINV_A_munch E _ m2 m3 OK); [| exact MU3| exact HWOlo].
        exact (AINV_A_pres_ex RT Σ E _ out 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)).
    -
      destruct XCHR as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ptr' & ST1 & FF1 & FR1 & Ejn & -> & ->).
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -80) LV ST1 ltac:(ul) ltac:(ul) Q16'') as COK1.
      assert (NE : 47 :: ptr' <> []) by discriminate.
      pose proof (lvl_ptr_range E OK P _ PAT NE) as (PB0 & PB1 & PB2 & PB3).
      pose proof (lvl_live_ptr RT E Σ P _ LV PAT NE) as INPB.
      pose proof (ptr_atA_facts E P _ m1 OK PAT (proj1 (proj2 (proj2 AI1)))) as (PTRB1 & PTRF & PP0 & PP1 & PL).
      pose proof (zlength_nonneg ptr') as ZL'. rewrite zlength_cons in *.
      set (buf := map (Z_to_bv 8) (47 :: ptr')) in *.
      assert (LBUF : Z.of_nat (length buf) = zlength ptr' + 1) by (subst buf; rewrite length_map; unfold zlength; cbn [length]; lia).
      pose proof (memchr_chk_le 126 (zlength ptr' + 1) buf ltac:(lia)) as CHK1. pose proof (memchr_chk_nonneg 126 (zlength ptr' + 1) buf ltac:(lia)) as CHK0.
      assert (MOK : memchr_ok P 126 (zlength ptr' + 1) buf).
      { pose proof (memchr_ok_all P 126 (47 :: ptr')) as X. rewrite zlength_cons in X. exact X. }
      assert (CSRC : checked_src RT Σ m1 (Z_to_bv 64 (q + -80)) (ae_lo E) P (memchr_chk 126 (zlength ptr' + 1) buf)).
      { apply (checked_src_live RT AF Σ m1 _ (ae_lo E) (ae_PB E) (ae_NPB E) P _ ART1 INPB); [lia| lia| exact LWIN]. }
      apply (rc_memchr RT RC Σ PMc (Z_to_bv 64 0x9a564) (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 P)
               (Z_to_bv 64 P) (Z_to_bv 64 126) (Z_to_bv 64 (zlength ptr' + 1)) a3' a4' a5' a6' a7' (Z_to_bv 64 (zlength ptr' + 1)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880)
               s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 P 126 (zlength ptr' + 1) buf (ae_lo E) FDO MST eq_refl eq_refl eq_refl
               ltac:(ul) ltac:(lia) ltac:(lia) PTRB1 MOK ltac:(left; rewrite LBUF; lia) CSRC ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU80 in ST2, PRES2. rewrite (ret_pc_even 0x9a564) in Hc2' by lia.
      assert (AG12 : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (q + -80) x) m1 m2).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. split; [exact Hx| lia]. }
      assert (FR2 : rw_cells bsegs m2 (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn)).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). eapply agree_sub; [exact AG12|]. intros x Hx. unfold elem_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
      assert (FF2 : rw_cells bsegs m2 (q + -80) [C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 0x9769c)]).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FF1). eapply agree_sub; [exact AG12|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
      assert (OUT2 : rw_cells bsegs m2 out [CB 24 jo]).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ OUT1). eapply agree_sub; [exact AG12|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
      assert (PTRB2 : bytes_at bsegs m2 P buf).
      { apply (bytes_at_agree bsegs m1 m2 _ _ PTRB1). eapply agree_sub; [exact AG12|]. intros x Hx. right; right; left. exists (ae_PB E), (ae_NPB E). split; [exact INPB| rewrite LBUF in Hx; lia]. }
      pose proof (proj2 (af_acc_live RT AF Σ m2 _ _ ART2 INPB)) as ACC2.
      pose proof (AINV_A_pres RT Σ E _ m1 m2 LV OK AI1 (rt_pres_of_ex0 _ _ _ _ _ _ PRES2)) as AI2x.

      set (K2 := fun ms => exists (ra' code : Z) (ya3 : word), elem_set_site ra' code /\ stk bsegs m2 (ae_lo E) (q + -64) /\
        ms = MS (mkR (Z_to_bv 64 ra') (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 (out + 16))
                     (Z_to_bv 64 out) (Z_to_bv 64 0) (Z_to_bv 64 16) ya3 b4 b5 b6 b7 (Z_to_bv 64 (zlength ptr' + 1)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                F2 (Z_to_bv 64 e_asan_memset) fc None m2 (seg_rom bsegs)).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt bsegs K2 ms) end.
      { intros ms <-. rewrite Ejn in FR2.
        eapply (elem_walk2 E K2 ptr' q out P _ node); [exact FR2| exact FF2| exact ST2| ul| ul| ul| exact PTRB2| exact PTRF| ul| ul| exact MI2| exact ACC2| lia| lia| reflexivity| ul| ul|].
        intros ra' code ya3 SITE ST'. subst K2. cbv beta. exists ra', code, ya3. split; [exact SITE|]. split; [exact ST'| reflexivity]. }
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & X3 & Hc3'). clear Hc3. subst K2. cbv beta in X3.
      destruct X3 as (ra' & code & ya3 & SITE & ST2' & ->). clear ST2. rename ST2' into ST2.
      assert (RAE : 0 <= ra' < 2^64 /\ ra' mod 2 = 0) by (destruct SITE as [(-> & _)|(-> & _)]; lia).

      assert (CDST : checked_dst RT Σ m2 (Z_to_bv 64 (q + -64)) out 16).
      { apply (checked_dst_stack RT AF Σ m2 _ out 16 ART2); [ul| ul| rewrite EU; lia|].
        apply (wr_at_sub m2 out 24 out 16); [| lia| lia| lia]. exact (proj2 OUT2). }
      pose proof (call_ok_lvl RT E OK Σ m2 (q + -64) LV ST2 ltac:(ul) ltac:(ul) Q16') as COK2.
      apply (rc_asan_memset RT RC Σ PMc (Z_to_bv 64 ra') (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 (out + 16))
               (Z_to_bv 64 out) (Z_to_bv 64 0) (Z_to_bv 64 16) ya3 b4 b5 b6 b7 (Z_to_bv 64 (zlength ptr' + 1)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
               F2 fc m2 out 16 (Z_to_bv 8 0) (ae_lo E) FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) CDST ART2 MI2 COK2 T c3).
      { unfold entry_st. exact Hc3'. }
      intros c4 Hc4. unfold icpt_postF in Hc4.
      destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4) & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & ->).
      rewrite EU in ST4, PRES4. change (Z.to_nat 16) with 16%nat in BY4.
      rewrite (ret_pc_even ra') in Hc4' by lia.
      assert (FR4 : rw_cells bsegs m4 (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn)).
      { apply (rw_cells_agree_nw bsegs m2 m4 _ _ FR2). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4).
        intros x Hx. unfold elem_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| lia]. }
      apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT2; [| reflexivity]. cbn [mk_CB_cells app] in OUT2.
      lazymatch type of OUT2 with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (jA := xa) in OUT2; set (jB := xb) in OUT2; set (jC := xc) in OUT2 end.
      clearbody jA jB jC.
      pose proof (rec_copy16 m2 m4 out [CB 16 jA] (CB 4 jB) jC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT2 eq_refl eq_refl BY4 eq_refl WM4 PRES4 ltac:(lia) ltac:(ul)) as OUT4.
      pose proof (lvl_shz_rec RT AF E OK Σ m4 out 24 ART4 LV ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia)) as SHZO4.
      set (K4 := fun ms => exists (m5 : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F4 (ret_pc ra) fc None m5 (seg_rom bsegs)
        /\ munch (elem_WO out) m4 m5 /\ wmono bsegs m4 m5 /\ mem_inv bsegs m5 /\ stk bsegs m5 (ae_lo E) q
        /\ rw_cells bsegs m5 out [CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 code); CB 4 jC]).
      lazymatch type of Hc4' with ASTA _ _ _ (eq ?X) _ =>
        assert (W4 : forall ms, eq X ms -> evt bsegs K4 ms) end.
      { intros ms <-. eapply (elem_after_set E OK K4); [exact FR4| exact ST4| exact MI4| lia| exact OUT4| exact QO| exact OB| exact O8| exact SHZO4| exact SITE|].
        intros m' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU5 WM5 MI5 ST5 OUT5. subst K4. cbv beta.
        exists m', y5, y6, y7, y10, y11, y12, y13, y14, y15. exists y16, y17, y28, y29, y30, y31.
        split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|]. split; [exact MI5|]. split; [exact ST5| exact OUT5]. }
      apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ PMc _ _ MST W4) Hc4'). clear W4. intros c5 Hc5.
      destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & X5 & Hc5'). clear Hc5. subst K4. cbv beta in X5.
      destruct X5 as (m5 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & MU5 & WM5 & MI5 & ST5 & OUT5).
      assert (OUT5' : out_recA E m5 out).
      { replace (repeat (Z_to_bv 8 0) 16) with (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)) in OUT5 by reflexivity.
        apply (out_recA_err E m5 out (Z_to_bv 64 0) 0 code jC); [| destruct SITE as [(_ & ->)|(_ & ->)]; lia]. apply rec_node16. exact OUT5. }
      apply Hk. split.
      2: { apply (cfrm0_of_asta RT Σ PMc _ c5 Hc5'). intros ms <-. exact FRM. }
      eapply (lvl_postA_intro RT E Σ Σ PMc c5); [exact Hc5'| | exact MI5| exact ST5| | exact OUT5'| | reflexivity| reflexivity| reflexivity| lia].
      + exact (lvl_art_munch RT AF E Σ _ m4 m5 ART4 LV (FPO Σ) MU5 WM5).
      + eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans; [| eapply rt_pres_fp_trans].
        * eapply (rt_pres_fp_of_ex _ _ (q + -80) q 0 0); [exact PRES2| lia|]. intros a _. lia.
        * eapply (rt_pres_fp_of_ex _ _ (q + -64) q out 16); [exact PRES4| lia|]. intros a Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. lia.
        * intros a Ha Ho. apply MU5. exact Ho.
      + eapply (AINV_A_munch E _ m4 m5 OK); [| exact MU5| exact HWOlo].
        exact (AINV_A_pres_ex RT Σ E _ out 16 m2 m4 LV OK AI2x PRES4 ltac:(lia)).
    -
      destruct XCHILD as (ra' & d' & e & c & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ST1 & FR1 & -> & Ed & NXT & EN & KIND).
      pose proof (call_ok_lvl RT E OK Σ m1 (q + -64) LV ST1 ltac:(ul) ltac:(ul) Q16') as COK1.
      pose proof (HOBJ d' Ed) as HOBJ'. pose proof (HARR d' Ed) as HARR'. rewrite Ed in FRB, CRB, LOR, CST0, Hk.
      unfold elem_needA in LOR. unfold elem_costA in CRB, CST0. rewrite Nat2Z.inj_succ in LOR, CRB, CST0.
      assert (RAE : 0 <= ra' < 2^64 /\ ra' mod 2 = 0 /\ (ra' = 0x97620 \/ ra' = 0x97648)) by (destruct KIND as [(-> & _)|(-> & _)]; lia).

      pose proof FR1 as FR1'. unfold elem_frame in FR1'.
      apply (proj1 (rw_cells_app bsegs m1 _ [CB 16 jn] _)) in FR1'. destruct FR1' as [FRb FRc]. cbn [cells_size csize Nat.add] in FRc.
      replace (q + -64 + Z.of_nat 16) with (q + -48) in FRc by lia.
      assert (CDST : checked_dst RT Σ m1 (Z_to_bv 64 (q + -64)) (q + -64) (Z.of_nat (length nbs))).
      { rewrite LNB. apply (checked_dst_stack RT AF Σ m1 _ (q + -64) 16 ART1); [ul| ul| rewrite EU; lia|]. exact (proj2 FRb). }
      apply (rc_asan_memcpy RT RC Σ PMc (Z_to_bv 64 ra') (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 out) (Z_to_bv 64 P)
               (Z_to_bv 64 (q + -64)) (Z_to_bv 64 node) (Z_to_bv 64 16) a3' a4' a5' a6' a7' (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880)
               s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
               F fc m1 (q + -64) node nbs (ae_lo E) FDO MST eq_refl eq_refl ltac:(rewrite LNB; reflexivity) ltac:(ul) ltac:(ul) ltac:(rewrite LNB; cbn; lia)
               NODEB CSRCN CDST ltac:(rewrite LNB; cbn; lia) ART1 MI1 COK1 T c1 Hc1').
      intros c2 Hc2. unfold icpt_postF in Hc2.
      destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2) & Hc2'). clear Hc2.
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
      rewrite EU in ST2, PRES2. rewrite LNB in PRES2. change (Z.of_nat 16%nat) with 16 in PRES2.
      rewrite (ret_pc_even ra') in Hc2' by lia.
      assert (AGR : agree_on (fun x => q + -64 <= x < USTACK_TOP /\ ~ (q + -64 <= x < q + -48)) m1 m2).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x [Hx1 Hx2]. split; [left; exact Hx1| lia]. }
      assert (FRc2 : rw_cells bsegs m2 (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FRc). eapply agree_sub; [exact AGR|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (OUT2 : rw_cells bsegs m2 out [CB 24 jo]).
      { apply (rw_cells_agree_nw bsegs m1 m2 _ _ OUT1). eapply agree_sub; [exact AGR|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (NODE16 : rw_cells bsegs m2 (q + -64) [CB 16 nbs]).
      { rewrite <- LNB. apply rw_cells_CB_intro; [exact BY2|]. rewrite LNB. exact (wr_at_transport bsegs m1 m2 _ _ (proj2 FRb) WM2). }
      assert (NODEC2 : rw_cells bsegs m2 (q + -64) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)]).
      { apply rec_node16. unfold nbs in NODE16. exact NODE16. }
      assert (FR2 : rw_cells bsegs m2 (q + -64) (elem_frame ra s0 s1 s2 s3 s4 nbs)).
      { unfold elem_frame. change (CB 16 nbs :: ?rest) with ([CB 16 nbs] ++ rest).
        apply (proj2 (rw_cells_app bsegs m2 _ [CB 16 nbs] _)). split; [exact NODE16|].
        cbn [cells_size csize Nat.add]. replace (q + -64 + Z.of_nat 16) with (q + -48) by lia. exact FRc2. }
      pose proof (call_ok_lvl RT E OK Σ m2 (q + -64) LV ST2 ltac:(ul) ltac:(ul) Q16') as COK2.

      set (cpc := if ra' =? 0x97620 then ATP_OBJ_A else ATP_ARR_A).
      set (TGT := MS (mkR (Z_to_bv 64 (ra' + 20)) (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 P)
                            (Z_to_bv 64 out) (Z_to_bv 64 (q + -64)) (Z_to_bv 64 P) (Z_to_bv 64 (zlength ptr)) b4 b5 b6 b7
                            (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F2 (Z_to_bv 64 cpc) fc None m2 (seg_rom bsegs)).
      lazymatch type of Hc2' with ASTA _ _ _ (eq ?X) _ =>
        assert (W2 : forall ms, eq X ms -> evt bsegs (eq TGT) ms) end.
      { intros ms <-. apply (elem_child_glue (eq TGT)); [exact MI2| ul| ul| exact (proj2 (proj2 RAE))| reflexivity]. }
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W2) Hc2'). clear W2. intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3. subst TGT.
      assert (FC3 : cfrm0 c3) by (apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3'); intros ms <-; exact FRM).

      assert (CHILDPOST : forall c4 (cost : Z),
        lvl_postA RT E Σ PMc (Z_to_bv 64 (ra' + 20)) (q + -64) gp (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880)
                  s5 s6 s7 s8 s9 s10 s11 out m2 cost c4 -> cfrm0 c4 -> cost <= elem_costA (S d') (zlength ptr) -> realizes bsegs c4 T).
      { intros c4 cost PO4 FC4 CST.
        destruct PO4 as (Σ1 & Hc4 & LV1 & FRS1 & SP1 & CR1).
        destruct (ASTA_unpack_f RT Σ1 _ _ c4 Hc4 FC4) as (ms4 & (v4 & m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & OUTC4 & AI4) & FRM4 & Hc4'). clear Hc4.
        destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->). cbn [ms_fcsr] in FRM4.
        rewrite (ret_pc_even (ra' + 20)) in Hc4' by lia.
        assert (LVx : a_live RT Σ1 E) by (exact (a_live_eq RT Σ Σ1 E LV LV1 FRS1 SP1)).
        assert (FR4 : rw_cells bsegs m4 (q + -64) (elem_frame ra s0 s1 s2 s3 s4 nbs)).
        { apply (rw_cells_agree_nw bsegs m2 m4 _ _ FR2). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES4).
          intros x Hx. unfold elem_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| cbn [outside]; split; [lia| exact I]]. }
        set (K5 := fun ms => exists (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
          ms = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                  F4 (ret_pc ra) fc4 None m4 (seg_rom bsegs) /\ stk bsegs m4 (ae_lo E) q).
        lazymatch type of Hc4' with ASTA _ _ _ (eq ?X) _ =>
          assert (W5 : forall ms, eq X ms -> evt bsegs K5 ms) end.
        { intros ms <-. eapply (elem_after_child E K5); [exact FR4| exact ST4| exact MI4| lia| lia|].
          intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 ST5. subst K5. cbv beta.
          exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16. exists y17, y28, y29, y30, y31. split; [reflexivity| exact ST5]. }
        apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W5) Hc4'). clear W5. intros c5 Hc5.
        destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & X5 & Hc5'). clear Hc5. subst K5. cbv beta in X5.
        destruct X5 as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & ST5).
        apply Hk. split.
        2: { apply (cfrm0_of_asta RT Σ1 PMc _ c5 Hc5'). intros ms <-. exact FRM4. }
        eapply (lvl_postA_intro RT E Σ Σ1 PMc c5); [exact Hc5'| exact ART4| exact MI4| exact ST5| | exact OUTC4| exact AI4| exact LV1| exact FRS1| exact SP1| lia].
        eapply rt_pres_fp_trans; [exact PFP1|]. eapply rt_pres_fp_trans.
        * exact (rt_pres_fp_of_ex_lower RT AF E Σ m (q + -64) q (q + -64) 16 [(out, out + 24)] m1 m2 ART0 LV ltac:(lia) ltac:(lia) ltac:(lia) PRES2).
        * exact (rt_pres_fp_mono_sp _ _ (q + -64) q _ m2 m4 PRES4 ltac:(lia)). }
      destruct KIND as [(-> & TY & CLOSE & TILES)|(-> & TY & CLOSE & TILES)]; subst cpc; cbn [Z.eqb Pos.eqb] in Hc3'.
      +
        assert (PRE' : lvl_pre RT E Σ m2 (q + -64) out (q + -64) i jo (obj_needA d') (obj_costA d' (zlength ptr)) (S d')).
        { unfold lvl_pre. split; [exact NODEC2|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
          split; [exact OUT2|]. split; [lia|]. split; [lia|]. split; [exact O8|]. split; [left; lia|].
          split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|]. split; [ul|]. split; [exact Q16'|].
          split; [exact FRB|]. split; [unfold obj_costA, LVL_C1, DCOST in *; lia| exact LVB]. }
        pose proof HOBJ' as HE. unfold atp_obj_cpsA in HE.
        apply (HE Σ PMc ptr i e c (q + -64) out (q + -64) P (Z_to_bv 64 (0x97620 + 20)) gp u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 P) b4 b5 b6 b7
                 (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc m2 jo
                 FDO MST LV (AINV_A_pres_ex RT Σ E _ (q + -64) 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)) PAT TY NXT CLOSE TILES I0 EN PRE' FRM T c3).
        { split; [unfold lvl_entry, ATP_OBJ_A; exact Hc3'| exact FC3]. }
        clear HE. intros c4 [PO4 FC4]. exact (CHILDPOST c4 _ PO4 FC4 ltac:(unfold obj_costA, elem_costA, LVL_C1, DCOST; rewrite ?Nat2Z.inj_succ; lia)).
      +
        assert (PRE' : lvl_pre RT E Σ m2 (q + -64) out (q + -64) i jo (arr_needA d') (arr_costA d' (zlength ptr)) d').
        { unfold lvl_pre. split; [exact NODEC2|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
          split; [exact OUT2|]. split; [lia|]. split; [lia|]. split; [exact O8|]. split; [left; lia|].
          split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|]. split; [ul|]. split; [exact Q16'|].
          split; [lia|]. split; [unfold arr_costA, LVL_C1, DCOST in *; lia| exact LVB]. }
        pose proof HARR' as HE. unfold atp_arr_cpsA in HE.
        apply (HE Σ PMc ptr i e c (q + -64) out (q + -64) P (Z_to_bv 64 (0x97648 + 20)) gp u0 u1 u2 (Z_to_bv 64 out) (Z_to_bv 64 P) b4 b5 b6 b7
                 (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc m2 jo
                 FDO MST LV (AINV_A_pres_ex RT Σ E _ (q + -64) 16 m1 m2 LV OK AI1 PRES2 ltac:(lia)) PAT TY NXT CLOSE TILES I0 EN PRE' FRM T c3).
        { split; [unfold lvl_entry, ATP_ARR_A; exact Hc3'| exact FC3]. }
        clear HE. intros c4 [PO4 FC4]. exact (CHILDPOST c4 _ PO4 FC4 ltac:(unfold arr_costA, elem_costA, LVL_C1, DCOST; rewrite ?Nat2Z.inj_succ; lia)).
  Qed.
End ElemLevel.
