(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX UnwindRecA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit ApErrKitA2 W_get_objectA W_check_tlenA W_err_newA W_err_set_debugA W_err_vsetA I_strcpyA Fr_asn1_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require ColDefs W_check_tlen_gen W_collect.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_bufmemA W_collectA W_collectDA W_collectLA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac unhide H := unfold hidden in H.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.
Local Ltac xportby H MU WM tac :=
  eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from fst snd]; tac].

Notation zxb_lit := CtRepP.W_get_object_walk.zxb_lit.

(* [comment removed for export] *)
Ltac ab_join_jb t u J ABok :=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    let pt := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
    let pu := eval vm_compute in (bv_key (Z_to_bv 5 u)) in
    eapply (evt_cut segs (fun ms => exists vt vu : word, ms = MS (tset pu vu (tset pt vt R)) F (Z_to_bv 64 J) fc rv m ro));
    [ lazymatch type of ABok with
      | absh_ok ?b ?X ?s =>
          let k := fresh "k" in let K1 := fresh "K1" in let K2 := fresh "K2" in let Es := fresh "Es" in let Ez := fresh "Ez" in
          destruct (absh_cases b X s ABok) as [-> | (k & K1 & K2 & Es & Ez)];
          [ rewrite ?zxb_z8, ?sxb_z8; Step.step; try first [if_false | if_true]; ab_at_join
          | rewrite ?Es, ?Ez; clear Es Ez; ab_branch; Step.step; ab_addi_opt; rewrite ?ab_land7w, ?ab_land7u; ab_branch; Step.step; ab_at_join ]
      end
    | let ms1 := fresh "ms" in let vt := fresh "abt" in let vu := fresh "abu" in
      intros ms1 (vt & vu & ->); map_cbv_set; clear ABok ]
  end.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ctxJ_call := (@uk_ctxJ_call UK ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6 UR).
Local Notation ctxJ_rec := (@uk_ctxJ_rec UK ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6 UR).

Section Proofs.
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCTL : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_gen_specA AR' UK.
  Local Notation ECT := (E_asn1_collect_2463a4 : uk_call 0x243768 0x243880 0x2426a8).

  Section Act.
  Variables (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)) (CST FRM : Z).
  Variables (BUF : Z).
  Hypothesis KH0 : kit_hyps sp LB lo c D XP 0 0.
  Hypothesis D1 : 0 < D.
  Hypothesis D63 : D + zlength c < 2 ^ 63.
  Hypothesis D26 : zlength c < 2 ^ 26.
  Hypothesis XBUF : In (BUF, BUF + 32) XP.
  Hypothesis ALB : BUF mod 8 = 0.
  Hypothesis FRMG : CHECK_TLEN_FRAMES_A <= FRM.

  Local Notation oinvK OFS STK := (oinv sp m Σ LB E lo K c D XP OFS STK CST FRM).
  Local Ltac kit L KHx := lazymatch type of KHx with kit_hyps _ _ _ _ _ _ ?OFSx ?STKx => eapply (L AR sp m Σ LB E lo K c D XP OFSx STKx CST FRM KHx) end.
  Local Ltac kitp L KHx H := lazymatch type of KHx with kit_hyps _ _ _ _ _ _ ?OFSx ?STKx => pose proof (L AR sp m Σ LB E lo K c D XP OFSx STKx CST FRM KHx) as H end.
  Local Ltac act_facts OFS STK LO OFS0 OFS16 STKP KH :=
    pose proof (KHof sp LB lo c D XP KH0 OFS STK LO ltac:(clear - STKP; lia) OFS0 OFS16) as KH;
    let DF := fresh "DF" in let CEIL := fresh "CEIL" in let LO0 := fresh "LO0" in let STK0 := fresh "STK0" in let TOP := fresh "TOP" in
    let SP16 := fresh "SP16" in let XPok := fresh "XPok" in let XPD := fresh "XPD" in let PBX := fresh "PBX" in let D0 := fresh "D0" in
    pose proof KH as (DF & CEIL & LO0 & _ & STK0 & _ & TOP & SP16 & _ & XPok & XPD & PBX & D0);
    pose proof (SPR sp LB lo c D XP OFS STK KH) as SPR; pose proof (ESP sp LB lo c D XP OFS STK KH) as ESP;
    pose proof TOP as TOPN; unfold USTACK_TOP in TOPN.
  Local Ltac heap_facts HEAPX :=
    let Ca := fresh "CEa" in let Cb := fresh "CEb" in let Cc := fresh "CEc" in
    pose proof (AH_ceil _ _ _ _ HEAPX) as (Ca & Cb & Cc);
    pose proof Ca as CN1; pose proof Cb as CN2; pose proof Cc as CN3; unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CN1, CN2, CN3.
  Local Ltac uw_from FR UW AXA :=
    lazymatch type of FR with
    | rw_cells _ ?mA ?a ?cs =>
        let pre := eval cbn [List.removelast app co_savedA] in (List.removelast (List.removelast cs)) in
        lazymatch goal with
        | |- uw_chain _ _ ?f1 ?fp1 _ =>
            eapply (uw_call _ mA f1 fp1 176 pre _ _ _ UW AXA);
              [reflexivity| clear; lia| uchk_open; Z.div_mod_to_equations; lia| unfold USTACK_TOP in *; lia| apply bv_unsigned_in_range
              | rewrite !Z_to_bv_bv_unsigned; replace (fp1 + - (176)) with a by (clear; lia); exact FR]
        end
    end.
  (* [comment removed for export] *)
  Local Notation buf_invK := (buf_invA c).
  Local Notation coll_postK := (@coll_postA AR sp m Σ LB E lo K c D XP CST FRM BUF).
  Local Notation loop_okK := (@loop_okA AR UK UR sp m Σ LB E lo K c D XP CST FRM BUF).
  Local Notation entry_okK := (@entry_okA AR UK UR sp m Σ LB E lo K c D XP CST FRM BUF).
  Local Notation co_exitK := (@co_exitA AR UK BE UR STRCPY sp m Σ LB E lo K c D XP CST FRM BUF KH0 XBUF FRMG).
  Local Notation co_raiseK := (@co_raiseA AR UK BE UR STRCPY sp m Σ LB E lo K c D XP CST FRM KH0 FRMG).
  Local Notation co_ret0K := (@co_ret0A AR sp m Σ LB E lo K c D XP CST FRM BUF KH0).
  Local Notation co_ret1K := (@co_ret1A AR sp m Σ LB E lo K c D XP CST FRM BUF KH0 XBUF).
  Local Notation co_dataK := (@co_dataA AR UK BE UR sp m Σ LB E lo K c D XP CST FRM BUF KH0 D1 D26 XBUF ALB).
  Local Notation co_raise0K := (@co_raise0A AR UK BE UR STRCPY sp m Σ LB E lo K c D XP CST FRM BUF KH0 XBUF FRMG).
  Local Notation buf_inv_agreeK := (W_collectDA.buf_inv_agreeA c).


  Local Ltac join2c H1 H2 :=
    lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in H2 by (clear; cbn [cells_size csize Nat.add]; lia);
      let J := fresh in pose proof (proj2 (rw_cells_app _ m A cs1 cs2) (conj H1 H2)) as J; clear H1 H2; cbn [app] in J; rename J into H1
    end end.

  Local Ltac cut_hdt H H1 a' tac :=
    lazymatch type of H with rw_cells _ ?m ?A (?c0 :: ?rest) =>
      change (rw_cells ctasegs m A ([c0] ++ rest)) in H; apply rw_cells_app in H; destruct H as [H1 H];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H;
      lazymatch type of H with rw_cells _ _ ?A2 _ => replace A2 with a' in H by tac end
    end.

  (* [comment removed for export] *)
  Lemma entry_of_loopA : forall f, loop_okK f -> entry_okK f.
  Proof using ALB BE D26 FRMG KH0 STRCPY XBUF.
    intros f IHL. unfold entry_okA.
    intros until ras. intros LO OFS0 OFS16 STKG OI CR PPlo PPhi ALP HBUF BI HPP P0 LEN0 PL DEP IVR IV1 BLP UW EQR CTXJ.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). pose proof STKG as STKG0. rewrite KC2, KC7 in STKG.
    assert (STKP : 66528 <= STK) by (clear - STKG DEP; lia).
    assert (STKG1 : COLLECT_STACK_A <= STK) by (rewrite KC2; exact STKP).
    act_facts OFS STK LO OFS0 OFS16 STKP KH.
    assert (E0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS)) = bv_unsigned sp + OFS) by (apply unsigned_lit; clear - SPR LO LO0 STKP OFS0; lia).
    assert (EPP : bv_unsigned (Z_to_bv 64 PP) = PP) by (apply unsigned_lit; clear - PPlo PPhi LO LO0 STKP SPR OFS0; lia).
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & DJO). clear OFc. heap_facts HEAPX.
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof OI as (_ & _ & _ & _ & _ & HB & _).
    rewrite ?E0 in STX.
    pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
    assert (HbB3 : In bB (OWX ++ (buf_blk b A0 ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
    pose proof (BND bB HbB3) as (BB3 & BB4 & BB5 & BB6).
    assert (EBUF : bv_unsigned (Z_to_bv 64 BUF) = BUF) by (apply unsigned_lit; clear - BB1 BB2 BB3 BB5 CEIL LO STKP OFS0 SPR; alia).
    (* [comment removed for export] *)
    assert (ACCS : acc ctasegs mX (bv_unsigned sp + OFS - 176) (176 + - OFS)).
    { destruct HEAPX as (HA & HS & _). apply (af_acc_stack RT AF ΣX mX _ _ HA); [| clear - TOP; unfold USTACK_TOP in *; lia].
      rewrite HS. clear - CEIL LO STKP. unfold BnHeapA.ACEIL, STACK_WIN in *. lia. }
    unfold MallocRep.wz in *. unfold ASN1_COLLECT_A. pose proof HBUF as HBUF0. unfold CtColP.ColDefs.buf_cells in HBUF.
    pose proof (munch_refl [(bv_unsigned sp + OFS - 176, bv_unsigned sp + OFS)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (OFFW : offshW [(bv_unsigned sp + OFS - 176, bv_unsigned sp + OFS)]%Z) by (cbn [offshW]; clear - CEIL LO STKP CN2 OFS0; alia).
    freeze HBUF0.
    apply implAp_from_evt.
    carve_frame 176%nat STX. do 15 step.
    lazymatch type of FR with rw_cells _ _ _ (CB 72 ?jk :: _) => set (j56 := jk) in FR; clearbody j56 end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 8 step.
    step. setreg 13%Z (Z_to_bv 64 (Z.land iv 1)) ltac:(rewrite ?(unsigned_lit iv) by (clear - IVR; lia); reflexivity). step.
    step. if_cases KL; zc KL.
    - (* [comment removed for export] *)
      assert (EL : len = 0) by (apply andb_false_iff in KL; destruct KL as [KL|KL]; apply Z.ltb_ge in KL; clear - KL LEN0 PL D26 P0; lia). subst len.
      name_mem m1.
      match goal with H : munch _ mX m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs mX m1 |- _ => rename H into WM1 end.
      match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 40 ?jb :: ?rest) =>
        change (rw_cells ctasegs m1 (bv_unsigned sp + OFS + -176) ([c0; c1; c2] ++ [CB 40 jb] ++ rest)) in FR; set (j16 := jb) in FR; clearbody j16 end.
      apply rw_cells_app in FR. destruct FR as [FRA FR]. apply rw_cells_app in FR. destruct FR as [FRJ FRB].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FRJ, FRB.
      replace (bv_unsigned sp + OFS + -176 + 24) with (bv_unsigned sp + OFS + -152) in FRJ by (clear; lia).
      replace (bv_unsigned sp + OFS + -176 + 24 + 40) with (bv_unsigned sp + OFS + -112) in FRB by (clear; lia).
      apply (cb_split_a _ _ 24 16) in FRJ. cut_hdt FRJ FRI (bv_unsigned sp + OFS + -128) ltac:(clear; lia).
      apply junk24_words in FRI.
      apply (cb_split_a _ _ 6 10) in FRJ. cut_hdt FRJ FJ6 (bv_unsigned sp + OFS + -122) ltac:(clear; lia).
      apply (cb_split_a _ _ 1 9) in FRJ. cut_hdt FRJ FJI (bv_unsigned sp + OFS + -121) ltac:(clear; lia).
      apply (cb_split_a _ _ 1 8) in FRJ. cut_hdt FRJ FJC (bv_unsigned sp + OFS + -120) ltac:(clear; lia).
      destruct (cb_byte_a _ _ _ FJI) as [bi FJI']. clear FJI. destruct (cb_byte_a _ _ _ FJC) as [bc FJC']. clear FJC.
      join2c FRA FRI. join2c FRA FJ6. join2c FRA FJI'. join2c FRA FJC'. join2c FRA FRJ. join2c FRA FRB. rename FRA into FR.
      (* [comment removed for export] *)
      stk_join ST1 FR STF (bv_unsigned sp + OFS).
      assert (OI0 : oinvK OFS STK ΣX stX m1 OWX boX (buf_blk b A0 ++ NEW1) CX).
      { kit @oinv_munch KH; [exact OI| exact MU1| exact WM1| exact MI1| exact STF| constructor; [left; cbn [fst snd]; clear - LO STKP OFS0; lia| constructor]]. }
      assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
      assert (OI1 : oinvK (OFS + -176) (STK - 176) ΣX stX m1 OWX boX (buf_blk b A0 ++ NEW1) CX).
      { eapply (oinv_reframe sp m Σ LB E lo K c D XP OFS STK CST FRM (OFS + -176) (STK - 176));
          [exact OI0| exact TOP| exact SP16| replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia); exact ST1| clear - LO; lia| clear - OFS0; lia| clear - STKP; lia| exact OFS16']. }
      assert (AXG1 : agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX m1).
      { eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [HX Ha]. cbn [outside fst snd]. split; [| exact I].
        destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hlow CN1 CEIL LO STKP OFS0; lia|].
        apply in_app_iff in Hb' as [Hb'|Hb'];
          [ pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)
          | pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)]; clear - Hr' Hc' CEIL LO STKP OFS0; lia. }
      assert (AXA1 : agree_on (fun a => bv_unsigned sp + OFS <= a < USTACK_TOP) mX m1).
      { eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [clear - Ha; lia| exact I]. }
      assert (BI1 : buf_invK m1 b A0).
      { eapply buf_inv_agreeK; [exact BI|]. intros q n EBD. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
        pose proof (BND (q, A0, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & BA & _).
        cbn [blk_addr blk_size fst snd] in BA. clear - Ha BA CEIL LO STKP OFS0; alia. }
      thaw HBUF0. xportby HBUF0 MU1 WM1 ltac:(unfold CtColP.ColDefs.buf_cells; cbn; clear - BB1 BB2 BB5 CEIL LO STKP OFS0; unfold BnHeapA.ACEIL in *; lia).
      pose proof BI as (_ & _ & _ & BIM & _).
      apply evt_done. replace (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) by (f_equal; clear; lia).
      try replace (Z_to_bv 64 (Z.shiftr PP 3 + SHB)) with (shw PP) by (unfold shw; rewrite EPP; reflexivity).
      eapply (co_exitK f j X0 OFS STK) with (p0 := p) (len0 := 0) (cap := bm_max b) (CX0 := CX) (iv := iv);
        [exact LO| exact OFS0| exact OFS16| exact STKG1| exact OI1| | exact PPlo| exact PPhi| exact ALP| exact HBUF0| exact BI1| exact HPP| exact AXG1
        | unfold co_headA, co_savedA, shw; cbn [app]; exact FR| exact IVR| exact IV1| clear; lia| clear - PL; lia| exact BLP| clear; lia| clear; lia| exact UW| exact EQR| exact CTXJ| exact AXA1].
      unfold co_credit, CO_RESERVE in CR. rewrite KC6, KC3 in CR. rewrite KC3. clear - CR BIM. lia.
      all: match goal with |- Z => exact 0%Z end.
    - (* [comment removed for export] *)
      do 12 step. setreg 22%Z (Z_to_bv 64 (Z.of_nat j + 1)) ltac:(rewrite ?unsigned_lit by (clear - DEP; lia); rewrite ?swrap32_small by (clear - DEP; lia); reflexivity).
      name_mem m1.
      match goal with H : munch _ mX m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs mX m1 |- _ => rename H into WM1 end.
      match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 16 ?jk :: ?rest) =>
        change (rw_cells ctasegs m1 (bv_unsigned sp + OFS + -176) ([c0; c1; c2; c3; c4; c5] ++ [CB 16 jk] ++ rest)) in FR; set (j16 := jk) in FR; clearbody j16 end.
      apply rw_cells_app in FR. destruct FR as [FRA FR]. apply rw_cells_app in FR. destruct FR as [FRJ FRB].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FRJ, FRB.
      replace (bv_unsigned sp + OFS + -176 + 48) with (bv_unsigned sp + OFS + -128) in FRJ by (clear; lia).
      replace (bv_unsigned sp + OFS + -176 + 48 + 16) with (bv_unsigned sp + OFS + -112) in FRB by (clear; lia).
      apply (cb_split_a _ _ 6 10) in FRJ. cut_hdt FRJ FJ6 (bv_unsigned sp + OFS + -122) ltac:(clear; lia).
      apply (cb_split_a _ _ 1 9) in FRJ. cut_hdt FRJ FJI (bv_unsigned sp + OFS + -121) ltac:(clear; lia).
      apply (cb_split_a _ _ 1 8) in FRJ. cut_hdt FRJ FJC (bv_unsigned sp + OFS + -120) ltac:(clear; lia).
      destruct (cb_byte_a _ _ _ FJI) as [bi FJI']. clear FJI. destruct (cb_byte_a _ _ _ FJC) as [bc FJC']. clear FJC.
      join2c FRA FJ6. join2c FRA FJI'. join2c FRA FJC'. join2c FRA FRJ. join2c FRA FRB. rename FRA into FR.
      (* [comment removed for export] *)
      stk_join ST1 FR STF (bv_unsigned sp + OFS).
      assert (OI0 : oinvK OFS STK ΣX stX m1 OWX boX (buf_blk b A0 ++ NEW1) CX).
      { kit @oinv_munch KH; [exact OI| exact MU1| exact WM1| exact MI1| exact STF| constructor; [left; cbn [fst snd]; clear - LO STKP OFS0; lia| constructor]]. }
      assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
      assert (OI1 : oinvK (OFS + -176) (STK - 176) ΣX stX m1 OWX boX (buf_blk b A0 ++ NEW1) CX).
      { eapply (oinv_reframe sp m Σ LB E lo K c D XP OFS STK CST FRM (OFS + -176) (STK - 176));
          [exact OI0| exact TOP| exact SP16| replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia); exact ST1| clear - LO; lia| clear - OFS0; lia| clear - STKP; lia| exact OFS16']. }
      assert (AXG1 : agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX m1).
      { eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [HX Ha]. cbn [outside fst snd]. split; [| exact I].
        destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hlow CN1 CEIL LO STKP OFS0; lia|].
        apply in_app_iff in Hb' as [Hb'|Hb'];
          [ pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)
          | pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)]; clear - Hr' Hc' CEIL LO STKP OFS0; lia. }
      assert (BI1 : buf_invK m1 b A0).
      { eapply buf_inv_agreeK; [exact BI|]. intros q n EBD. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
        pose proof (BND (q, A0, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & BA & _).
        cbn [blk_addr blk_size fst snd] in BA. clear - Ha BA CEIL LO STKP OFS0; alia. }
      thaw HBUF0. xportby HBUF0 MU1 WM1 ltac:(unfold CtColP.ColDefs.buf_cells; cbn; clear - BB1 BB2 BB5 CEIL LO STKP OFS0; unfold BnHeapA.ACEIL in *; lia).
      apply evt_done. replace (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) by (f_equal; clear; lia).
      try replace (Z_to_bv 64 (Z.shiftr PP 3 + SHB)) with (shw PP) by (unfold shw; rewrite EPP; reflexivity).
      try replace (Z_to_bv 64 (Z.shiftr BUF 3 + SHB)) with (shw BUF) by (unfold shw; rewrite EBUF; reflexivity).
      eapply (IHL j X0 OFS STK) with (p0 := p) (len0 := len) (cap := bm_max b) (CX0 := CX) (iv := iv);
        [exact LO| exact OFS0| exact OFS16| exact STKG0| exact OI1| exact PPlo| exact PPhi| exact ALP| exact HBUF0| exact BI1| exact HPP| exact AXG1
        | unfold co_frameA, co_headA, co_savedA, shw; cbn [app]; exact FR| exact IVR| exact IV1| exact P0| clear; lia| exact KL0| clear; lia| exact PL| exact DEP| exact BLP
        | clear; lia| clear; lia| exact CR| exact UW| exact EQR| exact CTXJ| reflexivity].
  Qed.

  Theorem collect_okA : forall fuel, loop_okK fuel /\ entry_okK fuel.
  Proof.
    induction fuel as [|f [IHL IHE]].
    - split; [apply loop_okA_O|]. unfold entry_okA. intros. rewrite collect_O. apply implAp_unr.
    - pose proof (loop_stepA STRCPY HCTL sp m Σ LB E lo K c D XP CST FRM BUF KH0 D1 D63 D26 XBUF ALB FRMG f IHL IHE) as L1. split; [exact L1| apply entry_of_loopA; exact L1].
  Qed.

  (* [comment removed for export] *)
  Theorem asn1_collect_walkA : forall fuel, entry_okK fuel.
  Proof. intros fuel. exact (proj2 (collect_okA fuel)). Qed.

  End Act.
End Proofs.
End WithRT.
