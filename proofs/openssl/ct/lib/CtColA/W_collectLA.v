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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_bufmemA W_collectA W_collectDA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
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

  Lemma loop_stepA : forall f, loop_okK f -> entry_okK f -> loop_okK (S f).
  Proof.
    intros f IHL IHE. unfold loop_okA.
    intros until ras. intros LO OFS0 OFS16 STKG OI PPlo PPhi ALP HBUF BI HPP AXG FR IV IV1 P0 PP0 LEN0 PLD PL DEP BLP CAP CRP CR0 UW EQR CTXJ E22.
    rewrite collect_S. replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; clear - LEN0; lia). subst x22.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). pose proof STKG as STKG0. rewrite KC2, KC7 in STKG.
    assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG DEP; lia).
    assert (STKG1 : COLLECT_STACK_A <= STK) by (rewrite KC2; clear - STKP; lia).
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    assert (E0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS)) = bv_unsigned sp + OFS) by (apply unsigned_lit; clear - SPR LO LO0 STKP OFS0; lia).
    assert (EPP : bv_unsigned (Z_to_bv 64 PP) = PP) by (apply unsigned_lit; clear - PPlo PPhi LO LO0 STKP SPR OFS0; lia).
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & FRESH & DJL & DJO). clear OFc. heap_facts HEAPA.
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STA & _ & _ & _ & _ & MIA & _ & _ & CRA & _). clear OC.
    pose proof OI as (_ & _ & _ & _ & _ & HB & _).
    replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STA by (clear; lia).
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
    assert (HbB3 : In bB (OWA ++ (buf_blk b A ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
    pose proof (BND bB HbB3) as (BB3 & BB4 & BB5 & BB6).
    assert (EBUF : bv_unsigned (Z_to_bv 64 BUF) = BUF) by (apply unsigned_lit; clear - BB1 BB2 BB3 BB5 CEIL LO STKP OFS0 SPR; alia).
    destruct PBX as [E0c|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0c in PL; unfold zlength in PL; cbn in PL; clear - PL P0 PP0 LEN0 PLD; lia|].
    assert (HPB3 : In (pb, PA, psz) (OWA ++ (buf_blk b A ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HPB).
    pose proof (BND _ HPB3) as (PBa & _ & PBc & PBi). cbn [blk_addr blk_size fst snd] in PBa, PBc, PBi.
    unfold co_frameA, co_headA, co_savedA, shw in FR. cbn [app] in FR. unfold MallocRep.wz in *.
    assert (BY : forall i, 0 <= i < zlength c -> 0 <= znth c i < 256) by (intros i Hi; apply CtRepP.W_get_object_walk.znth_range; exact DF).
    pose proof BI as (_ & _ & _ & BIM & _).
    assert (CXlow : len + 10 * (MB c - bm_max b) + 40 <= CXA) by (unfold co_credit, CO_RESERVE in CR0; rewrite KC6, KC3 in CR0; clear - CR0 CRP CAP PP0 PLD LEN0; lia).
    assert (CRE : GETOBJ_ERR_COST_A <= CXA) by (rewrite KC3; clear - CXlow LEN0 BIM; lia).
    (* [comment removed for export] *)
    assert (AXA : agree_on (fun a => bv_unsigned sp + OFS <= a < USTACK_TOP) mX mA).
    { eapply agree_on_mono; [exact AXG|]. intros a Ha. cbv beta in Ha. split; [| left; exact Ha].
      intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [cbn [rin_ivs fst snd] in Hr; clear - Hr Ha BB1 BB2 BB5 CEIL LO STKP OFS0; lia| pose proof (libw_below a Hr) as Hb; unfold SEGTOP_A in Hb; clear - Hb Ha CN1 CEIL LO STKP OFS0; lia]. }
    (* [comment removed for export] *)
    assert (CONT : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31 : word) (FB : bvmap 5 word) (fcB : bv 32)
                          ΣB stB mB OWB boB (b1 : bufm bptr) (A1 p2 CXB : Z) (j0' j1' jl' : list (bv 8)) (bi' bc' : bv 8),
      oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣB stB mB OWB boB (buf_blk b1 A1 ++ NEW1) CXB ->
      rw_cells ctasegs mB BUF (buf_cells b1 A1) -> buf_invK mB b1 A1 -> rw_cells ctasegs mB PP [C8 (Z_to_bv 64 (D + p0))] ->
      agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mB ->
      rw_cells ctasegs mB (bv_unsigned sp + OFS + -176)
        ([CB 8 j0'; C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 PP)) 3 + SHB)); C8 (Z_to_bv 64 (Z.land iv 1));
          C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (BUF + 8))) 3 + SHB)); C8 (Z_to_bv 64 (BUF + 8)); C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 BUF)) 3 + SHB)); CB 6 j1'; C1 bi'; C1 bc'; CB 8 jl'; C8 (Z_to_bv 64 (D + p2));
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
      p <= p2 <= p + len -> bm_len b1 <= p2 -> bm_max b <= bm_max b1 -> CX0 - ((p2 - p0) + 10 * (bm_max b1 - cap)) <= CXB ->
      implAp (collect f c b1 p2 (len - (p2 - p)) inf (Z.of_nat j) stB) ΣB (coll_postK OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p0 len0 cap CX0)
            (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) gp (Z_to_bv 64 TP_A) y5 y6 y7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 PP) y10 y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 len) (Z_to_bv 64 BUF) (Z_to_bv 64 5) (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 (D + p))
                     y24 y25 (Z_to_bv 64 1) (Z_to_bv 64 SHB) y28 y29 y30 y31)
                FB (Z_to_bv 64 0x243910) fcB None mB (seg_rom ctasegs))).
    { intros until bc'. intros OIB HBUFB BIB HPPB AXB FRB P2 BLP2 CAPB CRB.
      kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OIB) as (_ & STB & _ & _ & _ & _ & MIB & _). clear OC.
      replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STB by (clear; lia).
      pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
      apply implAp_from_evt.
      (* [comment removed for export] *)
      step. step. step. setreg 19%Z (Z_to_bv 64 (len - (p2 - p))) ltac:(rewrite ?unsigned_lit by (clear - P0 PP0 LEN0 PLD PL P2 D1 D63; lia); f_equal; clear; lia). step. if_cases KL; zc KL.
      - (* [comment removed for export] *)
        assert (KLpos : 0 < len - (p2 - p)) by (clear - KL0; lia).
        apply evt_done.
        replace (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) by (f_equal; clear; lia).
        try replace (Z_to_bv 64 (Z.shiftr PP 3 + SHB)) with (shw PP) by (unfold shw; rewrite EPP; reflexivity).
        eapply (IHL j X0 OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FB fcB) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0) (iv := iv);
          [exact LO| exact OFS0| exact OFS16| exact STKG0| exact OIB| exact PPlo| exact PPhi| exact ALP| exact HBUFB| exact BIB| exact HPPB| exact AXB
          | unfold co_frameA, co_headA, co_savedA, shw; cbn [app]; exact FRB| exact IV| exact IV1| exact P0| clear - PP0 P2; lia| exact KLpos| clear - PLD P2; lia| exact PL| exact DEP| exact BLP2
          | clear - CAP CAPB; lia| exact CRB| exact CR0| exact UW| exact EQR| exact CTXJ| reflexivity].
      - (* [comment removed for export] *)
        step. apply evt_done.
        assert (EL : len - (p2 - p) = 0) by (repeat match goal with H : context [len - (p2 - p)] |- _ => revert H end; clear - P2 PL PLD D26 P0 PP0; intros; lia).
        rewrite EL. replace (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) by (f_equal; clear; lia).
        try replace (Z_to_bv 64 (Z.shiftr PP 3 + SHB)) with (shw PP) by (unfold shw; rewrite EPP; reflexivity).
        eapply (co_exitK f j X0 OFS STK) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0) (iv := iv);
          [exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIB| | exact PPlo| exact PPhi| exact ALP| exact HBUFB| exact BIB| exact HPPB| exact AXB
          | unfold co_headA, co_savedA, shw; cbn [app]; exact FRB| exact IV| exact IV1| clear - PP0 P2 PLD; lia| exact PL| exact BLP2| clear - CAP CAPB; lia| | exact UW| exact EQR| exact CTXJ| ].
        + (* [comment removed for export] *)
          unfold co_credit, CO_RESERVE in CR0. rewrite KC6, KC3 in CR0. rewrite KC3. clear - CR0 CRB CAPB CAP P2 PP0 PLD LEN0 BI BIB.
          destruct BIB as (_ & _ & _ & BM1 & _). lia.
        + clear - CRB CAPB; lia.
        + eapply agree_on_mono; [exact AXB|]. intros a Ha. cbv beta in Ha. split; [| left; exact Ha].
          intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [cbn [rin_ivs fst snd] in Hr; clear - Hr Ha BB1 BB2 BB5 CEIL LO STKP OFS0; lia| pose proof (libw_below a Hr) as Hb; unfold SEGTOP_A in Hb; clear - Hb Ha CN1 CEIL LO STKP OFS0; lia]. }
    (* [comment removed for export] *)
    ablock HEAPA HPB3 ACCP OFFP.
    assert (ACCS : acc ctasegs mA (bv_unsigned sp + OFS - 176) (176 + - OFS)).
    { destruct HEAPA as (HA & HS & _). apply (af_acc_stack RT AF ΣA mA _ _ HA); [| clear - TOP; unfold USTACK_TOP in *; lia].
      rewrite HS. clear - CEIL LO STKP. unfold BnHeapA.ACEIL, STACK_WIN in *. lia. }
    pose proof (AH_shb _ _ _ _ HEAPA) as SHBC.
    assert (UWc : uw_chain USTACK_TOP mA (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (bv_unsigned ra :: ras)) by (uw_from FR UW AXA).
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    apply implAp_from_evt. unfold MallocRep.wz.
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
      change (rw_cells ctasegs mA (bv_unsigned sp + OFS + -176) ([c0; c1; c2; c3; c4; c5; c6] ++ [c7; c8; c9] ++ [c10] ++ rest)) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRH FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FPIC FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FPPC FRS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS.
    replace (bv_unsigned sp + OFS + -176 + 54) with (bv_unsigned sp + OFS + -122) in FPIC by (clear; lia).
    replace (bv_unsigned sp + OFS + -176 + 54 + 10) with (bv_unsigned sp + OFS + -112) in FPPC by (clear; lia).
    replace (bv_unsigned sp + OFS + -176 + 54 + 10 + 8) with (bv_unsigned sp + OFS + -104) in FRS by (clear; lia).
    clear MU. pose proof (munch_refl [(bv_unsigned sp + OFS + -176 - 16, bv_unsigned sp + OFS + -176); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)]%Z mA) as MU.
    assert (OFFW : offshW [(bv_unsigned sp + OFS + -176 - 16, bv_unsigned sp + OFS + -176); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)]%Z) by (cbn [offshW]; clear - CEIL LO STKP CN2 OFS0; alia).
    replace (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) with (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    eapply (evt_mono ctasegs (fun ms' => exists (y10 y11 y12 : word) mq,
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) gp (Z_to_bv 64 TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 PP) y10 y11 y12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 len) (Z_to_bv 64 BUF) (Z_to_bv 64 5) (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 (D + (if (2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0) then p + 2 else p)))
                      x24 x25 (Z_to_bv 64 1) (Z_to_bv 64 SHB) x28 x29 x30 x31)
                 FA (if (2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0) then Z_to_bv 64 0x243a34 else Z_to_bv 64 0x243850) fcA None mq (seg_rom ctasegs)
        /\ munch [(bv_unsigned sp + OFS + -176 - 16, bv_unsigned sp + OFS + -176); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)]%Z mA mq
        /\ wmono ctasegs mA mq /\ mem_inv ctasegs mq /\ stk ctasegs mq lo (bv_unsigned sp + OFS + -176)
        /\ rw_cells ctasegs mq (bv_unsigned sp + OFS + -112) [C8 (Z_to_bv 64 (D + (if (2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0) then p + 2 else p)))])).
    { clear FRH FPIC FRS HBUF HPP.
      step. if_cases KL2; zc KL2.
      - assert (L1 : len = 1) by (revert KL2; rewrite ?unsigned_lit by (clear - LEN0 PLD PL D26 P0 PP0; lia); clear; intros KL2; lia).
        apply evt_done. eexists _, _, _, mA.
        replace ((2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0)) with false by (rewrite (proj2 (Z.leb_gt 2 len) ltac:(clear - L1; lia)); reflexivity).
        split; [reflexivity|]. repeat (split; [first [assumption| replace (bv_unsigned sp + OFS + -104) with (bv_unsigned sp + OFS + -112 + 8) by (clear; lia); assumption]|]). exact FPPC.
      - assert (L2 : 2 <= len) by (revert KL2; rewrite ?unsigned_lit by (clear - LEN0 PLD PL D26 P0 PP0; lia); clear - LEN0; intros KL2; lia). clear KL2.
        pose proof (BY p ltac:(clear - P0 PP0 LEN0 PLD PL L2; lia)) as R0. pose proof (BY (p + 1) ltac:(clear - P0 PP0 LEN0 PLD PL L2; lia)) as R1.
        step. step. ab_shload 1. first [ (match goal with ABok : absh_ok _ _ _ |- _ => ab_join_jb 10 11 0x24382c ABok end) | (Step.step; first [if_false | if_true]) ]. pose proof (CtRepA.W_get_object_walkA.payload_readA mA D c p (wa (D + p)) HB DF ltac:(clear - P0 PP0 LEN0 PLD PL L2; lia) eq_refl) as RD. step. clear RD. rewrite ?(zxb_lit (znth c p)) by exact R0.
        step. if_cases K2; zc K2.
        + assert (K2' : znth c p <> 0) by (revert K2; rewrite <- ?unsigned_lit_land; rewrite ?unsigned_lit by (clear - R0; lia); clear - R0; intros K2; lia).
          apply evt_done. eexists _, _, _, mA.
          replace ((2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0)) with false by (rewrite (proj2 (Z.eqb_neq (znth c p) 0) K2'), andb_false_r; reflexivity).
          split; [reflexivity|]. repeat (split; [first [assumption| replace (bv_unsigned sp + OFS + -104) with (bv_unsigned sp + OFS + -112 + 8) by (clear; lia); assumption]|]). exact FPPC.
        + assert (K2' : znth c p = 0) by (revert K2; rewrite <- ?unsigned_lit_land; rewrite ?unsigned_lit by (clear - R0; lia); clear - R0; intros K2; lia).
          apre. pose proof (CtRepA.W_get_object_walkA.payload_readA mA D c (p + 1) (wa (D + p + 1)) HB DF ltac:(clear - P0 PP0 LEN0 PLD PL L2; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
          rewrite ?(zxb_lit (znth c (p + 1))) by exact R1.
          step. if_cases K3; zc K3.
          * assert (K3' : znth c (p + 1) = 0) by (revert K3; rewrite <- ?unsigned_lit_land; rewrite ?unsigned_lit by (clear - R1; lia); clear - R1; intros K3; lia).
            replace ((2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0)) with true by (rewrite (proj2 (Z.leb_le 2 len) L2), (proj2 (Z.eqb_eq _ _) K2'), (proj2 (Z.eqb_eq _ _) K3'); reflexivity).
            step. setreg 23%Z (Z_to_bv 64 (D + (p + 2))) ltac:(rewrite ?unsigned_lit by (clear - D1 D63 P0 PP0 LEN0 PLD PL; lia); f_equal; clear; lia).
            step. name_mem mq.
            apply evt_done. eexists _, _, _, mq. split; [reflexivity|]. repeat (split; [first [eassumption| replace (bv_unsigned sp + OFS + -104) with (bv_unsigned sp + OFS + -112 + 8) by (clear; lia); eassumption]|]). eassumption.
          * assert (K3' : znth c (p + 1) <> 0) by (revert K3; rewrite <- ?unsigned_lit_land; rewrite ?unsigned_lit by (clear - R1; lia); clear - R1; intros K3; lia).
            apply evt_done. eexists _, _, _, mA.
            replace ((2 <=? len) && (znth c p =? 0) && (znth c (p + 1) =? 0)) with false by (rewrite (proj2 (Z.eqb_neq (znth c (p + 1)) 0) K3'), andb_false_r; reflexivity).
            split; [reflexivity|]. repeat (split; [first [assumption| replace (bv_unsigned sp + OFS + -104) with (bv_unsigned sp + OFS + -112 + 8) by (clear; lia); assumption]|]). exact FPPC. }
    intros ms' (y10 & y11 & y12 & mq & -> & MUq & WMq & MIq & STq & HPq).
    replace (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (OUTq : forall a, (bv_unsigned sp + OFS - 176 <= a /\ ~ (bv_unsigned sp + OFS + -112 <= a < bv_unsigned sp + OFS + -104)) \/ a < lo ->
                  outside [(bv_unsigned sp + OFS + -176 - 16, bv_unsigned sp + OFS + -176); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)]%Z a).
    { intros a Ha. cbn [outside fst snd]. clear - Ha LO STKP OFS0. lia. }
    xportby FRH MUq WMq ltac:(clear - LO STKP OFS0; lia).
    xportby FPIC MUq WMq ltac:(clear - LO STKP OFS0; lia).
    xportby FRS MUq WMq ltac:(unfold co_savedA; cbn; clear - LO STKP OFS0; lia).
    xportby HBUF MUq WMq ltac:(unfold CtColP.ColDefs.buf_cells; cbn; clear - BB1 BB2 BB5 CEIL LO STKP OFS0; unfold BnHeapA.ACEIL in *; lia).
    xportby HPP MUq WMq ltac:(clear - PPlo PPhi OFS0; lia).
    assert (OIq : oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣA stA mq OWA boA (buf_blk b A ++ NEW1) CXA).
    { kit @oinv_munch KH; [exact OI| exact MUq| exact WMq| exact MIq| | constructor; [left; cbn [fst snd]; clear - LO STKP OFS0 STK0; lia| constructor; [left; cbn [fst snd]; clear - LO STKP OFS0 STK0; lia| constructor]]].
      replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia). exact STq. }
    assert (AXGq : agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mq).
    { eapply agree_on_trans; [exact AXG|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUq)|].
      intros a [HX Ha]. apply OUTq.
      destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha OFS0; lia| right; pose proof (client_static_below a Ha) as Hlow; clear - Hlow CN1 CEIL; lia| right].
      apply in_app_iff in Hb' as [Hb'|Hb'];
        [ pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)
        | pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)]; clear - Hr' Hc' CEIL; lia. }
    assert (AXAq : agree_on (fun a => bv_unsigned sp + OFS <= a < USTACK_TOP) mX mq).
    { eapply agree_on_trans; [exact AXA|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUq)|]. intros a Ha. cbv beta in Ha. apply OUTq. left. clear - Ha OFS0; lia. }
    assert (BIq : buf_invK mq b A).
    { eapply buf_inv_agreeK; [exact BI|]. intros q n EBD. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUq)|]. intros a Ha. cbv beta in Ha. apply OUTq. right.
      pose proof (BND (q, A, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & BA & _).
      cbn [blk_addr blk_size fst snd] in BA. clear - Ha BA CEIL; alia. }
    assert (HBq : bytes_at ctasegs mq D (to_bytes c)).
    { eapply bytes_at_transport; [exact HB| exact MUq|]. cbn [disjoint_from fst snd].
      replace (Z.of_nat (length (to_bytes c))) with (zlength c) by (unfold to_bytes, zlength; rewrite ?length_map, ?map_length; reflexivity). clear - PB2 PBc CEIL LO STKP OFS0. alia. }
    kitp @oinv_facts KH OFq. pose proof (OFq _ _ _ _ _ _ _ OIq) as (HEAPq & _). clear OFq.
    clear MU WM ACCP OFFP ACCS OFFW. pose proof (munch_refl (@nil (Z * Z)) mq) as MU. pose proof (wmono_refl ctasegs mq) as WM.
    (* [comment removed for export] *)
    assert (UWq : uw_chain USTACK_TOP mq (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (bv_unsigned ra :: ras)).
    { eapply uw_chain_agree16; [exact UWc|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUq)|]. intros a Ha. cbv beta in Ha. apply OUTq. left. clear - Ha OFS0; lia. }
    (* [comment removed for export] *)
    cbv beta. apply implAp_from_evt. unfold MallocRep.wz.
    if_cases ET.
    - (* [comment removed for export] *)
      rewrite ?ET in HPq. cbv iota in HPq.
      join2c FRH FPIC. join2c FRH HPq. join2c FRH FRS.
      (* [comment removed for export] *)
      step. step. if_cases KI; zc KI.
      + (* [comment removed for export] *)
        destruct inf; [| exfalso; apply KI; rewrite IV1; reflexivity].
        try replace (Z_to_bv 64 (Z.shiftr PP 3 + SHB)) with (shw PP) by (unfold shw; rewrite EPP; reflexivity).
        eapply evt_mono; [eapply (co_ret1K OFS STK) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0);
          [exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIq| exact PPlo| exact PPhi| exact ALP| exact HBUF| exact BIq| exact HPP| exact AXGq
          | unfold co_headA, co_savedA, shw; cbn [app]; exact FRH
          | clear - P0 PP0 LEN0 PLD ET; apply andb_prop in ET as [ET _]; apply andb_prop in ET as [ET _]; apply Z.leb_le in ET; lia| exact PL| clear - BLP; lia| exact CAP| clear - CRP; lia] |].
        intros ms Hms. apply implAp_aret. exact Hms.
      + (* [comment removed for export] *)
        destruct inf; [exfalso; revert KI; rewrite IV1; rewrite ?unsigned_lit by (clear; lia); clear; lia|].
        apply evt_done.
        eapply (co_raise0K 0x243a3c 0x243a58 3%nat RS_coll_unexp_eoc 159 j X0 OFS STK) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0);
          [right; right; right; repeat split; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIq| exact CRE| exact PPlo| exact PPhi| exact HBUF| exact BIq| exact HPP| exact AXGq
          | unfold co_headA, co_savedA, shw; cbn [app]; exact FRH| exact CAP| exact UWq| exact EQR| exact CTXJ].
    - (* [comment removed for export] *)
      rewrite ?ET in HPq. cbv iota in HPq.
      lazymatch goal with |- evt _ (fun ms' => implAp (?T stA) _ _ ms') _ => set (TL := T) end.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      do 11 step. step.
      setreg 10%Z (Z_to_bv 64 (bv_unsigned sp + OFS + -122 + 2)) ltac:(rewrite ?E0; f_equal; clear; lia).
      setreg 14%Z (Z_to_bv 64 (bv_unsigned sp + OFS + -122 + 1)) ltac:(rewrite ?E0; f_equal; clear; lia).
      setreg 13%Z (Z_to_bv 64 (bv_unsigned sp + OFS + -122)) ltac:(rewrite ?E0; f_equal; clear; lia).
      setreg 15%Z (Z_to_bv 64 (bv_unsigned sp + OFS + -112)) ltac:(rewrite ?E0; f_equal; clear; lia).
      (* [comment removed for export] *)
      assert (CLT : forall a, (bv_unsigned sp + OFS - 176 <= a < bv_unsigned sp + OFS + -122 \/ bv_unsigned sp + OFS + -104 <= a < USTACK_TOP \/ BUF <= a < BUF + 32) ->
               ax_client ((buf_blk b A ++ NEW1) ++ LB) (bv_unsigned sp + OFS + -176)
                 ([(bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122 + 10); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8);
                   (bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122)] ++ LIBW_A) a).
      { intros a Ha. split.
        - intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [cbn [rin_ivs fst snd] in Hr; clear - Hr Ha BB1 BB2 BB5 CEIL LO STKP OFS0; lia| pose proof (libw_rangeA a Hr) as Hb; clear - Ha Hb BB1 BB2 BB3 BB5 BB6 CEIL LO STKP OFS0 CN1; lia].
        - destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia| left; clear - Ha OFS0; lia| right; right; exists bB; split; [apply in_app_iff; right; exact HbB| clear - Ha BB1 BB2; lia]]. }
      assert (TP : forall mT, ax_pres ((buf_blk b A ++ NEW1) ++ LB) (bv_unsigned sp + OFS + -176)
                                      ([(bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122 + 10); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8);
                                        (bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122)] ++ LIBW_A) mq mT ->
        rw_cells ctasegs mT (bv_unsigned sp + OFS + -176)
          [CB 8 j0; C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 PP)) 3 + SHB)); C8 (Z_to_bv 64 (Z.land iv 1)); C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (BUF + 8))) 3 + SHB));
           C8 (Z_to_bv 64 (BUF + 8)); C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 BUF)) 3 + SHB)); CB 6 j1]
        /\ rw_cells ctasegs mT (bv_unsigned sp + OFS + -104) (co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells ctasegs mT BUF (buf_cells b A) /\ rw_cells ctasegs mT PP [C8 (Z_to_bv 64 (D + p0))] /\ buf_invK mT b A
        /\ agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mT
        /\ agree_on (fun a => bv_unsigned sp + OFS <= a < USTACK_TOP) mX mT
        /\ uw_chain USTACK_TOP mT (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (bv_unsigned ra :: ras)).
      { intros mT AXT. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
        - apply (rw_cells_agree _ _ _ _ _ AXT) in FRH; [exact FRH| intros a Ha; apply CLT; cbn in Ha; clear - Ha; lia].
        - apply (rw_cells_agree _ _ _ _ _ AXT) in FRS; [exact FRS| intros a Ha; apply CLT; unfold co_savedA in Ha; cbn in Ha; clear - Ha OFS0 TOP; unfold USTACK_TOP in *; lia].
        - apply (rw_cells_agree _ _ _ _ _ AXT) in HBUF; [exact HBUF| intros a Ha; apply CLT; unfold CtColP.ColDefs.buf_cells in Ha; cbn in Ha; clear - Ha; lia].
        - apply (rw_cells_agree _ _ _ _ _ AXT) in HPP; [exact HPP| intros a Ha; apply CLT; cbn in Ha; clear - Ha PPlo PPhi TOP; unfold USTACK_TOP in *; lia].
        - eapply buf_inv_agreeK; [exact BIq|]. intros q n EBD. eapply agree_on_mono; [exact AXT|]. intros a Ha. cbv beta. destruct BI as (BI1 & _ & _ & _ & BI4). rewrite EBD in BI4. destruct BI4 as (C1' & C2' & _).
          pose proof (BND (q, A, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & BA5 & BA6). cbn [blk_addr blk_size fst snd] in BA5, BA6.
          split; [intros Hr; apply rin_ivs_app in Hr as [Hr|Hr]; [cbn [rin_ivs fst snd] in Hr; clear - Hr Ha BA5 CEIL LO STKP OFS0 C1' BI1; lia| pose proof (libw_rangeA a Hr) as Hb; clear - Ha Hb BA6 C1' BI1; lia]|].
          right; right. exists (q, A, n). split; [apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity| cbn; clear - Ha C1' BI1; lia].
        - eapply agree_on_trans; [exact AXGq|]. eapply agree_on_mono; [exact AXT|]. intros a [HX Ha]. split.
          + intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [exfalso| apply HX; cbn [rin_ivs app]; right; exact Hr]. cbn [rin_ivs fst snd] in Hr.
            destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Hr Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hr Hlow CN1 CEIL LO STKP OFS0; lia|].
            apply in_app_iff in Hb' as [Hb'|Hb'];
              [ pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)
              | pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)]; clear - Hr Hr' Hc' CEIL LO STKP OFS0; lia.
          + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha OFS0; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
            apply in_app_iff in Hb' as [Hb'|Hb']; apply in_app_iff; [left; apply in_app_iff; right; exact Hb'| right; exact Hb'].
        - eapply agree_on_trans; [exact AXAq|]. eapply agree_on_mono; [exact AXT|]. intros a Ha. cbv beta in Ha. apply CLT. right; left. clear - Ha OFS0; lia.
        - eapply uw_chain_agree16; [exact UWq|]. eapply agree_on_mono; [exact AXT|]. intros a Ha. cbv beta in Ha. apply CLT. right; left. clear - Ha; lia. }
      apply evt_done. subst TL. cbv beta.
      pose proof (HCTL AR STRCPY sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM KH D1 D63 D26 (bufm bptr * option Z)%type None) as W.
      cbv beta iota delta [check_tlen_gen_actA CtColP.W_check_tlen_gen.tlen_tree] in W.
      eapply W with (KW := aunr) (TLCo := None) (PIC := bv_unsigned sp + OFS + -122) (PPC := bv_unsigned sp + OFS + -112) (j31 := @nil (bv 8)) (CX := CXA); clear W;
        [ clear - STKP KC1; rewrite KC1; lia| exact FRMG| exact OIq| rewrite KC6; clear - CXlow LEN0 BIM; lia
        | rewrite E0; replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia); exact UWq
        | rewrite unsigned_lit by (clear; lia); rewrite EQR; exact (ctxJ_call j X0 _ _ ECT ltac:(unfold ASN1_COLLECT_REC_RA; clear; lia) CTXJ)
        | clear; intros HX; discriminate HX
        | clear - P0 PP0; lia| exact LEN0| clear - PLD PL; lia| exact I
        | clear; lia| clear - OFS0; lia| clear; lia| clear - OFS0; lia| clear; lia
        | replace (bv_unsigned sp + OFS + -122 + 2) with (bv_unsigned sp + OFS + -120) by (clear; lia); apply mod8_frame; [exact SP16| exact OFS16| reflexivity]
        | apply mod8_frame; [exact SP16| exact OFS16| reflexivity]
        | exact I| exact FPIC| exact HPq| | | ].
      + (* [comment removed for export] *)
        intros e st' Σ' ms' bi' bc' jl' CX' EG HCX POT. unfold tlen_postA in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & FT & fcT & mT & OWT & boT & -> & OIT & AXT & HPICT & HPPCT & _).
        replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in AXT by (clear; lia).
        rewrite (ret_pc_even 0x243880) by (clear; lia).
        destruct (TP mT AXT) as (FRH' & FRS' & HBUF' & HPP' & BIT & AXGT & AXAT & UWcT).
        assert (CRT : GETOBJ_ERR_COST_A <= CX').
        { unfold ctl_costA in HCX. rewrite EG in HCX. unfold go_costA in HCX. rewrite EG in HCX. rewrite KC3 in HCX |- *. clear - HCX CXlow LEN0 BIM. lia. }
        kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OIT) as (_ & STT & _ & _ & _ & _ & MIT & _). clear OC.
        replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STT by (clear; lia).
        clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mT) as MU. pose proof (wmono_refl ctasegs mT) as WM.
        join2c FRH' HPICT. join2c FRH' HPPCT. join2c FRH' FRS'.
        unfold MallocRep.wz in *. apply implAp_from_evt.
        step. first [if_true| if_cases KT; zc KT; [clear KT| exfalso; apply KT; reflexivity]].
        apply evt_done.
        eapply (co_raise0K 0x243988 0x2439a4 4%nat RS_coll_nested ERR_R_NESTED_ASN1_ERROR j X0 OFS STK) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0);
          [right; left; repeat split; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIT| exact CRT| exact PPlo| exact PPhi| exact HBUF'| exact BIT| exact HPP'| exact AXGT
          | unfold co_headA, co_savedA, shw; cbn [app]; exact FRH'| exact CAP| exact UWcT| exact EQR| exact CTXJ].
      + (* [comment removed for export] *) intros t st' Σ' ms' bi' bc' jl' CX' ETG. discriminate ETG.
      + (* [comment removed for export] *)
        intros st' Σ' ms' CX' EG _ HCX POT. unfold tlen_postA in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & FT & fcT & mT & OWT & boT & -> & OIT & AXT & HPICT & HPPCT & _).
        replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in AXT by (clear; lia).
        rewrite (ret_pc_even 0x243880) by (clear; lia).
        set (g := get_object c p len) in *.
        pose proof (get_object_bounds c p len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros x Hx; clear - Hx; lia) LEN0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
        destruct GB as (GB1 & GB2 & GB3).
        pose proof (CtRepP.W_get_object.go_ret_cases c p len) as RC. cbv zeta in RC. fold g in RC.
        pose proof (ret_bits (go_ret g) RC) as (R1 & R32 & R129 & R128 & R11 & RTB).
        assert (PLB : 0 <= tlen_plen g p len /\ go_p g + tlen_plen g p len <= p + len) by (unfold CtColP.W_check_tlen_gen.tlen_plen; destruct (Z.testbit (go_ret g) 0); clear - GB1 GB2 GB3; lia).
        assert (HCX1 : CXA - 1 <= CX') by (unfold ctl_costA in HCX; rewrite EG in HCX; clear - HCX; lia).
        destruct (TP mT AXT) as (FRH' & FRS' & HBUF' & HPP' & BIT & AXGT & AXAT & UWcT). clear TP.
        kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OIT) as (_ & STT & _ & _ & _ & _ & MIT & _). clear OC.
        replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STT by (clear; lia).
        lazymatch type of HPICT with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (rw_cells ctasegs mT (bv_unsigned sp + OFS + -122) ([c0] ++ [c1] ++ rest)) in HPICT end.
        apply rw_cells_app in HPICT. destruct HPICT as [HINF HPICT]. apply rw_cells_app in HPICT. destruct HPICT as [HCST HPLEN]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in HCST, HPLEN.
        replace (bv_unsigned sp + OFS + -122 + 1) with (bv_unsigned sp + OFS + -121) in HCST by (clear; lia).
        replace (bv_unsigned sp + OFS + -122 + 1 + 1) with (bv_unsigned sp + OFS + -120) in HPLEN by (clear; lia).
        clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mT) as MU. pose proof (wmono_refl ctasegs mT) as WM.
        unfold MallocRep.wz in *. apply implAp_from_evt.
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        step. first [if_false| if_cases KA; zc KA; [exfalso; clear - KA; lia| clear KA]].
        step. rewrite (zxb_lit (Z.land (go_ret g) 32)) by (clear - R32; lia).
        step. destruct (Z.land (go_ret g) 32 =? 0) eqn:EC.
        * (* [comment removed for export] *)
          apply Z.eqb_eq in EC. first [if_true| if_cases KC; zc KC; [clear KC| exfalso; apply KC; rewrite EC; reflexivity]].
          cbv beta iota delta [negb]. fold (tlen_plen g p len). set (plen := tlen_plen g p len) in *.
          try replace (Z_to_bv 64 (Z.shiftr PP 3 + SHB)) with (shw PP) by (unfold shw; rewrite EPP; reflexivity).
          apply evt_done. eapply implAp_abind.
          { join2c FRH' HINF. join2c FRH' HCST. join2c FRH' HPLEN. join2c FRH' HPPCT. join2c FRH' FRS'.
            eapply (co_dataK j X0 OFS STK) with (p0 := p0) (b := b) (A := A) (CXT := CX');
              [exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIT| clear - HCX1 CXlow LEN0; lia| exact PPlo| exact PPhi| exact HBUF'| exact BIT| exact HPP'| exact AXGT
              | unfold co_savedA, shw; cbn [app]; exact FRH'| clear - GB1 P0 PP0; lia| clear - PLB; lia| clear - PLB PLD PL; lia| clear - BLP GB1; lia| exact UWcT| exact EQR| exact CTXJ]. }
          intros r ΣB msB POQ. unfold data_postA in POQ.
          destruct POQ as (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z23 & z27 & z28 & z29 & z30 & z31 & FB & fcB & mB & OWB & boB & b1 & A1 & CXB & jl1
                           & -> & ER & OIB & HBUFB & BIB & HPPB & AXB & FRB & BLPB & CAPB & CRB).
          rewrite ER. cbn beta iota. replace (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) with (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) by (f_equal; clear; lia).
          eapply CONT; [exact OIB| exact HBUFB| exact BIB| exact HPPB| exact AXB| unfold co_savedA, shw in FRB; cbn [app] in FRB; exact FRB| clear - GB1 PLB; lia| exact BLPB| clear - CAP CAPB; lia| clear - CRB HCX1 CRP GB1 CAPB CAP PLB; lia].
        * (* [comment removed for export] *)
          apply Z.eqb_neq in EC. first [if_cases KC; zc KC; [exfalso; pose proof (CtRepP.W_get_object.land_32_cases (go_ret g)) as [L0|L32]; [exact (EC L0)|]; revert KC; rewrite L32; rewrite ?unsigned_lit by (clear; lia); clear; intros KC; lia| clear KC] | idtac].
          cbv beta iota delta [negb]. fold (tlen_plen g p len). set (plen := tlen_plen g p len) in *.
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          step. destruct (5 <=? Z.of_nat j) eqn:ED.
          -- (* [comment removed for export] *)
             apply Z.leb_le in ED. if_cases KD; zc KD; [| exfalso; revert KD; rewrite ?unsigned_lit by (clear - DEP; lia); clear - ED; intros KD; lia]. clear KD.
             apply evt_done.
             apply rw_cells_CB_ofA in HPLEN. cbn [cells_size csize Nat.add cells_bytes cbytes app] in HPLEN. rewrite ?app_nil_r in HPLEN.
             join2c FRH' HINF. join2c FRH' HCST. join2c FRH' HPLEN. join2c FRH' HPPCT. join2c FRH' FRS'.
             eapply (co_raise0K 0x2439b4 0x2439d0 3%nat RS_coll_nest_str 197 j X0 OFS STK) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0);
               [right; right; left; repeat split; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIT| rewrite KC3; clear - HCX1 CXlow LEN0 BIM; lia| exact PPlo| exact PPhi| exact HBUF'| exact BIT| exact HPP'| exact AXGT
               | unfold co_headA, co_savedA, shw; cbn [app]; exact FRH'| exact CAP| exact UWcT| exact EQR| exact CTXJ].
          -- (* [comment removed for export] *)
             apply Z.leb_gt in ED. if_cases KD; zc KD; [exfalso; revert KD; rewrite ?unsigned_lit by (clear - DEP; lia); clear - ED; intros KD; lia|]. clear KD.
             (* [comment removed for export] *)
             step. step. setreg 13%Z (Z_to_bv 64 (Z.land (go_ret g) 1)) ltac:(rewrite ?zxb_lit by (clear - R1; lia); reflexivity).
             step. step. step. step.
             assert (IV1' : Z.land (Z.land (go_ret g) 1) 1 = (if Z.testbit (go_ret g) 0 then 1 else 0)).
             { rewrite R11. destruct (Z.testbit (go_ret g) 0) eqn:TB.
               - apply (proj1 RTB). first [exact TB| reflexivity].
               - destruct R1 as [E1|E1]; [exact E1|]. exfalso. pose proof (proj2 RTB E1) as X. first [discriminate X| rewrite X in TB; discriminate TB]. }
             assert (IVR : 0 <= Z.land (go_ret g) 1 < 2 ^ 64) by (clear - R1; lia).
             apply evt_done. eapply implAp_abind.
             { pose proof (IHE (S j) X0 (OFS + -176) (STK - 176)) as IH. rewrite Nat2Z.inj_succ in IH. unfold Z.succ in IH.
               eapply IH with (b := b) (A0 := A) (p := go_p g) (PP := bv_unsigned sp + OFS + -112) (CX := CX') (NEW1 := NEW1) (ras := bv_unsigned ra :: ras);
                 [ exact LO'| exact OFS0'| exact OFS16'| clear - STKG KC2 KC7 ED; rewrite KC2, KC7; lia| exact OIT
                 | unfold co_credit, CO_RESERVE; rewrite KC6, KC3; clear - HCX1 CXlow PLB GB1; subst plen; lia
                 | clear; lia| clear - OFS0; lia| apply mod8_frame; [exact SP16| exact OFS16| reflexivity]
                 | exact HBUF'| exact BIT| exact HPPCT
                 | clear - GB1 P0 PP0; lia| clear - PLB; lia| clear - PLB PLD PL; lia| clear - ED; lia| exact IVR| exact IV1'| clear - BLP GB1; lia
                 | rewrite E0; replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia); exact UWcT
                 | rewrite unsigned_lit by (clear; lia); rewrite EQR; unfold ASN1_COLLECT_REC_RA; reflexivity
                 | exact (ctxJ_rec j X0 CTXJ ltac:(clear - ED; lia)) ]; clear IH. }
             intros r1 Σ1 ms1 PO1. unfold coll_postA in PO1.
             destruct PO1 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F2 & fc2 & m2 & OW2 & bo2 & A2 & CX2 & -> & OI2 & HBUF2 & BI2 & HPP2 & AX2 & CAP2 & RES2).
             destruct r1 as [[b1 ro] st1]. cbn [fst snd] in OI2, HBUF2, BI2, HPP2, AX2, CAP2, RES2 |- *.
             rewrite (ret_pc_even 0x2438a8) by (clear; lia).
             replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in AX2 by (clear; lia).
             assert (CL2 : forall a, (bv_unsigned sp + OFS - 176 <= a < bv_unsigned sp + OFS + -112 \/ bv_unsigned sp + OFS + -104 <= a < USTACK_TOP) ->
                       ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS + -176) ([(BUF, BUF + 32); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)] ++ LIBW_A) a).
             { intros a Ha. split; [| left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia].
               intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [cbn [rin_ivs fst snd] in Hr; clear - Hr Ha BB1 BB2 BB5 CEIL LO STKP OFS0; lia| pose proof (libw_below a Hr) as Hb; unfold SEGTOP_A in Hb; clear - Hb Ha CN1 CEIL LO STKP OFS0; lia]. }
             apply (rw_cells_agree _ _ _ _ _ AX2) in FRH'; [| intros a Ha; apply CL2; cbn in Ha; clear - Ha; lia].
             apply (rw_cells_agree _ _ _ _ _ AX2) in HINF; [| intros a Ha; apply CL2; cbn in Ha; clear - Ha; lia].
             apply (rw_cells_agree _ _ _ _ _ AX2) in HCST; [| intros a Ha; apply CL2; cbn in Ha; clear - Ha; lia].
             apply (rw_cells_agree _ _ _ _ _ AX2) in HPLEN; [| intros a Ha; apply CL2; cbn in Ha; clear - Ha; lia].
             apply (rw_cells_agree _ _ _ _ _ AX2) in FRS'; [| intros a Ha; apply CL2; unfold co_savedA in Ha; cbn in Ha; clear - Ha OFS0 TOP; unfold USTACK_TOP in *; lia].
             apply (rw_cells_agree _ _ _ _ _ AX2) in HPP'; [| intros a Ha; apply CL2; cbn in Ha; clear - Ha PPlo PPhi TOP; unfold USTACK_TOP in *; lia].
             assert (AXG2 : agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX m2).
             { eapply agree_on_trans; [exact AXGT|]. eapply agree_on_mono; [exact AX2|]. intros a [HX Ha]. split.
               - intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [| apply HX; cbn [rin_ivs app]; right; exact Hr].
                 cbn [rin_ivs fst snd app] in Hr. destruct Hr as [Hr|[Hr|Hr]]; [apply HX; cbn [rin_ivs app fst snd]; left; exact Hr| exfalso| exact Hr].
                 destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Hr Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hr Hlow CN1 CEIL LO STKP OFS0; lia|].
                 apply in_app_iff in Hb' as [Hb'|Hb'];
                   [ pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)
                   | pose proof (BND b' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)]; clear - Hr Hr' Hc' CEIL LO STKP OFS0; lia.
               - destruct Ha as [Ha|[Ha|Hb]]; [left; clear - Ha OFS0; lia| right; left; exact Ha| right; right; exact Hb]. }
             kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI2) as (_ & ST2 & _ & _ & _ & _ & MI2 & _). clear OC.
             replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in ST2 by (clear; lia).
             clear MU WM. pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
             apply rw_cells_CB_ofA in HPLEN. cbn [cells_size csize Nat.add cells_bytes cbytes app] in HPLEN. rewrite ?app_nil_r in HPLEN.
             unfold MallocRep.wz in *. apply implAp_from_evt.
             destruct ro as [p2|].
             ++ (* [comment removed for export] *)
                destruct RES2 as (RP2 & RB2 & RC2).
                step. first [if_cases KR; zc KR; [exfalso; clear - KR; lia| clear KR] | if_false].
                step. apply evt_done. cbn beta iota. replace (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) with (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) by (f_equal; clear; lia).
                join2c FRH' HINF. join2c FRH' HCST. join2c FRH' HPLEN. join2c FRH' HPP2. join2c FRH' FRS'.
                eapply CONT; [exact OI2| exact HBUF2| exact BI2| exact HPP'| exact AXG2| unfold co_savedA in FRH'; cbn [app] in FRH'; exact FRH'| clear - RP2 GB1 PLB; lia| exact RB2| clear - CAP CAP2; lia| clear - RC2 HCX1 CRP GB1 CAP CAP2; lia].
             ++ (* [comment removed for export] *)
                step. first [if_true| if_cases KR; zc KR; [clear KR| exfalso; apply KR; reflexivity]].
                join2c FRH' HINF. join2c FRH' HCST. join2c FRH' HPLEN. join2c FRH' HPP2. join2c FRH' FRS'.
                destruct (co_head_blobA m2 _ (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 PP)) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (BUF + 8))) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 BUF)) 3 + SHB)) (Z_to_bv 64 (BUF + 8)) (Z.land iv 1) j0 j1 _ _ _ _ _ FRH') as [jhd FRh].
                eapply evt_mono; [eapply (co_ret0K OFS STK 0x243a6c) with (len := len0) (cap := cap) (CX0 := CX0); [right; split; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG1| exact OI2| exact PPlo| exact PPhi| exact HBUF2| exact BI2| exact HPP'| exact AXG2| exact FRh| clear - CAP CAP2; lia]
                                 | intros ms Hms; cbn beta iota; apply implAp_aret; exact Hms].
  Qed.
  End Act.
End Proofs.
End WithRT.
