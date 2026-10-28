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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_bufmemA W_collectA.
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
Local Notation E_co_grow := (E_asn1_collect_246410 : uk_call 0x243768 0x2438d8 0x24b32c).      (* [comment removed for export] *)

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


  Local Ltac cut_hdt H H1 a' tac :=
    lazymatch type of H with rw_cells _ ?m ?A (?c0 :: ?rest) =>
      change (rw_cells ctasegs m A ([c0] ++ rest)) in H; apply rw_cells_app in H; destruct H as [H1 H];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H;
      lazymatch type of H with rw_cells _ _ ?A2 _ => replace A2 with a' in H by tac end
    end.
  (* [comment removed for export] *)
  Local Ltac join2t H1 H2 tac :=
    lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in H2 by (cbn [cells_size csize Nat.add]; tac);
      let J := fresh in pose proof (proj2 (rw_cells_app _ m A cs1 cs2) (conj H1 H2)) as J; clear H1 H2; cbn [app] in J; rename J into H1
    end end.
  Local Ltac join2c H1 H2 :=
    lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in H2 by (clear; cbn [cells_size csize Nat.add]; lia);
      let J := fresh in pose proof (proj2 (rw_cells_app _ m A cs1 cs2) (conj H1 H2)) as J; clear H1 H2; cbn [app] in J; rename J into H1
    end end.
  Local Ltac blur_plen FR :=
    lazymatch type of FR with rw_cells _ ?mm ?a0 (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
      change (rw_cells ctasegs mm a0 ([c0; c1; c2; c3; c4; c5; c6; c7; c8] ++ [c9] ++ rest)) in FR;
      let FRH := fresh "FRH" in let FT := fresh "FT" in let HPL := fresh "HPL" in let FRS := fresh "FRS" in
      apply rw_cells_app in FR as [FRH FT]; apply rw_cells_app in FT as [HPL FRS];
      apply rw_cells_CB_ofA in HPL; cbn [cells_size csize Nat.add cells_bytes cbytes app] in HPL, FRS; rewrite ?app_nil_r in HPL;
      join2c FRH HPL; join2c FRH FRS; rename FRH into FR
    end.

  (* [comment removed for export] *)
  Lemma buf_inv_agreeA : forall mA mE b A, buf_invK mA b A ->
    (forall q n, bm_data b = Some (q, n) -> agree_on (fun a => A <= a < A + n) mA mE) -> buf_invK mE b A.
  Proof.
    intros mA mE b A (BI1 & BI2 & BI3 & BIM & BI4) AG. split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|]. split; [exact BIM|].
    destruct (bm_data b) as [[q n]|]; [| exact BI4]. destruct BI4 as (C1' & C2' & rest & HC). split; [exact C1'|]. split; [exact C2'|]. exists rest.
    apply (rw_cells_agree _ _ _ _ _ (AG q n eq_refl)) in HC; [exact HC|]. intros a Ha. cbn in Ha. clear - Ha C1' BI1. lia.
  Qed.

  (* [comment removed for export] *)
  Definition data_postA (OFS STK : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x18 x19 x22 x23 : word) (mX : mem) (NEW1 : list block) (b : bufm bptr)
      (PP p0 p1 plen ivm CXT : Z) (stT : ap_st bptr) (j0 j1 : list (bv 8)) (bi bc : bv 8)
      (r : (bufm bptr * Z) * ap_st bptr) (ΣB : rts RT) : machine_state -> Prop :=
    fun msB => exists (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31 : word) (FB : bvmap 5 word) (fcB : bv 32)
                      mB OWB boB (b1 : bufm bptr) (A1 CXB : Z) (jl' : list (bv 8)),
      msB = MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) y5 y6 y7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) y10 y11 y12 y13 y14 y15 y16 y17
                    x18 x19 (wz BUF) (wz 5) x22 x23 y24 y25 (wz 1) (wz SHB) y28 y29 y30 y31) FB (Z_to_bv 64 0x243910) fcB None mB (seg_rom ctasegs)
      /\ r = ((b1, p1 + plen), stT)
      /\ oinvK (OFS + -176) (STK - 176) ΣB stT mB OWB boB (buf_blk b1 A1 ++ NEW1) CXB
      /\ rw_cells ctasegs mB BUF (buf_cells b1 A1) /\ buf_invK mB b1 A1 /\ rw_cells ctasegs mB PP [C8 (wz (D + p0))]
      /\ agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mB
      /\ rw_cells ctasegs mB (bv_unsigned sp + OFS + -176)
           ([CB 8 j0; C8 (shw PP); C8 (wz ivm); C8 (shw (BUF + 8)); C8 (wz (BUF + 8)); C8 (shw BUF); CB 6 j1; C1 bi; C1 bc; CB 8 jl'; C8 (wz (D + (p1 + plen)))]
            ++ co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      /\ bm_len b1 <= p1 + plen /\ bm_max b <= bm_max b1 /\ CXT - 10 * (bm_max b1 - bm_max b) <= CXB.
  (* [comment removed for export] *)

  Lemma co_dataA : forall (j : nat) (X0 : list Z) (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x28 x29 x30 x31 : word)
      ΣT stT mX mT OWT boT NEW1 (b : bufm bptr) (A PP p0 p1 plen ivm CXT : Z) (j0 j1 : list (bv 8)) (bi bc : bv 8) (raA : Z) (ras : list Z),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A <= STK ->
    oinvK (OFS + -176) (STK - 176) ΣT stT mT OWT boT (buf_blk b A ++ NEW1) CXT -> 10 * (MB c - bm_max b) <= CXT ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp ->
    rw_cells ctasegs mT BUF (buf_cells b A) -> buf_invK mT b A -> rw_cells ctasegs mT PP [C8 (wz (D + p0))] ->
    agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mT ->
    rw_cells ctasegs mT (bv_unsigned sp + OFS + -176)
      ([CB 8 j0; C8 (shw PP); C8 (wz ivm); C8 (shw (BUF + 8)); C8 (wz (BUF + 8)); C8 (shw BUF); CB 6 j1; C1 bi; C1 bc; C8 (wz plen); C8 (wz (D + p1))]
       ++ co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 <= p1 -> 0 <= plen -> p1 + plen <= zlength c -> bm_len b <= p1 ->
    uw_chain USTACK_TOP mT (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (raA :: ras) ->
    raA :: ras = repeat ASN1_COLLECT_REC_RA j ++ X0 -> uk_ctxJ j X0 ->
    implAp ((if plen =? 0 then aret (b, p1) else collect_data c b p1 plen) stT) ΣT
           (data_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x18 x19 x22 x23 mX NEW1 b PP p0 p1 plen ivm CXT stT j0 j1 bi bc)
           (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) x10 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 (wz BUF) (wz 5) x22 x23 x24 x25 (wz 1) (wz SHB) x28 x29 x30 x31)
               F1 (Z_to_bv 64 0x2438b0) fc1 None mT (seg_rom ctasegs)).
  Proof using ALB BE D1 D26 KH0 XBUF.
    intros until ras. intros LO OFS0 OFS16 STKG OI CRG PPlo PPhi HBUF BI HPP AXG FR P1lo PLEN0 PL1 BLP UWc EQR CTXJ.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). pose proof STKG as STKG0. rewrite KC2 in STKG.
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia). assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    assert (E0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS)) = bv_unsigned sp + OFS) by (apply unsigned_lit; clear - SPR LO LO0 STKP OFS0; lia).
    assert (EPP : bv_unsigned (Z_to_bv 64 PP) = PP) by (apply unsigned_lit; clear - PPlo PPhi LO LO0 STKP SPR OFS0; lia).
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPT & NDT & BND & FRESH & DJL & DJO). clear OFc. heap_facts HEAPT.
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STT & _ & _ & _ & _ & MIT & _ & _ & CRT & _). clear OC.
    pose proof OI as (_ & _ & _ & _ & _ & HBT & _ & LBOKT).
    replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STT by (clear; lia).
    pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
    assert (HbB3 : In bB (OWT ++ (buf_blk b A ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
    pose proof (BND bB HbB3) as (BB3 & BB4 & BB5 & BB6).
    assert (EBUF : bv_unsigned (Z_to_bv 64 BUF) = BUF) by (apply unsigned_lit; clear - BB1 BB2 BB3 BB5 CEIL LO STKP OFS0 SPR; alia).
    unfold co_savedA, shw in FR. cbn [app] in FR. unfold MallocRep.wz in *.
    pose proof BI as (BL0 & BLEN & BBY & BIM & BI4).
    assert (BMX : bm_len b <= bm_max b /\ 0 <= bm_max b < 2 ^ 31).
    { unfold bm_max. destruct (bm_data b) as [[q n]|]; [destruct BI4 as (C1' & C2' & _); clear - C1' C2' BL0; lia| destruct BI4 as [_ EL]; rewrite EL; clear; lia]. }
    pose proof (munch_refl [(bv_unsigned sp + OFS - 176, bv_unsigned sp + OFS)]%Z mT) as MU. pose proof (wmono_refl ctasegs mT) as WM.
    assert (OFFW : offshW [(bv_unsigned sp + OFS - 176, bv_unsigned sp + OFS)]%Z) by (cbn [offshW]; clear - CEIL LO STKP CN2 OFS0; alia).
    ablock HEAPT HbB3 ACCB OFFB.
    apply implAp_from_evt.
    step. step. if_cases KZ; zc KZ.
    - (* [comment removed for export] *)
      assert (EZ : plen = 0) by (revert KZ; rewrite ?unsigned_lit by (clear - PLEN0 PL1 D26 P1lo; lia); clear; intros KZ; lia). clear KZ.
      subst plen. cbn [Z.eqb].
      apply evt_done. apply implAp_aret. unfold data_postA. rewrite (Z.add_0_r p1).
      blur_plen FR.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F1, fc1. exists mT, OWT, boT, b, A, CXT. eexists.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact OI|]. split; [exact HBUF|]. split; [exact BI|]. split; [exact HPP|]. split; [exact AXG|].
      split; [unfold co_savedA, shw; cbn [app]; exact FR|]. split; [exact BLP|]. clear; lia.
    - (* [comment removed for export] *)
      assert (PZ : 0 < plen) by (revert KZ; rewrite ?unsigned_lit by (clear - PLEN0 PL1 D26 P1lo; lia); clear - PLEN0; intros KZ; lia). clear KZ.
      replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; clear - PZ; lia).
      unfold collect_data.
      destruct PBX as [E0c|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0c in PL1; unfold zlength in PL1; cbn in PL1; clear - PL1 P1lo PZ; lia|].
      assert (HPB3 : In (pb, PA, psz) (OWT ++ (buf_blk b A ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HPB).
      pose proof (BND _ HPB3) as (PBa & _ & PBc & PBi). cbn [blk_addr blk_size fst snd] in PBa, PBc, PBi.
      (* [comment removed for export] *)
      assert (GCB : grow_costA b (bm_len b + plen) <= 10 * (grow_capA b (bm_len b + plen) - bm_max b) /\ bm_max b <= grow_capA b (bm_len b + plen) <= MB c).
      { unfold grow_costA, grow_capA, MB. destruct (Z.leb_spec (bm_len b + plen) (bm_max b)) as [Hle|Hgt].
        - clear - BIM. unfold MB in BIM |- *. lia.
        - pose proof (grow_cost_bound (bm_len b + plen) (bm_max b) ltac:(clear - BMX; lia) ltac:(clear - Hgt; lia) ltac:(clear - PL1 D26 BLP PZ P1lo; lia)) as G1.
          pose proof (cap_le_bound (bm_len b + plen) (zlength c) ltac:(clear - BL0 PZ; lia) ltac:(clear - PL1 BLP; lia)) as G2.
          clear - G1 G2 Hgt BMX BL0 PZ. split; [exact G1|]. split; [| exact G2]. Z.div_mod_to_equations. lia. }
      destruct GCB as (GC1 & GC2 & GC3).
      pose proof HBUF as HBUF0. unfold CtColP.ColDefs.buf_cells in HBUF.
      assert (E160 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) = bv_unsigned sp + OFS + -176) by (rewrite unsigned_lit by (clear - SPR LO LO0 STKP OFS0; lia); clear; lia).
      (* [comment removed for export] *)
      assert (HD : exists bytes0, firstn (Z.to_nat (bm_len b)) bytes0 = to_bytes (bm_bytes b) /\
                   match bm_data b with None => A = 0 | Some (q, n) => 4 <= n < 2 ^ 31 /\ rw_cells ctasegs mT A [CB (Z.to_nat n) bytes0] end).
      { destruct (bm_data b) as [[q n]|].
        - destruct BI4 as (C1' & C2' & rest & HC). exists (to_bytes (bm_bytes b) ++ rest). split.
          + rewrite firstn_app, firstn_all2 by (unfold to_bytes; rewrite length_map; clear - BLEN BL0; unfold zlength in BLEN; lia).
            replace (Z.to_nat (bm_len b) - length (to_bytes (bm_bytes b)))%nat with 0%nat by (unfold to_bytes; rewrite length_map; clear - BLEN BL0; unfold zlength in BLEN; lia).
            cbn [firstn]. rewrite app_nil_r. reflexivity.
          + split; [exact C2'|]. apply cb_join_a in HC. replace (Z.to_nat (bm_len b) + Z.to_nat (n - bm_len b))%nat with (Z.to_nat n) in HC by (clear - C1' BL0; lia). exact HC.
        - destruct BI4 as [EA EL]. exists (@nil (bv 8)). split; [| exact EA]. rewrite EL. cbn [Z.to_nat firstn].
          destruct (bm_bytes b) as [|x l] eqn:EBB; [reflexivity| exfalso; rewrite EL in BLEN; unfold zlength in BLEN; cbn in BLEN; clear - BLEN; lia]. }
      destruct HD as (bytes0 & FB0 & HDATA).
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      step. step.
      step. setreg 11%Z (Z_to_bv 64 (bm_len b + plen)) ltac:(rewrite ?unsigned_lit by (clear - BMX BL0 PZ PL1 D26 P1lo BLP; lia); reflexivity).
      step. if_cases KN; zc KN; [exfalso; clear - KN BMX BL0 PZ PL1 D26 P1lo BLP; lia|]. clear KN.
      step. step.
      apply evt_done. eapply implAp_abind.
      { eapply (BUF_MEM_grow_clean_walkA sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM KH) with (b := b) (A0 := A) (bytes := bytes0) (NEW1 := NEW1);
          [ clear - STKG KC5; rewrite KC5; lia| exact OI| exact XBUF| exact ALB| exact HBUF0| clear - BL0 BMX; lia| clear - PZ; lia| clear - PL1 D26 BLP P1lo PZ; lia
          | exact HDATA| clear - GC1 GC2 GC3 CRG; lia
          | rewrite E0; replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia); exact UWc
          | rewrite unsigned_lit by (clear; lia); rewrite EQR; exact (ctxJ_call j X0 _ _ E_co_grow ltac:(unfold ASN1_COLLECT_REC_RA; clear; lia) CTXJ) ]. }
      intros r1 Σ1 ms1 PO1. unfold grow_postA in PO1.
      destruct PO1 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & FY & fcY & mY & OWY & q & A' & n' & rest' & -> & ER & EB & OIY & OWI & HBUFY & HBLKY & LEN' & N4 & A0' & A16 & ACE & EN & AXY).
      rewrite FB0 in HBLKY. destruct r1 as [b' st1]. cbn [fst snd] in ER, EB, OIY |- *. subst st1 b'. cbn [bm_len bm_data bm_bytes].
      rewrite (ret_pc_even 0x2438d8) by (clear; lia).
      replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in AXY by (clear; lia).
      kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OIY) as (HEAPY & NDY & BNDY & FRESHY & DJLY & DJOY). clear OFc.
      kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OIY) as (_ & STY & _ & _ & _ & _ & MIY & _ & _ & CRY & _). clear OC.
      pose proof OIY as (_ & _ & _ & _ & _ & HBY & _ & LBOKY).
      replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STY by (clear; lia).
      pose proof (BNDY (q, A', n') ltac:(apply in_app_iff; right; apply in_app_iff; left; left; reflexivity)) as (_ & _ & BAC' & BAI'). cbn [blk_addr blk_size fst snd] in BAC', BAI'.
      (* [comment removed for export] *)
      assert (CL1 : forall a, bv_unsigned sp + OFS - 176 <= a < bv_unsigned sp -> ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS + -176) ([(BUF, BUF + 32)] ++ LIBW_A) a).
      { intros a Ha. split; [| left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia].
        intros Hr. apply rin_ivs_app in Hr as [Hr|Hr]; [cbn [rin_ivs fst snd] in Hr; clear - Hr Ha BB1 BB2 BB5 CEIL LO STKP OFS0; lia| pose proof (libw_below a Hr) as Hb; unfold SEGTOP_A in Hb; clear - Hb Ha CN1 CEIL LO STKP OFS0; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AXY) in FR; [| intros a Ha; apply CL1; cbn in Ha; clear - Ha OFS0; lia].
      apply (rw_cells_agree _ _ _ _ _ AXY) in HPP; [| intros a Ha; apply CL1; cbn in Ha; clear - Ha PPlo PPhi; lia].
      (* [comment removed for export] *)
      destruct (slice_bytes_a mY D c p1 plen HBY DF P1lo ltac:(clear - PZ; lia) PL1) as [SRC SLEN].
      pose proof (DJLY (q, A', n') (pb, PA, psz) ltac:(left; reflexivity) HPB) as SEP. cbn [blk_addr blk_size fst snd] in SEP.
      cut_hdt HBLKY HB1 (A' + bm_len b) ltac:(clear - BL0; lia).
      replace (Z.to_nat (n' - bm_len b)) with (Z.to_nat plen + Z.to_nat (n' - bm_len b - plen))%nat in HBLKY by (clear - LEN' PZ BL0; lia).
      apply cb_split_a in HBLKY. cut_hdt HBLKY HB2 (A' + bm_len b + plen) ltac:(clear - PZ; lia). rename HBLKY into HB3.
      clear MU WM ACCB OFFB. pose proof (munch_refl [(bv_unsigned sp + OFS - 176, bv_unsigned sp + OFS)]%Z mY) as MU. pose proof (wmono_refl ctasegs mY) as WM.
      assert (HbBY : In bB (OWY ++ ((q, A', n') :: NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
      ablock HEAPY HbBY ACCY OFFY.
      apply implAp_from_evt.
      step. if_cases KR; zc KR; [exfalso; revert KR; rewrite ?unsigned_lit by (clear - BL0 PZ PL1 D26 P1lo BLP; lia); clear - BL0 PZ; intros KR; lia|]. clear KR.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      step. step. step. step. step.
      setreg 10%Z (Z_to_bv 64 (A' + bm_len b)) ltac:(rewrite ?unsigned_lit by (clear - BAC' BAI' A0' LEN' BL0 PZ CN1 CN2 CN3; alia); f_equal; clear; lia).
      step. step. step.
      apply evt_done. eapply implAp_step_same.
      { eapply (asan_memcpy_cpsA) with (d := A' + bm_len b) (s := D + p1) (bs := to_bytes (slice c p1 plen)) (bd := (q, A', n')) (bsrc := (pb, PA, psz)) (lo := lo)
             (OW := OWY) (LB := ((q, A', n') :: NEW1) ++ LB); try reflexivity; rewrite ?E160, ?SLEN.
        - exact HEAPY.
        - exact STY.
        - exact CEIL.
        - unfold RT_STACK. clear - LO STKG. lia.
        - clear - TOP OFS0. unfold USTACK_TOP in *. lia.
        - uchk_open. clear - SP16 OFS16. Z.div_mod_to_equations. lia.
        - exact MIY.
        - apply in_app_iff. right. left. reflexivity.
        - cbn [blk_addr blk_size fst snd]. clear - BL0; lia.
        - cbn [blk_addr blk_size fst snd]. clear - LEN'; lia.
        - apply in_app_iff. right. apply in_app_iff. right. exact HPB.
        - cbn [blk_addr blk_size fst snd]. clear - PB1 P1lo; lia.
        - cbn [blk_addr blk_size fst snd]. clear - PB2 PL1; lia.
        - exact SRC.
        - clear - SEP BL0 LEN' PZ PB1 PB2 PL1 P1lo. lia.
        - clear - PL1 D26 P1lo PZ BLP; lia.
        - unfold MallocRep.wz. reflexivity. }
      intros msM PO. unfold icall_post in PO. rewrite ?E160, ?SLEN in PO.
      destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F4 & fc4 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & HCP & WR4).
      rewrite (ret_pc_even 0x243904) by (clear; lia).
      assert (CL4 : forall a, (bv_unsigned sp + OFS - 176 <= a < bv_unsigned sp) \/ (BUF <= a < BUF + 32) ->
                    aclient_addr (OWY ++ ((q, A', n') :: NEW1) ++ LB) (bv_unsigned sp + OFS + -176) a /\ ~ (A' + bm_len b <= a < A' + bm_len b + plen)).
      { intros a [Ha|Ha].
        - split; [left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia| clear - Ha BAC' CEIL LO STKP OFS0 LEN' BL0; alia].
        - split; [right; right; exists bB; split; [exact HbBY| clear - Ha BB1 BB2; lia]|].
          pose proof (DJLY (q, A', n') bB ltac:(left; reflexivity) HbB) as DJB. cbn [blk_addr blk_size fst snd] in DJB. clear - Ha DJB BB1 BB2 LEN' BL0 PZ; lia. }
      apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; apply CL4; cbn in Ha; clear - Ha OFS0; lia].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HPP; [| intros a Ha; apply CL4; cbn in Ha; clear - Ha PPlo PPhi; lia].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HBUFY; [| intros a Ha; apply CL4; cbn in Ha; clear - Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HB1; [| intros a Ha; cbn in Ha; split; [right; right; exists (q, A', n'); split; [apply in_app_iff; right; left; reflexivity| cbn; clear - Ha BL0 LEN' PZ; lia]| clear - Ha BL0; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HB3; [| intros a Ha; cbn in Ha; split; [right; right; exists (q, A', n'); split; [apply in_app_iff; right; left; reflexivity| cbn; clear - Ha BL0 LEN' PZ; lia]| clear - Ha BL0 PZ; lia]].
      assert (HCPc : rw_cells ctasegs m4 (A' + bm_len b) [CB (Z.to_nat plen) (to_bytes (slice c p1 plen))]).
      { replace (Z.to_nat plen) with (length (to_bytes (slice c p1 plen))) by (clear - SLEN PZ; lia). apply rw_cells_of_bytes_a; [exact HCP| rewrite SLEN; exact WR4]. }
      (* [comment removed for export] *)
      assert (OI4 : oinvK (OFS + -176) (STK - 176) Σ1 stT m4 OWY boT ((q, A', n') :: NEW1) (CXT - grow_costA b (bm_len b + plen) - 0)).
      { kit @oinv_heap KH; [exact OIY| | intros b' [Hb'|Hb']; apply in_app_iff; [left; exact Hb'| right; exact Hb']| exact HEAP4| exact LBOKY| exact MI4| | clear; lia| split; [clear; lia| clear - CRY; lia]].
        - eapply agree_on_mono; [exact AG4|]. intros a [Ha HXa]. split.
          + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
            apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; apply in_app_iff; right; exact Hb'].
          + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha BAC' CEIL LO STKP OFS0 LEN' BL0; alia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (q, A', n') a HEAPY ltac:(apply in_app_iff; right; left; reflexivity) ltac:(cbn; clear - Hx BL0 LEN'; lia) Ha)|].
            apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
            * pose proof (DJOY (q, A', n') b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' BL0 LEN'. lia.
            * pose proof (DJLY (q, A', n') b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' BL0 LEN'. lia.
        - replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia). exact ST4. }
      replace (CXT - grow_costA b (bm_len b + plen) - 0) with (CXT - grow_costA b (bm_len b + plen)) in OI4 by (clear; lia).
      clear MU WM. pose proof (munch_refl [(bv_unsigned sp + OFS - 176, bv_unsigned sp + OFS)]%Z m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
      apply implAp_from_evt. cbv beta.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      freeze HBUFY. freeze HB1. freeze HB3. freeze HCPc. freeze HPP.
      step. apre. setreg 24%Z (Z_to_bv 64 (D + (p1 + plen))) ltac:(rewrite ?unsigned_lit by (clear - D1 D63 P1lo PZ PL1 D0; lia); f_equal; clear; lia).
      step. step. name_mem m5.
      match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
      match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
      thaw HBUFY. thaw HB1. thaw HB3. thaw HCPc. thaw HPP.
      (* [comment removed for export] *)
      xportby HBUFY MU5 WM5 ltac:(clear - BB1 BB2 BB5 CEIL LO STKP OFS0; unfold BnHeapA.ACEIL in *; lia).
      xportby HB1 MU5 WM5 ltac:(clear - BAC' A0' CEIL LO STKP OFS0 BL0 PZ LEN'; alia).
      xportby HB3 MU5 WM5 ltac:(clear - BAC' A0' CEIL LO STKP OFS0 BL0 PZ LEN'; alia).
      xportby HCPc MU5 WM5 ltac:(clear - BAC' A0' CEIL LO STKP OFS0 BL0 PZ LEN'; alia).
      xportby HPP MU5 WM5 ltac:(clear - PPlo PPhi; lia).
      apply evt_done. apply implAp_aret. unfold data_postA.
      (* [comment removed for export] *)
      join2t HB1 HCPc ltac:(clear - BL0; lia). apply cb_join_a in HB1. rewrite <- to_bytes_app in HB1.
      replace (Z.to_nat (bm_len b) + Z.to_nat plen)%nat with (Z.to_nat (bm_len b + plen)) in HB1 by (clear - BL0 PZ; lia).
      join2t HB1 HB3 ltac:(clear - BL0 PZ; lia).
      blur_plen FR.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      exists m5, OWY, boT, (mkBuf (bm_len b + plen) (Some (q, n')) (bm_bytes b ++ slice c p1 plen)), A', (CXT - grow_costA b (bm_len b + plen)). eexists.
      split; [reflexivity|]. split; [reflexivity|].
      split. { kit @oinv_munch KH; [| exact MU5| exact WM5| exact MI5| | constructor; [left; cbn [fst snd]; clear - LO STKP OFS0 STK0; lia| constructor]].
               - unfold CtColP.ColDefs.buf_blk; cbn [bm_data app]. exact OI4.
               - match goal with H : stk ctasegs m5 lo _ |- _ => first [exact H| replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia); exact H] end. }
      split; [unfold CtColP.ColDefs.buf_cells, bm_max; cbn [bm_len bm_data]; exact HBUFY|].
      split. { unfold buf_invA. cbn [bm_len bm_data bm_bytes bm_max].
               split; [clear - BL0 PZ; lia|]. split; [rewrite zlength_app_c, zlength_slice by (clear - P1lo PZ PL1; lia); clear - BLEN; lia|].
               split; [apply Forall_app; split; [exact BBY| apply slice_range; exact DF]|].
               split; [unfold bm_max; cbn [bm_data]; rewrite EN; exact GC3|].
               split; [exact LEN'|]. split; [exact N4|]. eexists. replace (n' - bm_len b - plen) with (n' - (bm_len b + plen)) in HB1 by (clear; lia). exact HB1. }
      split; [exact HPP|].
      split. { (* [comment removed for export] *)
               eapply agree_on_trans; [exact AXG|]. eapply agree_on_trans; [| eapply agree_on_trans].
               - eapply agree_on_mono; [exact AXY|]. intros a [HX Ha]. split; [exact HX|].
                 destruct Ha as [Ha|[Ha|Hb]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Hb].
               - eapply agree_on_mono; [exact AG4|]. intros a [HX Ha]. split.
                 + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
                   apply in_app_iff. right. right. exact Hb'.
                 + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha BAC' CEIL LO STKP OFS0 LEN' BL0; alia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (q, A', n') a HEAPY ltac:(apply in_app_iff; right; left; reflexivity) ltac:(cbn; clear - Hx BL0 LEN'; lia) Ha)|].
                   apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
                   * assert (NEb : blk_id (q, A', n') <> blk_id b').
                     { intros Ei. pose proof NDY as ND'. rewrite map_app in ND'. apply nodup_app_r in ND'. cbn [map app] in ND'. apply NoDup_cons_iff in ND' as [NI _].
                       apply NI. rewrite Ei, map_app. apply in_app_iff. left. exact (in_map blk_id _ _ Hb'). }
                     pose proof (AH_disjoint_gen _ _ _ _ (q, A', n') b' HEAPY ltac:(apply in_app_iff; right; left; reflexivity) ltac:(apply in_app_iff; right; right; apply in_app_iff; left; exact Hb') NEb) as DJ.
                     cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' BL0 LEN' PZ. lia.
                   * pose proof (DJLY (q, A', n') b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' BL0 LEN'. lia.
               - eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU5)|]. intros a [HX Ha]. cbn [outside fst snd]. split; [| exact I].
                 destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hlow CN1 CEIL LO STKP OFS0; lia|].
                 apply in_app_iff in Hb' as [Hb'|Hb'];
                   [ pose proof (BNDY b' ltac:(apply in_app_iff; right; apply in_app_iff; left; right; exact Hb')) as (_ & _ & Hc' & _)
                   | pose proof (BNDY b' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb')) as (_ & _ & Hc' & _)]; clear - Hr' Hc' CEIL LO STKP OFS0; lia. }
      split; [unfold co_savedA, shw; cbn [app]; exact FR|].
      cbn [bm_len bm_max bm_data]. split; [clear - BLP; lia|]. split; [rewrite EN; exact GC2|]. rewrite EN. clear - GC1; lia.
  Qed.


  (* [comment removed for export] *)
  Lemma co_raise0A : forall base rad nmid rs rsn (j : nat) (X0 : list Z) (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      ΣA stA mX mA OWA boA NEW1 (b : bufm bptr) (A PP p0 len0 cap CX0 CXA ivm pv : Z) (wpp w1 w2 w3 : word) (j0 j1 jl : list (bv 8)) (bi bc : bv 8) (ras : list Z),
    co_siteA base rad nmid rs rsn ->
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A <= STK ->
    oinvK (OFS + -176) (STK - 176) ΣA stA mA OWA boA (buf_blk b A ++ NEW1) CXA -> GETOBJ_ERR_COST_A <= CXA ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp ->
    rw_cells ctasegs mA BUF (buf_cells b A) -> buf_invK mA b A -> rw_cells ctasegs mA PP [C8 (wz (D + p0))] ->
    agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mA ->
    rw_cells ctasegs mA (bv_unsigned sp + OFS + -176) (co_headA wpp w1 w2 w3 ivm j0 j1 bi bc jl pv ++ co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    cap <= bm_max b ->
    uw_chain USTACK_TOP mA (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (bv_unsigned ra :: ras) ->
    bv_unsigned ra :: ras = repeat ASN1_COLLECT_REC_RA j ++ X0 -> uk_ctxJ j X0 ->
    implAp (abind (err_raise rs) (fun _ => aret (b, @None Z)) stA) ΣA
           (coll_postK OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p0 len0 cap CX0)
           (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               FA (Z_to_bv 64 base) fcA None mA (seg_rom ctasegs)).
  Proof.
    intros until ras. intros SITE LO OFS0 OFS16 STKG OI CRE PPlo PPhi HBUF BI HPP AXG FR CAP UWc EQR CTXJ.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). pose proof STKG as STKG1. rewrite KC2 in STKG.
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia). assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & FRESH & DJL & DJO). clear OFc. heap_facts HEAPA.
    pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
    assert (HbB3 : In bB (OWA ++ (buf_blk b A ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
    pose proof (BND bB HbB3) as (BB3 & BB4 & BB5 & BB6).
    unfold MallocRep.wz in *.
    eapply implAp_abind.
    { eapply (co_raiseK base rad nmid rs rsn j X0 OFS STK); [exact SITE| exact LO| exact OFS0| exact OFS16| exact STKG1| exact OI| exact CRE| exact UWc| exact EQR| exact CTXJ]. }
    intros r1 Σ1 ms1 PO1. unfold co_raise_postA in PO1.
    destruct PO1 as (q0 & q1 & q2 & p0' & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mR & OWR & boR & -> & OIR & AXR).
    cbn [fst snd] in OIR.
    assert (CL : forall a, (bv_unsigned sp + OFS - 176 <= a < bv_unsigned sp + OFS \/ BUF <= a < BUF + 32 \/ PP <= a < PP + 8) ->
                  ax_client ((buf_blk b A ++ NEW1) ++ LB) (bv_unsigned sp + (OFS + -176)) LIBW_A a).
    { intros a Ha. split; [intros Hr; pose proof (libw_rangeA a Hr) as Hb; clear - Ha Hb BB1 BB2 BB3 BB5 BB6 CEIL LO STKP PPlo OFS0 CN1; lia|].
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia| | left; clear - Ha PPlo PPhi TOP OFS0; unfold USTACK_TOP in *; lia].
      right; right. exists bB. split; [apply in_app_iff; right; exact HbB| clear - Ha BB1 BB2; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AXR) in FR; [| intros a Ha; apply CL; unfold co_headA, co_savedA in Ha; cbn in Ha; clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AXR) in HBUF; [| intros a Ha; apply CL; unfold CtColP.ColDefs.buf_cells in Ha; cbn in Ha; clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AXR) in HPP; [| intros a Ha; apply CL; cbn in Ha; clear - Ha; lia].
    assert (BIR : buf_invK mR b A).
    { eapply buf_inv_agreeA; [exact BI|]. intros q n EBD. eapply agree_on_mono; [exact AXR|]. intros a Ha. cbv beta. destruct BI as (BI1 & _ & _ & _ & BI4). rewrite EBD in BI4. destruct BI4 as (C1' & C2' & _).
      split; [intros Hr; pose proof (libw_rangeA a Hr) as Hb|].
      - pose proof (BND (q, A, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & _ & BA6).
        cbn [blk_addr blk_size fst snd] in BA6. clear - Ha Hb BA6 C1' BI1. lia.
      - right; right. exists (q, A, n). split; [apply in_app_iff; left; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity| cbn; clear - Ha C1' BI1; lia]. }
    destruct (co_head_blobA mR _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as [jhd FRh].
    destruct r1 as [u stR]. cbn [fst snd] in OIR |- *.
    apply implAp_from_evt.
    eapply evt_mono; [eapply (co_ret0K OFS STK 0x243a68); [left; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG1| exact OIR| exact PPlo| exact PPhi| exact HBUF| exact BIR| exact HPP| | exact FRh| exact CAP]
                     | intros ms Hms; apply implAp_aret; exact Hms].
    eapply agree_on_trans; [exact AXG|]. eapply agree_on_mono; [exact AXR|]. intros a [HX Ha]. split; [intros Hr; apply HX; cbn [rin_ivs fst snd app] in Hr |- *; clear - Hr; tauto|].
    destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha OFS0; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
    apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; apply in_app_iff; right; exact Hb'| right; exact Hb'].
  Qed.

  End Act.
End Proofs.
End WithRT.
