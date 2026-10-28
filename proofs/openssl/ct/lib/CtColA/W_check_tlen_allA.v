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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA Fr_asn1_check_tlen W_check_tlenA W_get_object_closedA W_err_newA W_err_set_debugA W_err_vsetA ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtSizes CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require W_check_tlen_gen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_check_tlen_genA W_ctlA_defs W_ctlA_exit W_ctlA_raise W_ctlA_ok W_ctlA_cache.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.

Section Kit.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_go := (E_asn1_check_tlen_2453ec : uk_call 0x2426a8 0x2429a0 0x223b30).    (* [comment removed for export] *)
Local Notation E_go0 := (E_asn1_check_tlen_2453d0 : uk_call 0x2426a8 0x24295c 0x223b30).   (* [comment removed for export] *)

Section Proofs.
  Hypothesis STRCPY : strcpy_icontract RT.

  Theorem check_tlen_cps_walkA : check_tlen_cpsA.
  Proof.
    unfold check_tlen_cpsA. intros until j31. cbv zeta.
    intros PRE TP UW CTX RNE KOW KIDS PAY OP0 TL0 OPT OT PIClo PIChi PPClo PPChi DJ AL2 AL1 HTLC HPIC HPPC KE_ KW_ KS_. subst tp.
    set (g := get_object d op len) in *.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    unfold CHECK_TLEN_STACK_A, CHECK_TLEN_FRAMES_A, ACTL_FRAME in LOSP, FRM. rewrite KC6 in CRED.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
    pose proof (conj CE1 (conj CE2 CE3)) as CN. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CN.
    assert (VPOS : 0 <= GETOBJ_STACK_A /\ 0 <= GETOBJ_ERR_COST_A /\ 0 <= GETOBJ_FRAMES_A /\ RT_STACK <= GETOBJ_STACK_A)
      by (unfold GETOBJ_STACK_A, GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, ERR_NEW_COST, ERR_SET_DEBUG_COST,
                 ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, RT_STACK; clear; lia).
    pose proof PAY as (HB & PF & D0 & D63 & D26 & HBLK).
    destruct HBLK as [->|(bd & HBD & PA1 & PA2)]; [exfalso; unfold zlength in OPT; cbn in OPT; clear - OPT OP0 TL0; lia|].
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof PIChi as PICN. pose proof PPChi as PPCN. unfold USTACK_TOP in PICN, PPCN.
    assert (EPPC : bv_unsigned (Z_to_bv 64 PPC) = PPC) by (apply unsigned_lit; clear - PPClo SPR PPCN; lia).
    intros X' Φ Dl SAFE LINK.
    change (wz CHECK_TLEN_A) with (wz ACTL_ENTRY).
    eapply (actl_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
      [exact HEAP | exact ST | exact CEIL | unfold ACTL_FRAME; clear - LOSP VPOS; lia | exact TOP | exact AL16
      | unfold MallocRep.wz; rewrite EPPC; exact AL1 | exact MI | reflexivity
      | clear - FRM VPOS; lia | clear - CRED VPOS; lia |].
    intros Σ1 m3 f spa gg junk gj ra' t0' t1' t2' a5' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 j48 j56 j104 j128 j136 j144
           jf24 jf32 jf36 jf48 jf52 jf64 jf72 jf96 jf104 HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
    unfold MallocRep.wz in FRL, FRH. unfold MallocRep.wz. rewrite ?EPPC.
    pose proof (get_object_bounds d op len ltac:(eapply Forall_impl; [| exact PF]; cbv beta; intros; lia) TL0) as GB. cbv zeta in GB. fold g in GB.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CN CEIL LOSP SPAL SPAH SPR TOP VPOS LO0; alia).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold SEGTOP_A in G4. cbn [ar_SP0 push amb] in G3.
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CN; alia).
    (* [comment removed for export] *)
    pose proof (pro_closeA Σ st m OW LB E bo sp lo _ _ _ f 1%nat Σ1 m3 spa 256 PRE HEAP3 ST3 MI3 AGF CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(unfold CHECK_TLEN_STACK_A, ACTL_FRAME; clear - VPOS; lia)
                  ltac:(rewrite KC6; clear - VPOS; lia) ltac:(unfold CHECK_TLEN_FRAMES_A; clear - VPOS; lia)) as PRE1.
    unfold CHECK_TLEN_STACK_A, CHECK_TLEN_FRAMES_A, ACTL_FRAME in PRE1. rewrite KC6 in PRE1.
    replace (272 + GETOBJ_STACK_A - 256 - 16) with GETOBJ_STACK_A in PRE1 by (clear; lia).
    replace (1 + GETOBJ_FRAMES_A - 1) with GETOBJ_FRAMES_A in PRE1 by (clear; lia).
    pose proof PRE1 as (_ & AS1 & IDS1 & DC1 & ST1 & CEIL1 & LOSP1 & TOP1 & AL161 & MI1 & CRED1 & FRM1).
    rewrite ESPA in ST1, LOSP1, TOP1, AL161. cbn [ar_FR ar_RT ar_SP0 push amb] in CRED1, FRM1, CEIL1.
    (* [comment removed for export] *)
    destruct (actl_open_pbs Σ1 OW LB m3 f HEAP3 FRESH GEO FRS) as (qp & ql & qt & qc & HEAPX).
    set (pbs := actl_pbs f qp ql qt qc) in HEAPX.
    assert (INX : forall b, In b LB -> In b (pbs ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (OFFOW : forall b, In b OW -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; left; exact Hb).
    assert (OFFLB : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    pose proof (OFFLB bd HBD) as OD. unfold off_fr in OD. change (fs_size 1) with 128 in OD. cbn [blk_addr blk_size fst snd] in OD.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGF) in HPIC; [| intros a Ha; cbn in Ha; left; clear - Ha PIClo PIChi; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HPPC; [| intros a Ha; cbn in Ha; left; clear - Ha PPClo PPChi; unfold USTACK_TOP in *; lia].
    assert (PAY3 : payload_okA m3 LB D d).
    { eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGF|]. intros a Ha. right; right. eapply in_block_mono; [| exact Ha]. intros b Hb; apply in_or_app; right; exact Hb. }
    clear HB.
    (* [comment removed for export] *)
    lazymatch type of FRF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: nil)
        with ([c0; c1; c2; c3] ++ [c4] ++ [c5] ++ [c6] ++ [c7] ++ [c8] ++ [c9] ++ [c10] ++ [c11]) in FRF end.
    apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OT3 FRF]. apply rw_cells_app in FRF as [_ FRF].
    apply rw_cells_app in FRF as [OC3 FRF]. apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OL3 FRF].
    apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OP3 _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in OT3, OC3, OL3, OP3.
    replace (f + Z.of_nat 32) with (f + 32) in OT3 by (clear; lia).
    replace (f + 32 + 4 + 12) with (f + 48) in OC3 by (clear; lia).
    replace (f + 32 + 4 + 12 + 4 + 12) with (f + 64) in OL3 by (clear; lia).
    replace (f + 32 + 4 + 12 + 4 + 12 + 8 + 24) with (f + 96) in OP3 by (clear; lia).
    clear FRS.
    (* [comment removed for export] *)
    assert (ACCS : acc ctasegs m3 PPC (PPC + 8 - PPC)).
    { destruct HEAP3 as (HA3 & HS3 & _). apply (af_acc_stack RT AF Σ1 m3 _ _ HA3); [| clear - PPChi; lia].
      rewrite HS3. cbn [ar_SP0 push amb]. unfold BnHeapA.ACEIL in CEIL. clear - CEIL LOSP PPClo VPOS. lia. }
    pose proof (munch_refl [(spa, spa + 152); (f + 96, f + 104)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
    assert (OFF3 : offshW [(spa, spa + 152); (f + 96, f + 104)]%Z).
    { cbn [offshW]. clear - CN CEIL LOSP SPAL G5 VPOS. plia. }
    eapply (implAp_elim (tlen_tree g ot KE KW KS st)); [| exact SAFE | exact LINK | exact EL1].
    unfold ACTL_BODY, MallocRep.wz. apply implAp_from_evt.
    pose proof HPPC as HPPC0.
    repeat match goal with H : rw_cells ctasegs m3 ?a _ |- _ =>
      lazymatch H with HPIC => idtac | HPPC0 => idtac end;
      let T := type of H in change (frozen T) in H end.
    (* [comment removed for export] *)
    assert (FACTSof : forall bt, match TLCo with Some a => In bt LB /\ blk_addr bt <= a /\ a + 32 <= blk_addr bt + blk_size bt /\ a mod 8 = 0 | None => True end ->
              ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC TLCo ot f spa gg junk gj bd bt).
    { intros bt HBT. unfold ctl_factsA.
      split; [exact SPR|]. split; [exact (conj CE1 (conj CE2 CE3))|]. split; [exact CEIL|]. split; [clear - LOSP VPOS; unfold GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in *; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact LO0|].
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
      split; [exact SPA32|]. split; [exact SPAL|]. split; [exact SPAH|]. split; [exact ESPA|]. split; [exact Ef|]. split; [exact OFFLB|].
      split; [exact PF|]. split; [exact D0|]. split; [exact D63|]. split; [exact D26|]. split; [exact HBD|]. split; [exact PA1|]. split; [exact PA2|].
      split; [exact OP0|]. split; [exact TL0|]. split; [exact OPT|]. split; [exact OT|].
      split; [exact PIClo|]. split; [exact PIChi|]. split; [exact PPClo|]. split; [exact PPChi|]. split; [exact DJ|]. split; [exact AL2|]. split; [exact AL1|].
      split; [exact HBT|].
      split; [clear - FRM VPOS; unfold GETOBJ_FRAMES_A, ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES in *; lia|].
      split; [clear - CRED; lia|]. split; [exact CR1|]. split; [exact GSZ|]. split; [exact SAVJ|]. split; [exact KOW|].
      split; [intros b Hb Hin; apply (KIDS b Hb); apply in_app_iff; right; exact Hin|].
      split; [exact AGF|]. split; [exact UW|]. split; [exact CTX| exact RNE]. }
    assert (FLO : f + 128 <= spa) by (clear - G3 CEIL LOSP SPAL VPOS; plia).
    (* [comment removed for export] *)
    assert (AFTER : forall mc m4 Σ4 (st4 : ap_st bptr) OW4 (W : list (Z * Z)) (c24 c32 c40 : cell),
      munch W m3 mc -> (forall a, outside W a \/ (spa <= a < spa + 152) \/ (f + 96 <= a < f + 104)) ->
      @ap_preA (push AR f 1) Σ4 st4 m4 OW4 (pbs ++ LB) E bo (Z_to_bv 64 spa) lo 0 0 0 ->
      ax_pres (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) mc m4 ->
      rt_credit RT Σ1 - go_costA g <= rt_credit RT Σ4 -> blocks_kept K st4 OW4 mc m4 ->
      rw_cells ctasegs mc spa (ctl_frame0A j0 j8 j16 c24 c32 c40 f PIC PPC len ot j128 j136 gg junk) -> csize c24 = 8%nat -> csize c32 = 8%nat -> csize c40 = 8%nat ->
      rw_cells ctasegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc m4 Σ4 st4 OW4 bo (1 + go_costA g) (ctl_frame0A j0 j8 j16 c24 c32 c40 f PIC PPC len ot j128 j136 gg junk)
      /\ rw_cells ctasegs m4 PIC [C1 bi; C1 bc; CB 8 jl] /\ rw_cells ctasegs m4 PPC [C8 (Z_to_bv 64 (D + op))]).
    { intros mc m4 Σ4 st4 OW4 W c24 c32 c40 MUc HW PRE4 AXP4 CRED4 KEPT4 FRLc E24 E32 E40 FRHc.
      assert (STW : forall a, spa <= a -> a < USTACK_TOP ->
                ax_client (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) a).
      { intros a Ha Hb. split; [| left; clear - Ha Hb; lia]. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha FLO CN CEIL LOSP SPAL VPOS. plia. }
      (* [comment removed for export] *)
      assert (CV : forall a, aclient_addr LB (bv_unsigned sp) a -> (a < f \/ f + 128 <= a) /\ (a < spa \/ bv_unsigned sp <= a) /\ aclient_addr (pbs ++ LB) spa a /\ aclient_addr (OW ++ LB) (bv_unsigned sp) a).
      { intros a Hc. destruct Hc as [H1|[H1|(b & Hb & Hr)]].
        - split; [clear - H1 FLO SPAH; lia|]. split; [right; clear - H1; lia|]. split; [left; clear - H1 SPAH; lia| left; exact H1].
        - pose proof (client_static_lowA a H1) as Ha. unfold SEGTOP_A in Ha. split; [clear - Ha G4; lia|]. split; [left; clear - Ha CN CEIL LOSP SPAL VPOS; plia|].
          split; [right; left; exact H1| right; left; exact H1].
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFLB b Hb) as O.
          unfold off_fr in O. change (fs_size 1) with 128 in O.
          split; [clear - Hr O; lia|]. split; [left; clear - Hr R4 CEIL LOSP SPAL VPOS; plia|].
          split; [right; right; exists b; split; [apply INX; exact Hb| exact Hr]| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]]. }
      assert (OUTc : forall a, aclient_addr LB (bv_unsigned sp) a -> outside W a).
      { intros a Hc. destruct (CV a Hc) as (A1 & A2 & _). destruct (HW a) as [Ho|[Ho|Ho]]; [exact Ho| exfalso; clear - Ho A2 SPAH; lia| exfalso; clear - Ho A1; lia]. }
      assert (AG0c : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mc).
      { eapply agree_on_trans; [exact AGF|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a Hc.
        destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [apply OUTc; left; exact H1| apply OUTc; right; left; exact H1|].
        apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply OUTc; right; right; exists b; split; [exact Hb| exact Hr]].
        pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFOW b Hb) as O.
        unfold off_fr in O. change (fs_size 1) with 128 in O.
        destruct (HW a) as [Ho|[Ho|Ho]]; [exact Ho| exfalso; clear - Ho Hr R4 CEIL LOSP SPAL VPOS; plia| exfalso; clear - Ho Hr O; lia]. }
      split; [| split].
      - split; [exact PRE4|]. split; [exact (blocks_kept_pre K st4 OW OW4 LB (bv_unsigned sp) m mc m4 KOW AG0c KEPT4)|].
        split.
        { eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [_ Hc]; exact (proj2 (proj2 (proj2 (CV a Hc))))|].
          eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]; intros a [_ Hc]; exact (OUTc a Hc)|].
          eapply agree_on_mono; [exact AXP4|]. intros a [HX Hc]. destruct (CV a Hc) as (A1 & _ & A3 & _). split; [| exact A3].
          intros HY. apply rin_ivs_app in HY. destruct HY as [HY|HY]; [cbn [rin_ivs fst snd app] in HY; clear - HY A1; lia|].
          apply HX. unfold ctl_XX. cbn [rin_ivs app]. right; right; right. exact HY. }
        split; [cbn [ar_RT push amb] in CRED4 |- *; clear - CR1 CRED4; lia|].
        split; [eapply rw_cells_agree; [exact AXP4| exact FRLc| intros a Ha; unfold ctl_frame0A in Ha; cbn [cells_size csize Nat.add] in Ha; rewrite E24, E32, E40 in Ha; apply STW; clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia]|].
        eapply rw_cells_agree; [exact AXP4| exact FRHc| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia].
      - unfold frozen in HPIC. eapply rw_cells_agree; [exact AXP4| | intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPAH PIClo PIChi; lia].
        eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MUc)| exact HPIC| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUTc; left; clear - Ha PIClo PIChi; lia].
      - unfold frozen in HPPC0. unfold MallocRep.wz in HPPC0. eapply rw_cells_agree; [exact AXP4| | intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPAH PPClo PPChi; lia].
        eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MUc)| exact HPPC0| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUTc; left; clear - Ha PPClo PPChi; lia]. }
    (* [comment removed for export] *)
    ab_shload 8. rstep. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. step. step.
    step. if_cases KLEN; zc KLEN; [exfalso; revert KLEN; rewrite ?signed_small by (clear - TL0 OPT D26 OP0; lia); clear - TL0 OPT D26 OP0; lia|].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    step. if_cases KCTX; zc KCTX.
    - (* [comment removed for export] *)
      destruct TLCo as [tlc|].
      { exfalso. destruct HTLC as ((bt & HBT & TB1 & TB2) & ALT & _).
        pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_intror HBT))) as (BT0 & _ & _ & BT3 & _).
        revert KCTX. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). rewrite Z.mod_small by (clear - BT0 BT3 TB1 TB2 CN; alia).
        clear - BT0 TB1; lia. }
      clear KCTX HTLC.
      (* [comment removed for export] *)
      do 12 step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
      match goal with H : munch _ m3 mc |- _ => rename H into MUc end. match goal with H : wmono ctasegs m3 mc |- _ => rename H into WMc end.
      match goal with H : stk ctasegs mc lo spa |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end.
      apply evt_done.
      (* [comment removed for export] *)
      assert (HEAPc : @BnHeapA.AHEAP (push AR f 1) Σ1 OW (pbs ++ LB) mc).
      { eapply (@AH_frame (push AR f 1)); [exact HEAPX| exact MUc| exact WMc|].
        constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAL SPAH TOP VPOS; plia|].
        constructor; [right; right; exists (qp, f + 96, 8); split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear; lia]| constructor]. }
      assert (AGLc : agree_on (lib_addr OW) m3 mc).
      { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a HL. cbn [outside fst snd].
        destruct HL as [HS|(b & Hb & Hr)].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA G4 CN CEIL LOSP SPAL VPOS. plia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFOW b Hb) as O.
          unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4, O. clear - Hr R4 O CEIL LOSP SPAL VPOS. lia. }
      assert (PREc : @ap_preA (push AR f 1) Σ1 st mc OW (pbs ++ LB) E bo (Z_to_bv 64 spa) lo GETOBJ_STACK_A GETOBJ_ERR_COST_A GETOBJ_FRAMES_A).
      { eapply (@ap_preA_memA (push AR f 1)); [eapply ap_preA_weaken; [exact PRE1| clear; lia| rewrite KC3; clear; lia| clear - VPOS; lia]| exact HEAPc| exact AGLc| rewrite ESPA; exact STc| exact MIc]. }
      assert (PAYc : payload_okA mc (pbs ++ LB) D d).
      { eapply payload_okA_monoA; [| exact INX]. eapply payload_okA_agreeA; [exact PAY3|].
        eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a (b & Hb & Hr). cbn [outside fst snd].
        pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFLB b Hb) as O.
        unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4, O. clear - Hr R4 O CEIL LOSP SPAL VPOS. lia. }
      assert (CIN : forall q A n, In (q, A, n) pbs -> cellA_in (pbs ++ LB) A n).
      { intros q A n Hin. exists (q, A, n). split; [apply in_or_app; left; exact Hin| cbn; clear; lia]. }
      assert (GC : go_cellsA_ok (pbs ++ LB) (f + 96) (f + 64) (f + 32) (f + 48)).
      { split; [apply (CIN qp); subst pbs; cbn; tauto|]. split; [apply (CIN ql); subst pbs; cbn; tauto|]. split; [apply (CIN qt); subst pbs; cbn; tauto|].
        split; [apply (CIN qc); subst pbs; cbn; tauto|]. clear - G2. Z.div_mod_to_equations. lia. }
      assert (GOFF : go_cells_offA D (zlength d) (f + 96) (f + 64) (f + 32) (f + 48)).
      { unfold go_cells_offA. clear - OD PA1 PA2. lia. }
      (* [comment removed for export] *)
      assert (UWc : uw_chain USTACK_TOP mc spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { eapply (uw_call m mc spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
          [ exact UW
          | eapply agree_on_trans; [ eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha
                                   | eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]; intros a Ha; cbn [outside fst snd]; clear - Ha SPAH FLO; lia ]
          | reflexivity | clear - SPAH; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia
          | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH ]. }
      pose proof (FACTSof bd I) as FACTS.
      rewrite ?EPPC in FRL.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (CALL : @implAp (push AR f 1) _ (go_eff g st) Σ1
          (@getobj_postA (push AR f 1) (Z_to_bv 64 0x24295c) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 0) (Z_to_bv 64 (D + op))
                        Σ1 OW (pbs ++ LB) E bo lo mc K D (f + 96) (f + 64) (f + 32) (f + 48) g)
          (MS (mkR (Z_to_bv 64 0x24295c) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 (f + 48)) t1' t2' sp (Z_to_bv 64 spa)
                   (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 len) (Z_to_bv 64 (D + op)) (Z_to_bv 64 len) a7'
                   (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 0) (Z_to_bv 64 (D + op)) t3' t4' t5' t6')
              F' (Z_to_bv 64 ASN1_GET_OBJECT_A) fc' None mc (seg_rom ctasegs))).
      { pose proof (@ASN1_get_object_closedA (push AR f 1) UK BE STRCPY) as HGO. unfold ASN1_get_object_specA in HGO.
        eapply HGO with (K := K) (LB := pbs ++ LB) (lo := lo) (D := D) (d := d) (op := op) (omax := len)
                                                                          (PP := f + 96) (PL := f + 64) (PT := f + 32) (PC := f + 48);
          [exact PREc| reflexivity| rewrite ESPA; exact UWc| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_go0 CTX)| apply cons_ne
          | exact KOW| exact KIDS| exact PAYc| exact OP0| exact TL0| exact OPT| exact GC| exact GOFF| exact OP3| exact OL3| exact OT3| exact OC3
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      match type of CALL with implAp _ _ ?P ?MSc => pose (GPOST := P); change (implAp (go_eff g st) Σ1 GPOST MSc) in CALL end.
      assert (HWN : forall a, outside [(spa, spa + 152); (f + 96, f + 104)]%Z a \/ (spa <= a < spa + 152) \/ (f + 96 <= a < f + 104))
        by (intros a; cbn [outside fst snd]; clear; lia).
      (* [comment removed for export] *)
      assert (UWK : forall m4, ax_pres (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) mc m4 ->
                uw_chain USTACK_TOP m4 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { intros m4 AXP4. eapply uw_chain_agree16; [exact UWc|]. eapply agree_on_mono; [exact AXP4|]. intros a Ha. cbv beta in Ha. split; [| left; clear - Ha SPAH; lia].
        intros HY. apply rin_ivs_app in HY. destruct HY as [HY|HY]; [cbn [rin_ivs fst snd app] in HY; clear - HY Ha FLO SPAH; lia|].
        pose proof (libw_below a HY) as Hb. unfold SEGTOP_A in Hb. clear - Hb Ha CN CEIL LOSP SPAH VPOS. plia. }
      clear HEAPc AGLc PREc PAYc CIN GC GOFF.
      destruct (go_err g) as [e|] eqn:EG.
      + (* [comment removed for export] *)
        unfold CtColP.W_check_tlen_gen.tlen_tree. rewrite EG.
        eapply implAp_abind.
        * unfold tlen_fail. eapply implAp_abind with (Q1 := GPOST).
          -- unfold CtRepP.W_get_object.go_eff in CALL. rewrite EG in CALL. exact CALL.
          -- intros r1 Σ4 ms4 PO4. cbv beta in PO4. subst GPOST. unfold getobj_postA in PO4. cbn [fst snd] in PO4. rewrite EG in PO4.
             destruct PO4 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m4 & OW4 & jl4 & jt4 & jc4 & -> & PRE4 & AXP4 & CRED4 & KEPT4 & HPP4 & RES4).
             rewrite ?ESPA in AXP4. unfold MallocRep.wz in HPP4, RES4.
             (* [comment removed for export] *)
             assert (CELLS : Z.land (bv_unsigned z0) 128 <> 0 /\ exists jl' j2' j3', rw_cells ctasegs m4 (f + 64) [CB 8 jl'] /\ rw_cells ctasegs m4 (f + 32) [CB 4 j2'] /\ rw_cells ctasegs m4 (f + 48) [CB 4 j3']).
             { destruct e; [| | destruct GB].
               - destruct RES4 as (-> & H1 & H2 & H3). split; [rewrite unsigned_lit by (clear; lia); change (Z.land 128 128) with 128; clear; lia|].
                 exists jl4, jt4, jc4. split; [exact H1| split; [exact H2| exact H3]].
               - destruct RES4 as (-> & H1 & H2 & H3). split.
                 + pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
                   assert (LV : (Z.lor (go_ret g) 128 = 128 \/ Z.lor (go_ret g) 128 = 129) \/ (Z.lor (go_ret g) 128 = 160 \/ Z.lor (go_ret g) 128 = 161)).
                   { destruct RC as [E0|[E0|[E0|E0]]]; rewrite E0; [left; left| left; right| right; left| right; right]; reflexivity. }
                   assert (LA : Z.land (Z.lor (go_ret g) 128) 128 = 128 /\ 0 <= Z.lor (go_ret g) 128 < 2 ^ 64).
                   { destruct LV as [[E1|E1]|[E1|E1]]; rewrite E1; (split; [reflexivity| clear; lia]). }
                   destruct LA as [LA1 LA2]. rewrite unsigned_lit by exact LA2. rewrite LA1. clear; lia.
                 + apply (rw_cells_cb_first m4 _ _ 1) in H1. apply (rw_cells_cb_first m4 _ _ 1) in H2. apply (rw_cells_cb_first m4 _ _ 1) in H3. cbn [cb_first csize] in H1, H2, H3.
                   eexists _, _, _. split; [exact H1| split; [exact H2| exact H3]]. }
             clear RES4. destruct CELLS as (B7 & jl' & j2' & j3' & OL4 & OT4 & OC4).
             destruct (AFTER mc m4 Σ4 (snd r1) OW4 _ (CB 8 j24) (CB 8 j32) (C8 (Z_to_bv 64 SHB)) MUc HWN PRE4 AXP4 CRED4 KEPT4 FRL eq_refl eq_refl eq_refl FRH) as (MEM4 & HPIC4 & HPPC4).
             pose proof (UWK m4 AXP4) as UW4.
             pose proof MEM4 as (_ & _ & _ & _ & FRL4 & _). unfold ctl_frame0A in FRL4.
             pose proof PRE4 as (_ & _ & _ & _ & ST4 & _ & _ & _ & _ & MI4 & _ & _). rewrite ESPA in ST4.
             pose proof (bv_unsigned_in_range 64 z0) as ZR. unfold bv_modulus in ZR. cbn in ZR.
             assert (LR : 0 <= Z.land (bv_unsigned z0) 128 < 2 ^ 64).
             { split; [apply Z.land_nonneg; right; clear; lia|]. eapply Z.le_lt_trans; [apply land_le_lA; clear - ZR; lia| clear - ZR; lia]. }
             rewrite (ret_pc_even 0x24295c) by (clear; lia).
             pose proof (munch_refl (@nil (Z * Z)) m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
             apply implAp_from_evt. unfold MallocRep.wz.
             (* [comment removed for export] *)
             do 10 step.
             step. step. if_cases KB; zc KB; [| exfalso; apply B7; revert KB; rewrite ?unsigned_lit by exact LR; clear; intros KB; lia].
             apply evt_done.
             eapply (ctl_raiseA STRCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS 0x242ba8 1226 102 RS_tlen_bad_hdr 4%nat);
               [left; repeat split; reflexivity
               | eapply ctl_memA_reframe; [exact MEM4| intros HF; apply (ctl_frame0A_cb m4 spa j0 j8 j16 (CB 8 j24) (CB 8 j32) (C8 (Z_to_bv 64 SHB))); [reflexivity| reflexivity| reflexivity| exact HF]]
               | unfold go_costA; rewrite EG, KC3, KC6; clear; lia| exact UW4| rewrite ctl_frameA_size; clear - GSZ; lia| exact HPIC4| reflexivity| exact HPPC4| exact I].
        * (* [comment removed for export] *)
          intros r2 Σ7 ms7 RP. cbv beta.
          eapply (ctl_ret0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS (KE (snd r2)) Q r2 Σ7 ms7); [exact RP| reflexivity|].
          intros Σ' ms' PO. eapply (KE_ e); [reflexivity| replace (ctl_costA g ot) with (1 + go_costA g + GETOBJ_ERR_COST_A) by (unfold ctl_costA; rewrite EG; clear; lia); exact PO].
      + (* [comment removed for export] *)
        eapply (implAp_seq_ret (tt, st)) with (Q1 := GPOST); [unfold CtRepP.W_get_object.go_eff in CALL; rewrite EG in CALL; exact CALL|].
        intros Σ4 ms4 PO4. cbv beta in PO4. subst GPOST. unfold getobj_postA in PO4. cbn [fst snd] in PO4. rewrite EG in PO4.
        destruct PO4 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m4 & OW4 & jl4 & jt4 & jc4 & -> & PRE4 & AXP4 & CRED4 & KEPT4 & HPP4 & -> & HPL4 & HPT4 & HPC4).
        rewrite ?ESPA in AXP4. unfold MallocRep.wz in HPP4, HPL4, HPT4, HPC4.
        destruct (AFTER mc m4 Σ4 st OW4 _ (CB 8 j24) (CB 8 j32) (C8 (Z_to_bv 64 SHB)) MUc HWN PRE4 AXP4 CRED4 KEPT4 FRL eq_refl eq_refl eq_refl FRH) as (MEM4 & HPIC4 & HPPC4).
        replace (1 + go_costA g) with 1 in MEM4 by (unfold go_costA; rewrite EG; clear; lia).
        pose proof (UWK m4 AXP4) as UW4.
        pose proof MEM4 as (_ & _ & _ & _ & FRL4 & _). unfold ctl_frame0A in FRL4.
        pose proof PRE4 as (_ & _ & _ & _ & ST4 & _ & _ & _ & _ & MI4 & _ & _). rewrite ESPA in ST4.
        rewrite (ret_pc_even 0x24295c) by (clear; lia).
        pose proof (munch_refl (@nil (Z * Z)) m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
        apply implAp_from_evt. unfold MallocRep.wz.
        do 10 step. apply evt_done.
        eapply (ctl_okA STRCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS _ _ _ _ _ _ _ _ KE KW KS Q);
          [exact EG
          | eapply ctl_memA_reframe; [exact MEM4| intros HF; apply (ctl_frame0A_cb m4 spa j0 j8 j16 (CB 8 j24) (CB 8 j32) (C8 (Z_to_bv 64 SHB))); [reflexivity| reflexivity| reflexivity| exact HF]]
          | exact UW4| exact HPIC4| exact HPPC4| exact I| exact HPT4| exact HPC4| exact HPL4| exact HPP4
          | intros t st' Σ' ms' bi' bc' jl' ET _ NE PO; exact (KW_ t st' Σ' ms' bi' bc' jl' ET eq_refl NE PO)
          | intros st' Σ' ms' _ HM PO; exact (KS_ st' Σ' ms' eq_refl HM PO)].
    - (* [comment removed for export] *)
      destruct TLCo as [tlc|]; [| exfalso; apply KCTX; reflexivity].
      destruct HTLC as ((bt & HBT & TB1 & TB2) & ALT & HTLC).
      assert (HBT' : In bt (OW ++ LB)) by (apply in_or_app; right; exact HBT).
      pose proof (AH_range_gen _ _ _ _ _ HEAP HBT') as (BT0 & _ & _ & BT3 & BT4).
      pose proof (OFFLB bt HBT) as OBT. unfold off_fr in OBT. change (fs_size 1) with 128 in OBT. cbn [blk_addr blk_size fst snd] in OBT.
      assert (ETLC : bv_unsigned (Z_to_bv 64 tlc) = tlc) by (apply unsigned_lit; clear - BT0 BT3 TB1 TB2 CN; alia).
      clear KCTX.
      pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bt HEAPX ltac:(apply in_or_app; right; apply INX; exact HBT))) as ACCT.
      pose proof (@AH_offsh (push AR f 1) _ _ _ _ bt HEAPX ltac:(apply in_or_app; right; apply INX; exact HBT)) as OFFT.
      apply (rw_cells_agree _ _ _ _ _ AGF) in HTLC; [| intros a Ha; cbn in Ha; right; right; exists bt; split; [exact HBT'| clear - Ha TB1 TB2; lia]].
      unfold CtRepP.W_check_tlen.tlc_in in HTLC.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      step.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with MU : munch _ m3 mx |- _ =>
          eapply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HTLC;
            [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; clear - Ha BT3 TB1 TB2 OBT CEIL LOSP SPAL VPOS; plia]
        end end.
      (* [comment removed for export] *)
      step. step. step. step. if_true.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
      match goal with H : munch _ m3 mc |- _ => rename H into MUc end. match goal with H : wmono ctasegs m3 mc |- _ => rename H into WMc end.
      match goal with H : stk ctasegs mc lo spa |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end.
      apply evt_done.
      (* [comment removed for export] *)
      lazymatch type of FRL with rw_cells _ _ _ (_ :: _ :: _ :: C8 ?v :: _) => set (v24 := v) in FRL end.
      (* [comment removed for export] *)
      assert (HEAPc : @BnHeapA.AHEAP (push AR f 1) Σ1 OW (pbs ++ LB) mc).
      { eapply (@AH_frame (push AR f 1)); [exact HEAPX| exact MUc| exact WMc|].
        constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAL SPAH TOP VPOS; plia|].
        constructor; [right; right; exists (qp, f + 96, 8); split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear; lia]| constructor]. }
      assert (AGLc : agree_on (lib_addr OW) m3 mc).
      { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a HL. cbn [outside fst snd].
        destruct HL as [HS|(b & Hb & Hr)].
        - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA G4 CN CEIL LOSP SPAL VPOS. plia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFOW b Hb) as O.
          unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4, O. clear - Hr R4 O CEIL LOSP SPAL VPOS. lia. }
      assert (PREc : @ap_preA (push AR f 1) Σ1 st mc OW (pbs ++ LB) E bo (Z_to_bv 64 spa) lo GETOBJ_STACK_A GETOBJ_ERR_COST_A GETOBJ_FRAMES_A).
      { eapply (@ap_preA_memA (push AR f 1)); [eapply ap_preA_weaken; [exact PRE1| clear; lia| rewrite KC3; clear; lia| clear - VPOS; lia]| exact HEAPc| exact AGLc| rewrite ESPA; exact STc| exact MIc]. }
      assert (PAYc : payload_okA mc (pbs ++ LB) D d).
      { eapply payload_okA_monoA; [| exact INX]. eapply payload_okA_agreeA; [exact PAY3|].
        eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a (b & Hb & Hr). cbn [outside fst snd].
        pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFLB b Hb) as O.
        unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4, O. clear - Hr R4 O CEIL LOSP SPAL VPOS. lia. }
      assert (CIN : forall q A n, In (q, A, n) pbs -> cellA_in (pbs ++ LB) A n).
      { intros q A n Hin. exists (q, A, n). split; [apply in_or_app; left; exact Hin| cbn; clear; lia]. }
      assert (GC : go_cellsA_ok (pbs ++ LB) (f + 96) (f + 64) (f + 32) (f + 48)).
      { split; [apply (CIN qp); subst pbs; cbn; tauto|]. split; [apply (CIN ql); subst pbs; cbn; tauto|]. split; [apply (CIN qt); subst pbs; cbn; tauto|].
        split; [apply (CIN qc); subst pbs; cbn; tauto|]. clear - G2. Z.div_mod_to_equations. lia. }
      assert (GOFF : go_cells_offA D (zlength d) (f + 96) (f + 64) (f + 32) (f + 48)).
      { unfold go_cells_offA. clear - OD PA1 PA2. lia. }
      (* [comment removed for export] *)
      assert (UWc : uw_chain USTACK_TOP mc spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { eapply (uw_call m mc spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
          [ exact UW
          | eapply agree_on_trans; [ eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha
                                   | eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]; intros a Ha; cbn [outside fst snd]; clear - Ha SPAH FLO; lia ]
          | reflexivity | clear - SPAH; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia
          | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH ]. }
      pose proof (FACTSof bt (conj HBT (conj TB1 (conj TB2 ALT)))) as FACTS.
      rewrite ?EPPC in FRL. rewrite ?ETLC.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (CALL : @implAp (push AR f 1) _ (go_eff g st) Σ1
          (@getobj_postA (push AR f 1) (Z_to_bv 64 0x2429a0) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 f) (Z_to_bv 64 tlc) (Z_to_bv 64 0) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (tlc + 4)) (Z_to_bv 64 (Z.shiftr tlc 3 + SHB)) (Z_to_bv 64 SHB)
                        Σ1 OW (pbs ++ LB) E bo lo mc K D (f + 96) (f + 64) (f + 32) (f + 48) g)
          (MS (mkR (Z_to_bv 64 0x2429a0) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 (f + 48)) t1' t2' sp (Z_to_bv 64 spa)
                   (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 len) (Z_to_bv 64 (D + op)) (Z_to_bv 64 len) a7'
                   (Z_to_bv 64 f) (Z_to_bv 64 tlc) (Z_to_bv 64 0) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (tlc + 4)) (Z_to_bv 64 (Z.shiftr tlc 3 + SHB)) (Z_to_bv 64 SHB) t3' t4' t5' t6')
              F' (Z_to_bv 64 ASN1_GET_OBJECT_A) fc' None mc (seg_rom ctasegs))).
      { pose proof (@ASN1_get_object_closedA (push AR f 1) UK BE STRCPY) as HGO. unfold ASN1_get_object_specA in HGO.
        eapply HGO with (K := K) (LB := pbs ++ LB) (lo := lo) (D := D) (d := d) (op := op) (omax := len)
                                                                          (PP := f + 96) (PL := f + 64) (PT := f + 32) (PC := f + 48);
          [exact PREc| reflexivity| rewrite ESPA; exact UWc| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_go CTX)| apply cons_ne
          | exact KOW| exact KIDS| exact PAYc| exact OP0| exact TL0| exact OPT| exact GC| exact GOFF| exact OP3| exact OL3| exact OT3| exact OC3
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      match type of CALL with implAp _ _ ?P ?MSc => pose (GPOST := P); change (implAp (go_eff g st) Σ1 GPOST MSc) in CALL end.
      assert (HWN : forall a, outside [(spa, spa + 152); (f + 96, f + 104)]%Z a \/ (spa <= a < spa + 152) \/ (f + 96 <= a < f + 104))
        by (intros a; cbn [outside fst snd]; clear; lia).
      assert (UWK : forall m4, ax_pres (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) mc m4 ->
                uw_chain USTACK_TOP m4 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { intros m4 AXP4. eapply uw_chain_agree16; [exact UWc|]. eapply agree_on_mono; [exact AXP4|]. intros a Ha. cbv beta in Ha. split; [| left; clear - Ha SPAH; lia].
        intros HY. apply rin_ivs_app in HY. destruct HY as [HY|HY]; [cbn [rin_ivs fst snd app] in HY; clear - HY Ha FLO SPAH; lia|].
        pose proof (libw_below a HY) as Hb. unfold SEGTOP_A in Hb. clear - Hb Ha CN CEIL LOSP SPAH VPOS. plia. }
      (* [comment removed for export] *)
      assert (TLK : forall m4, ax_pres (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) mc m4 ->
                rw_cells ctasegs m4 tlc [C1 (Z_to_bv 8 0); CB 31 j31]).
      { intros m4 AXP4. eapply rw_cells_agree; [exact AXP4| exact HTLC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split.
        - unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha OBT TB1 TB2 BT4. lia.
        - right; right. exists bt. split; [apply INX; exact HBT| clear - Ha TB1 TB2; lia]. }
      assert (HLg : 0 <= go_p g - op <= len).
      { clear - GB TL0. destruct (go_err g) as [[| |]|]; [lia| lia| destruct GB| lia]. }
      clear HEAPc AGLc PREc PAYc CIN GC GOFF.
      destruct (go_err g) as [e|] eqn:EG.
      + (* [comment removed for export] *)
        unfold CtColP.W_check_tlen_gen.tlen_tree. rewrite EG.
        eapply implAp_abind.
        * unfold tlen_fail. eapply implAp_abind with (Q1 := GPOST).
          -- unfold CtRepP.W_get_object.go_eff in CALL. rewrite EG in CALL. exact CALL.
          -- intros r1 Σ4 ms4 PO4. cbv beta in PO4. subst GPOST. unfold getobj_postA in PO4. cbn [fst snd] in PO4. rewrite EG in PO4.
             destruct PO4 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m4 & OW4 & jl4 & jt4 & jc4 & -> & PRE4 & AXP4 & CRED4 & KEPT4 & HPP4 & RES4).
             rewrite ?ESPA in AXP4. unfold MallocRep.wz in HPP4, RES4.
             assert (CELLS : (Z.land (bv_unsigned z0) 128 <> 0 /\ Z.land (bv_unsigned z0) 129 <> 0)
                             /\ exists jl' j2' j3', rw_cells ctasegs m4 (f + 64) [CB 8 jl'] /\ rw_cells ctasegs m4 (f + 32) [CB 4 j2'] /\ rw_cells ctasegs m4 (f + 48) [CB 4 j3']).
             { destruct e; [| | destruct GB].
               - destruct RES4 as (-> & H1 & H2 & H3). split; [rewrite !unsigned_lit by (clear; lia); change (Z.land 128 128) with 128; change (Z.land 128 129) with 128; clear; lia|].
                 exists jl4, jt4, jc4. split; [exact H1| split; [exact H2| exact H3]].
               - destruct RES4 as (-> & H1 & H2 & H3). split.
                 + pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
                   assert (LV : (Z.lor (go_ret g) 128 = 128 \/ Z.lor (go_ret g) 128 = 129) \/ (Z.lor (go_ret g) 128 = 160 \/ Z.lor (go_ret g) 128 = 161)).
                   { destruct RC as [E0|[E0|[E0|E0]]]; rewrite E0; [left; left| left; right| right; left| right; right]; reflexivity. }
                   assert (LA : Z.land (Z.lor (go_ret g) 128) 128 = 128 /\ (Z.land (Z.lor (go_ret g) 128) 129 = 128 \/ Z.land (Z.lor (go_ret g) 128) 129 = 129) /\ 0 <= Z.lor (go_ret g) 128 < 2 ^ 64).
                   { destruct LV as [[E1|E1]|[E1|E1]]; rewrite E1; (split; [reflexivity| split; [first [left; reflexivity| right; reflexivity]| clear; lia]]). }
                   destruct LA as (LA1 & LA3 & LA2). rewrite !unsigned_lit by exact LA2. rewrite LA1. clear - LA3; lia.
                 + apply (rw_cells_cb_first m4 _ _ 1) in H1. apply (rw_cells_cb_first m4 _ _ 1) in H2. apply (rw_cells_cb_first m4 _ _ 1) in H3. cbn [cb_first csize] in H1, H2, H3.
                   eexists _, _, _. split; [exact H1| split; [exact H2| exact H3]]. }
             clear RES4. destruct CELLS as ([B7 B81] & jl' & j2' & j3' & OL4 & OT4 & OC4).
             destruct (AFTER mc m4 Σ4 (snd r1) OW4 _ (C8 v24) (C8 (Z_to_bv 64 (f + 48))) (C8 (Z_to_bv 64 0)) MUc HWN PRE4 AXP4 CRED4 KEPT4 FRL eq_refl eq_refl eq_refl FRH) as (MEM4 & HPIC4 & HPPC4).
             pose proof (UWK m4 AXP4) as UW4. pose proof (TLK m4 AXP4) as HTLC4.
             rewrite (ret_pc_even 0x2429a0) by (clear; lia).
             eapply (ctl_cacheA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS j0 j8 j16 j128 j136);
               [exact MEM4| exact UW4| exact HPIC4| reflexivity| exact HPPC4| exact HTLC4| exact OT4| exact OC4| exact OL4| exact HPP4| exact HLg| left; exact B81|].
             (* [comment removed for export] *)
             intros ma x11' x12' x13' x14' x16' MEMa UWa HPICa HPPCa HTLCa OTa OCa OLa OPa.
             pose proof MEMa as (PREa & _ & _ & _ & FRLa & _). unfold ctl_frameA in FRLa.
             pose proof PREa as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & _ & _). rewrite ESPA in STa.
             pose proof (bv_unsigned_in_range 64 z0) as ZR. unfold bv_modulus in ZR. cbn in ZR.
             assert (LR : 0 <= Z.land (bv_unsigned z0) 128 < 2 ^ 64).
             { split; [apply Z.land_nonneg; right; clear; lia|]. eapply Z.le_lt_trans; [apply land_le_lA; clear - ZR; lia| clear - ZR; lia]. }
             pose proof (munch_refl (@nil (Z * Z)) ma) as MUa. pose proof (wmono_refl ctasegs ma) as WMa.
             apply implAp_from_evt. unfold MallocRep.wz.
             step. step. if_cases KB; zc KB; [| exfalso; apply B7; revert KB; rewrite ?unsigned_lit by exact LR; clear; intros KB; lia].
             apply evt_done.
             eapply (ctl_raiseA STRCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS 0x242ba8 1226 102 RS_tlen_bad_hdr 4%nat);
               [left; repeat split; reflexivity| exact MEMa| unfold go_costA; rewrite EG, KC3, KC6; clear; lia| exact UWa| rewrite ctl_frameA_size; clear - GSZ; lia
               | exact HPICa| reflexivity| exact HPPCa| exact HTLCa].
        * (* [comment removed for export] *)
          intros r2 Σ7 ms7 RP. cbv beta.
          eapply (ctl_ret0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS (KE (snd r2)) Q r2 Σ7 ms7); [exact RP| reflexivity|].
          intros Σ' ms' PO. eapply (KE_ e); [reflexivity| replace (ctl_costA g ot) with (1 + go_costA g + GETOBJ_ERR_COST_A) by (unfold ctl_costA; rewrite EG; clear; lia); exact PO].
      + (* [comment removed for export] *)
        eapply (implAp_seq_ret (tt, st)) with (Q1 := GPOST); [unfold CtRepP.W_get_object.go_eff in CALL; rewrite EG in CALL; exact CALL|].
        intros Σ4 ms4 PO4. cbv beta in PO4. subst GPOST. unfold getobj_postA in PO4. cbn [fst snd] in PO4. rewrite EG in PO4.
        destruct PO4 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m4 & OW4 & jl4 & jt4 & jc4 & -> & PRE4 & AXP4 & CRED4 & KEPT4 & HPP4 & -> & HPL4 & HPT4 & HPC4).
        rewrite ?ESPA in AXP4. unfold MallocRep.wz in HPP4, HPL4, HPT4, HPC4.
        destruct (AFTER mc m4 Σ4 st OW4 _ (C8 v24) (C8 (Z_to_bv 64 (f + 48))) (C8 (Z_to_bv 64 0)) MUc HWN PRE4 AXP4 CRED4 KEPT4 FRL eq_refl eq_refl eq_refl FRH) as (MEM4 & HPIC4 & HPPC4).
        replace (1 + go_costA g) with 1 in MEM4 by (unfold go_costA; rewrite EG; clear; lia).
        pose proof (UWK m4 AXP4) as UW4. pose proof (TLK m4 AXP4) as HTLC4.
        pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
        assert (RB : 0 <= go_ret g < 64) by (destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; clear; lia).
        destruct GB as (GB1 & GB2 & GB3).
        apply (rw_cells_cb_first m4 _ _ 1) in HPL4. apply (rw_cells_cb_first m4 _ _ 1) in HPT4. apply (rw_cells_cb_first m4 _ _ 1) in HPC4. cbn [cb_first csize] in HPL4, HPT4, HPC4.
        rewrite (ret_pc_even 0x2429a0) by (clear; lia).
        eapply (ctl_cacheA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS j0 j8 j16 j128 j136);
          [exact MEM4| exact UW4| exact HPIC4| reflexivity| exact HPPC4| exact HTLC4| exact HPT4| exact HPC4| exact HPL4| exact HPP4| exact HLg| |].
        { (* [comment removed for export] *)
          rewrite (unsigned_lit (go_ret g)) by (clear - RB; lia).
          destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER;
            [right; split; [reflexivity| split; [reflexivity| split; [exact GB2| exact GB3]]]| left; clear; cbv; discriminate
            | right; split; [reflexivity| split; [reflexivity| split; [exact GB2| exact GB3]]]| left; clear; cbv; discriminate]. }
        intros ma x11' x12' x13' x14' x16' MEMa UWa HPICa HPPCa HTLCa OTa OCa OLa OPa.
        apply (rw_cells_recast ma (f + 32) _ [C4 (Z_to_bv 64 (go_tag g))]) in OTa; [| cbn; repeat split; exact I| reflexivity| reflexivity].
        apply (rw_cells_recast ma (f + 48) _ [C4 (Z_to_bv 64 (go_cls g))]) in OCa; [| cbn; repeat split; exact I| reflexivity| reflexivity].
        apply (rw_cells_recast ma (f + 64) _ [C8 (Z_to_bv 64 (go_len g))]) in OLa; [| cbn; repeat split; exact I| reflexivity| reflexivity].
        eapply (ctl_okA STRCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS _ _ _ _ _ _ _ _ KE KW KS Q);
          [exact EG| exact MEMa| exact UWa| exact HPICa| exact HPPCa| exact HTLCa| exact OTa| exact OCa| exact OLa| exact OPa
          | intros t st' Σ' ms' bi' bc' jl'' ET _ NE PO; exact (KW_ t st' Σ' ms' bi' bc' jl'' ET eq_refl NE PO)
          | intros st' Σ' ms' _ HM PO; exact (KS_ st' Σ' ms' eq_refl HM PO)].
  Qed.
End Proofs.
End Kit.
