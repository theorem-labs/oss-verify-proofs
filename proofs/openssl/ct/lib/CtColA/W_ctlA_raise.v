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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_check_tlen_genA W_ctlA_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac clia := cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb length] in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_ASN1_CHECK_TLEN_FN_A : Z := 0x72de0.

(* [comment removed for export] *)
Definition ctl_siteA (base line reason : Z) (rs : rsite) (nmid : nat) : Prop :=
  (base = 0x242ba8 /\ line = 1226 /\ reason = 102 /\ rs = RS_tlen_bad_hdr /\ nmid = 4%nat)
  \/ (base = 0x242cfc /\ line = 1236 /\ reason = 168 /\ rs = RS_tlen_wrong_tag /\ nmid = 5%nat).

Local Notation E_new1 := (E_asn1_check_tlen_245628 : uk_call 0x2426a8 0x242bac 0x1fd52c).
Local Notation E_dbg1 := (E_asn1_check_tlen_245640 : uk_call 0x2426a8 0x242bc4 0x1fd844).
Local Notation E_err := (E_asn1_check_tlen_245650 : uk_call 0x2426a8 0x242bd4 0x1fdab8).
Local Notation E_new2 := (E_asn1_check_tlen_245784 : uk_call 0x2426a8 0x242d00 0x1fd52c).
Local Notation E_dbg2 := (E_asn1_check_tlen_24579c : uk_call 0x2426a8 0x242d18 0x1fd844).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Act.
  Hypothesis STRCPY : strcpy_icontract RT.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m3 : mem) (Σ Σ1 : rts RT) (OW LB K : list block) (E : ap_env) (lo : Z) (ras : list Z).
  Variables (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo ot : option Z) (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) (qp ql qt qc : bptr).
  Hypothesis FACTS : ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC TLCo ot f spa gg junk gj bd bt.
  Local Notation pbs := (actl_pbs f qp ql qt qc).
  Local Notation XX := (ctl_XX PIC PPC TLCo).
  Local Notation memA := (ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc).

  Local Ltac ecu := unfold GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST, ERR_NEW_FRAMES, ERR_SET_DEBUG_FRAMES,
                           ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in *.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ctl_raiseA : forall (base line reason : Z) (rs : rsite) (nmid : nat)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (ma : mem) (Σ4 : rts RT) (st4 : ap_st bptr) (OW4 : list block) (bo4 : Z * Z) (spent : Z) (frame : list cell) (cpic : list cell) (pp : Z),
    ctl_siteA base line reason rs nmid ->
    memA ma Σ4 st4 OW4 bo4 spent frame -> spent + GETOBJ_ERR_COST_A <= CHECK_TLEN_GEN_COST_A ->
    uw_chain USTACK_TOP ma spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
    spa + Z.of_nat (cells_size frame) <= bv_unsigned sp ->
    rw_cells ctasegs ma PIC cpic -> cells_size cpic = 10%nat -> rw_cells ctasegs ma PPC [C8 (Z_to_bv 64 pp)] -> ctl_tlcA TLCo ma ->
    implAp (err_raise rs st4) Σ4
      (ctl_rpostA ra sp gp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc (spent + GETOBJ_ERR_COST_A) frame x20 x24 x25 x26 cpic pp)
      (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) x24 x25 x26 (Z_to_bv 64 SHB) x28 x29 x30 x31)
          F (Z_to_bv 64 base) fc None ma (seg_rom ctasegs)).
  Proof.
    intros until pp. intros SITE MEM CXG UW4 FSZ HPIC SZP HPPC HTLC. ctl_facts FACTS.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). rewrite KC3, KC6 in CXG.
    destruct MEM as (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH).
    pose proof PRE4 as (HEAP4 & AS4 & IDS4 & DC4 & ST4 & CEIL4 & LOSP4 & TOP4 & AL164 & MI4 & _ & FRM4). rewrite ESPA in ST4, LOSP4, TOP4, AL164.
    cbn [ar_FR ar_RT push amb length] in FRM4, CRED4.
    destruct (lit_okA_auto A_TASN_DEC_C_A 23 ltac:(vm_compute; reflexivity)) as (fs' & fk & LF).
    destruct (lit_okA_auto A_ASN1_CHECK_TLEN_FN_A 16 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 23) by (destruct SITE as [(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]; reflexivity).
    assert (RSN : rs_fnlen rs = 16) by (destruct SITE as [(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]; reflexivity).
    assert (RSL : rs_line rs = line) by (destruct SITE as [(_ & -> & _ & -> & _)|(_ & -> & _ & -> & _)]; reflexivity).
    assert (RC : rs_code rs = ERR_PACK 13 reason /\ 0 <= reason < 8388608) by (destruct SITE as [(_ & _ & -> & -> & _)|(_ & _ & -> & -> & _)]; (split; [reflexivity| clear; lia])).
    destruct RC as [RC RB]. rewrite <- RSF in LF. rewrite <- RSN in LN.
    pose proof (KEPT4) as (KOW4 & KID4 & KP4).
    assert (KIDS4 : forall b, In b K -> ~ In (blk_id b) (es_ids st4 ++ env_ids E)).
    { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (KID4 b Hb Hin)| exact (KIDE b Hb Hin)]. }
    (* [comment removed for export] *)
    assert (UWK : forall mA mB, ax_pres (pbs ++ LB) spa LIBW_A mA mB ->
                  uw_chain USTACK_TOP mA spa (bv_unsigned sp) (bv_unsigned ra :: ras) -> uw_chain USTACK_TOP mB spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { intros mA mB AX UWx. apply (uw_chain_axpres _ _ _ _ _ _ _ AX) in UWx; [exact UWx| clear - SPAH; lia| clear - CN CEIL LOSP; alia]. }
    assert (STW : forall a, spa <= a -> a < USTACK_TOP -> ax_client (pbs ++ LB) spa LIBW_A a).
    { intros a Ha Hb. split; [| left; clear - Ha Hb; lia]. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha CN CEIL LOSP SPAL. plia. }
    assert (TLW : match TLCo with Some a => forall x, a <= x < a + 32 -> ax_client (pbs ++ LB) spa LIBW_A x | None => True end).
    { destruct TLCo as [a|]; [| exact I]. destruct TB as (HBT & TB1 & TB2 & _). intros x Hx.
      pose proof (@AH_range_gen (push AR f 1) _ _ _ _ bt HEAP4 ltac:(apply in_or_app; right; apply in_or_app; right; exact HBT)) as (_ & _ & _ & _ & BT4).
      split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Hx TB1 TB2 BT4; lia|].
      right; right. exists bt. split; [apply in_or_app; right; exact HBT| clear - Hx TB1 TB2; lia]. }
    assert (CELLK : forall mA mB, ax_pres (pbs ++ LB) spa LIBW_A mA mB ->
              rw_cells ctasegs mA spa frame -> rw_cells ctasegs mA (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
              rw_cells ctasegs mA PIC cpic -> rw_cells ctasegs mA PPC [C8 (Z_to_bv 64 pp)] -> ctl_tlcA TLCo mA ->
              rw_cells ctasegs mB spa frame /\ rw_cells ctasegs mB (bv_unsigned sp + -16) [C8 s0; C8 ra]
              /\ rw_cells ctasegs mB PIC cpic /\ rw_cells ctasegs mB PPC [C8 (Z_to_bv 64 pp)] /\ ctl_tlcA TLCo mB).
    { intros mA mB AX H1 H2 H3 H4 H5.
      split; [eapply rw_cells_agree; [exact AX| exact H1| intros a Ha; apply STW; clear - Ha FSZ TOP; unfold USTACK_TOP in *; lia]|].
      split; [eapply rw_cells_agree; [exact AX| exact H2| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia]|].
      split; [eapply rw_cells_agree; [exact AX| exact H3| intros a Ha; rewrite SZP in Ha; apply STW; clear - Ha SPAH PIClo PIChi; unfold USTACK_TOP in *; lia]|].
      split; [eapply rw_cells_agree; [exact AX| exact H4| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPAH PPClo PPChi; unfold USTACK_TOP in *; lia]|].
      destruct TLCo as [a|]; [| exact I]. destruct H5 as (vb & j & H5). exists vb, j.
      eapply rw_cells_agree; [exact AX| exact H5| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply TLW; clear - Hx; lia]. }
    (* [comment removed for export] *)
    assert (AXK : forall mA mB, ax_pres (pbs ++ LB) spa LIBW_A mA mB -> agree_on (ax_client LB (bv_unsigned sp) (XX ++ LIBW_A)) mA mB).
    { intros mA mB AX. eapply agree_on_mono; [exact AX|]. intros a [HX Hc]. split.
      - intros HY. apply HX. unfold ctl_XX. cbn [rin_ivs app]. right; right; right. exact HY.
      - destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; clear - H1 SPAH; lia| right; left; exact H1| right; right].
        exists b. split; [apply in_or_app; right; exact Hb| exact Hr]. }
    unfold err_raise.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (ΣA : rts RT) (rad : Z) (q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1,
      ((rad = 0x242bc4 /\ nmid = 4%nat /\ reason = 102) \/ (rad = 0x242d18 /\ nmid = 5%nat /\ reason = 168)) ->
      @ap_preA (push AR f 1) ΣA (snd r1) mA OW1 (pbs ++ LB) E bo4 (Z_to_bv 64 spa) lo 0 0 0 ->
      blocks_kept K (snd r1) OW1 m mA -> agree_on (ax_client LB (bv_unsigned sp) (XX ++ LIBW_A)) m mA ->
      rt_credit RT Σ - (spent + ERR_NEW_COST) <= rt_credit RT ΣA ->
      uw_chain USTACK_TOP mA spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
      rw_cells ctasegs mA spa frame -> rw_cells ctasegs mA (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells ctasegs mA PIC cpic -> rw_cells ctasegs mA PPC [C8 (Z_to_bv 64 pp)] -> ctl_tlcA TLCo mA ->
      implAp (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)) ΣA
        (ctl_rpostA ra sp gp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc (spent + GETOBJ_ERR_COST_A) frame x20 x24 x25 x26 cpic pp)
        (MS (mkR (Z_to_bv 64 rad) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 spa)
                  (Z_to_bv 64 A_TASN_DEC_C_A) (Z_to_bv 64 line) (Z_to_bv 64 A_ASN1_CHECK_TLEN_FN_A) q13 q14 q15 q16 q17
                  (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) x24 x25 x26 (Z_to_bv 64 SHB) q28 q29 q30 q31)
            F1 (Z_to_bv 64 ERR_SET_DEBUG) fc1 None mA (seg_rom ctasegs))).
    { intros until OW1. intros HS PREa KEPTa AXa CRa UWa FRLa FRHa HPICa HPPCa HTLCa.
      pose proof KEPTa as (KOWa & KIDa & _).
      assert (KIDSa : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (KIDa b Hb Hin)| exact (KIDE b Hb Hin)]. }
      assert (Edbg : uk_ctx ERR_SET_DEBUG (rad :: bv_unsigned ra :: ras)).
      { destruct HS as [(-> & _)|(-> & _)]; [exact (uk_ctx_call _ _ _ _ E_dbg1 CTX)| exact (uk_ctx_call _ _ _ _ E_dbg2 CTX)]. }
      assert (RADR : 0 <= rad < 2 ^ 64) by (destruct HS as [(-> & _)|(-> & _)]; clear; lia).
      eapply implAp_abind.
      { pose proof (@ERR_set_debug_walkA (push AR f 1) UK BE STRCPY rs A_TASN_DEC_C_A A_ASN1_CHECK_TLEN_FN_A bo4 _ _ _ _ LF LN) as W2. unfold ap_stmtA in W2.
        eapply W2; [eapply ap_preA_restockA; [exact PREa| rewrite ESPA; ecu; clear - LOSP SPAL; clia| ecu; clear - CRED CRa CXG; clia| ecu; clear; clia| ecu; cbn [ar_FR push amb length]; clear - FRMX; clia]
                  | reflexivity| rewrite ESPA; exact UWa| rewrite unsigned_lit by exact RADR; exact Edbg| apply cons_ne
                  | unfold MallocRep.wz; rewrite RSL; repeat split; reflexivity| exact KOWa| exact KIDSa]. }
      intros r2 ΣB ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & bo2 & -> & PREb & AXb & CRb & BKb & EBO2). subst bo2.
      rewrite ESPA in AXb. pose proof (UWK _ _ AXb UWa) as UWb.
      destruct (CELLK _ _ AXb FRLa FRHa HPICa HPPCa HTLCa) as (FRLb & FRHb & HPICb & HPPCb & HTLCb).
      pose proof (blocks_kept_transA K _ _ _ _ m mA mB KEPTa BKb) as KEPTb. pose proof KEPTb as (KOWb & KIDb & _).
      assert (KIDSb : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (KIDb b Hb Hin)| exact (KIDE b Hb Hin)]. }
      rewrite (ret_pc_even rad) by (destruct HS as [(-> & _)|(-> & _)]; clear; lia).
      pose proof PREb as (HEAPb & _ & _ & _ & STb & _ & _ & _ & _ & MIb & CREDb & _). rewrite ESPA in STb. cbn [ar_RT push amb] in CRb, CREDb.
      (* [comment removed for export] *)
      assert (SE : forall (q5' q6' q7' q13' q14' q15' q16' q17' q28' q29' q30' q31' : word),
        implAp (err_set_error rs (snd r2)) ΣB
          (ctl_rpostA ra sp gp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc (spent + GETOBJ_ERR_COST_A) frame x20 x24 x25 x26 cpic pp)
          (MS (mkR (Z_to_bv 64 0x242bd4) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) q5' q6' q7' sp (Z_to_bv 64 spa)
                    (Z_to_bv 64 13) (Z_to_bv 64 reason) (Z_to_bv 64 0) q13' q14' q15' q16' q17'
                    (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) x24 x25 x26 (Z_to_bv 64 SHB) q28' q29' q30' q31')
              F2 (Z_to_bv 64 ERR_SET_ERROR) fc2 None mB (seg_rom ctasegs))).
      { intros.
        eapply implAp_mono.
        { pose proof (ERR_set_error_closedA (push AR f 1) UK BE rs 13 reason bo4) as W3. unfold ERR_set_error_specA, ap_stmtA in W3.
          eapply W3; [eapply ap_preA_restockA; [exact PREb| rewrite ESPA; ecu; clear - LOSP SPAL; clia| ecu; clear - CRED CRa CRb CXG; clia| ecu; clear; clia| ecu; cbn [ar_FR push amb length]; clear - FRMX; clia]
                    | reflexivity| rewrite ESPA; exact UWb| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_err CTX)| apply cons_ne
                    | unfold ERR_LIB_SYS, MallocRep.wz; repeat split; first [reflexivity| exact RC| (clear - RB; lia)| (clear; lia)]| exact KOWb| exact KIDSb]. }
        intros r3 ΣC ms3 PO3. cbv beta in PO3.
        destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & bo3 & -> & PREc & AXc & CRc & BKc & EBO3). subst bo3.
        rewrite ESPA in AXc. cbn [ar_RT push amb] in CRc.
        destruct (CELLK _ _ AXc FRLb FRHb HPICb HPPCb HTLCb) as (FRLc & FRHc & HPICc & HPPCc & HTLCc).
        rewrite (ret_pc_even 0x242bd4) by (clear; lia).
        unfold ctl_rpostA. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, bo4.
        split; [reflexivity|].
        split.
        { split; [exact PREc|]. split; [exact (blocks_kept_transA K _ _ _ _ m mB mC KEPTb BKc)|].
          split; [eapply agree_on_trans; [exact AXa| eapply agree_on_trans; [exact (AXK _ _ AXb)| exact (AXK _ _ AXc)]]|].
          split; [ecu; rewrite KC3; clear - CRa CRb CRc; clia|].
          split; [exact FRLc| exact FRHc]. }
        split; [exact HPICc|]. split; [exact HPPCc| exact HTLCc]. }
      pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
      apply implAp_from_evt. unfold MallocRep.wz.
      destruct HS as [(-> & -> & ->)|(-> & -> & ->)].
      - do 4 step. apply evt_done. apply SE.
      - do 5 step. apply evt_done. apply SE. }
    (* [comment removed for export] *)
    pose proof (munch_refl (@nil (Z * Z)) ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
    assert (HEAD : forall rad' : Z, ((base = 0x242ba8 /\ rad' = 0x242bc4) \/ (base = 0x242cfc /\ rad' = 0x242d18)) ->
      uk_ctx ERR_NEW (base + 4 :: bv_unsigned ra :: ras) ->
      implAp (abind err_new (fun _ : unit => abind (err_set_debug rs) (fun _ : unit => err_set_error rs)) st4) Σ4
        (ctl_rpostA ra sp gp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc (spent + GETOBJ_ERR_COST_A) frame x20 x24 x25 x26 cpic pp)
        (MS (mkR (Z_to_bv 64 (base + 4)) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) x24 x25 x26 (Z_to_bv 64 SHB) x28 x29 x30 x31)
            F (Z_to_bv 64 ERR_NEW) fc None ma (seg_rom ctasegs))).
    { intros rad' HB Enew.
      assert (BASR : 0 <= base + 4 < 2 ^ 64) by (destruct HB as [[-> _]|[-> _]]; clear; lia).
      eapply implAp_abind.
      { pose proof (@ERR_new_walkA (push AR f 1) UK BE bo4) as W1. unfold ap_stmtA in W1.
        eapply W1; [eapply ap_preA_restockA; [exact PRE4| rewrite ESPA; ecu; clear - LOSP SPAL; clia| ecu; clear - CRED CRED4 CXG; clia| ecu; clear; clia| ecu; clear - FRMX FRM4; clia]
                  | reflexivity| rewrite ESPA; exact UW4| rewrite unsigned_lit by exact BASR; exact Enew| apply cons_ne| reflexivity| exact KOW4| exact KIDS4]. }
      intros r1 ΣA ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & bo1 & -> & PREa & AXa & CRa & BKa & EBO1). subst bo1.
      rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa.
      destruct (CELLK _ _ AXa FRL FRH HPIC HPPC HTLC) as (FRLa & FRHa & HPICa & HPPCa & HTLCa).
      pose proof PREa as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & _ & _). rewrite ESPA in STa.
      rewrite (ret_pc_even (base + 4)) by (destruct HB as [[-> _]|[-> _]]; clear; lia).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      apply implAp_from_evt. unfold MallocRep.wz.
      destruct HB as [[-> ->]|[-> ->]]; [change (0x242ba8 + 4) with 0x242bac| change (0x242cfc + 4) with 0x242d00].
      - do 6 step. apply evt_done. change (Z_to_bv 64 0x72b80) with (Z_to_bv 64 A_TASN_DEC_C_A). change (Z_to_bv 64 0x72de0) with (Z_to_bv 64 A_ASN1_CHECK_TLEN_FN_A).
        destruct SITE as [(_ & -> & -> & _ & ->)|(EB & _)]; [| exfalso; clear - EB; discriminate EB].
        eapply (TAIL r1 ΣA 0x242bc4); [left; repeat split; reflexivity| exact PREa| exact (blocks_kept_transA K _ _ _ _ m ma mA KEPT4 BKa)| eapply agree_on_trans; [exact AX4| exact (AXK _ _ AXa)]
          | ecu; clear - CRED4 CRa; clia| exact (UWK _ _ AXa UW4)| exact FRLa| exact FRHa| exact HPICa| exact HPPCa| exact HTLCa].
      - do 6 step. apply evt_done. change (Z_to_bv 64 0x72b80) with (Z_to_bv 64 A_TASN_DEC_C_A). change (Z_to_bv 64 0x72de0) with (Z_to_bv 64 A_ASN1_CHECK_TLEN_FN_A).
        destruct SITE as [(EB & _)|(_ & -> & -> & _ & ->)]; [exfalso; clear - EB; discriminate EB|].
        eapply (TAIL r1 ΣA 0x242d18); [right; repeat split; reflexivity| exact PREa| exact (blocks_kept_transA K _ _ _ _ m ma mA KEPT4 BKa)| eapply agree_on_trans; [exact AX4| exact (AXK _ _ AXa)]
          | ecu; clear - CRED4 CRa; clia| exact (UWK _ _ AXa UW4)| exact FRLa| exact FRHa| exact HPICa| exact HPPCa| exact HTLCa]. }
    apply implAp_from_evt. unfold MallocRep.wz.
    destruct SITE as [(-> & _)|(-> & _)].
    - step. apply evt_done. apply (HEAD 0x242bc4); [left; split; reflexivity| exact (uk_ctx_call _ _ _ _ E_new1 CTX)].
    - step. apply evt_done. apply (HEAD 0x242d18); [right; split; reflexivity| exact (uk_ctx_call _ _ _ _ E_new2 CTX)].
  Qed.
End Act.
End WithRT.
