(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_rzt Fz_W3_dec Fz_W4_defs Fz_W4_init Fz_W4_update Fz_W4_final.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | apply wa_of_var; lia ].

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem INI_proof :
    RZT_stmt libenv errst_at_rest errst_live -> DEC_stmt libenv errst_at_rest errst_live -> INI_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros RZTP DECP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s9 s10 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 ta
           qc qn ctxv namev nn hBv dBv BMY bn KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM ER0 REM RA2 RB2 RBIG2 LXY LOC OWNC CTXC OWNN NN LBN NMC NUL MBX MBY LY1 ELB CFRESH EL NDT OUT.
    unfold DEC_stmt, J_DEC in DECP. unfold RZT_stmt, J_RZT in RZTP. unfold ECTX in *.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_INI, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (NDKY & NDC3 & DJY).
    (* [comment removed for export] *)
    destruct MBY as (BB & RP & fl & rrw & padw & nr & nw & OWNBI & NDK & METH & HEAD & W1C & FLOK & TAILC & (rmaxw & OWNBB & BBC & OWNBM & OWNRP & OFF0 & LENMAX & MAX31 & INNER)).
    destruct (k_d KY) as [pd|] eqn:KD; [| destruct INNER as [MX0 _]; exfalso; clear - MX0 LENMAX LY1; lia].
    destruct INNER as (D & nmd & junk & OWND & MAXP & BMC & RPC & LJ & DC).
    (* [comment removed for export] *)
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNC)) as (C0 & C16 & _ & CCL & CIMG'). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in CCL.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCL & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in DCL.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBM)) as (BM0 & BM16 & _ & BMCL & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in BMCL.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    assert (KYD : In pd (mbio_blocks KY)) by (unfold mbio_blocks; rewrite KD; apply in_or_app; right; left; reflexivity).
    assert (KYM : In (k_bm KY) (mbio_blocks KY)) by (unfold mbio_blocks; apply in_or_app; left; right; right; left; reflexivity).
    assert (NCD : qc <> pd) by (intros E; apply (DJY qc); [rewrite E; exact KYD| left; reflexivity]).
    assert (NCM : qc <> k_bm KY) by (intros E; apply (DJY qc); [rewrite E; exact KYM| left; reflexivity]).
    assert (NDM : pd <> k_bm KY).
    { intros E. unfold mbio_blocks in NDK. rewrite KD in NDK. clear - NDK E.
      apply nd_split in NDK. destruct NDK as (_ & _ & DJ). apply (DJ (k_bm KY)); [right; right; left; reflexivity| left; exact E]. }
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNC) (proj1 OWND) NCD) as ACD.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNC) (proj1 OWNBM) NCM) as ACM.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND) (proj1 OWNBM) NDM) as ADM.
    unfold blk_addr, blk_size in ACD, ACM, ADM; cbn [fst snd] in ACD, ACM, ADM.
    (* [comment removed for export] *)
    change (Z.to_nat 92) with 92%nat in CTXC.
    apply (rw_cells_split_CB usegs _ _ [] 92%nat _ _ [4; 80; 4; 4]%nat) in CTXC; [| reflexivity]. cbn [mk_CB_cells app firstn skipn repeat] in CTXC.
    eapply (th_cells_congr _ _ _ _ (ectx_cells (wz 0) (repeat (Z_to_bv 8 0) 80) (wz 0) (wz 0))) in CTXC; [| vm_compute; reflexivity| reflexivity| cbn; repeat split; auto; reflexivity].
    (* [comment removed for export] *)
    unfold pem_loc in LOC.
    lazymatch type of LOC with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13] =>
      change [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12] ++ [c13]) in LOC end.
    apply (proj1 (rw_cells_app usegs m _ _ _)) in LOC. destruct LOC as [LOCa LOC']. apply (proj1 (rw_cells_app usegs m _ _ _)) in LOC'. destruct LOC' as [TA TB].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in TA, TB.
    replace (bv_unsigned (e_sp en) + -208 + 96) with (bv_unsigned (e_sp en) + -112) in TA by (clear; lia).
    replace (bv_unsigned (e_sp en) + -208 + 96 + 4) with (bv_unsigned (e_sp en) + -108) in TB by (clear; lia).
    (* [comment removed for export] *)
    inversion NDC3 as [|z1 k1 NQ1 _]; subst. cbn [In] in NQ1.
    assert (NNC : qn <> qc) by (clear - NQ1; intros E; apply NQ1; left; exact E).
    assert (NND : qn <> pd) by (intros E; apply (DJY qn); [rewrite E; exact KYD| right; left; reflexivity]).
    assert (NNM : qn <> k_bm KY) by (intros E; apply (DJY qn); [rewrite E; exact KYM| right; left; reflexivity]).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN) (proj1 OWNC) NNC) as ANC.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN) (proj1 OWND) NND) as AND.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN) (proj1 OWNBM) NNM) as ANM.
    unfold blk_addr, blk_size in ANC, AND, ANM; cbn [fst snd] in ANC, AND, ANM. hide ANC. hide AND. hide ANM.
    assert (KYI : In (k_bi KY) (mbio_blocks KY)) by (unfold mbio_blocks; apply in_or_app; left; left; reflexivity).
    assert (KYB : In (k_bb KY) (mbio_blocks KY)) by (unfold mbio_blocks; apply in_or_app; left; right; left; reflexivity).
    assert (KYR : In (k_rp KY) (mbio_blocks KY)) by (unfold mbio_blocks; apply in_or_app; left; right; right; right; left; reflexivity).
    assert (NDK5 : List.NoDup [k_bi KY; k_bb KY; k_bm KY; k_rp KY; pd]) by (unfold mbio_blocks in NDK; rewrite KD in NDK; exact NDK).
    assert (NIC : k_bi KY <> qc) by (intros E; apply (DJY qc); [rewrite <- E; exact KYI| left; reflexivity]).
    assert (NBC : k_bb KY <> qc) by (intros E; apply (DJY qc); [rewrite <- E; exact KYB| left; reflexivity]).
    assert (NRC : k_rp KY <> qc) by (intros E; apply (DJY qc); [rewrite <- E; exact KYR| left; reflexivity]).
    pose proof NDK5 as ND5. inversion ND5 as [|y1 w1 NI1 ND6]; subst. inversion ND6 as [|y2 w2 NI2 ND7]; subst. inversion ND7 as [|y3 w3 NI3 ND8]; subst. inversion ND8 as [|y4 w4 NI4 _]; subst.
    cbn [In] in NI1, NI2, NI3, NI4.
    assert (NID : k_bi KY <> pd) by (clear - NI1; intros E; apply NI1; intuition congruence). assert (NIM : k_bi KY <> k_bm KY) by (clear - NI1; intros E; apply NI1; intuition congruence).
    assert (NBD : k_bb KY <> pd) by (clear - NI2; intros E; apply NI2; intuition congruence). assert (NBM : k_bb KY <> k_bm KY) by (clear - NI2; intros E; apply NI2; intuition congruence).
    assert (NRD : k_rp KY <> pd) by (clear - NI4; intros E; apply NI4; intuition congruence). assert (NRM : k_rp KY <> k_bm KY) by (clear - NI3; intros E; apply NI3; intuition congruence).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBI) (proj1 OWNC) NIC) as AIC.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBI) (proj1 OWND) NID) as AID.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBI) (proj1 OWNBM) NIM) as AIM.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBB) (proj1 OWNC) NBC) as ABC.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBB) (proj1 OWND) NBD) as ABD.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBB) (proj1 OWNBM) NBM) as ABM.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNRP) (proj1 OWNC) NRC) as ARC.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNRP) (proj1 OWND) NRD) as ARD.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNRP) (proj1 OWNBM) NRM) as ARM.
    unfold blk_addr, blk_size in AIC, AID, AIM, ABC, ABD, ABM, ARC, ARD, ARM; cbn [fst snd] in AIC, AID, AIM, ABC, ABD, ABM, ARC, ARD, ARM.
    hide AIC. hide AID. hide AIM. hide ABC. hide ABD. hide ABM. hide ARC. hide ARD. hide ARM. hide METH.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBI)) as (BI0 & _ & _ & BICL & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNBB)) as (BB0 & _ & _ & BBCL & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNRP)) as (RP0 & _ & _ & RPCL & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in BICL, BBCL, RPCL.
    (* [comment removed for export] *)
    assert (FIN : forall m', munch [(bv_unsigned (e_sp en) + -208 - 160, bv_unsigned (e_sp en) + -208); (ctxv, ctxv + 92); (D, D + maxY);
                                   (bv_unsigned (e_sp en) + -112, bv_unsigned (e_sp en) + -104); (BMY, BMY + 8)]%Z m m' ->
              wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' (e_lo en) (bv_unsigned (e_sp en) + -208) ->
              pem_com libenv en s LBc Lc f m' off rem rA rB rBig /\ errst_at_rest (e_E en) [] m' /\ rw_cells usegs m' namev [CB (Z.to_nat nn) bn]
              /\ (exists BMX, mbio_repx m' LBc Lc KX hBv BMX (wz lenX) methX lenX maxX 0)
              /\ rw_cells usegs m' (bv_unsigned (e_sp en)) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
              /\ (forall (blw : word) (bs' : list byte), rw_cells usegs m' BMY [C8 blw; C8 (wz D); C8 (wz maxY); C8 (wz (msec methY))] ->
                    length bs' = Z.to_nat maxY -> rw_cells usegs m' D [CB (Z.to_nat maxY) bs'] -> mbio_repx m' LBc Lc KY dBv BMY blw methY lenY maxY 0)).
    { intros m' MU' WM' MI' ST'.
      assert (HW : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun q => q <> qc /\ q <> pd /\ q <> k_bm KY))
                            [(bv_unsigned (e_sp en) + -208 - 160, bv_unsigned (e_sp en) + -208); (ctxv, ctxv + 92); (D, D + maxY);
                             (bv_unsigned (e_sp en) + -112, bv_unsigned (e_sp en) + -104); (BMY, BMY + 8)]%Z).
      { apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|].
        apply Forall_cons; [right; exists (qc, ctxv, 92); split; [exact (proj1 OWNC)|]; split; [cbn; clear; intuition congruence|]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [right; exists (pd, D, maxY); split; [exact (proj1 OWND)|]; split; [cbn; clear; intuition congruence|]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|].
        apply Forall_cons; [right; exists (k_bm KY, BMY, 32); split; [exact (proj1 OWNBM)|]; split; [cbn; clear; intuition congruence|]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
      assert (HXE : forall b, In b (e_LBall en) -> (fun q => q <> qc /\ q <> pd /\ q <> k_bm KY) (blk_id b)).
      { intros b Hb. cbv beta. split; [| split]; intros E; apply (CFRESH _ Hb); rewrite E; apply in_or_app; [right; apply in_or_app; right; left; reflexivity| right; apply in_or_app; left; exact KYD| right; apply in_or_app; left; exact KYM]. }
      assert (HPE : (fun q => q <> qc /\ q <> pd /\ q <> k_bm KY) (e_pe en)).
      { cbv beta. split; [| split]; intros E; [apply (DJC qc); [apply in_or_app; right; apply in_or_app; right; left; reflexivity| left; exact E]
          | apply (DJC pd); [apply in_or_app; right; apply in_or_app; left; exact KYD| left; exact E]
          | apply (DJC (k_bm KY)); [apply in_or_app; right; apply in_or_app; left; exact KYM| left; exact E]]. }
      split. { eapply (com_segI en); [exact COM| exact MU'| exact WM'| exact MI'| exact ST'| exact HW| exact HXE| unfold e_PL; cbn [disjoint_from]; clear - CCL DCL BMCL LO SLO; lia]. }
      split; [exact (er0_segI _ en _ _ _ _ _ _ _ _ _ _ _ _ ER0 MU' WM' CST INE HW HPE)|].
      split. { eapply rw_cells_transport; [exact NMC| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - ANC AND ANM RN1 RN2 LO SLO NN. unfold hideP in *. lia. }
      split. { eapply (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX CST MU' WM' HW). cbv beta. intros q Hq. split; [| split]; intros E.
               - apply (DJX q); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; left; exact (eq_sym E)].
               - apply (DJX q); [apply mbio_T_blocks; exact Hq| apply in_or_app; left; rewrite E; exact KYD].
               - apply (DJX q); [apply mbio_T_blocks; exact Hq| apply in_or_app; left; rewrite E; exact KYM]. }
      split. { eapply rw_cells_transport; [exact OUT| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - CCL DCL BMCL LO SLO. lia. }
      intros blw bs' BMC' LBS DC'.
      assert (HEAD' : rw_cells usegs m' dBv (bio_head methY)).
      { eapply rw_cells_transport; [exact HEAD| exact MU'| exact WM'|]. unfold bio_head. cbn [disjoint_from cells_size csize Nat.add]. clear - AIC AID AIM BI0 BICL LO SLO. unfold hideP in *. lia. }
      assert (W1C' : rw_cells usegs m' (dBv + 40) (bio_w1_cells (wz 4294967297) fl rrw (wz 4294967295) padw (wz BB))).
      { eapply rw_cells_transport; [exact W1C| exact MU'| exact WM'|]. unfold bio_w1_cells. cbn [disjoint_from cells_size csize Nat.add]. clear - AIC AID AIM BI0 BICL LO SLO. unfold hideP in *. lia. }
      assert (TAILC' : rw_cells usegs m' (dBv + 72) (bio_tail nr nw)).
      { eapply rw_cells_transport; [exact TAILC| exact MU'| exact WM'|]. unfold bio_tail. cbn [disjoint_from cells_size csize Nat.add]. clear - AIC AID AIM BI0 BICL LO SLO. unfold hideP in *. lia. }
      assert (BBC' : rw_cells usegs m' BB [C8 (wz BMY); C8 (wz RP)]).
      { eapply rw_cells_transport; [exact BBC| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - ABC ABD ABM BB0 BBCL LO SLO. unfold hideP in *. lia. }
      assert (RPC' : rw_cells usegs m' RP (readp_cells lenY D 0 rmaxw (wz (msec methY)))).
      { eapply rw_cells_transport; [exact RPC| exact MU'| exact WM'|]. unfold readp_cells. cbn [disjoint_from cells_size csize Nat.add]. clear - ARC ARD ARM RP0 RPCL LO SLO. unfold hideP in *. lia. }
      exists BB, RP, fl, rrw, padw, nr, nw. split; [exact OWNBI|]. split; [exact NDK|]. split; [unfold hideP in METH; exact METH|]. split; [exact HEAD'|]. split; [exact W1C'|]. split; [exact FLOK|]. split; [exact TAILC'|].
      exists rmaxw. split; [exact OWNBB|]. split; [exact BBC'|]. split; [exact OWNBM|]. split; [exact OWNRP|]. split; [clear - LY1; lia|]. split; [exact LENMAX|]. split; [exact MAX31|].
      rewrite KD. exists D, nmd, bs'. split; [exact OWND|]. split; [exact MAXP|]. split; [exact BMC'|]. split; [exact RPC'|]. split; [exact LBS| exact DC']. }
    (* [comment removed for export] *)
    hide NMC. hide OUT. hide HEAD. hide W1C. hide TAILC. hide BBC. hide RPC. clear FR0 LE MB SAVED ERR.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -208 - 160, bv_unsigned (e_sp en) + -208); (ctxv, ctxv + 92); (D, D + maxY);
                            (bv_unsigned (e_sp en) + -112, bv_unsigned (e_sp en) + -104); (BMY, BMY + 8)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    pose proof W4_decode_init_proof as WI. unfold W4_decode_init_stmt in WI.
    pose proof W4_decode_update_proof as WU. unfold W4_decode_update_stmt in WU.
    pose proof W4_decode_final_proof as WF. unfold W4_decode_final_stmt in WF.
    (* [comment removed for export] *)
    cprefix. ths. ths.
    name_sp (e_sp en) (-208).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut;
      [ eapply WI with (C := ctxv) (lo := e_lo en);
        [ reflexivity| exact C0| clear - C16; Z.div_mod_to_equations; lia| exact CTXC| reflexivity
        | match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; hyp_by_addr| clear - GLO; lia| match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; clear - SLO; lia
        | left; clear - CCL LO SLO; lia| hyp_by_addr ]
      | post_call usegs mq ]
    end.
    all: unname_sp.
    lazymatch goal with H : rw_cells usegs _ ctxv (ectx_cells _ _ _ _) |- _ => rename H into CTX1 end.
    (* [comment removed for export] *)
    pose proof alloc_ceiling_lt_2p47 as ACL.
    ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ths. ths. ths. ths.
    name_sp (e_sp en) (-208).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut;
      [ eapply WU with (C := ctxv) (B := D) (OL := bv_unsigned (e_sp en) + -108) (N := Z.to_nat maxY) (inl := lenY) (num := 0) (lo := e_lo en);
        [ reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
        | exact C0| clear - C16; Z.div_mod_to_equations; lia| exact D0| clear - SLO GLO; lia| clear - AL16; Z.div_mod_to_equations; lia
        | exact CTX1| reflexivity| clear; lia
        | hyp_by_addr| clear - LY1 LENMAX; lia| clear - LENMAX MAX31; lia| clear - LENMAX LY1; lia
        | hyp_by_addr
        | match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; hyp_by_addr| clear - GLO; lia| match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; clear - SLO; lia
        | clear - ACD MAXP; lia| left; clear - CCL LO SLO; lia| left; clear - DCL LO SLO LENMAX LY1; lia
        | left; clear - CCL LO SLO; lia| left; clear - DCL LO SLO LENMAX LY1; lia| right; match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; clear; lia
        | hyp_by_addr ]
      | cbv beta delta [dupdate_post]; post_call usegs mq ]
    end.
    all: unname_sp.
    lazymatch goal with H : -1 <= ?rv0 <= 1 /\ 0 <= ?ret0 /\ 0 <= ?num0 <= 64 /\ _ |- _ =>
      rename H into PCU; rename rv0 into rv; rename ret0 into ret; rename num0 into num1 end.
    destruct PCU as (RVR & RET0 & NUM1 & INEQ).
    lazymatch goal with H : rw_cells usegs _ ctxv (ectx_cells _ ?edx _ _) |- _ => rename H into CTX2; rename edx into ed1 end.
    lazymatch goal with H : length ed1 = 80%nat |- _ => rename H into LED1 end.
    lazymatch goal with H : rw_cells usegs _ D [CB _ ?bsx] |- _ => rename H into DC2; rename bsx into bs1 end.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned (e_sp en) + -108) [C4 _] |- _ => rename H into TB2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : stk usegs m2 (e_lo en) _ |- _ => rename H into ST2 end.
    lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
    pose proof (rw_cells_CB_length _ _ _ _ _ DC2) as LBS1.
    assert (RET31 : ret < 2 ^ 31) by (clear - INEQ NUM1 RET0 LENMAX MAX31; lia).
    (* [comment removed for export] *)
    lazymatch type of LOCa with rw_cells _ _ _ ?CA =>
    assert (EXIT_RZT : forall m' (tav tbv : word) (xra' u0 u1 u2 s1' b0 b1 b2 b3 b4 b5 b6 b7 s2' s3' s4' s7' s11' u3 u4 u5 u6 : word) (blw : word) (bs' : list byte),
      munch [(bv_unsigned (e_sp en) + -208 - 160, bv_unsigned (e_sp en) + -208); (ctxv, ctxv + 92); (D, D + maxY);
             (bv_unsigned (e_sp en) + -112, bv_unsigned (e_sp en) + -104); (BMY, BMY + 8)]%Z m m' -> wmono usegs m m' -> mem_inv usegs m' ->
      stk usegs m' (e_lo en) (bv_unsigned (e_sp en) + -208) ->
      rw_cells usegs m' (bv_unsigned (e_sp en) + -208) CA ->
      rw_cells usegs m' (bv_unsigned (e_sp en) + -112) [C4 tav] -> rw_cells usegs m' (bv_unsigned (e_sp en) + -108) [C4 tbv] ->
      rw_cells usegs m' BMY [C8 blw; C8 (wz D); C8 (wz maxY); C8 (wz (msec methY))] -> length bs' = Z.to_nat maxY -> rw_cells usegs m' D [CB (Z.to_nat maxY) bs'] ->
      climpl f Lc s (MS (mkR xra' (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) u0 u1 u2 (e_sp en) s1' b0 b1 b2 b3 b4 b5 b6 b7
                        s2' s3' s4' (wz (e_flags en)) (wz hBv) s7' (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) (wz dBv) s11' u3 u4 u5 u6)
                    (e_F en) (wz 0x188764) (e_fc en) None m' (seg_rom usegs))
        (pem_post libenv errst_live en)) end.
    { intros m' tav tbv xra' u0 u1 u2 s1' b0 b1 b2 b3 b4 b5 b6 b7 s2' s3' s4' s7' s11' u3 u4 u5 u6 blw bs' MU' WM' MI' ST' LOCa' TA' TB' BMC' LBS' DC'.
      destruct (FIN m' MU' WM' MI' ST') as (COM' & ER' & NMC' & [BMX MBX'] & OUT' & REB). pose proof (REB blw bs' BMC' LBS' DC') as MBY'.
      lazymatch type of LOCa' with rw_cells _ _ _ ?CA' => assert (LOC' : rw_cells usegs m' (bv_unsigned (e_sp en) + -208) (CA' ++ [C4 tav] ++ [C4 tbv])) end.
      { apply (proj2 (rw_cells_app usegs m' _ _ _)). split; [exact LOCa'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        apply (proj2 (rw_cells_app usegs m' _ _ _)). split; [replace (bv_unsigned (e_sp en) + -208 + 96) with (bv_unsigned (e_sp en) + -112) by (clear; lia); exact TA'|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned (e_sp en) + -208 + 96 + 4) with (bv_unsigned (e_sp en) + -108) by (clear; lia). exact TB'. }
      cbn [app] in LOC'.
      eapply (RZTP en s LBc Lc f m' off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ qc qn ctxv namev nn hBv dBv bn KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) blw);
        [exact COM'| exact ER'| clear - REM; lia| exact RA2| unfold pem_loc; exact LOC'| exact OWNC| exact OWNN| exact NN| exact LBN| exact NMC'| exact NUL| exact MBX'| exact MBY'
        | exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT']. }
    lazymatch type of LOCa with rw_cells _ _ _ ?CA =>
    assert (EXIT_DEC : forall m' (tav : word) (dlen : Z) (xra' u0 u1 u2 s1' b1 b3 b4 b5 b6 b7 s2' s3' s4' s11' u3 u4 u5 u6 : word) (bs' : list byte),
      munch [(bv_unsigned (e_sp en) + -208 - 160, bv_unsigned (e_sp en) + -208); (ctxv, ctxv + 92); (D, D + maxY);
             (bv_unsigned (e_sp en) + -112, bv_unsigned (e_sp en) + -104); (BMY, BMY + 8)]%Z m m' -> wmono usegs m m' -> mem_inv usegs m' ->
      stk usegs m' (e_lo en) (bv_unsigned (e_sp en) + -208) ->
      rw_cells usegs m' (bv_unsigned (e_sp en) + -208) CA ->
      rw_cells usegs m' (bv_unsigned (e_sp en) + -112) [C4 tav] -> rw_cells usegs m' (bv_unsigned (e_sp en) + -108) [C4 (wz dlen)] ->
      rw_cells usegs m' BMY [C8 (wz dlen); C8 (wz D); C8 (wz maxY); C8 (wz (msec methY))] -> length bs' = Z.to_nat maxY -> rw_cells usegs m' D [CB (Z.to_nat maxY) bs'] ->
      0 <= dlen <= lenY ->
      climpl f Lc s (MS (mkR xra' (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) u0 u1 u2 (e_sp en) s1' (wz hBv) b1 (wz 0) b3 b4 b5 b6 b7
                        s2' s3' s4' (wz (e_flags en)) (wz hBv) (e_sp en) (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) (wz dBv) s11' u3 u4 u5 u6)
                    (e_F en) (wz 0x188688) (e_fc en) None m' (seg_rom usegs))
        (pem_post libenv errst_live en)) end.
    { intros m' tav dlen xra' u0 u1 u2 s1' b1 b3 b4 b5 b6 b7 s2' s3' s4' s11' u3 u4 u5 u6 bs' MU' WM' MI' ST' LOCa' TA' TB' BMC' LBS' DC' DLEN.
      destruct (FIN m' MU' WM' MI' ST') as (COM' & ER' & NMC' & MBX' & OUT' & REB). pose proof (REB (wz dlen) bs' BMC' LBS' DC') as MBY'.
      lazymatch type of LOCa' with rw_cells _ _ _ ?CA' => assert (LOC' : rw_cells usegs m' (bv_unsigned (e_sp en) + -208) (CA' ++ [C4 tav] ++ [C4 (wz dlen)])) end.
      { apply (proj2 (rw_cells_app usegs m' _ _ _)). split; [exact LOCa'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        apply (proj2 (rw_cells_app usegs m' _ _ _)). split; [replace (bv_unsigned (e_sp en) + -208 + 96) with (bv_unsigned (e_sp en) + -112) by (clear; lia); exact TA'|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned (e_sp en) + -208 + 96 + 4) with (bv_unsigned (e_sp en) + -108) by (clear; lia). exact TB'. }
      cbn [app] in LOC'. destruct MBX' as [BMX MBX'].
      eapply (DECP en s LBc Lc f m' off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ qc qn ctxv namev nn hBv dBv BMY dlen bn KX KY methX methY lenX maxX lenY maxY);
        [exact COM'| exact ER'| exact REM| exact RA2| exact RB2| exact RBIG2| exact LXY| unfold pem_loc; exact LOC'| exact OWNC| exact OWNN| exact NN| exact LBN| exact NMC'| exact NUL| exists BMX; exact MBX'| exact MBY'
        | exact DLEN| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT']. }
    clear FIN.
    (* [comment removed for export] *)
    assert (RVC : rv = -1 \/ 0 <= rv <= 1) by (clear - RVR; lia).
    destruct RVC as [->|RVP].
    { ths. try th_if_lit.
      chere. eapply (EXIT_RZT m2); [exact MU| exact WM| exact MI2| exact ST2| exact LOCa| exact TA| exact TB2| exact BMC| exact LBS1| exact DC2]. }
    ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - RVP; lia); clear - K RVP; lia|]. clear K.
    (* [comment removed for export] *)
    ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ths. ths. ths.
    rewrite (unsigned_lit ret) by (clear - RET0 RET31; lia). rewrite (swrap32_small ret) by (clear - RET0 RET31; lia).
    rewrite v_sltu_b2z, v_sltiu_b2z. rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit D) by (clear - D0 DCL ACL LENMAX LY1; lia).
    rewrite (unsigned_lit (ret + D)) by (clear - D0 DCL ACL RET0 INEQ NUM1 LENMAX LY1 MAXP; lia).
    replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; clear - D0; lia).
    replace (bv_wrap 64 1) with 1 by reflexivity. replace (ret + D <? 1) with false by (symmetry; apply Z.ltb_ge; clear - D0 RET0; lia). cbn [Z.b2z]. ubs_if.
    ths. ths. ths. ths. ths.
    rewrite v_sltu_b2z, v_slti_b2z. try (rewrite (unsigned_lit (ret + D)) by (clear - D0 DCL ACL RET0 INEQ NUM1 LENMAX LY1 MAXP; lia)).
    try (rewrite (unsigned_lit D) by (clear - D0 DCL ACL LENMAX LY1; lia)). try (rewrite (unsigned_lit ret) by (clear - RET0 RET31; lia)).
    replace (ret + D <? D) with false by (symmetry; apply Z.ltb_ge; clear - RET0; lia).
    rewrite (t_sx32_small ret) by (clear - RET0 RET31; lia). rewrite (unsigned_lit ret) by (clear - RET0 RET31; lia). rewrite (zb_lxor_pow2_small ret 63) by (clear - RET0 RET31; lia).
    replace (ret + 2 ^ 63 <? 0 + 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; clear - RET0; lia). cbn [Z.b2z].
    change (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 0))))) 1) with 1. ubs_if.
    ths. ths. ths. replace (ret + D) with (D + ret) by (clear; lia).
    destruct (rw_cells_CB_split_at usegs m2 D (Z.to_nat maxY) bs1 (Z.to_nat ret) ltac:(clear - INEQ NUM1 RET0 LENMAX; lia) DC2) as [DCa DCb].
    replace (D + Z.of_nat (Z.to_nat ret)) with (D + ret) in DCb by (clear - RET0; lia).
    name_sp (e_sp en) (-208).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut;
      [ eapply WF with (C := ctxv) (T := D + ret) (OL := bv_unsigned (e_sp en) + -112) (lo := e_lo en) (num := num1) (K := (Z.to_nat maxY - Z.to_nat ret)%nat);
        [ reflexivity| reflexivity| reflexivity
        | exact C0| clear - C16; Z.div_mod_to_equations; lia| clear - SLO GLO; lia| clear - AL16; Z.div_mod_to_equations; lia| clear - D0 RET0; lia
        | exact CTX2| exact LED1| exact NUM1
        | exact DCb| clear - INEQ NUM1 RET0 LENMAX; lia
        | hyp_by_addr
        | match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; hyp_by_addr| clear - GLO; lia| match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; clear - SLO; lia
        | clear - ACD MAXP INEQ NUM1 RET0 LENMAX; lia| left; clear - CCL LO SLO; lia| left; clear - DCL LO SLO INEQ NUM1 RET0 LENMAX; lia
        | left; clear - CCL LO SLO; lia| left; clear - DCL LO SLO INEQ NUM1 RET0 LENMAX; lia| right; match goal with Hs : bv_unsigned _ = _ |- _ => rewrite Hs end; clear; lia
        | hyp_by_addr ]
      | post_call usegs mq ]
    end.
    all: unname_sp.
    lazymatch goal with H : ?rvx = 1 /\ ?numx = 0 /\ 0 <= ?dlx <= 3 * (num1 / 4) \/ _ |- _ => rename H into PCF; rename rvx into rv2; rename numx into num2; rename dlx into dl end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : stk usegs m3 (e_lo en) _ |- _ => rename H into ST3 end.
    lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
    lazymatch goal with H : rw_cells usegs m3 (D + ret) [CB _ ?bsx] |- _ => rename H into DCb3; rename bsx into bs2 end.
    lazymatch goal with H : rw_cells usegs m3 (bv_unsigned (e_sp en) + -112) [C4 _] |- _ => rename H into TA3 end.
    pose proof (rw_cells_CB_length _ _ _ _ _ DCb3) as LBS2.
    assert (DC3 : rw_cells usegs m3 D [CB (Z.to_nat maxY) (firstn (Z.to_nat ret) bs1 ++ bs2)]).
    { replace (Z.to_nat maxY) with (Z.to_nat ret + (Z.to_nat maxY - Z.to_nat ret))%nat by (clear - INEQ NUM1 RET0 LENMAX; lia).
      eapply rw_cells_CB_join; [exact DCa|]. replace (D + Z.of_nat (Z.to_nat ret)) with (D + ret) by (clear - RET0; lia). exact DCb3. }
    pose proof (rw_cells_CB_length _ _ _ _ _ DC3) as LBS3. clear DCa DCb3.
    (* [comment removed for export] *)
    destruct PCF as [(-> & -> & DLR)|(-> & -> & ->)].
    2:{ ths. try th_if_lit.
        chere. eapply (EXIT_RZT m3); [exact MU| exact WM| exact MI3| exact ST3| exact LOCa| exact TA3| exact TB2| exact BMC| exact LBS3| exact DC3]. }
    ths. try th_if_lit.
    (* [comment removed for export] *)
    ths. rewrite (t_sx32_small dl) by (clear - DLR NUM1; Z.div_mod_to_equations; lia).
    ths. rewrite (t_sx32_small ret) by (clear - RET0 RET31; lia).
    ths. ths.
    replace (bv_unsigned (Z_to_bv 64 ret)) with ret by (symmetry; apply unsigned_lit; clear - RET0 RET31; lia).
    replace (bv_unsigned (Z_to_bv 64 dl)) with dl by (symmetry; apply unsigned_lit; clear - DLR NUM1; Z.div_mod_to_equations; lia).
    replace (bv_swrap 32 (ret + dl)) with (ret + dl) by (symmetry; apply swrap32_small; clear - DLR NUM1 RET0 INEQ LENMAX MAX31; Z.div_mod_to_equations; lia).
    ths. rewrite bv_eqb_Z, Z.eqb_refl. cbv [negb].
    ths. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with H : stk usegs m4 (e_lo en) _ |- _ => rename H into ST4 end.
    lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MI4 end.
    lazymatch goal with H : rw_cells usegs m4 (bv_unsigned (e_sp en) + -108) _ |- _ => rename H into TB4 end.
    lazymatch goal with H : rw_cells usegs m4 BMY _ |- _ => rename H into BMC4 end.
    rewrite (unsigned_lit (ret + dl)), Z.add_0_r, (swrap32_small (ret + dl)) in BMC4 by (clear - DLR NUM1 RET0 INEQ LENMAX MAX31; Z.div_mod_to_equations; lia).
    chere.
    eapply (EXIT_DEC m4 _ (ret + dl)); [exact MU| exact WM| exact MI4| exact ST4| hyp_by_addr| hyp_by_addr| exact TB4| exact BMC4| exact LBS3| hyp_by_addr
      | clear - DLR NUM1 RET0 INEQ; Z.div_mod_to_equations; lia].
  Qed.
End W3.
