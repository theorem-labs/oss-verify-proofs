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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_rzt Fz_W3_dec.
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
  Local Notation com_callI := (com_call libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_callI := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem TAIL_proof :
    bio_ctrl_ptr_stmt -> evp_ctx_new_stmt -> END_stmt libenv errst_at_rest errst_live -> INI_stmt libenv errst_at_rest errst_live ->
    TAIL_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BCP ECN ENDP INIP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s10 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 l11 ta tb
           qn namev nn hBv dBv bn KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM ER0 REM RA3 RB2 RBIG2 LXY LOC OWNN NN LBN NMC NUL MBX MBY ELB CFRESH EL NDT OUT.
    unfold END_stmt, J_END in ENDP. unfold INI_stmt, J_INI in INIP. unfold bio_ctrl_ptr_stmt in BCP. unfold evp_ctx_new_stmt in ECN.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_TAIL, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (NDKY & _ & DJY).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    (* [comment removed for export] *)
    assert (LY31 : 0 <= lenY /\ lenY <= maxY /\ maxY < 2 ^ 31 - 1).
    { destruct MBY as (BMY0 & BB & RP & fl & rrw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & (rmaxw & _ & _ & _ & _ & O1 & O2 & O3 & _)). clear - O1 O2 O3. lia. }
    (* [comment removed for export] *)
    assert (HYL : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ mbio_T KY q).
    { intros q [Hq|Hq] _ X; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. apply in_or_app; right; apply in_or_app; left. apply mbio_T_blocks. exact X.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). apply in_or_app; right; apply in_or_app; left. apply mbio_T_blocks. exact X. }
    assert (HYK : forall q, mbio_T (e_K en) q -> ~ mbio_T KY q) by (intros q Hq X; apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact X| right; apply mbio_T_blocks; exact Hq]).
    assert (HYE : ~ mbio_T KY (e_pe en)) by (intros X; apply (DJC (e_pe en)); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact X| left; reflexivity]).
    assert (HXY : forall q, mbio_T KX q -> ~ mbio_T KY q) by (intros q Hq X; apply (DJX q); [apply mbio_T_blocks; exact Hq| apply in_or_app; left; apply mbio_T_blocks; exact X]).
    assert (HYN : ~ mbio_T KY qn) by (intros X; apply (DJY qn); [apply mbio_T_blocks; exact X| left; reflexivity]).
    (* [comment removed for export] *)
    unfold pem_loc in LOC.
    lazymatch type of LOC with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13] =>
      change [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [c11] ++ [c12; c13]) in LOC end.
    apply (proj1 (rw_cells_app usegs m _ _ _)) in LOC. destruct LOC as [LOCa LOC']. apply (proj1 (rw_cells_app usegs m _ _ _)) in LOC'. destruct LOC' as [PP TT].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PP, TT.
    replace (bv_unsigned (e_sp en) + -208 + 88) with (bv_unsigned (e_sp en) + -120) in PP by (clear; lia).
    replace (bv_unsigned (e_sp en) + -208 + 88 + 8) with (bv_unsigned (e_sp en) + -112) in TT by (clear; lia).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BCP with (K := KY) (BI := dBv) (meth := methY) (len := lenY) (max := maxY) (off := 0) (lo := e_lo en) (B := e_B en) (old := l11);
        [exact CST| rewrite unsigned_lit by lia; unfold BCTRL_STACK; clear - SLO; lia| exact MBY| rewrite unsigned_lit by lia; exact LOCa| reflexivity
        | rewrite unsigned_lit by lia; try replace (bv_unsigned (e_sp en) + -208 + 88) with (bv_unsigned (e_sp en) + -120) by (clear; lia); exact PP
        | rewrite unsigned_lit by lia; clear - PLBB; lia| rewrite unsigned_lit by lia; clear - AL16; lia| reflexivity| reflexivity| reflexivity| rewrite unsigned_lit by lia; cbv delta [MallocRep.wz]; f_equal; clear; lia]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (BMY & -> & -> & -> & LOCa1 & PP1 & MBY1)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite !unsigned_lit in FRM1 by lia. rewrite !unsigned_lit in LOCa1 by lia. rewrite !unsigned_lit in PP1 by lia.
    try replace (bv_unsigned (e_sp en) + -208 + 88) with (bv_unsigned (e_sp en) + -120) in PP1 by (clear; lia).
    try replace (bv_unsigned (e_sp en) + -208 + 96) with (bv_unsigned (e_sp en) + -112) in FRM1 by (clear; lia).
    replace (lenY - 0) with lenY in MBY1 by (clear; lia).
    assert (COM1 : pem_com libenv en st1 LBc Lc f1 m1 off rem rA rB rBig).
    { eapply (com_callI en) with (T1 := mbio_T KY); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear; lia| exact GR1| | | | | | | exact HYL| exact HYK| exact HYE]; clear - RA0 RB0 RBIG0; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX FRM1 HXY) as MBX1.
    pose proof (er0_callI en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HYE) as ER1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 TT ltac:(clear; lia)) as TT1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HYN ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    pose proof COM1 as (_ & _ & _ & _ & _ & _ & OWNE1 & _ & _ & _ & _ & ROOM1 & _ & RA1 & RB1 & RBIG1 & _).
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 TT OUT NMC MBX ER0 FR0 LE MB SAVED.
    (* [comment removed for export] *)
    pose proof MBY1 as MBYc.
    destruct MBYc as (BB & RP & fl & rrw & padw & nr & nw & OWNBI & NDK & METH & HEAD & W1C & FLOK & TAILC & (rmaxw & OWNBB & BBC & OWNBM & OWNRP & OFF0 & LENMAX & MAX31 & INNER)).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNBM)) as (BM0 & BMAL & _ & BMCL & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in BMCL.
    pose proof alloc_ceiling_lt_2p47 as ACL.
    assert (BMC : exists w1 w2 flw, rw_cells usegs m1 BMY [C8 (wz lenY); C8 w1; C8 w2; C8 flw]).
    { destruct (k_d KY) as [pd|]; [destruct INNER as (D & nmd & junk & _ & _ & BMC & _)| destruct INNER as (_ & BMC & _)]; eexists _, _, _; exact BMC. }
    clear HEAD W1C TAILC BBC INNER OWNBI OWNBB OWNRP. destruct BMC as (w1 & w2 & flw & BMC). hide NMC1. hide METH.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -108, bv_unsigned (e_sp en) + -104)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths.
    rewrite (unsigned_lit lenY) by (clear - LY31; lia). rewrite Z.shiftr_div_pow2 by (clear; lia).
    replace (lenY / 2 ^ 31) with 0 by (symmetry; apply Z.div_small; clear - LY31; lia).
    ths. try th_if_lit. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : stk usegs m2 (e_lo en) _ |- _ => rename H into ST2 end. lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
    lazymatch goal with H : munch _ m1 m2 |- _ => rename H into MU2 end. lazymatch goal with H : wmono usegs m1 m2 |- _ => rename H into WM2 end.
    lazymatch goal with H : rw_cells usegs m2 (bv_unsigned (e_sp en) + -112) _ |- _ => rename H into TT2 end.
    assert (HWo : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True)) [(bv_unsigned (e_sp en) + -108, bv_unsigned (e_sp en) + -104)])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    assert (COM2 : pem_com libenv en st1 LBc Lc f1 m2 off rem rA rB rBig).
    { eapply (com_segI en) with (EX := fun _ => True); [exact COM1| exact MU2| exact WM2| exact MI2| exact ST2| exact HWo| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
    pose proof (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1 CST1 MU2 WM2 HWo ltac:(intros q _; exact I)) as MBX2.
    pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY1 CST1 MU2 WM2 HWo ltac:(intros q _; exact I)) as MBY2.
    pose proof (er0_segI _ en _ _ _ _ _ _ _ _ _ _ _ _ ER1 MU2 WM2 CST1 (proj1 OWNE1) HWo I) as ER2.
    unfold hideP in NMC1.
    assert (NMC2 : rw_cells usegs m2 namev [CB (Z.to_nat nn) bn]).
    { eapply rw_cells_transport; [exact NMC1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - RN1 RN2 LO SLO NN. lia. }
    lazymatch goal with H : rw_cells usegs m2 (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOCa2 end.
    lazymatch goal with H : rw_cells usegs m2 (bv_unsigned (e_sp en) + -120) _ |- _ => rename H into PP2 end.
    lazymatch goal with H : rw_cells usegs m2 (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT2 end.
    lazymatch type of LOCa2 with rw_cells _ _ _ ?CA => lazymatch type of PP2 with rw_cells _ _ _ ?CP => lazymatch type of TT2 with rw_cells _ _ _ ?CT =>
      assert (LOC2 : rw_cells usegs m2 (bv_unsigned (e_sp en) + -208) (CA ++ CP ++ CT)) end end end.
    { apply (proj2 (rw_cells_app usegs m2 _ _ _)). split; [exact LOCa2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      apply (proj2 (rw_cells_app usegs m2 _ _ _)). split; [replace (bv_unsigned (e_sp en) + -208 + 88) with (bv_unsigned (e_sp en) + -120) by (clear; lia); exact PP2|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned (e_sp en) + -208 + 88 + 8) with (bv_unsigned (e_sp en) + -112) by (clear; lia). exact TT2. }
    cbn [app] in LOC2. pose proof COM2 as (CST2 & _). clear COM1 CST1 NMC1 MBX1 MBY1 ER1 LOCa2 PP2 TT2.
    ths. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (LZ : lenY = 0) by (rewrite ?unsigned_lit in K by (clear - LY31; lia); clear - K LY31; lia). clear K.
      ths. ths. ths. ths. chere.
      destruct (out4_split _ _ _ _ _ _ OUT2) as (O1 & O2 & O3 & O4). destruct MBX2 as [BMX MBX2].
      eapply (ENDP en st1 LBc Lc f1 m2 off rem rA rB rBig _ [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ None (Some qn) 0 namev nn hBv dBv 0 KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) (wz lenY));
        [exact COM2| left; split; [reflexivity| exact ER2]| clear - REM; lia| exact LOC2| reflexivity| reflexivity
        | cbv iota beta; split; [exact OWNN| split; [clear - NN; lia| apply rw_cells_CB0; clear - RN1 RN2 NN LO SLO SPR; lia]]| exact MBX2| exact MBY2| | intros b []| apply Forall_nil| | intros b []| | | | ].
      + intros b Hb. cbn [opt_ids app]. destruct (ELB _ Hb) as [X|X]; [left; exact X| right; left]. exact X.
      + intros b Hb. cbn [opt_ids app]. exact (CFRESH _ Hb).
      + intros q nm Hq. cbn [opt_ids app]. exact (EL _ _ Hq).
      + cbn [opt_ids map app]. exact NDT.
      + left. split; [reflexivity|]. split; [reflexivity|]. split; [exact O4|]. split; [exact O3|]. split; [exact O2| eexists; exact O1].
      + pose proof COM2 as (_ & _ & _ & _ & _ & _ & _ & _ & OFF2 & _). cbn. clear - OFF2. lia.
    - (* [comment removed for export] *)
      assert (LP : 1 <= lenY) by (rewrite ?unsigned_lit in K by (clear - LY31; lia); clear - K LY31; lia). clear K.
      ths. chere.
      eapply climpl_seq.
      { eapply ECN with (lo := e_lo en) (B := e_B en); [clear - FU FU1 REM; lia| eapply croom_weaken; [exact ROOM1| clear - RA3; lia| clear - RB1; lia| clear - RBIG1; lia]| exact CST2| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia]. }
      cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (qc & ctxv & -> & -> & -> & RNC & CTXC)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia. unfold ECTX in *.
      assert (COM3 : pem_com libenv en st3 ((qc, ctxv, 92) :: LBc) ((qc, 92) :: Lc) f3 m3 off (rem - 1) (rA - 1) rB rBig).
      { eapply (com_callI en) with (T1 := fun _ => False); [exact COM2| exact CST3| exact FRM3| unfold e_PL; clear; lia| exact FU3| clear - REM; lia| exact GR3| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
          clear - RA1 RB1 RBIG1 RA3; lia. }
      pose proof FRM3 as (CFR3 & KP3 & _).
      pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2 FRM3 ltac:(intros q _ X; exact X)) as MBX3.
      pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2 FRM3 ltac:(intros q _ X; exact X)) as MBY3.
      pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN FRM3 ltac:(intros X; exact X)) as OWNN3.
      pose proof (er0_callI en _ _ _ _ _ _ _ _ _ _ ER2 FRM3 (proj1 OWNE1) ltac:(intros X; exact X)) as ER3.
      pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
      pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR3 NMC2 (proj1 OWNN) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC3.
      pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
      pose proof RNC as (CX0 & _ & _ & CXCL & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in CXCL.
      (* [comment removed for export] *)
      assert (FRC : forall q A' n', In (q, A', n') LBc -> q <> qc) by (intros q A' n' Hq; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 Hq)).
      destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [_ NDL3]. cbn [map fst] in NDL3. inversion NDL3 as [|z3 k3 NQC _]; subst.
      assert (IDS : forall q, In q (mbio_blocks KX ++ mbio_blocks KY ++ [qn]) \/ q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
      { destruct MBX2 as [BMX0 MBX0]. intros q [X|[->|X]].
        - apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBX0 X)|].
          apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBY2 X)|].
          destruct X as [<-|[]]. exact (cown_id _ _ _ _ _ _ OWNN).
        - apply in_map_iff. exists (e_pe en, e_E en, 904). split; [reflexivity| exact INE].
        - apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
      assert (NQC' : ~ In qc ((mbio_blocks KX ++ mbio_blocks KY ++ [qn]) ++ e_pe en :: mbio_blocks (e_K en))).
      { intros X. assert (Y : In qc (map blk_id LBc)); [apply IDS; apply in_app_iff in X; destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X]|].
        apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hq). cbn in E. exact (FRC _ _ _ Hq E). }
      clear CST2 COM2 FRM3 CFR3 LOC2 OUT2 NMC2 MBX2 MBY2 ER2.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      (* [comment removed for export] *)
      cprefix. ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - CX0 CXCL LO SLO SPR; lia); clear - K CX0; lia|]. clear K.
      chere.
      eapply (INIP en st3 ((qc, ctxv, 92) :: LBc) ((qc, 92) :: Lc) f3 m3 off (rem - 1)%nat (rA - 1) rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                qc qn ctxv namev nn hBv dBv BMY bn KX KY methX methY lenX maxX lenY maxY);
        [exact COM3| exact ER3| clear - REM; lia| clear - RA3; lia| exact RB2| exact RBIG2| exact LXY| unfold pem_loc; exact LOC3| split; left; reflexivity| exact CTXC
        | exact OWNN3| exact NN| exact LBN| exact NMC3| exact NUL| exact MBX3| exact MBY3| exact LP| | | | | exact OUT3].
      + intros b [<-|Hb]; [right; apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
        destruct (ELB _ Hb) as [X|X]; [left; exact X| right].
        apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. right. exact X.
      + intros b Hb X. apply in_app_iff in X. destruct X as [X|X]; [apply (CFRESH _ Hb); apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [apply (CFRESH _ Hb); apply in_or_app; right; apply in_or_app; left; exact X|].
        destruct X as [X|X]; [| apply (CFRESH _ Hb); apply in_or_app; right; apply in_or_app; right; exact X].
        destruct b as [[q A'] n']. exact (FRC _ _ _ (PLB _ Hb) (eq_sym X)).
      + intros q nm Hq X. apply in_app_iff in X. destruct X as [X|X]; [apply (EL _ _ Hq); apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [apply (EL _ _ Hq); apply in_or_app; right; apply in_or_app; left; exact X|].
        destruct X as [X|X]; [| apply (EL _ _ Hq); apply in_or_app; right; apply in_or_app; right; exact X].
        apply NQC. rewrite X. apply in_map_iff. exists (q, nm). split; [reflexivity| exact (PLC _ _ Hq)].
      + lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY) ++ qc :: qn :: e_pe en :: mbio_blocks (e_K en)) by (rewrite <- ?app_assoc; reflexivity) end.
        apply nd_insert1; [rewrite <- app_assoc; replace (mbio_blocks KX ++ mbio_blocks KY ++ qn :: e_pe en :: mbio_blocks (e_K en)) with ((mbio_blocks KX ++ mbio_blocks KY ++ [qn]) ++ e_pe en :: mbio_blocks (e_K en)) by (rewrite <- ?app_assoc; reflexivity); exact NDT|].
        intros X. apply NQC'. rewrite <- ?app_assoc in X |- *. cbn [app] in X |- *. exact X.
  Qed.
End W3.
