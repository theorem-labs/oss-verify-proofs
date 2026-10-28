(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W3_iface Fz_W2_rep Fz_W3_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Export Fz_W3_lems.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  Local Notation libenv_cfrI := (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation pem_err_cfrI := (pem_err_cfr errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem END0_proof : evp_ctx_free_null_stmt -> pem_free_null_stmt -> bio_free_null_stmt -> END0_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros CFN PFN BFN en s LBc Lc f m off rem rA rB rBig strs loc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s10 s11 t3 t4 t5 t6 COM PE ELB SLB SL SFR NDS LOC LOCZ OUT.
    destruct COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_END, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. chere.
    eapply climpl_seq. { eapply CFN with (lo := e_lo en) (B := e_B en); [exact CST| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(clear; lia)) as SAVED1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (libenv_cfrI _ _ _ _ _ _ _ LE CFR1 INCL ltac:(intros b _ X; exact X)) as LE1.
    pose proof (pem_err_cfrI en _ _ _ _ _ _ PE CFR1 INE ltac:(intros X; exact X) SLB ltac:(intros b _ X; exact X)) as PE1.
    pose proof (mbio_rep_cfr _ _ _ _ _ _ _ _ _ _ _ _ _ MB CFR1 ltac:(intros q _ X; exact X)) as MB1.
    pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR0 FRM1 ltac:(clear; lia) ltac:(intros a X; exact X) ltac:(intros q _ _ X; exact X)) as FRa.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    clear CST FR0 LE PE MB SAVED LOC OUT CFR1 FRM1 MU WM HP ST MI LXS LATCH CIMG ERR AV errv.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq. { eapply PFN with (flags := e_flags en) (lo := e_lo en) (B := e_B en); [clear - FLR; lia| exact CST1| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (-> & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 SAVED1 ltac:(clear; lia)) as SAVED2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof (libenv_cfrI _ _ _ _ _ _ _ LE1 CFR2 INCL ltac:(intros b _ X; exact X)) as LE2.
    pose proof (pem_err_cfrI en _ _ _ _ _ _ PE1 CFR2 INE ltac:(intros X; exact X) SLB ltac:(intros b _ X; exact X)) as PE2.
    pose proof (mbio_rep_cfr _ _ _ _ _ _ _ _ _ _ _ _ _ MB1 CFR2 ltac:(intros q _ X; exact X)) as MB2.
    pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRa FRM2 ltac:(clear; lia) ltac:(intros a X; exact X) ltac:(intros q _ _ X; exact X)) as FRb.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    clear CST1 FRa LE1 PE1 MB1 SAVED1 LOC1 OUT1 CFR2 FRM2 MU WM HP1 ST1 MI1 errv1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. chere.
    eapply climpl_seq. { eapply BFN with (lo := e_lo en) (B := e_B en); [exact CST2| rewrite unsigned_lit by lia; clear - SLO; lia| reflexivity]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (-> & -> & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    pose proof FRM3 as (CFR3 & KP3 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 SAVED2 ltac:(clear; lia)) as SAVED3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
    pose proof (libenv_cfrI _ _ _ _ _ _ _ LE2 CFR3 INCL ltac:(intros b _ X; exact X)) as LE3.
    pose proof (pem_err_cfrI en _ _ _ _ _ _ PE2 CFR3 INE ltac:(intros X; exact X) SLB ltac:(intros b _ X; exact X)) as PE3.
    pose proof (mbio_rep_cfr _ _ _ _ _ _ _ _ _ _ _ _ _ MB2 CFR3 ltac:(intros q _ X; exact X)) as MB3.
    pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRb FRM3 ltac:(clear; lia) ltac:(intros a X; exact X) ltac:(intros q _ _ X; exact X)) as FRc.
    pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    clear CST2 FRb LE2 PE2 MB2 SAVED2 LOC2 OUT2 CFR3 FRM3 MU WM HP2 ST2 MI2 errv2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    cprefix. ths. ths. chere.
    eapply climpl_seq. { eapply BFN with (lo := e_lo en) (B := e_B en); [exact CST3| rewrite unsigned_lit by lia; clear - SLO; lia| reflexivity]. }
    cbv beta. intros f4 L4 st4 ms4 (v4 & m4 & LB4 & RET & FU4 & GR4 & CST4 & FRM4 & (-> & -> & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM4 by lia.
    pose proof FRM4 as (CFR4 & KP4 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 SAVED3 ltac:(clear; lia)) as SAVED4. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 LOC3 ltac:(clear; lia)) as LOC4.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 OUT3 ltac:(clear; lia)) as OUT4.
    pose proof (libenv_cfrI _ _ _ _ _ _ _ LE3 CFR4 INCL ltac:(intros b _ X; exact X)) as LE4.
    pose proof (pem_err_cfrI en _ _ _ _ _ _ PE3 CFR4 INE ltac:(intros X; exact X) SLB ltac:(intros b _ X; exact X)) as PE4.
    pose proof (mbio_rep_cfr _ _ _ _ _ _ _ _ _ _ _ _ _ MB3 CFR4 ltac:(intros q _ X; exact X)) as MB4.
    pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRc FRM4 ltac:(clear; lia) ltac:(intros a X; exact X) ltac:(intros q _ _ X; exact X)) as FRd.
    pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _). rewrite unsigned_lit in ST4 by lia.
    clear CST3 FRc LE3 PE3 MB3 SAVED3 LOC3 OUT3 CFR4 FRM4 MU WM HP3 ST3 MI3 errv3.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    (* [comment removed for export] *)
    unfold pem_saved in SAVED4.
    cprefix. ths. do 13 ths. ths.
    assert (FRj : rw_cells usegs m4 (bv_unsigned (e_sp en) + -208) (loc ++ pem_saved en)).
    { apply (proj2 (rw_cells_app usegs m4 _ _ _)). split; [exact LOC4|]. rewrite <- (Nat2Z.id (cells_size loc)), LOCZ. replace (bv_unsigned (e_sp en) + -208 + 104) with (bv_unsigned (e_sp en) + -104) by (clear; lia). exact SAVED4. }
    clear LOC4 SAVED4.
    lazymatch goal with H : stk usegs _ (e_lo en) _ |- _ => rename H into STe end.
    eapply stk_release in FRj; [| exact STe| clear - SLO LO GLO; lia]. rewrite cells_size_app, Nat2Z.inj_add, LOCZ in FRj. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRj.
    replace (bv_unsigned (e_sp en) + -208 + (104 + 104)) with (bv_unsigned (e_sp en)) in FRj by (clear; lia). clear STe.
    ths. chere. apply climpl_done.
    try replace (bv_unsigned (e_sp en) + 0) with (bv_unsigned (e_sp en)) by (clear; lia). try rewrite Z_to_bv_bv_unsigned.
    lazymatch goal with H : stk usegs m4 (e_lo en) _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MIf end.
    unfold pem_post, cpostx. exists (wz 0), m4, LBc. split; [unfold cret; do 14 eexists; reflexivity|].
    split; [clear - FU FU1 FU2 FU3 FU4; lia|]. split; [eapply cgrow_weaken; [exact CG| clear - RA0; lia| clear - RB0; lia| clear - RBIG0; lia]|].
    split. { eapply (cstate_seg [] _ _ _ _ m4 m4 _ (e_sp en) _ (e_lo en) (e_B en) (bv_unsigned (e_sp en))); [exact CST4| apply munch_refl| apply wmono_refl| exact MIf| apply Forall_nil| clear - SLO; lia| clear - PLBB; lia| cbn; exact I| exact STf| clear - PLBB; lia]. }
    split; [exact FRd|].
    unfold pem_read_res. destruct PE4 as [[-> REST]|(top & bot & LV & LEN)].
    - exists 0, off, 0, 0, [], []. split; [reflexivity|]. split; [exact OFF|]. split; [exact MB4|]. split; [exact LE4|]. split; [exact (errst_rest_live _ _ REST)|]. split; [cbn; clear; lia|].
      split; [apply Forall_nil|]. split; [constructor|]. split; [cbn; clear - OFF; lia|].
      split. { left. split; [reflexivity|]. split; [reflexivity|]. cbn [app] in OUT4 |- *.
        change ([C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]) with ([C8 (wz 0)] ++ [C8 (wz 0)] ++ [C8 (wz 0)] ++ [C8 (wz 0)]) in OUT4.
        apply (proj1 (rw_cells_app usegs m4 _ _ _)) in OUT4. destruct OUT4 as [O0 OUT4]. apply (proj1 (rw_cells_app usegs m4 _ _ _)) in OUT4. destruct OUT4 as [O1 OUT4].
        apply (proj1 (rw_cells_app usegs m4 _ _ _)) in OUT4. destruct OUT4 as [O2 O3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in O1, O2, O3.
        replace (bv_unsigned (e_sp en) + 8 + 8 + 8) with (bv_unsigned (e_sp en) + 24) in O3 by (clear; lia). replace (bv_unsigned (e_sp en) + 8 + 8) with (bv_unsigned (e_sp en) + 16) in O2 by (clear; lia).
        split; [exact O3|]. split; [exact O2|]. split; [exact O1| exists (wz 0); exact O0]. }
      cbn [app]. split; [| split; [intros b []| exact PLC]].
      intros b. split; [intros Hb| intros [Hb|[]]; exact (PLB _ Hb)]. destruct (ELB _ Hb) as [X|[]]. left; exact X.
    - exists 0, off, top, bot, strs, []. split; [reflexivity|]. split; [exact OFF|]. split; [exact MB4|]. split; [exact LE4|]. split; [exact LV|]. split; [exact LEN|].
      split; [exact SL|]. split; [rewrite app_nil_r; exact NDS|]. split; [cbn; clear - OFF; lia|].
      split. { left. split; [reflexivity|]. split; [reflexivity|].
        change ([C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]) with ([C8 (wz 0)] ++ [C8 (wz 0)] ++ [C8 (wz 0)] ++ [C8 (wz 0)]) in OUT4.
        apply (proj1 (rw_cells_app usegs m4 _ _ _)) in OUT4. destruct OUT4 as [O0 OUT4]. apply (proj1 (rw_cells_app usegs m4 _ _ _)) in OUT4. destruct OUT4 as [O1 OUT4].
        apply (proj1 (rw_cells_app usegs m4 _ _ _)) in OUT4. destruct OUT4 as [O2 O3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in O1, O2, O3.
        replace (bv_unsigned (e_sp en) + 8 + 8 + 8) with (bv_unsigned (e_sp en) + 24) in O3 by (clear; lia). replace (bv_unsigned (e_sp en) + 8 + 8) with (bv_unsigned (e_sp en) + 16) in O2 by (clear; lia).
        split; [exact O3|]. split; [exact O2|]. split; [exact O1| exists (wz 0); exact O0]. }
      rewrite app_nil_r. split; [| split; [exact SFR| exact PLC]].
      intros b. split; [intros Hb; exact (ELB _ Hb)| intros [Hb|Hb]; [exact (PLB _ Hb)| exact (SLB _ Hb)]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem END_proof : evp_ctx_free_stmt -> evp_ctx_free_null_stmt -> pem_free_stmt -> pem_free_null_stmt -> bio_free_mem_stmt libenv -> END_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros CF CFN PF PFN BF en s LBc Lc f m off rem rA rB rBig loc strs news xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s10 s11 t3 t4 t5 t6
           octx oname ctxv namev nn hBv dBv ret KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
    cbv zeta. intros COM PE REM LOC LOCZ HCTX HNAME MBX MBY ELB SN SL CFRESH SFR EL NDT PO NB.
    destruct COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_END, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (CG0 : cgrow (e_L en) Lc 16 8 (pem_BIG en)) by (eapply cgrow_weaken; [exact CG| clear - RA0; lia| clear - RB0; lia| clear - RBIG0; lia]). clear CG ROOM RA0 RB0 RBIG0.
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY). pose proof (nd_split _ _ NDC3) as (_ & _ & DJCN).
    (* [comment removed for export] *)
    assert (K5 : forall s4 LB4 L4 f4 m4 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
      cstate s4 LB4 (e_LB0 en) L4 m4 (wz (bv_unsigned (e_sp en) + -208)) (e_tp en) (e_lo en) (e_B en) ->
      cframe (pem_T en) [] (bv_unsigned (e_sp en) + 32) (e_s en) (e_LBall en) (e_L en) (e_m en) s4 LB4 L4 m4 ->
      libenv m4 (e_LBL en) (e_E en) -> mbio_rep m4 LB4 L4 (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off -> pem_err errst_at_rest errst_live en strs m4 ->
      rw_cells usegs m4 (bv_unsigned (e_sp en) + -104) (pem_saved en) -> rw_cells usegs m4 (bv_unsigned (e_sp en) + -208) loc ->
      pem_out ret m4 LB4 L4 (bv_unsigned (e_sp en) + 24) (bv_unsigned (e_sp en) + 16) (bv_unsigned (e_sp en) + 8) (bv_unsigned (e_sp en)) news ->
      (e_f en - pem_EV en <= f4)%nat -> cgrow (e_L en) L4 16 8 (pem_BIG en) ->
      (forall b, In b LB4 -> In b (e_LBall en) \/ In b (strs ++ news)) -> incl_blocks (strs ++ news) LB4 -> strs_inL L4 strs -> incl_blocks (e_LBall en) LB4 -> (forall q nm, In (q, nm) (e_L en) -> In (q, nm) L4) ->
      climpl f4 L4 s4 (MS (mkR (wz 0x18820c) (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) y0 y1 y2 (e_sp en) (wz dBv) y3 y4 y5 y6 y7 y8 y9 y10
                            (wz namev) (wz ret) s2 (wz (e_flags en)) (wz hBv) s5 (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) s10 s11 y11 y12 y13 y14)
                        (e_F en) (wz 0x18820c) (e_fc en) None m4 (seg_rom usegs)) (pem_post libenv errst_live en)).
    { intros s4 LB4 L4 f4 m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CST4 FR4 LE4 MB4 PE4 SAVED4 LOC4 PO4 FU4 CG4 ELB4 SN4 SL4 PLB4 PLC4.
      pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _). rewrite unsigned_lit in ST4 by lia.
      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
      unfold pem_saved in SAVED4.
      cprefix. ths. do 13 ths. ths.
      assert (FRj : rw_cells usegs m4 (bv_unsigned (e_sp en) + -208) (loc ++ pem_saved en)).
      { apply (proj2 (rw_cells_app usegs m4 _ _ _)). split; [exact LOC4|]. rewrite <- (Nat2Z.id (cells_size loc)), LOCZ. replace (bv_unsigned (e_sp en) + -208 + 104) with (bv_unsigned (e_sp en) + -104) by (clear; lia). exact SAVED4. }
      clear LOC4 SAVED4.
      lazymatch goal with H : stk usegs _ (e_lo en) _ |- _ => rename H into STe end.
      eapply stk_release in FRj; [| exact STe| clear - SLO LO GLO; lia]. rewrite cells_size_app, Nat2Z.inj_add, LOCZ in FRj. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRj.
      replace (bv_unsigned (e_sp en) + -208 + (104 + 104)) with (bv_unsigned (e_sp en)) in FRj by (clear; lia). clear STe.
      ths. chere. apply climpl_done.
      try replace (bv_unsigned (e_sp en) + 0) with (bv_unsigned (e_sp en)) by (clear; lia). try rewrite Z_to_bv_bv_unsigned.
      lazymatch goal with H : stk usegs m4 (e_lo en) _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MIf end.
      unfold pem_post, cpostx. exists (wz ret), m4, LB4. split; [unfold cret; do 14 eexists; reflexivity|].
      split; [exact FU4|]. split; [exact CG4|].
      split. { eapply (cstate_seg [] _ _ _ _ m4 m4 _ (e_sp en) _ (e_lo en) (e_B en) (bv_unsigned (e_sp en))); [exact CST4| apply munch_refl| apply wmono_refl| exact MIf| apply Forall_nil| clear - SLO; lia| clear - PLBB; lia| cbn; exact I| exact STf| clear - PLBB; lia]. }
      split; [exact FR4|].
      unfold pem_read_res. destruct PE4 as [[-> REST]|(top & bot & LV & LEN)].
      - exists ret, off, 0, 0, [], news. split; [reflexivity|]. split; [exact OFF|]. split; [exact MB4|]. split; [exact LE4|]. split; [exact (errst_rest_live _ _ REST)|]. split; [cbn; clear; lia|].
        split; [apply Forall_nil|]. split; [exact (proj1 (nd_split _ _ NDR))|]. split; [exact NB|]. split; [exact PO4|]. cbn [app] in *. split; [| split; [exact SFR| exact PLC4]].
        intros b. split; [intros Hb; exact (ELB4 _ Hb)| intros [Hb|Hb]; [exact (PLB4 _ Hb)| exact (SN4 _ Hb)]].
      - exists ret, off, top, bot, strs, news. split; [reflexivity|]. split; [exact OFF|]. split; [exact MB4|]. split; [exact LE4|]. split; [exact LV|]. split; [exact LEN|].
        split; [exact SL4|]. split; [exact (proj1 (nd_split _ _ NDR))|]. split; [exact NB|]. split; [exact PO4|]. split; [| split; [exact SFR| exact PLC4]].
        intros b. split; [intros Hb; exact (ELB4 _ Hb)| intros [Hb|Hb]; [exact (PLB4 _ Hb)| exact (SN4 _ Hb)]]. }
    (* [comment removed for export] *)
    assert (K4 : forall s3 LB3 L3 f3 m3 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
      cstate s3 LB3 (e_LB0 en) L3 m3 (wz (bv_unsigned (e_sp en) + -208)) (e_tp en) (e_lo en) (e_B en) ->
      cframe (pem_T en) [] (bv_unsigned (e_sp en) + 32) (e_s en) (e_LBall en) (e_L en) (e_m en) s3 LB3 L3 m3 ->
      libenv m3 (e_LBL en) (e_E en) -> incl_blocks (e_LBL en) LB3 -> cown LB3 L3 (e_pe en) (e_E en) 904 (e_Enm en) ->
      mbio_rep m3 LB3 L3 (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off -> pem_err errst_at_rest errst_live en strs m3 ->
      rw_cells usegs m3 (bv_unsigned (e_sp en) + -104) (pem_saved en) -> rw_cells usegs m3 (bv_unsigned (e_sp en) + -208) loc ->
      pem_out ret m3 LB3 L3 (bv_unsigned (e_sp en) + 24) (bv_unsigned (e_sp en) + 16) (bv_unsigned (e_sp en) + 8) (bv_unsigned (e_sp en)) news ->
      (e_f en - pem_EV en + 5 <= f3)%nat -> cgrow (e_L en) L3 16 8 (pem_BIG en) ->
      mbio_repx m3 LB3 L3 KY dBv BMY blwY methY lenY maxY offY ->
      (forall b, In b LB3 -> In b (e_LBall en) \/ In (blk_id b) (mbio_blocks KY) \/ In b (strs ++ news)) -> incl_blocks (strs ++ news) LB3 -> strs_inL L3 strs -> incl_blocks (e_LBall en) LB3 ->
      (forall q nm, In (q, nm) (e_L en) -> In (q, nm) L3) ->
      climpl f3 L3 s3 (MS (mkR (wz 0x188204) (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) y0 y1 y2 (e_sp en) (wz dBv) y3 y4 y5 y6 y7 y8 y9 y10
                            (wz namev) (wz ret) s2 (wz (e_flags en)) (wz hBv) s5 (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) s10 s11 y11 y12 y13 y14)
                        (e_F en) (wz 0x188204) (e_fc en) None m3 (seg_rom usegs)) (pem_post libenv errst_live en)).
    { intros s3 LB3 L3 f3 m3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CST3 FR3 LE3 INCL3 OWNE3 MB3 PE3 SAVED3 LOC3 PO3 FU3 CG3 MBY3 ELB3 SN3 SL3 PLB3 PLC3.
      pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      (* [comment removed for export] *)
      assert (NKY : forall q, mbio_T KY q -> ~ In q (map blk_id (strs ++ news) ++ e_pe en :: mbio_blocks (e_K en))).
      { intros q Hq X. apply mbio_T_blocks in Hq. apply (DJC q); [apply in_or_app; right; apply in_or_app; left; exact Hq| exact X]. }
      cprefix. ths. ths. chere.
      eapply climpl_seq.
      { eapply BF with (LBL := e_LBL en) (E := e_E en) (lo := e_lo en) (B := e_B en);
          [pose proof (mbio_blocks_len KY); clear - FU3 H; lia| exact CST3| rewrite unsigned_lit by lia; unfold BFREE_STACK; clear - SLO; lia| rewrite unsigned_lit by lia; clear - AL16; lia| exact LE3| exact INCL3
          | intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); apply mbio_T_blocks in X; apply in_or_app; right; apply in_or_app; left; exact X
          | exact MBY3| reflexivity]. }
      cbv beta. intros f4 L4 st4 ms4 (v4 & m4 & LB4 & RET & FU4 & GR4 & CST4 & FRM4 & (-> & LE4 & KB4 & KL4)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM4 by lia.
      pose proof FRM4 as (CFR4 & KP4 & _).
      assert (KO4 : forall p A n nm, ~ In p (mbio_blocks KY) -> cown LB3 L3 p A n nm -> cown LB4 L4 p A n nm).
      { intros p A n nm NI O. eapply cown_keep; [exact O| intros I; apply KB4; split; [exact I| exact NI]| intros I; apply KL4; split; [exact I| exact NI]]. }
      eapply K5; [exact CST4| | exact LE4| | | exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 SAVED3 ltac:(clear; lia))| exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 LOC3 ltac:(clear; lia))
                | | pose proof (mbio_blocks_len KY); clear - FU3 FU4 H; lia| eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG3 GR4)| clear; lia| clear; lia| clear; lia]| | | | |].
      - eapply cframe_call; [exact FR3| exact FRM4| clear; lia| intros a X; exact X|]. intros q Hq _ X. apply mbio_T_blocks in X.
        destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
        + destruct Hq as (b & <- & Hb). apply (CFRESH _ Hb). apply in_or_app; right; apply in_or_app; left; exact X.
        + destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). apply in_or_app; right; apply in_or_app; left; exact X.
      - eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB3| exact CFR4| intros q Hq X; apply (NKY _ X); apply mbio_T_blocks in Hq; apply in_or_app; right; right; exact Hq]| |].
        + intros b Hb Tb. apply KB4. split; [exact Hb| intros X; apply mbio_T_blocks in X; apply (NKY _ X); apply mbio_T_blocks in Tb; apply in_or_app; right; right; exact Tb].
        + intros p nm Hp Tp. apply KL4. split; [exact Hp| intros X; apply mbio_T_blocks in X; apply (NKY _ X); apply mbio_T_blocks in Tp; apply in_or_app; right; right; exact Tp].
      - eapply pem_err_cfrI; [exact PE3| exact CFR4| exact (proj1 OWNE3)| intros X; apply (NKY _ X); apply in_or_app; right; left; reflexivity
          | intros b Hb; apply SN3; apply in_or_app; left; exact Hb| intros b Hb X; apply (NKY _ X); apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
      - eapply pem_out_keep; [exact PO3| exact CFR4| clear; lia| intros p A n nm Hn O; apply KO4; [| exact O]| intros b Hb; apply SN3; apply in_or_app; right; exact Hb|].
        + intros X. apply (NKY _ (proj2 (mbio_T_blocks _ _) X)). apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hn].
        + intros b Hb X. apply (NKY _ X). apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map. exact Hb.
      - intros b Hb. destruct (proj1 (KB4 b) Hb) as [Hb3 NI]. destruct (ELB3 _ Hb3) as [X|[X|X]]; [left; exact X| exfalso; exact (NI X)| right; exact X].
      - intros b Hb. apply KB4. split; [exact (SN3 _ Hb)|]. intros X. apply (NKY _ (proj2 (mbio_T_blocks _ _) X)). apply in_or_app; left. apply in_map. exact Hb.
      - eapply strs_inL_keep; [exact SL3| intros q nm Hq NX; apply KL4; split; [exact Hq| exact NX]
          | intros b Hb X; apply (NKY _ (proj2 (mbio_T_blocks _ _) X)); apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
      - intros b Hb. apply KB4. split; [exact (PLB3 _ Hb)|]. intros X. apply (CFRESH _ Hb). apply in_or_app; right; apply in_or_app; left; exact X.
      - intros q nm Hq. apply KL4. split; [exact (PLC3 _ _ Hq)|]. intros X. apply (EL _ _ Hq). apply in_or_app; right; apply in_or_app; left; exact X. }
    (* [comment removed for export] *)
    assert (K3 : forall s2' LB2 L2 f2 m2 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
      cstate s2' LB2 (e_LB0 en) L2 m2 (wz (bv_unsigned (e_sp en) + -208)) (e_tp en) (e_lo en) (e_B en) ->
      cframe (pem_T en) [] (bv_unsigned (e_sp en) + 32) (e_s en) (e_LBall en) (e_L en) (e_m en) s2' LB2 L2 m2 ->
      libenv m2 (e_LBL en) (e_E en) -> incl_blocks (e_LBL en) LB2 -> cown LB2 L2 (e_pe en) (e_E en) 904 (e_Enm en) ->
      mbio_rep m2 LB2 L2 (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off -> pem_err errst_at_rest errst_live en strs m2 ->
      rw_cells usegs m2 (bv_unsigned (e_sp en) + -104) (pem_saved en) -> rw_cells usegs m2 (bv_unsigned (e_sp en) + -208) loc ->
      pem_out ret m2 LB2 L2 (bv_unsigned (e_sp en) + 24) (bv_unsigned (e_sp en) + 16) (bv_unsigned (e_sp en) + 8) (bv_unsigned (e_sp en)) news ->
      (e_f en - pem_EV en + 10 <= f2)%nat -> cgrow (e_L en) L2 16 8 (pem_BIG en) ->
      mbio_repx m2 LB2 L2 KX hBv BMX blwX methX lenX maxX offX -> mbio_repx m2 LB2 L2 KY dBv BMY blwY methY lenY maxY offY ->
      (forall b, In b LB2 -> In b (e_LBall en) \/ In (blk_id b) (mbio_blocks KX ++ mbio_blocks KY) \/ In b (strs ++ news)) -> incl_blocks (strs ++ news) LB2 -> strs_inL L2 strs -> incl_blocks (e_LBall en) LB2 ->
      (forall q nm, In (q, nm) (e_L en) -> In (q, nm) L2) ->
      climpl f2 L2 s2' (MS (mkR (wz 0x1881fc) (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) y0 y1 y2 (e_sp en) (wz dBv) y3 y4 y5 y6 y7 y8 y9 y10
                             (wz namev) (wz ret) s2 (wz (e_flags en)) (wz hBv) s5 (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) s10 s11 y11 y12 y13 y14)
                         (e_F en) (wz 0x1881fc) (e_fc en) None m2 (seg_rom usegs)) (pem_post libenv errst_live en)).
    { intros s2' LB2 L2 f2 m2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CST2 FR2 LE2 INCL2 OWNE2 MB2 PE2 SAVED2 LOC2 PO2 FU2 CG2 MBX2 MBY2 ELB2 SN2 SL2 PLB2 PLC2.
      pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      (* [comment removed for export] *)
      assert (NKX : forall q, mbio_T KX q -> ~ In q (mbio_blocks KY ++ map blk_id (strs ++ news) ++ e_pe en :: mbio_blocks (e_K en))).
      { intros q Hq X. apply mbio_T_blocks in Hq. apply in_app_iff in X. destruct X as [X|X]; [exact (DJX _ Hq ltac:(apply in_or_app; left; exact X))| exact (DJC q ltac:(apply in_or_app; left; exact Hq) X)]. }
      cprefix. ths. ths. chere.
      eapply climpl_seq.
      { eapply BF with (LBL := e_LBL en) (E := e_E en) (lo := e_lo en) (B := e_B en);
          [pose proof (mbio_blocks_len KX); clear - FU2 H; lia| exact CST2| rewrite unsigned_lit by lia; unfold BFREE_STACK; clear - SLO; lia| rewrite unsigned_lit by lia; clear - AL16; lia| exact LE2| exact INCL2
          | intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); apply mbio_T_blocks in X; apply in_or_app; left; exact X
          | exact MBX2| reflexivity]. }
      cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (-> & LE3 & KB3 & KL3)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
      pose proof FRM3 as (CFR3 & KP3 & _).
      assert (KO3 : forall p A n nm, ~ In p (mbio_blocks KX) -> cown LB2 L2 p A n nm -> cown LB3 L3 p A n nm).
      { intros p A n nm NI O. eapply cown_keep; [exact O| intros I; apply KB3; split; [exact I| exact NI]| intros I; apply KL3; split; [exact I| exact NI]]. }
      eapply K4; [exact CST3| | exact LE3| | | | | exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 SAVED2 ltac:(clear; lia))| exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia))
                | | pose proof (mbio_blocks_len KX); clear - FU2 FU3 H; lia| eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG2 GR3)| clear; lia| clear; lia| clear; lia]| | | | | |].
      - eapply cframe_call; [exact FR2| exact FRM3| clear; lia| intros a X; exact X|]. intros q Hq _ X. apply mbio_T_blocks in X.
        destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
        + destruct Hq as (b & <- & Hb). apply (CFRESH _ Hb). apply in_or_app; left; exact X.
        + destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). apply in_or_app; left; exact X.
      - eapply incl_blocks_keep; [exact INCL2| exact KP3| intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); apply mbio_T_blocks in X; apply in_or_app; left; exact X].
      - apply KO3; [| exact OWNE2]. intros X. apply (NKX _ (proj2 (mbio_T_blocks _ _) X)). apply in_or_app; right; apply in_or_app; right; left; reflexivity.
      - eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB2| exact CFR3| intros q Hq X; apply (NKX _ X); apply mbio_T_blocks in Hq; apply in_or_app; right; apply in_or_app; right; right; exact Hq]| |].
        + intros b Hb Tb. apply KB3. split; [exact Hb| intros X; apply (NKX _ (proj2 (mbio_T_blocks _ _) X)); apply mbio_T_blocks in Tb; apply in_or_app; right; apply in_or_app; right; right; exact Tb].
        + intros p nm Hp Tp. apply KL3. split; [exact Hp| intros X; apply (NKX _ (proj2 (mbio_T_blocks _ _) X)); apply mbio_T_blocks in Tp; apply in_or_app; right; apply in_or_app; right; right; exact Tp].
      - eapply pem_err_cfrI; [exact PE2| exact CFR3| exact (proj1 OWNE2)| intros X; apply (NKX _ X); apply in_or_app; right; apply in_or_app; right; left; reflexivity
          | intros b Hb; apply SN2; apply in_or_app; left; exact Hb| intros b Hb X; apply (NKX _ X); apply in_or_app; right; apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
      - eapply pem_out_keep; [exact PO2| exact CFR3| clear; lia| intros p A n nm Hn O; apply KO3; [| exact O]| intros b Hb; apply SN2; apply in_or_app; right; exact Hb|].
        + intros X. apply (NKX _ (proj2 (mbio_T_blocks _ _) X)). apply in_or_app; right; apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hn].
        + intros b Hb X. apply (NKX _ X). apply in_or_app; right; apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map. exact Hb.
      - eapply mbio_repx_keep; [eapply mbio_repx_cfr; [exact MBY2| exact CFR3| intros q Hq X; apply (NKX _ X); apply mbio_T_blocks in Hq; apply in_or_app; left; exact Hq]| |].
        + intros b Hb Tb. apply KB3. split; [exact Hb| intros X; apply (NKX _ (proj2 (mbio_T_blocks _ _) X)); apply mbio_T_blocks in Tb; apply in_or_app; left; exact Tb].
        + intros p nm Hp Tp. apply KL3. split; [exact Hp| intros X; apply (NKX _ (proj2 (mbio_T_blocks _ _) X)); apply mbio_T_blocks in Tp; apply in_or_app; left; exact Tp].
      - intros b Hb. destruct (proj1 (KB3 b) Hb) as [Hb2 NI]. destruct (ELB2 _ Hb2) as [X|[X|X]]; [left; exact X| | right; right; exact X].
        apply in_app_iff in X. destruct X as [X|X]; [exfalso; exact (NI X)| right; left; exact X].
      - intros b Hb. apply KB3. split; [exact (SN2 _ Hb)|]. intros X. apply (NKX _ (proj2 (mbio_T_blocks _ _) X)). apply in_or_app; right; apply in_or_app; left. apply in_map. exact Hb.
      - eapply strs_inL_keep; [exact SL2| intros q nm Hq NX; apply KL3; split; [exact Hq| exact NX]
          | intros b Hb X; apply (NKX _ (proj2 (mbio_T_blocks _ _) X)); apply in_or_app; right; apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
      - intros b Hb. apply KB3. split; [exact (PLB2 _ Hb)|]. intros X. apply (CFRESH _ Hb). apply in_or_app; left; exact X.
      - intros q nm Hq. apply KL3. split; [exact (PLC2 _ _ Hq)|]. intros X. apply (EL _ _ Hq). apply in_or_app; left; exact X. }
    (* [comment removed for export] *)
    assert (K2 : forall s1' LB1 L1 f1 m1 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
      cstate s1' LB1 (e_LB0 en) L1 m1 (wz (bv_unsigned (e_sp en) + -208)) (e_tp en) (e_lo en) (e_B en) ->
      cframe (pem_T en) [] (bv_unsigned (e_sp en) + 32) (e_s en) (e_LBall en) (e_L en) (e_m en) s1' LB1 L1 m1 ->
      libenv m1 (e_LBL en) (e_E en) -> incl_blocks (e_LBL en) LB1 -> cown LB1 L1 (e_pe en) (e_E en) 904 (e_Enm en) ->
      mbio_rep m1 LB1 L1 (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off -> pem_err errst_at_rest errst_live en strs m1 ->
      rw_cells usegs m1 (bv_unsigned (e_sp en) + -104) (pem_saved en) -> rw_cells usegs m1 (bv_unsigned (e_sp en) + -208) loc ->
      pem_out ret m1 LB1 L1 (bv_unsigned (e_sp en) + 24) (bv_unsigned (e_sp en) + 16) (bv_unsigned (e_sp en) + 8) (bv_unsigned (e_sp en)) news ->
      (e_f en - pem_EV en + 11 <= f1)%nat -> cgrow (e_L en) L1 16 8 (pem_BIG en) ->
      match oname with None => namev = 0 | Some qn => cown LB1 L1 qn namev nn nn /\ 1 <= nn /\ rw_cells usegs m1 namev [CB 0%nat []] end ->
      mbio_repx m1 LB1 L1 KX hBv BMX blwX methX lenX maxX offX -> mbio_repx m1 LB1 L1 KY dBv BMY blwY methY lenY maxY offY ->
      (forall b, In b LB1 -> In b (e_LBall en) \/ In (blk_id b) (mbio_blocks KX ++ mbio_blocks KY ++ opt_ids oname) \/ In b (strs ++ news)) -> incl_blocks (strs ++ news) LB1 ->
      strs_inL L1 strs -> incl_blocks (e_LBall en) LB1 -> (forall q nm, In (q, nm) (e_L en) -> In (q, nm) L1) ->
      climpl f1 L1 s1' (MS (mkR (wz 0x1881e8) (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) y0 y1 y2 (e_sp en) (wz dBv) y3 y4 y5 y6 y7 y8 y9 y10
                             (wz namev) (wz ret) s2 (wz (e_flags en)) (wz hBv) s5 (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) s10 s11 y11 y12 y13 y14)
                         (e_F en) (wz 0x1881e8) (e_fc en) None m1 (seg_rom usegs)) (pem_post libenv errst_live en)).
    { intros s1' LB1 L1 f1 m1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CST1 FR1 LE1 INCL1 OWNE1 MB1 PE1 SAVED1 LOC1 PO1 FU1 CG1 HNAME1 MBX1 MBY1 ELB1 SN1 SL1 PLB1 PLC1.
      pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      cprefix. ths. ths. ths. ths. ths. chere.
      destruct oname as [qn|].
      - (* [comment removed for export] *)
        destruct HNAME1 as (OWNN & NN1 & NC).
        assert (NQN : ~ In qn (mbio_blocks KX ++ mbio_blocks KY ++ map blk_id (strs ++ news) ++ e_pe en :: mbio_blocks (e_K en))).
        { intros X. apply in_app_iff in X. destruct X as [X|X]; [apply (DJX _ X); apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
          apply in_app_iff in X. destruct X as [X|X]; [apply (DJY _ X); apply in_or_app; right; left; reflexivity|].
          apply (DJC qn); [do 3 (apply in_or_app; right); left; reflexivity| exact X]. }
        eapply climpl_seq.
        { eapply PF with (p := qn) (A := namev) (n := nn) (nm := nn) (num := 0) (flags := e_flags en) (junk := []) (lo := e_lo en) (B := e_B en);
            [clear - FU1; lia| exact OWNN| clear - NN1; lia| exact NC| clear - FLR; lia| exact CST1| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia
            | reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (-> & i & HI & ->)).
        destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
        pose proof FRM2 as (CFR2 & KP2 & _).
        assert (KB2 : forall b, In b LB1 -> blk_id b <> qn -> In b (lb_remove qn LB1)) by (intros b Hb NE; apply lb_remove_In; split; [exact Hb| exact NE]).
        assert (KL2 : forall q nm, In (q, nm) L1 -> q <> qn -> In (q, nm) (cremove i L1)) by (intros q nm Hq NE; eapply cremove_keep; [exact HI| exact Hq| exact NE]).
        assert (KO2 : forall p A n nm, p <> qn -> cown LB1 L1 p A n nm -> cown (lb_remove qn LB1) (cremove i L1) p A n nm).
        { intros p A n nm NE O. eapply cown_keep; [exact O| intros I; exact (KB2 _ I NE)| intros I; exact (KL2 _ _ I NE)]. }
        eapply K3; [exact CST2| | | | | | | exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 SAVED1 ltac:(clear; lia))| exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia))
                  | | clear - FU1 FU2; lia| eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG1 GR2)| | |]; try (unfold wA, wB, wBig; destruct (nn <=? TIER_A_MAX); destruct (TIER_A_MAX <? nn); clear - NN1; lia)| | | | | | |].
        + eapply cframe_call; [exact FR1| exact FRM2| clear; lia| intros a X; exact X|]. intros q Hq _ X. subst q.
          destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
          * destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 3 (apply in_or_app; right); left; reflexivity.
          * destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 3 (apply in_or_app; right); left; reflexivity.
        + eapply libenv_cfrI; [exact LE1| exact CFR2| exact INCL1| intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); rewrite <- X; do 3 (apply in_or_app; right); left; reflexivity].
        + eapply incl_blocks_keep; [exact INCL1| exact KP2| intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); rewrite <- X; do 3 (apply in_or_app; right); left; reflexivity].
        + apply KO2; [| exact OWNE1]. intros X. apply NQN. rewrite <- X. do 2 (apply in_or_app; right); apply in_or_app; right; left; reflexivity.
        + eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB1| exact CFR2| intros q Hq X; subst q; apply NQN; apply mbio_T_blocks in Hq; do 3 (apply in_or_app; right); right; exact Hq]| |].
          * intros b Hb Tb. apply KB2; [exact Hb| intros X; apply NQN; rewrite <- X; apply mbio_T_blocks in Tb; do 3 (apply in_or_app; right); right; exact Tb].
          * intros p nm Hp Tp. apply KL2; [exact Hp| intros X; apply NQN; rewrite <- X; apply mbio_T_blocks in Tp; do 3 (apply in_or_app; right); right; exact Tp].
        + eapply pem_err_cfrI; [exact PE1| exact CFR2| exact (proj1 OWNE1)| intros X; apply NQN; rewrite <- X; do 2 (apply in_or_app; right); apply in_or_app; right; left; reflexivity
            | intros b Hb; apply SN1; apply in_or_app; left; exact Hb| intros b Hb X; apply NQN; rewrite X; do 2 (apply in_or_app; right); apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
        + eapply pem_out_keep; [exact PO1| exact CFR2| clear; lia| intros p A n nm Hn O; apply KO2; [| exact O]| intros b Hb; apply SN1; apply in_or_app; right; exact Hb|].
          * intros X. apply NQN. rewrite <- X. do 2 (apply in_or_app; right); apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hn].
          * intros b Hb X. apply NQN. rewrite X. do 2 (apply in_or_app; right); apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map. exact Hb.
        + eapply mbio_repx_keep; [eapply mbio_repx_cfr; [exact MBX1| exact CFR2| intros q Hq X; subst q; apply NQN; apply mbio_T_blocks in Hq; apply in_or_app; left; exact Hq]| |].
          * intros b Hb Tb. apply KB2; [exact Hb| intros X; apply NQN; rewrite <- X; apply mbio_T_blocks in Tb; apply in_or_app; left; exact Tb].
          * intros p nm Hp Tp. apply KL2; [exact Hp| intros X; apply NQN; rewrite <- X; apply mbio_T_blocks in Tp; apply in_or_app; left; exact Tp].
        + eapply mbio_repx_keep; [eapply mbio_repx_cfr; [exact MBY1| exact CFR2| intros q Hq X; subst q; apply NQN; apply mbio_T_blocks in Hq; apply in_or_app; right; apply in_or_app; left; exact Hq]| |].
          * intros b Hb Tb. apply KB2; [exact Hb| intros X; apply NQN; rewrite <- X; apply mbio_T_blocks in Tb; apply in_or_app; right; apply in_or_app; left; exact Tb].
          * intros p nm Hp Tp. apply KL2; [exact Hp| intros X; apply NQN; rewrite <- X; apply mbio_T_blocks in Tp; apply in_or_app; right; apply in_or_app; left; exact Tp].
        + intros b Hb. apply lb_remove_In in Hb. destruct Hb as [Hb NE]. destruct (ELB1 _ Hb) as [X|[X|X]]; [left; exact X| | right; right; exact X].
          rewrite app_assoc in X. apply in_app_iff in X. destruct X as [X|X]; [right; left; exact X| exfalso; cbn in X; destruct X as [X|[]]; exact (NE (eq_sym X))].
        + intros b Hb. apply KB2; [exact (SN1 _ Hb)| intros X; apply NQN; rewrite <- X; do 2 (apply in_or_app; right); apply in_or_app; left; apply in_map; exact Hb].
        + eapply strs_inL_keep; [exact SL1| intros q nm Hq NX; exact (KL2 _ _ Hq NX)
            | intros b Hb X; apply NQN; rewrite <- X; do 2 (apply in_or_app; right); apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
        + intros b Hb. apply KB2; [exact (PLB1 _ Hb)| intros X; apply (CFRESH _ Hb); rewrite X; do 3 (apply in_or_app; right); left; reflexivity].
        + intros q nm Hq. apply KL2; [exact (PLC1 _ _ Hq)| intros X; apply (EL _ _ Hq); rewrite X; do 3 (apply in_or_app; right); left; reflexivity].
      - (* [comment removed for export] *)
        subst namev.
        eapply climpl_seq. { eapply PFN with (flags := e_flags en) (lo := e_lo en) (B := e_B en); [clear - FLR; lia| exact CST1| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
        cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (-> & ->)).
        destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
        pose proof FRM2 as (CFR2 & KP2 & _).
        eapply K3; [exact CST2| | | exact INCL1| exact OWNE1| | | exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 SAVED1 ltac:(clear; lia))| exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia))
                  | | clear - FU1 FU2; lia| eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG1 GR2)| clear; lia| clear; lia| clear; lia]| | | | exact SN1| exact SL1| exact PLB1| exact PLC1].
        + eapply cframe_call; [exact FR1| exact FRM2| clear; lia| intros a X; exact X| intros q _ _ X; exact X].
        + eapply libenv_cfrI; [exact LE1| exact CFR2| exact INCL1| intros b _ X; exact X].
        + eapply mbio_rep_cfr; [exact MB1| exact CFR2| intros q _ X; exact X].
        + eapply pem_err_cfrI; [exact PE1| exact CFR2| exact (proj1 OWNE1)| intros X; exact X| intros b Hb; apply SN1; apply in_or_app; left; exact Hb| intros b _ X; exact X].
        + eapply pem_out_keep; [exact PO1| exact CFR2| clear; lia| intros p A n nm _ O; exact O| intros b Hb; apply SN1; apply in_or_app; right; exact Hb| intros b _ X; exact X].
        + eapply mbio_repx_cfr; [exact MBX1| exact CFR2| intros q _ X; exact X].
        + eapply mbio_repx_cfr; [exact MBY1| exact CFR2| intros q _ X; exact X].
        + intros b Hb. destruct (ELB1 _ Hb) as [X|[X|X]]; [left; exact X| right; left; rewrite app_assoc in X; apply in_app_iff in X; destruct X as [X|[]]; exact X| right; right; exact X]. }
    (* [comment removed for export] *)
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    cprefix. ths. ths. chere.
    destruct octx as [qc|].
    - assert (NQC : ~ In qc (mbio_blocks KX ++ mbio_blocks KY ++ opt_ids oname ++ map blk_id (strs ++ news) ++ e_pe en :: mbio_blocks (e_K en))).
      { intros X. apply in_app_iff in X. destruct X as [X|X]; [apply (DJX _ X); apply in_or_app; right; apply in_or_app; left; left; reflexivity|].
        apply in_app_iff in X. destruct X as [X|X]; [apply (DJY _ X); apply in_or_app; left; left; reflexivity|].
        apply in_app_iff in X. destruct X as [X|X]; [exact (DJCN qc ltac:(left; reflexivity) X)|].
        apply (DJC qc); [do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity| exact X]. }
      eapply climpl_seq.
      { eapply CF with (p := qc) (A := ctxv) (lo := e_lo en) (B := e_B en);
          [clear - FU REM; lia| exact HCTX| exact CST| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity]. }
      cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & i & HI & ->)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
      pose proof FRM1 as (CFR1 & KP1 & _).
      assert (KB1 : forall b, In b LBc -> blk_id b <> qc -> In b (lb_remove qc LBc)) by (intros b Hb NE; apply lb_remove_In; split; [exact Hb| exact NE]).
      assert (KL1 : forall q nm, In (q, nm) Lc -> q <> qc -> In (q, nm) (cremove i Lc)) by (intros q nm Hq NE; eapply cremove_keep; [exact HI| exact Hq| exact NE]).
      assert (KO1 : forall p A n nm, p <> qc -> cown LBc Lc p A n nm -> cown (lb_remove qc LBc) (cremove i Lc) p A n nm).
      { intros p A n nm NE O. eapply cown_keep; [exact O| intros I; exact (KB1 _ I NE)| intros I; exact (KL1 _ _ I NE)]. }
      eapply K2; [exact CST1| | | | | | | exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(clear; lia))| exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia))
                | | clear - FU FU1 REM; lia| eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG0 GR1)| clear; lia| clear; lia| clear; lia]| | | | | | | |].
      + eapply cframe_call; [exact FR0| exact FRM1| clear; lia| intros a X; exact X|]. intros q Hq _ X. subst q.
        destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
        * destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity.
        * destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity.
      + eapply libenv_cfrI; [exact LE| exact CFR1| exact INCL| intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); rewrite <- X; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity].
      + eapply incl_blocks_keep; [exact INCL| exact KP1| intros b Hb X; apply (CFRESH b (INCL0 _ Hb)); rewrite <- X; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity].
      + apply KO1; [| exact OWNE]. intros X. apply NQC. rewrite <- X. do 3 (apply in_or_app; right); apply in_or_app; right; left; reflexivity.
      + eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB| exact CFR1| intros q Hq X; subst q; apply NQC; apply mbio_T_blocks in Hq; do 4 (apply in_or_app; right); right; exact Hq]| |].
        * intros b Hb Tb. apply KB1; [exact Hb| intros X; apply NQC; rewrite <- X; apply mbio_T_blocks in Tb; do 4 (apply in_or_app; right); right; exact Tb].
        * intros p nm Hp Tp. apply KL1; [exact Hp| intros X; apply NQC; rewrite <- X; apply mbio_T_blocks in Tp; do 4 (apply in_or_app; right); right; exact Tp].
      + eapply pem_err_cfrI; [exact PE| exact CFR1| exact INE| intros X; apply NQC; rewrite <- X; do 3 (apply in_or_app; right); apply in_or_app; right; left; reflexivity
          | intros b Hb; apply SN; apply in_or_app; left; exact Hb| intros b Hb X; apply NQC; rewrite X; do 3 (apply in_or_app; right); apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
      + eapply pem_out_keep; [exact PO| exact CFR1| clear; lia| intros p A n nm Hn O; apply KO1; [| exact O]| intros b Hb; apply SN; apply in_or_app; right; exact Hb|].
        * intros X. apply NQC. rewrite <- X. do 3 (apply in_or_app; right); apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hn].
        * intros b Hb X. apply NQC. rewrite X. do 3 (apply in_or_app; right); apply in_or_app; left. rewrite map_app; apply in_or_app; right. apply in_map. exact Hb.
      + destruct oname as [qn|]; [| exact HNAME]. destruct HNAME as (OWNN & NN1 & NC).
        assert (NE : qn <> qc) by (intros E; apply NQC; do 2 (apply in_or_app; right); apply in_or_app; left; left; exact E).
        split; [apply KO1; [exact NE| exact OWNN]|]. split; [exact NN1|].
        eapply (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NC (proj1 OWNN)); [cbn [blk_id fst]; intros E; exact (NE (eq_sym E))| unfold blk_addr; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; clear - NN1; lia].
      + eapply mbio_repx_keep; [eapply mbio_repx_cfr; [exact MBX| exact CFR1| intros q Hq X; subst q; apply NQC; apply mbio_T_blocks in Hq; apply in_or_app; left; exact Hq]| |].
        * intros b Hb Tb. apply KB1; [exact Hb| intros X; apply NQC; rewrite <- X; apply mbio_T_blocks in Tb; apply in_or_app; left; exact Tb].
        * intros p nm Hp Tp. apply KL1; [exact Hp| intros X; apply NQC; rewrite <- X; apply mbio_T_blocks in Tp; apply in_or_app; left; exact Tp].
      + eapply mbio_repx_keep; [eapply mbio_repx_cfr; [exact MBY| exact CFR1| intros q Hq X; subst q; apply NQC; apply mbio_T_blocks in Hq; apply in_or_app; right; apply in_or_app; left; exact Hq]| |].
        * intros b Hb Tb. apply KB1; [exact Hb| intros X; apply NQC; rewrite <- X; apply mbio_T_blocks in Tb; apply in_or_app; right; apply in_or_app; left; exact Tb].
        * intros p nm Hp Tp. apply KL1; [exact Hp| intros X; apply NQC; rewrite <- X; apply mbio_T_blocks in Tp; apply in_or_app; right; apply in_or_app; left; exact Tp].
      + intros b Hb. apply lb_remove_In in Hb. destruct Hb as [Hb NEb]. destruct (ELB _ Hb) as [X|[X|X]]; [left; exact X| right; left| right; right; exact X].
        rewrite !in_app_iff in X |- *. cbn [opt_ids app In] in X. destruct X as [X|[X|[X|X]]]; [tauto| tauto| exfalso; exact (NEb (eq_sym X))| tauto].
      + intros b Hb. apply KB1; [exact (SN _ Hb)| intros X; apply NQC; rewrite <- X; do 3 (apply in_or_app; right); apply in_or_app; left; apply in_map; exact Hb].
      + eapply strs_inL_keep; [exact SL| intros q nm Hq NX; exact (KL1 _ _ Hq NX)
          | intros b Hb X; apply NQC; rewrite <- X; do 3 (apply in_or_app; right); apply in_or_app; left; rewrite map_app; apply in_or_app; left; apply in_map; exact Hb].
      + intros b Hb. apply KB1; [exact (PLB _ Hb)| intros X; apply (CFRESH _ Hb); rewrite X; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity].
      + intros q nm Hq. apply KL1; [exact (PLC _ _ Hq)| intros X; apply (EL _ _ Hq); rewrite X; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity].
    - subst ctxv.
      eapply climpl_seq. { eapply CFN with (lo := e_lo en) (B := e_B en); [exact CST| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity]. }
      cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & ->)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
      pose proof FRM1 as (CFR1 & KP1 & _).
      eapply K2; [exact CST1| | | exact INCL| exact OWNE| | | exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(clear; lia))| exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia))
                | | clear - FU FU1 REM; lia| eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG0 GR1)| clear; lia| clear; lia| clear; lia]| | | | | exact SN| exact SL| exact PLB| exact PLC].
      + eapply cframe_call; [exact FR0| exact FRM1| clear; lia| intros a X; exact X| intros q _ _ X; exact X].
      + eapply libenv_cfrI; [exact LE| exact CFR1| exact INCL| intros b _ X; exact X].
      + eapply mbio_rep_cfr; [exact MB| exact CFR1| intros q _ X; exact X].
      + eapply pem_err_cfrI; [exact PE| exact CFR1| exact INE| intros X; exact X| intros b Hb; apply SN; apply in_or_app; left; exact Hb| intros b _ X; exact X].
      + eapply pem_out_keep; [exact PO| exact CFR1| clear; lia| intros p A n nm _ O; exact O| intros b Hb; apply SN; apply in_or_app; right; exact Hb| intros b _ X; exact X].
      + destruct oname as [qn|]; [| exact HNAME]. destruct HNAME as (OWNN & NN1 & NC). split; [exact OWNN|]. split; [exact NN1|].
        exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 NC ltac:(clear; lia)) || (eapply (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NC (proj1 OWNN)); [cbn [blk_id fst]; intros []| unfold blk_addr; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; clear - NN1; lia]).
      + eapply mbio_repx_cfr; [exact MBX| exact CFR1| intros q _ X; exact X].
      + eapply mbio_repx_cfr; [exact MBY| exact CFR1| intros q _ X; exact X].
      + intros b Hb. destruct (ELB _ Hb) as [X|[X|X]]; [left; exact X| right; left| right; right; exact X].
        rewrite !in_app_iff in X |- *. cbn [opt_ids app In] in X. tauto.
  Qed.
End W3.
