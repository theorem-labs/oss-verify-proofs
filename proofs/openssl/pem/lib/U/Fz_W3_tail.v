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
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
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
  Local Notation err_callI := (err_call errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where).
  Local Notation err_segI := (pem_err_munch errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem OUTFREE_proof : pem_free_stmt -> pem_free_null_stmt -> END_stmt libenv errst_at_rest errst_live -> OUTFREE_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros PF PFN ENDP en s LBc Lc f m off rem rA rB rBig strs xra t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 l11 ta tb
           qc qn qh ctxv namev nn HD nh hBv dBv bh KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
    cbv zeta. intros COM PE REM LOC OWNC OWNN NN1 OWNH NH1 LBH HC MBX MBY ELB SN SL CFRESH SFR EL NDT OUT. unfold END_stmt, J_END in ENDP.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_OUTFREE, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|x1 k1 NQ1 ND4]; subst. inversion ND4 as [|x2 k2 NQ2 _]; subst. cbn [In] in NQ1, NQ2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    assert (SUB : forall x, In x (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) -> In x (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn; qh])).
    { intros x X. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
      cbn in X |- *. clear - X. tauto. }
    assert (NQH : ~ In qh (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn] ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en))).
    { intros X. apply in_app_iff in X. destruct X as [X|X]; [apply (DJX _ X); apply in_or_app; right; do 2 right; left; reflexivity|].
      apply in_app_iff in X. destruct X as [X|X]; [apply (DJY _ X); do 2 right; left; reflexivity|].
      apply in_app_iff in X. destruct X as [X|X]; [cbn in X; clear - X NQ1 NQ2; intuition congruence|].
      apply (DJC qh); [do 2 (apply in_or_app; right); do 2 right; left; reflexivity| exact X]. }
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ qh = q).
    { intros q [Hq|Hq] _ <-; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). do 2 right; left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). do 2 right; left; reflexivity. }
    assert (HK1 : forall q, mbio_T (e_K en) q -> ~ qh = q) by (intros q Hq <-; apply NQH; apply mbio_T_blocks in Hq; do 4 (apply in_or_app; right); right; exact Hq).
    assert (HE1 : ~ qh = e_pe en) by (intros X; apply NQH; do 4 (apply in_or_app; right); left; exact (eq_sym X)).
    assert (HX1 : forall q, mbio_T KX q -> ~ qh = q) by (intros q Hq <-; apply NQH; apply mbio_T_blocks in Hq; apply in_or_app; left; exact Hq).
    assert (HY1 : forall q, mbio_T KY q -> ~ qh = q) by (intros q Hq <-; apply NQH; apply mbio_T_blocks in Hq; apply in_or_app; right; apply in_or_app; left; exact Hq).
    assert (HS1 : forall b, In b strs -> ~ qh = blk_id b) by (intros b Hb X; apply NQH; do 3 (apply in_or_app; right); apply in_or_app; left; rewrite X; apply in_map; exact Hb).
    assert (HC1 : ~ qh = qc) by (clear - NQ1; intuition). assert (HN1 : ~ qh = qn) by (clear - NQ2; intuition).
    pose proof (w_bounds nh ltac:(clear - NH1; lia)) as WB.
    destruct (rw_cells_CB_split_at usegs m HD (Z.to_nat nh) bh 0 ltac:(clear; lia) HC) as [HC0 _]. cbn [firstn] in HC0.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply PF with (p := qh) (A := HD) (n := nh) (nm := nh) (num := 0) (flags := e_flags en) (junk := []) (lo := e_lo en) (B := e_B en);
        [clear - FU REM; lia| exact OWNH| clear - NH1; lia| exact HC0| clear - FLR; lia| exact CST| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia
        | reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & i & HI & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    assert (COM1 : pem_com libenv en st1 (lb_remove qh LBc) (cremove i Lc) f1 m1 off 13 rA rB rBig).
    { eapply (com_callI en) with (T1 := eq qh); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear - REM; lia| exact GR1| | | | | | | exact HT1| exact HK1| exact HE1]; clear - WB RA0 RB0 RBIG0; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX FRM1 HX1) as MBX1. pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY FRM1 HY1) as MBY1.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC FRM1 HC1) as OWNC1. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN FRM1 HN1) as OWNN1.
    destruct (err_callI en strs _ _ _ _ _ _ _ _ _ _ PE FRM1 INE HE1 SN HS1) as [PE1 SN1]. pose proof (strs_call strs _ _ _ _ _ _ _ _ _ _ SL FRM1 HS1) as SL1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia. pose proof COM1 as (_ & _ & _ & _ & _ & _ & OWNE1 & _).
    pose proof (munch_refl [(bv_unsigned (e_sp en) + 16, bv_unsigned (e_sp en) + 24)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. ths. ths. chere.
    lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into m1' end.
    lazymatch goal with H : stk usegs m1' _ _ |- _ => rename H into ST1' end. lazymatch goal with H : mem_inv usegs m1' |- _ => rename H into MI1' end.
    lazymatch goal with H : munch _ m1 m1' |- _ => rename H into MU1' end. lazymatch goal with H : wmono usegs m1 m1' |- _ => rename H into WM1' end.
    assert (HWlo1 : Forall (wfree (lb_remove qh LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True)) [(bv_unsigned (e_sp en) + 16, bv_unsigned (e_sp en) + 24)])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    assert (COM1' : pem_com libenv en st1 (lb_remove qh LBc) (cremove i Lc) f1 m1' off 13 rA rB rBig).
    { eapply (com_segI en) with (EX := fun _ => True); [exact COM1| exact MU1'| exact WM1'| exact MI1'| exact ST1'| exact HWlo1| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
    pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1 CST1 MU1' WM1' HWlo1 ltac:(intros q _; exact I)) as MBX1'.
    pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY1 CST1 MU1' WM1' HWlo1 ltac:(intros q _; exact I)) as MBY1'.
    pose proof (err_segI _ en strs _ _ _ _ _ _ _ _ _ _ _ _ PE1 MU1' WM1' CST1 (proj1 OWNE1) SN1 HWlo1 I ltac:(intros b _; exact I)) as PE1'.
    pose proof COM1' as (CST1' & _). clear CST1.
    eapply climpl_seq. { eapply PFN with (flags := e_flags en) (lo := e_lo en) (B := e_B en); [clear - FLR; lia| exact CST1'| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (-> & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    pose proof COM1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RA1 & RB1 & RBIG1 & _).
    assert (COM2 : pem_com libenv en st2 (lb_remove qh LBc) (cremove i Lc) f2 m2 off 12 rA rB rBig).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM1'| exact CST2| exact FRM2| unfold e_PL; clear; lia| exact FU2| clear; lia| exact GR2| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X]; clear - RA1 RB1 RBIG1; lia. }
    pose proof FRM2 as (CFR2 & _).
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1' FRM2 ltac:(intros q _ X; exact X)) as MBX2. pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY1' FRM2 ltac:(intros q _ X; exact X)) as MBY2.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC1 FRM2 ltac:(intros X; exact X)) as OWNC2. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN1 FRM2 ltac:(intros X; exact X)) as OWNN2.
    destruct (err_callI en strs _ _ _ _ _ _ _ _ _ _ PE1' FRM2 (proj1 OWNE1) ltac:(intros X; exact X) SN1 ltac:(intros b _ X; exact X)) as [PE2 SN2].
    pose proof (strs_call strs _ _ _ _ _ _ _ _ _ _ SL1 FRM2 ltac:(intros b _ X; exact X)) as SL2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia. pose proof COM2 as (_ & _ & _ & _ & _ & _ & OWNE2 & _).
    pose proof (munch_refl [(bv_unsigned (e_sp en) + 8, bv_unsigned (e_sp en) + 16)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    clear CST1' HP1 MI1' ST1' LOC1 OUT1.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2' end.
    lazymatch goal with H : stk usegs m2' _ _ |- _ => rename H into ST2' end. lazymatch goal with H : mem_inv usegs m2' |- _ => rename H into MI2' end.
    lazymatch goal with H : munch _ m2 m2' |- _ => rename H into MU2' end. lazymatch goal with H : wmono usegs m2 m2' |- _ => rename H into WM2' end.
    chere.
    assert (HWlo2 : Forall (wfree (lb_remove qh LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True)) [(bv_unsigned (e_sp en) + 8, bv_unsigned (e_sp en) + 16)])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    assert (COM2' : pem_com libenv en st2 (lb_remove qh LBc) (cremove i Lc) f2 m2' off 12 rA rB rBig).
    { eapply (com_segI en) with (EX := fun _ => True); [exact COM2| exact MU2'| exact WM2'| exact MI2'| exact ST2'| exact HWlo2| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
    pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2 CST2 MU2' WM2' HWlo2 ltac:(intros q _; exact I)) as MBX2'.
    pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2 CST2 MU2' WM2' HWlo2 ltac:(intros q _; exact I)) as MBY2'.
    pose proof (err_segI _ en strs _ _ _ _ _ _ _ _ _ _ _ _ PE2 MU2' WM2' CST2 (proj1 OWNE2) SN2 HWlo2 I ltac:(intros b _; exact I)) as PE2'.
    destruct (out4_split _ _ _ _ _ _ OUT2) as (O1 & O2 & O3 & O4).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ (proj1 COM2') (proj1 OWNN2)) as (RN1 & _ & _ & RN2 & _).
    eapply (ENDP en st2 (lb_remove qh LBc) (cremove i Lc) f2 m2' off 12%nat rA rB rBig (pem_loc l0 l1 (wz namev) l3 l4 l5 (wz (bv_unsigned (e_sp en) + 8)) (wz (bv_unsigned (e_sp en) + 16)) l8 l9 (wz (e_flags en)) l11 ta tb) strs []
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Some qc) (Some qn) ctxv namev nn hBv dBv 0 KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY);
      [exact COM2'| exact PE2'| clear; lia| unfold pem_loc; exact LOC2| reflexivity| cbv iota beta; exact OWNC2
      | cbv iota beta; split; [exact OWNN2| split; [exact NN1| apply rw_cells_CB0; clear - RN1 RN2 NN1 LO SLO SPR; lia]]| exact MBX2'| exact MBY2'| | | | | | | | |].
    - intros b Hb. cbn [opt_ids app]. rewrite app_nil_r. apply lb_remove_In in Hb. destruct Hb as [Hb NE]. destruct (ELB _ Hb) as [X|[X|X]]; [left; exact X| right; left| right; right; exact X].
      apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
      cbn in X |- *. clear - X NE. intuition congruence.
    - rewrite app_nil_r. exact SN2.
    - exact SL2.
    - intros b Hb X. apply (CFRESH _ Hb). apply SUB. cbn [opt_ids app] in X. exact X.
    - rewrite app_nil_r. exact SFR.
    - intros q nm Hq X. apply (EL _ _ Hq). apply SUB. cbn [opt_ids app] in X. exact X.
    - cbn [opt_ids app]. rewrite app_nil_r. apply (nd_drop (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) _ qh).
      lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn; qh]) ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en)); [exact NDT| rewrite <- ?app_assoc; reflexivity] end.
    - left. split; [reflexivity|]. split; [reflexivity|]. split; [exact O4|]. split; [exact O3|]. split; [exact O2| eexists; exact O1].
    - pose proof COM2' as (_ & _ & _ & _ & _ & _ & _ & _ & OFF2 & _). cbn. clear - OFF2. lia.
  Qed.
End W3.
