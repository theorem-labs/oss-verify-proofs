(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
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

(* [comment removed for export] *)
Definition gn_func_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x380d1 8 with Some bs => bs | None => [] end).
Definition gn_func_slk : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x380da 6 with Some bs => bs | None => [] end).
Lemma gn_func_ro : ro_bytes Image.usegs 0x380d1 (gn_func_str ++ Z_to_bv 8 0 :: gn_func_slk).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma gn_func_nonul : ~ In (Z_to_bv 8 0) gn_func_str.
Proof. unfold gn_func_str. intros H. repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate|]). exact H. Qed.
Lemma gn_func_len : length gn_func_str = 8%nat. Proof. reflexivity. Qed.

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
  Local Notation err_callI := (err_call errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where).
  Local Notation com_callEI := (com_callE libenv).

  Theorem FREE1_proof : pem_free_stmt -> END_stmt libenv errst_at_rest errst_live -> FREE1_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros PF ENDP en s LBc Lc f m off rem rA rB rBig strs xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l6 l7 l10 l11 ta tb
           ql LB1 hBv dBv bs KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM PE REM LOC OWNL LBS LBC MBX MBY ELB SN SL CFRESH SFR EL NDT OUT. unfold END_stmt, J_END in ENDP. unfold pem_free_stmt in PF.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_FREE1, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    (* [comment removed for export] *)
    assert (NQL : ~ In ql (mbio_blocks KX ++ mbio_blocks KY ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en))).
    { intros X. apply in_app_iff in X. destruct X as [X|X]; [apply (DJX _ X); apply in_or_app; right; left; reflexivity|].
      apply in_app_iff in X. destruct X as [X|X]; [apply (DJY _ X); left; reflexivity|].
      apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| exact X]. }
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ ql = q).
    { intros q [Hq|Hq] _ <-; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). left; reflexivity. }
    assert (HK1 : forall q, mbio_T (e_K en) q -> ~ ql = q) by (intros q Hq <-; apply NQL; apply mbio_T_blocks in Hq; do 3 (apply in_or_app; right); right; exact Hq).
    assert (HE1 : ~ ql = e_pe en) by (intros X; apply NQL; do 3 (apply in_or_app; right); left; exact (eq_sym X)).
    assert (HX1 : forall q, mbio_T KX q -> ~ ql = q) by (intros q Hq <-; apply NQL; apply mbio_T_blocks in Hq; apply in_or_app; left; exact Hq).
    assert (HY1 : forall q, mbio_T KY q -> ~ ql = q) by (intros q Hq <-; apply NQL; apply mbio_T_blocks in Hq; apply in_or_app; right; apply in_or_app; left; exact Hq).
    assert (HS1 : forall b, In b strs -> ~ ql = blk_id b) by (intros b Hb X; apply NQL; do 2 (apply in_or_app; right); apply in_or_app; left; rewrite X; apply in_map; exact Hb).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply PF with (p := ql) (A := LB1) (n := 256) (nm := 256) (num := 256) (flags := e_flags en) (junk := bs) (lo := e_lo en) (B := e_B en);
        [clear - FU REM; lia| exact OWNL| clear; lia| exact LBC| clear - FLR; lia| exact CST| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia
        | reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1' & RET & FU1 & GR1 & CST1 & FRM1 & (-> & i & HI & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof (w_bounds 256 ltac:(clear; lia)) as (WA & WB' & WAB & WBIG).
    assert (COM1 : pem_com libenv en st1 (lb_remove ql LBc) (cremove i Lc) f1 m1 off 12 rA rB rBig).
    { eapply (com_callI en) with (T1 := eq ql); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear - REM; lia| exact GR1| | | | | | | exact HT1| exact HK1| exact HE1]; clear - WA WB' WBIG RA0 RB0 RBIG0; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX FRM1 HX1) as MBX1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY FRM1 HY1) as MBY1.
    destruct (err_callI en strs _ _ _ _ _ _ _ _ _ _ PE FRM1 INE HE1 SN HS1) as [PE1 SN1]. pose proof (strs_call strs _ _ _ _ _ _ _ _ _ _ SL FRM1 HS1) as SL1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 LOC OUT MBX MBY.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. chere.
    destruct (out4_split _ _ _ _ _ _ OUT1) as (O1 & O2 & O3 & O4). destruct MBX1 as [BMX MBX1]. destruct MBY1 as [BMY MBY1].
    eapply (ENDP en st1 (lb_remove ql LBc) (cremove i Lc) f1 m1 off 12%nat rA rB rBig _ strs [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ None None 0 0 0 hBv dBv 0
              KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) (wz lenY));
      [exact COM1| exact PE1| clear; lia| exact LOC1| reflexivity| reflexivity| reflexivity| exact MBX1| exact MBY1| | rewrite app_nil_r; exact SN1| exact SL1| | rewrite app_nil_r; exact SFR| | | | cbn; clear - OFF; lia].
    - intros b Hb. cbn [opt_ids app]. rewrite !app_nil_r. apply lb_remove_In in Hb. destruct Hb as [Hb NE]. destruct (ELB _ Hb) as [X|[X|X]]; [left; exact X| right; left| right; right; exact X].
      apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. destruct X as [X|X]; [exact X|]. exfalso. cbn in X. clear - X NE. intuition congruence.
    - intros b Hb X. apply (CFRESH _ Hb). cbn [opt_ids app] in X. rewrite !app_nil_r in X. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right; apply in_or_app; left; exact X].
    - intros q nm Hq X. apply (EL _ _ Hq). cbn [opt_ids app] in X. rewrite !app_nil_r in X. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right; apply in_or_app; left; exact X].
    - cbn [opt_ids app]. rewrite !app_nil_r. apply (nd_drop (mbio_blocks KX ++ mbio_blocks KY) _ ql).
      lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [ql]) ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en)); [exact NDT| rewrite <- ?app_assoc; reflexivity] end.
    - left. split; [reflexivity|]. split; [reflexivity|]. split; [exact O4|]. split; [exact O3|]. split; [exact O2| eexists; exact O1].
  Qed.

  Theorem RAISE1_proof :
    err_new_rest_stmt libenv errst_at_rest errst_live -> err_set_debug_stmt libenv errst_live -> err_set_error_stmt libenv errst_live ->
    FREE1_stmt libenv errst_at_rest errst_live -> RAISE1_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ENEW EDBG ESET FREE1P en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l6 l7 l11 ta tb
           ql LB2 hBv dBv bs KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM ER0 REM RA2 LOC OWNL LBS LBC MBX MBY ELB CFRESH EL NDT OUT. unfold FREE1_stmt, J_FREE1 in FREE1P.
    unfold err_new_rest_stmt in ENEW. unfold err_set_debug_stmt in EDBG. unfold err_set_error_stmt in ESET.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_RAISE1, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (proj1 (NoDup_cons_iff _ _) NDR) as [NPE _].
    assert (HKE : forall q, mbio_T (e_K en) q -> e_pe en <> q) by (intros q Hq E; apply NPE; rewrite E; apply mbio_T_blocks; exact Hq).
    assert (HLE : ~ e_pe en = ql) by (intros E; apply (DJC ql); [apply in_or_app; right; apply in_or_app; right; left; reflexivity| left; exact E]).
    assert (HXE : forall q, mbio_T KX q -> ~ e_pe en = q) by (intros q Hq E; apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| left; exact E]).
    assert (HYE : forall q, mbio_T KY q -> ~ e_pe en = q) by (intros q Hq E; apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| left; exact E]).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    assert (IDS : forall q, In q (mbio_blocks KX ++ mbio_blocks KY ++ [ql]) \/ q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
    { destruct MBX as [BMX0 MBX0]. destruct MBY as [BMY0 MBY0]. intros q [X|[->|X]].
      - apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBX0 X)|].
        apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBY0 X)|].
        destruct X as [<-|[]]; exact (cown_id _ _ _ _ _ _ OWNL).
      - apply in_map_iff. exists (e_pe en, e_E en, 904). split; [reflexivity| exact INE].
      - apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. chere.
    eapply climpl_seq.
    { eapply ENEW with (lo := e_lo en) (B := e_B en); [exact CST| rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE| exact INCL| exact OWNE| exact ER0]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & -> & LE1 & EL1)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    assert (COM1 : pem_com libenv en st1 LBc Lc f1 m1 off rem rA rB rBig).
    { eapply (com_callEI en) with (EV1 := 0%nat) (dA := 0) (dB := 0) (dBig := 0); [exact COM| exact CST1| exact FRM1| exact FU1| clear; lia| exact GR1| | | | | | | intros b X; exact X| intros q nm X; exact X| exact LE1| exact HKE];
        clear - RA0 RB0 RBIG0; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX FRM1 HXE) as MBX1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY FRM1 HYE) as MBY1.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNL FRM1 HLE) as OWNL1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ql, LB2, 256) CFR1 LBC (proj1 OWNL) HLE ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as LBC1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia. pose proof COM1 as (_ & _ & _ & _ & _ & _ & OWNE1 & _).
    pose proof COM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM1 & _ & RA1 & RB1 & RBIG1 & _).
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 LOC OUT LBC MBX MBY OWNL LE.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply EDBG with (lo := e_lo en) (B := e_B en) (SF := 0x30126) (SN := 0x380d1) (nf := 21) (nn := 9) (line := 790) (fstr := pem_file_str) (nstr := gn_func_str) (fslack := pem_file_slk) (nslack := gn_func_slk);
        [clear - FU FU1 REM; lia| eapply croom_weaken; [exact ROOM1| clear - RA2; lia| clear - RB1; lia| clear - RBIG1; lia]| exact CST1
        | rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE1| exact INCL| exact OWNE1| exact EL1
        | reflexivity| reflexivity| reflexivity| exact pem_file_ro'| exact gn_func_ro| exact pem_file_nonul| exact gn_func_nonul
        | clear; cbn; lia| clear; cbn; lia| clear; lia| clear; cbn; lia| clear; lia| clear; cbn; lia
        | rewrite pem_file_len; reflexivity| rewrite gn_func_len; reflexivity| clear; lia| clear; lia]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2' & RET & FU2 & GR2 & CST2 & FRM2 & (qf & qs & QF & QS & -> & -> & LE2 & EL2)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    assert (COM2 : pem_com libenv en st2 ((qs, QS, 9) :: (qf, QF, 21) :: LBc) ((qs, 9) :: (qf, 21) :: Lc) f2 m2 off (rem - 2) (rA - 2) rB rBig).
    { eapply (com_callEI en) with (EV1 := 2%nat) (dA := 2) (dB := 0) (dBig := 0); [exact COM1| exact CST2| exact FRM2| exact FU2| clear - REM; lia| exact GR2| | | | | | | intros b X; right; right; exact X| intros q nm X; right; right; exact X| exact LE2| exact HKE];
        clear - RA1 RB1 RBIG1 RA2; lia. }
    pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1 FRM2 HXE) as MBX2. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY1 FRM2 HYE) as MBY2.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNL1 FRM2 HLE) as OWNL2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ql, LB2, 256) CFR2 LBC1 (proj1 OWNL1) HLE ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as LBC2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia. pose proof COM2 as (_ & _ & _ & _ & _ & _ & OWNE2 & _).
    pose proof COM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM2 & _ & RA2' & RB2 & RBIG2 & _).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _]. cbn [map blk_id fst] in ND2.
    inversion ND2 as [|z1 k1 NQS ND2']; subst. inversion ND2' as [|z2 k2 NQF _]; subst. cbn [In] in NQS.
    clear MU WM CST1 HP1 MI1 ST1 COM1 FRM2 CFR2 LOC1 OUT1 LBC1 MBX1 MBY1 OWNL1 LE1 EL1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply ESET with (lo := e_lo en) (B := e_B en) (lib := 9) (reason := 108);
        [exact CST2| rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE2| intros b Hb; right; right; exact (INCL _ Hb)| exact OWNE2| exact EL2
        | reflexivity| reflexivity| reflexivity| clear; lia| clear; lia| clear; lia]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (-> & -> & LE3 & EL3)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    assert (COM3 : pem_com libenv en st3 ((qs, QS, 9) :: (qf, QF, 21) :: LBc) ((qs, 9) :: (qf, 21) :: Lc) f3 m3 off (rem - 2) (rA - 2) rB rBig).
    { eapply (com_callEI en) with (EV1 := 0%nat) (dA := 0) (dB := 0) (dBig := 0); [exact COM2| exact CST3| exact FRM3| exact FU3| clear; lia| exact GR3| | | | | | | intros b X; exact X| intros q nm X; exact X| exact LE3| exact HKE];
        clear - RA2' RB2 RBIG2; lia. }
    pose proof FRM3 as (CFR3 & KP3 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2 FRM3 HXE) as MBX3. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2 FRM3 HYE) as MBY3.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNL2 FRM3 HLE) as OWNL3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ql, LB2, 256) CFR3 LBC2 (proj1 OWNL2) HLE ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as LBC3.
    pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    clear MU WM CST2 HP2 MI2 ST2 COM2 FRM3 CFR3 LOC2 OUT2 LBC2 MBX2 MBY2 OWNL2 LE2 EL2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    cprefix. ths. chere.
    (* [comment removed for export] *)
    eapply (FREE1P en st3 ((qs, QS, 9) :: (qf, QF, 21) :: LBc) ((qs, 9) :: (qf, 21) :: Lc) f3 m3 off (rem - 2)%nat (rA - 2) rB rBig [(qs, QS, 9); (qf, QF, 21)]
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l6 l7 (wz (e_flags en)) l11 ta tb ql LB2 hBv dBv bs KX KY methX methY lenX maxX lenY maxY);
      [exact COM3| right; exists 1, 0; split; [exact EL3| cbn; clear; lia]| clear - REM; lia| unfold pem_loc; exact LOC3
      | exact OWNL3| exact LBS| exact LBC3| exact MBX3| exact MBY3| | | | exact CFRESH| | exact EL| | exact OUT3].
    - intros b Hb. destruct Hb as [<-|[<-|Hb]]; [right; right; left; reflexivity| right; right; right; left; reflexivity|].
      destruct (ELB _ Hb) as [X|X]; [left; exact X| right; left; exact X].
    - intros b [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity].
    - apply Forall_cons; [split; [left; reflexivity| cbn; clear; lia]| apply Forall_cons; [split; [right; left; reflexivity| cbn; clear; lia]| apply Forall_nil]].
    - intros b [<-|[<-|[]]] X; cbn [blk_id fst] in X; [apply NQS; right| apply NQF]; apply in_map_iff in X; destruct X as (b' & E & Hb');
        rewrite <- E; apply in_map; exact (PLB _ Hb').
    - cbn [map blk_id fst].
      lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [ql]) ++ qs :: qf :: e_pe en :: mbio_blocks (e_K en)) by (rewrite <- ?app_assoc; reflexivity) end.
      apply nd_insert2; [exact NDT| | | clear - NQS; intros E; apply NQS; left; exact (eq_sym E)].
      + intros X. apply NQS. right. apply IDS. apply in_app_iff in X. destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X].
      + intros X. apply NQF. apply IDS. apply in_app_iff in X. destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X].
  Qed.
End W3.
