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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_rzt.
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
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Lemma wBig_mono : forall a b, 0 <= a <= b -> wBig a <= wBig b.
Proof. intros a b H. unfold wBig. destruct (Z.ltb_spec TIER_A_MAX a); destruct (Z.ltb_spec TIER_A_MAX b); lia. Qed.

Lemma nd_insert1 : forall (l1 l2 : list bptr) x, List.NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> List.NoDup (l1 ++ x :: l2).
Proof.
  intros l1 l2 x ND NX. induction l1 as [|z l1 IH]; cbn [app] in *.
  - constructor; [exact NX| exact ND].
  - inversion ND as [|z' l' NI ND']; subst. constructor.
    + intros X. apply in_app_iff in X. destruct X as [X|X]; [apply NI; apply in_or_app; left; exact X|].
      cbn in X. destruct X as [X|X]; [apply NX; left; exact (eq_sym X)| apply NI; apply in_or_app; right; exact X].
    + apply IH; [exact ND'| intros X; apply NX; right; exact X].
Qed.

Lemma nodup_blk_eq : forall (LB : list block) (b b' : block), List.NoDup (map blk_id LB) -> In b LB -> In b' LB -> blk_id b = blk_id b' -> b = b'.
Proof.
  intros LB b b' ND Hb Hb' E. induction LB as [|x LB IH]; [destruct Hb|]. cbn [map] in ND. inversion ND as [|y l NI ND']; subst.
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb']; [reflexivity| exfalso; apply NI; rewrite E; apply in_map; exact Hb'| exfalso; apply NI; rewrite <- E; apply in_map; exact Hb| exact (IH ND' Hb Hb')].
Qed.

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
  Local Notation err_segI := (pem_err_munch errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where).

  (* [comment removed for export] *)
  Lemma er0_call : forall en (m m1 : mem) T1 SP s LBc Lc s1 LB1 L1,
    errst_at_rest (e_E en) [] m -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> In (e_pe en, e_E en, 904) LBc -> ~ T1 (e_pe en) -> errst_at_rest (e_E en) [] m1.
  Proof.
    intros en m m1 T1 SP s LBc Lc s1 LB1 L1 ER (CFR & _) INE NT. eapply errst_rest_agree; [exact ER|]. eapply agree_on_mono; [exact CFR|]. cbv beta.
    intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R|(b & [] & _)]. right; left. exists (e_pe en, e_E en, 904). split; [exact INE|]. split; [exact NT|]. unfold blk_addr, blk_size; cbn [fst snd]. exact R.
  Qed.
  Lemma er0_seg : forall (W : list (Z * Z)) en m m' s LBc LB0 L sp tp lo hi B EX,
    errst_at_rest (e_E en) [] m -> munch W m m' -> wmono usegs m m' -> cstate s LBc LB0 L m sp tp lo B ->
    In (e_pe en, e_E en, 904) LBc -> Forall (wfree LBc lo hi EX) W -> EX (e_pe en) -> errst_at_rest (e_E en) [] m'.
  Proof.
    intros W en m m' s LBc LB0 L sp tp lo hi B EX ER MU WM CST INE HW HXE.
    eapply errst_rest_agree; [exact ER|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. cbv beta. intros a Ha.
    eapply wfree_outside; [exact CST| exact HW|]. right. destruct (errst_fp_where _ _ _ Ha) as [R|(b & [] & _)].
    exists (e_pe en, e_E en, 904). split; [exact INE|]. split; [exact HXE|]. unfold blk_addr, blk_size; cbn [fst snd]. exact R.
  Qed.

  Lemma mb_call : forall (m m1 : mem) T1 SP s LBc Lc s1 LB1 L1 K BI meth len max off,
    mbio_rep m LBc Lc K BI meth len max off -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> (forall q, mbio_T K q -> ~ T1 q) -> mbio_rep m1 LB1 L1 K BI meth len max off.
  Proof. intros m m1 T1 SP s LBc Lc s1 LB1 L1 K BI meth len max off [BM MB] FR HK. exists BM. exact (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MB FR HK). Qed.
  Lemma mb_seg : forall Wseg (m m' : mem) s LBc LB0 Lc sp tp lo hi B K EX BI meth len max off,
    mbio_rep m LBc Lc K BI meth len max off -> cstate s LBc LB0 Lc m sp tp lo B -> munch Wseg m m' -> wmono usegs m m' -> Forall (wfree LBc lo hi EX) Wseg ->
    (forall q, mbio_T K q -> EX q) -> mbio_rep m' LBc Lc K BI meth len max off.
  Proof. intros Wseg m m' s LBc LB0 Lc sp tp lo hi B K EX BI meth len max off [BM MB] CST MU WM HW HX. exists BM. eapply mbx_seg; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem DEC_proof :
    bio_ctrl_info_stmt -> pem_malloc_stmt -> pem_malloc0_stmt -> bio_read_stmt ->
    END_stmt libenv errst_at_rest errst_live -> OUTFREE_stmt libenv errst_at_rest errst_live -> DEC_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BCI PM PM0 BRD ENDP OUTP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 l11 ta
           qc qn ctxv namev nn hBv dBv BMY dlen bn KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM ER0 REM RA2 RB2 RBIG2 LXY LOC OWNC OWNN NN LBN NMC NUL MBX MBY DLEN ELB CFRESH EL NDT OUT.
    unfold END_stmt, J_END in ENDP. unfold OUTFREE_stmt, J_OUTFREE in OUTP.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_DEC, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as NDLB. pose proof (proj1 OWNN) as INN0.
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (proj1 (NoDup_cons_iff _ _) NDR) as [NPE _].
    (* [comment removed for export] *)
    assert (LX31 : 0 <= lenX < 2 ^ 31 - 1).
    { destruct MBX as (BMX0 & BB & RP & fl & rrw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & (rmaxw & _ & _ & _ & _ & O1 & O2 & O3 & _)). clear - O1 O2 O3. lia. }
    assert (LY31 : lenY < 2 ^ 31 - 1).
    { destruct MBY as (BB & RP & fl & rrw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & (rmaxw & _ & _ & _ & _ & O1 & O2 & O3 & _)). clear - O1 O2 O3. lia. }
    (* [comment removed for export] *)
    assert (HXE : forall q, mbio_T KX q -> ~ e_pe en = q) by (intros q Hq E; apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| left; exact E]).
    assert (HYE : forall q, mbio_T KY q -> ~ e_pe en = q) by (intros q Hq E; apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| left; exact E]).
    assert (HXK : forall q, mbio_T (e_K en) q -> ~ mbio_T KX q) by (intros q Hq X; apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact X| right; apply mbio_T_blocks; exact Hq]).
    assert (HYK : forall q, mbio_T (e_K en) q -> ~ mbio_T KY q) by (intros q Hq X; apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact X| right; apply mbio_T_blocks; exact Hq]).
    assert (HXL : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ mbio_T KX q).
    { intros q [Hq|Hq] X; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. apply in_or_app; left. apply mbio_T_blocks. exact X.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). apply in_or_app; left. apply mbio_T_blocks. exact X. }
    assert (HYL : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ mbio_T KY q).
    { intros q [Hq|Hq] X; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. apply in_or_app; right; apply in_or_app; left. apply mbio_T_blocks. exact X.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). apply in_or_app; right; apply in_or_app; left. apply mbio_T_blocks. exact X. }
    pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|z1 k1 NQ1 _]; subst. cbn [In] in NQ1.
    assert (HXC : ~ mbio_T KX qc) by (intros X; apply (DJX qc); [apply mbio_T_blocks; exact X| apply in_or_app; right; left; reflexivity]).
    assert (HXN : ~ mbio_T KX qn) by (intros X; apply (DJX qn); [apply mbio_T_blocks; exact X| apply in_or_app; right; right; left; reflexivity]).
    assert (HYC : ~ mbio_T KY qc) by (intros X; apply (DJY qc); [apply mbio_T_blocks; exact X| left; reflexivity]).
    assert (HYN : ~ mbio_T KY qn) by (intros X; apply (DJY qn); [apply mbio_T_blocks; exact X| right; left; reflexivity]).
    assert (HXY : forall q, mbio_T KY q -> ~ mbio_T KX q) by (intros q Hq X; apply (DJX q); [apply mbio_T_blocks; exact X| apply in_or_app; left; apply mbio_T_blocks; exact Hq]).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    (* [comment removed for export] *)
    assert (IDS : forall q, In q (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) \/ q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
    { destruct MBX as [BMX0 MBX0]. intros q [X|[->|X]].
      - apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBX0 X)|].
        apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBY X)|].
        destruct X as [<-|[<-|[]]]; [exact (cown_id _ _ _ _ _ _ OWNC)| exact (cown_id _ _ _ _ _ _ OWNN)].
      - apply in_map_iff. exists (e_pe en, e_E en, 904). split; [reflexivity| exact INE].
      - apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BCI with (lo := e_lo en) (B := e_B en); [exact CST| rewrite unsigned_lit by lia; unfold BCTRL_STACK; clear - SLO; lia| exact MBX| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & -> & -> & MBX1)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    replace (lenX - 0) with lenX in * by (clear; lia).
    assert (COM1 : pem_com libenv en st1 LBc Lc f1 m1 off rem rA rB rBig).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear; lia| exact GR1| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X]; clear - RA0 RB0 RBIG0; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY FRM1 ltac:(intros q _ X; exact X)) as MBY1.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC FRM1 ltac:(intros X; exact X)) as OWNC1. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN FRM1 ltac:(intros X; exact X)) as OWNN1.
    pose proof (er0_call en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE ltac:(intros X; exact X)) as ER1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    pose proof COM1 as (_ & _ & _ & _ & _ & _ & OWNE1 & _ & _ & _ & _ & ROOM1 & _ & RA1 & RB1 & RBIG1 & _).
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 LOC OUT NMC MBX MBY OWNC OWNN ER0 HP1.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    assert (SGS : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z) by (intros z Hz; rewrite zb_signed; rewrite unsigned_lit by lia; destruct (Z.ltb_spec z (2 ^ 63)); lia).
    cprefix. ths. rewrite (t_sextw_small lenX) by (clear - LX31; lia). ths.
    replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 lenX) + 1)) with (lenX + 1) by (rewrite unsigned_lit by (clear - LX31; lia); symmetry; apply swrap32_small; clear - LX31; lia).
    ths. if_cases K; try unfold c_lts in K; zify_cond K; [exfalso; rewrite !SGS in K by (clear - LX31; lia); clear - K; lia|]. clear K. ths. ths. ths. ths. chere.
    pose proof (w_bounds (lenX + 1) ltac:(clear - LX31; lia)) as (WA1 & WB1 & WAB1 & WBIG1).
    eapply climpl_seq.
    { eapply PM with (n := lenX + 1) (flags := e_flags en) (lo := e_lo en) (B := e_B en);
        [clear - FU FU1 REM; lia| eapply croom_weaken; [exact ROOM1| clear - RA2 WA1; lia| clear - RB2 WB1; lia| clear - RBIG2 DLEN; pose proof (w_bounds lenY ltac:(clear - DLEN; lia)); lia]
        | clear - LX31; lia| clear - FLR; lia| exact CST1| rewrite unsigned_lit by lia; unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (qh & HD & hjunk & -> & -> & -> & RNH & HDC)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    pose proof (rw_cells_CB_length _ _ _ _ _ HDC) as LHJ.
    assert (COM2 : pem_com libenv en st2 ((qh, HD, lenX + 1) :: LBc) ((qh, lenX + 1) :: Lc) f2 m2 off (rem - 1) (rA - wA (lenX + 1)) (rB - wB (lenX + 1)) (rBig - wBig (lenX + 1))).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM1| exact CST2| exact FRM2| unfold e_PL; clear; lia| exact FU2| clear - REM; lia| exact GR2| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
        clear - RA1 RB1 RBIG1 RA2 RB2 RBIG2 WA1 WB1 WAB1 WBIG1 LX31 DLEN; pose proof (w_bounds lenY ltac:(clear - DLEN; lia)); lia. }
    pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1 FRM2 ltac:(intros q _ X; exact X)) as MBX2.
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY1 FRM2 ltac:(intros q _ X; exact X)) as MBY2.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC1 FRM2 ltac:(intros X; exact X)) as OWNC2. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN1 FRM2 ltac:(intros X; exact X)) as OWNN2.
    pose proof (er0_call en _ _ _ _ _ _ _ _ _ _ ER1 FRM2 INE ltac:(intros X; exact X)) as ER2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR2 NMC1 (proj1 OWNN1) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    pose proof COM2 as (_ & _ & _ & _ & _ & _ & OWNE2 & _ & _ & _ & _ & ROOM2 & _ & RA2' & RB2' & RBIG2' & _).
    pose proof RNH as (HD0 & _ & _ & HDC' & HDIMG). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in HDC'.
    (* [comment removed for export] *)
    assert (FRH : forall q A' n', In (q, A', n') LBc -> q <> qh) by (intros q A' n' Hq; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 Hq)).
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [_ NDL2]. cbn [map fst] in NDL2. inversion NDL2 as [|z2 k2 NQH _]; subst.
    assert (OWNH : cown ((qh, HD, lenX + 1) :: LBc) ((qh, lenX + 1) :: Lc) qh HD (lenX + 1) (lenX + 1)) by (split; left; reflexivity).
    assert (SUB : forall x, In x (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) -> In x (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn; qh])).
    { intros xq X. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
      cbn in X |- *. clear - X. tauto. }
    assert (NQH' : ~ In qh (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn] ++ e_pe en :: mbio_blocks (e_K en))).
    { intros X. assert (Y : In qh (map blk_id LBc)).
      { apply IDS. apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; right; apply in_or_app; left; exact X|].
        cbn in X. destruct X as [X|[X|[X|X]]]; [left; apply in_or_app; right; apply in_or_app; right; left; exact X| left; apply in_or_app; right; apply in_or_app; right; right; left; exact X| right; left; exact (eq_sym X)| right; right; exact X]. }
      apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hq). cbn in E. exact (FRH _ _ _ Hq E). }
    clear MU WM CST1 MI1 ST1 COM1 FRM2 CFR2 LOC1 OUT1 NMC1 MBX1 MBY1 OWNC1 OWNN1 ER1 ROOM1 RA1 RB1 RBIG1.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + 16, bv_unsigned (e_sp en) + 24)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    hide NMC2. hide HDC.
    cprefix. ths. rewrite (t_sx32_small dlen) by (clear - DLEN LY31; lia). ths. ths. ths. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2' end.
    lazymatch goal with H : stk usegs m2' _ _ |- _ => rename H into ST2' end. lazymatch goal with H : mem_inv usegs m2' |- _ => rename H into MI2' end.
    lazymatch goal with H : munch _ m2 m2' |- _ => rename H into MU2' end. lazymatch goal with H : wmono usegs m2 m2' |- _ => rename H into WM2' end.
    chere.
    assert (HWo2 : Forall (wfree ((qh, HD, lenX + 1) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True)) [(bv_unsigned (e_sp en) + 16, bv_unsigned (e_sp en) + 24)])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    assert (COM2' : pem_com libenv en st2 ((qh, HD, lenX + 1) :: LBc) ((qh, lenX + 1) :: Lc) f2 m2' off (rem - 1) (rA - wA (lenX + 1)) (rB - wB (lenX + 1)) (rBig - wBig (lenX + 1))).
    { eapply (com_segI en) with (EX := fun _ => True); [exact COM2| exact MU2'| exact WM2'| exact MI2'| exact ST2'| exact HWo2| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
    pose proof (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2 CST2 MU2' WM2' HWo2 ltac:(intros q _; exact I)) as MBX2'.
    pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2 CST2 MU2' WM2' HWo2 ltac:(intros q _; exact I)) as MBY2'.
    pose proof (er0_seg _ en _ _ _ _ _ _ _ _ _ _ _ _ ER2 MU2' WM2' CST2 (proj1 OWNE2) HWo2 I) as ER2'.
    unfold hideP in NMC2, HDC.
    assert (NMC2' : rw_cells usegs m2' namev [CB (Z.to_nat nn) bn]).
    { eapply rw_cells_transport; [exact NMC2| exact MU2'| exact WM2'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - RN1 RN2 LO SLO NN. lia. }
    assert (HDC2' : rw_cells usegs m2' HD [CB (Z.to_nat (lenX + 1)) hjunk]).
    { eapply rw_cells_transport; [exact HDC| exact MU2'| exact WM2'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - HD0 HDC' LO SLO LX31. lia. }
    pose proof COM2' as (CST2' & _). clear CST2 MI2' ST2'.
    destruct (Z.eq_dec dlen 0) as [DZ|DNZ].
    - (* [comment removed for export] *)
      subst dlen.
      unfold pem_malloc0_stmt in PM0.
      eapply climpl_seq.
      { eapply PM0 with (flags := e_flags en) (lo := e_lo en) (B := e_B en); [clear - FLR; lia| exact CST2'| rewrite unsigned_lit by lia; unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
      cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (-> & -> & ->)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
      assert (COM3 : pem_com libenv en st3 ((qh, HD, lenX + 1) :: LBc) ((qh, lenX + 1) :: Lc) f3 m3 off (rem - 1) (rA - wA (lenX + 1)) (rB - wB (lenX + 1)) (rBig - wBig (lenX + 1))).
      { eapply (com_callI en) with (T1 := fun _ => False); [exact COM2'| exact CST3| exact FRM3| unfold e_PL; clear; lia| exact FU3| clear; lia| exact GR3| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
          clear - RA2' RB2' RBIG2'; lia. }
      pose proof FRM3 as (CFR3 & KP3 & _).
      pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2' FRM3 ltac:(intros q _ X; exact X)) as MBX3.
      pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2' FRM3 ltac:(intros q _ X; exact X)) as MBY3.
      pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC2 FRM3 ltac:(intros X; exact X)) as OWNC3. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN2 FRM3 ltac:(intros X; exact X)) as OWNN3.
      pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNH FRM3 ltac:(intros X; exact X)) as OWNH3.
      pose proof (er0_call en _ _ _ _ _ _ _ _ _ _ ER2' FRM3 (proj1 OWNE2) ltac:(intros X; exact X)) as ER3.
      pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
      pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR3 NMC2' (proj1 OWNN2) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC3.
      pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qh, HD, lenX + 1) CFR3 HDC2' (proj1 OWNH) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - LX31; lia)) as HDC3.
      pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
      pose proof COM3 as (_ & _ & _ & _ & _ & _ & OWNE3 & _).
      clear CST2' COM2' FRM3 CFR3 LOC2 OUT2 NMC2' HDC2' MBX2' MBY2' OWNC2 OWNN2 ER2'.
      pose proof (munch_refl [(bv_unsigned (e_sp en) + 8, bv_unsigned (e_sp en) + 16)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      hide NMC3. hide HDC3.
      cprefix. ths. ths.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3' end.
      lazymatch goal with H : stk usegs m3' _ _ |- _ => rename H into ST3' end. lazymatch goal with H : mem_inv usegs m3' |- _ => rename H into MI3' end.
      lazymatch goal with H : munch _ m3 m3' |- _ => rename H into MU3' end. lazymatch goal with H : wmono usegs m3 m3' |- _ => rename H into WM3' end.
      ths. ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - HD0 HDC' LO SLO SPR; lia); clear - K HD0; lia|]. clear K.
      ths. try th_if_lit.
      chere.
      assert (HWo3 : Forall (wfree ((qh, HD, lenX + 1) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True)) [(bv_unsigned (e_sp en) + 8, bv_unsigned (e_sp en) + 16)])
        by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
      assert (COM3' : pem_com libenv en st3 ((qh, HD, lenX + 1) :: LBc) ((qh, lenX + 1) :: Lc) f3 m3' off (rem - 1) (rA - wA (lenX + 1)) (rB - wB (lenX + 1)) (rBig - wBig (lenX + 1))).
      { eapply (com_segI en) with (EX := fun _ => True); [exact COM3| exact MU3'| exact WM3'| exact MI3'| exact ST3'| exact HWo3| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
      pose proof (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX3 CST3 MU3' WM3' HWo3 ltac:(intros q _; exact I)) as [BMX MBX3'].
      pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY3 CST3 MU3' WM3' HWo3 ltac:(intros q _; exact I)) as MBY3'.
      pose proof (er0_seg _ en _ _ _ _ _ _ _ _ _ _ _ _ ER3 MU3' WM3' CST3 (proj1 OWNE3) HWo3 I) as ER3'.
      unfold hideP in NMC3, HDC3.
      assert (NMC3' : rw_cells usegs m3' namev [CB (Z.to_nat nn) bn]).
      { eapply rw_cells_transport; [exact NMC3| exact MU3'| exact WM3'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - RN1 RN2 LO SLO NN. lia. }
      assert (HDC3' : rw_cells usegs m3' HD [CB (Z.to_nat (lenX + 1)) hjunk]).
      { eapply rw_cells_transport; [exact HDC3| exact MU3'| exact WM3'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - HD0 HDC' LO SLO LX31. lia. }
      lazymatch goal with H : rw_cells usegs m3' (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC3' end.
      lazymatch goal with H : rw_cells usegs m3' (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT3' end.
      eapply (OUTP en st3 ((qh, HD, lenX + 1) :: LBc) ((qh, lenX + 1) :: Lc) f3 m3' off (rem - 1)%nat (rA - wA (lenX + 1)) (rB - wB (lenX + 1)) (rBig - wBig (lenX + 1)) []
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ qc qn qh ctxv namev nn HD (lenX + 1) hBv dBv hjunk KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) (wz 0));
        [exact COM3'| left; split; [reflexivity| exact ER3']| clear - REM; lia| unfold pem_loc; exact LOC3'| exact OWNC3| exact OWNN3| clear - NN; lia| exact OWNH3| clear - LX31; lia
        | rewrite LHJ; reflexivity| exact HDC3'| exact MBX3'| exact MBY3'| | intros b []| apply Forall_nil| | intros b []| | | exact OUT3'].
      + intros b Hb. destruct Hb as [<-|Hb]; [right; left; apply in_or_app; right; apply in_or_app; right; right; right; left; reflexivity|].
        destruct (ELB _ Hb) as [X|X]; [left; exact X| right; left; exact (SUB _ X)].
      + intros [[q A'] n'] Hb X. apply in_app_iff in X. destruct X as [X|X]; [apply (CFRESH _ Hb); apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [apply (CFRESH _ Hb); apply in_or_app; right; apply in_or_app; left; exact X|].
        cbn in X. destruct X as [X|[X|[X|[]]]]; [apply (CFRESH _ Hb); apply in_or_app; right; apply in_or_app; right; left; exact X| apply (CFRESH _ Hb); apply in_or_app; right; apply in_or_app; right; right; left; exact X|].
        exact (FRH _ _ _ (PLB _ Hb) (eq_sym X)).
      + intros q nm Hq X. apply in_app_iff in X. destruct X as [X|X]; [apply (EL _ _ Hq); apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [apply (EL _ _ Hq); apply in_or_app; right; apply in_or_app; left; exact X|].
        cbn in X. destruct X as [X|[X|[X|[]]]]; [apply (EL _ _ Hq); apply in_or_app; right; apply in_or_app; right; left; exact X| apply (EL _ _ Hq); apply in_or_app; right; apply in_or_app; right; right; left; exact X|].
        apply NQH. rewrite X. apply in_map_iff. exists (q, nm). split; [reflexivity| exact (PLC _ _ Hq)].
      + cbn [map app]. lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) ++ qh :: e_pe en :: mbio_blocks (e_K en)) by (rewrite <- ?app_assoc; reflexivity) end.
        apply nd_insert1; [exact NDT| intros X; apply NQH'; rewrite <- ?app_assoc in X; exact X].
    - (* [comment removed for export] *)
      pose proof (w_bounds dlen ltac:(clear - DLEN DNZ; lia)) as (WA2 & WB2' & WAB2 & WBIG2).
      pose proof (wBig_mono dlen lenY ltac:(clear - DLEN DNZ; lia)) as WBM.
      eapply climpl_seq.
      { eapply PM with (n := dlen) (flags := e_flags en) (lo := e_lo en) (B := e_B en);
          [clear - FU FU1 FU2 REM; lia| eapply croom_weaken; [exact ROOM2| clear - RA2 WA1 WA2 WAB1 WAB2 WB1 WB2'; lia| clear - RB2 WB1 WB2' WAB1 WAB2 WA1 WA2; lia| clear - RBIG2 WBM WBIG1 WBIG2 DLEN; lia]
          | clear - DLEN DNZ LY31; lia| clear - FLR; lia| exact CST2'| rewrite unsigned_lit by lia; unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
      cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (qd & DT & djunk & -> & -> & -> & RND & DTC)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
      pose proof (rw_cells_CB_length _ _ _ _ _ DTC) as LDJ.
      assert (COM3 : pem_com libenv en st3 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f3 m3 off (rem - 2)
                       (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)).
      { eapply (com_callI en) with (T1 := fun _ => False); [exact COM2'| exact CST3| exact FRM3| unfold e_PL; clear; lia| exact FU3| clear - REM; lia| exact GR3| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
          clear - RA2' RB2' RBIG2' RA2 RB2 RBIG2 WA1 WA2 WAB1 WAB2 WB1 WB2' WBIG1 WBIG2 WBM DLEN; lia. }
      pose proof FRM3 as (CFR3 & KP3 & _).
      pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2' FRM3 ltac:(intros q _ X; exact X)) as MBX3.
      pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2' FRM3 ltac:(intros q _ X; exact X)) as MBY3.
      pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC2 FRM3 ltac:(intros X; exact X)) as OWNC3. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN2 FRM3 ltac:(intros X; exact X)) as OWNN3.
      pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNH FRM3 ltac:(intros X; exact X)) as OWNH3.
      pose proof (er0_call en _ _ _ _ _ _ _ _ _ _ ER2' FRM3 (proj1 OWNE2) ltac:(intros X; exact X)) as ER3.
      pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
      pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR3 NMC2' (proj1 OWNN2) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC3.
      pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qh, HD, lenX + 1) CFR3 HDC2' (proj1 OWNH) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - LX31; lia)) as HDC3.
      pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
      pose proof COM3 as (_ & _ & _ & _ & _ & _ & OWNE3 & _ & _ & _ & _ & ROOM3 & _ & RA3 & RB3 & RBIG3 & _).
      pose proof RND as (DT0 & _ & _ & DTC' & DTIMG). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in DTC'.
      assert (FRD : forall q A' n', In (q, A', n') ((qh, HD, lenX + 1) :: LBc) -> q <> qd) by (intros q A' n' Hq; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 Hq)).
      destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [_ NDL3]. cbn [map fst] in NDL3. inversion NDL3 as [|z3 k3 NQD _]; subst. cbn [In] in NQD.
      assert (OWND : cown ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) qd DT dlen dlen) by (split; left; reflexivity).
      clear CST2' COM2' FRM3 CFR3 LOC2 OUT2 NMC2' HDC2' MBX2' MBY2' OWNC2 OWNN2 ER2' ROOM2 RA2' RB2' RBIG2'.
      (* [comment removed for export] *)
      assert (NKXH : ~ mbio_T KX qh) by (intros X; apply NQH'; apply in_or_app; left; apply mbio_T_blocks; exact X).
      assert (NKYH : ~ mbio_T KY qh) by (intros X; apply NQH'; apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact X).
      assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ (mbio_T KX q \/ q = qh)).
      { intros q Hq _ [X| ->]; [exact (HXL _ Hq X)|]. destruct Hq as [Hq|Hq].
        - apply in_map_iff in Hq. destruct Hq as ([[q A'] n'] & E & Hb). cbn in E. exact (FRH _ _ _ (PLB _ Hb) E).
        - apply NQH. apply in_map_iff in Hq. destruct Hq as ([q nm] & E & Hq). cbn in E. subst q. apply in_map_iff. exists (qh, nm). split; [reflexivity| exact (PLC _ _ Hq)]. }
      assert (HK1 : forall q, mbio_T (e_K en) q -> ~ (mbio_T KX q \/ q = qh)).
      { intros q Hq [X| ->]; [exact (HXK _ Hq X)|]. pose proof (EK _ Hq) as Y. apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hb). cbn in E. exact (FRH _ _ _ (PLB _ Hb) E). }
      assert (HE1 : ~ (mbio_T KX (e_pe en) \/ e_pe en = qh)) by (intros [X|E]; [exact (HXE _ X eq_refl)| exact (FRH _ _ _ INE E)]).
      assert (HY1 : forall q, mbio_T KY q -> ~ (mbio_T KX q \/ q = qh)) by (intros q Hq [X| ->]; [exact (HXY _ Hq X)| exact (NKYH Hq)]).
      assert (HC1 : ~ (mbio_T KX qc \/ qc = qh)) by (intros [X|E]; [exact (HXC X)| apply NQH'; apply in_or_app; right; apply in_or_app; right; left; exact E]).
      assert (HN1 : ~ (mbio_T KX qn \/ qn = qh)) by (intros [X|E]; [exact (HXN X)| apply NQH'; apply in_or_app; right; apply in_or_app; right; right; left; exact E]).
      assert (HD1 : ~ (mbio_T KX qd \/ qd = qh)).
      { intros [X|E]; [| exact (FRD _ _ _ (or_introl eq_refl) (eq_sym E))].
        assert (Y : In qd (map blk_id LBc)) by (apply IDS; left; apply in_or_app; left; apply mbio_T_blocks; exact X).
        apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hq). cbn in E. exact (FRD _ _ _ (or_intror Hq) E). }
      (* [comment removed for export] *)
      assert (JOIN : forall f4 st4 m4 (hj : list byte) (xra' u0 u1 u2 b0 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
        pem_com libenv en st4 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f4 m4 off (rem - 2)
                (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen) ->
        errst_at_rest (e_E en) [] m4 ->
        (exists BMX, mbio_repx m4 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) KX hBv BMX (wz lenX) methX lenX maxX lenX) ->
        mbio_repx m4 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) KY dBv BMY (wz dlen) methY lenY maxY 0 ->
        rw_cells usegs m4 (bv_unsigned (e_sp en) + -208)
          [C8 l0; C8 l1; C8 (wz namev); C8 l3; C8 l4; C8 l5; C8 (wz (bv_unsigned (e_sp en) + 8)); C8 (wz (bv_unsigned (e_sp en) + 16)); C8 l8; C8 l9; C8 (wz (e_flags en)); C8 l11; C4 ta; C4 (wz dlen)] ->
        rw_cells usegs m4 (bv_unsigned (e_sp en)) [C8 (wz 0); C8 (wz DT); C8 (wz HD); C8 (wz 0)] ->
        rw_cells usegs m4 namev [CB (Z.to_nat nn) bn] -> length hj = Z.to_nat (lenX + 1) -> rw_cells usegs m4 HD [CB (Z.to_nat (lenX + 1)) hj] ->
        rw_cells usegs m4 DT [CB (Z.to_nat dlen) djunk] ->
        climpl f4 ((qd, dlen) :: (qh, lenX + 1) :: Lc) st4
          (MS (mkR xra' (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) u0 u1 u2 (e_sp en) (wz (e_flags en)) b0 (wz HD) b2 b3 b4 b5 b6 b7
                   (wz (bv_unsigned (e_sp en) + 16)) (wz lenX) s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (bv_unsigned (e_sp en) + 24)) (wz ctxv) (wz dBv) s11 u3 u4 u5 u6)
              (e_F en) (wz 0x1886fc) (e_fc en) None m4 (seg_rom usegs))
          (pem_post libenv errst_live en)).
      { intros f4 st4 m4 hj xra' u0 u1 u2 b0 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 COM4 ER4 [BMX MBX4] MBY4 LOC4 OUT4 NMC4 LHJ4 HDC4 DTC4.
        pose proof COM4 as (CST4 & _ & _ & _ & _ & _ & OWNE4 & _ & _ & _ & _ & ROOM4 & _ & RA4 & RB4 & RBIG4 & _).
        pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _). unfold e_PL in *. rewrite unsigned_lit in ST4 by (clear - SPR SLO LO GLO; lia).
        (* [comment removed for export] *)
        assert (HT2 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ (mbio_T KY q \/ q = qd)).
        { intros q Hq _ [X| ->]; [exact (HYL _ Hq X)|]. destruct Hq as [Hq|Hq].
          - apply in_map_iff in Hq. destruct Hq as ([[q A'] n'] & E & Hb). cbn in E. exact (FRD _ _ _ (or_intror (PLB _ Hb)) E).
          - apply in_map_iff in Hq. destruct Hq as ([q nm] & E & Hq). cbn in E. subst q. apply NQD. right. apply in_map_iff. exists (qd, nm). split; [reflexivity| exact (PLC _ _ Hq)]. }
        assert (HK2 : forall q, mbio_T (e_K en) q -> ~ (mbio_T KY q \/ q = qd)).
        { intros q Hq [X| ->]; [exact (HYK _ Hq X)|]. pose proof (EK _ Hq) as Y. apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hb). cbn in E. exact (FRD _ _ _ (or_intror (PLB _ Hb)) E). }
        assert (HE2 : ~ (mbio_T KY (e_pe en) \/ e_pe en = qd)) by (intros [X|E]; [exact (HYE _ X eq_refl)| exact (FRD _ _ _ (or_intror INE) E)]).
        assert (HX2 : forall q, mbio_T KX q -> ~ (mbio_T KY q \/ q = qd)).
        { intros q Hq [X| ->]; [exact (HXY _ X Hq)|].
          assert (Y : In qd (map blk_id LBc)) by (apply IDS; left; apply in_or_app; left; apply mbio_T_blocks; exact Hq).
          apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hb). cbn in E. exact (FRD _ _ _ (or_intror Hb) E). }
        assert (HC2 : ~ (mbio_T KY qc \/ qc = qd)).
        { intros [X|E]; [exact (HYC X)|]. assert (Y : In qc (map blk_id LBc)) by (apply IDS; left; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
          apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E2 & Hb). cbn in E2. exact (FRD _ _ _ (or_intror Hb) (eq_trans E2 E)). }
        assert (HN2 : ~ (mbio_T KY qn \/ qn = qd)).
        { intros [X|E]; [exact (HYN X)|]. assert (Y : In qn (map blk_id LBc)) by (apply IDS; left; apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
          apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E2 & Hb). cbn in E2. exact (FRD _ _ _ (or_intror Hb) (eq_trans E2 E)). }
        assert (HH2 : ~ (mbio_T KY qh \/ qh = qd)) by (intros [X|E]; [exact (NKYH X)| exact (FRD _ _ _ (or_introl eq_refl) E)]).
        assert (NKYD : ~ mbio_T KY qd).
        { intros X. assert (Y : In qd (map blk_id LBc)) by (apply IDS; left; apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact X).
          apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hb). cbn in E. exact (FRD _ _ _ (or_intror Hb) E). }
        (* [comment removed for export] *)
        destruct (rw_cells_CB_split_at usegs m4 HD (Z.to_nat (lenX + 1)) hj (Z.to_nat lenX) ltac:(clear - LX31; lia) HDC4) as [HDa HDb].
        replace (HD + Z.of_nat (Z.to_nat lenX)) with (HD + lenX) in HDb by (clear - LX31; lia).
        replace (Z.to_nat (lenX + 1) - Z.to_nat lenX)%nat with 1%nat in HDb by (clear - LX31; lia).
        pose proof (rw_cells_CB_length _ _ _ _ _ HDb) as LT1.
        destruct (skipn (Z.to_nat lenX) hj) as [|hb [|hb' tl']] eqn:EH; [cbn in LT1; discriminate| | cbn in LT1; discriminate].
        eapply (th_cells_congr _ _ _ _ [C1 hb]) in HDb; [| reflexivity| reflexivity| cbn; repeat split; auto].
        pose proof (munch_refl [(HD + lenX, HD + lenX + 1)]%Z m4) as MU. pose proof (wmono_refl usegs m4) as WM.
        pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 (proj1 OWNN3) (proj1 OWNH3) ltac:(intros E; apply NQH'; apply in_or_app; right; apply in_or_app; right; right; left; exact E)) as APNH.
        pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 (proj1 OWND) (proj1 OWNH3) ltac:(intros E; exact (FRD _ _ _ (or_introl eq_refl) (eq_sym E)))) as APDH.
        unfold blk_addr, blk_size in APNH, APDH. cbn [fst snd] in APNH, APDH.
        pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST4 (proj1 OWND)) as (RD1 & _ & _ & RD2 & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RD2.
        clear HDC4. hide NMC4. hide DTC4. hide HDa.
        cprefix. ths. ths. ths. ths.
        rewrite ?v_sltu_b2z, ?v_sltiu_b2z. rewrite ?(unsigned_lit 0), ?(unsigned_lit HD), ?(unsigned_lit (HD + lenX)) by (clear - HD0 HDC' LO SLO SPR LX31; lia). try change (bv_wrap 64 1) with 1.
        replace (0 <? HD) with true by (symmetry; apply Z.ltb_lt; clear - HD0; lia). replace (HD + lenX <? 1) with false by (symmetry; apply Z.ltb_ge; clear - HD0 LX31; lia). cbn [Z.b2z]. th_if_lit.
        ths. ths. ths. ths. ths.
        rewrite ?v_sltu_b2z, ?v_slti_b2z. rewrite ?(unsigned_lit HD), ?(unsigned_lit lenX), ?(unsigned_lit (HD + lenX)) by (clear - HD0 HDC' LO SLO SPR LX31; lia). rewrite (zb_lxor_sign lenX) by (clear - LX31; lia). rewrite (Z.mod_small (lenX + 2 ^ 63)) by (clear - LX31; lia).
        replace (HD + lenX <? HD) with false by (symmetry; apply Z.ltb_ge; clear - LX31; lia). replace (lenX + 2 ^ 63 <? 0 + 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; clear - LX31; lia). cbn [Z.b2z]. th_if_lit.
        ths. ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - HD0 HDC' LO SLO SPR; lia); clear - K HD0; lia|]. clear K. ths.
        remember (HD + lenX) as HL eqn:EHL.
        ths. ths. ths. rewrite (t_sx32_small dlen) by (clear - DLEN LY31; lia). ths.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4' end.
        lazymatch goal with H : stk usegs m4' _ _ |- _ => rename H into ST4' end. lazymatch goal with H : mem_inv usegs m4' |- _ => rename H into MI4' end.
        lazymatch goal with H : munch _ m4 m4' |- _ => rename H into MU4' end. lazymatch goal with H : wmono usegs m4 m4' |- _ => rename H into WM4' end.
        lazymatch goal with H : rw_cells usegs m4' HL _ |- _ => rename H into HDz end.
        chere.
        assert (HWo4 : Forall (wfree ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun q => q <> qh)) [(HL, HL + 1)]).
        { apply Forall_cons; [| apply Forall_nil]. right. exists (qh, HD, lenX + 1). split; [right; left; reflexivity|]. split; [intros X; apply X; reflexivity|].
          unfold blk_addr, blk_size; cbn [fst snd]. clear - EHL LX31; lia. }
        assert (COM4' : pem_com libenv en st4 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f4 m4' off (rem - 2)
                          (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)).
        { eapply (com_segI en) with (EX := fun q => q <> qh); [exact COM4| exact MU4'| exact WM4'| exact MI4'| exact ST4'| exact HWo4| | unfold e_PL; cbn [disjoint_from]; clear - EHL HD0 HDC' LO SLO LX31; lia].
          intros [[q A'] n'] Hb. cbn. exact (FRH _ _ _ (PLB _ Hb)). }
        pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX4 CST4 MU4' WM4' HWo4 ltac:(intros q Hq E; apply NKXH; rewrite <- E; exact Hq)) as MBX4'.
        pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY4 CST4 MU4' WM4' HWo4 ltac:(intros q Hq E; apply NKYH; rewrite <- E; exact Hq)) as MBY4'.
        pose proof (er0_seg _ en _ _ _ _ _ _ _ _ _ _ _ _ ER4 MU4' WM4' CST4 (proj1 OWNE4) HWo4 ltac:(cbv beta; intros E; exact (FRH _ _ _ INE E))) as ER4'.
        unfold hideP in NMC4, DTC4, HDa.
        assert (NMC4' : rw_cells usegs m4' namev [CB (Z.to_nat nn) bn]).
        { eapply rw_cells_transport; [exact NMC4| exact MU4'| exact WM4'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - APNH EHL NN LX31; lia. }
        assert (DTC4' : rw_cells usegs m4' DT [CB (Z.to_nat dlen) djunk]).
        { eapply rw_cells_transport; [exact DTC4| exact MU4'| exact WM4'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - APDH EHL DLEN LX31; lia. }
        assert (HDa' : rw_cells usegs m4' HD [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj)]).
        { eapply rw_cells_transport; [exact HDa| exact MU4'| exact WM4'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - EHL LX31; lia. }
        assert (HDC4' : rw_cells usegs m4' HD [CB (Z.to_nat (lenX + 1)) (firstn (Z.to_nat lenX) hj ++ [Z_to_bv 8 0])]).
        { replace (Z.to_nat (lenX + 1)) with (Z.to_nat lenX + 1)%nat by (clear - LX31; lia). eapply rw_cells_CB_join; [exact HDa'|].
          replace (HD + Z.of_nat (Z.to_nat lenX)) with HL by (clear - EHL LX31; lia). eapply (th_cells_congr _ _ _ _ [CB 1%nat [Z_to_bv 8 0]]) in HDz; [exact HDz| reflexivity| reflexivity| cbn; repeat split; auto]. }
        lazymatch goal with H : rw_cells usegs m4' (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC4' end.
        lazymatch goal with H : rw_cells usegs m4' (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT4' end.
        pose proof COM4' as (CST4' & _). clear CST4 MI4' ST4' COM4 NMC4 DTC4 HDa HDa' HDz MBX4 MBY4 ER4.
        (* [comment removed for export] *)
        unfold bio_read_stmt in BRD.
        eapply climpl_seq.
        { eapply BRD with (K := KY) (po := qd) (BI := dBv) (BM := BMY) (meth := methY) (len := lenY) (max := maxY) (off := 0) (OUT := DT) (no := dlen) (n := dlen) (lo := e_lo en) (B := e_B en) (blw := wz dlen) (ojunk := djunk);
            [exact CST4'| rewrite unsigned_lit by lia; unfold BREAD_STACK; clear - SLO; lia| exact MBY4'| clear - DLEN DNZ; lia| exact OWND| exact NKYD| clear; lia| exact LDJ| exact DTC4'| rewrite unsigned_lit by lia; clear - AL16; lia| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros f5 L5 st5 ms5 (v5 & m5 & LB5 & RET & FU5 & GR5 & CST5 & FRM5 & (dj5 & -> & -> & -> & MBY5 & LDJ5 & DTC5)).
        destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM5 by lia. rewrite Z.add_0_l in MBY5.
        assert (COM5 : pem_com libenv en st5 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f5 m5 off (rem - 2)
                         (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)).
        { eapply (com_callI en) with (T1 := fun q => mbio_T KY q \/ q = qd); [exact COM4'| exact CST5| exact FRM5| unfold e_PL; clear; lia| exact FU5| clear; lia| exact GR5| | | | | | | exact HT2| exact HK2| exact HE2];
            clear - RA4 RB4 RBIG4; lia. }
        pose proof FRM5 as (CFR5 & KP5 & _).
        pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX4' FRM5 HX2) as MBX5.
        pose proof (er0_call en _ _ _ _ _ _ _ _ _ _ ER4' FRM5 (proj1 OWNE4) HE2) as ER5.
        pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 LOC4' ltac:(clear; lia)) as LOC5. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 OUT4' ltac:(clear; lia)) as OUT5.
        pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR5 NMC4' (proj1 OWNN3) HN2 ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC5.
        pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qh, HD, lenX + 1) CFR5 HDC4' (proj1 OWNH3) HH2 ltac:(cbn; clear; lia) ltac:(cbn; clear - LX31; lia)) as HDC5.
        pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _). rewrite unsigned_lit in ST5 by lia.
        pose proof COM5 as (_ & _ & _ & _ & _ & _ & OWNE5 & _).
        clear CST4' COM4' FRM5 CFR5 LOC4' OUT4' NMC4' DTC4' HDC4' MBX4' MBY4' ER4'.
        pose proof (munch_refl [(bv_unsigned (e_sp en), bv_unsigned (e_sp en) + 8); (bv_unsigned (e_sp en) + 24, bv_unsigned (e_sp en) + 32)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
        hide NMC5. hide DTC5. hide HDC5.
        (* [comment removed for export] *)
        cprefix. ths. rewrite (t_sx32_small dlen) by (clear - DLEN LY31; lia). ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - DLEN LY31; lia); clear - K; lia|]. clear K.
        ths. ths. ths. ths. ths. ths. ths. ths.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5' end.
        lazymatch goal with H : stk usegs m5' _ _ |- _ => rename H into ST5' end. lazymatch goal with H : mem_inv usegs m5' |- _ => rename H into MI5' end.
        lazymatch goal with H : munch _ m5 m5' |- _ => rename H into MU5' end. lazymatch goal with H : wmono usegs m5 m5' |- _ => rename H into WM5' end.
        chere.
        assert (HWo5 : Forall (wfree ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True))
                               [(bv_unsigned (e_sp en), bv_unsigned (e_sp en) + 8); (bv_unsigned (e_sp en) + 24, bv_unsigned (e_sp en) + 32)])
          by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|]; apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
        assert (COM5' : pem_com libenv en st5 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f5 m5' off (rem - 2)
                          (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)).
        { eapply (com_segI en) with (EX := fun _ => True); [exact COM5| exact MU5'| exact WM5'| exact MI5'| exact ST5'| exact HWo5| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
        pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX5 CST5 MU5' WM5' HWo5 ltac:(intros q _; exact I)) as MBX5'.
        pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY5 CST5 MU5' WM5' HWo5 ltac:(intros q _; exact I)) as MBY5'.
        pose proof (er0_seg _ en _ _ _ _ _ _ _ _ _ _ _ _ ER5 MU5' WM5' CST5 (proj1 OWNE5) HWo5 I) as ER5'.
        unfold hideP in NMC5, DTC5, HDC5.
        assert (NMC5' : rw_cells usegs m5' namev [CB (Z.to_nat nn) bn]).
        { eapply rw_cells_transport; [exact NMC5| exact MU5'| exact WM5'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - RN1 RN2 LO SLO NN. lia. }
        assert (DTC5' : rw_cells usegs m5' DT [CB (Z.to_nat dlen) dj5]).
        { eapply rw_cells_transport; [exact DTC5| exact MU5'| exact WM5'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - RD1 RD2 LO SLO DLEN. lia. }
        assert (HDC5' : rw_cells usegs m5' HD [CB (Z.to_nat (lenX + 1)) (firstn (Z.to_nat lenX) hj ++ [Z_to_bv 8 0])]).
        { eapply rw_cells_transport; [exact HDC5| exact MU5'| exact WM5'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - HD0 HDC' LO SLO LX31. lia. }
        lazymatch goal with H : rw_cells usegs m5' (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC5' end.
        lazymatch goal with H : rw_cells usegs m5' (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT5' end.
        destruct (out4_split _ _ _ _ _ _ OUT5') as (O1 & O2 & O3 & O4).
        (* [comment removed for export] *)
        assert (NQD' : ~ In qd ((mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) ++ e_pe en :: mbio_blocks (e_K en))).
        { intros X. assert (Y : In qd (map blk_id LBc)); [apply IDS; apply in_app_iff in X; destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X]|].
          apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hq). cbn in E. exact (FRD _ _ _ (or_intror Hq) E). }
        eapply (ENDP en st5 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f5 m5' off (rem - 2)%nat
                  (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)
                  _ [] [(qd, DT, dlen); (qh, HD, lenX + 1); (qn, namev, nn)]
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Some qc) None ctxv 0 nn hBv dBv 1 KX KY BMX BMY methX methY lenX maxX lenX lenY maxY dlen (wz lenX) (wz dlen));
          [exact COM5'| left; split; [reflexivity| exact ER5']| clear - REM; lia| exact LOC5'| reflexivity| cbv iota beta; exact OWNC3| reflexivity| exact MBX5'| exact MBY5'| | | apply Forall_nil| | | | | |].
        * intros b Hb. cbn [opt_ids app]. destruct Hb as [<-|[<-|Hb]]; [right; right; left; reflexivity| right; right; right; left; reflexivity|].
          destruct (ELB _ Hb) as [X|X]; [left; exact X|].
          apply in_app_iff in X. destruct X as [X|X]; [right; left; apply in_or_app; left; exact X|].
          apply in_app_iff in X. destruct X as [X|X]; [right; left; apply in_or_app; right; apply in_or_app; left; exact X|].
          destruct X as [X|[X|[]]]; [right; left; apply in_or_app; right; apply in_or_app; right; left; exact X|].
          right; right. right; right; left. symmetry. apply (nodup_blk_eq LBc); [exact NDLB| exact Hb| exact INN0| transitivity qn; [exact (eq_sym X)| reflexivity]].
        * intros b [<-|[<-|[<-|[]]]]; [left; reflexivity| right; left; reflexivity| exact (proj1 OWNN3)].
        * intros b Hb X. apply (CFRESH _ Hb). cbn [opt_ids app] in X. rewrite ?app_nil_r in X.
          apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
          destruct X as [X|[]]. left. exact X.
        * intros b Hn X. apply in_map_iff in X. destruct X as ([[q' A''] n''] & E' & Hb').
          destruct Hn as [<-|[<-|[<-|[]]]]; cbn in E'.
          -- exact (FRD _ _ _ (or_intror (PLB _ Hb')) E').
          -- exact (FRH _ _ _ (PLB _ Hb') E').
          -- apply (CFRESH _ Hb'). cbn [blk_id fst]. rewrite E'. apply in_or_app; right; apply in_or_app; right; right; left; reflexivity.
        * intros q nm Hq X. apply (EL _ _ Hq). cbn [opt_ids app] in X. rewrite ?app_nil_r in X.
          apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
          destruct X as [X|[]]. left. exact X.
        * assert (PERM : Permutation ((mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) ++ qd :: qh :: e_pe en :: mbio_blocks (e_K en))
                                     ((mbio_blocks KX ++ mbio_blocks KY ++ [qc]) ++ [qd; qh; qn] ++ e_pe en :: mbio_blocks (e_K en))).
          { rewrite <- (app_assoc (mbio_blocks KX) (mbio_blocks KY ++ [qc; qn]) _), <- (app_assoc (mbio_blocks KY) [qc; qn] _).
            rewrite <- (app_assoc (mbio_blocks KX) (mbio_blocks KY ++ [qc]) _), <- (app_assoc (mbio_blocks KY) [qc] _).
            apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply perm_skip. apply (Permutation_middle [qd; qh] (e_pe en :: mbio_blocks (e_K en)) qn). }
          eapply Permutation_NoDup; [| apply (nd_insert2 _ _ qd qh NDT NQD' ltac:(intros X; apply NQH'; rewrite <- ?app_assoc in X; exact X) ltac:(intros E; exact (FRD _ _ _ (or_introl eq_refl) (eq_sym E))))].
          eapply Permutation_trans; [exact PERM|]. cbn [opt_ids map blk_id fst app]. rewrite ?app_nil_r. apply Permutation_refl.
        * right. split; [reflexivity|]. exists qn, qh, qd, namev, HD, DT, nn, (lenX + 1), dlen, bn, (firstn (Z.to_nat lenX) hj ++ [Z_to_bv 8 0]), dj5.
          split; [reflexivity|]. split; [exact OWNN3|]. split; [exact OWNH3|]. split; [exact OWND|]. split; [exact NN|]. split; [clear - LX31; lia|]. split; [clear - DLEN DNZ LY31; lia|].
          split; [exact O4|]. split; [exact O3|]. split; [exact O2|]. split; [exact O1|].
          split; [exact LBN|]. split; [exact NMC5'|]. split; [exact NUL|].
          split; [rewrite length_app, length_firstn, LHJ4; cbn; clear - LX31; lia|]. split; [exact HDC5'|].
          split; [rewrite nth_error_app2 by (rewrite length_firstn, LHJ4; clear - LX31; lia); rewrite length_firstn, LHJ4; replace (Z.to_nat (lenX + 1 - 1) - Nat.min (Z.to_nat lenX) (Z.to_nat (lenX + 1)))%nat with 0%nat by (clear - LX31; lia); reflexivity|].
          split; [exact LDJ5| exact DTC5'].
        * unfold news_sz, blk_size. cbn [fold_right snd]. pose proof COM5' as (_ & _ & _ & _ & _ & _ & _ & _ & OFF5 & _). clear - OFF5 NN LXY DLEN. lia. }
      pose proof (munch_refl [(bv_unsigned (e_sp en) + 8, bv_unsigned (e_sp en) + 16)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      hide NMC3. hide HDC3. hide DTC.
      cprefix. ths. ths.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3' end.
      lazymatch goal with H : stk usegs m3' _ _ |- _ => rename H into ST3' end. lazymatch goal with H : mem_inv usegs m3' |- _ => rename H into MI3' end.
      lazymatch goal with H : munch _ m3 m3' |- _ => rename H into MU3' end. lazymatch goal with H : wmono usegs m3 m3' |- _ => rename H into WM3' end.
      ths. ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - HD0 HDC' LO SLO SPR; lia); clear - K HD0; lia|]. clear K.
      ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - DT0 DTC' LO SLO SPR; lia); clear - K DT0; lia|]. clear K.
      assert (HWo3 : Forall (wfree ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True)) [(bv_unsigned (e_sp en) + 8, bv_unsigned (e_sp en) + 16)])
        by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
      assert (COM3' : pem_com libenv en st3 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f3 m3' off (rem - 2)
                        (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)).
      { eapply (com_segI en) with (EX := fun _ => True); [exact COM3| exact MU3'| exact WM3'| exact MI3'| exact ST3'| exact HWo3| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
      pose proof (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX3 CST3 MU3' WM3' HWo3 ltac:(intros q _; exact I)) as MBX3'.
      pose proof (mbx_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY3 CST3 MU3' WM3' HWo3 ltac:(intros q _; exact I)) as MBY3'.
      pose proof (er0_seg _ en _ _ _ _ _ _ _ _ _ _ _ _ ER3 MU3' WM3' CST3 (proj1 OWNE3) HWo3 I) as ER3'.
      unfold hideP in NMC3, HDC3, DTC.
      assert (NMC3' : rw_cells usegs m3' namev [CB (Z.to_nat nn) bn]).
      { eapply rw_cells_transport; [exact NMC3| exact MU3'| exact WM3'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - RN1 RN2 LO SLO NN. lia. }
      assert (HDC3' : rw_cells usegs m3' HD [CB (Z.to_nat (lenX + 1)) hjunk]).
      { eapply rw_cells_transport; [exact HDC3| exact MU3'| exact WM3'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - HD0 HDC' LO SLO LX31. lia. }
      assert (DTC3' : rw_cells usegs m3' DT [CB (Z.to_nat dlen) djunk]).
      { eapply rw_cells_transport; [exact DTC| exact MU3'| exact WM3'|]. cbn [disjoint_from cells_size csize Nat.add]. clear - DT0 DTC' LO SLO DLEN. lia. }
      lazymatch goal with H : rw_cells usegs m3' (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC3' end.
      lazymatch goal with H : rw_cells usegs m3' (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT3' end.
      pose proof COM3' as (CST3' & _). clear CST3 MI3' ST3' COM3 NMC3 HDC3 DTC MBX3 MBY3 ER3.
      ths. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        assert (LX0 : lenX = 0) by (rewrite ?unsigned_lit in K by (clear - LX31; lia); clear - K LX31; lia). clear K. subst lenX.
        chere. destruct MBX3' as [BMX MBh].
        eapply (JOIN f3 st3 m3' hjunk); [exact COM3'| exact ER3'| exists BMX; exact MBh| exact MBY3'| exact LOC3'| exact OUT3'| exact NMC3'| exact LHJ| exact HDC3'| exact DTC3'].
      + (* [comment removed for export] *)
        assert (LXP : 0 < lenX) by (rewrite ?unsigned_lit in K by (clear - LX31; lia); clear - K LX31; lia). clear K.
        ths. ths. ths. chere. destruct MBX3' as [BMX MBh]. unfold bio_read_stmt in BRD.
        eapply climpl_seq.
        { eapply BRD with (K := KX) (po := qh) (BI := hBv) (BM := BMX) (meth := methX) (len := lenX) (max := maxX) (off := 0) (OUT := HD) (no := lenX + 1) (n := lenX) (lo := e_lo en) (B := e_B en) (blw := wz lenX) (ojunk := hjunk);
            [exact CST3'| rewrite unsigned_lit by lia; unfold BREAD_STACK; clear - SLO; lia| exact MBh| clear - LXP; lia| exact OWNH3| exact NKXH| clear; lia| exact LHJ| exact HDC3'| rewrite unsigned_lit by lia; clear - AL16; lia| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros f4 L4 st4 ms4 (v4 & m4 & LB4 & RET & FU4 & GR4 & CST4 & FRM4 & (hj4 & -> & -> & -> & MB4 & LHJ4 & HDC4)).
        destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM4 by lia.
        assert (COM4 : pem_com libenv en st4 ((qd, DT, dlen) :: (qh, HD, lenX + 1) :: LBc) ((qd, dlen) :: (qh, lenX + 1) :: Lc) f4 m4 off (rem - 2)
                         (rA - wA (lenX + 1) - wA dlen) (rB - wB (lenX + 1) - wB dlen) (rBig - wBig (lenX + 1) - wBig dlen)).
        { eapply (com_callI en) with (T1 := fun q => mbio_T KX q \/ q = qh); [exact COM3'| exact CST4| exact FRM4| unfold e_PL; clear; lia| exact FU4| clear; lia| exact GR4| | | | | | | exact HT1| exact HK1| exact HE1];
            clear - RA3 RB3 RBIG3; lia. }
        pose proof FRM4 as (CFR4 & KP4 & _).
        pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY3' FRM4 HY1) as MBY4.
        pose proof (er0_call en _ _ _ _ _ _ _ _ _ _ ER3' FRM4 (proj1 OWNE3) HE1) as ER4.
        pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 LOC3' ltac:(clear; lia)) as LOC4. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 OUT3' ltac:(clear; lia)) as OUT4.
        pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR4 NMC3' (proj1 OWNN3) HN1 ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC4.
        pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qd, DT, dlen) CFR4 DTC3' (proj1 OWND) HD1 ltac:(cbn; clear; lia) ltac:(cbn; clear - DLEN; lia)) as DTC4.
        pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _). rewrite unsigned_lit in ST4 by lia.
        clear CST3' COM3' FRM4 CFR4 LOC3' OUT3' NMC3' DTC3' HDC3' MBY3' ER3' MBh.
        pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
        (* [comment removed for export] *)
        cprefix. ths. ths. ths. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - LX31; lia); clear - K; lia|]. clear K.
        chere.
        eapply (JOIN f4 st4 m4 hj4); [exact COM4| exact ER4| exists BMX; exact MB4| exact MBY4| exact LOC4| exact OUT4| exact NMC4| exact LHJ4| exact HDC4| exact DTC4].
  Qed.
End W3.
