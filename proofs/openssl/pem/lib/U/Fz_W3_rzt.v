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

(* [comment removed for export] *)
Definition pem_file_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x30126 20 with Some bs => bs | None => [] end).
Definition pem_func_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x31642 15 with Some bs => bs | None => [] end).
Lemma pem_file_ro : ro_bytes Image.usegs 0x30126 (pem_file_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Definition pem_file_slk : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x3013b 5 with Some bs => bs | None => [] end).
Lemma pem_file_ro' : ro_bytes Image.usegs 0x30126 (pem_file_str ++ Z_to_bv 8 0 :: pem_file_slk).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition pem_func_slk : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x31652 6 with Some bs => bs | None => [] end).
Lemma pem_func_ro' : ro_bytes Image.usegs 0x31642 (pem_func_str ++ Z_to_bv 8 0 :: pem_func_slk).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_func_ro : ro_bytes Image.usegs 0x31642 (pem_func_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_file_nonul : ~ In (Z_to_bv 8 0) pem_file_str.
Proof. unfold pem_file_str. intros H. repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate|]). exact H. Qed.
Lemma pem_func_nonul : ~ In (Z_to_bv 8 0) pem_func_str.
Proof. unfold pem_func_str. intros H. repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate|]). exact H. Qed.
Lemma pem_file_len : length pem_file_str = 20%nat. Proof. reflexivity. Qed.
Lemma pem_func_len : length pem_func_str = 15%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nd_insert2 : forall (l1 l2 : list bptr) x y,
  List.NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> ~ In y (l1 ++ l2) -> x <> y -> List.NoDup (l1 ++ x :: y :: l2).
Proof.
  intros l1 l2 x y ND NX NY NE. induction l1 as [|z l1 IH]; cbn [app] in *.
  - constructor; [cbn; intros [H|H]; [exact (NE (eq_sym H))| exact (NX H)]|]. constructor; [exact NY| exact ND].
  - inversion ND as [|z' l' NI ND']; subst. constructor.
    + intros X. apply in_app_iff in X. destruct X as [X|X]; [apply NI; apply in_or_app; left; exact X|].
      cbn in X. destruct X as [X|[X|X]]; [apply NX; left; exact (eq_sym X)| apply NY; left; exact (eq_sym X)| apply NI; apply in_or_app; right; exact X].
    + apply IH; [exact ND'| intros X; apply NX; right; exact X| intros X; apply NY; right; exact X].
Qed.

(* [comment removed for export] *)
Lemma cown_id : forall LBall L p A n nm, cown LBall L p A n nm -> In p (map blk_id LBall).
Proof. intros LBall L p A n nm [H _]. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact H]. Qed.
Lemma mbx_ids `{CE__ : Ceiling} : forall m LBall L K BI BM blw meth len max off q,
  mbio_repx m LBall L K BI BM blw meth len max off -> In q (mbio_blocks K) -> In q (map blk_id LBall).
Proof.
  intros m LBall L K BI BM blw meth len max off q (BB & RP & fl & rrw & padw & nr & nw & OB & _ & _ & _ & _ & _ & _ & (rmaxw & OBB & _ & OBM & ORP & _ & _ & _ & INNER)) Hq.
  unfold mbio_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
  - destruct Hq as [<-|[<-|[<-|[<-|[]]]]]; [exact (cown_id _ _ _ _ _ _ OB)| exact (cown_id _ _ _ _ _ _ OBB)| exact (cown_id _ _ _ _ _ _ OBM)| exact (cown_id _ _ _ _ _ _ ORP)].
  - destruct (k_d K) as [pd|]; [| destruct Hq]. destruct Hq as [<-|[]]. destruct INNER as (D & nmd & junk & OD & _). exact (cown_id _ _ _ _ _ _ OD).
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
  Local Notation com_callEI := (com_callE libenv).
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem RZT_proof :
    err_new_rest_stmt libenv errst_at_rest errst_live -> err_set_debug_stmt libenv errst_live -> err_set_error_stmt libenv errst_live ->
    END_stmt libenv errst_at_rest errst_live -> RZT_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ENEW EDBG ESET ENDP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l6 l7 l8 l9 l11 ta tb
           qc qn ctxv namev nn hBv dBv bn KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
    cbv zeta. intros COM ER0 REM RA2 LOC OWNC OWNN NN LBN NMC NUL MBX MBY ELB CFRESH EL NDT OUT. unfold END_stmt, J_END in ENDP.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_RZT, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC).
    (* [comment removed for export] *)
    pose proof (proj1 (NoDup_cons_iff _ _) NDR) as [NPE _].
    assert (HKE : forall q, mbio_T (e_K en) q -> e_pe en <> q) by (intros q Hq E; apply NPE; rewrite E; apply mbio_T_blocks; exact Hq).
    assert (HCE : ~ e_pe en = qc) by (intros E; apply (DJC qc); [apply in_or_app; right; apply in_or_app; right; left; reflexivity| left; exact E]).
    assert (HNE : ~ e_pe en = qn) by (intros E; apply (DJC qn); [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity| left; exact E]).
    assert (HXE : forall q, mbio_T KX q -> ~ e_pe en = q) by (intros q Hq E; apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| left; exact E]).
    assert (HYE : forall q, mbio_T KY q -> ~ e_pe en = q) by (intros q Hq E; apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| left; exact E]).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    (* [comment removed for export] *)
    assert (IDS : forall q, In q (mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) \/ q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
    { intros q [X|[->|X]].
      - apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBX X)|].
        apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBY X)|].
        destruct X as [<-|[<-|[]]]; [exact (cown_id _ _ _ _ _ _ OWNC)| exact (cown_id _ _ _ _ _ _ OWNN)].
      - apply in_map_iff. exists (e_pe en, e_E en, 904). split; [reflexivity| exact INE].
      - apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
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
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX FRM1 HXE) as MBX1. pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY FRM1 HYE) as MBY1.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC FRM1 HCE) as OWNC1. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN FRM1 HNE) as OWNN1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HNE ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia. pose proof COM1 as (_ & _ & _ & _ & _ & _ & OWNE1 & _).
    pose proof COM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM1 & _ & RA1 & RB1 & RBIG1 & _).
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 LOC OUT NMC MBX MBY OWNC OWNN LE.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply EDBG with (lo := e_lo en) (B := e_B en) (SF := 0x30126) (SN := 0x31642) (nf := 21) (nn := 16) (line := 996) (fstr := pem_file_str) (nstr := pem_func_str) (fslack := pem_file_slk) (nslack := pem_func_slk);
        [clear - FU FU1 REM; lia| eapply croom_weaken; [exact ROOM1| clear - RA2; lia| clear - RB1; lia| clear - RBIG1; lia]| exact CST1
        | rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE1| exact INCL| exact OWNE1| exact EL1
        | reflexivity| reflexivity| reflexivity| exact pem_file_ro'| exact pem_func_ro'| exact pem_file_nonul| exact pem_func_nonul
        | clear; cbn; lia| clear; cbn; lia| clear; lia| clear; cbn; lia| clear; lia| clear; cbn; lia
        | rewrite pem_file_len; reflexivity| rewrite pem_func_len; reflexivity| clear; lia| clear; lia]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (qf & qs & QF & QS & -> & -> & LE2 & EL2)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    assert (COM2 : pem_com libenv en st2 ((qs, QS, 16) :: (qf, QF, 21) :: LBc) ((qs, 16) :: (qf, 21) :: Lc) f2 m2 off (rem - 2) (rA - 2) rB rBig).
    { eapply (com_callEI en) with (EV1 := 2%nat) (dA := 2) (dB := 0) (dBig := 0); [exact COM1| exact CST2| exact FRM2| exact FU2| clear - REM; lia| exact GR2| | | | | | | intros b X; right; right; exact X| intros q nm X; right; right; exact X| exact LE2| exact HKE];
        clear - RA1 RB1 RBIG1 RA2; lia. }
    pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1 FRM2 HXE) as MBX2. pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY1 FRM2 HYE) as MBY2.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC1 FRM2 HCE) as OWNC2. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN1 FRM2 HNE) as OWNN2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR2 NMC1 (proj1 OWNN1) HNE ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia. pose proof COM2 as (_ & _ & _ & _ & _ & _ & OWNE2 & _).
    pose proof COM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM2 & _ & RA2' & RB2 & RBIG2 & _).
    (* [comment removed for export] *)
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _]. cbn [map blk_id fst] in ND2.
    inversion ND2 as [|z1 k1 NQS ND2']; subst. inversion ND2' as [|z2 k2 NQF _]; subst. cbn [In] in NQS.
    clear MU WM CST1 HP1 MI1 ST1 COM1 FRM2 CFR2 LOC1 OUT1 NMC1 MBX1 MBY1 OWNC1 OWNN1 LE1 EL1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply ESET with (lo := e_lo en) (B := e_B en) (lib := 9) (reason := 100);
        [exact CST2| rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE2| intros b Hb; right; right; exact (INCL _ Hb)| exact OWNE2| exact EL2
        | reflexivity| reflexivity| reflexivity| clear; lia| clear; lia| clear; lia]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (-> & -> & LE3 & EL3)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    assert (COM3 : pem_com libenv en st3 ((qs, QS, 16) :: (qf, QF, 21) :: LBc) ((qs, 16) :: (qf, 21) :: Lc) f3 m3 off (rem - 2) (rA - 2) rB rBig).
    { eapply (com_callEI en) with (EV1 := 0%nat) (dA := 0) (dB := 0) (dBig := 0); [exact COM2| exact CST3| exact FRM3| exact FU3| clear; lia| exact GR3| | | | | | | intros b X; exact X| intros q nm X; exact X| exact LE3| exact HKE];
        clear - RA2' RB2 RBIG2; lia. }
    pose proof FRM3 as (CFR3 & KP3 & _).
    pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2 FRM3 HXE) as MBX3. pose proof (mbx_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2 FRM3 HYE) as MBY3.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNC2 FRM3 HCE) as OWNC3. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN2 FRM3 HNE) as OWNN3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR3 NMC2 (proj1 OWNN2) HNE ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC3.
    pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    clear MU WM CST2 HP2 MI2 ST2 COM2 FRM3 CFR3 LOC2 OUT2 NMC2 MBX2 MBY2 OWNC2 OWNN2 LE2 EL2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM. unfold pem_loc in LOC3.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. ths. chere.
    destruct (out4_split _ _ _ _ _ _ OUT3) as (O1 & O2 & O3 & O4).
    eapply (ENDP en st3 ((qs, QS, 16) :: (qf, QF, 21) :: LBc) ((qs, 16) :: (qf, 21) :: Lc) f3 m3 off (rem - 2)%nat (rA - 2) rB rBig (pem_loc l0 l1 (wz namev) l3 l4 l5 l6 l7 l8 l9 (wz (e_flags en)) l11 ta tb) [(qs, QS, 16); (qf, QF, 21)] []
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Some qc) (Some qn) ctxv namev nn hBv dBv 0 KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY);
      [exact COM3| right; exists 1, 0; split; [exact EL3| cbn; clear; lia]| clear - REM; lia| exact LOC3| reflexivity| cbv iota beta; exact OWNC3
      | cbv iota beta; split; [exact OWNN3| split; [clear - NN; lia| apply rw_cells_CB0; clear - RN1 RN2 NN LO SLO SPR; lia]]| exact MBX3| exact MBY3| | | | | | | | |].
    - intros b Hb. cbn [opt_ids app]. rewrite ?app_nil_r. destruct Hb as [<-|[<-|Hb]]; [right; right; left; reflexivity| right; right; right; left; reflexivity|].
      destruct (ELB _ Hb) as [X|X]; [left; exact X| right; left; exact X].
    - rewrite ?app_nil_r. intros b [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity].
    - apply Forall_cons; [split; [left; reflexivity| cbn; clear; lia]| apply Forall_cons; [split; [right; left; reflexivity| cbn; clear; lia]| apply Forall_nil]].
    - exact CFRESH.
    - rewrite ?app_nil_r. intros b [<-|[<-|[]]] X; cbn [blk_id fst] in X; [apply NQS; right| apply NQF]; apply in_map_iff in X; destruct X as (b' & E & Hb');
        rewrite <- E; apply in_map; exact (PLB _ Hb').
    - exact EL.
    - cbn [opt_ids map blk_id fst app]. rewrite ?app_nil_r.
      lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn]) ++ qs :: qf :: e_pe en :: mbio_blocks (e_K en)) by (rewrite <- ?app_assoc; reflexivity) end.
      apply nd_insert2; [exact NDT| | | clear - NQS; intros E; apply NQS; left; exact (eq_sym E)].
      + intros X. apply NQS. right. apply IDS. apply in_app_iff in X. destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X].
      + intros X. apply NQF. apply IDS. apply in_app_iff in X. destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X].
    - left. split; [reflexivity|]. split; [reflexivity|]. split; [exact O4|]. split; [exact O3|]. split; [exact O2| eexists; exact O1].
    - pose proof COM3 as (_ & _ & _ & _ & _ & _ & _ & _ & OFF3 & _). cbn. clear - OFF3. lia.
  Qed.
End W3.
