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
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_rzt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

Definition J_RAISE0 : Z := 0x188000.

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

  (* [comment removed for export] *)
  Definition RAISE0_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig loc
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word),
    pem_com libenv en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (2 <= rem)%nat -> 2 <= rA ->
    (forall b, In b LBc -> In b (e_LBall en)) -> List.NoDup (e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en + -208) loc -> Z.of_nat (cells_size loc) = 104 ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) s6 s7 (wz (e_PL en + 24)) s9 s10 s11 t3 t4 t5 t6) (e_F en) (wz J_RAISE0) (e_fc en) None m (seg_rom usegs))
      (pem_post libenv errst_live en).

  Theorem RAISE0_proof :
    err_new_rest_stmt libenv errst_at_rest errst_live -> err_set_debug_stmt libenv errst_live -> err_set_error_stmt libenv errst_live ->
    END0_stmt libenv errst_at_rest errst_live -> RAISE0_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ENEW EDBG ESET END0P en s LBc Lc f m off rem rA rB rBig loc xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6.
    intros COM ER0 REM RA2 ELB NDR LOC LOCZ OUT. unfold END0_stmt, J_END in END0P.
    unfold err_new_rest_stmt in ENEW. unfold err_set_debug_stmt in EDBG. unfold err_set_error_stmt in ESET.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_RAISE0, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (proj1 (NoDup_cons_iff _ _) NDR) as [NPE _].
    assert (HKE : forall q, mbio_T (e_K en) q -> e_pe en <> q) by (intros q Hq E; apply NPE; rewrite E; apply mbio_T_blocks; exact Hq).
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
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear - LOCZ; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia. pose proof COM1 as (_ & _ & _ & _ & _ & _ & OWNE1 & _).
    pose proof COM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM1 & _ & RA1 & RB1 & RBIG1 & _).
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 LOC OUT LE.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply EDBG with (lo := e_lo en) (B := e_B en) (SF := 0x30126) (SN := 0x31642) (nf := 21) (nn := 16) (line := 955) (fstr := pem_file_str) (nstr := pem_func_str) (fslack := pem_file_slk) (nslack := pem_func_slk);
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
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear - LOCZ; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia. pose proof COM2 as (_ & _ & _ & _ & _ & _ & OWNE2 & _).
    pose proof COM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM2 & _ & RA2' & RB2 & RBIG2 & _).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _]. cbn [map blk_id fst] in ND2.
    inversion ND2 as [|z1 k1 NQS ND2']; subst. inversion ND2' as [|z2 k2 NQF _]; subst. cbn [In] in NQS.
    clear MU WM CST1 HP1 MI1 ST1 COM1 FRM2 CFR2 LOC1 OUT1 LE1 EL1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply ESET with (lo := e_lo en) (B := e_B en) (lib := 9) (reason := 0x80106);
        [exact CST2| rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE2| intros b Hb; right; right; exact (INCL _ Hb)| exact OWNE2| exact EL2
        | reflexivity| reflexivity| reflexivity| clear; lia| clear; lia| clear; lia]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (-> & -> & LE3 & EL3)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    assert (COM3 : pem_com libenv en st3 ((qs, QS, 16) :: (qf, QF, 21) :: LBc) ((qs, 16) :: (qf, 21) :: Lc) f3 m3 off (rem - 2) (rA - 2) rB rBig).
    { eapply (com_callEI en) with (EV1 := 0%nat) (dA := 0) (dB := 0) (dBig := 0); [exact COM2| exact CST3| exact FRM3| exact FU3| clear; lia| exact GR3| | | | | | | intros b X; exact X| intros q nm X; exact X| exact LE3| exact HKE];
        clear - RA2' RB2 RBIG2; lia. }
    pose proof FRM3 as (CFR3 & KP3 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear - LOCZ; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
    pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    clear MU WM CST2 HP2 MI2 ST2 COM2 FRM3 CFR3 LOC2 OUT2 LE2 EL2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. ths. chere.
    eapply (END0P en st3 ((qs, QS, 16) :: (qf, QF, 21) :: LBc) ((qs, 16) :: (qf, 21) :: Lc) f3 m3 off (rem - 2)%nat (rA - 2) rB rBig [(qs, QS, 16); (qf, QF, 21)] loc);
      [exact COM3| right; exists 1, 0; split; [exact EL3| cbn; clear; lia]| | | | | | exact LOC3| exact LOCZ| exact OUT3].
    - intros b Hb. destruct Hb as [<-|[<-|Hb]]; [right; left; reflexivity| right; right; left; reflexivity| left; exact (ELB _ Hb)].
    - intros b [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity].
    - apply Forall_cons; [split; [left; reflexivity| cbn; clear; lia]| apply Forall_cons; [split; [right; left; reflexivity| cbn; clear; lia]| apply Forall_nil]].
    - intros b [<-|[<-|[]]] X; cbn [blk_id fst] in X; [apply NQS; right| apply NQF]; apply in_map_iff in X; destruct X as (b' & E & Hb');
        rewrite <- E; apply in_map; exact (PLB _ Hb').
    - cbn [map blk_id fst]. constructor; [cbn; intros [E|[]]; apply NQS; left; exact E| constructor; [intros []| constructor]].
  Qed.
End W3.
