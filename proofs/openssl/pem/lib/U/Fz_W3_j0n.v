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
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Fz_W3_endl Fz_W3_hdg Fz_W3_j0g.
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

Lemma nd_app : forall (l1 l2 : list bptr), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 N1 N2 DJ; [exact N2|]. cbn. inversion N1; subst. constructor.
  - intros X. apply in_app_iff in X. destruct X as [X|X]; [tauto| exact (DJ a (or_introl eq_refl) X)].
  - apply IH; [assumption| exact N2| intros x Hx; exact (DJ x (or_intror Hx))].
Qed.

Definition J_J0N : Z := 0x188054.

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
  Local Notation er0_callI' := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  (* [comment removed for export] *)
  Definition J0N_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 ta tb : word) (meth : Z),
    pem_com libenv en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m ->
    (Z.to_nat (2 * (e_blen en - off) + 28) <= rem)%nat -> 0 <= e_boff en -> e_blen en < 2 ^ 26 ->
    14 <= rA -> 6 <= rB -> 6 * (e_blen en - e_boff en) + 32778 + 8448 + 8448 <= rBig ->
    (forall b, In b LBc -> In b (e_LBall en)) -> List.NoDup (e_pe en :: mbio_blocks (e_K en)) -> (meth = M_MEM \/ meth = M_SECMEM) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 ta tb) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 (wz meth) a1 a2 a3 a4 a5 a6 a7
                       (wz meth) (wz (e_PL en + 8)) (wz (e_PL en + 16)) (wz (e_flags en)) s6 (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) s10 s11 t3 t4 t5 t6)
                 (e_F en) (wz J_J0N) (e_fc en) None m (seg_rom usegs))
      (pem_post libenv errst_live en).

  Theorem J0N_proof : bio_new_mem_stmt libenv -> pem_malloc_stmt -> J0G_stmt libenv errst_at_rest errst_live -> J0N_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BN PM J0GP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 ta tb meth.
    intros COM ER0 REM BOFF BLEN RA14 RB6 RBIG LBE NDR METH LOC OUT.
    unfold J0G_stmt, J_J0G in J0GP. unfold bio_new_mem_stmt in BN. unfold pem_malloc_stmt in PM.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_J0N, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (proj1 (NoDup_cons_iff _ _) NDR) as [NPE _].
    assert (HKE : forall q, mbio_T (e_K en) q -> e_pe en <> q) by (intros q Hq E; apply NPE; rewrite E; apply mbio_T_blocks; exact Hq).
    pose proof (wB_big 256 ltac:(unfold TIER_A_MAX; clear; lia)) as (WA0 & WB1 & WBIG1).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. chere.
    eapply climpl_seq.
    { eapply BN with (meth := meth) (E := e_E en) (LBL := e_LBL en) (lo := e_lo en) (B := e_B en);
        [clear - FU REM OFF; lia| eapply croom_weaken; [exact ROOM| clear - RA14; lia| clear - RB0; lia| clear - RBIG0; lia]| exact CST
        | rewrite unsigned_lit by lia; unfold BNEW_STACK; clear - SLO; lia| exact LE| exact INCL| reflexivity| exact METH]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1' & RET & FU1 & GR1 & CST1 & FRM1 & (LE1 & (KX & hBv & BBX & BMX & RPX & -> & KXN & -> & -> & MBX1))).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    assert (COM1 : pem_com libenv en st1 ((k_rp KX, RPX, 32) :: (k_bm KX, BMX, 32) :: (k_bb KX, BBX, 16) :: (k_bi KX, hBv, 128) :: LBc)
                                        ((k_rp KX, 32) :: (k_bm KX, 32) :: (k_bb KX, 16) :: (k_bi KX, 128) :: Lc) f1 m1 off (rem - 4) (rA - 4) rB rBig).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear - REM OFF; lia| exact GR1| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
        clear - RA14 RB6 RBIG RA0 RB0 RBIG0 OFF BOFF; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE ltac:(intros X; exact X)) as ER1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    pose proof COM1 as (_ & _ & _ & _ & INCL1 & _ & OWNE1 & _ & _ & _ & _ & ROOM1 & _ & RA1 & RB1 & RBIG1 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (or_intror (or_intror (or_intror (or_introl eq_refl))))) as (RX1 & _ & _ & RX2 & _).
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG COM FRM1 CFR1 LOC OUT.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BN with (meth := meth) (E := e_E en) (LBL := e_LBL en) (lo := e_lo en) (B := e_B en);
        [clear - FU FU1 REM OFF; lia| eapply croom_weaken; [exact ROOM1| clear - RA1 RA14; lia| clear - RB1 RB0; lia| clear - RBIG1 RBIG0; lia]| exact CST1
        | rewrite unsigned_lit by lia; unfold BNEW_STACK; clear - SLO; lia| exact LE1| exact INCL1| reflexivity| exact METH]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2' & RET & FU2 & GR2 & CST2 & FRM2 & (LE2 & (KY & dBv & BBY & BMY & RPY & -> & KYN & -> & -> & MBY2))).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    set (LBc1 := (k_rp KX, RPX, 32) :: (k_bm KX, BMX, 32) :: (k_bb KX, BBX, 16) :: (k_bi KX, hBv, 128) :: LBc) in *.
    set (Lc1 := (k_rp KX, 32) :: (k_bm KX, 32) :: (k_bb KX, 16) :: (k_bi KX, 128) :: Lc) in *.
    assert (COM2 : pem_com libenv en st2 ((k_rp KY, RPY, 32) :: (k_bm KY, BMY, 32) :: (k_bb KY, BBY, 16) :: (k_bi KY, dBv, 128) :: LBc1)
                                        ((k_rp KY, 32) :: (k_bm KY, 32) :: (k_bb KY, 16) :: (k_bi KY, 128) :: Lc1) f2 m2 off (rem - 8) (rA - 8) rB rBig).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM1| exact CST2| exact FRM2| unfold e_PL; clear; lia| exact FU2| clear - REM OFF; lia| exact GR2| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
        clear - RA14 RB6 RBIG RA1 RB1 RBIG1 OFF BOFF; lia. }
    pose proof FRM2 as (CFR2 & KP2 & _).
    assert (INE1 : In (e_pe en, e_E en, 904) LBc1) by (do 4 right; exact INE).
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER1 FRM2 INE1 ltac:(intros X; exact X)) as ER2.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX1 FRM2 ltac:(intros q _ X; exact X)) as MBX2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    pose proof COM2 as (_ & _ & _ & _ & INCL2 & _ & OWNE2 & _ & _ & _ & _ & ROOM2 & _ & RA2 & RB2 & RBIG2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror (or_intror (or_intror (or_introl eq_refl))))) as (RY1 & _ & _ & RY2 & _).
    clear MU WM CST1 HP1 MI1 ST1 COM1 FRM2 CFR2 LOC1 OUT1 ER1 MBX1 LE1 INCL1 OWNE1 ROOM1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths.
    ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by (clear - RX1 RX2 LO SLO SPR; lia). clear - K0 RX1. lia. }
    ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by (clear - RY1 RY2 LO SLO SPR; lia). clear - K1 RY1. lia. }
    ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply PM with (n := 256) (flags := e_flags en) (lo := e_lo en) (B := e_B en);
        [clear - FU FU1 FU2 REM OFF; lia| eapply croom_weaken; [exact ROOM2| rewrite WA0; clear - RA2 RA14; lia| rewrite WB1; clear - RB2 RB6; lia| rewrite WBIG1; clear - RBIG2 RBIG OFF BOFF; lia]
        | clear; lia| clear - FLR; lia| exact CST2| rewrite unsigned_lit by lia; unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3' & RET & FU3 & GR3 & CST3 & FRM3 & (ql & LB1 & ljunk & -> & -> & -> & RNL & LBC3)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    set (LBc2 := (k_rp KY, RPY, 32) :: (k_bm KY, BMY, 32) :: (k_bb KY, BBY, 16) :: (k_bi KY, dBv, 128) :: LBc1) in *.
    set (Lc2 := (k_rp KY, 32) :: (k_bm KY, 32) :: (k_bb KY, 16) :: (k_bi KY, 128) :: Lc1) in *.
    assert (COM3 : pem_com libenv en st3 ((ql, LB1, 256) :: LBc2) ((ql, 256) :: Lc2) f3 m3 off (rem - 9) (rA - 8 - wA 256) (rB - wB 256) (rBig - wBig 256)).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM2| exact CST3| exact FRM3| unfold e_PL; clear; lia| exact FU3| clear - REM OFF; lia| exact GR3| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
        rewrite ?WA0, ?WB1, ?WBIG1; clear - RA14 RB6 RBIG RA2 RB2 RBIG2 OFF BOFF; lia. }
    pose proof FRM3 as (CFR3 & KP3 & _).
    assert (INE2 : In (e_pe en, e_E en, 904) LBc2) by (do 4 right; exact INE1).
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER2 FRM3 INE2 ltac:(intros X; exact X)) as ER3.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX2 FRM3 ltac:(intros q _ X; exact X)) as MBX3.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY2 FRM3 ltac:(intros q _ X; exact X)) as MBY3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 LOC2 ltac:(clear; lia)) as LOC3. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 OUT2 ltac:(clear; lia)) as OUT3.
    pose proof CST3 as (HP3 & CO3 & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    pose proof COM3 as (_ & _ & _ & _ & _ & _ & OWNE3 & _).
    pose proof RNL as (LB10 & _ & _ & LB1CL & _).
    pose proof (rw_cells_CB_length _ _ _ _ _ LBC3) as LBS3.
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 NDL3]. subst LBc2 Lc2 LBc1 Lc1. cbn [map blk_id fst] in ND3, NDL3.
    lazymatch type of ND3 with List.NoDup (?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: ?x8 :: ?x9 :: ?tl) =>
      pose proof (nd_split [x1; x2; x3; x4; x5; x6; x7; x8; x9] tl ND3) as (NDnew & _ & DJN) end.
    lazymatch type of NDL3 with List.NoDup (?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: ?x8 :: ?x9 :: ?tl) =>
      pose proof (nd_split [x1; x2; x3; x4; x5; x6; x7; x8; x9] tl NDL3) as (_ & _ & DJL) end.
    assert (IDS0 : forall q, q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
    { intros q [->|X]; [apply in_map_iff; exists (e_pe en, e_E en, 904); split; [reflexivity| exact INE]|].
      apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
    clear MU WM CST2 HP2 MI2 ST2 COM2 FRM3 CFR3 LOC2 OUT2 ER2 MBX2 MBY2 LE2 INCL2 OWNE2 ROOM2.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -160, bv_unsigned (e_sp en) + -120)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    (* [comment removed for export] *)
    cprefix. ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by (clear - LB10 LB1CL LO SLO SPR; lia). clear - K2 LB10. lia. }
    ths. ths. ths. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with H : stk usegs m4 (e_lo en) _ |- _ => rename H into ST4 end. lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MI4 end.
    lazymatch goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. lazymatch goal with H : wmono usegs m3 m4 |- _ => rename H into WM4 end.
    assert (HWo : Forall (wfree ((ql, LB1, 256) :: (k_rp KY, RPY, 32) :: (k_bm KY, BMY, 32) :: (k_bb KY, BBY, 16) :: (k_bi KY, dBv, 128)
                                  :: (k_rp KX, RPX, 32) :: (k_bm KX, BMX, 32) :: (k_bb KX, BBX, 16) :: (k_bi KX, hBv, 128) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ => True))
                         [(bv_unsigned (e_sp en) + -160, bv_unsigned (e_sp en) + -120)])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    assert (COM4 : pem_com libenv en st3 ((ql, LB1, 256) :: (k_rp KY, RPY, 32) :: (k_bm KY, BMY, 32) :: (k_bb KY, BBY, 16) :: (k_bi KY, dBv, 128)
                                        :: (k_rp KX, RPX, 32) :: (k_bm KX, BMX, 32) :: (k_bb KX, BBX, 16) :: (k_bi KX, hBv, 128) :: LBc)
                     ((ql, 256) :: (k_rp KY, 32) :: (k_bm KY, 32) :: (k_bb KY, 16) :: (k_bi KY, 128) :: (k_rp KX, 32) :: (k_bm KX, 32) :: (k_bb KX, 16) :: (k_bi KX, 128) :: Lc)
                     f3 m4 off (rem - 9) (rA - 8 - wA 256) (rB - wB 256) (rBig - wBig 256)).
    { eapply (com_segI en) with (EX := fun _ => True); [exact COM3| exact MU4| exact WM4| exact MI4| exact ST4| exact HWo| intros b _; exact I| unfold e_PL; cbn [disjoint_from]; clear; lia]. }
    pose proof (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX3 CST3 MU4 WM4 HWo ltac:(intros q _; exact I)) as MBX4.
    pose proof (mb_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY3 CST3 MU4 WM4 HWo ltac:(intros q _; exact I)) as MBY4.
    pose proof (er0_segI _ en _ _ _ _ _ _ _ _ _ _ _ _ ER3 MU4 WM4 CST3 (proj1 OWNE3) HWo I) as ER4.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells usegs m4 LB1 _ |- _ => rename H into LBC4 end.
    lazymatch goal with H : rw_cells usegs m4 (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC4 end.
    lazymatch goal with H : rw_cells usegs m4 (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT4 end.
    chere.
    assert (REM4 : (Z.to_nat (2 * (e_blen en - off) + 19) <= rem - 9)%nat) by (clear - REM OFF; lia).
    assert (RA6 : 6 <= rA - 8 - wA 256) by (rewrite WA0; clear - RA14; lia). assert (RB5 : 5 <= rB - wB 256) by (rewrite WB1; clear - RB6; lia).
    assert (RBIG6 : 6 * (e_blen en - e_boff en) + 32778 + 8448 <= rBig - wBig 256) by (rewrite WBIG1; clear - RBIG; lia).
    eapply (J0GP en st3 _ _ f3 m4 off (rem - 9)%nat (rA - 8 - wA 256) (rB - wB 256) (rBig - wBig 256) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l2 l3 l4 l5 l11 ta tb ql LB1 hBv dBv ljunk KX KY meth meth);
      [exact COM4| exact ER4| exact REM4| exact BOFF| exact BLEN| exact RA6| exact RB5| exact RBIG6| | split; left; reflexivity| exact LBS3| exact LBC4
      | exact MBX4| exact KXN| exact MBY4| exact KYN| | | | | exact OUT4].
    - unfold pem_loc, e_PL. exact LOC4.
    - intros b Hb. destruct Hb as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hb]]]]]]]]]; [right; unfold blk_id, mbio_blocks; cbn [fst]; rewrite KXN, KYN, !in_app_iff; cbn [In app]; clear; tauto ..| left; exact (LBE _ Hb)].
    - intros b Hb X. apply (DJN (blk_id b)); [| apply in_map; exact (PLB _ Hb)]. revert X. unfold mbio_blocks. rewrite KXN, KYN, !in_app_iff. cbn [In app]. clear. tauto.
    - intros q nm Hq X. apply (DJL q); [| apply in_map_iff; exists (q, nm); split; [reflexivity| exact (PLC _ _ Hq)]]. revert X. unfold mbio_blocks. rewrite KXN, KYN, !in_app_iff. cbn [In app]. clear. tauto.
    - apply nd_app; [| exact NDR|].
      + unfold mbio_blocks. rewrite KXN, KYN. cbn [app]. eapply Permutation_NoDup; [| exact NDnew]. apply Permutation_sym. exact (Permutation_rev _).
      + intros q0 Xq Yq. apply (DJN q0); [| apply IDS0; destruct Yq as [E|Yq]; [left; exact (eq_sym E)| right; exact Yq]]. revert Xq. unfold mbio_blocks. rewrite KXN, KYN, !in_app_iff. cbn [In app]. clear. tauto.
  Qed.
End W3.
