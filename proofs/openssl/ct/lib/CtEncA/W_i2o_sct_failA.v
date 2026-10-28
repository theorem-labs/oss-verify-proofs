(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApState ApErr ApPrim.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA UnwindA UnwindX EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame I_strcpyA W_err_newA W_err_set_debugA W_err_vsetA W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA Fr_i2o_SCT W_sct_completeA W_i2o_sctA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].
Ltac lit_addr H := lazymatch type of H with
  | ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H
  | rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H end.
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

(* [comment removed for export] *)
Definition I2O_SCT_FAIL_STACK_A : Z := IOS_FRAME + ERR_SET_ERROR_STACK.
(* [comment removed for export] *)
Definition I2O_SCT_FAIL_COST_A : Z := 1 + ERR_NEW_COST + ERR_SET_DEBUG_COST + ERR_SET_ERROR_COST.
Definition I2O_SCT_FAIL_FRAMES_A : Z := 1 + ERR_SET_ERROR_FRAMES.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_new := (E_i2o_SCT_34a3bc : uk_call 3367120 3367452 2086188).
Local Notation E_dbg := (E_i2o_SCT_34a3d8 : uk_call 3367120 3367480 2086980).
Local Notation E_err := (E_i2o_SCT_34a3ec : uk_call 3367120 3367500 2087608).
Local Notation E_cf := (E_i2o_SCT_34a408 : uk_call 3367120 3367528 2085684).

(* [comment removed for export] *)
Hypothesis STRCPY : strcpy_icontract RT.

Local Ltac ecu := unfold I2O_SCT_FAIL_STACK_A, I2O_SCT_FAIL_COST_A, I2O_SCT_FAIL_FRAMES_A, IOS_FRAME, ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK,
                         ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK, ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK,
                         ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, CRYPTO_FREE_STACK, RT_STACK in *.

(* [comment removed for export] *)
Lemma ap_preA_restock' : forall (AR' : ARun) Σ' (st' : ap_st bptr) m' OW' LB E bo' (spw : word) lo stack cost frames,
  @ap_preA AR' Σ' st' m' OW' LB E bo' spw lo 0 0 0 -> lo <= bv_unsigned spw - stack -> 0 <= cost <= rt_credit (@ar_RT AR') Σ' ->
  0 <= frames -> Z.of_nat (length (@ar_FR AR')) + frames <= Z.of_nat FRAMES_MAX ->
  @ap_preA AR' Σ' st' m' OW' LB E bo' spw lo stack cost frames.
Proof.
  intros until frames. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) H1 H2 H3 H4.
  unfold ap_preA. repeat (split; [first [assumption | lia]|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2o_sct_failA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
    (lo : Z) (K : list block) (ras : list Z) (STK CST FRMb : Z)
    (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  ap_preA Σ st m OW LB E bo sp lo STK CST FRMb -> tp = wz TP_A ->
  I2O_SCT_FAIL_STACK_A <= STK -> I2O_SCT_FAIL_COST_A <= CST -> I2O_SCT_FAIL_FRAMES_A <= FRMb ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx I2O_SCT_A (bv_unsigned ra :: ras) -> ras <> nil ->
  (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) LB -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc -> sct_complete sc = false ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  implAp (err_raise RS_i2o_notset st) Σ
         (ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K I2O_SCT_FAIL_COST_A (fun r OW' m' a0' bo' => a0' = Z_to_bv 64 (-1) /\ bo' = bo))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz I2O_SCT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until vs. intros PRE TP STKB CSTB FRMB UW CTX NE KOW KIDS HINL AL16S HX OK CPL A0.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
  pose proof AS as (_ & (CS & _) & _).
  assert (HIN : In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB)) by (apply in_or_app; right; exact HINL).
  pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu.
  unfold I2O_SCT_FAIL_STACK_A, IOS_FRAME, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in STKu.
  unfold I2O_SCT_FAIL_COST_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST in CSTu.
  unfold I2O_SCT_FAIL_FRAMES_A, ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES in FRMu.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bv_unsigned_in_range 64 s0) as S0R.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (XB0 & _ & _ & XBC & XBI). cbn [blk_addr blk_size fst snd] in *.
  pose proof CEIL as CEILu. pose proof LOSP as LOSPu. pose proof TOP as TOPu. pose proof XBC as XBCu.
  unfold BnHeapA.ACEIL, STACK_WIN in CEILu, XBCu. unfold USTACK_TOP in TOPu.
  pose proof CE1 as CE1u. pose proof CE3 as CE3u. unfold BnHeapA.ACEIL, SEGTOP_A, STACK_WIN, USTACK_TOP in CE1u, CE3u.
  assert (FLEN : (length FRM < FRAMES_MAX)%nat) by (clear - FRM0 FRMu; lia).
  intros XX Φ DD SAFE LINK.
  eapply (ios_head_cps _) with (lo := lo) (STK := STK) (OW := OW) (LB := LB) (adr := adr) (sc := sc) (vs := vs);
    [exact HEAP| exact ST| exact CEIL| clear - LOSP; lia| unfold I2O_SCT_LEN_STACK_A, IOS_FRAME; clear - STKu; plia| exact TOP| exact AL16| exact MI| exact TP| exact FLEN
    | clear - CRED CSTu; lia| exact HIN| exact AL16S| exact HX| exact OK| exact A0|].
  intros Σ1 m4 f spa g junk gj x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F1 fc1 j0 j8 j16 j24 j32 j40
         HEAP4 FRESH GEO CR1 EL1 ST4 MI4 AG4 FRL FRH HP FRS HX4 SPA32 SPAL SPAH GSZ SAVJ.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5. unfold BnHeapA.ACEIL, STACK_WIN in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEILu LO0 LOSPu STKu SPAL SPAH SPR; lia).
  (* [comment removed for export] *)
  assert (PREb : @ap_preA (push AR f 0) Σ1 st m4 OW LB E bo (Z_to_bv 64 spa) lo (STK - 160 - 16) (CST - 1) (FRMb - 1)).
  { eapply (pro_closeA Σ st m OW LB E bo sp lo STK CST FRMb f 0%nat Σ1 m4 spa 160);
      [exact PRE| exact HEAP4| exact ST4| exact MI4| exact AG4| exact CR1| exact SPA32| clear - SPAL; lia| clear - SPAH; lia| clear; lia| clear - STKu; lia| clear - CSTu; lia| clear - FRMu; lia]. }
  (* [comment removed for export] *)
  assert (UWT : forall mX, agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX -> rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
                uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { intros mX AGX FRHX. eapply (uw_call m mX spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
      [exact UW| exact AGX| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| clear - TOP; lia| exact S0R| rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRHX]. }
  assert (AGS4 : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m m4) by (eapply agree_on_mono; [exact AG4| intros a Ha; left; exact Ha]).
  pose proof (UWT m4 AGS4 FRH) as UW4.
  (* [comment removed for export] *)
  destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
  destruct (lit_okA_auto A_I2O_SCT_A 8 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
  (* [comment removed for export] *)
  assert (AXS : forall mA mB a, ax_pres LB spa LIBW_A mA mB -> spa <= a < bv_unsigned sp -> mB (wa a) = mA (wa a)).
  { intros mA mB a AX Ha. apply AX; [clear - Ha SPR CEILu LOSPu STKu SPAL LO0; lia|]. split; [| left; clear - Ha TOPu; unfold USTACK_TOP; lia].
    unfold LIBW_A. cbn [rin_ivs fst snd]. clear - Ha CEILu CE1u LOSPu STKu SPAL. lia. }
  assert (KFRL : forall mA mB, ax_pres LB spa LIBW_A mA mB -> rw_cells ctasegs mA spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk] ->
                 rw_cells ctasegs mB spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk]).
  { intros mA mB AX H. eapply rw_cells_agree; [| exact H|]; [intros wa' Hr Hc; exact (AX wa' Hr Hc)|].
    intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEILu CE1u LOSPu STKu SPAL; lia| left; clear - Ha TOPu GSZ SPAH; unfold USTACK_TOP; lia]. }
  assert (KFRH : forall mA mB, ax_pres LB spa LIBW_A mA mB -> rw_cells ctasegs mA (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells ctasegs mB (bv_unsigned sp + -16) [C8 s0; C8 ra]).
  { intros mA mB AX H. eapply rw_cells_agree; [| exact H|]; [intros wa' Hr Hc; exact (AX wa' Hr Hc)|].
    intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEILu CE1u LOSPu STKu SPAL SPAH; lia| left; clear - Ha TOPu SPAH; unfold USTACK_TOP; lia]. }
  assert (KUW : forall mA mB, ax_pres LB spa LIBW_A mA mB -> uw_chain USTACK_TOP mA spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
                uw_chain USTACK_TOP mB spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { intros mA mB AX H. eapply (uw_chain_axpres _ _ _ _ _ _ _ AX H); [clear - SPAH; lia| unfold SEGTOP_A; clear - CEILu CE1u LOSPu STKu SPAH; lia]. }
  pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
  rewrite CPL. cbn [bret].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. btaken. zstep.
  apply evt_done.
  eapply (implAp_elim (err_raise RS_i2o_notset st) Σ Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| exact EL1].
  unfold err_raise.
  eapply (implAp_post _ _ (fun (r : unit * ap_st bptr) (Σ' : rts RT) (ms' : machine_state) =>
            exists (y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (OW' : list block) (bo' : Z * Z),
              ms' = MS (mkR (Z_to_bv 64 0x33624c) (Z_to_bv 64 spa) gp (wz TP_A) y0 y1 y2 sp (Z_to_bv 64 spa) z0 z1 z2 z3 z4 z5 z6 z7
                           (Z_to_bv 64 f) (Z_to_bv 64 (adr (sc_blk sc))) s4 s5 s6 a1 s8 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) y3 y4 y5 y6)
                       F' (Z_to_bv 64 0x33624c) fc' None m' (seg_rom ctasegs)
              /\ @ap_preA (push AR f 0) Σ' (snd r) m' OW' LB E bo' (Z_to_bv 64 spa) lo 0 0 0
              /\ ax_pres LB spa LIBW_A m4 m' /\ rt_credit RT Σ1 - 13 <= rt_credit RT Σ' /\ blocks_kept K (snd r) OW' m4 m' /\ bo' = bo)).
  { (* [comment removed for export] *)
    eapply implAp_abind.
    { pose proof (@ERR_new_walkA (push AR f 0) UK BE bo) as W1. unfold ap_stmtA in W1.
      eapply W1; [eapply ap_preA_weaken; [exact PREb| ecu; clear - STKu; lia| ecu; clear - CSTu CRED; lia| ecu; clear - FRMu FRM0; lia]
                | reflexivity| rewrite ESPA; exact UW4| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_new CTX)| apply cons_ne| reflexivity| exact KOW| exact KIDS]. }
    intros r1 Σa ms1 PO1. cbv beta in PO1.
    destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & Fa & fca & mA & OWa & boa & -> & PREa & AXa & CRa & BKa & EBOa). subst boa.
    rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x33621c) by (clear; lia).
    pose proof (KFRL _ _ AXa FRL) as FRLa. pose proof (KFRH _ _ AXa FRH) as FRHa. pose proof (KUW _ _ AXa UW4) as UWa. clear FRL FRH.
    assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
    { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
    pose proof PREa as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & _ & _). rewrite ESPA in STa.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU1. pose proof (wmono_refl ctasegs mA) as WM1.
    eapply implAp_abind.
    { (* [comment removed for export] *)
      apply implAp_from_evt. unfold MallocRep.wz. do 6 zstep. apply evt_done.
      pose proof (@ERR_set_debug_walkA (push AR f 0) UK BE STRCPY RS_i2o_notset A_CT_OCT_C_A A_I2O_SCT_A bo fs fk ns nk LF LN) as W2. unfold ap_stmtA in W2.
      eapply W2; [eapply (ap_preA_restock' (push AR f 0)); [exact PREa| rewrite ESPA; ecu; clear - LOSPu STKu SPAL; lia| ecu; cbn [ar_RT ar_FR push amb length]; clear - CRED CSTu CR1 CRa; lia| ecu; clear; lia| ecu; cbn [ar_RT ar_FR push amb length]; clear - FRM0 FRMu; lia]
                | reflexivity| rewrite ESPA; exact UWa| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_dbg CTX)| apply cons_ne
                | unfold A_CT_OCT_C_A, A_I2O_SCT_A, MallocRep.wz; cbn [rs_line RS_i2o_notset]; repeat split; reflexivity| exact (proj1 BKa)| exact KIDS1]. }
    intros r2 Σb ms2 PO2. cbv beta in PO2.
    destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & Fb & fcb & mB & OWb & bob & -> & PREb2 & AXb & CRb & BKb & EBOb). subst bob.
    rewrite ESPA in AXb. cbn [ar_RT push amb] in CRb. rewrite (ret_pc_even 0x336238) by (clear; lia).
    pose proof (KFRL _ _ AXb FRLa) as FRLb. pose proof (KFRH _ _ AXb FRHa) as FRHb. pose proof (KUW _ _ AXb UWa) as UWb. clear FRLa FRHa UWa.
    assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
    { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
    pose proof PREb2 as (_ & _ & _ & _ & STb & _ & _ & _ & _ & MIb & _ & _). rewrite ESPA in STb.
    pose proof (munch_refl (@nil (Z * Z)) mB) as MU2. pose proof (wmono_refl ctasegs mB) as WM2.
    (* [comment removed for export] *)
    eapply implAp_mono.
    { apply implAp_from_evt. unfold MallocRep.wz. do 4 zstep. apply evt_done.
    pose proof (@ERR_set_error_closedA (push AR f 0) UK BE RS_i2o_notset 50 106 bo) as W3. unfold ERR_set_error_specA, ap_stmtA in W3.
    eapply W3; [eapply (ap_preA_restock' (push AR f 0)); [exact PREb2| rewrite ESPA; ecu; clear - LOSPu STKu SPAL; lia| ecu; cbn [ar_RT ar_FR push amb length]; clear - CRED CSTu CR1 CRa CRb; lia| ecu; clear; lia| ecu; cbn [ar_RT ar_FR push amb length]; clear - FRM0 FRMu; lia]
              | reflexivity| rewrite ESPA; exact UWb| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_err CTX)| apply cons_ne
              | unfold ERR_LIB_SYS, MallocRep.wz; cbn [rs_code RS_i2o_notset]; unfold ERR_LIB_CT; repeat split; first [reflexivity | (clear; lia)]| exact (proj1 BKb)| exact KIDS2]. }
    intros r3 Σc ms3 PO3. cbv beta in PO3.
    destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & PREc & AXc & CRc & BKc & EBOc).
    rewrite ESPA in AXc. cbn [ar_RT push amb] in CRc. rewrite (ret_pc_even 0x33624c) by (clear; lia).
    do 17 eexists. exists mC, OWc, boc. split; [reflexivity|]. split; [exact PREc|].
    split; [eapply ax_pres_trans; [exact AXa| eapply ax_pres_trans; [exact AXb| exact AXc]]|].
    split; [unfold ERR_NEW_COST in CRa; unfold ERR_SET_DEBUG_COST in CRb; unfold ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST in CRc; clear - CRa CRb CRc; lia|]. split; [| exact EBOc].
    split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
    intros a Ha Hin. rewrite (proj2 (proj2 BKc) a Ha Hin), (proj2 (proj2 BKb) a Ha Hin), (proj2 (proj2 BKa) a Ha Hin). reflexivity. }
  (* [comment removed for export] *)
  intros r3 Σc ms3 PO3. cbv beta in PO3.
  destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & PREc & AXc & CRc & BKc & EBOc). subst boc.
  pose proof PREc as (HEAPc & ASc & _ & _ & STc & _ & _ & _ & _ & MIc & _ & _). rewrite ESPA in STc. pose proof ASc as (_ & (CSc & _) & _).
  intros X2 Φ2 D2 SAFE2 LINK2.
  pose proof (munch_refl (@nil (Z * Z)) mC) as MU3. pose proof (wmono_refl ctasegs mC) as WM3.
  apply cps_from_evt'. unfold MallocRep.wz.
  (* [comment removed for export] *)
  do 6 zstep.
  apply evt_done. eapply cps_step_same.
  { eapply (@CRYPTO_free_null_cpsA (push AR f 0) UK BE) with (lo := lo) (OW := OWc) (LB := LB) (ras := bv_unsigned ra :: ras); rewrite ?ESPA; try reflexivity.
    - exact HEAPc.
    - exact STc.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    - ecu. clear - LOSPu STKu SPAL. lia.
    - clear - TOP SPAH. unfold USTACK_TOP in *. lia.
    - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
    - exact MIc.
    - exact CSc.
    - exact (KUW _ _ AXc UW4).
    - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_cf CTX). }
  intros msF POF. destruct POF as (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & FF & fcF & mF & -> & MIF & STF & HEAPF & AGF').
  rewrite ?ESPA in STF, AGF'. rewrite (ret_pc_even 0x336268) by (clear; lia). unfold MallocRep.wz.
  pose proof (KFRL _ _ AXc FRL) as FRLc. pose proof (KFRH _ _ AXc FRH) as FRHc.
  apply (rw_cells_agree _ _ _ _ _ AGF') in FRLc; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; clear - Hxa TOPu GSZ SPAH; unfold USTACK_TOP; lia].
  apply (rw_cells_agree _ _ _ _ _ AGF') in FRHc; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; clear - Hxa TOPu SPAH; unfold USTACK_TOP; lia].
  pose proof (munch_refl (@nil (Z * Z)) mF) as MU5. pose proof (wmono_refl ctasegs mF) as WM5.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  apply evt_done. change (Z_to_bv 64 3367600) with (wz IOS_EXIT).
  eapply (@ios_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAPF| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STF| exact CEIL| clear - LOSPu STKu SPAL; lia
    | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIF| exact FRLc| exact FRHc| reflexivity|].
  intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
  eapply (implAp_elim (ARet r3) Σc Σ' _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| exact LIVE'].
  apply implAp_ret. rewrite (v_addiw0_int (-1)) by (clear; lia).
  eapply (epi_closeA (fun r OW' m' a0' bo' => a0' = Z_to_bv 64 (-1) /\ bo' = bo) r3) with (spw := Z_to_bv 64 spa) (m1 := m4) (C1 := 13) (mk := mC) (STACK := STK) (FRAMES := FRMb); rewrite ?ESPA.
  - eapply ap_preA_weaken; [exact PRE| clear; lia| clear - CSTu CRED; unfold I2O_SCT_FAIL_COST_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST; lia| clear - FRM0; lia].
  - exact AG4.
  - exact CR1.
  - clear - SPAH. lia.
  - exact PREc.
  - exact AXc.
  - exact CRc.
  - exact BKc.
  - exact KOW.
  - clear - CSTu. unfold I2O_SCT_FAIL_COST_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST. lia.
  - exact HEAP'.
  - exact CR'.
  - exact ST'.
  - exact MI'.
  - eapply agree_on_trans; [exact AGF'| exact AG'].
  - split; reflexivity.
Qed.

End WithRT.
