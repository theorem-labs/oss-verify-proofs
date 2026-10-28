(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame ApErrKitA ApErrKitA2 W_locks W_tlocalA Fr_init_base W_get_stateA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_err_clear_error.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PW := OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP.W_err_clear_error.
Module EK := OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP.ApErrKit.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac pstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.   (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

(* [comment removed for export] *)
Ltac es_store WR :=
  let HS := fresh "HS" in let ESn := fresh "ESn" in
  destruct WR as [HS ESn]; unfold MallocRep.wz, ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP in HS, ESn; step;
  lazymatch type of ESn with es_raw (write_to_mem ?m ?a ?bs) _ _ =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a2 ?bs2) _) =>
      first [ constr_eq a a2; constr_eq bs bs2
            | replace (write_to_mem m a2 bs2) with (write_to_mem m a bs) by (unfold wa; f_equal; first [reflexivity | word_eq_tac | vm_compute; reflexivity]) ]
    end;
    try match goal with H : es_raw m _ _ |- _ => clear H end
  end;
  store_done; rename ESn into ES;
  (* [comment removed for export] *)
  try lazymatch goal with
  | ES : es_raw _ _ ?g, GL : g_len _ |- _ =>
      let GLn := fresh "GLn" in
      assert (GLn : g_len g)
        by (let H := fresh in pose proof GL as H; unfold CtRepP.ApErrKit.g_len in H |- *;
            cbn [CtRepP.ApErrKit.g_fl CtRepP.ApErrKit.g_ma CtRepP.ApErrKit.g_bu CtRepP.ApErrKit.g_da CtRepP.ApErrKit.g_ds CtRepP.ApErrKit.g_df
                 CtRepP.ApErrKit.g_fi CtRepP.ApErrKit.g_li CtRepP.ApErrKit.g_fu CtRepP.ApErrKit.g_top CtRepP.ApErrKit.g_bot
                 CtRepP.ApErrKit.set_g_fl CtRepP.ApErrKit.set_g_ma CtRepP.ApErrKit.set_g_bu CtRepP.ApErrKit.set_g_da CtRepP.ApErrKit.set_g_ds
                 CtRepP.ApErrKit.set_g_df CtRepP.ApErrKit.set_g_fi CtRepP.ApErrKit.set_g_li CtRepP.ApErrKit.set_g_fu CtRepP.ApErrKit.set_g_top
                 CtRepP.ApErrKit.set_g_bot] in H |- *;
            rewrite ?upd_length in H; rewrite ?upd_length; exact H);
      clear GL; rename GLn into GL
  end.

Definition ECE_STK : Z := 96 + GET_STATE_STACK.    (* [comment removed for export] *)
Definition ECE_RA1 : Z := 0x1fe874.               (* [comment removed for export] *)
Definition ECE_HEAD : Z := 0x1fe894.              (* [comment removed for export] *)
Definition ECE_MID : Z := 0x1fe934.               (* [comment removed for export] *)
Definition ECE_BNE : Z := 0x1fe9f8.               (* [comment removed for export] *)
Definition ECE_FREE1_RA : Z := 0x1fe9b4.
Definition ECE_FREE2_RA : Z := 0x1fe9e4.
Definition ECE_LIT : Z := 0x49a00.                (* [comment removed for export] *)

Local Notation E_free1 := (E_err_clear_1f9ba4 : uk_call 0x1fe828 0x1fe9b4 0x1fd334).     (* [comment removed for export] *)
Local Notation E_free2 := (E_err_clear_1f9be4 : uk_call 0x1fe828 0x1fe9e4 0x1fd334).     (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  (* [comment removed for export] *)
  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo : Z).
  Hypothesis IDS : ids_ok E st.
  Hypothesis CEIL : ACEIL <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ECE_STK.
  Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
  Hypothesis AL16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESB : e_es E + 904 < 2 ^ 63.
  Hypothesis EES16 : e_es E mod 16 = 0.   (* [comment removed for export] *)
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists mI, ap_state st mI OW E bo0.
  Hypothesis DF0 : dflags_ok st.
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Variables (COST : Z).
  Hypothesis COST1 : 1 <= COST.
  Hypothesis FRM : Z.of_nat (length FR) + 0 <= Z.of_nat FRAMES_MAX.
  (* [comment removed for export] *)
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ERR_CLEAR_ERROR (bv_unsigned ra :: ras).

  Local Notation W2 := ([(bv_unsigned sp - ECE_STK, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Local Notation SB := (seg_baseA m OW st E bo0 LB K (bv_unsigned sp) Σ) (only parsing).
  Local Notation clr := PW.clr (only parsing).
  Local Notation rms := (PW.rms st) (only parsing).
  Local Notation FINAL := (PW.FINAL st) (only parsing).
  Let POST := ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K COST
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0 /\ snd r = st_of_ls (ls_of_st (snd r))).
  Definition ece_frame : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at_pc (pc : Z) (i : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mc : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 (e_es E)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 ECE_LIT) x19 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat i * 8)) (Z_to_bv 64 (Z.of_nat i * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) x25 x26 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mc (seg_rom ctasegs).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition round_ok (i n : nat) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mb mc : mem),
      SB 1 Σc (rms i OW) mb -> munch W2 mb mc -> wmono ctasegs mb mc ->
      rw_cells ctasegs mc (bv_unsigned sp + -96) ece_frame -> stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
      es_raw mc (e_es E) (g_of (clr i st) (badr OW)) ->
      implAp (abind (err_clear_slots i n) PW.FIN (clr i st)) Σc POST
        (at_pc ECE_HEAD i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 F fc mc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma I16 : forall i, (i < 16)%nat -> (i < length (as_file st))%nat /\ (i < length (as_func st))%nat /\ (i < length (as_data st))%nat /\ length (as_dflags st) = length (as_data st).
  Proof. intros i Hi. pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7). unfold ERR_NUM in L1, L2, L3, L4, L5, L6, L7. clear - Hi L1 L2 L3 L4 L5 L6 L7. repeat split; lia. Qed.

  Lemma fin_dsubA : forall i q k, get_data i FINAL = Some (q, k) -> get_data i st = Some (q, k).
  Proof.
    intros i q k Hd. unfold PW.FINAL in Hd. rewrite PW.get_data_tb in Hd.
    pose proof (PW.clr_shape 16 st SH) as (_ & _ & L3' & _). unfold ERR_NUM in L3'.
    assert (Hi : (i < 16)%nat).
    { destruct (Nat.lt_ge_cases i 16) as [X|X]; [exact X|]. rewrite PW.get_data_over in Hd by (clear - X L3'; lia). discriminate. }
    destruct (PW.clr_lo 16 st i SH DF0 ltac:(unfold ERR_NUM; clear; lia) Hi) as (_ & _ & _ & _ & _ & [[GD _]|(b & GD & GD0 & _)]); rewrite GD in Hd; [discriminate|].
    injection Hd as ->. exact GD0.
  Qed.

  Lemma fin_dflagsA : dflags_ok FINAL.
  Proof.
    intros i Hd. unfold PW.FINAL in *. rewrite PW.get_data_tb in Hd. rewrite PW.get_dflags_tb.
    pose proof (PW.clr_shape 16 st SH) as (_ & _ & L3 & L4 & _). unfold ERR_NUM in L3, L4.
    destruct (Nat.lt_ge_cases i 16) as [Hi|Hi]; [|rewrite PW.get_dflags_over by (clear - Hi L3 L4; lia); reflexivity].
    destruct (PW.clr_lo 16 st i SH DF0 ltac:(unfold ERR_NUM; clear; lia) Hi) as (_ & _ & _ & _ & _ & [[GD GF]|(b & GD & _ & GF)]); [rewrite GF; reflexivity|rewrite GD in Hd; discriminate].
  Qed.

  Lemma fin_data_slotsA : forall i q k, get_data i FINAL = Some (q, k) -> In (q, badr (rms 16 OW) q, k) (rms 16 OW) /\ 0 < badr (rms 16 OW) q.
  Proof.
    intros i q k Hd. pose proof (fin_dsubA i q k Hd) as GD0. rewrite (PW.badr_rms_data st OW E IDS 16 i q k GD0).
    exact (PW.slot_data_in sp st OW E IDS OD 16 i q k GD0).
  Qed.

  Lemma rest_rmsA : forall k mX, ap_restA mX OW E bo0 (as_cnf st) -> ap_restA mX (rms k OW) E bo0 (as_cnf st).
  Proof.
    induction k as [|k IH]; intros mX HR; [exact HR|]. cbn [PW.rms]. apply rest_lremoveA; [apply rest_lremoveA; [apply IH; exact HR|]|].
    - intros q n G. split; [eapply file_not_rest; [exact IDS|exact G]|eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact G]].
    - intros q n G. split; [eapply func_not_rest; [exact IDS|exact G]|eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact G]].
  Qed.

  Lemma fin_stateA : forall m9, ap_restA m9 OW E bo0 (as_cnf st) -> es_raw m9 (e_es E) (g_of FINAL (badr OW)) -> ap_state FINAL m9 (rms 16 OW) E bo0.
  Proof.
    intros m9 AR9 ES. pose proof (PW.fin_nf st SH DF0) as NF. apply ap_state_joinA.
    - unfold PW.FINAL. rewrite PW.tb_cnf. rewrite (proj2 (proj2 (PW.clr_proj 16 st))). apply rest_rmsA. exact AR9.
    - exact (PW.fin_shape st SH).
    - rewrite (g_of_adr_ext FINAL (badr (rms 16 OW)) (badr OW)); [exact ES| | |].
      + rewrite NF. cbn [as_file st_of_ls ls_of_st]. intros p n Hin. apply repeat_spec in Hin. discriminate.
      + rewrite NF. cbn [as_func st_of_ls ls_of_st]. intros p n Hin. apply repeat_spec in Hin. discriminate.
      + intros p n Hin. destruct (PW.as_data_in FINAL p n Hin) as (i & _ & Gi). eapply (PW.badr_rms_data st OW E IDS). exact (fin_dsubA i p n Gi).
    - rewrite NF. cbn [as_file st_of_ls ls_of_st]. apply Forall_forall. intros o Ho. apply repeat_spec in Ho. subst o. exact I.
    - rewrite NF. cbn [as_func st_of_ls ls_of_st]. apply Forall_forall. intros o Ho. apply repeat_spec in Ho. subst o. exact I.
    - apply PW.optb_ok_of_slots. exact fin_data_slotsA.
  Qed.

  Lemma fin_dataA : forall m9, data_cells m9 OW st -> data_cells m9 (rms 16 OW) FINAL.
  Proof.
    intros m9 DC9. apply (data_cells_subA m9 (rms 16 OW) st).
    - eapply data_cells_OWA; [exact DC9|]. intros i q k Hd. eapply (PW.badr_rms_data st OW E IDS). exact Hd.
    - intros i q k Hd. exists i. apply fin_dsubA. exact Hd.
    - exact fin_dflagsA.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LOSP : lo <= bv_unsigned sp.
  Proof. clear - LO. unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LO. lia. Qed.
  Lemma TOP' : bv_unsigned sp <= USTACK_TOP.
  Proof. clear - TOP. lia. Qed.

  (* [comment removed for export] *)
  Lemma HW2 : forall (L : list block) (P : bptr -> Prop), In (p_es E, e_es E, 904) L -> P (p_es E) ->
    Forall (segW (L ++ LB) lo (bv_unsigned sp) P) W2.
  Proof.
    intros L P HIN HP. constructor; [left; cbn; clear - LO; unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia|]. constructor; [| constructor].
    right; right. exists (p_es E), (e_es E), 904. split; [apply in_app_iff; left; exact HIN|]. split; [exact HP | cbn; clear; lia].
  Qed.

  Lemma es_seg_writable : seg_writableA OW st E K (p_es E).
  Proof. exact (es_writableA OW st E bo0 K IDS AS0 KIDS). Qed.

  (* [comment removed for export] *)
  Lemma sb_munch : forall c Σc OWc mb mc, SB c Σc OWc mb -> munch W2 mb mc -> wmono ctasegs mb mc -> SB c Σc OWc mc.
  Proof.
    intros c Σc OWc mb mc SBb MU WM. pose proof (seg_baseA_es _ _ _ _ _ _ _ _ _ _ _ _ _ SBb) as IESc.
    eapply (seg_baseA_munch m OW st E bo0 LB K (bv_unsigned sp) lo Σ CEIL LOSP TOP'); [exact SBb|exact MU|exact WM|].
    apply HW2; [exact IESc|]. split; [exact es_seg_writable|]. change (p_es E) with (blk_id (p_es E, e_es E, 904)). apply in_map. exact IESc.
  Qed.

  (* [comment removed for export] *)
  Lemma sb_store_data : forall c Σc OWc mc m1 i0 pd nd x y junk',
    SB c Σc OWc mc -> get_data i0 st = Some (pd, nd) -> In (pd, badr OW pd, nd) OWc ->
    lo <= x -> y <= bv_unsigned sp ->
    munch [(x, y); (badr OW pd, badr OW pd + 1)] mc m1 -> wmono ctasegs mc m1 ->
    rw_cells ctasegs m1 (badr OW pd) [CB (Z.to_nat nd) junk'] -> SB c Σc OWc m1.
  Proof.
    intros until junk'. intros SBc GD HIN LX YS MU WM HD.
    pose proof SBc as (HEAP & AX & HAR & RB & DC & DIN & KP & KOWc & IESc & CR).
    pose proof (proj1 (proj1 DC i0 pd nd GD)) as ND1.
    assert (HINL : In (pd, badr OW pd, nd) (OWc ++ LB)) by (apply in_app_iff; left; exact HIN).
    assert (HW : forall P : bptr -> Prop, P pd -> Forall (segW (OWc ++ LB) lo (bv_unsigned sp) P) [(x, y); (badr OW pd, badr OW pd + 1)]).
    { intros P HP. constructor; [left; cbn; clear - LX YS; lia|]. constructor; [| constructor]. right; right. exists pd, (badr OW pd), nd.
      split; [exact HINL|]. split; [exact HP | cbn; clear - ND1; lia]. }
    destruct (seg_closeA Σc OWc LB _ mc m1 lo (bv_unsigned sp) (fun p => p = pd) HEAP CEIL LOSP TOP' MU WM (HW _ eq_refl)) as [HEAP1 AX1].
    { intros p A n HIN' ->. pose proof (AH_nodup _ _ _ _ HEAP) as ND. destruct (badr_size_unique (OWc ++ LB) pd A n (badr OW pd) nd ND HIN' HINL) as [-> ->]. exact HIN. }
    split; [exact HEAP1|]. split; [eapply ax_pres_trans; [exact AX|exact AX1]|].
    split; [eapply (rest_of_segA Σc OWc LB _ mc m1); [exact HAR|exact HEAP|exact RB|exact CEIL|exact MU|apply HW; eapply data_not_rest; [exact IDS|exact GD]]|].
    split; [exact RB|].
    split; [eapply (data_cells_store1A Σc OWc LB mc m1 OW st lo (bv_unsigned sp)); [exact DC|exact DIN|exact HINL|exact ND1|exact HEAP|exact CEIL|exact LX|exact YS|exact MU|exact HD]|].
    split; [exact DIN|].
    split; [eapply kept_trans; [exact KP|]; eapply (kept_of_munchA Σc OWc LB _ mc m1 K lo); [exact HEAP|intros b Hb; apply in_app_iff; left; apply KOWc; exact Hb|exact CEIL|exact MU|];
           apply HW; eapply K_not_es; [exact KIDS|]; eapply es_ids_data; exact GD|].
    split; [exact KOWc|]. split; [exact IESc|exact CR].
  Qed.

  (* [comment removed for export] *)
  Lemma sb_free_file : forall c Σc Σ' i mb mc SP',
    (i < 16)%nat -> SB c Σc (rms i OW) mb ->
    agree_on (aclient_addr (lremove (get_file i st) (rms i OW) ++ LB) SP') mb mc -> SP' <= bv_unsigned sp ->
    AHEAP Σ' (lremove (get_file i st) (rms i OW)) LB mc -> rt_credit RT Σ' = rt_credit RT Σc ->
    SB c Σ' (lremove (get_file i st) (rms i OW)) mc.
  Proof.
    intros c Σc Σ' i mb mc SP' Hi SBb AG HSP HEAP' CR'.
    eapply (seg_baseA_free m OW st E bo0 LB K (bv_unsigned sp) Σ); [exact SBb| |exact AG|exact HSP|exact HEAP'|exact CR'].
    intros q n GF. split; [|split].
    - change q with (blk_id (q, badr OW q, n)). apply in_map. exact (proj1 (PW.slot_file_in sp st OW E IDS OF i q n Hi GF)).
    - split; [eapply file_not_rest; [exact IDS|exact GF]|]. split; [intros j q' k' Hd EQ; subst q'; exact (ids_file_data_ne E st i j q n q k' IDS GF Hd eq_refl)|].
      eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF].
    - eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF].
  Qed.

  Lemma sb_free_func : forall c Σc Σ' i mb mc SP',
    (i < 16)%nat -> SB c Σc (lremove (get_file i st) (rms i OW)) mb ->
    agree_on (aclient_addr (lremove (get_func i st) (lremove (get_file i st) (rms i OW)) ++ LB) SP') mb mc -> SP' <= bv_unsigned sp ->
    AHEAP Σ' (lremove (get_func i st) (lremove (get_file i st) (rms i OW))) LB mc -> rt_credit RT Σ' = rt_credit RT Σc ->
    SB c Σ' (rms (S i) OW) mc.
  Proof.
    intros c Σc Σ' i mb mc SP' Hi SBb AG HSP HEAP' CR'. change (rms (S i) OW) with (lremove (get_func i st) (lremove (get_file i st) (rms i OW))).
    eapply (seg_baseA_free m OW st E bo0 LB K (bv_unsigned sp) Σ); [exact SBb| |exact AG|exact HSP|exact HEAP'|exact CR'].
    intros q n GN. split; [|split].
    - change q with (blk_id (q, badr OW q, n)). apply in_map. exact (proj1 (PW.slot_func_in sp st OW E IDS OFN i q n Hi GN)).
    - split; [eapply func_not_rest; [exact IDS|exact GN]|]. split; [intros j q' k' Hd EQ; subst q'; exact (ids_func_data_ne E st i j q n q k' IDS GN Hd eq_refl)|].
      eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN].
    - eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN].
  Qed.

  (* [comment removed for export] *)
  Lemma es_in_rms : forall k, In (p_es E, e_es E, 904) (rms k OW).
  Proof. intros k. exact (PW.es_in_rms sp st OW E IDS IES k). Qed.
  Lemma es_in_rms_file : forall i, In (p_es E, e_es E, 904) (lremove (get_file i st) (rms i OW)).
  Proof.
    intros i. apply lremove_keep; [apply es_in_rms|]. intros q k GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ece_finish : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σc : rts RT) (mb m9 : mem),
    SB 1 Σc (rms 16 OW) mb -> munch W2 mb m9 -> wmono ctasegs mb m9 ->
    es_raw m9 (e_es E) (g_of FINAL (badr OW)) -> stk ctasegs m9 lo (bv_unsigned sp) -> mem_inv ctasegs m9 ->
    POST (tt, FINAL) Σc
         (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m9 (seg_rom ctasegs)).
  Proof.
    intros until m9. intros SBb MU WM ES ST MI.
    pose proof (sb_munch _ _ _ _ _ SBb MU WM) as SB9.
    destruct SB9 as (HEAP9 & AX9 & AR9 & RB9 & DC9 & DIN9 & KP9 & KOW9 & IES9 & CR9).
    pose proof (fin_stateA m9 AR9 ES) as AS9. pose proof (fin_dataA m9 DC9) as DC9'.
    pose proof (PW.fin_ids sp st E IDS SH) as IDS9. pose proof (PW.fin_kids sp st E SH K KIDS) as KID9. pose proof (PW.fin_nf st SH DF0) as NF.
    revert AS9 DC9' IDS9 KID9 NF. generalize FINAL. intros FIN' AS9 DC9' IDS9 KID9 NF.
    set (OW16 := rms 16 OW) in *. clearbody OW16.
    unfold POST, ap_postA.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m9, OW16, bo0.
    split; [reflexivity|].
    split.
    { unfold ap_preA. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS9|]. split; [exact DC9'|]. split; [exact ST|]. split; [exact CEIL|].
      split; [pose proof LOSP as X; clear - X; lia|]. split; [exact TOP|]. split; [exact AL16|]. split; [exact MI|].
      split; [pose proof (af_credit_nonneg RT AF Σc m9 (AH_art _ _ _ _ HEAP9)) as X; clear - X; lia|]. split; [clear; lia|]. clear - FRM. lia. }
    split; [exact AX9|].
    split; [clear - CR9 COST1; lia|].
    split; [| cbn [snd]; split; [reflexivity | exact NF]].
    split; [exact KOW9|]. split; [exact KID9 | exact KP9].
  Qed.

  Local Ltac g_cbn := cbn [EK.g_fl EK.g_ma EK.g_bu EK.g_da EK.g_ds EK.g_df EK.g_fi EK.g_li EK.g_fu EK.g_top EK.g_bot
                           EK.set_g_fl EK.set_g_ma EK.set_g_bu EK.set_g_da EK.set_g_ds EK.set_g_df EK.set_g_fi EK.set_g_li EK.set_g_fu EK.set_g_top EK.set_g_bot EK.g_of].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ece_body2 : forall (i n : nat) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mb mc : mem),
    (i < 16)%nat ->
    SB 1 Σc (rms i OW) mb -> munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) ece_frame ->
    stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of (ecd i (clr i st)) (badr OW)) ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y26 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σ' : rts RT) (mb' mc' : mem),
        SB 1 Σ' (rms (S i) OW) mb' -> munch W2 mb' mc' -> wmono ctasegs mb' mc' ->
        rw_cells ctasegs mc' (bv_unsigned sp + -96) ece_frame -> stk ctasegs mc' lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc' ->
        es_raw mc' (e_es E) (g_of (clr (S i) st) (badr OW)) ->
        implAp (abind (err_clear_slots (S i) n) PW.FIN (clr (S i) st)) Σ' POST
          (at_pc ECE_BNE (S i) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y26 y28 y29 y30 y31 F' fc' mc')) ->
    implAp (ofree (option_map fst (get_file i st)) (ofree (option_map fst (get_func i st)) (abind (err_clear_slots (S i) n) PW.FIN (clr (S i) st)))) Σc POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 (e_es E)) (Z_to_bv 64 (e_es E + 4 * Z.of_nat i)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ECE_LIT) x19 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat i * 8)) (Z_to_bv 64 (Z.of_nat i * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128)
               (Z_to_bv 64 (e_es E + 8 * Z.of_nat i)) x26 s11 x28 x29 x30 x31)
          F (wz ECE_MID) fc None mc (seg_rom ctasegs)).
      (* [comment removed for export] *)
  Proof using AL16 AS0 BE CEIL COST CTX EES16 EESB EESP IDS IES KIDS LO OF OFN SH TOP UW.
    intros until mc. intros Hi SBb MU WM FR ST MI ES KONT.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBb) as HEAPb.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu, MU.
    assert (Hi' : (i < ERR_NUM)%nat) by (unfold ERR_NUM; exact Hi).
    set (X := clr i st) in *.
    pose proof (PW.shape_mid st SH i) as SHY. fold X in SHY.
    assert (GL : g_len (g_of (ecd i X) (badr OW))) by (apply g_len_of; exact SHY).
    destruct (PW.slot_i st i Hi) as (XF & XN & XD & XG). fold X in XF, XN, XD, XG.
    destruct (PW.slot_i_mid st i) as (YF & YN & YF' & YN' & _). fold X in YF, YN, YF', YN'. rewrite XF in YF, YF'. rewrite XN in YN, YN'.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    pose proof (es_in_rms i) as IESi. assert (IESi' : In (p_es E, e_es E, 904) (rms i OW ++ LB)) by (apply in_app_iff; left; exact IESi).
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IESi') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IESi' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IESi') as (_ & _ & EESC & EESI & _).
    unfold ece_frame in FR. unfold ECE_MID, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    es_store (es_wr_ma mc (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m1.
    (* [comment removed for export] *)
    es_store (es_wr_fl m1 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m2.
    (* [comment removed for export] *)
    es_store (es_wr_bu m2 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m3.
    (* [comment removed for export] *)
    es_store (es_wr_li m3 (e_es E) _ i (Z_to_bv 64 (-1)) ES GL Hi'). name_mem m4.
    (* [comment removed for export] *)
    pose proof (es_rd_fi m4 (e_es E) _ i (wa (e_es E + 576 + 8 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. zstep. clear RD.
    setreg 10 (Z_to_bv 64 (optr (badr OW) (get_file i st))) ltac:(g_cbn; rewrite nth_wl_optr, YF'; reflexivity).
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof (sb_munch _ _ _ _ _ SBb MU WM) as SB4.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB4) as HEAP4. pose proof (seg_baseA_crypto_statics _ _ _ _ _ _ _ _ _ _ _ _ _ SB4) as CS4.
    clear MU WM ACCE.
    apply evt_done.
    eapply CRYPTO_free_opt_walkAp with (lo := lo) (od := get_file i st) (adr := badr OW) (OW := rms i OW) (LB := LB);
      [exact HEAP4 | | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact CS4 | reflexivity
      | rewrite ESP; uw_call_ax_tac m 96 UW (seg_baseA_ax _ _ _ _ _ _ _ _ _ _ _ _ _ SB4) FR;
          [clear; lia | pose proof (AH_ceil _ _ _ _ (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB4)) as (Cq1 & _ & _); unfold SEGTOP_A in *; clear - LOu CEIL Cq1; unfold BnHeapA.ACEIL in *; lia
          | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free1 CTX) | ].
    { destruct (get_file i st) as [[qf nf]|] eqn:GF; [|exact I]. exact (proj1 (PW.slot_file_in sp st OW E IDS OF i qf nf Hi GF)). }
    intros Σ5 ms5 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F5 & fc5 & m5 & -> & MI5 & ST5 & AG5 & CR5 & HEAP5).
    rewrite (ret_pc_even ECE_FREE1_RA) by (clear; unfold ECE_FREE1_RA; lia). unfold ECE_FREE1_RA.
    (* [comment removed for export] *)
    pose proof (sb_free_file 1 Σc Σ5 i m4 m5 _ Hi SB4 AG5 ltac:(clear; lia) HEAP5 CR5) as SB5.
    apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG5|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [apply in_app_iff; left; apply es_in_rms_file|cbn; clear - Ha; lia]. }
    pose proof (AH_ceil _ _ _ _ HEAP5) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3.
    clear AG5 SB4 HEAP4 CS4 MI ST SBb HEAPb C1 C2 C3 OFFE EESC EESI. rename ST5 into ST. rename MI5 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m5) as MU3. pose proof (wmono_refl ctasegs m5) as WM3.
    pose proof (es_in_rms_file i) as IES5. assert (IES5' : In (p_es E, e_es E, 904) (lremove (get_file i st) (rms i OW) ++ LB)) by (apply in_app_iff; left; exact IES5).
    ablock HEAP5 IES5' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP5 IES5') as (_ & _ & EESC & EESI & _).
    apply implAp_from_evt.
    es_store (es_wr_fi m5 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m6.
    pose proof (es_rd_fu m6 (e_es E) _ i (wa (e_es E + 768 + 8 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. zstep. clear RD.
    setreg 10 (Z_to_bv 64 (optr (badr OW) (get_func i st))) ltac:(g_cbn; rewrite nth_wl_optr, YN'; reflexivity).
    zstep. zstep. zstep.
    pose proof (sb_munch _ _ _ _ _ SB5 MU3 WM3) as SB6.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB6) as HEAP6. pose proof (seg_baseA_crypto_statics _ _ _ _ _ _ _ _ _ _ _ _ _ SB6) as CS6.
    clear MU3 WM3 ACCE.
    apply evt_done.
    eapply CRYPTO_free_opt_walkAp with (lo := lo) (od := get_func i st) (adr := badr OW) (OW := lremove (get_file i st) (rms i OW)) (LB := LB);
      [exact HEAP6 | | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact CS6 | reflexivity
      | rewrite ESP; uw_call_ax_tac m 96 UW (seg_baseA_ax _ _ _ _ _ _ _ _ _ _ _ _ _ SB6) FR;
          [clear; lia | pose proof (AH_ceil _ _ _ _ (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB6)) as (Cq1 & _ & _); unfold SEGTOP_A in *; clear - LOu CEIL Cq1; unfold BnHeapA.ACEIL in *; lia
          | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free2 CTX) | ].
    { destruct (get_func i st) as [[qn nn]|] eqn:GN; [|exact I]. exact (proj1 (PW.slot_func_in sp st OW E IDS OFN i qn nn Hi GN)). }
    intros Σ7 ms7 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F7 & fc7 & m7 & -> & MI7 & ST7 & AG7 & CR7 & HEAP7).
    rewrite (ret_pc_even ECE_FREE2_RA) by (clear; unfold ECE_FREE2_RA; lia). unfold ECE_FREE2_RA.
    (* [comment removed for export] *)
    pose proof (sb_free_func 1 Σ5 Σ7 i m6 m7 _ Hi SB6 AG7 ltac:(clear; lia) HEAP7 CR7) as SB7.
    change (lremove (get_func i st) (lremove (get_file i st) (rms i OW))) with (rms (S i) OW) in HEAP7, AG7.
    apply (rw_cells_agree _ _ _ _ _ AG7) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG7|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [apply in_app_iff; left; apply es_in_rms|cbn; clear - Ha; lia]. }
    pose proof (AH_ceil _ _ _ _ HEAP7) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    clear AG7 SB6 HEAP6 CS6 MI ST SB5 HEAP5 D1 D2 D3 OFFE EESC EESI IES5 IES5'. rename ST7 into ST. rename MI7 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m7) as MU4. pose proof (wmono_refl ctasegs m7) as WM4.
    pose proof (es_in_rms (S i)) as IES7. assert (IES7' : In (p_es E, e_es E, 904) (rms (S i) OW ++ LB)) by (apply in_app_iff; left; exact IES7).
    ablock HEAP7 IES7' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP7 IES7') as (_ & _ & EESC & EESI & _).
    apply implAp_from_evt.
    es_store (es_wr_fu m7 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m8.
    zstep. zstep. rewrite ?(unsigned_lit (Z.of_nat i * 8)), ?(unsigned_lit (Z.of_nat i * 4)) by (clear - Hi; lia).
    setreg 21 (Z_to_bv 64 (Z.of_nat (S i) * 8)) ltac:(f_equal; clear - Hi; lia). setreg 22 (Z_to_bv 64 (Z.of_nat (S i) * 4)) ltac:(f_equal; clear - Hi; lia).
    (* [comment removed for export] *)
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (clr (S i) st) (badr OW)) in ES
        by (rewrite PW.clr_S; fold X; unfold EK.ecl_fin, EK.ecl_mid; rewrite g_of_set_func, g_of_set_file, g_of_set_line, g_of_set_buf, g_of_set_marks;
            g_cbn; unfold MallocRep.wz; cbn [optr]; rewrite (upd_zeros 16 i Hi); reflexivity)
    end.
    apply evt_done.
    eapply (KONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 fc7 Σ7 m7 m8); [exact SB7|exact MU4|exact WM4|exact FR|exact ST|exact MI|exact ES].   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ece_round_in : forall (i n : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mb mc : mem),
    (i < 16)%nat ->
    SB 1 Σc (rms i OW) mb -> munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) ece_frame ->
    stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of (clr i st) (badr OW)) ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y26 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σ' : rts RT) (mb' mc' : mem),
        SB 1 Σ' (rms (S i) OW) mb' -> munch W2 mb' mc' -> wmono ctasegs mb' mc' ->
        rw_cells ctasegs mc' (bv_unsigned sp + -96) ece_frame -> stk ctasegs mc' lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc' ->
        es_raw mc' (e_es E) (g_of (clr (S i) st) (badr OW)) ->
        implAp (abind (err_clear_slots (S i) n) PW.FIN (clr (S i) st)) Σ' POST
          (at_pc ECE_BNE (S i) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y26 y28 y29 y30 y31 F' fc' mc')) ->
    implAp (abind (err_clear_slots i (S n)) PW.FIN (clr i st)) Σc POST
      (at_pc ECE_HEAD i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 F fc mc).
      (* [comment removed for export] *)
  Proof using AL16 AS0 BE CEIL COST CTX DF0 EES16 EESB EESP IDS IES KIDS LO OD OF OFN SH TOP UW.
    intros until mc. intros Hi SBb MU WM FR ST MI ES KONT.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBb) as HEAPb.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu, MU.
    assert (Hi' : (i < ERR_NUM)%nat) by (unfold ERR_NUM; exact Hi).
    set (X := clr i st) in *.
    pose proof (PW.clr_shape i st SH) as SHX. fold X in SHX.
    assert (GL : g_len (g_of X (badr OW))) by (apply g_len_of; exact SHX).
    destruct (PW.slot_i st i Hi) as (XF & XN & XD & XG). fold X in XF, XN, XD, XG.
    destruct (PW.slot_i_mid st i) as (_ & _ & _ & _ & MF & MN). fold X in MF, MN. rewrite XF in MF. rewrite XN in MN.
    pose proof (es_in_rms i) as IESi. assert (IESi' : In (p_es E, e_es E, 904) (rms i OW ++ LB)) by (apply in_app_iff; left; exact IESi).
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IESi') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IESi' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IESi') as (_ & _ & EESC & EESI & _).
    (* [comment removed for export] *)
    rewrite (PW.clear_step_tree i n PW.FIN X), MF, MN. change (ecl_fin i X) with (clr (S i) st).
    unfold at_pc, ece_frame in *. unfold ECE_HEAD, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. rewrite ?(unsigned_lit (Z.of_nat i * 4)) by (clear - Hi; lia).
    setreg 10 (Z_to_bv 64 (e_es E + 4 * Z.of_nat i)) ltac:(f_equal; clear - Hi; lia).
    (* [comment removed for export] *)
    destruct (shb_cells_munch _ _ _ _ _ (AH_shb _ _ _ _ HEAPb) MU
                ltac:(intros x Hx; unfold A_GOT_SHB, A_SHB_CELL in Hx; cbn [outside]; unfold BnHeapA.ACEIL, SHLO, SHHI, SEGTOP_A in *; uchk_open; clear - Hx EESC EESI EESP CEIL LOu C1 C2 C3 SPR; lia)) as [SHB1_ SHB2_].
    pose proof (es_rd_df1 mc (e_es E) _ i (wa (e_es E + 512 + 4 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. zstep. clear RD. try clear SHB1_ SHB2_.
    set (f := get_dflags i st).
    zstep. (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (Z.land f ERR_TXT_MALLOCED))
      ltac:(g_cbn; rewrite nth_wl; change (nth i (as_dflags X) 0) with (get_dflags i X); rewrite XG; unfold zx8, MallocRep.wz;
            rewrite (unsigned_lit (_ mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned (Z_to_bv 64 (get_dflags i st))) (2 ^ 8) ltac:(clear; lia)) as H; clear - H; lia);
            rewrite dflag_bit; reflexivity).
    assert (FR01 : 0 <= Z.land f ERR_TXT_MALLOCED <= 1) by apply land_malloced_range.
    zstep. rewrite ?(unsigned_lit (Z.of_nat i * 8)) by (clear - Hi; lia). (* [comment removed for export] *)
    setreg 25 (Z_to_bv 64 (e_es E + 8 * Z.of_nat i)) ltac:(f_equal; clear - Hi; lia).
    zstep. if_cases KF; zify_cond KF; rewrite ?land_malloced_mask in KF.
    - (* [comment removed for export] *)
      pose proof (es_rd_da mc (e_es E) _ i (wa (e_es E + 256 + 8 * Z.of_nat i)) ES GL Hi' eq_refl) as RD. zstep. clear RD.
      setreg 12 (Z_to_bv 64 (optr (badr OW) (get_data i st))) ltac:(g_cbn; rewrite nth_wl_optr; change (nth i (as_data X) None) with (get_data i X); rewrite XD; reflexivity).
      destruct (get_data i st) as [[pd nd]|] eqn:GD; cbn [optr].
      2:{ exfalso. pose proof (DF0 i GD) as Z0. fold f in Z0. clear - KF Z0. lia. }
      destruct (PW.slot_data_in sp st OW E IDS OD i i pd nd GD) as [HINd HPd].
      assert (HINd' : In (pd, badr OW pd, nd) (rms i OW ++ LB)) by (apply in_app_iff; left; exact HINd).
      pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb HINd') as (BD1 & BD2 & BD3 & BD4 & BD5).
      pose proof (blk_disjointA _ _ _ _ pd (badr OW pd) nd (p_es E) (e_es E) 904 HEAPb HINd' IESi' (ids_data_es_ne E st i pd nd IDS GD)) as DJd.
      zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear - BD1 BD3 C3; lia); clear - K2 BD1; lia|]. clear K2. (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (sb_munch _ _ _ _ _ SBb MU WM) as SBc.
      pose proof SBc as (HEAPc & _ & _ & _ & DCc & _).
      destruct (proj1 DCc i pd nd GD) as [ND1 [junkd HD]].
      assert (EK : exists k, Z.to_nat nd = S k) by (exists (Z.to_nat nd - 1)%nat; clear - ND1; lia). destruct EK as [kd EK]. rewrite EK in HD.
      apply (rw_cells_split_CB ctasegs mc (badr OW pd) [] (S kd) junkd [] [1%nat; kd]) in HD; [|cbn; clear; lia].
      cbn [mk_CB_cells app] in HD.
      clear MU WM ACCE OFFE.
      pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z mc) as MU3. pose proof (wmono_refl ctasegs mc) as WM3.
      ablock HEAPc HINd' ACCD OFFD.
      assert (OFF3 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z) by (cbn [offshW]; clear - OFFD BD2 C1 C2 CEIL LOu; alia).
      (* [comment removed for export] *)
      zstep.
      name_mem m3. zstep.
      lazymatch type of HD with rw_cells _ _ _ ?cs =>
        pose proof (rw_cells_merge ctasegs m3 (badr OW pd) (@nil cell) cs (@nil cell) ltac:(rewrite app_nil_r; exact HD)) as HD' end.
      cbn [app cells_size csize cells_bytes cbytes length] in HD'.
      match type of HD' with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat nd) in HD' by (clear - EK; lia) end.
      pose proof (sb_store_data 1 Σc (rms i OW) mc m3 i pd nd (bv_unsigned sp - (96 + (48 + (112 + 65536)))) (bv_unsigned sp) _ SBc GD HINd ltac:(clear - LOu; lia) ltac:(clear; lia) MU3 WM3 HD') as SB3.
      eapply (es_raw_of_munchA Σc (rms i OW) LB _ mc m3 E _ lo (bv_unsigned sp) (p_es E)) in ES;
        [|exact GL|exact IESi'|exact HEAPc|exact CEIL|exact MU3|exact WM3|].
      2:{ constructor; [left; cbn; clear - LOu; lia|]. constructor; [|constructor]. right; right. exists pd, (badr OW pd), nd.
          split; [exact HINd'|]. split; [exact (ids_data_es_ne E st i pd nd IDS GD) | cbn; clear - ND1; lia]. }
      pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) as HEAP3.
      clear MU3 WM3 HD HD' HEAPc DCc SBc ACCD OFFD OFF3.
      pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m3) as MU4. pose proof (wmono_refl ctasegs m3) as WM4.
      ablock HEAP3 IESi' ACCE OFFE.
      (* [comment removed for export] *)
      es_store (es_wr_df m3 (e_es E) _ i (Z_to_bv 64 1) ES GL Hi'). name_mem m4.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd i X) (badr OW)) in ES
          by (unfold EK.ecd; rewrite XG, XD; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KF FR01; lia); cbn [negb];
              rewrite g_of_set_dflags; unfold ERR_TXT_MALLOCED, MallocRep.wz; reflexivity)
      end.
      apply evt_done.
      eapply (ece_body2 i n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc Σc m3 m4 Hi); [exact SB3|exact MU4|exact WM4|exact FR|exact ST|exact MI|exact ES|exact KONT].
    - (* [comment removed for export] *)
      es_store (es_wr_da mc (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m1.
      zstep.
      es_store (es_wr_ds m1 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m2.
      zstep.
      es_store (es_wr_df m2 (e_es E) _ i (Z_to_bv 64 0) ES GL Hi'). name_mem m3.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd i X) (badr OW)) in ES
          by (unfold EK.ecd; rewrite XG; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with true by (symmetry; apply Z.eqb_eq; clear - KF FR01; lia); cbn [negb];
              rewrite g_of_set_dflags, g_of_set_data; cbn [optr osize]; unfold MallocRep.wz; reflexivity)
      end.
      apply evt_done.
      eapply (ece_body2 i n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc Σc mb m3 Hi); [exact SBb|exact MU|exact WM|exact FR|exact ST|exact MI|exact ES|exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma ece_round_k : forall (i n : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mb mc : mem),
    (i < 16)%nat ->
    SB 1 Σc (rms i OW) mb -> munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) ece_frame -> stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of (clr i st) (badr OW)) ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y26 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σ' : rts RT) (mb' mc' : mem),
        SB 1 Σ' (rms (S i) OW) mb' -> munch W2 mb' mc' -> wmono ctasegs mb' mc' ->
        rw_cells ctasegs mc' (bv_unsigned sp + -96) ece_frame -> stk ctasegs mc' lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc' ->
        es_raw mc' (e_es E) (g_of (clr (S i) st) (badr OW)) ->
        implAp (abind (err_clear_slots (S i) n) PW.FIN (clr (S i) st)) Σ' POST
          (at_pc ECE_BNE (S i) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y26 y28 y29 y30 y31 F' fc' mc')) ->
    implAp (abind (err_clear_slots i (S n)) PW.FIN (clr i st)) Σc POST
      (at_pc ECE_HEAD i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 F fc mc).
  Proof using AL16 AS0 BE CEIL COST CTX DF0 EES16 EESB EESP IDS IES KIDS LO OD OF OFN SH TOP UW.
    intros until mc. intros Hi SBb MU WM FR ST MI ES KONT.
    eapply (ece_round_in i n x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 F fc Σc mb mc Hi);
      [exact SBb|exact MU|exact WM|exact FR|exact ST|exact MI|exact ES|exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma ece_round : forall i n, (S i < 16)%nat -> round_ok (S i) n -> round_ok i (S n).
  Proof using AL16 AS0 BE CEIL CTX DF0 EES16 EESB EESP IDS IES KIDS LO OD OF OFN SH TOP UW.
    intros i n HSi IH. unfold round_ok. intros until mc. intros SBb MU WM FR ST MI ES.
    eapply (ece_round_k i n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc Σc mb mc ltac:(clear - HSi; lia)); [exact SBb|exact MU|exact WM|exact FR|exact ST|exact MI|exact ES|].
    intros until mc'. intros SB' MU' WM' FR' ST' MI' ES'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold round_ok, at_pc in IH. unfold at_pc. unfold ECE_BNE, ECE_HEAD, MallocRep.wz in *.
    apply implAp_from_evt.
    zstep. if_cases KK; zify_cond KK; [|exfalso; rewrite ?unsigned_lit in KK by (clear - HSi; lia); clear - KK HSi; lia]. clear KK.
    apply evt_done.
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' Σ' mb' mc'); [exact SB'|exact MU'|exact WM'|exact FR'|exact ST'|exact MI'|exact ES'].   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma ece_last_gen : forall X16 : ap_st bptr, clr 16 st = X16 -> round_ok 15 1.
  Proof.
    intros X16 EX16. unfold round_ok. intros until mc. intros SBb MU WM FR ST MI ES.
    eapply (ece_round_k 15 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc Σc mb mc ltac:(clear; lia)); [exact SBb|exact MU|exact WM|exact FR|exact ST|exact MI|exact ES|].
    intros until mc'. intros SB' MU' WM' FR' ST' MI' ES'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB') as HEAPb.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu, MU'.
    pose proof (PW.clr_shape 16 st SH) as SH16. clear ES. rename ES' into ES. rewrite EX16 in SH16, ES. rewrite EX16.
    assert (GL : g_len (g_of X16 (badr OW))) by (apply g_len_of; exact SH16).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    pose proof (es_in_rms 16) as IESi. assert (IESi' : In (p_es E, e_es E, 904) (rms 16 OW ++ LB)) by (apply in_app_iff; left; exact IESi).
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IESi') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IESi' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IESi') as (_ & _ & EESC & EESI & _).
    unfold at_pc, ece_frame in *. unfold ECE_BNE, MallocRep.wz in *.
    apply implAp_from_evt.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear; lia); clear - KK; lia|]. clear KK. (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    es_store (es_wr_bot mc' (e_es E) _ 0 ES GL). name_mem m1.
    es_store (es_wr_top m1 (e_es E) _ 0 ES GL). name_mem m2.
    (* [comment removed for export] *)
    do 12 zstep. zstep. release_frame FR' ST' (bv_unsigned sp). zstep.
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (set_bottom 0 (set_top 0 X16)) (badr OW)) in ES
        by (rewrite g_of_set_bottom, g_of_set_top;
            cbn [Z.of_nat EK.g_fl EK.g_ma EK.g_bu EK.g_da EK.g_ds EK.g_df EK.g_fi EK.g_li EK.g_fu EK.g_top EK.g_bot EK.set_g_top EK.set_g_bot]; reflexivity)
    end.
    rewrite (PW.fin_tree X16).
    apply evt_done. apply implAp_ret. subst X16. change (set_bottom 0 (set_top 0 (clr 16 st))) with FINAL in *.
    eapply (ece_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' Σ' mb' m2); [exact SB'|exact MU'|exact WM'|exact ES|exact ST'|exact MI'].
  Qed.
  Lemma ece_last : round_ok 15 1.
  Proof. exact (ece_last_gen (clr 16 st) eq_refl). Qed.

  (* [comment removed for export] *)
  Lemma ece_loop : forall n i, (i + n = 16)%nat -> (1 <= n)%nat -> round_ok i n.
  Proof.
    induction n as [|n IH]; intros i Hin Hn; [lia|]. destruct n as [|n'].
    - replace i with 15%nat by lia. exact ece_last.
    - apply ece_round; [lia|]. apply IH; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ece_act : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    AHEAP Σ OW LB m -> ap_state st m OW E bo0 -> data_cells m OW st ->
    stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> tp = wz TP_A ->
    (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    implAp (err_clear_error st) Σ POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_CLEAR_ERROR) fc None m (seg_rom ctasegs)).
  Proof.
    intros until fc. intros HEAP AS DC ST MI -> FLEN CRED.
    unfold ERR_CLEAR_ERROR, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z) by (cbn [offshW]; alia).
    apply implAp_from_evt.
    carve_frame 96%nat ST. do 14 zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    name_mem m0.
    assert (HW0 : Forall (segW (OW ++ LB) lo (bv_unsigned sp) (fun _ => False)) [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z).
    { constructor; [left; cbn; clear - LOu; lia|]. constructor; [right; left; reflexivity | constructor]. }
    destruct (seg_closeA Σ OW LB _ m m0 lo (bv_unsigned sp) (fun _ => False) HEAP CEIL ltac:(clear - LOu; lia) ltac:(clear - TOPu; unfold USTACK_TOP; lia) MU WM HW0 ltac:(intros p A n _ []))
      as [HEAP0 AX0].
    assert (AS0' : ap_state st m0 OW E bo0) by (eapply (ap_state_of_munchA Σ st m m0); [exact AS | exact HEAP | exact CEIL | exact MU | exact HW0]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    destruct (errno_cellA m0) as [errv HERR].
    apply evt_done. intros X Φ D SAFE LINK.
    eapply (get_state_cpsA _) with (lo := lo) (OW := OW) (LB := LB) (E := E) (st := st) (bo := bo0) (v := 0);
      [exact HEAP0 | exact AS0' | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact FLEN | exact CRED
      | exact HERR | left; reflexivity | reflexivity |].
    intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 errv2 HEAP2 CR2 EL2 ST2 MI2 AG2 HERR2.
    rewrite ESP in ST2, AG2. rewrite (ret_pc_even ECE_RA1) by (clear; unfold ECE_RA1; lia). unfold ECE_RA1.
    eapply (implAp_elim (err_clear_error st)); [| exact SAFE | exact LINK | exact EL2].
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; split; [left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia | cbn [cells_size csize Nat.add] in Ha; unfold ERRNO_A, TP_A; clear - Ha LOu CEIL C1; lia]].
    pose proof (lib_agree_of_ex_errno Σ OW LB m0 m0 m2 _ HEAP0 AG2) as LAG2.
    assert (AXb : ax_pres LB (bv_unsigned sp) LIBW_A m m2) by (eapply ax_pres_trans; [exact AX0 | eapply (ax_pres_of_ex_errno OW LB); [exact AG2 | clear; lia]]).
    assert (AS2 : ap_state st m2 OW E bo0) by (eapply ap_state_agree; [exact AS0' | exact LAG2]).
    assert (DCb : data_cells m2 OW st).
    { eapply data_cells_agree; [| exact LAG2 | exact OD]. eapply (data_cells_of_munchA Σ OW LB _ m m0); [exact DC | | exact HEAP | exact CEIL | exact MU | eapply segW_mono; [| exact HW0]; intros p []].
      intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (KPb : kept K m m2).
    { eapply kept_trans; [| eapply kept_of_lib_agree; [exact KOW | exact LAG2]].
      eapply (kept_of_munchA Σ OW LB _ m m0 K lo); [exact HEAP | intros b Hb; apply INCL; apply KOW; exact Hb | exact CEIL | exact MU | eapply segW_mono; [| exact HW0]; intros p []]. }
    assert (SB2 : SB 1 Σ2 OW m2).
    { eapply (seg_baseA_intro m OW st E bo0 LB K (bv_unsigned sp) Σ); [exact HEAP2|exact AXb|exact AS2|exact DCb|exact KPb|exact KOW|rewrite CR2; clear; lia]. }
    pose proof (ap_state_esA _ _ _ _ _ AS2) as (ES & GL & _).
    clear MU WM OFF HW0 HEAP0 AX0 AS0' AS HEAP DC HERR LAG2 MI ST AG2 AXb DCb KPb. try clear SHB1_ SHB2_. clear m0.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    pose proof (AH_ceil _ _ _ _ HEAP2) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3.
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAP2 IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAP2 IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP2 IES') as (_ & _ & EESC & EESI & _).
    apply implAp_from_evt.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - EESP EESB; lia); clear - KK EESP EESB; lia|]. clear KK. (* [comment removed for export] *)
    do 7 zstep. (* [comment removed for export] *)
    apply evt_done.
    change (err_clear_error st) with (abind (err_clear_slots 0 16) PW.FIN (clr 0 st)).
    pose proof (ece_loop 16 0 eq_refl ltac:(clear; lia)) as RO. unfold round_ok, at_pc, ECE_HEAD, ECE_LIT, MallocRep.wz in RO. cbn [Z.of_nat Z.mul] in RO.
    eapply (RO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 m2 m2); [exact SB2|exact MU2|exact WM2|exact FR|exact ST2|exact MI2|exact ES].   (* [comment removed for export] *)
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_clear_error_walkA : ERR_clear_error_specA.
  Proof.
    intros bo0. unfold ap_stmtA. intros until K. intros ras PRE TP UW CTX NE EBO KOW KIDS. subst bo.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP' & TOP & AL16 & MI & CRED & FRM).
    unfold ERR_CLEAR_ERROR_STACK, ERR_CLEAR_ERROR_COST, ERR_CLEAR_ERROR_FRAMES in *.
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    pose proof (data_cells_dflagsA _ _ _ DC) as DF0.
    eapply (ece_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo0 lo
              IDS CEIL ltac:(unfold ECE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME; clear - LOSP'; lia) TOP AL16 SH IES EESP EESB EES16 OF OFN OD (ex_intro _ m AS) DF0 K KOW KIDS
              ERR_CLEAR_ERROR_COST ltac:(unfold ERR_CLEAR_ERROR_COST; clear; lia) ltac:(clear - FRM; lia) ras UW CTX);
      [exact HEAP | exact AS | exact DC | exact ST | exact MI | exact TP | clear - FRM; unfold FRAMES_MAX in *; lia | clear - CRED; lia].
  Qed.

End WithRT.
