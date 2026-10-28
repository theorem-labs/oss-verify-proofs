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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame ApErrKitA ApErrKitA2 W_locks W_tlocalA Fr_init_base W_get_stateA Fr_err_set_error.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Ltac by_cases16 t H :=
  try clearbody t; clear - H; revert H;
  do 16 (destruct t as [|t]; [intros _; vm_compute; reflexivity|]); intros H; exfalso; lia.

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

Definition VSE_STK : Z := 128 + GET_STATE_STACK.   (* [comment removed for export] *)   (* [comment removed for export] *)
Definition VSE_RA1 : Z := 0x1fdcd0.               (* [comment removed for export] *)
Definition VSE_CLEAR : Z := 0x1fde28.   (* [comment removed for export] *)             (* [comment removed for export] *)
Definition VSE_SET : Z := 0x1fdedc.               (* [comment removed for export] *)

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
  Variables (rs : rsite) (lib reason : Z).
  Hypothesis IDS : ids_ok E st.
  Hypothesis CEIL : ACEIL <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - VSE_STK.
  Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
  Hypothesis AL16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESB : e_es E + 904 < 2 ^ 63.
  Hypothesis EES16 : e_es E mod 16 = 0.
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists mI, ap_state st mI OW E bo0.
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis RSC : rs_code rs = ERR_PACK lib reason.
  Hypothesis LIBR : 0 <= lib < 256.
  Hypothesis LIBNS : lib <> ERR_LIB_SYS.
  Hypothesis REAR : 0 <= reason < 8388608.
  Variables (COST FRAMES : Z).
  Hypothesis COST1 : 1 <= COST.
  Hypothesis FRM : Z.of_nat (length FR) + 0 <= Z.of_nat FRAMES_MAX.

  Let tn : nat := as_top st.
  Local Notation W2 := ([(bv_unsigned sp - VSE_STK, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Let POST := ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K COST
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0).
  (* [comment removed for export] *)
  Definition vse_frame (j0 : list byte) : list cell :=   (* [comment removed for export] *)
    [CB 8 j0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma TNB : (tn < 16)%nat.
  Proof. pose proof (ids_ok_top _ _ IDS) as [T _]. exact T. Qed.

  (* [comment removed for export] *)
  Lemma vse_finish : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σ2 : rts RT) (mb m9 : mem),
    AHEAP Σ2 OW LB mb -> ax_pres LB (bv_unsigned sp) LIBW_A m mb -> ap_restA mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    rt_credit RT Σ2 = rt_credit RT Σ - 1 ->
    munch W2 mb m9 -> wmono ctasegs mb m9 ->
    es_raw m9 (e_es E) (g_of (eserr_fin rs st) (badr OW)) -> stk ctasegs m9 lo (bv_unsigned sp) -> mem_inv ctasegs m9 ->
    POST (tt, eserr_fin rs st) Σ2
         (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m9 (seg_rom ctasegs)).
  Proof.
    intros until m9. intros HEAPb AXb ARb DCb KPb CR2 MU WM ES ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [_ BNB'].
    unfold VSE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK, USTACK_TOP in *.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (HW : forall P : bptr -> Prop, P (p_es E) -> Forall (segW (OW ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { intros P HP. constructor; [left; cbn; clear - LO; lia|]. constructor; [| constructor]. right; right. exists (p_es E), (e_es E), 904.
      split; [apply INCL; exact IES|]. split; [exact HP | cbn; clear; lia]. }
    destruct (seg_closeA Σ2 OW LB _ mb m9 lo (bv_unsigned sp) (fun p => p = p_es E) HEAPb CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU WM (HW _ eq_refl))
      as [HEAP9 AX9].
    { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAPb) as ND.
      destruct (badr_size_unique (OW ++ LB) (p_es E) A n (e_es E) 904 ND HIN (INCL _ IES)) as [-> ->]. exact IES. }
    assert (AR9 : ap_restA m9 OW E bo0 (as_cnf st)).
    { eapply (rest_of_segA Σ2 OW LB _ mb m9); [exact ARb|exact HEAPb|intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact ARb|exact Hb]|exact CEIL|exact MU|].
      apply HW. destruct AS0 as [mI AS0']. eapply es_not_restA; [exact AS0'|exact IDS]. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC9 : data_cells m9 OW st).
    { eapply (data_cells_of_munchA Σ2 OW LB _ mb m9); [exact DCb|exact DIN|exact HEAPb|exact CEIL|exact MU|].
      apply HW. intros i q k Hd. eapply ids_data_es_ne; [exact IDS|exact Hd]. }
    (* [comment removed for export] *)
    assert (PERM : exists pre, Permutation (pre ++ st_blocks (eserr_fin rs st)) (st_blocks st) /\ (pre = [] \/ pre = optb (get_data tn st))).
    { unfold CtRepP.ApErrKit.eserr_fin. rewrite st_blocks_set_buf. pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
      destruct (st_blocks_ecd tn st ltac:(rewrite L3; exact TNB')) as [P|P]; [exists []; split; [exact P|left; reflexivity]|exists (optb (get_data tn st)); split; [exact P|right; reflexivity]]. }
    destruct PERM as (pre & PERM & Hpre).
    pose proof (ecd_proj tn st) as (PT & PB & PF & PN & PM & PU & PL & PC).
    assert (IDS' : ids_ok E (eserr_fin rs st)).
    { eapply ids_ok_sub; [exact PERM| | |apply marks_sub_eserr_fin|exact IDS]; unfold CtRepP.ApErrKit.eserr_fin; cbn [as_top as_bottom set_buf]; [rewrite PT; exact TNB'|rewrite PB; exact BNB']. }
    assert (DSUB : forall i q k, get_data i (eserr_fin rs st) = Some (q, k) -> get_data i st = Some (q, k)).
    { intros i q k Hd. apply (get_data_ecd tn st). unfold get_data, CtRepP.ApErrKit.eserr_fin in Hd |- *. cbn [as_data set_buf] in Hd. exact Hd. }
    assert (AS9 : ap_state (eserr_fin rs st) m9 OW E bo0).
    { apply ap_state_joinA.
      - replace (as_cnf (eserr_fin rs st)) with (as_cnf st) by (unfold CtRepP.ApErrKit.eserr_fin; cbn [as_cnf set_buf]; rewrite PC; reflexivity). exact AR9.
      - unfold CtRepP.ApErrKit.eserr_fin. apply es_shape_setters. unfold CtRepP.ApErrKit.ecd. destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; exact SH.
      - exact ES.
      - unfold CtRepP.ApErrKit.eserr_fin. cbn [as_file set_buf]. rewrite PF. exact OF.
      - unfold CtRepP.ApErrKit.eserr_fin. cbn [as_func set_buf]. rewrite PN. exact OFN.
      - unfold CtRepP.ApErrKit.eserr_fin. cbn [as_data set_buf]. unfold CtRepP.ApErrKit.ecd. destruct (negb _); [destruct (get_data _ _)|]; cbn [as_data set_dflags set_data]; try apply optb_ok_lset_none; exact OD. }
    assert (DC9' : data_cells m9 OW (eserr_fin rs st)).
    { apply (data_cells_subA m9 OW st); [exact DC9|intros i q k Hd; exists i; apply DSUB; exact Hd|].
      unfold CtRepP.ApErrKit.eserr_fin. eapply dflags_ok_same; [reflexivity|reflexivity|]. pose proof SH as (_ & _ & L3 & L4 & _).
      apply dflags_ok_ecd; [rewrite L3; exact TNB'|rewrite L3, L4; reflexivity|eapply data_cells_dflagsA; exact DCb]. }
    assert (KP9 : kept K mb m9).
    { eapply (kept_of_munchA Σ2 OW LB _ mb m9 K lo); [exact HEAPb|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      apply HW. eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto. }
    unfold POST, ap_postA.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m9, OW, bo0.
    split; [reflexivity|].
    split.
    { unfold ap_preA. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS'|]. split; [exact DC9'|]. split; [exact ST|]. split; [exact CEIL|].
      split; [clear - LO; lia|]. split; [unfold USTACK_TOP; clear - TOP; lia|]. split; [exact AL16|]. split; [exact MI|].
      split; [pose proof (af_credit_nonneg RT AF Σ2 m9 (AH_art _ _ _ _ HEAP9)) as X; clear - X; lia|]. split; [clear; lia|]. clear - FRM. lia. }
    split; [eapply ax_pres_trans; [exact AXb | exact AX9]|].
    split; [clear - CR2 COST1; lia|].
    split; [| reflexivity].
    split; [exact KOW|]. split; [| intros a Ha Hin; rewrite (KP9 a Ha Hin); exact (KPb a Ha Hin)].
    intros b Hb Hin. apply (KIDS b Hb). apply in_app_iff. left. eapply es_ids_sub_perm; [exact PERM|exact Hin].
  Qed.

  (* [comment removed for export] *)
  Lemma vse_tail2 : forall (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (Σ2 : rts RT) (mb mc : mem) (j0 : list byte),
    AHEAP Σ2 OW LB mb -> ax_pres LB (bv_unsigned sp) LIBW_A m mb -> ap_restA mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    rt_credit RT Σ2 = rt_credit RT Σ - 1 ->
    munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -112) (vse_frame j0) ->
    stk ctasegs mc lo (bv_unsigned sp + -112) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of (ecd tn st) (badr OW)) ->
    implAp (ARet (tt, eserr_fin rs st)) Σ2 POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 0) x10 x11 x12 (Z_to_bv 64 (Z.shiftr (e_es E + 896) 3 + SHB)) x14 x15 x16 x17
               (Z_to_bv 64 0) (wz (e_es E)) (Z_to_bv 64 reason) (Z_to_bv 64 0) (Z_to_bv 64 lib) (Z_to_bv 64 (e_es E + 896)) (Z_to_bv 64 0) (Z_to_bv 64 SHB)
               x26 x27 x28 x29 x30 x31)
          F2 (wz VSE_SET) fc2 None mc (seg_rom ctasegs)).   (* [comment removed for export] *)
  Proof using AL16 AS0 CEIL COST1 EESB EESP FRM IDS IES KIDS KOW LIBNS LIBR LO OD OF OFN REAR RSC SH TOP.
    intros until j0. intros HEAPb AXb ARb DCb KPb CR2 MU2 WM2 FR1 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    unfold VSE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK, USTACK_TOP in LO, TOP, MU2.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (SH1 : es_shape (ecd tn st)) by (unfold CtRepP.ApErrKit.ecd; destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; exact SH).
    assert (GL : g_len (g_of (ecd tn st) (badr OW))) by (apply g_len_of; exact SH1).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    assert (OFF2 : offshW [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IES') as (_ & _ & EESC & EESI & _).
    unfold vse_frame in FR1. unfold VSE_SET, ERR_LIB_SYS, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    pose proof (es_rd_top mc (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. step. clear RD.
    cbn [CtRepP.ApErrKit.g_top CtRepP.ApErrKit.g_of]. rewrite (proj1 (ecd_proj tn st)). rewrite !sx32_small by (clear - TOPB; lia). fold tn.
    step. step. if_cases KK; zify_cond KK; [| exfalso; rewrite ?unsigned_lit in KK by (clear - LIBR; lia); clear - KK LIBNS; lia]. clear KK.
    (* [comment removed for export] *)
    do 5 step.
    setreg 13 (Z_to_bv 64 (ERR_PACK lib reason)) ltac:(rewrite <- (err_pack_bits lib reason LIBR REAR); reflexivity).
    pose proof (err_pack_range lib reason LIBR REAR) as PKR.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    ual.
    step. step. rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia). (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. step. rewrite (zext32_shifts (ERR_PACK lib reason)) by (clear - PKR; lia).
    es_store (es_wr_bu mc (e_es E) _ tn (Z_to_bv 64 (ERR_PACK lib reason)) ES GL TNB'). name_mem m3.
    (* [comment removed for export] *)
    step. if_true.
    do 13 step. step.
    release_frame FR1 ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (eserr_fin rs st) (badr OW)) in ES
        by (unfold CtRepP.ApErrKit.eserr_fin; fold tn; rewrite g_of_set_buf, RSC; unfold MallocRep.wz; reflexivity)
    end.
    apply evt_done. apply implAp_ret.
    eapply (vse_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Σ2 mb m3);
      [exact HEAPb | exact AXb | exact ARb | exact DCb | exact KPb | exact CR2 | exact MU2 | exact WM2 | exact ES | exact ST | exact MI].
  Qed.

  (* [comment removed for export] *)
  Lemma vse_tail : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (Σ2 : rts RT) (mb mc : mem) (j0 : list byte),
    AHEAP Σ2 OW LB mb -> ax_pres LB (bv_unsigned sp) LIBW_A m mb -> ap_restA mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    rt_credit RT Σ2 = rt_credit RT Σ - 1 ->
    munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -112) (vse_frame j0) ->
    stk ctasegs mc lo (bv_unsigned sp + -112) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of st (badr OW)) ->
    implAp (ARet (tt, eserr_fin rs st)) Σ2 POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 0) (wz (e_es E)) (Z_to_bv 64 reason) (Z_to_bv 64 0) (Z_to_bv 64 lib) (Z_to_bv 64 (e_es E + 896)) (Z_to_bv 64 0) (Z_to_bv 64 SHB)
               (Z_to_bv 64 (Z.shiftr (e_es E + 896) 3)) x27 x28 x29 x30 x31)
          F2 (wz VSE_CLEAR) fc2 None mc (seg_rom ctasegs)).
      (* [comment removed for export] *)
  Proof using AL16 AS0 CEIL COST1 EESB EESP FRM IDS IES KIDS KOW LIBNS LIBR LO OD OF OFN REAR RSC SH TOP.
    intros until j0. intros HEAPb AXb ARb DCb KPb CR2 MU2 WM2 FR1 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    unfold VSE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK, USTACK_TOP in LO, TOP, MU2.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (GL : g_len (g_of st (badr OW))) by (apply g_len_of; exact SH).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    assert (OFF2 : offshW [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IES') as (_ & _ & EESC & EESI & _).
    unfold vse_frame in FR1. unfold VSE_CLEAR, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    pose proof (es_rd_top mc (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. zstep. clear RD.
    cbn [CtRepP.ApErrKit.g_top CtRepP.ApErrKit.g_of]. rewrite !sx32_small by (clear - TOPB; lia). fold tn.
    step. step. rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia).
    setreg 10 (Z_to_bv 64 (4 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia).
    pose proof (es_rd_df1 mc (e_es E) _ tn (wa (e_es E + 512 + 4 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD.
    zstep. clear RD.
    zstep. (* [comment removed for export] *)
    set (f := get_dflags tn st).
    zstep. (* [comment removed for export] *)
    setreg 16 (Z_to_bv 64 (Z.land f ERR_TXT_MALLOCED))
      ltac:(cbn [CtRepP.ApErrKit.g_df CtRepP.ApErrKit.g_of]; rewrite nth_wl; unfold zx8, MallocRep.wz; rewrite (unsigned_lit (_ mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned (Z_to_bv 64 (nth tn (as_dflags st) 0))) (2 ^ 8) ltac:(clear; lia)); clear - H; lia);
            rewrite dflag_bit; reflexivity).
    assert (FR01 : 0 <= Z.land f ERR_TXT_MALLOCED <= 1) by apply land_malloced_range.
    zstep. rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia). (* [comment removed for export] *)
    setreg 15 (Z_to_bv 64 (Z.of_nat tn * 8)) ltac:(f_equal; clear - TOPB; lia).
    pstep. setreg 11 (Z_to_bv 64 (e_es E + 256 + 8 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia). (* [comment removed for export] *)
    zstep. if_cases KF; zify_cond KF; rewrite land_malloced_mask in KF.
    - (* [comment removed for export] *)
      pose proof (es_rd_da mc (e_es E) _ tn (wa (e_es E + 256 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. zstep. clear RD.
      setreg 11 (Z_to_bv 64 (optr (badr OW) (get_data tn st))) ltac:(cbn [CtRepP.ApErrKit.g_da CtRepP.ApErrKit.g_of]; rewrite nth_wl_optr; reflexivity).
      assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
      { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
      destruct (get_data tn st) as [[pd nd]|] eqn:GD; cbn [optr].
      + (* [comment removed for export] *)
        destruct (optb_ok_nth OW _ tn pd nd OD GD) as [HINd HPd].
        pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb (INCL _ HINd)) as (BD1 & BD2 & BD3 & BD4 & BD5).
        pose proof (blk_disjointA _ _ _ _ pd (badr OW pd) nd (p_es E) (e_es E) 904 HEAPb (INCL _ HINd) IES' ltac:(eapply ids_data_es_ne; [exact IDS|exact GD])) as DJd.
        zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear - BD1 BD3 C3; lia); clear - K2 BD1; lia|]. clear K2.
        (* [comment removed for export] *)
        assert (HW2 : forall P : bptr -> Prop, P (p_es E) -> Forall (segW (OW ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
        { intros P HP. constructor; [left; cbn; clear - LO; lia|]. constructor; [| constructor]. right; right. exists (p_es E), (e_es E), 904.
          split; [exact IES'|]. split; [exact HP | cbn; clear; lia]. }
        destruct (seg_closeA Σ2 OW LB _ mb mc lo (bv_unsigned sp) (fun p => p = p_es E) HEAPb CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU2 WM2 (HW2 _ eq_refl))
          as [HEAPc AXc].
        { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAPb) as ND. destruct (badr_size_unique (OW ++ LB) (p_es E) A n (e_es E) 904 ND HIN IES') as [-> ->]. exact IES. }
        assert (ARc : ap_restA mc OW E bo0 (as_cnf st)).
        { eapply (rest_of_segA Σ2 OW LB _ mb mc); [exact ARb|exact HEAPb|intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact ARb|exact Hb]|exact CEIL|exact MU2|].
          apply HW2. destruct AS0 as [mI AS0']. eapply es_not_restA; [exact AS0'|exact IDS]. }
        assert (DCc : data_cells mc OW st).
        { eapply (data_cells_of_munchA Σ2 OW LB _ mb mc); [exact DCb|exact DIN|exact HEAPb|exact CEIL|exact MU2|]. apply HW2. intros i q k Hd. eapply ids_data_es_ne; [exact IDS|exact Hd]. }
        assert (AXc' : ax_pres LB (bv_unsigned sp) LIBW_A m mc) by (eapply ax_pres_trans; [exact AXb|exact AXc]).
        assert (KPc : kept K m mc).
        { eapply kept_trans; [exact KPb|]. eapply (kept_of_munchA Σ2 OW LB _ mb mc K lo); [exact HEAPb|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU2|].
          apply HW2. eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto. }
        destruct (proj1 DCc tn pd nd GD) as [ND1 [junkd HD]].
        assert (EK : exists k, Z.to_nat nd = S k) by (exists (Z.to_nat nd - 1)%nat; clear - ND1; lia). destruct EK as [kd EK]. rewrite EK in HD.
        apply (rw_cells_split_CB ctasegs mc (badr OW pd) [] (S kd) junkd [] [1%nat; kd]) in HD; [|cbn; clear; lia].
        cbn [mk_CB_cells app] in HD.
        clear MU2 WM2 ACCE OFFE.
        pose proof (munch_refl [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z mc) as MU3. pose proof (wmono_refl ctasegs mc) as WM3.
        assert (HINd' : In (pd, badr OW pd, nd) (OW ++ LB)) by (apply INCL; exact HINd).
        ablock HEAPc HINd' ACCD OFFD.
        assert (OFF3 : offshW [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z) by (cbn [offshW]; clear - OFFD BD2 C1 C2 CEIL LO; alia).
        zstep. (* [comment removed for export] *)
        name_mem m3. zstep. (* [comment removed for export] *)
        assert (HW3 : forall P : bptr -> Prop, P pd -> Forall (segW (OW ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z).
        { intros P HP. constructor; [left; cbn; clear - LO; lia|]. constructor; [| constructor]. right; right. exists pd, (badr OW pd), nd.
          split; [exact HINd'|]. split; [exact HP | cbn; clear - ND1; lia]. }
        destruct (seg_closeA Σ2 OW LB _ mc m3 lo (bv_unsigned sp) (fun p => p = pd) HEAPc CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU3 WM3 (HW3 _ eq_refl))
          as [HEAP3 AX3].
        { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAPc) as ND. destruct (badr_size_unique (OW ++ LB) pd A n (badr OW pd) nd ND HIN HINd') as [-> ->]. exact HINd. }
        assert (AR3 : ap_restA m3 OW E bo0 (as_cnf st)).
        { eapply (rest_of_segA Σ2 OW LB _ mc m3); [exact ARc|exact HEAPc|intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact ARc|exact Hb]|exact CEIL|exact MU3|].
          apply HW3. eapply data_not_rest; [exact IDS|exact GD]. }
        lazymatch type of HD with rw_cells _ _ _ ?cs =>
          pose proof (rw_cells_merge ctasegs m3 (badr OW pd) (@nil cell) cs (@nil cell) ltac:(rewrite app_nil_r; exact HD)) as HD' end.
        cbn [app cells_size csize cells_bytes cbytes length] in HD'.
        match type of HD' with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat nd) in HD' by (clear - EK; lia) end.
        assert (DC3 : data_cells m3 OW st).
        { eapply (data_cells_store1A Σ2 OW LB mc m3 OW st lo (bv_unsigned sp)); [exact DCc|exact DIN|exact HINd'|exact ND1|exact HEAPc|exact CEIL| | |exact MU3|exact HD']; clear - LO; lia. }
        eapply (es_raw_of_munchA Σ2 OW LB _ mc m3 E _ lo (bv_unsigned sp) (p_es E)) in ES; [|exact GL|exact IES'|exact HEAPc|exact CEIL|exact MU3|exact WM3|apply HW3; intros EQ; exact (ids_data_es_ne E st tn (p_es E) nd IDS ltac:(rewrite <- EQ; exact GD) eq_refl)].
        assert (AX3' : ax_pres LB (bv_unsigned sp) LIBW_A m m3) by (eapply ax_pres_trans; [exact AXc'|exact AX3]).
        assert (KP3 : kept K m m3).
        { eapply kept_trans; [exact KPc|]. eapply (kept_of_munchA Σ2 OW LB _ mc m3 K lo); [exact HEAPc|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU3|].
          apply HW3. eapply K_not_es; [exact KIDS|]. eapply es_ids_data; exact GD. }
        clear MU3 WM3 HD HD' HEAPc AXc AXc' ARc DCc KPc ACCD OFFD OFF3.
        pose proof (munch_refl [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m3) as MU4. pose proof (wmono_refl ctasegs m3) as WM4.
        ablock HEAP3 IES' ACCE OFFE.
        (* [comment removed for export] *)
        es_store (es_wr_df m3 (e_es E) _ tn (Z_to_bv 64 1) ES GL TNB'). name_mem m4.
        lazymatch type of ES with es_raw _ _ ?g =>
          replace g with (g_of (ecd tn st) (badr OW)) in ES
            by (unfold CtRepP.ApErrKit.ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KF FR01; lia); cbn [negb];
                rewrite GD, g_of_set_dflags; unfold ERR_TXT_MALLOCED, MallocRep.wz; reflexivity)
        end.
        apply evt_done.
        eapply (vse_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 m3 _ j0);
          [exact HEAP3|exact AX3'|exact AR3|exact DC3|exact KP3|exact CR2|exact MU4|exact WM4|exact FR1|exact ST|exact MI|exact ES].
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; [|exfalso; rewrite ?unsigned_lit in K2 by (clear; lia); clear - K2; lia]. clear K2.
        replace (g_of st (badr OW)) with (g_of (ecd tn st) (badr OW)) in ES
          by (unfold CtRepP.ApErrKit.ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KF FR01; lia); cbn [negb]; rewrite GD; reflexivity).
        apply evt_done.
        eapply (vse_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 mb _ j0);
          [exact HEAPb|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR1|exact ST|exact MI|exact ES].
    - (* [comment removed for export] *)
      es_store (es_wr_da mc (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m3.
      step. es_store (es_wr_ds m3 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m4.
      zstep. (* [comment removed for export] *)
      rewrite ?zxb_z8.
      es_store (es_wr_df m4 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m5. (* [comment removed for export] *)
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd tn st) (badr OW)) in ES
          by (unfold CtRepP.ApErrKit.ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with true by (symmetry; apply Z.eqb_eq; clear - KF FR01; lia); cbn [negb];
              rewrite g_of_set_dflags, g_of_set_data; cbn [optr osize]; unfold MallocRep.wz; reflexivity)
      end.
      apply evt_done.
      eapply (vse_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 mb _ j0);
        [exact HEAPb|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR1|exact ST|exact MI|exact ES].
  Qed.

  (* [comment removed for export] *)
  Lemma vse_act : forall (tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    AHEAP Σ OW LB m -> ap_state st m OW E bo0 -> data_cells m OW st ->
    stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> tp = wz TP_A ->
    (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    implAp (err_set_error rs st) Σ POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz lib) (wz reason) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_VSET_ERROR) fc None m (seg_rom ctasegs)).
  Proof using AL16 AS0 CEIL COST1 EES16 EESB EESP FRM IDS IES KIDS KOW LIBNS LIBR LO OD OF OFN REAR RSC SH TOP.
    intros until fc. intros HEAP AS DC ST MI -> FLEN CRED.
    unfold ERR_VSET_ERROR, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    unfold VSE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK, USTACK_TOP in LO, TOP.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    rewrite (err_set_error_tree rs st).
    pose proof (munch_refl [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z) by (cbn [offshW]; alia).
    apply implAp_from_evt.
    carve_frame 112%nat ST. do 15 zstep.
    do 3 zstep.
    zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    name_mem m0.
    assert (HW0 : Forall (segW (OW ++ LB) lo (bv_unsigned sp) (fun _ => False)) [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z).
    { constructor; [left; cbn; clear - LO; lia|]. constructor; [right; left; reflexivity | constructor]. }
    destruct (seg_closeA Σ OW LB _ m m0 lo (bv_unsigned sp) (fun _ => False) HEAP CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU WM HW0 ltac:(intros p A n _ []))
      as [HEAP0 AX0].
    assert (AS0' : ap_state st m0 OW E bo0) by (eapply (ap_state_of_munchA Σ st m m0); [exact AS | exact HEAP | exact CEIL | exact MU | exact HW0]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - SPR LO CEIL C1; lia).
    destruct (errno_cellA m0) as [errv HERR].
    apply evt_done. intros X Φ D SAFE LINK.
    eapply (get_state_cpsA _) with (lo := lo) (OW := OW) (LB := LB) (E := E) (st := st) (bo := bo0) (v := 1);
      [exact HEAP0 | exact AS0' | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact FLEN | exact CRED
      | exact HERR | right; reflexivity | reflexivity |].
    intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 errv2 HEAP2 CR2 EL2 ST2 MI2 AG2 HERR2.
    rewrite ESP in ST2, AG2. rewrite (ret_pc_even VSE_RA1) by (clear; unfold VSE_RA1; lia). unfold VSE_RA1.
    eapply (implAp_elim (ARet (tt, eserr_fin rs st))); [| exact SAFE | exact LINK | exact EL2].
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; split; [left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOP; lia | cbn [cells_size csize Nat.add] in Ha; unfold ERRNO_A, TP_A; clear - Ha LO CEIL C1; lia]].
    pose proof (lib_agree_of_ex_errno Σ OW LB m0 m0 m2 _ HEAP0 AG2) as LAG2.
    assert (AXb : ax_pres LB (bv_unsigned sp) LIBW_A m m2) by (eapply ax_pres_trans; [exact AX0 | eapply (ax_pres_of_ex_errno OW LB); [exact AG2 | clear; lia]]).
    assert (AS2 : ap_state st m2 OW E bo0) by (eapply ap_state_agree; [exact AS0' | exact LAG2]).
    assert (DCb : data_cells m2 OW st).
    { eapply data_cells_agree; [| exact LAG2 | exact OD]. eapply (data_cells_of_munchA Σ OW LB _ m m0); [exact DC | | exact HEAP | exact CEIL | exact MU | eapply segW_mono; [| exact HW0]; intros p []].
      intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (KPb : kept K m m2).
    { eapply kept_trans; [| eapply kept_of_lib_agree; [exact KOW | exact LAG2]].
      eapply (kept_of_munchA Σ OW LB _ m m0 K lo); [exact HEAP | intros b Hb; apply INCL; apply KOW; exact Hb | exact CEIL | exact MU | eapply segW_mono; [| exact HW0]; intros p []]. }
    pose proof (proj1 (proj1 (ap_state_splitA _ _ _ _ _) AS2)) as ARb.
    pose proof (ap_state_esA _ _ _ _ _ AS2) as (ES & GL & _).
    clear MU WM OFF HW0 HEAP0 AX0 AS0' AS HEAP DC HERR LAG2 MI ST AG2. try clear SHB1_ SHB2_. clear m0.
    pose proof (munch_refl [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    assert (OFF2 : offshW [(bv_unsigned sp - (128 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAP2 IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAP2 IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP2 IES') as (_ & _ & EESC & EESI & _).
    apply implAp_from_evt.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - EESP EESB; lia); clear - KK EESP EESB; lia|]. clear KK. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep.
    zstep. if_true. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    apply evt_done.
    eapply (vse_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 m2 m2);
      [exact HEAP2|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR|exact ST2|exact MI2|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_vset_error_walkA : forall rs lib reason, ERR_vset_error_specA rs lib reason.
  Proof.
    intros rs lib reason bo0. unfold ap_stmtA. intros until K. intros ras PRE TP UW CTX NE (A0 & A1 & A2 & RSC & LIBR & LIBNS & REAR & EBO) KOW KIDS. subst bo a0 a1 a2.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    unfold ERR_VSET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES in *.
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    eapply (vse_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo0 lo rs lib reason
              IDS CEIL ltac:(unfold VSE_STK, GET_STATE_STACK, IB_STACK, IB_FRAME; clear - LOSP; lia) TOP AL16 SH IES EESP EESB EES16 OF OFN OD (ex_intro _ m AS) K KOW KIDS
              RSC LIBR LIBNS REAR ERR_VSET_ERROR_COST ltac:(unfold ERR_VSET_ERROR_COST; clear; lia) ltac:(clear - FRM; lia));
      [exact HEAP | exact AS | exact DC | exact ST | exact MI | exact TP | clear - FRM; unfold FRAMES_MAX in *; lia | clear - CRED; lia].
  Qed.

End WithRT.

(* [comment removed for export] *)
Theorem ERR_set_error_closedA : forall (AR : ARun) (UK : UnwindKit) (BE : BnEdges) rs lib reason, @ERR_set_error_specA AR UK rs lib reason.
Proof. intros AR UK BE rs lib reason. apply ERR_set_error_walkA. intros f. apply (@ERR_vset_error_walkA (push AR f 0) UK). Qed.
