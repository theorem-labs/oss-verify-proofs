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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import PzUTacB.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame ApErrKitA ApErrKitA2 W_locks W_tlocalA Fr_init_base W_get_stateA.
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

Definition ENW_STK : Z := 64 + GET_STATE_STACK.   (* [comment removed for export] *)    (* [comment removed for export] *)
Definition ENW_RA1 : Z := 0x1fd560.               (* [comment removed for export] *)
Definition ENW_CLEAR : Z := 0x1fd5e8.   (* [comment removed for export] *)             (* [comment removed for export] *)
Definition ENW_TAIL : Z := 0x1fd680.              (* [comment removed for export] *)
Definition ENW_FREE1_RA : Z := 0x1fd708.
Definition ENW_FREE2_RA : Z := 0x1fd73c.
Local Notation E_free1 := (E_ERR_new_1f8e14 : uk_call 0x1fd52c 0x1fd708 0x1fd334).
Local Notation E_free2 := (E_ERR_new_1f8e54 : uk_call 0x1fd52c 0x1fd73c 0x1fd334).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition ERR_new_specA : Prop := forall bo0 : Z * Z,
  ap_stmtA ERR_NEW ERR_NEW_STACK ERR_NEW_COST ERR_NEW_FRAMES (fun st OW m a0 a1 a2 a3 a4 a5 bo => bo = bo0) err_new (fun r OW' m' a0' bo' => bo' = bo0).

Lemma ERR_new_specA_stmt : ERR_new_specA -> ERR_new_stmtA.
Proof.
  intros H. unfold ERR_new_stmtA, ERR_new_specA, ap_stmtA in *. intros until K. intros ras PRE TP UW CTX NE _ KOW KIDS.
  eapply implAp_mono; [eapply (H bo); [exact PRE|exact TP|exact UW|exact CTX|exact NE|reflexivity|exact KOW|exact KIDS]|].
  intros [a st'] Σ' ms' PO. cbv beta in PO |- *.
  destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & E1 & PRE2 & AXP2 & CRED2 & KEPT2 & RES2).
  do 17 eexists. exists m2, OW2, bo2. repeat (split; [eassumption|]). exact I.
Qed.

  (* [comment removed for export] *)
  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo : Z).
  Hypothesis IDS : ids_ok E st.
  Hypothesis CEIL : ACEIL <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ENW_STK.
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
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Variables (COST : Z).
  Hypothesis COST1 : 1 <= COST.
  Hypothesis FRM : Z.of_nat (length FR) + 0 <= Z.of_nat FRAMES_MAX.
  (* [comment removed for export] *)
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ERR_NEW (bv_unsigned ra :: ras).

  Let tn : nat := enew_top st.
  Let st1 : ap_st bptr := enew_st1 st.
  Local Notation W2 := ([(bv_unsigned sp - ENW_STK, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Let TREE := ofree (option_map fst (get_file tn (ecl_mid tn st1))) (ofree (option_map fst (get_func tn (ecl_mid tn st1))) (ARet (tt, ecl_fin tn st1))).
  Let POST := ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K COST
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0).
  Definition enw_frame : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

  Lemma TNB : (tn < 16)%nat.
  Proof. unfold tn, CtRepP.ApErrKit.enew_top, ring_next, ERR_NUM. apply Nat.mod_upper_bound. lia. Qed.
  Lemma BNB : (enew_bot st < 16)%nat.
  Proof.
    pose proof (ids_ok_top _ _ IDS) as [T B']. unfold CtRepP.ApErrKit.enew_bot, ring_next, ERR_NUM in *.
    destruct (Nat.eqb _ _); [apply Nat.mod_upper_bound; lia|exact B'].
  Qed.

  Local Ltac segW_tac HIN :=
    intros P HP; constructor; [left; cbn; clear - LO; unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia|]; constructor; [| constructor]; right; right;
    eexists _, _, _; split; [exact HIN|]; split; [exact HP | cbn; clear; lia].

  (* [comment removed for export] *)
  Lemma enw_finish : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σb : rts RT) (mb m9 : mem),
    let OW8 := lremove (get_func tn st) (lremove (get_file tn st) OW) in
    AHEAP Σb OW8 LB mb -> ax_pres LB (bv_unsigned sp) LIBW_A m mb -> ap_restA mb OW E bo0 (as_cnf st) ->
    (forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OW8 ++ LB)) -> In (p_es E, e_es E, 904) OW8 -> data_cells mb OW st -> kept K m mb ->
    (forall b, In b K -> In b OW8) ->
    rt_credit RT Σb = rt_credit RT Σ - 1 ->
    munch W2 mb m9 -> wmono ctasegs mb m9 ->
    es_raw m9 (e_es E) (g_of (ecl_fin tn st1) (badr OW)) -> stk ctasegs m9 lo (bv_unsigned sp) -> mem_inv ctasegs m9 ->
    POST (tt, ecl_fin tn st1) Σb
         (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m9 (seg_rom ctasegs)).
  Proof.
    intros until m9. cbn zeta. intros HEAPb AXb ARb RB IES8 DCb KPb KOW8 CR2 MU WM ES ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW8 := lremove (get_func tn st) (lremove (get_file tn st) OW)) in *.
    pose proof TNB as TNB'. pose proof BNB as BNB'.
    unfold USTACK_TOP in TOP.
    assert (IES8' : In (p_es E, e_es E, 904) (OW8 ++ LB)) by (apply in_or_app; left; exact IES8).
    assert (HW : forall P : bptr -> Prop, P (p_es E) -> Forall (segW (OW8 ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - ENW_STK, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) by segW_tac IES8'.
    destruct (seg_closeA Σb OW8 LB _ mb m9 lo (bv_unsigned sp) (fun p => p = p_es E) HEAPb CEIL ltac:(clear - LO; unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU WM (HW _ eq_refl))
      as [HEAP9 AX9].
    { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAPb) as ND. destruct (badr_size_unique (OW8 ++ LB) (p_es E) A n (e_es E) 904 ND HIN IES8') as [-> ->]. exact IES8. }
    assert (AR9 : ap_restA m9 OW E bo0 (as_cnf st)).
    { eapply (rest_of_segA Σb OW8 LB _ mb m9); [exact ARb|exact HEAPb|exact RB|exact CEIL|exact MU|].
      apply HW. destruct AS0 as [mI AS0']. eapply es_not_restA; [exact AS0'|exact IDS]. }
    assert (DIN8 : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW8 ++ LB)).
    { intros i q k Hd. apply in_app_iff. left. subst OW8. destruct (optb_ok_nth OW _ i q k OD Hd) as [HIn _].
      apply lremove_keep; [apply lremove_keep; [exact HIn|]|]; cbn.
      - intros q' n' G. apply not_eq_sym. eapply ids_file_data_ne; [exact IDS|exact G|exact Hd].
      - intros q' n' G. apply not_eq_sym. eapply ids_func_data_ne; [exact IDS|exact G|exact Hd]. }
    assert (DC9 : data_cells m9 OW st).
    { eapply (data_cells_of_munchA Σb OW8 LB _ mb m9); [exact DCb|exact DIN8|exact HEAPb|exact CEIL|exact MU|].
      apply HW. intros i q k Hd. eapply ids_data_es_ne; [exact IDS|exact Hd]. }
    (* [comment removed for export] *)
    destruct (st_blocks_ecl_fin tn st1 ltac:(unfold st1, CtRepP.ApErrKit.enew_st1; apply es_shape_setters; apply es_shape_setters; exact SH) ltac:(unfold ERR_NUM; exact TNB'))
      as (pre & PERM & Hpre).
    assert (GF1 : get_file tn st1 = get_file tn st) by reflexivity. assert (GN1 : get_func tn st1 = get_func tn st) by reflexivity.
    assert (SB1 : st_blocks st1 = st_blocks st) by reflexivity.
    rewrite GF1, GN1, SB1 in PERM.
    assert (IDS' : ids_ok E (ecl_fin tn st1)).
    { eapply ids_ok_sub; [exact PERM| | |eapply marks_sub_trans; [apply marks_sub_ecl_fin|apply marks_sub_enew_st1]|exact IDS]; unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid; cbn [as_top as_bottom set_func set_file set_line set_buf set_marks].
      - rewrite (proj1 (ecd_proj tn st1)). unfold st1, CtRepP.ApErrKit.enew_st1. cbn. unfold ERR_NUM. exact TNB'.
      - rewrite (proj1 (proj2 (ecd_proj tn st1))). unfold st1, CtRepP.ApErrKit.enew_st1. cbn. unfold ERR_NUM. exact BNB'. }
    assert (NOTPRE : forall p, In p (es_ids (ecl_fin tn st1)) ->
              (forall q n, get_file tn st = Some (q, n) -> p <> q) /\ (forall q n, get_func tn st = Some (q, n) -> p <> q)).
    { intros p Hp. pose proof (ids_pre_disjoint E st (ecl_fin tn st1) _ p IDS PERM Hp) as NI. rewrite !map_app, !in_app_iff in NI.
      split; intros q n G ->; apply NI; rewrite G; cbn; tauto. }
    pose proof (ecd_proj tn st1) as (PT & PB & PF & PN & PM & PU & PL & PC).
    assert (AS9 : ap_state (ecl_fin tn st1) m9 OW8 E bo0).
    { apply ap_state_joinA.
      - replace (as_cnf (ecl_fin tn st1)) with (as_cnf st) by (unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid; cbn [as_cnf set_func set_file set_line set_buf set_marks]; rewrite PC; reflexivity).
        subst OW8. apply rest_lremoveA; [apply rest_lremoveA; [exact AR9|]|].
        + intros q n GF. split; [eapply file_not_rest; [exact IDS|exact GF]|]. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF].
        + intros q n GN. split; [|eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]].
          intros Hin. eapply (func_not_rest st E OW tn q n IDS GN). rewrite rest_ids in Hin |- *. rewrite in_app_iff in Hin |- *.
          destruct Hin as [Hin|Hin]; [left; exact Hin|right]. revert Hin. clear. destruct (as_cnf st) as [[[lk lh] bk]|]; cbn; [|tauto].
          tauto.
      - unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid. do 5 apply es_shape_setters. unfold CtRepP.ApErrKit.ecd. destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; unfold st1, CtRepP.ApErrKit.enew_st1; repeat apply es_shape_setters; exact SH.
      - rewrite (g_of_adr_ext (ecl_fin tn st1) (badr OW8) (badr OW)); [exact ES| | |];
          intros p n Hin; subst OW8; destruct (NOTPRE p ltac:(eapply es_ids_in; eauto)) as [N1 N2];
          rewrite (badr_lremove (get_func tn st)) by (intros q k G; eapply N2; exact G);
          rewrite (badr_lremove (get_file tn st)) by (intros q k G; eapply N1; exact G); reflexivity.
      - subst OW8. apply optb_ok_lremove; [apply optb_ok_lremove|].
        + unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid. cbn [as_file set_func set_file set_line set_buf set_marks]. rewrite PF. unfold st1, CtRepP.ApErrKit.enew_st1. cbn [as_file set_bottom set_top]. apply optb_ok_lset_none. exact OF.
        + intros p n q k Hin G. exact (proj1 (NOTPRE p ltac:(eapply es_ids_in; left; exact Hin)) q k G).
        + intros p n q k Hin G. exact (proj2 (NOTPRE p ltac:(eapply es_ids_in; left; exact Hin)) q k G).
      - subst OW8. apply optb_ok_lremove; [apply optb_ok_lremove|].
        + unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid. cbn [as_func set_func set_file set_line set_buf set_marks]. rewrite PN. unfold st1, CtRepP.ApErrKit.enew_st1. cbn [as_func set_bottom set_top]. apply optb_ok_lset_none. exact OFN.
        + intros p n q k Hin G. exact (proj1 (NOTPRE p ltac:(eapply es_ids_in; right; left; exact Hin)) q k G).
        + intros p n q k Hin G. exact (proj2 (NOTPRE p ltac:(eapply es_ids_in; right; left; exact Hin)) q k G).
      - subst OW8. apply optb_ok_lremove; [apply optb_ok_lremove|].
        + unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid. cbn [as_data set_func set_file set_line set_buf set_marks]. unfold CtRepP.ApErrKit.ecd.
          destruct (negb _); [destruct (get_data _ _)|]; unfold st1, CtRepP.ApErrKit.enew_st1; cbn [as_data set_dflags set_data set_bottom set_top]; try apply optb_ok_lset_none; exact OD.
        + intros p n q k Hin G. exact (proj1 (NOTPRE p ltac:(eapply es_ids_in; right; right; exact Hin)) q k G).
        + intros p n q k Hin G. exact (proj2 (NOTPRE p ltac:(eapply es_ids_in; right; right; exact Hin)) q k G). }
    assert (DC9' : data_cells m9 OW8 (ecl_fin tn st1)).
    { apply (data_cells_subA m9 OW8 st).
      - eapply data_cells_OWA; [exact DC9|]. intros i q k Hd. subst OW8.
        rewrite (badr_lremove (get_func tn st)) by (intros q' n' G; apply not_eq_sym; eapply ids_func_data_ne; [exact IDS|exact G|exact Hd]).
        rewrite (badr_lremove (get_file tn st)) by (intros q' n' G; apply not_eq_sym; eapply ids_file_data_ne; [exact IDS|exact G|exact Hd]). reflexivity.
      - intros i q k Hd. exists i. apply (get_data_ecd tn st1). unfold get_data, CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid in Hd |- *.
        cbn [as_data set_func set_file set_line set_buf set_marks] in Hd. exact Hd.
      - unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid. eapply dflags_ok_same; [reflexivity|reflexivity|]. pose proof SH as (_ & _ & L3 & L4 & _).
        apply dflags_ok_ecd; [unfold st1, CtRepP.ApErrKit.enew_st1; cbn [as_data set_bottom set_top]; rewrite L3; exact TNB'
                            |unfold st1, CtRepP.ApErrKit.enew_st1; cbn [as_data as_dflags set_bottom set_top]; rewrite L3, L4; reflexivity
                            |eapply dflags_ok_same; [| |eapply data_cells_dflagsA; exact DCb]; reflexivity]. }
    assert (KP9 : kept K mb m9).
    { eapply (kept_of_munchA Σb OW8 LB _ mb m9 K lo); [exact HEAPb|intros b Hb; apply in_app_iff; left; apply KOW8; exact Hb|exact CEIL|exact MU|].
      apply HW. eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto. }
    (* [comment removed for export] *)
    unfold POST, ap_postA.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m9, OW8, bo0.
    split; [reflexivity|].
    split.
    { unfold ap_preA. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS'|]. split; [exact DC9'|]. split; [exact ST|]. split; [exact CEIL|].
      split; [clear - LO; unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia|]. split; [unfold USTACK_TOP; clear - TOP; lia|]. split; [exact AL16|]. split; [exact MI|].
      split; [pose proof (af_credit_nonneg RT AF Σb m9 (AH_art _ _ _ _ HEAP9)) as X; clear - X; lia|]. split; [clear; lia|]. clear - FRM. lia. }
    split; [eapply ax_pres_trans; [exact AXb | exact AX9]|].
    split; [clear - CR2 COST1; lia|].
    split; [| reflexivity].
    split; [exact KOW8|]. split; [| intros a Ha Hin; rewrite (KP9 a Ha Hin); exact (KPb a Ha Hin)].
    intros b Hb Hin. apply (KIDS b Hb). apply in_app_iff. left. eapply es_ids_sub_perm; [exact PERM|exact Hin].
  Qed.

  (* [comment removed for export] *)
  Lemma enw_tail2 : forall (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (Σ2 : rts RT) (mb mc : mem),
    AHEAP Σ2 OW LB mb -> ax_pres LB (bv_unsigned sp) LIBW_A m mb -> ap_restA mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    rt_credit RT Σ2 = rt_credit RT Σ - 1 ->
    munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -48) enw_frame ->
    stk ctasegs mc lo (bv_unsigned sp + -48) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of (ecd tn st1) (badr OW)) ->
    implAp TREE Σ2 POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz TP_A) x5 x6 x7 sp s1 (Z_to_bv 64 (e_es E + 4 * Z.of_nat tn)) x11 (Z_to_bv 64 (e_es E + 512 + 4 * Z.of_nat tn)) x13 x14 x15 x16 x17
               (Z_to_bv 64 SHB) (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F2 (wz ENW_TAIL) fc2 None mc (seg_rom ctasegs)).   (* [comment removed for export] *)
  Proof using AL16 AS0 BE CEIL COST1 CTX EES16 EESB EESP FRM IDS IES KIDS KOW LO OD OF OFN SH TOP UW.
    intros until mc. intros HEAPb AXb ARb DCb KPb CR2 MU2 WM2 FR ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    unfold USTACK_TOP in TOP. unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LO, MU2.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (KOWL : forall b, In b K -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; apply KOW; exact Hb).
    assert (SH1 : es_shape (ecd tn st1)).
    { unfold CtRepP.ApErrKit.ecd. destruct (negb _); [destruct (get_data _ _)|]; unfold st1, CtRepP.ApErrKit.enew_st1; repeat apply es_shape_setters; exact SH. }
    assert (GL : g_len (g_of (ecd tn st1) (badr OW))) by (apply g_len_of; exact SH1).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    assert (OFF2 : offshW [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IES') as (_ & _ & EESC & EESI & _).
    unfold enw_frame in FR. unfold ENW_TAIL, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    es_store (es_wr_ma mc (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m2.
    (* [comment removed for export] *)
    es_store (es_wr_fl m2 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m3.
    (* [comment removed for export] *)
    es_store (es_wr_bu m3 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m4.
    (* [comment removed for export] *)
    zstep. zstep. setreg 9 (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia).
    es_store (es_wr_li m4 (e_es E) _ tn (Z_to_bv 64 (-1)) ES GL TNB'). name_mem m5.
    (* [comment removed for export] *)
    pose proof (es_rd_fi m5 (e_es E) _ tn (wa (e_es E + 576 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. zstep. clear RD.
    do 3 zstep. zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (ecd_proj tn st1) as (_ & _ & PF & PN & _ & _ & _ & PC).
    assert (EF : get_file tn (ecl_mid tn st1) = get_file tn st) by (unfold get_file, CtRepP.ApErrKit.ecl_mid; cbn [as_file set_line set_buf set_marks]; rewrite PF; reflexivity).
    assert (EFN : get_func tn (ecl_mid tn st1) = get_func tn st) by (unfold get_func, CtRepP.ApErrKit.ecl_mid; cbn [as_func set_line set_buf set_marks]; rewrite PN; reflexivity).
    assert (EF' : nth tn (as_file (ecd tn st1)) None = get_file tn st) by (rewrite <- EF; unfold get_file, CtRepP.ApErrKit.ecl_mid; reflexivity).
    setreg 10 (wz (optr (badr OW) (get_file tn st)))
      ltac:(cbn [CtRepP.ApErrKit.g_fi CtRepP.ApErrKit.g_of CtRepP.ApErrKit.set_g_bu CtRepP.ApErrKit.set_g_fl CtRepP.ApErrKit.set_g_ma CtRepP.ApErrKit.set_g_li]; rewrite nth_wl_optr, EF'; reflexivity).
    (* [comment removed for export] *)
    assert (HW2 : forall P : bptr -> Prop, P (p_es E) -> Forall (segW (OW ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { intros P HP. constructor; [left; cbn; clear - LO; lia|]. constructor; [| constructor]. right; right. exists (p_es E), (e_es E), 904.
      split; [exact IES'|]. split; [exact HP | cbn; clear; lia]. }
    destruct (seg_closeA Σ2 OW LB _ mb m5 lo (bv_unsigned sp) (fun p => p = p_es E) HEAPb CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU2 WM2 (HW2 _ eq_refl))
      as [HEAP5 AX5].
    { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAPb) as ND. destruct (badr_size_unique (OW ++ LB) (p_es E) A n (e_es E) 904 ND HIN IES') as [-> ->]. exact IES. }
    assert (AR5 : ap_restA m5 OW E bo0 (as_cnf st)).
    { eapply (rest_of_segA Σ2 OW LB _ mb m5); [exact ARb|exact HEAPb|intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact ARb|exact Hb]|exact CEIL|exact MU2|].
      apply HW2. destruct AS0 as [mI AS0']. eapply es_not_restA; [exact AS0'|exact IDS]. }
    assert (AX5' : ax_pres LB (bv_unsigned sp) LIBW_A m m5) by (eapply ax_pres_trans; [exact AXb|exact AX5]).
    assert (KP5 : kept K m m5).
    { eapply kept_trans; [exact KPb|]. eapply (kept_of_munchA Σ2 OW LB _ mb m5 K lo); [exact HEAPb|exact KOWL|exact CEIL|exact MU2|].
      apply HW2. eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC5 : data_cells m5 OW st).
    { eapply (data_cells_of_munchA Σ2 OW LB _ mb m5); [exact DCb|exact DIN|exact HEAPb|exact CEIL|exact MU2|]. apply HW2. intros i q k Hd. eapply ids_data_es_ne; [exact IDS|exact Hd]. }
    assert (CS5 : crypto_statics m5) by (destruct AR5 as (_ & (CS & _) & _); exact CS).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR LO CEIL C1; lia).
    assert (UW5 : uw_chain USTACK_TOP m5 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { pose proof (AH_ceil _ _ _ _ HEAP5) as (Cq1 & Cq2 & Cq3).
      eapply (uw_call_ax m m5 _ _ _ _ 48 [C8 s4; C8 s3; C8 s2; C8 s1]);   (* [comment removed for export] *)
        [exact UW | exact AX5' | clear; lia | clear - LO CEIL Cq1; unfold BnHeapA.ACEIL, ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia
        | reflexivity | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - TOP; lia | apply bv_unsigned_in_range
        | rewrite !Z_to_bv_bv_unsigned; exact FR]. }
    clear MU2 WM2 ACCE.
    apply evt_done. subst TREE. rewrite EF, EFN.
    eapply CRYPTO_free_opt_walkAp with (lo := lo) (od := get_file tn st) (adr := badr OW) (OW := OW) (LB := LB);
      [exact HEAP5 | | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact CS5 | reflexivity
      | rewrite ESP; exact UW5 | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free1 CTX) | ].
    { destruct (get_file tn st) as [[qf nf]|] eqn:GF; [|exact I]. exact (proj1 (optb_ok_nth OW _ tn qf nf OF GF)). }
    intros Σ6 ms6 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F6 & fc6 & m6 & -> & MI6 & ST6 & AG6 & CR6 & HEAP6).
    rewrite (ret_pc_even ENW_FREE1_RA) by (clear; unfold ENW_FREE1_RA; lia). unfold ENW_FREE1_RA.
    (* [comment removed for export] *)
    pose proof (AH_nodup _ _ _ _ HEAP5) as ND5.
    assert (QF : forall q n, get_file tn st = Some (q, n) -> In q (map blk_id OW)).
    { intros q n GF. pose proof (proj1 (optb_ok_nth OW _ tn q n OF GF)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn. }
    assert (QFE : forall q n, get_file tn st = Some (q, n) -> In q (es_ids st)) by (intros q n GF; eapply es_ids_file; exact GF).
    set (OW6 := lremove (get_file tn st) OW) in *.
    assert (EOW6 : lremove (get_file tn st) (OW ++ LB) = OW6 ++ LB) by (subst OW6; apply (lremove_app (get_file tn st) OW LB ND5 QF)).
    assert (INCL6 : forall b, In b OW6 -> In b (OW6 ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES6 : In (p_es E, e_es E, 904) OW6).
    { subst OW6. apply lremove_keep; [exact IES|]. intros q n GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply QFE; exact GF]. }
    assert (IES6' : In (p_es E, e_es E, 904) (OW6 ++ LB)) by (apply INCL6; exact IES6).
    apply (rw_cells_agree _ _ _ _ _ AG6) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOP; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG6|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [exact IES6'|cbn; clear - Ha; lia]. }
    assert (RB6 : forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OW6 ++ LB)).
    { rewrite <- EOW6. apply rest_blocks_lremove; [intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact AR5|exact Hb]|].
      intros q n GF. eapply file_not_rest; [exact IDS|exact GF]. }
    assert (AR6 : ap_restA m6 OW E bo0 (as_cnf st)) by (eapply (rest_of_aclientA (OW6 ++ LB)); [exact AR5|exact AG6|exact RB6]).
    assert (AX6 : ax_pres LB (bv_unsigned sp) LIBW_A m m6) by (eapply ax_pres_trans; [exact AX5'| eapply (ax_pres_of_aclient OW6 LB); [exact AG6|clear; lia]]).
    assert (CS6 : crypto_statics m6) by (destruct AR6 as (_ & (CS & _) & _); exact CS).
    assert (DIN6 : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW6 ++ LB)).
    { intros i q k Hd. rewrite <- EOW6. apply lremove_keep; [eapply DIN; exact Hd|].
      intros q' n' G. cbn. apply not_eq_sym. eapply ids_file_data_ne; [exact IDS|exact G|exact Hd]. }
    assert (DC6 : data_cells m6 OW st) by (eapply (data_cells_aclientA (OW6 ++ LB)); [exact DC5|exact AG6|exact DIN6]).
    assert (KOW6 : forall b, In b K -> In b (OW6 ++ LB)).
    { intros b Hb. rewrite <- EOW6. eapply (K_lremove K); [exact KOWL| |exact Hb]. intros q n GF. eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF]. }
    assert (KP6 : kept K m m6) by (eapply kept_trans; [exact KP5|eapply (kept_of_aclientA K (OW6 ++ LB)); [exact AG6|exact KOW6]]).
    pose proof (AH_ceil _ _ _ _ HEAP6) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3.
    clear AG6 CS5 AR5 AX5 AX5' HEAP5 MI ST DC5 KP5 HEAPb AXb ARb DCb KPb C1 C2 C3 OFFE EESC EESI. rename ST6 into ST. rename MI6 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m6) as MU3. pose proof (wmono_refl ctasegs m6) as WM3.
    ablock HEAP6 IES6' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP6 IES6') as (_ & _ & EESC & EESI & _).
    apply implAp_from_evt.
    (* [comment removed for export] *)
    es_store (es_wr_fi m6 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m7.
    (* [comment removed for export] *)
    pose proof (es_rd_fu m7 (e_es E) _ tn (wa (e_es E + 768 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. zstep. clear RD.
    do 3 zstep. zstep.
    assert (EFN' : nth tn (as_func (ecd tn st1)) None = get_func tn st) by (rewrite <- EFN; unfold get_func, CtRepP.ApErrKit.ecl_mid; reflexivity).
    setreg 10 (wz (optr (badr OW) (get_func tn st)))
      ltac:(cbn [CtRepP.ApErrKit.g_fu CtRepP.ApErrKit.g_of CtRepP.ApErrKit.set_g_fi CtRepP.ApErrKit.set_g_bu CtRepP.ApErrKit.set_g_fl CtRepP.ApErrKit.set_g_ma CtRepP.ApErrKit.set_g_li]; rewrite nth_wl_optr, EFN'; reflexivity).
    (* [comment removed for export] *)
    assert (HW3 : forall P : bptr -> Prop, P (p_es E) -> Forall (segW (OW6 ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { intros P HP. constructor; [left; cbn; clear - LO; lia|]. constructor; [| constructor]. right; right. exists (p_es E), (e_es E), 904.
      split; [exact IES6'|]. split; [exact HP | cbn; clear; lia]. }
    destruct (seg_closeA Σ6 OW6 LB _ m6 m7 lo (bv_unsigned sp) (fun p => p = p_es E) HEAP6 CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU3 WM3 (HW3 _ eq_refl))
      as [HEAP7 AX7].
    { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAP6) as ND. destruct (badr_size_unique (OW6 ++ LB) (p_es E) A n (e_es E) 904 ND HIN IES6') as [-> ->]. exact IES6. }
    assert (AR7 : ap_restA m7 OW E bo0 (as_cnf st)).
    { eapply (rest_of_segA Σ6 OW6 LB _ m6 m7); [exact AR6|exact HEAP6|exact RB6|exact CEIL|exact MU3|].
      apply HW3. destruct AS0 as [mI AS0']. eapply es_not_restA; [exact AS0'|exact IDS]. }
    assert (AX7' : ax_pres LB (bv_unsigned sp) LIBW_A m m7) by (eapply ax_pres_trans; [exact AX6|exact AX7]).
    assert (KP7 : kept K m m7).
    { eapply kept_trans; [exact KP6|]. eapply (kept_of_munchA Σ6 OW6 LB _ m6 m7 K lo); [exact HEAP6|exact KOW6|exact CEIL|exact MU3|].
      apply HW3. eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto. }
    assert (DC7 : data_cells m7 OW st).
    { eapply (data_cells_of_munchA Σ6 OW6 LB _ m6 m7); [exact DC6|exact DIN6|exact HEAP6|exact CEIL|exact MU3|]. apply HW3. intros i q k Hd. eapply ids_data_es_ne; [exact IDS|exact Hd]. }
    assert (CS7 : crypto_statics m7) by (destruct AR7 as (_ & (CS & _) & _); exact CS).
    clear MU3 WM3 ACCE.
    assert (UW7 : uw_chain USTACK_TOP m7 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { pose proof (AH_ceil _ _ _ _ HEAP7) as (Cq1 & Cq2 & Cq3).
      eapply (uw_call_ax m m7 _ _ _ _ 48 [C8 s4; C8 s3; C8 s2; C8 s1]);   (* [comment removed for export] *)
        [exact UW | exact AX7' | clear; lia | clear - LO CEIL Cq1; unfold BnHeapA.ACEIL, ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia
        | reflexivity | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - TOP; lia | apply bv_unsigned_in_range
        | rewrite !Z_to_bv_bv_unsigned; exact FR]. }
    pose proof (AH_nodup _ _ _ _ HEAP6) as ND6.
    apply evt_done.
    eapply CRYPTO_free_opt_walkAp with (lo := lo) (od := get_func tn st) (adr := badr OW) (OW := OW6) (LB := LB);
      [exact HEAP7 | | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact CS7 | reflexivity
      | rewrite ESP; exact UW7 | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free2 CTX) | ].
    { destruct (get_func tn st) as [[qn nn]|] eqn:GN; [|exact I]. subst OW6. apply lremove_keep; [exact (proj1 (optb_ok_nth OW _ tn qn nn OFN GN))|].
      intros q n GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
    intros Σ8 ms8 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F8 & fc8 & m8 & -> & MI8 & ST8 & AG8 & CR8 & HEAP8).
    rewrite (ret_pc_even ENW_FREE2_RA) by (clear; unfold ENW_FREE2_RA; lia). unfold ENW_FREE2_RA.
    (* [comment removed for export] *)
    assert (QN : forall q n, get_func tn st = Some (q, n) -> In q (map blk_id OW6)).
    { intros q n GN. subst OW6. pose proof (proj1 (optb_ok_nth OW _ tn q n OFN GN)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map.
      apply lremove_keep; [exact HIn|]. intros q' n' GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
    assert (QNE : forall q n, get_func tn st = Some (q, n) -> In q (es_ids st)) by (intros q n GN; eapply es_ids_func; exact GN).
    set (OW8 := lremove (get_func tn st) OW6) in *.
    assert (EOW8 : lremove (get_func tn st) (OW6 ++ LB) = OW8 ++ LB) by (subst OW8; apply (lremove_app (get_func tn st) OW6 LB ND6 QN)).
    assert (INCL8 : forall b, In b OW8 -> In b (OW8 ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES8 : In (p_es E, e_es E, 904) OW8).
    { subst OW8. apply lremove_keep; [exact IES6|]. intros q n GN. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply QNE; exact GN]. }
    assert (IES8' : In (p_es E, e_es E, 904) (OW8 ++ LB)) by (apply INCL8; exact IES8).
    apply (rw_cells_agree _ _ _ _ _ AG8) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOP; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG8|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [exact IES8'|cbn; clear - Ha; lia]. }
    assert (RB8 : forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OW8 ++ LB)).
    { rewrite <- EOW8. apply rest_blocks_lremove; [exact RB6|]. intros q n GN. eapply func_not_rest; [exact IDS|exact GN]. }
    assert (AR8 : ap_restA m8 OW E bo0 (as_cnf st)) by (eapply (rest_of_aclientA (OW8 ++ LB)); [exact AR7|exact AG8|exact RB8]).
    assert (AX8 : ax_pres LB (bv_unsigned sp) LIBW_A m m8) by (eapply ax_pres_trans; [exact AX7'| eapply (ax_pres_of_aclient OW8 LB); [exact AG8|clear; lia]]).
    assert (DIN8 : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW8 ++ LB)).
    { intros i q k Hd. rewrite <- EOW8. apply lremove_keep; [eapply DIN6; exact Hd|].
      intros q' n' G. cbn. apply not_eq_sym. eapply ids_func_data_ne; [exact IDS|exact G|exact Hd]. }
    assert (DC8 : data_cells m8 OW st) by (eapply (data_cells_aclientA (OW8 ++ LB)); [exact DC7|exact AG8|exact DIN8]).
    assert (KOW8 : forall b, In b K -> In b (OW8 ++ LB)).
    { intros b Hb. rewrite <- EOW8. eapply (K_lremove K); [exact KOW6| |exact Hb]. intros q n GN. eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN]. }
    assert (KOW8' : forall b, In b K -> In b OW8).
    { intros b Hb. subst OW8 OW6. apply (K_lremove K); [intros b' Hb'; apply (K_lremove K); [exact KOW| |exact Hb']| |exact Hb].
      - intros q n GF. eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF].
      - intros q n GN. eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN]. }
    assert (KP8 : kept K m m8) by (eapply kept_trans; [exact KP7|eapply (kept_of_aclientA K (OW8 ++ LB)); [exact AG8|exact KOW8]]).
    assert (CR8' : rt_credit RT Σ8 = rt_credit RT Σ - 1) by (rewrite CR8, CR6; exact CR2).
    pose proof (AH_ceil _ _ _ _ HEAP8) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    clear AG8 CS7 AR7 AX7 AX7' HEAP7 MI ST CS6 AX6 AR6 HEAP6 RB6 KP6 KP7 DC6 DC7 D1 D2 D3 OFFE EESC EESI. rename ST8 into ST. rename MI8 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m8) as MU4. pose proof (wmono_refl ctasegs m8) as WM4.
    ablock HEAP8 IES8' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP8 IES8') as (_ & _ & EESC & EESI & _).
    apply implAp_from_evt.
    (* [comment removed for export] *)
    es_store (es_wr_fu m8 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m9.
    do 6 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    (* [comment removed for export] *)
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (ecl_fin tn st1) (badr OW)) in ES
        by (unfold CtRepP.ApErrKit.ecl_fin, CtRepP.ApErrKit.ecl_mid; rewrite g_of_set_func, g_of_set_file, g_of_set_line, g_of_set_buf, g_of_set_marks;
            cbn [CtRepP.ApErrKit.g_fl CtRepP.ApErrKit.g_ma CtRepP.ApErrKit.g_bu CtRepP.ApErrKit.g_da CtRepP.ApErrKit.g_ds CtRepP.ApErrKit.g_df CtRepP.ApErrKit.g_fi
                 CtRepP.ApErrKit.g_li CtRepP.ApErrKit.g_fu CtRepP.ApErrKit.g_top CtRepP.ApErrKit.g_bot CtRepP.ApErrKit.set_g_fl CtRepP.ApErrKit.set_g_ma
                 CtRepP.ApErrKit.set_g_bu CtRepP.ApErrKit.set_g_da CtRepP.ApErrKit.set_g_ds CtRepP.ApErrKit.set_g_df CtRepP.ApErrKit.set_g_fi CtRepP.ApErrKit.set_g_li
                 CtRepP.ApErrKit.set_g_fu CtRepP.ApErrKit.set_g_top CtRepP.ApErrKit.set_g_bot CtRepP.ApErrKit.g_of];
            unfold MallocRep.wz; cbn [optr]; rewrite (upd_zeros 16 tn TNB'); reflexivity)
    end.
    apply evt_done. apply implAp_ret.
    eapply (enw_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Σ8 m8 m9);
      [exact HEAP8|exact AX8|exact AR8|exact RB8|exact IES8|exact DC8|exact KP8|exact KOW8'|exact CR8'|exact MU4|exact WM4|exact ES|exact ST|exact MI].
  Qed.

  (* [comment removed for export] *)
  Lemma enw_tail1 : forall (x1 x5 x6 x7 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (Σ2 : rts RT) (mb mc : mem),
    AHEAP Σ2 OW LB mb -> ax_pres LB (bv_unsigned sp) LIBW_A m mb -> ap_restA mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    rt_credit RT Σ2 = rt_credit RT Σ - 1 ->
    munch W2 mb mc -> wmono ctasegs mb mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -48) enw_frame ->
    stk ctasegs mc lo (bv_unsigned sp + -48) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of st1 (badr OW)) ->
    implAp TREE Σ2 POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz TP_A) x5 x6 x7 sp s1 (Z_to_bv 64 (e_es E + 900)) (Z_to_bv 64 (e_es E)) x12 x13 (Z_to_bv 64 (Z.of_nat tn)) x15 x16 x17
               (Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F2 (wz ENW_CLEAR) fc2 None mc (seg_rom ctasegs)).   (* [comment removed for export] *)
  Proof using AL16 AS0 BE CEIL COST1 CTX EES16 EESB EESP FRM IDS IES KIDS KOW LO OD OF OFN SH TOP UW.
    intros until mc. intros HEAPb AXb ARb DCb KPb CR2 MU2 WM2 FR ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAPb) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    unfold USTACK_TOP in TOP. unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LO, MU2.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (KOWL : forall b, In b K -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; apply KOW; exact Hb).
    assert (SHs : es_shape st1) by (unfold st1, CtRepP.ApErrKit.enew_st1; repeat apply es_shape_setters; exact SH).
    assert (GL : g_len (g_of st1 (badr OW))) by (apply g_len_of; exact SHs).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    assert (OFF2 : offshW [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPb IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPb IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb IES') as (_ & _ & EESC & EESI & _).
    unfold enw_frame in FR. unfold ENW_CLEAR, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    ual. do 3 pstep. rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia).
    setreg 10 (Z_to_bv 64 (e_es E + 4 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia).
    setreg 12 (Z_to_bv 64 (e_es E + 512 + 4 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia).
    pose proof (es_rd_df1 mc (e_es E) _ tn (wa (e_es E + 512 + 4 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD.
    zstep. clear RD.
    do 4 pstep. (* [comment removed for export] *)
    set (f := get_dflags tn st1).
    rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia). (* [comment removed for export] *)
    setreg 15 (Z_to_bv 64 (Z.land f ERR_TXT_MALLOCED))
      ltac:(cbn [CtRepP.ApErrKit.g_df CtRepP.ApErrKit.g_of]; rewrite nth_wl; unfold zx8, MallocRep.wz; rewrite (unsigned_lit (_ mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned (Z_to_bv 64 (nth tn (as_dflags st1) 0))) (2 ^ 8) ltac:(clear; lia)); clear - H; lia);
            rewrite dflag_bit; reflexivity).
    assert (FR01 : 0 <= Z.land f ERR_TXT_MALLOCED <= 1) by apply land_malloced_range.
    setreg 19 (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia). (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (Z.of_nat tn * 8)) ltac:(f_equal; clear - TOPB; lia).
    setreg 11 (Z_to_bv 64 (e_es E + 256 + 8 * Z.of_nat tn)) ltac:(f_equal; clear - TOPB; lia). (* [comment removed for export] *)
    do 3 zstep. if_cases KF; zify_cond KF; rewrite land_malloced_mask in KF.
    - (* [comment removed for export] *)
      pose proof (es_rd_da mc (e_es E) _ tn (wa (e_es E + 256 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. zstep. clear RD.
      setreg 11 (Z_to_bv 64 (optr (badr OW) (get_data tn st1))) ltac:(cbn [CtRepP.ApErrKit.g_da CtRepP.ApErrKit.g_of]; rewrite nth_wl_optr; reflexivity).
      assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
      { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
      destruct (get_data tn st1) as [[pd nd]|] eqn:GD; cbn [optr].
      + (* [comment removed for export] *)
        assert (GD0 : get_data tn st = Some (pd, nd)) by exact GD.
        destruct (optb_ok_nth OW _ tn pd nd OD GD0) as [HINd HPd].
        pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPb (INCL _ HINd)) as (BD1 & BD2 & BD3 & BD4 & BD5).
        pose proof (blk_disjointA _ _ _ _ pd (badr OW pd) nd (p_es E) (e_es E) 904 HEAPb (INCL _ HINd) IES' ltac:(eapply ids_data_es_ne; [exact IDS|exact GD0])) as DJd.
        zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear - BD1 BD3 C3; lia); clear - K2 BD1; lia|]. clear K2.
        assert (HW2 : forall P : bptr -> Prop, P (p_es E) -> Forall (segW (OW ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
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
        { eapply kept_trans; [exact KPb|]. eapply (kept_of_munchA Σ2 OW LB _ mb mc K lo); [exact HEAPb|exact KOWL|exact CEIL|exact MU2|].
          apply HW2. eapply K_not_env; [exact KIDS|]. rewrite env_ids_unfold. cbn. tauto. }
        destruct (proj1 DCc tn pd nd GD0) as [ND1 [junkd HD]].
        assert (EK : exists k, Z.to_nat nd = S k) by (exists (Z.to_nat nd - 1)%nat; clear - ND1; lia). destruct EK as [kd EK]. rewrite EK in HD.
        apply (rw_cells_split_CB ctasegs mc (badr OW pd) [] (S kd) junkd [] [1%nat; kd]) in HD; [|cbn; clear; lia].
        cbn [mk_CB_cells app] in HD.
        clear MU2 WM2 ACCE OFFE.
        pose proof (munch_refl [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z mc) as MU3. pose proof (wmono_refl ctasegs mc) as WM3.
        assert (HINd' : In (pd, badr OW pd, nd) (OW ++ LB)) by (apply INCL; exact HINd).
        ablock HEAPc HINd' ACCD OFFD.
        assert (OFF3 : offshW [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z) by (cbn [offshW]; clear - OFFD BD2 C1 C2 CEIL LO; alia).
        zstep. (* [comment removed for export] *)
        name_mem m3. zstep. (* [comment removed for export] *)
        assert (HW3 : forall P : bptr -> Prop, P pd -> Forall (segW (OW ++ LB) lo (bv_unsigned sp) P) [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z).
        { intros P HP. constructor; [left; cbn; clear - LO; lia|]. constructor; [| constructor]. right; right. exists pd, (badr OW pd), nd.
          split; [exact HINd'|]. split; [exact HP | cbn; clear - ND1; lia]. }
        destruct (seg_closeA Σ2 OW LB _ mc m3 lo (bv_unsigned sp) (fun p => p = pd) HEAPc CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU3 WM3 (HW3 _ eq_refl))
          as [HEAP3 AX3].
        { intros p A n HIN ->. pose proof (AH_nodup _ _ _ _ HEAPc) as ND. destruct (badr_size_unique (OW ++ LB) pd A n (badr OW pd) nd ND HIN HINd') as [-> ->]. exact HINd. }
        assert (AR3 : ap_restA m3 OW E bo0 (as_cnf st)).
        { eapply (rest_of_segA Σ2 OW LB _ mc m3); [exact ARc|exact HEAPc|intros b Hb; apply INCL; eapply rest_blocks_OWA; [exact ARc|exact Hb]|exact CEIL|exact MU3|].
          apply HW3. eapply data_not_rest; [exact IDS|exact GD0]. }
        lazymatch type of HD with rw_cells _ _ _ ?cs =>
          pose proof (rw_cells_merge ctasegs m3 (badr OW pd) (@nil cell) cs (@nil cell) ltac:(rewrite app_nil_r; exact HD)) as HD' end.
        cbn [app cells_size csize cells_bytes cbytes length] in HD'.
        match type of HD' with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat nd) in HD' by (clear - EK; lia) end.
        assert (DC3 : data_cells m3 OW st).
        { eapply (data_cells_store1A Σ2 OW LB mc m3 OW st lo (bv_unsigned sp)); [exact DCc|exact DIN|exact HINd'|exact ND1|exact HEAPc|exact CEIL| | |exact MU3|exact HD']; clear - LO; lia. }
        eapply (es_raw_of_munchA Σ2 OW LB _ mc m3 E _ lo (bv_unsigned sp) (p_es E)) in ES; [|exact GL|exact IES'|exact HEAPc|exact CEIL|exact MU3|exact WM3|apply HW3; intros EQ; exact (ids_data_es_ne E st tn (p_es E) nd IDS ltac:(rewrite <- EQ; exact GD0) eq_refl)].
        assert (AX3' : ax_pres LB (bv_unsigned sp) LIBW_A m m3) by (eapply ax_pres_trans; [exact AXc'|exact AX3]).
        assert (KP3 : kept K m m3).
        { eapply kept_trans; [exact KPc|]. eapply (kept_of_munchA Σ2 OW LB _ mc m3 K lo); [exact HEAPc|exact KOWL|exact CEIL|exact MU3|].
          apply HW3. eapply K_not_es; [exact KIDS|]. eapply es_ids_data; exact GD0. }
        clear MU3 WM3 HD HD' HEAPc AXc AXc' ARc DCc KPc ACCD OFFD OFF3.
        pose proof (munch_refl [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m3) as MU4. pose proof (wmono_refl ctasegs m3) as WM4.
        ablock HEAP3 IES' ACCE OFFE.
        (* [comment removed for export] *)
        es_store (es_wr_df m3 (e_es E) _ tn (Z_to_bv 64 1) ES GL TNB'). name_mem m4.
        lazymatch type of ES with es_raw _ _ ?g =>
          replace g with (g_of (ecd tn st1) (badr OW)) in ES
            by (unfold CtRepP.ApErrKit.ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KF FR01; lia); cbn [negb];
                rewrite GD, g_of_set_dflags; unfold ERR_TXT_MALLOCED, MallocRep.wz; reflexivity)
        end.
        apply evt_done.
        eapply (enw_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 m3 _);
          [exact HEAP3|exact AX3'|exact AR3|exact DC3|exact KP3|exact CR2|exact MU4|exact WM4|exact FR|exact ST|exact MI|exact ES].
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; [|exfalso; rewrite ?unsigned_lit in K2 by (clear; lia); clear - K2; lia]. clear K2.
        replace (g_of st1 (badr OW)) with (g_of (ecd tn st1) (badr OW)) in ES
          by (unfold CtRepP.ApErrKit.ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KF FR01; lia); cbn [negb]; rewrite GD; reflexivity).
        apply evt_done.
        eapply (enw_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 mb _);
          [exact HEAPb|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR|exact ST|exact MI|exact ES].
    - (* [comment removed for export] *)
      es_store (es_wr_da mc (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m3.
      es_store (es_wr_ds m3 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m4.
      zstep. (* [comment removed for export] *)
      rewrite ?zxb_z8. rewrite KF.
      es_store (es_wr_df m4 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m5.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd tn st1) (badr OW)) in ES
          by (unfold CtRepP.ApErrKit.ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with true by (symmetry; apply Z.eqb_eq; clear - KF FR01; lia); cbn [negb];
              rewrite g_of_set_dflags, g_of_set_data; cbn [optr osize]; unfold MallocRep.wz; reflexivity)
      end.
      apply evt_done.
      eapply (enw_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 mb _);
        [exact HEAPb|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR|exact ST|exact MI|exact ES].
  Qed.

  (* [comment removed for export] *)
  Lemma enw_act : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    AHEAP Σ OW LB m -> ap_state st m OW E bo0 -> data_cells m OW st ->
    stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> tp = wz TP_A ->
    (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    implAp (err_new st) Σ POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_NEW) fc None m (seg_rom ctasegs)).
  Proof.
    intros until fc. intros HEAP AS DC ST MI -> FLEN CRED.
    unfold ERR_NEW, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LO. unfold USTACK_TOP in TOP.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    rewrite (err_new_tree st).
    pose proof (munch_refl [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z) by (cbn [offshW]; alia).
    apply implAp_from_evt.
    carve_frame 48%nat ST. do 9 zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    name_mem m0.
    assert (HW0 : Forall (segW (OW ++ LB) lo (bv_unsigned sp) (fun _ => False)) [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z).
    { constructor; [left; cbn; clear - LO; lia|]. constructor; [right; left; reflexivity | constructor]. }
    destruct (seg_closeA Σ OW LB _ m m0 lo (bv_unsigned sp) (fun _ => False) HEAP CEIL ltac:(clear - LO; lia) ltac:(unfold USTACK_TOP; clear - TOP; lia) MU WM HW0 ltac:(intros p A n _ []))
      as [HEAP0 AX0].
    assert (AS0' : ap_state st m0 OW E bo0) by (eapply (ap_state_of_munchA Σ st m m0); [exact AS | exact HEAP | exact CEIL | exact MU | exact HW0]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR LO CEIL C1; lia).
    destruct (errno_cellA m0) as [errv HERR].
    apply evt_done. intros X Φ D SAFE LINK.
    eapply (get_state_cpsA _) with (lo := lo) (OW := OW) (LB := LB) (E := E) (st := st) (bo := bo0) (v := 1);
      [exact HEAP0 | exact AS0' | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact FLEN | exact CRED
      | exact HERR | right; reflexivity | reflexivity |].
    intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 errv2 HEAP2 CR2 EL2 ST2 MI2 AG2 HERR2.
    rewrite ESP in ST2, AG2. rewrite (ret_pc_even ENW_RA1) by (clear; unfold ENW_RA1; lia). unfold ENW_RA1.
    eapply (implAp_elim TREE); [| exact SAFE | exact LINK | exact EL2].
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
    pose proof (munch_refl [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    assert (OFF2 : offshW [(bv_unsigned sp - (64 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAP2 IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAP2 IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP2 IES') as (_ & _ & EESC & EESI & _).
    unfold MallocRep.wz. apply implAp_from_evt.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - EESP EESB; lia); clear - KK EESP EESB; lia|]. clear KK. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    (* [comment removed for export] *)
    pose proof (es_rd_top m2 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD.
    ual. ub. ab. zstep. clear RD.
    cbn [CtRepP.ApErrKit.g_top CtRepP.ApErrKit.g_bot CtRepP.ApErrKit.g_of]. rewrite !sx32_small by (clear - TOPB; lia).
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 7 zstep.
    pose proof TNB as TNB'.
    setreg 14 (Z_to_bv 64 (Z.of_nat tn)) ltac:(unfold tn, CtRepP.ApErrKit.enew_top, ring_next, ERR_NUM; set (t := as_top st) in *; by_cases16 t TOPB).
    (* [comment removed for export] *)
    es_store (es_wr_top m2 (e_es E) _ (Z.of_nat tn) ES GL). name_mem m3.
    set (bot := as_bottom st) in *.
    (* [comment removed for export] *)
    pose proof (es_rd_bot m3 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. zstep. clear RD.
    cbn [CtRepP.ApErrKit.g_top CtRepP.ApErrKit.g_bot CtRepP.ApErrKit.g_of CtRepP.ApErrKit.set_g_top]. rewrite !sx32_small by (clear - BOTB; lia). fold bot.
    zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      assert (NEB : Nat.eqb tn bot = false) by (apply Nat.eqb_neq; intros EQ; apply KK; rewrite EQ; reflexivity).
      replace (set_g_top (Z.of_nat tn) (g_of st (badr OW))) with (g_of st1 (badr OW)) in ES
        by (unfold st1, CtRepP.ApErrKit.enew_st1, CtRepP.ApErrKit.enew_bot; fold tn bot; rewrite NEB; reflexivity).
      apply evt_done.
      eapply (enw_tail1 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 m2 _);
        [exact HEAP2|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR|exact ST2|exact MI2|exact ES].
    - (* [comment removed for export] *)
      assert (TB : tn = bot) by (apply Nat2Z.inj; exact KK).
      (* [comment removed for export] *)
      do 9 zstep.
      setreg 12 (Z_to_bv 64 (Z.of_nat (ring_next bot)))
        ltac:(rewrite TB; unfold ring_next, ERR_NUM; subst bot; set (b := as_bottom st) in *; by_cases16 b BOTB).
      es_store (es_wr_bot m3 (e_es E) _ (Z.of_nat (ring_next bot)) ES GL). name_mem m4.
      assert (EQB : Nat.eqb tn bot = true) by (apply Nat.eqb_eq; exact TB).
      replace (set_g_bot (Z.of_nat (ring_next bot)) (set_g_top (Z.of_nat tn) (g_of st (badr OW)))) with (g_of st1 (badr OW)) in ES
        by (unfold st1, CtRepP.ApErrKit.enew_st1, CtRepP.ApErrKit.enew_bot; fold tn bot; rewrite EQB; reflexivity).
      apply evt_done.
      eapply (enw_tail1 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ2 m2 _);
        [exact HEAP2|exact AXb|exact ARb|exact DCb|exact KPb|exact CR2|exact MU2|exact WM2|exact FR|exact ST2|exact MI2|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_new_walkA : ERR_new_specA.
  Proof.
    intros bo0. unfold ap_stmtA. intros until K. intros ras PRE TP UW CTX NE EBO KOW KIDS. subst bo.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    unfold ERR_NEW_STACK, ERR_NEW_COST, ERR_NEW_FRAMES in *.
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    eapply (enw_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo0 lo
              IDS CEIL ltac:(unfold ENW_STK, GET_STATE_STACK, IB_STACK, IB_FRAME; clear - LOSP; lia) TOP AL16 SH IES EESP EESB EES16 OF OFN OD (ex_intro _ m AS) K KOW KIDS
              ERR_NEW_COST ltac:(unfold ERR_NEW_COST; clear; lia) ltac:(clear - FRM; lia) ras UW CTX);
      [exact HEAP | exact AS | exact DC | exact ST | exact MI | exact TP | clear - FRM; unfold FRAMES_MAX in *; lia | clear - CRED; lia].
  Qed.

  Theorem ERR_new_closedA : ERR_new_stmtA.
  Proof. apply ERR_new_specA_stmt. exact ERR_new_walkA. Qed.

End WithRT.
