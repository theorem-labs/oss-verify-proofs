(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit HxpGetState.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac step := upre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := upre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

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

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

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
        by (let H := fresh in pose proof GL as H; unfold g_len in H |- *;
            cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fl set_g_ma set_g_bu set_g_da set_g_ds set_g_df set_g_fi set_g_li set_g_fu set_g_top set_g_bot] in H |- *;
            rewrite ?upd_length in H; rewrite ?upd_length; exact H);
      clear GL; rename GLn into GL
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ERR_new_spec : Prop := forall bo0 : Z * Z,
  ap_stmt ERR_NEW ERR_NEW_STACK (fun st OW m a0 a1 a2 a3 a4 a5 bo => bo = bo0) err_new (fun r OW' m' a0' bo' => bo' = bo0).

Lemma ap_post_mono : forall {A} ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K
    (RES RES' : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) r s' ms',
  (forall r OW' m' a bo, RES r OW' m' a bo -> RES' r OW' m' a bo) ->
  ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K RES r s' ms' ->
  ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K RES' r s' ms'.
Proof.
  intros until ms'. intros Himp PO. unfold ap_post in *.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & F' & fc' & m' & OW' & errv' & bo' & E1 & FR1 & FE1 & P1 & L1 & S1 & S2 & BK1 & R1).
  exists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, F', fc', m', OW', errv', bo'.
  repeat (split; [assumption|]). apply Himp. exact R1.
Qed.

Lemma ERR_new_spec_stmt : ERR_new_spec -> ERR_new_stmt.
Proof.
  intros H. unfold ERR_new_stmt, ERR_new_spec, ap_stmt in *. intros until K. intros PRE TP FRM _ KOW KIDS.
  eapply implM_mono; [eapply (H bo); [exact PRE|exact TP|exact FRM|reflexivity|exact KOW|exact KIDS]|].
  intros r s' ms' PO. eapply ap_post_mono; [|exact PO]. intros; exact I.
Qed.

Section Proofs.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo B : Z) (canary : word).
  Hypothesis IDS : ids_ok E st.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - (48 + 48 + 16 + 8192).
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis FRM : frm0 fc.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESC : e_es E + 904 <= alloc_ceiling.
  Hypothesis EESI : e_es E + 904 <= 65536 \/ 3493888 <= e_es E.
  Hypothesis EES16 : e_es E mod 16 = 0.
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists m0, ap_state st m0 OW E bo0.
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

  Let tn : nat := enew_top st.
  Let st1 : ap_st bptr := enew_st1 st.
  Local Notation W2 := ([(bv_unsigned sp - 48 - 16 - 8192, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Let TREE := ofree (option_map fst (get_file tn (ecl_mid tn st1))) (ofree (option_map fst (get_func tn (ecl_mid tn st1))) (ARet (tt, ecl_fin tn st1))).
  Let POST := ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0).

  Hypothesis CAN : canary = rr_guard.
  Hypothesis EA : errno_addr (Z_to_bv 64 RATP) = 3355012.

  Lemma TNB : (tn < 16)%nat.
  Proof. unfold tn, enew_top, ring_next, ERR_NUM. apply Nat.mod_upper_bound. lia. Qed.
  Lemma BNB : (enew_bot st < 16)%nat.
  Proof.
    pose proof (ids_ok_top _ _ IDS) as [T B']. unfold enew_bot, ring_next, ERR_NUM in *.
    destruct (Nat.eqb _ _); [apply Nat.mod_upper_bound; lia|exact B'].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_new_finish : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mb m9 : mem) (errv' : word) (sC : PState),
    let OW8 := lremove (get_func tn st) (lremove (get_file tn st) OW) in
    RHEAP sC (OW8 ++ LB) mb -> rauxv_ok mb B -> lx_pres LB (bv_unsigned sp) LIBW_AP m mb -> ap_rest mb OW E bo0 (as_cnf st) ->
    (forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OW8 ++ LB)) -> In (p_es E, e_es E, 904) OW8 -> data_cells mb OW st -> kept K m mb ->
    (forall b, In b K -> In b OW8) ->
    munch W2 mb m9 -> wmono ctusegs mb m9 ->
    es_raw m9 (e_es E) (g_of (ecl_fin tn st1) (badr OW)) -> stk ctusegs m9 lo (bv_unsigned sp) -> mem_inv ctusegs m9 ->
    rw_cells ctusegs m9 3355012 [C4 errv'] -> ps_so sC = ps_so s -> ps_fa sC = ps_fa s ->
    POST (tt, ecl_fin tn st1) sC
         (MS (mkR ra sp gp (wz RATP) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m9 (seg_rom ctusegs)).
  Proof.
    intros until sC. cbn zeta. intros HEAPb AUXb LXb ARb RB IES8 DCb KPb KOW8 MU WM ES ST MI ERR SO FA.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW8 := lremove (get_func tn st) (lremove (get_file tn st) OW)) in *.
    pose proof TNB as TNB'. pose proof BNB as BNB'.
    (* [comment removed for export] *)
    destruct (seg_close sC OW8 LB _ mb m9 lo (bv_unsigned sp) B HEAPb AUXb CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP9 & AUX9 & LX9).
    { constructor; [left; cbn; lia|]. constructor; [right; right; exists (p_es E), (e_es E), 904; split; [exact IES8|cbn; lia]|constructor]. }
    assert (AR9 : ap_rest m9 OW E bo0 (as_cnf st)).
    { eapply (rest_of_seg' sC (OW8 ++ LB) _ mb m9); [exact ARb|exact HEAPb|exact RB|exact CEIL|unfold GLOBALS_TOP; lia|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (p_es E), (e_es E), 904. split; [apply in_app_iff; left; exact IES8|].
      split; [destruct AS0 as [m0 AS0']; eapply es_not_rest; [exact AS0'|exact IDS]|cbn; lia]. }
    assert (DIN8 : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW8 ++ LB)).
    { intros i q k Hd. apply in_app_iff. left. subst OW8. destruct (optb_ok_nth OW _ i q k OD Hd) as [HIn _].
      apply lremove_keep; [apply lremove_keep; [exact HIn|]|]; cbn.
      - intros q' n' G. apply not_eq_sym. eapply ids_file_data_ne; [exact IDS|exact G|exact Hd].
      - intros q' n' G. apply not_eq_sym. eapply ids_func_data_ne; [exact IDS|exact G|exact Hd]. }
    assert (DC9 : data_cells m9 OW st).
    { eapply (data_cells_of_munch sC (OW8 ++ LB) _ mb m9); [exact DCb|exact DIN8|exact HEAPb|exact CEIL|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply in_app_iff; left; exact IES8|].
      split; [intros i q k Hd; eapply ids_data_es_ne; [exact IDS|exact Hd]|cbn; lia]. }
    (* [comment removed for export] *)
    destruct (st_blocks_ecl_fin tn st1 ltac:(unfold st1, enew_st1; apply es_shape_setters; apply es_shape_setters; exact SH) ltac:(unfold ERR_NUM; exact TNB'))
      as (pre & PERM & Hpre).
    assert (GF1 : get_file tn st1 = get_file tn st) by reflexivity. assert (GN1 : get_func tn st1 = get_func tn st) by reflexivity.
    assert (SB1 : st_blocks st1 = st_blocks st) by reflexivity.
    rewrite GF1, GN1, SB1 in PERM.
    assert (IDS' : ids_ok E (ecl_fin tn st1)).
    { eapply ids_ok_sub; [exact PERM| | |eapply marks_sub_trans; [apply marks_sub_ecl_fin|apply marks_sub_enew_st1]|exact IDS]; unfold ecl_fin, ecl_mid; cbn [as_top as_bottom set_func set_file set_line set_buf set_marks].
      - rewrite (proj1 (ecd_proj tn st1)). unfold st1, enew_st1. cbn. unfold ERR_NUM. exact TNB'.
      - rewrite (proj1 (proj2 (ecd_proj tn st1))). unfold st1, enew_st1. cbn. unfold ERR_NUM. exact BNB'. }
    assert (NOTPRE : forall p, In p (es_ids (ecl_fin tn st1)) ->
              (forall q n, get_file tn st = Some (q, n) -> p <> q) /\ (forall q n, get_func tn st = Some (q, n) -> p <> q)).
    { intros p Hp. pose proof (ids_pre_disjoint E st (ecl_fin tn st1) _ p IDS PERM Hp) as NI. rewrite !map_app, !in_app_iff in NI.
      split; intros q n G ->; apply NI; rewrite G; cbn; tauto. }
    (* [comment removed for export] *)
    pose proof (ecd_proj tn st1) as (PT & PB & PF & PN & PM & PU & PL & PC).
    assert (AS9 : ap_state (ecl_fin tn st1) m9 OW8 E bo0).
    { apply ap_state_join.
      - replace (as_cnf (ecl_fin tn st1)) with (as_cnf st) by (unfold ecl_fin, ecl_mid; cbn [as_cnf set_func set_file set_line set_buf set_marks]; rewrite PC; reflexivity).
        subst OW8. apply rest_lremove; [apply rest_lremove; [exact AR9|]|].
        + intros q n GF. split; [eapply file_not_rest; [exact IDS|exact GF]|]. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF].
        + intros q n GN. split; [|eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]].
          intros Hin. eapply (func_not_rest st E OW tn q n IDS GN). rewrite rest_ids in Hin |- *. rewrite in_app_iff in Hin |- *.
          destruct Hin as [Hin|Hin]; [left; exact Hin|right]. revert Hin. clear. destruct (as_cnf st) as [[[lk lh] bk]|]; cbn; [|tauto].
          tauto.
      - unfold ecl_fin, ecl_mid. do 5 apply es_shape_setters. unfold ecd. destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; unfold st1, enew_st1; repeat apply es_shape_setters; exact SH.
      - rewrite (g_of_adr_ext (ecl_fin tn st1) (badr OW8) (badr OW)); [exact ES| | |];
          intros p n Hin; subst OW8; destruct (NOTPRE p ltac:(eapply es_ids_in; eauto)) as [N1 N2];
          rewrite (badr_lremove (get_func tn st)) by (intros q k G; eapply N2; exact G);
          rewrite (badr_lremove (get_file tn st)) by (intros q k G; eapply N1; exact G); reflexivity.
      - subst OW8. apply optb_ok_lremove; [apply optb_ok_lremove|].
        + unfold ecl_fin, ecl_mid. cbn [as_file set_func set_file set_line set_buf set_marks]. rewrite PF. unfold st1, enew_st1. cbn [as_file set_bottom set_top]. apply optb_ok_lset_none. exact OF.
        + intros p n q k Hin G. exact (proj1 (NOTPRE p ltac:(eapply es_ids_in; left; exact Hin)) q k G).
        + intros p n q k Hin G. exact (proj2 (NOTPRE p ltac:(eapply es_ids_in; left; exact Hin)) q k G).
      - subst OW8. apply optb_ok_lremove; [apply optb_ok_lremove|].
        + unfold ecl_fin, ecl_mid. cbn [as_func set_func set_file set_line set_buf set_marks]. rewrite PN. unfold st1, enew_st1. cbn [as_func set_bottom set_top]. apply optb_ok_lset_none. exact OFN.
        + intros p n q k Hin G. exact (proj1 (NOTPRE p ltac:(eapply es_ids_in; right; left; exact Hin)) q k G).
        + intros p n q k Hin G. exact (proj2 (NOTPRE p ltac:(eapply es_ids_in; right; left; exact Hin)) q k G).
      - subst OW8. apply optb_ok_lremove; [apply optb_ok_lremove|].
        + unfold ecl_fin, ecl_mid. cbn [as_data set_func set_file set_line set_buf set_marks]. unfold ecd.
          destruct (negb _); [destruct (get_data _ _)|]; unfold st1, enew_st1; cbn [as_data set_dflags set_data set_bottom set_top]; try apply optb_ok_lset_none; exact OD.
        + intros p n q k Hin G. exact (proj1 (NOTPRE p ltac:(eapply es_ids_in; right; right; exact Hin)) q k G).
        + intros p n q k Hin G. exact (proj2 (NOTPRE p ltac:(eapply es_ids_in; right; right; exact Hin)) q k G). }
    assert (DC9' : data_cells m9 OW8 (ecl_fin tn st1)).
    { apply (data_cells_sub m9 OW8 st).
      - eapply data_cells_OW; [exact DC9|]. intros i q k Hd. subst OW8.
        rewrite (badr_lremove (get_func tn st)) by (intros q' n' G; apply not_eq_sym; eapply ids_func_data_ne; [exact IDS|exact G|exact Hd]).
        rewrite (badr_lremove (get_file tn st)) by (intros q' n' G; apply not_eq_sym; eapply ids_file_data_ne; [exact IDS|exact G|exact Hd]). reflexivity.
      - intros i q k Hd. exists i. apply (get_data_ecd tn st1). unfold get_data, ecl_fin, ecl_mid in Hd |- *.
        cbn [as_data set_func set_file set_line set_buf set_marks] in Hd. exact Hd.
      - unfold ecl_fin, ecl_mid. eapply dflags_ok_same; [reflexivity|reflexivity|]. pose proof SH as (_ & _ & L3 & L4 & _).
        apply dflags_ok_ecd; [unfold st1, enew_st1; cbn [as_data set_bottom set_top]; rewrite L3; exact TNB'
                            |unfold st1, enew_st1; cbn [as_data as_dflags set_bottom set_top]; rewrite L3, L4; reflexivity
                            |eapply dflags_ok_same; [| |eapply data_cells_dflags; exact DCb]; reflexivity]. }
    assert (KP9 : kept K mb m9).
    { eapply (kept_of_munch sC (OW8 ++ LB) _ mb m9 K lo); [exact HEAPb|intros b Hb; apply in_app_iff; left; apply KOW8; exact Hb|exact CEIL|exact MU|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply in_app_iff; left; exact IES8|].
      split; [eapply K_not_env; [exact KIDS|]; rewrite env_ids_unfold; cbn; tauto|cbn; lia]. }
    (* [comment removed for export] *)
    unfold POST, ap_post.
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m9, OW8, errv', bo0.
    split; [reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
    split; [|split; [eapply lx_pres_trans; [exact LXb|exact LX9]|split; [exact SO|split; [exact FA|split; [|reflexivity]]]]].
    2:{ split; [exact KOW8|]. split; [|eapply kept_trans; [exact KPb|exact KP9]].
        intros b Hb Hin. apply (KIDS b Hb). apply in_app_iff. left. eapply es_ids_sub_perm; [exact PERM|exact Hin]. }
    unfold ap_pre. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS'|]. split; [exact DC9'|]. split; [exact AUX9|]. split; [exact SPB|]. split; [exact B63|].
    split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; exact GLO|]. split; [lia|].
    split. { unfold MallocRep.wz. rewrite EA. exact ERR. } split. { rewrite CAN. eapply RHEAP_ssp. exact HEAP9. } split. { exact MI. } exact SP16.
  Qed.


  (* [comment removed for export] *)
  Lemma ERR_new_tail2 : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mb mc : mem) (j0 : list byte) (errv2 : word),
    RHEAP s (OW ++ LB) mb -> rauxv_ok mb B -> lx_pres LB (bv_unsigned sp) LIBW_AP m mb -> ap_rest mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    munch W2 mb mc -> wmono ctusegs mb mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -48) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of (ecd tn st1) (badr OW)) ->
    implM ctusegs (interp (ap_embed TREE)) s POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 (e_es E))
              (Z_to_bv 64 (Z.of_nat tn * 4)) (Z_to_bv 64 (e_es E + 4 * Z.of_nat tn)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat tn * 8)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe7ec4) fc None mc (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EES16 EESC EESI EESP FRM GLO HF IDS IES KIDS KOW LO OD OF OFN SH SP16 SPB.
    intros until errv2. intros HEAPb AUXb LXb ARb DCb KPb MU2 WM2 FR ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (KOWL : forall b, In b K -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; apply KOW; exact Hb).
    assert (SH1 : es_shape (ecd tn st1)).
    { unfold ecd. destruct (negb _); [destruct (get_data _ _)|]; unfold st1, enew_st1; repeat apply es_shape_setters; exact SH. }
    assert (GL : g_len (g_of (ecd tn st1) (badr OW))) by (apply g_len_of; exact SH1).
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. es_store (es_wr_ma mc (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m1.
    (* [comment removed for export] *)
    step. step. es_store (es_wr_fl m1 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m3.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. step. step. es_store (es_wr_bu m3 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m4.
    do 4 step. setreg 19 (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) ltac:(rewrite ?unsigned_lit by lia; f_equal; lia).
    es_store (es_wr_li m4 (e_es E) _ tn (Z_to_bv 64 (-1)) ES GL TNB'). name_mem m5.
    pose proof (es_rd_fi m5 (e_es E) _ tn (wa (e_es E + 576 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
    do 4 step.
    (* [comment removed for export] *)
    pose proof (ecd_proj tn st1) as (_ & _ & PF & PN & _ & _ & _ & PC).
    assert (EF : get_file tn (ecl_mid tn st1) = get_file tn st) by (unfold get_file, ecl_mid; cbn [as_file set_line set_buf set_marks]; rewrite PF; reflexivity).
    assert (EFN : get_func tn (ecl_mid tn st1) = get_func tn st) by (unfold get_func, ecl_mid; cbn [as_func set_line set_buf set_marks]; rewrite PN; reflexivity).
    assert (EF' : nth tn (as_file (ecd tn st1)) None = get_file tn st) by (rewrite <- EF; unfold get_file, ecl_mid; reflexivity).
    setreg 10 (wz (optr (badr OW) (get_file tn st))) ltac:(cbn [g_fi g_of set_g_bu set_g_fl set_g_ma set_g_li]; rewrite nth_wl_optr, EF'; reflexivity).
    (* [comment removed for export] *)
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    destruct (seg_close s OW LB _ mb m5 lo (bv_unsigned sp) B HEAPb AUXb CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU2 WM2) as (HEAP5 & AUX5 & LX5).
    { constructor; [left; cbn; lia|]. constructor; [right; right; exists (p_es E), (e_es E), 904; split; [exact IES|cbn; lia]|constructor]. }
    assert (AR5 : ap_rest m5 OW E bo0 (as_cnf st)).
    { eapply (rest_of_seg s (OW ++ LB) _ mb m5); [right; exact ARb|exact IDS|exact AS0|exact HEAPb|exact INCL|exact CEIL|unfold GLOBALS_TOP; lia|exact MU2|exact WM2|].
      constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold ES_SIZE; lia|constructor]. }
    assert (LX5' : lx_pres LB (bv_unsigned sp) LIBW_AP m m5) by (eapply lx_pres_trans; [exact LXb|exact LX5]).
    assert (KP5 : kept K m m5).
    { eapply kept_trans; [exact KPb|]. eapply (kept_of_munch s (OW ++ LB) _ mb m5 K lo); [exact HEAPb|exact KOWL|exact CEIL|exact MU2|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
      split; [eapply K_not_env; [exact KIDS|]; rewrite env_ids_unfold; cbn; tauto|cbn; lia]. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC5 : data_cells m5 OW st).
    { eapply (data_cells_of_munch s (OW ++ LB) _ mb m5); [exact DCb|exact DIN|exact HEAPb|exact CEIL|exact MU2|exact WM2|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
      split; [intros i q k Hd; eapply ids_data_es_ne; [exact IDS|exact Hd]|cbn; lia]. }
    assert (CS5 : crypto_statics m5) by (destruct AR5 as (_ & _ & (CS & _) & _); exact CS).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    clear MU2 WM2.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    subst TREE. rewrite EF, EFN. rewrite (ap_embed_ofree (option_map fst (get_file tn st))).
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv2) (od := get_file tn st) (adr := badr OW) (L := OW ++ LB);
      [exact HEAP5 | | exact AUX5 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI | reflexivity
      | exact CS5 | reflexivity | ].
    { destruct (get_file tn st) as [[qf nf]|] eqn:GF; [|exact I]. apply INCL. exact (proj1 (optb_ok_nth OW _ tn qf nf OF GF)). }
    intros sB msB PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
    replace (ret_pc (Z_to_bv 64 0xe7f30)) with (Z_to_bv 64 0xe7f30) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR6. change (3355176 - 164) with 3355012 in ERR6.
    (* [comment removed for export] *)
    pose proof (LH_nodup _ _ _ HEAP5) as ND5.
    assert (QF : forall q n, get_file tn st = Some (q, n) -> In q (map blk_id OW)).
    { intros q n GF. pose proof (proj1 (optb_ok_nth OW _ tn q n OF GF)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn. }
    assert (QFE : forall q n, get_file tn st = Some (q, n) -> In q (es_ids st)) by (intros q n GF; eapply es_ids_file; exact GF).
    rewrite (lremove_app (get_file tn st) OW LB ND5 QF) in HEAP6, HP6.
    set (OW6 := lremove (get_file tn st) OW) in *.
    assert (INCL6 : forall b, In b OW6 -> In b (OW6 ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES6 : In (p_es E, e_es E, 904) OW6).
    { subst OW6. apply lremove_keep; [exact IES|]. intros q n GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply QFE; exact GF]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
    apply (rw_cells_agree _ _ _ _ _ AG6) in FR; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG6|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [apply in_app_iff; left; exact IES6|cbn; lia]. }
    assert (AR6 : ap_rest m6 OW E bo0 (as_cnf st)).
    { eapply rest_of_heap_pres; [exact AR5|exact HP6|]. rewrite <- (lremove_app (get_file tn st) OW LB ND5 QF).
      apply rest_blocks_lremove; [intros b Hb; apply INCL; eapply rest_blocks_OW; [exact AR5|exact Hb]|]. intros q n GF. eapply file_not_rest; [exact IDS|exact GF]. }
    assert (RB6 : forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OW6 ++ LB)).
    { rewrite <- (lremove_app (get_file tn st) OW LB ND5 QF). apply rest_blocks_lremove; [intros b Hb; apply INCL; eapply rest_blocks_OW; [exact AR5|exact Hb]|].
      intros q n GF. eapply file_not_rest; [exact IDS|exact GF]. }
    assert (LX6 : lx_pres LB (bv_unsigned sp) LIBW_AP m m6).
    { eapply lx_pres_trans; [exact LX5'|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6|lia|].
      intros b Hb. apply in_app_iff. right. exact Hb. }
    assert (CS6 : crypto_statics m6) by (destruct AR6 as (_ & _ & (CS & _) & _); exact CS).
    assert (DIN6 : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW6 ++ LB)).
    { intros i q k Hd. subst OW6. rewrite <- (lremove_app (get_file tn st) OW LB ND5 QF). apply lremove_keep; [eapply DIN; exact Hd|].
      intros q' n' G. cbn. apply not_eq_sym. eapply ids_file_data_ne; [exact IDS|exact G|exact Hd]. }
    assert (DC6 : data_cells m6 OW st) by (eapply data_cells_heap_pres; [exact DC5|exact HP6|exact DIN6]).
    assert (KOW6 : forall b, In b K -> In b (OW6 ++ LB)).
    { intros b Hb. rewrite <- (lremove_app (get_file tn st) OW LB ND5 QF). eapply (K_lremove K); [exact KOWL| |exact Hb].
      intros q n GF. eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF]. }
    assert (KP6 : kept K m m6) by (eapply kept_trans; [exact KP5|eapply kept_of_heap_pres; [exact HP6|exact KOW6]]).
    clear AG6 HP6 CS5 AR5 LX5 LX5' HEAP5 AUX5 MI ST ERR2 DC5 KP5. rename ST6 into ST. rename MI6 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 48 - 16 - 8192, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m6) as MU3. pose proof (wmono_refl ctusegs m6) as WM3.
    unfold implM. iprefix.
    step. step. es_store (es_wr_fi m6 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m7.
    setreg 9 (Z_to_bv 64 (e_es E + 768 + 8 * Z.of_nat tn)) ltac:(rewrite ?unsigned_lit by lia; f_equal; lia).
    pose proof (es_rd_fu m7 (e_es E) _ tn (wa (e_es E + 768 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
    do 4 step.
    assert (EFN' : nth tn (as_func (ecd tn st1)) None = get_func tn st) by (rewrite <- EFN; unfold get_func, ecl_mid; reflexivity).
    setreg 10 (wz (optr (badr OW) (get_func tn st))) ltac:(cbn [g_fu g_of set_g_fi set_g_bu set_g_fl set_g_ma set_g_li]; rewrite nth_wl_optr, EFN'; reflexivity).
    (* [comment removed for export] *)
    destruct (seg_close sB OW6 LB _ m6 m7 lo (bv_unsigned sp) B HEAP6 AUX6 CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU3 WM3) as (HEAP7 & AUX7 & LX7).
    { constructor; [left; cbn; lia|]. constructor; [right; right; exists (p_es E), (e_es E), 904; split; [exact IES6|cbn; lia]|constructor]. }
    assert (AR7 : ap_rest m7 OW E bo0 (as_cnf st)).
    { eapply (rest_of_seg' sB (OW6 ++ LB) _ m6 m7); [exact AR6|exact HEAP6|exact RB6|exact CEIL|unfold GLOBALS_TOP; lia|exact MU3|exact WM3|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (p_es E), (e_es E), 904. split; [apply in_app_iff; left; exact IES6|].
        split; [destruct AS0 as [m0 AS0']; eapply es_not_rest; [exact AS0'|exact IDS]|cbn; lia]. }
    assert (LX7' : lx_pres LB (bv_unsigned sp) LIBW_AP m m7) by (eapply lx_pres_trans; [exact LX6|exact LX7]).
    assert (KP7 : kept K m m7).
    { eapply kept_trans; [exact KP6|]. eapply (kept_of_munch sB (OW6 ++ LB) _ m6 m7 K lo); [exact HEAP6|exact KOW6|exact CEIL|exact MU3|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL6; exact IES6|].
      split; [eapply K_not_env; [exact KIDS|]; rewrite env_ids_unfold; cbn; tauto|cbn; lia]. }
    assert (DC7 : data_cells m7 OW st).
    { eapply (data_cells_of_munch sB (OW6 ++ LB) _ m6 m7); [exact DC6|exact DIN6|exact HEAP6|exact CEIL|exact MU3|exact WM3|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL6; exact IES6|].
      split; [intros i q k Hd; eapply ids_data_es_ne; [exact IDS|exact Hd]|cbn; lia]. }
    assert (CS7 : crypto_statics m7) by (destruct AR7 as (_ & _ & (CS & _) & _); exact CS).
    clear MU3 WM3.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    rewrite (ap_embed_ofree (option_map fst (get_func tn st))).
    pose proof (LH_nodup _ _ _ HEAP6) as ND6.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv2) (od := get_func tn st) (adr := badr OW) (L := OW6 ++ LB);
      [exact HEAP7 | | exact AUX7 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR6 | exact MI | reflexivity
      | exact CS7 | reflexivity | ].
    { destruct (get_func tn st) as [[qn nn]|] eqn:GN; [|exact I]. apply INCL6. subst OW6. apply lremove_keep; [exact (proj1 (optb_ok_nth OW _ tn qn nn OFN GN))|].
      intros q n GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
    intros sC msC PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m8
                    & -> & MI8 & ST8 & ERR8 & AUX8 & HP8 & FA8 & SO8 & HEAP8).
    replace (ret_pc (Z_to_bv 64 0xe7f58)) with (Z_to_bv 64 0xe7f58) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR8. change (3355176 - 164) with 3355012 in ERR8.
    (* [comment removed for export] *)
    assert (QN : forall q n, get_func tn st = Some (q, n) -> In q (map blk_id OW6)).
    { intros q n GN. subst OW6. pose proof (proj1 (optb_ok_nth OW _ tn q n OFN GN)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map.
      apply lremove_keep; [exact HIn|]. intros q' n' GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
    assert (QNE : forall q n, get_func tn st = Some (q, n) -> In q (es_ids st)) by (intros q n GN; eapply es_ids_func; exact GN).
    rewrite (lremove_app (get_func tn st) OW6 LB ND6 QN) in HEAP8, HP8.
    set (OW8 := lremove (get_func tn st) OW6) in *.
    assert (INCL8 : forall b, In b OW8 -> In b (OW8 ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES8 : In (p_es E, e_es E, 904) OW8).
    { subst OW8. apply lremove_keep; [exact IES6|]. intros q n GN. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply QNE; exact GN]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP8) as AG8.
    apply (rw_cells_agree _ _ _ _ _ AG8) in FR; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG8|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [apply in_app_iff; left; exact IES8|cbn; lia]. }
    assert (AR8 : ap_rest m8 OW E bo0 (as_cnf st)).
    { eapply rest_of_heap_pres; [exact AR7|exact HP8|]. rewrite <- (lremove_app (get_func tn st) OW6 LB ND6 QN).
      apply rest_blocks_lremove; [exact RB6|]. intros q n GN. eapply func_not_rest; [exact IDS|exact GN]. }
    assert (RB8 : forall b, In b (rest_blocks OW E (as_cnf st)) -> In b (OW8 ++ LB)).
    { rewrite <- (lremove_app (get_func tn st) OW6 LB ND6 QN). apply rest_blocks_lremove; [exact RB6|]. intros q n GN. eapply func_not_rest; [exact IDS|exact GN]. }
    assert (LX8 : lx_pres LB (bv_unsigned sp) LIBW_AP m m8).
    { eapply lx_pres_trans; [exact LX7'|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP8|lia|].
      intros b Hb. apply in_app_iff. right. exact Hb. }
    assert (DIN8 : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW8 ++ LB)).
    { intros i q k Hd. subst OW8. rewrite <- (lremove_app (get_func tn st) OW6 LB ND6 QN). apply lremove_keep; [eapply DIN6; exact Hd|].
      intros q' n' G. cbn. apply not_eq_sym. eapply ids_func_data_ne; [exact IDS|exact G|exact Hd]. }
    assert (DC8 : data_cells m8 OW st) by (eapply data_cells_heap_pres; [exact DC7|exact HP8|exact DIN8]).
    assert (KOW8 : forall b, In b K -> In b (OW8 ++ LB)).
    { intros b Hb. rewrite <- (lremove_app (get_func tn st) OW6 LB ND6 QN). eapply (K_lremove K); [exact KOW6| |exact Hb].
      intros q n GN. eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN]. }
    assert (KOW8' : forall b, In b K -> In b OW8).
    { intros b Hb. subst OW8 OW6. apply (K_lremove K); [intros b' Hb'; apply (K_lremove K); [exact KOW| |exact Hb']| |exact Hb].
      - intros q n GF. eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF].
      - intros q n GN. eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN]. }
    assert (KP8 : kept K m m8) by (eapply kept_trans; [exact KP7|eapply kept_of_heap_pres; [exact HP8|exact KOW8]]).
    clear AG8 HP8 CS7 AR7 LX7 LX7' HEAP7 AUX7 MI ST ERR6 CS6 LX6 AR6 HEAP6 AUX6 RB6 KP6 KP7. rename ST8 into ST. rename MI8 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 48 - 16 - 8192, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m8) as MU4. pose proof (wmono_refl ctusegs m8) as WM4.
    unfold implM. iprefix.
    es_store (es_wr_fu m8 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m9.
    do 5 step. step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (ecl_fin tn st1) (badr OW)) in ES
        by (unfold ecl_fin, ecl_mid; rewrite g_of_set_func, g_of_set_file, g_of_set_line, g_of_set_buf, g_of_set_marks;
            cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fl set_g_ma set_g_bu set_g_da set_g_ds set_g_df set_g_fi set_g_li set_g_fu set_g_top set_g_bot g_of];
            unfold MallocRep.wz; cbn [optr]; rewrite (upd_zeros 16 tn TNB'); reflexivity)
    end.
    apply evt_done. cbn [ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
    eapply (ERR_new_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 m9 errv2 sC);
      [exact HEAP8|exact AUX8|exact LX8|exact AR8|exact RB8|exact IES8|exact DC8|exact KP8|exact KOW8'|exact MU4|exact WM4|exact ES|exact ST|exact MI|exact ERR8
      |rewrite SO8; exact SO6|rewrite FA8; exact FA6].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_new_tail1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mb mc : mem) (errv2 : word) (j0 : list byte),
    RHEAP s (OW ++ LB) mb -> rauxv_ok mb B -> lx_pres LB (bv_unsigned sp) LIBW_AP m mb -> ap_rest mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    munch W2 mb mc -> wmono ctusegs mb mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -48) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of st1 (badr OW)) ->
    implM ctusegs (interp (ap_embed TREE)) s POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 (e_es E)) x10
              x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat tn)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe7e4c) fc None mc (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EES16 EESC EESI EESP FRM GLO HF IDS IES KIDS KOW LO OD OF OFN SH SP16 SPB.
    intros until j0. intros HEAPb AUXb LXb ARb DCb KPb MU2 WM2 FR ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (KOWL : forall b, In b K -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; apply KOW; exact Hb).
    assert (SHs : es_shape st1) by (unfold st1, enew_st1; repeat apply es_shape_setters; exact SH).
    assert (GL : g_len (g_of st1 (badr OW))) by (apply g_len_of; exact SHs).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    unfold implM. iprefix.
    upre. rewrite ?(unsigned_lit (Z.of_nat tn)) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    setreg 10 (Z_to_bv 64 (Z.of_nat tn * 4)) ltac:(f_equal; lia).
    setreg 11 (Z_to_bv 64 (e_es E + 4 * Z.of_nat tn)) ltac:(f_equal; lia).
    setreg 12 (Z_to_bv 64 (e_es E + 512 + 4 * Z.of_nat tn)) ltac:(f_equal; lia).
    pose proof (es_rd_df1 mc (e_es E) _ tn (wa (e_es E + 512 + 4 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD.
    OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. clear RD.
    set (f := get_dflags tn st1).
    step. step. step. step. rewrite ?(unsigned_lit (Z.of_nat tn)) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    setreg 18 (Z_to_bv 64 (Z.of_nat tn * 8)) ltac:(f_equal; lia).
    setreg 13 (Z_to_bv 64 (e_es E + 256 + 8 * Z.of_nat tn)) ltac:(f_equal; lia).
    setreg 15 (Z_to_bv 64 (Z.land f ERR_TXT_MALLOCED))
      ltac:(cbn [g_df g_of]; rewrite nth_wl; unfold zx8, MallocRep.wz; rewrite (unsigned_lit (_ mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned (Z_to_bv 64 (nth tn (as_dflags st1) 0))) (2 ^ 8) ltac:(lia)); lia);
            rewrite dflag_bit; reflexivity).
    assert (FR01 : 0 <= Z.land f ERR_TXT_MALLOCED <= 1) by apply land_malloced_range.
    step. if_cases KF; zify_cond KF; rewrite land_malloced_mask in KF.
    - (* [comment removed for export] *)
      pose proof (es_rd_da mc (e_es E) _ tn (wa (e_es E + 256 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
      setreg 14 (Z_to_bv 64 (optr (badr OW) (get_data tn st1))) ltac:(cbn [g_da g_of]; rewrite nth_wl_optr; reflexivity).
      destruct (get_data tn st1) as [[pd nd]|] eqn:GD; cbn [optr].
      + (* [comment removed for export] *)
        assert (GD0 : get_data tn st = Some (pd, nd)) by exact GD.
        destruct (optb_ok_nth OW _ tn pd nd OD GD0) as [HINd HPd].
        pose proof (blk_bounds _ _ _ _ _ _ HEAPb (INCL _ HINd)) as (BD1 & BD2 & BD3 & BD4 & BD5).
        pose proof (blk_disjoint _ _ _ pd (badr OW pd) nd (p_es E) (e_es E) 904 HEAPb (INCL _ HINd) (INCL _ IES)
                      ltac:(eapply ids_data_es_ne; [exact IDS|exact GD0])) as DJd.
        step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
        (* [comment removed for export] *)
        assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
        { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
        destruct (seg_close s OW LB _ mb mc lo (bv_unsigned sp) B HEAPb AUXb CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU2 WM2) as (HEAPc & AUXc & LXc).
        { constructor; [left; cbn; lia|]. constructor; [right; right; exists (p_es E), (e_es E), 904; split; [exact IES|cbn; lia]|constructor]. }
        assert (ARc : ap_rest mc OW E bo0 (as_cnf st)).
        { eapply (rest_of_seg' s (OW ++ LB) _ mb mc); [exact ARb|exact HEAPb|intros b Hb; apply INCL; eapply rest_blocks_OW; [exact ARb|exact Hb]|exact CEIL|unfold GLOBALS_TOP; lia|exact MU2|exact WM2|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
          split; [destruct AS0 as [m0 AS0']; eapply es_not_rest; [exact AS0'|exact IDS]|cbn; lia]. }
        assert (DCc : data_cells mc OW st).
        { eapply (data_cells_of_munch s (OW ++ LB) _ mb mc); [exact DCb|exact DIN|exact HEAPb|exact CEIL|exact MU2|exact WM2|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
          split; [intros i q k Hd; eapply ids_data_es_ne; [exact IDS|exact Hd]|cbn; lia]. }
        assert (LXc' : lx_pres LB (bv_unsigned sp) LIBW_AP m mc) by (eapply lx_pres_trans; [exact LXb|exact LXc]).
        assert (KPc : kept K m mc).
        { eapply kept_trans; [exact KPb|]. eapply (kept_of_munch s (OW ++ LB) _ mb mc K lo); [exact HEAPb|exact KOWL|exact CEIL|exact MU2|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
          split; [eapply K_not_env; [exact KIDS|]; rewrite env_ids_unfold; cbn; tauto|cbn; lia]. }
        destruct (proj1 DCc tn pd nd GD0) as [ND1 [junkd HD]].
        assert (EK : exists k, Z.to_nat nd = S k) by (exists (Z.to_nat nd - 1)%nat; lia). destruct EK as [kd EK]. rewrite EK in HD.
        apply (rw_cells_split_CB ctusegs mc (badr OW pd) [] (S kd) junkd [] [1%nat; kd]) in HD; [|cbn; lia].
        cbn [mk_CB_cells app] in HD.
        clear MU2 WM2.
        pose proof (munch_refl [(bv_unsigned sp - 48 - 16 - 8192, bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z mc) as MU3. pose proof (wmono_refl ctusegs mc) as WM3.
        step. name_mem m3. step.
        (* [comment removed for export] *)
        destruct (seg_close s OW LB _ mc m3 lo (bv_unsigned sp) B HEAPc AUXc CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU3 WM3) as (HEAP3 & AUX3 & LX3).
        { constructor; [left; cbn; lia|]. constructor; [right; right; exists pd, (badr OW pd), nd; split; [exact HINd|cbn; lia]|constructor]. }
        assert (AR3 : ap_rest m3 OW E bo0 (as_cnf st)).
        { eapply (rest_of_seg' s (OW ++ LB) _ mc m3); [exact ARc|exact HEAPc|intros b Hb; apply INCL; eapply rest_blocks_OW; [exact ARc|exact Hb]|exact CEIL|unfold GLOBALS_TOP; lia|exact MU3|exact WM3|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists pd, (badr OW pd), nd. split; [apply INCL; exact HINd|].
          split; [eapply data_not_rest; [exact IDS|exact GD0]|cbn; lia]. }
        lazymatch type of HD with rw_cells _ _ _ ?cs =>
          pose proof (rw_cells_merge ctusegs m3 (badr OW pd) (@nil cell) cs (@nil cell) ltac:(rewrite app_nil_r; exact HD)) as HD' end.
        cbn [app cells_size csize cells_bytes cbytes length] in HD'.
        match type of HD' with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat nd) in HD' by lia end.
        assert (DC3 : data_cells m3 OW st).
        { eapply (data_cells_store1 s (OW ++ LB) mc m3); [exact DCc|exact DIN|apply INCL; exact HINd|exact ND1|exact HEAPc|exact CEIL| |exact MU3|exact WM3|exact HD']. lia. }
        eapply es_raw_transport in ES; [|exact GL|exact MU3|exact WM3|cbn; lia].
        assert (LX3' : lx_pres LB (bv_unsigned sp) LIBW_AP m m3) by (eapply lx_pres_trans; [exact LXc'|exact LX3]).
        assert (KP3 : kept K m m3).
        { eapply kept_trans; [exact KPc|]. eapply (kept_of_munch s (OW ++ LB) _ mc m3 K lo); [exact HEAPc|exact KOWL|exact CEIL|exact MU3|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists pd, (badr OW pd), nd. split; [apply INCL; exact HINd|].
          split; [eapply K_not_es; [exact KIDS|]; eapply es_ids_data; exact GD0|cbn; lia]. }
        clear MU3 WM3 HD HD' HEAPc AUXc LXc LXc' ARc DCc KPc.
        (* [comment removed for export] *)
        pose proof (munch_refl [(bv_unsigned sp - 48 - 16 - 8192, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m3) as MU4. pose proof (wmono_refl ctusegs m3) as WM4.
        es_store (es_wr_df m3 (e_es E) _ tn (Z_to_bv 64 1) ES GL TNB'). name_mem m4.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
          lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
        lazymatch type of ES with es_raw _ _ ?g =>
          replace g with (g_of (ecd tn st1) (badr OW)) in ES
            by (unfold ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [negb];
                rewrite GD, g_of_set_dflags; unfold ERR_TXT_MALLOCED, MallocRep.wz; reflexivity)
        end.
        eapply (ERR_new_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 _ j0 errv2);
          [exact HEAP3|exact AUX3|exact LX3'|exact AR3|exact DC3|exact KP3|exact MU4|exact WM4|exact FR|exact ERR2|exact ST|exact MI|exact ES].
      + (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; [|exfalso; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
          lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
        replace (g_of st1 (badr OW)) with (g_of (ecd tn st1) (badr OW)) in ES
          by (unfold ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [negb]; rewrite GD; reflexivity).
        eapply (ERR_new_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ mb _ j0 errv2);
          [exact HEAPb|exact AUXb|exact LXb|exact ARb|exact DCb|exact KPb|exact MU2|exact WM2|exact FR|exact ERR2|exact ST|exact MI|exact ES].
    - (* [comment removed for export] *)
      step. step.
      es_store (es_wr_da mc (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m3.
      step. step. setreg 14 (Z_to_bv 64 (e_es E + 384 + 8 * Z.of_nat tn)) ltac:(f_equal; lia).
      es_store (es_wr_ds m3 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m4.
      step. if_cases KZ; zify_cond KZ; [| exfalso; rewrite ?unsigned_lit in KZ by lia; lia]. clear KZ.
      es_store (es_wr_df m4 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m5.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd tn st1) (badr OW)) in ES
          by (unfold ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with true by (symmetry; apply Z.eqb_eq; lia); cbn [negb];
              rewrite g_of_set_dflags, g_of_set_data; cbn [optr osize]; unfold MallocRep.wz; reflexivity)
      end.
      eapply (ERR_new_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ mb _ j0 errv2);
        [exact HEAPb|exact AUXb|exact LXb|exact ARb|exact DCb|exact KPb|exact MU2|exact WM2|exact FR|exact ERR2|exact ST|exact MI|exact ES].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_new_act : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
    RHEAP s (OW ++ LB) m -> ap_state st m OW E bo0 -> data_cells m OW st -> rauxv_ok m B ->
    stk ctusegs m lo (bv_unsigned sp) -> rw_cells ctusegs m 3355012 [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    implM ctusegs (interp (ap_embed (err_new st))) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_NEW) fc None m (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EES16 EESC EESI EESP FRM GLO HF IDS IES KIDS KOW LO OD OF OFN SH SP16 SPB.
    intros until errv. intros HEAP AS DC AUX ST ERR MI ->.
    unfold ERR_NEW, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (3355012, 3355012 + 4)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    rewrite (err_new_tree st).
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 9 step.
    name_mem m1.
    assert (AS1 : ap_state st m1 OW E bo0).
    { eapply (ap_state_of_munch st m m1); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    assert (HEAP1 : RHEAP s (OW ++ LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_errno|constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (get_state_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo s (OW ++ LB) OW E st bo0 errv 1);
        [exact AS1|exact HEAP1|exact INCL|rewrite ESP; exact ST|exact CEIL|unfold GLOBALS_TOP; lia|rewrite ESP; lia|rewrite ESP; clear - SP16 SPR GLO LO;
         replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SP16; reflexivity
        |exact ERR|exact MI|reflexivity|right; reflexivity|reflexivity]. }
    post_call_esp ESP m1.
    match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
    match goal with H : rw_cells ctusegs _ 3355012 _ |- _ => rename H into ERR2 end.
    match goal with H : mem_inv ctusegs _ |- _ => rename H into MI2 end.
    name_mem m2. clear AS1 HEAP1.
    assert (AS2 : ap_state st m2 OW E bo0).
    { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    destruct (seg_close s OW LB _ m m2 lo (bv_unsigned sp) B HEAP AUX CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP2 & AUX2 & LX2).
    { constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|constructor]. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC2 : data_cells m2 OW st).
    { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|exact DIN|exact HEAP|exact CEIL|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. left. reflexivity. }
    assert (KP2 : kept K m m2).
    { eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. left. reflexivity. }
    pose proof (proj1 (ap_state_split _ _ _ _ _) AS2) as [AR2 _].
    clear MU WM AS HEAP AUX DC m1.
    pose proof (ap_state_es _ _ _ _ _ AS2) as (ES & GL & _).
    pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    (* [comment removed for export] *)
    pose proof (es_rd_top m2 (e_es E) _ _ ES eq_refl) as RD1. pose proof (es_rd_bot m2 (e_es E) _ _ ES eq_refl) as RD2.
    unfold MallocRep.wz in RD1, RD2 |- *.
    do 13 (first [ ub1 | zstep ]; try udecide; try (cbn [g_top g_bot g_of]; rewrite ?sx32_small by lia)).
    clear RD1 RD2.
    (* [comment removed for export] *)
    pose proof TNB as TNB'.
    setreg 18 (Z_to_bv 64 (Z.of_nat tn)) ltac:(unfold tn, enew_top, ring_next, ERR_NUM; set (t := as_top st) in *; by_cases16 t TOPB).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 48 - 16 - 8192, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU2. pose proof (wmono_refl ctusegs m2) as WM2.
    es_store (es_wr_top m2 (e_es E) _ (Z.of_nat tn) ES GL). name_mem m3.
    set (bot := as_bottom st) in *.
    step. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      assert (NEB : Nat.eqb tn bot = false) by (apply Nat.eqb_neq; intros EQ; apply KK; rewrite EQ; reflexivity).
      replace (set_g_top (Z.of_nat tn) (g_of st (badr OW))) with (g_of st1 (badr OW)) in ES
        by (unfold st1, enew_st1, enew_bot; fold tn bot; rewrite NEB; reflexivity).
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply (ERR_new_tail1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 _ _ _);
        [exact HEAP2|exact AUX2|exact LX2|exact AR2|exact DC2|exact KP2|exact MU2|exact WM2|exact FR|exact ERR2|exact ST|exact MI2|exact ES].
    - (* [comment removed for export] *)
      assert (TB : tn = bot) by (apply Nat2Z.inj; exact KK).
      do 9 step.
      setreg 10 (Z_to_bv 64 (Z.of_nat (ring_next bot)))
        ltac:(rewrite TB; unfold ring_next, ERR_NUM; subst bot; set (b := as_bottom st) in *; by_cases16 b BOTB).
      es_store (es_wr_bot m3 (e_es E) _ (Z.of_nat (ring_next bot)) ES GL). name_mem m4.
      assert (EQB : Nat.eqb tn bot = true) by (apply Nat.eqb_eq; exact TB).
      replace (set_g_bot (Z.of_nat (ring_next bot)) (set_g_top (Z.of_nat tn) (g_of st (badr OW)))) with (g_of st1 (badr OW)) in ES
        by (unfold st1, enew_st1, enew_bot; fold tn bot; rewrite EQB; reflexivity).
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply (ERR_new_tail1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 _ _ _);
        [exact HEAP2|exact AUX2|exact LX2|exact AR2|exact DC2|exact KP2|exact MU2|exact WM2|exact FR|exact ERR2|exact ST|exact MI2|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_new_walk : ERR_new_spec.
  Proof using HF.
    intros bo0. unfold ap_stmt. intros until K. intros PRE TP FRM EBO KOW KIDS. subst bo.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    unfold ERR_NEW_STACK, GLOBALS_TOP in *.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof ERR as ERR'. unfold MallocRep.wz in ERR'. rewrite EA in ERR'.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP (INCL _ IES)) as (_ & _ & EESC & EESI & _).
    pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as CAN.
    eapply (ERR_new_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s st OW LB E bo0 lo B canary
              IDS SPB B63 CEIL GLO LO SP16);
      first [exact FRM|exact SH|exact IES|exact EESP|exact EESC|exact EESI|exact EES16|exact OF|exact OFN|exact OD|exact (ex_intro _ m AS)|exact CAN
            |unfold errno_addr in EA; exact EA|exact KOW|exact KIDS|exact HEAP|exact AS|exact DC|exact AUX|exact ST|exact ERR'|exact MI|exact TP].
  Qed.
End Proofs.
End WithCeiling0.
