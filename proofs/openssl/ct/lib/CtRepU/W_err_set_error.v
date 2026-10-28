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

Definition ERR_set_error_spec (rs : rsite) (lib reason : Z) : Prop := forall bo0 : Z * Z,
  ap_stmt ERR_SET_ERROR ERR_SET_ERROR_STACK
          (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz lib /\ a1 = wz reason /\ a2 = wz 0 /\ rs_code rs = ERR_PACK lib reason
                                                /\ 0 <= lib < 256 /\ lib <> ERR_LIB_SYS /\ 0 <= reason < 8388608 /\ bo = bo0)
          (err_set_error rs)
          (fun r OW' m' a0' bo' => bo' = bo0).

Section Proofs.
  (* [comment removed for export] *)
  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo B : Z) (canary : word).
  Variables (rs : rsite) (lib reason : Z).
  Hypothesis IDS : ids_ok E st.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - (80 + 96 + 48 + 8192).
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis FRM : frm0 fc.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESC : e_es E + 904 <= alloc_ceiling.
  Hypothesis EESI : e_es E + 904 <= 65536 \/ 3493888 <= e_es E.
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists m0, ap_state st m0 OW E bo0.
  Hypothesis CAN : canary = rr_guard.
  Hypothesis EA : errno_addr (Z_to_bv 64 RATP) = 3355012.
  Hypothesis RSC : rs_code rs = ERR_PACK lib reason.
  Hypothesis LIBR : 0 <= lib < 256.
  Hypothesis LIBNS : lib <> ERR_LIB_SYS.
  Hypothesis REAR : 0 <= reason < 8388608.
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

  Let tn : nat := as_top st.
  Local Notation W2 := ([(bv_unsigned sp - 176 - 1024, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Let POST := ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0).
  (* [comment removed for export] *)
  Definition se_frame (j0 j32 : list byte) (a3 a4 a5 a6 a7 : word) : list cell :=
    [CB 8 j0; C8 (Z_to_bv 64 (bv_unsigned sp + -40)); C8 s0; C8 ra; CB 8 j32; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].
  (* [comment removed for export] *)
  Definition vse_frame : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 0xe8154)].

  Lemma TNB : (tn < 16)%nat.
  Proof using IDS. pose proof (ids_ok_top _ _ IDS) as [T _]. exact T. Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_error_finish : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mb m9 : mem) (errv' : word) (sC : PState),
    RHEAP sC (OW ++ LB) mb -> rauxv_ok mb B -> lx_pres LB (bv_unsigned sp) LIBW_AP m mb -> ap_rest mb OW E bo0 (as_cnf st) -> data_cells mb OW st ->
    kept K m mb ->
    munch W2 mb m9 -> wmono ctusegs mb m9 ->
    es_raw m9 (e_es E) (g_of (eserr_fin rs st) (badr OW)) -> stk ctusegs m9 lo (bv_unsigned sp) -> mem_inv ctusegs m9 ->
    rw_cells ctusegs m9 3355012 [C4 errv'] -> ps_so sC = ps_so s -> ps_fa sC = ps_fa s ->
    POST (tt, eserr_fin rs st) sC
         (MS (mkR ra sp gp (wz RATP) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m9 (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EESI FRM GLO IDS IES KIDS KOW LIBR LO OD OF OFN REAR SH SP16 SPB.
    intros until sC. intros HEAPb AUXb LXb ARb DCb KPb MU WM ES ST MI ERR SO FA.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [_ BNB'].
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    destruct (seg_close sC OW LB _ mb m9 lo (bv_unsigned sp) B HEAPb AUXb CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP9 & AUX9 & LX9).
    { constructor; [left; cbn; lia|]. constructor; [right; right; exists (p_es E), (e_es E), 904; split; [exact IES|cbn; lia]|constructor]. }
    assert (AR9 : ap_rest m9 OW E bo0 (as_cnf st)).
    { eapply (rest_of_seg' sC (OW ++ LB) _ mb m9); [exact ARb|exact HEAPb|intros b Hb; apply INCL; eapply rest_blocks_OW; [exact ARb|exact Hb]|exact CEIL|unfold GLOBALS_TOP; lia|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
      split; [destruct AS0 as [m0 AS0']; eapply es_not_rest; [exact AS0'|exact IDS]|cbn; lia]. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC9 : data_cells m9 OW st).
    { eapply (data_cells_of_munch sC (OW ++ LB) _ mb m9); [exact DCb|exact DIN|exact HEAPb|exact CEIL|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
      split; [intros i q k Hd; eapply ids_data_es_ne; [exact IDS|exact Hd]|cbn; lia]. }
    (* [comment removed for export] *)
    assert (PERM : exists pre, Permutation (pre ++ st_blocks (eserr_fin rs st)) (st_blocks st) /\ (pre = [] \/ pre = optb (get_data tn st))).
    { unfold eserr_fin. rewrite st_blocks_set_buf. pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
      destruct (st_blocks_ecd tn st ltac:(rewrite L3; exact TNB')) as [P|P]; [exists []; split; [exact P|left; reflexivity]|exists (optb (get_data tn st)); split; [exact P|right; reflexivity]]. }
    destruct PERM as (pre & PERM & Hpre).
    pose proof (ecd_proj tn st) as (PT & PB & PF & PN & PM & PU & PL & PC).
    assert (IDS' : ids_ok E (eserr_fin rs st)).
    { eapply ids_ok_sub; [exact PERM| | |apply marks_sub_eserr_fin|exact IDS]; unfold eserr_fin; cbn [as_top as_bottom set_buf]; [rewrite PT; exact TNB'|rewrite PB; exact BNB']. }
    assert (DSUB : forall i q k, get_data i (eserr_fin rs st) = Some (q, k) -> get_data i st = Some (q, k)).
    { intros i q k Hd. apply (get_data_ecd tn st). unfold get_data, eserr_fin in Hd |- *. cbn [as_data set_buf] in Hd. exact Hd. }
    assert (AS9 : ap_state (eserr_fin rs st) m9 OW E bo0).
    { apply ap_state_join.
      - replace (as_cnf (eserr_fin rs st)) with (as_cnf st) by (unfold eserr_fin; cbn [as_cnf set_buf]; rewrite PC; reflexivity). exact AR9.
      - unfold eserr_fin. apply es_shape_setters. unfold ecd. destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; exact SH.
      - exact ES.
      - unfold eserr_fin. cbn [as_file set_buf]. rewrite PF. exact OF.
      - unfold eserr_fin. cbn [as_func set_buf]. rewrite PN. exact OFN.
      - unfold eserr_fin. cbn [as_data set_buf]. unfold ecd. destruct (negb _); [destruct (get_data _ _)|]; cbn [as_data set_dflags set_data]; try apply optb_ok_lset_none; exact OD. }
    assert (DC9' : data_cells m9 OW (eserr_fin rs st)).
    { apply (data_cells_sub m9 OW st); [exact DC9|intros i q k Hd; exists i; apply DSUB; exact Hd|].
      unfold eserr_fin. eapply dflags_ok_same; [reflexivity|reflexivity|]. pose proof SH as (_ & _ & L3 & L4 & _).
      apply dflags_ok_ecd; [rewrite L3; exact TNB'|rewrite L3, L4; reflexivity|eapply data_cells_dflags; exact DCb]. }
    assert (KP9 : kept K mb m9).
    { eapply (kept_of_munch sC (OW ++ LB) _ mb m9 K lo); [exact HEAPb|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
      split; [eapply K_not_env; [exact KIDS|]; rewrite env_ids_unfold; cbn; tauto|cbn; lia]. }
    unfold POST, ap_post.
    exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m9, OW, errv', bo0.
    split; [reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
    split; [|split; [eapply lx_pres_trans; [exact LXb|exact LX9]|split; [exact SO|split; [exact FA|split; [|reflexivity]]]]].
    2:{ split; [exact KOW|]. split; [|eapply kept_trans; [exact KPb|exact KP9]].
        intros b Hb Hin. apply (KIDS b Hb). apply in_app_iff. left. eapply es_ids_sub_perm; [exact PERM|exact Hin]. }
    unfold ap_pre. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS'|]. split; [exact DC9'|]. split; [exact AUX9|]. split; [exact SPB|]. split; [exact B63|].
    split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; exact GLO|]. split; [lia|].
    split. { unfold MallocRep.wz. rewrite EA. exact ERR. } split. { rewrite CAN. eapply RHEAP_ssp. exact HEAP9. } split. { exact MI. } exact SP16.
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_error_tail2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j0 j32 : list byte) (va3 va4 va5 va6 va7 : word)
      (mb mc : mem) (errv2 : word),
    RHEAP s (OW ++ LB) mb -> rauxv_ok mb B -> lx_pres LB (bv_unsigned sp) LIBW_AP m mb -> ap_rest mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    munch W2 mb mc -> wmono ctusegs mb mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -80) (se_frame j0 j32 va3 va4 va5 va6 va7) ->
    rw_cells ctusegs mc (bv_unsigned sp + -176) vse_frame ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -176) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of (ecd tn st) (badr OW)) ->
    implM ctusegs (interp (ap_embed (ARet (tt, eserr_fin rs st)))) s POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -80)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat tn))
              x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z_to_bv 64 (e_es E)) (Z_to_bv 64 0) (Z_to_bv 64 reason) (Z_to_bv 64 lib) (Z_to_bv 64 0)
              (Z_to_bv 64 (e_es E + 384)) (Z_to_bv 64 (e_es E + 512)) (Z_to_bv 64 (e_es E + 256)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8368) fc None mc (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EESC EESI EESP FRM GLO IDS IES KIDS KOW LIBNS LIBR LO OD OF OFN REAR RSC SH SP16 SPB.
    intros until errv2. intros HEAPb AUXb LXb ARb DCb KPb MU2 WM2 FR1 FR2 ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (SH1 : es_shape (ecd tn st)) by (unfold ecd; destruct (negb _); [destruct (get_data _ _)|]; repeat apply es_shape_setters; exact SH).
    assert (GL : g_len (g_of (ecd tn st) (badr OW))) by (apply g_len_of; exact SH1).
    unfold se_frame in FR1. unfold vse_frame in FR2. unfold ERR_LIB_SYS in LIBNS.
    pose proof alloc_ceiling_range as CEIL_RANGE.
    unfold implM. iprefix.
    step. step. if_cases KK; zify_cond KK; [|exfalso; rewrite ?unsigned_lit in KK by lia; lia]. clear KK.
    do 5 step.
    setreg 11 (Z_to_bv 64 (ERR_PACK lib reason)) ltac:(rewrite <- (err_pack_bits lib reason LIBR REAR); reflexivity).
    pose proof (err_pack_range lib reason LIBR REAR) as PKR.
    ub. step. step. ub. step. step. step.
    rewrite (zext32_shifts (ERR_PACK lib reason)) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    setreg 12 (Z_to_bv 64 (e_es E + 128 + 8 * Z.of_nat tn)) ltac:(f_equal; lia).
    (* [comment removed for export] *)
    es_store (es_wr_bu mc (e_es E) _ tn (Z_to_bv 64 (ERR_PACK lib reason)) ES GL TNB'). name_mem m3.
    (* [comment removed for export] *)
    step. if_cases KK; zify_cond KK; [|exfalso; rewrite ?unsigned_lit in KK by lia; lia]. clear KK.
    do 12 step. step. step.
    replace (ret_pc (Z_to_bv 64 0xe8154)) with (Z_to_bv 64 0xe8154) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    release_frame FR2 ST (bv_unsigned sp + -80).
    step. step. step. release_frame FR1 ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    lazymatch type of ES with es_raw _ _ ?g =>
      replace g with (g_of (eserr_fin rs st) (badr OW)) in ES
        by (unfold eserr_fin; fold tn; rewrite g_of_set_buf, RSC; unfold MallocRep.wz; reflexivity)
    end.
    apply evt_done. cbn [ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
    eapply (ERR_set_error_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mb m3 errv2);
      [exact HEAPb|exact AUXb|exact LXb|exact ARb|exact DCb|exact KPb|exact MU2|exact WM2|exact ES|exact ST|exact MI|exact ERR2|reflexivity|reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_error_tail : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j0 j32 : list byte) (va3 va4 va5 va6 va7 : word)
      (mb mc : mem) (errv2 : word),
    RHEAP s (OW ++ LB) mb -> rauxv_ok mb B -> lx_pres LB (bv_unsigned sp) LIBW_AP m mb -> ap_rest mb OW E bo0 (as_cnf st) -> data_cells mb OW st -> kept K m mb ->
    munch W2 mb mc -> wmono ctusegs mb mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -80) (se_frame j0 j32 va3 va4 va5 va6 va7) ->
    rw_cells ctusegs mc (bv_unsigned sp + -176) vse_frame ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -176) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of st (badr OW)) ->
    implM ctusegs (interp (ap_embed (ARet (tt, eserr_fin rs st)))) s POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -176)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -80)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat tn))
              x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z_to_bv 64 (e_es E)) (Z_to_bv 64 0) (Z_to_bv 64 reason) (Z_to_bv 64 lib) (Z_to_bv 64 0)
              (Z_to_bv 64 (e_es E + 384)) (Z_to_bv 64 (e_es E + 512)) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe82f0) fc None mc (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EESC EESI EESP FRM GLO IDS IES KIDS KOW LIBNS LIBR LO OD OF OFN REAR RSC SH SP16 SPB.
    intros until errv2. intros HEAPb AUXb LXb ARb DCb KPb MU2 WM2 FR1 FR2 ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    assert (GL : g_len (g_of st (badr OW))) by (apply g_len_of; exact SH).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    unfold se_frame in FR1. unfold vse_frame in FR2.
    pose proof alloc_ceiling_range as CEIL_RANGE.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. ub1. step. step. ub1.
    rewrite ?Z.shiftl_mul_pow2 by lia.
    setreg 11 (Z_to_bv 64 (e_es E + 512 + 4 * Z.of_nat tn)) ltac:(f_equal; lia).
    pose proof (es_rd_df1 mc (e_es E) _ tn (wa (e_es E + 512 + 4 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
    step. step. step. step. rewrite ?(unsigned_lit (Z.of_nat tn)) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    setreg 12 (Z_to_bv 64 (e_es E + 256 + 8 * Z.of_nat tn)) ltac:(f_equal; lia).
    set (f := get_dflags tn st).
    setreg 14 (Z_to_bv 64 (Z.land f ERR_TXT_MALLOCED))
      ltac:(cbn [g_df g_of]; rewrite nth_wl; unfold zx8, MallocRep.wz; rewrite (unsigned_lit (_ mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned (Z_to_bv 64 (nth tn (as_dflags st) 0))) (2 ^ 8) ltac:(lia)); lia);
            rewrite dflag_bit; reflexivity).
    assert (FR01 : 0 <= Z.land f ERR_TXT_MALLOCED <= 1) by apply land_malloced_range.
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    step. if_cases KF; zify_cond KF; rewrite land_malloced_mask in KF.
    - (* [comment removed for export] *)
      ub1.
      pose proof (es_rd_da mc (e_es E) _ tn (wa (e_es E + 256 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
      setreg 13 (Z_to_bv 64 (optr (badr OW) (get_data tn st))) ltac:(cbn [g_da g_of]; rewrite nth_wl_optr; reflexivity).
      destruct (get_data tn st) as [[pd nd]|] eqn:GD; cbn [optr].
      + (* [comment removed for export] *)
        destruct (optb_ok_nth OW _ tn pd nd OD GD) as [HINd HPd].
        pose proof (blk_bounds _ _ _ _ _ _ HEAPb (INCL _ HINd)) as (BD1 & BD2 & BD3 & BD4 & BD5).
        pose proof (blk_disjoint _ _ _ pd (badr OW pd) nd (p_es E) (e_es E) 904 HEAPb (INCL _ HINd) (INCL _ IES)
                      ltac:(eapply ids_data_es_ne; [exact IDS|exact GD])) as DJd.
        step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
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
        { eapply kept_trans; [exact KPb|]. eapply (kept_of_munch s (OW ++ LB) _ mb mc K lo); [exact HEAPb|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU2|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists (p_es E), (e_es E), 904. split; [apply INCL; exact IES|].
          split; [eapply K_not_env; [exact KIDS|]; rewrite env_ids_unfold; cbn; tauto|cbn; lia]. }
        destruct (proj1 DCc tn pd nd GD) as [ND1 [junkd HD]].
        assert (EK : exists k, Z.to_nat nd = S k) by (exists (Z.to_nat nd - 1)%nat; lia). destruct EK as [kd EK]. rewrite EK in HD.
        apply (rw_cells_split_CB ctusegs mc (badr OW pd) [] (S kd) junkd [] [1%nat; kd]) in HD; [|cbn; lia].
        cbn [mk_CB_cells app] in HD.
        clear MU2 WM2.
        pose proof (munch_refl [(bv_unsigned sp - 176 - 1024, bv_unsigned sp); (badr OW pd, badr OW pd + 1)]%Z mc) as MU3. pose proof (wmono_refl ctusegs mc) as WM3.
        ub1. step. ub1. step. name_mem m3.
        destruct (seg_close s OW LB _ mc m3 lo (bv_unsigned sp) B HEAPc AUXc CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU3 WM3) as (HEAP3 & AUX3 & LX3).
        { constructor; [left; cbn; lia|]. constructor; [right; right; exists pd, (badr OW pd), nd; split; [exact HINd|cbn; lia]|constructor]. }
        assert (AR3 : ap_rest m3 OW E bo0 (as_cnf st)).
        { eapply (rest_of_seg' s (OW ++ LB) _ mc m3); [exact ARc|exact HEAPc|intros b Hb; apply INCL; eapply rest_blocks_OW; [exact ARc|exact Hb]|exact CEIL|unfold GLOBALS_TOP; lia|exact MU3|exact WM3|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists pd, (badr OW pd), nd. split; [apply INCL; exact HINd|].
          split; [eapply data_not_rest; [exact IDS|exact GD]|cbn; lia]. }
        lazymatch type of HD with rw_cells _ _ _ ?cs =>
          pose proof (rw_cells_merge ctusegs m3 (badr OW pd) (@nil cell) cs (@nil cell) ltac:(rewrite app_nil_r; exact HD)) as HD' end.
        cbn [app cells_size csize cells_bytes cbytes length] in HD'.
        match type of HD' with rw_cells _ _ _ [CB ?k ?bs] => replace k with (Z.to_nat nd) in HD' by lia end.
        assert (DC3 : data_cells m3 OW st).
        { eapply (data_cells_store1 s (OW ++ LB) mc m3); [exact DCc|exact DIN|apply INCL; exact HINd|exact ND1|exact HEAPc|exact CEIL| |exact MU3|exact WM3|exact HD']. lia. }
        eapply es_raw_transport in ES; [|exact GL|exact MU3|exact WM3|cbn; lia].
        assert (LX3' : lx_pres LB (bv_unsigned sp) LIBW_AP m m3) by (eapply lx_pres_trans; [exact LXc'|exact LX3]).
        assert (KP3 : kept K m m3).
        { eapply kept_trans; [exact KPc|]. eapply (kept_of_munch s (OW ++ LB) _ mc m3 K lo); [exact HEAPc|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU3|].
          constructor; [left; cbn; lia|]. constructor; [|constructor]. right. right. exists pd, (badr OW pd), nd. split; [apply INCL; exact HINd|].
          split; [eapply K_not_es; [exact KIDS|]; eapply es_ids_data; exact GD|cbn; lia]. }
        clear MU3 WM3 HD HD' HEAPc AUXc LXc LXc' ARc DCc KPc.
        pose proof (munch_refl [(bv_unsigned sp - 176 - 1024, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m3) as MU4. pose proof (wmono_refl ctusegs m3) as WM4.
        es_store (es_wr_df m3 (e_es E) _ tn (Z_to_bv 64 1) ES GL TNB'). name_mem m4.
        (* [comment removed for export] *)
        pose proof (es_rd_top m4 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. step. clear RD.
        cbn [g_top g_of set_g_df]. rewrite !sx32_small by lia. fold tn.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
          lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
        lazymatch type of ES with es_raw _ _ ?g =>
          replace g with (g_of (ecd tn st) (badr OW)) in ES
            by (unfold ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [negb];
                rewrite GD, g_of_set_dflags; unfold ERR_TXT_MALLOCED, MallocRep.wz; reflexivity)
        end.
        eapply (ERR_set_error_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 _ errv2);
          [exact HEAP3|exact AUX3|exact LX3'|exact AR3|exact DC3|exact KP3|exact MU4|exact WM4|exact FR1|exact FR2|exact ERR2|exact ST|exact MI|exact ES].
      + (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; [|exfalso; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
          lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
        replace (g_of st (badr OW)) with (g_of (ecd tn st) (badr OW)) in ES
          by (unfold ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [negb]; rewrite GD; reflexivity).
        eapply (ERR_set_error_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mb _ errv2);
          [exact HEAPb|exact AUXb|exact LXb|exact ARb|exact DCb|exact KPb|exact MU2|exact WM2|exact FR1|exact FR2|exact ERR2|exact ST|exact MI|exact ES].
    - (* [comment removed for export] *)
      ub1. ub1. step. es_store (es_wr_da mc (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m3.
      ub1. step. step. es_store (es_wr_ds m3 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m4.
      step. if_cases KZ; zify_cond KZ; [| exfalso; rewrite ?unsigned_lit in KZ by lia; lia]. clear KZ.
      es_store (es_wr_df m4 (e_es E) _ tn (Z_to_bv 64 0) ES GL TNB'). name_mem m5.
      pose proof (es_rd_top m5 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. step. clear RD.
      cbn [g_top g_of set_g_df set_g_ds set_g_da]. rewrite !sx32_small by lia. fold tn.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      lazymatch type of ES with es_raw _ _ ?g =>
        replace g with (g_of (ecd tn st) (badr OW)) in ES
          by (unfold ecd; fold f; replace (Z.land f ERR_TXT_MALLOCED =? 0) with true by (symmetry; apply Z.eqb_eq; lia); cbn [negb];
              rewrite g_of_set_dflags, g_of_set_data; cbn [optr osize]; unfold MallocRep.wz; reflexivity)
      end.
      eapply (ERR_set_error_tail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mb _ errv2);
        [exact HEAPb|exact AUXb|exact LXb|exact ARb|exact DCb|exact KPb|exact MU2|exact WM2|exact FR1|exact FR2|exact ERR2|exact ST|exact MI|exact ES].
  Qed.
  (* [comment removed for export] *)
  Lemma ERR_set_error_act : forall (tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
    RHEAP s (OW ++ LB) m -> ap_state st m OW E bo0 -> data_cells m OW st -> rauxv_ok m B ->
    stk ctusegs m lo (bv_unsigned sp) -> rw_cells ctusegs m 3355012 [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    implM ctusegs (interp (ap_embed (err_set_error rs st))) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz lib) (wz reason) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_SET_ERROR) fc None m (seg_rom ctusegs)).
  Proof using AS0 B63 CAN CEIL EA EESC EESI EESP FRM GLO IDS IES KIDS KOW LIBNS LIBR LO OD OF OFN REAR RSC SH SP16 SPB.
    intros until errv. intros HEAP AS DC AUX ST ERR MI ->.
    unfold ERR_SET_ERROR, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 176 - 1024, bv_unsigned sp); (3355012, 3355012 + 4)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    rewrite (err_set_error_tree rs st).
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 12 step.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. do 12 step. do 7 step. step.
    name_mem m1.
    assert (AS1 : ap_state st m1 OW E bo0).
    { eapply (ap_state_of_munch st m m1); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    assert (HEAP1 : RHEAP s (OW ++ LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_errno|constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (get_state_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo s (OW ++ LB) OW E st bo0 errv 1);
        [exact AS1|exact HEAP1|exact INCL|rewrite ESP; exact ST|exact CEIL|unfold GLOBALS_TOP; lia|rewrite ESP; lia|rewrite ESP; clear - SP16 SPR GLO LO;
         replace (bv_unsigned sp + -176) with (bv_unsigned sp - 176) by lia; rewrite Zminus_mod, SP16; reflexivity
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
    pose proof (ap_state_es _ _ _ _ _ AS2) as (ES & GL & _ & _ & _ & _ & EES16 & _).
    assert (A8 : e_es E mod 8 = 0) by (clear - EES16; Z.div_mod_to_equations; lia).
    pose proof alloc_ceiling_range as CEIL_RANGE.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    unfold MallocRep.wz in *. step. ub1. ub1.
    pose proof (es_rd_top m2 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. step. clear RD.
    cbn [g_top g_of]. rewrite !sx32_small by lia. fold tn.
    step. step. step. if_true.
    do 4 step.
    pose proof (munch_refl [(bv_unsigned sp - 176 - 1024, bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU2. pose proof (wmono_refl ctusegs m2) as WM2.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    eapply (ERR_set_error_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 _ _);
      [exact HEAP2|exact AUX2|exact LX2|exact AR2|exact DC2|exact KP2|exact MU2|exact WM2|unfold se_frame; exact FR|unfold vse_frame; exact FR0|exact ERR2|exact ST|exact MI2|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_set_error_walk : forall rs lib reason, ERR_set_error_spec rs lib reason.
  Proof.
    intros rs lib reason bo0. unfold ap_stmt. intros until K. intros PRE TP FRM (A0 & A1 & A2 & RSC & LIBR & LIBNS & REAR & EBO) KOW KIDS. subst bo a0 a1 a2.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    unfold ERR_SET_ERROR_STACK, GLOBALS_TOP in *.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof ERR as ERR'. unfold MallocRep.wz in ERR'. rewrite EA in ERR'.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP (INCL _ IES)) as (_ & _ & EESC & EESI & _).
    pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as CAN.
    eapply (ERR_set_error_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s st OW LB E bo0 lo B canary rs lib reason
              IDS SPB B63 CEIL GLO LO SP16);
      first [exact FRM|exact SH|exact IES|exact EESP|exact EESC|exact EESI|exact OF|exact OFN|exact OD|exact (ex_intro _ m AS)|exact CAN
            |unfold errno_addr in EA; exact EA|exact RSC|exact LIBR|exact LIBNS|exact REAR|exact KOW|exact KIDS|exact HEAP|exact AS|exact DC|exact AUX|exact ST|exact ERR'|exact MI|exact TP].
  Qed.

End Proofs.
End WithCeiling0.
