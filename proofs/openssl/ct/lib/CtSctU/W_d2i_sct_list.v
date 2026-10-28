(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk W_c2i_ibuf W_c2i_int W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import W_crypto_realloc W_get_object W_item_d2i_stmt W_asn1_string W_obj_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_free W_sct_list_free SctRep W_sct_new W_sct_leaves W_memdup W_sct_set1_signature W_sk_leaves W_sk_new W_realloc_array W_sk_push SctStmt W_o2i_sig W_o2i_sct O2iKit W_o2i_sct_list.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.


Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HR : rrealloc_stmt.
  Hypothesis HD2I : d2i_octet_spec.

  Section Act.
  Variables (X : Type) (KK : option (skr bptr) -> @AM bptr X) (Q : X * ap_st bptr -> PState -> machine_state -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (adr : bptr -> Z) (d : list Z) (D PIN : Z).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary D2I_SCT_LIST_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_ok m LB D d.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis PINlo : bv_unsigned sp <= PIN.
  Hypothesis PINhi : PIN + 8 <= B.
  Hypothesis PINal : PIN mod 8 = 0.
  Hypothesis HPIN : rw_cells ctusegs m PIN [C8 (wz D)].
  Hypothesis HK : forall ok st' s' ms',
    d2i_list_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr D (zlength d) PIN ok st' s' ms' ->
    implM ctusegs (interp (ap_embed (KK ok st'))) s' Q ms'.

  (* [comment removed for export] *)
  Definition STK : Z := Z.max D2I_OCTET_STACK O2I_SCT_LIST_STACK.
  Lemma CEIL : alloc_ceiling <= lo. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma GLO : 3493888 <= lo. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). unfold GLOBALS_TOP in H. exact H. Qed.
  Lemma LO : lo <= bv_unsigned sp + -64 - STK. Proof using PIN PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). unfold D2I_SCT_LIST_STACK in H. unfold STK. lia. Qed.
  Lemma STK0 : 0 <= STK. Proof. unfold STK, D2I_OCTET_STACK, O2I_SCT_LIST_STACK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK. lia. Qed.
  Lemma OFS0 : -64 <= 0. Proof. lia. Qed.
  Lemma OFS16 : -64 mod 16 = 0. Proof. reflexivity. Qed.
  Lemma SPB : bv_unsigned sp <= B. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma B63 : B < 2 ^ 63. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma SP16 : bv_unsigned sp mod 16 = 0. Proof using PRE. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64. Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma DF : Forall (fun b => 0 <= b < 256) d. Proof using PAY. destruct PAY as (_ & H & _). exact H. Qed.
  Lemma PBX : d = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz.
  Proof using PAY.
    destruct PAY as (_ & _ & _ & _ & _ & [H|([[pb PA] psz] & H1 & H2 & H3)]); [left; exact H| right]. exists pb, PA, psz. cbn [blk_addr blk_size fst snd] in H2, H3.
    split; [exact H1|]. split; [exact H2| exact H3].
  Qed.
  Lemma D0 : 0 <= D. Proof using PAY PIN. destruct PAY as (_ & _ & H & _). lia. Qed.
  Lemma NDL : List.NoDup (map blk_id (OW ++ LB)). Proof using PRE. destruct PRE as (HEAP & _). exact (LH_nodup _ _ _ HEAP). Qed.

  Local Notation oinvD := (oinv sp m s LB E lo B canary K d D PIN (-64) STK).
  Local Notation KFACTS := (oinv_facts sp m s LB E lo B canary K d D PIN (-64) STK).
  Local Notation KMUNCH := (oinv_munch sp m s LB E lo B canary K d D PIN (-64) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 PINlo PINhi PBX).
  Local Notation KHEAP := (oinv_heap sp m s LB E lo B canary K d D PIN (-64) STK CEIL GLO LO STK0 OFS0 SPB B63 PBX).
  Local Notation KCALL := (oinv_call sp m s LB E lo B canary K d D PIN (-64) STK GLO LO STK0 OFS0 SPB B63).
  Local Notation KAFTER := (oinv_after sp m s LB E lo B canary K d D PIN (-64) STK CEIL GLO LO STK0 OFS0 SPB B63 OFS16 PINlo PBX).
  Local Notation KPERM := (oinv_perm sp m s LB E lo B canary K d D PIN (-64) STK).
  Local Notation KRESP := (pre_resp sp E lo B canary d (-64) STK LO STK0 OFS0 SPB SP16).

  Local Ltac ctx := pose proof CEIL as CEIL; pose proof GLO as GLO; pose proof LO as LO; pose proof STK0 as STK0; pose proof SPB as SPB; pose proof B63 as B63;
                    pose proof SP16 as SP16; pose proof SPR as SPR; pose proof DF as DF; pose proof D0 as D0; pose proof (ESP sp lo B (-64) STK GLO LO STK0 OFS0 SPB B63) as ESP;
                    unfold STK, D2I_OCTET_STACK, O2I_SCT_LIST_STACK, O2I_SCT_STACK, O2I_SCT_SIGNATURE_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in LO.

  (* [comment removed for export] *)
  Definition dframe : list cell := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma free_tail : forall (ok : option (skr bptr)) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 pvT : word) (FL : bvmap 5 word) (fcL : bv 32)
      sL stL mT OWL errvL boL (adrO adrL : bptr -> Z) (NEWO NEWL : list block) (os : octet bptr) j,
    let A := adrO (os_blk os) in let DP := optr adrO (os_data os) in
    oinvD sL stL mT OWL errvL boL (NEWL ++ NEWO) -> frm0 fcL -> (forall r : reg, bv_unsigned r <> 10 -> reg_get FL r = reg_get F r) ->
    NEWO = oct_blocks adrO os -> (match os_data os with Some (dp, _) => dp <> os_blk os | None => True end) ->
    (forall b, In b LB -> adrO (blk_id b) = adr (blk_id b)) -> (forall b, In b (NEWO ++ LB) -> adrL (blk_id b) = adrO (blk_id b)) ->
    rw_cells ctusegs mT (bv_unsigned sp + -64) [CB 8 j] -> rw_cells ctusegs mT (bv_unsigned sp + -40) dframe ->
    rw_cells ctusegs mT (bv_unsigned sp + -48) [C8 (Z_to_bv 64 A)] -> rw_cells ctusegs mT PIN [C8 pvT] -> (exists pvP, rw_cells ctusegs mT (bv_unsigned sp + -56) [C8 pvP]) ->
    rw_cells ctusegs mT A [C4 (Z_to_bv 64 (os_len os)); C4 (Z_to_bv 64 V_ASN1_OCTET_STRING); C8 (Z_to_bv 64 DP); C8 (Z_to_bv 64 0)] ->
    match ok with
    | Some k => Permutation NEWL (sk_blocks adrL k) /\ sk_rep mT (OWL ++ NEWL ++ NEWO ++ LB) adrL k /\ pvT = wz (D + zlength d)
    | None => NEWL = []
    end ->
    implM ctusegs (interp (ap_embed (abind (octet_free os) (fun _ => KK ok) stL))) sL Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) x5 x6 x7 sp (wz PIN) x10 x11 x12 x13 x14 x15 x16 x17 (wz (zlength d))
              (wz match ok with Some k => adrL (sk_blk k) | None => 0 end) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          FL (Z_to_bv 64 0x19d3dc) fcL None mT (seg_rom ctusegs)).
  Proof using HF HK PAY PINlo PRE.
    intros until j. cbv zeta. intros OI FRML FEL ENO NBD ADRO ADRL FR0 FRH HOC HP (pvP & HPP) OCS OK. ctx.
    set (A := adrO (os_blk os)) in *. set (DP := optr adrO (os_data os)) in *.
    pose proof (KFACTS _ _ _ _ _ _ _ OI) as (HEAPT & NDT & BND & FRESH & _).
    pose proof (KCALL _ _ _ _ _ _ _ OI) as (_ & AUXT & SPBT & STT & _ & _ & ERRT & MI & CST & AST).
    pose proof OI as (PRET & LXT & KO & KI & KP & SO & FA & HB).
    assert (OIN : In (os_blk os, A, ASN1_STRING_SIZE) NEWO) by (rewrite ENO; left; reflexivity).
    pose proof (BND (os_blk os) A ASN1_STRING_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact OIN)) as (BA0 & _ & BAC & BAI & _). unfold ASN1_STRING_SIZE in BAC, BAI.
    set (L := OWL ++ (NEWL ++ NEWO) ++ LB) in *.
    (* [comment removed for export] *)
    assert (NI : forall q, In q (map blk_id NEWO) -> ~ In q (map blk_id (OWL ++ NEWL ++ LB))).
    { intros q Hq Hin. rewrite !map_app, !in_app_iff in Hin. apply in_map_iff in Hq. destruct Hq as (b & Eb & Hb).
      destruct Hin as [Hin|[Hin|Hin]].
      - apply (FRESH (blk_id b) (blk_addr b) (blk_size b)); [destruct b as [[q' Aq] n]; apply in_app_iff; right; exact Hb| rewrite map_app; apply in_app_iff; left; rewrite Eb; exact Hin].
      - subst L. rewrite (map_app blk_id OWL), (map_app blk_id (NEWL ++ NEWO) LB), map_app in NDT.
        destruct (NoDup_app_split _ _ NDT) as (N23 & _ & _). destruct (NoDup_app_split _ _ N23) as (_ & _ & N2). destruct (NoDup_app_split _ _ N2) as (_ & DX & _).
        apply (DX q Hin). rewrite <- Eb. apply in_map. exact Hb.
      - apply (FRESH (blk_id b) (blk_addr b) (blk_size b)); [destruct b as [[q' Aq] n]; apply in_app_iff; right; exact Hb| rewrite map_app; apply in_app_iff; right; rewrite Eb; exact Hin]. }
    assert (EQL : lb_remove (os_blk os) (lremove (os_data os) L) = OWL ++ NEWL ++ LB).
    { subst L. rewrite ENO in NI |- *. unfold oct_blocks in NI |- *.
      assert (NIB := NI (os_blk os) ltac:(left; reflexivity)). rewrite !map_app, !in_app_iff in NIB.
      destruct (os_data os) as [[dp n]|]; cbn [lremove].
      - assert (NID := NI dp ltac:(right; left; reflexivity)). rewrite !map_app, !in_app_iff in NID.
        rewrite !lb_remove_app. rewrite (lb_remove_notin dp OWL), (lb_remove_notin dp NEWL), (lb_remove_notin dp LB) by tauto.
        rewrite !lb_remove_cons. cbn [blk_id fst snd]. rewrite (bptr_eqb_neq (os_blk os) dp) by (intros E0; apply NBD; symmetry; exact E0). rewrite !bptr_eqb_refl.
        change (lb_remove dp []) with (@nil block). rewrite lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl. change (lb_remove (os_blk os) []) with (@nil block).
        rewrite (lb_remove_notin (os_blk os) OWL), (lb_remove_notin (os_blk os) NEWL), (lb_remove_notin (os_blk os) LB) by tauto. rewrite app_nil_r. reflexivity.
      - rewrite !lb_remove_app, lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl. change (lb_remove (os_blk os) []) with (@nil block).
        rewrite (lb_remove_notin (os_blk os) OWL), (lb_remove_notin (os_blk os) NEWL), (lb_remove_notin (os_blk os) LB) by tauto. rewrite app_nil_r. reflexivity. }
    unfold dframe in FRH. unfold MallocRep.wz in HP |- *.
    pose proof (munch_refl (@nil (Z * Z)) mT) as MU. pose proof (wmono_refl ctusegs mT) as WM.
    unfold implM. iprefix. step. step. ihere. to_implM.
    (* [comment removed for export] *)
    assert (KT : forall sG msG, vfree_post (Z_to_bv 64 0x19d3e4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp sp (Z_to_bv 64 PIN) (Z_to_bv 64 (zlength d))
                                           (Z_to_bv 64 match ok with Some k => adrL (sk_blk k) | None => 0 end) s4 s5 s6 s7 s8 s9 s10 s11 FL fcL sL
                                           (lb_remove (os_blk os) (lremove (os_data os) L)) lo B errvL mT (fun _ => True) sG msG ->
                 implM ctusegs (interp (ap_embed (KK ok stL))) sG Q msG).
    { intros sG msG PO. unfold vfree_post in PO. rewrite ?ESP, EQL in PO.
      destruct PO as (g0 & g1 & g2 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g3 & g4 & g5 & g6 & mG & -> & MIG & STG & ERRG & AUXG & HPG & FAG & SOG & HEAPG & _).
      replace (ret_pc (Z_to_bv 64 0x19d3e4)) with (Z_to_bv 64 0x19d3e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (OIG : oinvD sG stL mG OWL errvL boL NEWL).
      { eapply (KHEAP _ _ _ _ _ _ (NEWL ++ NEWO) sG mG errvL _ _ NEWL); [exact OI| exact HPG| | exact HEAPG| apply Permutation_refl| exact MIG| exact STG| exact ERRG| exact AUXG| exact FAG| exact SOG].
        intros b Hb. rewrite !in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
      pose proof (agree_of_heap_pres _ _ _ _ HPG) as AGG.
      apply (rw_cells_agree _ _ _ _ _ AGG) in FR0; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGG) in FRH; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGG) in HP; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGG) in HPP; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGG) in HOC; [| intros a Ha; left; cbn in Ha; lia].
      clear MU WM MI. rename MIG into MI. pose proof (munch_refl (@nil (Z * Z)) mG) as MU. pose proof (wmono_refl ctusegs mG) as WM.
      pose proof OIG as (PREG & LXG & KOG & KIG & KPG & SO' & FA' & _). pose proof (KFACTS _ _ _ _ _ _ _ OIG) as (_ & _ & _ & FRESHG & _).
      pose proof (KCALL _ _ _ _ _ _ _ OIG) as (_ & _ & _ & STG' & _).
      unfold implM. iprefix. step. step. do 5 step.
      release_frame FR0 STG' (bv_unsigned sp + -56). release_frame HPP STG' (bv_unsigned sp + -48). release_frame HOC STG' (bv_unsigned sp + -40). release_frame FRH STG' (bv_unsigned sp).
      step. step. ihere. to_implM.
      eapply HK. unfold d2i_list_post.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FL, fcL, mG, OWL, errvL, boL, adrL, NEWL.
      split; [reflexivity|]. split; [exact FRML|]. split; [exact FEL|].
      split; [eapply KRESP; [exact PREG| exact STG']|].
      split; [exact LXG|]. split; [exact SO'|]. split; [exact FA'|].
      split; [split; [exact KOG| split; [intros b Hb Hin; apply (KIG b Hb); apply in_app_iff; left; exact Hin| exact KPG]]|].
      split; [intros b Hb; rewrite (ADRL b) by (apply in_app_iff; right; exact Hb); apply ADRO; exact Hb|].
      split; [intros [[q Aq] n] Hb; cbn; exact (FRESHG q Aq n Hb)|].
      destruct ok as [k|].
      - destruct OK as (PM & SK & ->). split; [exact PM|]. split; [| exact HP].
        eapply (sk_rep_agreeP _ mT mG); [exact AGG| | eapply sk_rep_mono; [| exact SK]].
        + intros q Aq n a Hq Ha. right. right. exists (q, Aq, n). split; [| cbn; lia]. apply in_app_iff. right. apply in_app_iff. left. eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hq].
        + intros b Hb. apply in_app_iff. right. apply in_app_iff. left. eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb].
      - split; [exact OK|]. exists pvT. exact HP. }
    unfold octet_free. destruct (os_data os) as [[dp n]|] eqn:EOD; cbn [abind apbind afree_opt afree aret option_map fst snd ap_embed lremove] in KT |- *.
    - eapply (ASN1_pfree_walk HF) with (L := L) (lo := lo) (B := B) (A := A) (D := DP) (alloc := n) (len := os_len os) (ty := V_ASN1_OCTET_STRING);
        [right; left; reflexivity| exact HEAPT| exact AUXT| rewrite ESP; lia| rewrite ESP; exact STT| exact CEIL| unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
        | exact ERRT| exact MI| reflexivity| exact CST
        | subst L; apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact OIN
        | subst L; apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; rewrite ENO; right; cbn; rewrite EOD; left; subst DP; reflexivity
        | intros E0; apply NBD; symmetry; exact E0
        | unfold asn1_string_cells, MallocRep.wz; subst DP; cbn [optr] in OCS |- *; exact OCS| reflexivity| exact KT].
    - eapply (ASN1_pfree_nodata_walk HF) with (L := L) (lo := lo) (B := B) (A := A) (len := os_len os) (ty := V_ASN1_OCTET_STRING);
        [right; left; reflexivity| exact HEAPT| exact AUXT| rewrite ESP; lia| rewrite ESP; exact STT| exact CEIL| unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
        | exact ERRT| exact MI| reflexivity| exact CST
        | subst L; apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; right; exact OIN
        | unfold asn1_string_cells, MallocRep.wz; subst DP; cbn [optr] in OCS |- *; exact OCS| reflexivity| exact KT].
  Qed.

  Theorem d2i_main : forall (t0 t1 t2 t3 a3 a4 a5 a6 a7 t4 t5 t6 : word),
    implM ctusegs (interp (ap_embed (d2i_list_tree d KK st))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz PIN) (wz (zlength d)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz D2I_SCT_LIST) fc None m (seg_rom ctusegs)).
  Proof using ADR FRM HD2I HF HK HM HPIN HR KIDS KOW PAY PINal PINhi PINlo PRE TP.
    intros. ctx. rewrite TP.
    pose proof PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & _).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    unfold MallocRep.wz in HPIN. pose proof HPIN as HP. clear HPIN.
    pose proof PAY as (HB0 & _).
    assert (OI0 : oinvD s st m OW errv bo []).
    { eapply (oinv_entry sp m s LB E lo B canary K d D PIN (-64) STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 PINlo PINhi st OW bo errv); [| exact KOW| exact KIDS| exact HB0].
      unfold STK. unfold D2I_SCT_LIST_STACK in PRE. exact PRE. }
    unfold D2I_SCT_LIST, MallocRep.wz.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 7 step. step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia|]. clear K1.
    step. step. step. step. step. name_mem m1.
    assert (OI1 : oinvD s st m1 OW errv bo []).
    { eapply KMUNCH; [exact OI0| exact MU| exact WM| exact MI| exact ST| exact ERR|]. constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app m1 (bv_unsigned sp + -64) [CB 8 _] _)) in FR. destruct FR as [FR0 FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    apply (proj1 (rw_cells_app m1 _ [C8 (Z_to_bv 64 D)] _)) in FR1. destruct FR1 as [FRP FR1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR1.
    apply (proj1 (rw_cells_app m1 _ [C8 (Z_to_bv 64 0)] _)) in FR1. destruct FR1 as [FRO FRH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRH.
    replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FRP by lia.
    replace (bv_unsigned sp + -64 + 8 + 8) with (bv_unsigned sp + -48) in FRO by lia.
    replace (bv_unsigned sp + -64 + 8 + 8 + 8) with (bv_unsigned sp + -40) in FRH by lia.
    (* [comment removed for export] *)
    step. ihere. unfold d2i_list_tree. to_implM.
    pose proof OI1 as (PRE1 & LX1 & KO1 & KI1 & KP1 & SO1 & FA1 & HB1).
    eapply implM_abind.
    { pose proof HD2I as W. unfold d2i_octet_spec in W.
      eapply W with (LB := LB) (K := K) (adr := adr) (D := D) (OPP := bv_unsigned sp + -56) (OCT := bv_unsigned sp + -48) (lo := lo) (B := B) (E := E) (bo := bo) (OW := OW) (errv := errv) (canary := canary); clear W;
        [ eapply ap_pre_stack_le; [exact PRE1| unfold STK; lia]| reflexivity| exact FRM| exact KO1| exact KI1
        | destruct PAY as (_ & P1 & P2 & P3 & P4 & P5); split; [exact HB1| split; [exact P1| split; [exact P2| split; [exact P3| split; [exact P4| exact P5]]]]]
        | exact ADR| rewrite ESP; lia| lia| exact FRP| clear - SP16; Z.div_mod_to_equations; lia| rewrite ESP; lia| lia| exact FRO| clear - SP16; Z.div_mod_to_equations; lia| lia| reflexivity| reflexivity| reflexivity]. }
    intros r sO msO PO. unfold d2i_octet_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & FS & fcS & mO & OWO & errvO & boO & adrO & NEWO & ov & cv
                    & -> & FRMS & FES & PREO & LXO & SOO & FAO & BKO & ADRO & FRESHO & HPP & HOC & RES).
    destruct r as [oo stO]. cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 0x19d37c)) with (Z_to_bv 64 0x19d37c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (OIO : oinvD sO stO mO OWO errvO boO (NEWO ++ [])).
    { eapply (KAFTER s st m1 OW errv bo [] sO stO mO OWO errvO boO [(bv_unsigned sp + -56, bv_unsigned sp + -56 + 8); (bv_unsigned sp + -48, bv_unsigned sp + -48 + 8)]%Z NEWO);
        [exact OI1| exact PREO| exact LXO| | exact SOO| exact FAO| exact BKO].
      intros a Ha. cbn [rin_ivs fst snd] in Ha. left. lia. }
    rewrite app_nil_r in OIO.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXO) as AGO.
    assert (CLo : forall a, bv_unsigned sp + -64 <= a -> ~ (bv_unsigned sp + -56 <= a < bv_unsigned sp + -40) ->
                lx_client ([] ++ LB) (bv_unsigned sp + -64) ([(bv_unsigned sp + -56, bv_unsigned sp + -56 + 8); (bv_unsigned sp + -48, bv_unsigned sp + -48 + 8)]%Z ++ LIBW_AP) a).
    { intros a Ha Hn. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; exact Ha]. }
    apply (rw_cells_agree _ _ _ _ _ AGO) in FR0; [| intros a Ha; apply CLo; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGO) in FRH; [| intros a Ha; apply CLo; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGO) in HP; [| intros a Ha; apply CLo; cbn in Ha; lia].
    clear MU WM MI AGO CLo. pose proof (KCALL _ _ _ _ _ _ _ OIO) as (HEAPO & AUXO & SPBO & STO & _ & _ & ERRO & MI & CSO & ASO).
    unfold LX_ERRNO, RATP in ERRO. change (3355176 - 164) with 3355012 in ERRO.
    pose proof (KFACTS _ _ _ _ _ _ _ OIO) as (_ & NDO & BNDO & FRESHO' & _).
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8)]%Z mO) as MU. pose proof (wmono_refl ctusegs mO) as WM.
    unfold MallocRep.wz.
    destruct oo as [os|].
    - (* [comment removed for export] *)
      destruct RES as (ENO & ORP & ->). unfold MallocRep.wz in HOC.
      pose proof ORP as (OIN & OCS & OLEN & ODF & OL31 & ODAT).
      set (A := adrO (os_blk os)) in *.
      pose proof (BNDO (os_blk os) A ASN1_STRING_SIZE ltac:(apply in_app_iff; right; apply in_app_iff; left; rewrite ENO; left; reflexivity)) as (BA0 & _ & BAC & BAI & BAL). unfold ASN1_STRING_SIZE in BAC, BAI.
      unfold asn1_string_cells, MallocRep.wz in OCS.
      set (DP := optr adrO (os_data os)) in *.
      assert (DPR : 0 <= DP /\ DP + zlength (os_bytes os) < 2 ^ 63 /\ (os_data os = None -> DP = 0)).
      { subst DP. destruct (os_data os) as [[dp n]|] eqn:EOD; cbn [optr].
        - destruct ODAT as (NBD & DIN & DLE & DBY). pose proof (BNDO dp (adrO dp) n ltac:(apply in_app_iff; right; apply in_app_iff; left; rewrite ENO; right; cbn; rewrite EOD; left; reflexivity)) as (B1 & B2 & B3 & B4 & B5).
          split; [lia|]. split; [lia| discriminate].
        - rewrite ODAT. unfold zlength. cbn. split; [lia|]. split; [lia| reflexivity]. }
      destruct DPR as (DP0 & DP63 & DPN).
      unfold implM. iprefix.
      step. if_cases KN; zc KN; [exfalso; revert KN; rewrite ?land_ones64_small, ?unsigned_lit by lia; lia|]. clear KN.
      (* [comment removed for export] *)
      step. step. carve_frame 16%nat STO. do 4 step. step. if_cases KG0; zify_cond KG0; [exfalso; rewrite ?unsigned_lit in KG0 by lia; lia|]. clear KG0.
      step. step. if_cases KG1; zify_cond KG1; [exfalso; revert KG1; rewrite ?unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - BAL; Z.div_mod_to_equations; lia|]. clear KG1.
      step. do 3 step. release_frame FR STO (bv_unsigned sp + -64). step.
      (* [comment removed for export] *)
      step. step. step.
      step. carve_frame 16%nat STO. do 4 step. step. if_cases KL0; zify_cond KL0; [exfalso; rewrite ?unsigned_lit in KL0 by lia; lia|]. clear KL0.
      step. step. if_cases KL1; zify_cond KL1; [exfalso; revert KL1; rewrite ?unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - BAL; Z.div_mod_to_equations; lia|]. clear KL1.
      step. do 3 step. release_frame FR STO (bv_unsigned sp + -64). step.
      assert (OL0 : 0 <= os_len os) by (rewrite OLEN; unfold zlength; lia).
      setreg 10%Z (Z_to_bv 64 (os_len os)) ltac:(symmetry; apply sx32_small; lia).
      step. step. step. name_mem m2.
      assert (OI2 : oinvD sO stO m2 OWO errvO boO NEWO).
      { eapply KMUNCH; [exact OIO| exact MU| exact WM| exact MI| exact STO| exact ERRO|]. constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity| constructor]. }
      pose proof OI2 as (PRE2 & LX2 & KO2 & KI2 & KP2 & SO2 & FA2 & HB2).
      step. ihere. to_implM.
      eapply implM_abind.
      { pose proof (o2i_sct_list_walk HM HF HR) as W. unfold o2i_sct_list_spec in W.
        eapply W with (LB := NEWO ++ LB) (K := K) (adr := adrO) (c := os_bytes os) (D := DP) (PIN := bv_unsigned sp + -56) (lo := lo) (B := B) (E := E) (bo := boO) (OW := OWO) (errv := errvO) (canary := canary); clear W.
        - eapply ap_pre_stack_le; [exact PRE2| unfold STK; lia].
        - reflexivity.
        - exact FRMS.
        - exact KO2.
        - exact KI2.
        - exact OLEN.
        - exact DP0.
        - exact DP63.
        - exact ODF.
        - destruct (os_data os) as [[dp n]|] eqn:EOD.
          + destruct ODAT as (NBD & DIN & DLE & DBY). subst DP. cbn [optr].
            eapply bytes_at_transport; [exact DBY| exact MU|].
            pose proof (BNDO dp (adrO dp) n ltac:(apply in_app_iff; right; apply in_app_iff; left; rewrite ENO; right; cbn; rewrite EOD; left; reflexivity)) as (B1 & B2 & B3 & B4 & B5).
            rewrite zlength_to_bytes. cbn. lia.
          + rewrite ODAT, (DPN eq_refl). cbn. unfold bytes_at. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
        - destruct (os_data os) as [[dp n]|] eqn:EOD; [right| left; exact ODAT]. destruct ODAT as (NBD & DIN & DLE & DBY). exists dp, (adrO dp), n.
          split; [apply in_app_iff; left; rewrite ENO; right; cbn; rewrite EOD; left; reflexivity|]. subst DP. cbn [optr]. lia.
        - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| rewrite (ADRO b Hb); apply ADR; exact Hb].
          rewrite ENO in Hb. destruct b as [[q Aq] n]. cbn. destruct Hb as [E0|Hb]; [injection E0; intros; subst; reflexivity|].
          destruct (os_data os) as [[dp n']|]; [| destruct Hb]. destruct Hb as [E0|[]]. injection E0; intros; subst; reflexivity.
        - rewrite ESP. lia.
        - lia.
        - clear - SP16. Z.div_mod_to_equations. lia.
        - exact HPP.
        - reflexivity.
        - reflexivity.
        - reflexivity. }
      intros r sL msL POL. unfold o2i_list_post in POL. rewrite ?ESP in POL.
      destruct POL as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & FL & fcL & mL & OWL & errvL & boL & adrL & NEWL & pv
                       & -> & FRML & FEL & PREL & LXL & SOL & FAL & BKL & ADRL & FRESHL & HPL & RESL).
      destruct r as [ok stL]. cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 0x19d3a8)) with (Z_to_bv 64 0x19d3a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (OIL : oinvD sL stL mL OWL errvL boL (NEWL ++ NEWO)).
      { eapply (KAFTER sO stO m2 OWO errvO boO NEWO sL stL mL OWL errvL boL [(bv_unsigned sp + -56, bv_unsigned sp + -56 + 8)]%Z NEWL);
          [exact OI2| exact PREL| exact LXL| | exact SOL| exact FAL| exact BKL].
        intros a Ha. cbn [rin_ivs fst snd] in Ha. left. lia. }
      pose proof (agree_of_lx_pres _ _ _ _ _ LXL) as AGL.
      assert (CLl : forall a, bv_unsigned sp + -64 <= a -> ~ (bv_unsigned sp + -56 <= a < bv_unsigned sp + -48) ->
                  lx_client (NEWO ++ LB) (bv_unsigned sp + -64) ([(bv_unsigned sp + -56, bv_unsigned sp + -56 + 8)]%Z ++ LIBW_AP) a).
      { intros a Ha Hn. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AGL) in FR0; [| intros a Ha; apply CLl; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGL) in FRH; [| intros a Ha; apply CLl; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGL) in HP; [| intros a Ha; apply CLl; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGL) in HOC; [| intros a Ha; apply CLl; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGL) in OCS.
      2:{ intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|]. right. left. exists (os_blk os, A, ASN1_STRING_SIZE).
          split; [apply in_app_iff; left; rewrite ENO; left; reflexivity| cbn in Ha |- *; unfold ASN1_STRING_SIZE; lia]. }
      clear MU WM MI AGL CLl. pose proof (KCALL _ _ _ _ _ _ _ OIL) as (HEAPL & AUXL & SPBL & STL & _ & _ & ERRL & MI & CSL & ASL).
      unfold LX_ERRNO, RATP in ERRL. change (3355176 - 164) with 3355012 in ERRL.
      pose proof (KFACTS _ _ _ _ _ _ _ OIL) as (_ & NDL2 & BNDL & FRESHL' & _).
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PIN, PIN + 8)]%Z mL) as MU. pose proof (wmono_refl ctusegs mL) as WM.
      unfold MallocRep.wz.
      assert (NBD : match os_data os with Some (dp, _) => dp <> os_blk os | None => True end) by (destruct (os_data os) as [[dp n]|]; [exact (proj1 ODAT)| exact I]).
      assert (FEL' : forall r0 : reg, bv_unsigned r0 <> 10 -> reg_get FL r0 = reg_get F r0) by (intros r0 Hr0; rewrite (FEL r0 Hr0); apply (FES r0 Hr0)).
      destruct ok as [k|].
      + (* [comment removed for export] *)
        destruct RESL as [PML SKL].
        pose proof (BNDL (sk_blk k) (adrL (sk_blk k)) STACK_SIZE) as BK.
        specialize (BK ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PML|]; unfold sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity)).
        destruct BK as (BK0 & _ & BKC & BKI & _). unfold STACK_SIZE in BKC, BKI.
        unfold implM. iprefix. step. step. if_cases KZ; zc KZ; [exfalso; revert KZ; rewrite ?land_ones64_small, ?unsigned_lit by lia; lia|]. clear KZ.
        step. step. setreg 10%Z (Z_to_bv 64 (D + zlength d)) ltac:(symmetry; apply bv_eq; destruct PAY as (_ & _ & P2 & P3 & P4 & _); rewrite ?unsigned_lit by lia; bv_solve).
        pose proof PAY as (_ & _ & PD0 & PD63 & PD30 & _). assert (LZ : 0 <= zlength d) by (unfold zlength; lia).
        step. step. setreg 12%Z (Z_to_bv 64 1) ltac:(rewrite v_sltu_b2z, !unsigned_lit by lia; destruct (Z.ltb_spec 0 D); [reflexivity| lia]).
        setreg 13%Z (Z_to_bv 64 0) ltac:(rewrite v_sltiu_b2z, unsigned_lit by lia; replace (bv_wrap 64 1) with 1 by reflexivity; destruct (Z.ltb_spec (D + zlength d) 1); [lia| reflexivity]).
        step. if_cases K2; zc K2; [exfalso; revert K2; rewrite ?unsigned_lit by lia; lia|]. clear K2.
        step. step. setreg 11%Z (Z_to_bv 64 0) ltac:(rewrite v_sltu_b2z, !unsigned_lit by lia; destruct (Z.ltb_spec (D + zlength d) D); [lia| reflexivity]).
        setreg 12%Z (Z_to_bv 64 0) ltac:(rewrite v_slti_b2z, unsigned_lit, zb_lxor_sign by lia; rewrite Z.mod_small by lia; destruct (Z.ltb_spec (zlength d + 2 ^ 63) (0 + 2 ^ 63)); [lia| reflexivity]).
        step. step. setreg 11%Z (Z_to_bv 64 1) ltac:(apply bv_eq; vm_compute; reflexivity).
        step. if_cases K3; zc K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; lia|]. clear K3.
        step. name_mem m3.
        assert (OI3 : oinvD sL stL m3 OWL errvL boL (NEWL ++ NEWO)).
        { eapply KMUNCH; [exact OIL| exact MU| exact WM| exact MI| exact STL| exact ERRL|]. constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity| constructor]. }
        ihere. to_implM.
        eapply (free_tail (Some k) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FL fcL sL stL m3 OWL errvL boL adrO adrL NEWO NEWL os);
          [exact OI3| exact FRML| exact FEL'| exact ENO| exact NBD| exact ADRO| exact ADRL| exact FR0| exact FRH| exact HOC| exact HP| eexists; exact HPL| exact OCS|].
        split; [exact PML|]. split; [| reflexivity].
        eapply (sk_rep_agreeP _ mL m3); [apply (agree_on_of_munch _ _ _ MU WM)| | exact SKL].
        intros q Aq n a Hq Ha. cbn beta.
        pose proof (BNDL q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PML| exact Hq])) as (B1 & B2 & B3 & B4 & B5).
        apply seg_outside. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor].
      + (* [comment removed for export] *)
        unfold implM. iprefix. step. step. if_cases KZ; zc KZ; [| exfalso; apply KZ; reflexivity]. clear KZ.
        ihere. to_implM.
        eapply (free_tail None _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FL fcL sL stL mL OWL errvL boL adrO adrL NEWO NEWL os);
          [exact OIL| exact FRML| exact FEL'| exact ENO| exact NBD| exact ADRO| exact ADRL| exact FR0| exact FRH| exact HOC| exact HP| eexists; exact HPL| exact OCS| exact RESL].
    - (* [comment removed for export] *)
      subst NEWO. cbn [app] in OIO.
      pose proof OIO as (PREO' & LXO' & KOO & KIO & KPO & SOO' & FAO' & _).
      unfold implM. iprefix. step. if_cases KZ; zc KZ; [| exfalso; apply KZ; reflexivity]. clear KZ.
      step. step. do 5 step.
      release_frame FR0 STO (bv_unsigned sp + -56). release_frame HPP STO (bv_unsigned sp + -48). release_frame HOC STO (bv_unsigned sp + -40). release_frame FRH STO (bv_unsigned sp).
      step. step. ihere. to_implM.
      eapply HK. unfold d2i_list_post.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FS, fcS, mO, OWO, errvO, boO, adrO, [].
      split; [reflexivity|]. split; [exact FRMS|]. split; [exact FES|].
      split; [eapply KRESP; [exact PREO'| exact STO]|].
      split; [exact LXO'|]. split; [exact SOO'|]. split; [exact FAO'|].
      split; [split; [exact KOO| split; [intros b Hb Hin; apply (KIO b Hb); apply in_app_iff; left; exact Hin| exact KPO]]|].
      split; [exact ADRO|]. split; [intros b []|]. split; [reflexivity|]. exists (Z_to_bv 64 D). exact HP.
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem d2i_sct_list_walk : d2i_sct_list_spec.
  Proof using HD2I HF HM HR.
    unfold d2i_sct_list_spec. intros until PIN. intros PRE TP FRM KOW KIDS PAY ADR PINlo PINhi PINal HPIN -> -> -> HK.
    eapply d2i_main; eassumption.
  Qed.
End Proofs.
End WithCeiling0.
