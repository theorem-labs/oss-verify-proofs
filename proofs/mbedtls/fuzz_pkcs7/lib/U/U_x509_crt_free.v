(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux CellsX Cells Mem Step Frame Tac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_asn1_sequence_free U_asn1_free_named_data_list_shallow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts CrtStmts CrtRelStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import H3Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition pk0 (f : crt_own) : crt_own :=
  CRT (co_ob f) (co_rawlen f) (co_rawp f) (co_issuer_next f) (co_issuer f) (co_subject_next f) (co_subject f)
      0 0 (co_pkowned f) (co_san_next f) (co_san f) (co_akid_next f) (co_akid f) (co_pol_next f) (co_pol f)
      (co_eku_next f) (co_eku f) (co_sigopts f).

Definition crt_pre (f : crt_own) (j : crt_junk) : list cell := firstn 11 (crt_cells f j).    (* [comment removed for export] *)
Definition crt_suf (f : crt_own) (j : crt_junk) : list cell := skipn 13 (crt_cells f j).     (* [comment removed for export] *)

Lemma crt_cells_pk0 f j :
  crt_cells (pk0 f) j = crt_pre f j ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ crt_suf f j.
Proof. reflexivity. Qed.
Lemma crt_pre_size f j : Z.of_nat (cells_size (crt_pre f j)) = 360.
Proof. reflexivity. Qed.
Lemma crt_suf_size f j : Z.of_nat (cells_size (crt_suf f j)) = 368.
Proof. reflexivity. Qed.

Lemma rw_cells_blob m A0 cs : rw_cells usegs m A0 cs -> rw_cells usegs m A0 [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros H. pose proof H as H'. destruct H' as [[Hwf _] _].
  eapply rw_cells_reshape; [exact H| cbn; split; [apply cells_bytes_length; exact Hwf| exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Hypothesis HFREE : hl_free L = 0x3fa98.
  Hypothesis HMSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis PKFREE : pk_free_stmt2 usegs L HI PK 0x29c28.

  Let SHALLOW := U_asn1_free_named_data_list_shallow_spec L HI HFREE HLS.
  Let SEQFREE := U_asn1_sequence_free_spec L HI HFREE HLS.
  Let ZFREE := U_zeroize_and_free_spec L HI HFREE HLS SW DIMG.

  (* [comment removed for export] *)
  Section Inv.
    Variables (sp ra s0 s1 s2 : word) (m : mem) (mo : Model) (h : HST usegs L HI) (LBo LB : list blk)
              (A lo : Z) (f : crt_own) (j : crt_junk).

    Definition cinv (P : list blk) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST usegs L HI) : Prop :=
      HEAP usegs L HI hc (Lc ++ LB) mc moc
      /\ heap_top usegs L HI hc = heap_top usegs L HI h
      /\ mo_frame mo moc
      /\ (forall b, In b Lc -> In b LBo)
      /\ (forall b, In b LBo -> ~ In (fst b) (map fst P) -> In b Lc)
      /\ (forall b, In b Lc -> In (fst b) (map fst P) -> fst b = co_rawp f /\ co_rawp f <> 0 /\ co_ob f <> Z_to_bv 64 1)
      /\ heap_presx usegs L (Lc ++ LB) (bv_unsigned sp) [(A + 360, A + 376)] m mc
      /\ rw_cells usegs mc (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells usegs mc A (crt_cells (pk0 f) j)
      /\ mem_inv usegs mc /\ statics_ok usegs L mc /\ stk usegs mc lo (bv_unsigned sp + -32).

    Hypothesis SUB : forall b, In b (crt_blocks f) -> In b LBo.
    Hypothesis ND : List.NoDup (map fst (crt_blocks f)).
    Hypothesis HH : HEAP usegs L HI h (LBo ++ LB) m mo.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LOSP : lo <= bv_unsigned sp + -32.
    Hypothesis SPA : bv_unsigned sp <= A.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.

    #[using="ND"] Lemma seg_nodup P S R : crt_blocks f = P ++ S ++ R -> List.NoDup (map fst S).
    Proof.
      intros E. pose proof ND as N. rewrite E, !map_app in N.
      apply NoDup_app_inv_r in N. apply NoDup_app_inv_l in N. exact N.
    Qed.

    #[using="ND"] Lemma seg_nodup_nodes P ns nodes R : crt_blocks f = P ++ map (fun a => (a, ns)) nodes ++ R -> List.NoDup nodes.
    Proof. intros E. pose proof (seg_nodup _ _ _ E) as N. rewrite map_fst_map_pair in N. exact N. Qed.

    #[using="SUB ND"] Lemma cinv_seg_in P S R Lc mc moc hc :
      cinv P Lc mc moc hc -> crt_blocks f = P ++ S ++ R -> forall b, In b S -> In b Lc.
    Proof.
      intros CI E b Hb. ddestruct CI as (_ & _ & _ & _ & KEEP & _).
      apply KEEP; [apply SUB; rewrite E; apply in_or_app; right; apply in_or_app; left; exact Hb|].
      pose proof ND as N. rewrite E, !map_app in N.
      apply (NoDup_app_notin_l _ _ (fst b) N). apply in_or_app. left. apply in_map. exact Hb.
    Qed.

    #[using="SUB ND HH CEIL LOSP SPA"] Lemma cinv_chain P ns no NP nodes R Lc mc moc hc a :
      cinv P Lc mc moc hc -> crt_blocks f = P ++ map (fun a => (a, ns)) nodes ++ R ->
      chain usegs ns no NP m (LBo ++ LB) a nodes -> 0 <= ns ->
      chain usegs ns no NP mc (Lc ++ LB) a nodes.
    Proof.
      intros CI E HC Hns. pose proof CI as CI'. ddestruct CI' as (_ & _ & _ & _ & _ & _ & HPX & _).
      eapply chain_presx; [exact HC| | exact HPX| exact Hns|].
      - intros x Hx. apply in_or_app. left. eapply (cinv_seg_in _ _ _ _ _ _ _ CI E). apply in_map_iff. exists x. auto.
      - intros x Hx. pose proof (chain_nodes_below usegs L HI _ _ _ _ _ _ _ _ _ _ HH HC Hns x Hx) as B.
        cbn [disjoint_from]. lia.
    Qed.

    #[using="Type"] Lemma cinv_skip P S Lc mc moc hc : cinv P Lc mc moc hc ->
      (forall b, In b Lc -> In (fst b) (map fst S) -> fst b = co_rawp f /\ co_rawp f <> 0 /\ co_ob f <> Z_to_bv 64 1) ->
      cinv (P ++ S) Lc mc moc hc.
    Proof.
      intros CI HS. ddestruct CI as (C1 & C2 & C3 & C4 & KEEP & REL & C6).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj _ (conj _ C6)))))).
      - intros b Hb Hn. apply KEEP; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
      - intros b Hb Hin. rewrite map_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (REL b Hb Hin)| exact (HS b Hb Hin)].
    Qed.

    #[using="Type"] Lemma nodup_fst_lb_remove : forall (l : list blk) x, List.NoDup (map fst l) -> List.NoDup (map fst (lb_remove x l)).
    Proof.
      induction l as [|[c k] l IH]; cbn; intros x NDx; [constructor|].
      apply List.NoDup_cons_iff in NDx as [Hni NDy]. destruct (Z.eqb_spec c x) as [->|NE]; [exact NDy|].
      cbn. constructor; [| apply IH; exact NDy]. intros C. apply Hni. apply in_map_iff in C. ddestruct C as (b & E & Hb).
      apply in_map_iff. exists b. split; [exact E| eapply In_lb_remove; exact Hb].
    Qed.

    #[using="Type"] Lemma lb_remove_all_fst_notin : forall nodes (l : list blk) b, List.NoDup (map fst l) -> In b (lb_remove_all nodes l) -> ~ In (fst b) nodes.
    Proof.
      induction nodes as [|a r IH]; cbn; intros l b NDx Hb; [tauto|].
      intros [E|Hin].
      - subst a. pose proof (In_lb_remove_all _ _ _ Hb) as Hb1. exact (lb_remove_fst_neq _ _ _ NDx Hb1 eq_refl).
      - exact (IH _ _ (nodup_fst_lb_remove _ _ NDx) Hb Hin).
    Qed.

    #[using="SW HND SUB ND SPA"] Lemma cinv_after_chain P ns nodes R Lc mc moc hc m' mo' (h' : HST usegs L HI) :
      cinv P Lc mc moc hc -> crt_blocks f = P ++ map (fun a => (a, ns)) nodes ++ R ->
      HEAP usegs L HI h' (lb_remove_all nodes (Lc ++ LB)) m' mo' ->
      heap_pres usegs L (lb_remove_all nodes (Lc ++ LB)) (bv_unsigned sp + -32) mc m' ->
      heap_top usegs L HI h' = heap_top usegs L HI hc -> mo_frame moc mo' -> mem_inv usegs m' ->
      stk usegs m' lo (bv_unsigned sp + -32) ->
      cinv (P ++ map (fun a => (a, ns)) nodes) (lb_remove_all nodes Lc) m' mo' h'.
    Proof.
      intros CI E HH' HP HT' MF' MI' ST'.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      assert (HINn : forall x, In x nodes -> In x (map fst Lc)).
      { intros x Hx. replace x with (fst (x, ns)) by reflexivity. apply in_map.
        eapply (cinv_seg_in _ _ _ _ _ _ _ CI E). apply in_map_iff. exists x. auto. }
      rewrite (lb_remove_all_app_l nodes Lc LB NDn HINn) in HH', HP.
      ddestruct CI as (C1 & C2 & C3 & SUBL & KEEP & REL & HPX & FR & CELLS & MI & SO & ST).
      pose proof (HND _ _ _ _ C1) as NDL. rewrite map_app in NDL. apply NoDup_app_inv_l in NDL.
      pose proof (rw_cells_bound usegs _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
      assert (SUBL' : forall b, In b (lb_remove_all nodes Lc ++ LB) -> In b (Lc ++ LB)).
      { apply lb_sub_app. intros b Hb. eapply In_lb_remove_all; exact Hb. }
      split; [exact HH'|]. split; [congruence|]. split; [eapply mo_frame_trans; eassumption|].
      split; [intros b Hb; apply SUBL; eapply In_lb_remove_all; exact Hb|].
      split.
      { intros b Hb Hn. apply In_lb_remove_all_keep.
        - apply KEEP; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
        - intros C. apply Hn. rewrite map_app. apply in_or_app. right. rewrite map_fst_map_pair. exact C. }
      split.
      { intros b Hb Hin. rewrite map_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        - apply REL; [eapply In_lb_remove_all; exact Hb| exact Hin].
        - exfalso. rewrite map_fst_map_pair in Hin. exact (lb_remove_all_fst_notin _ _ _ NDL Hb Hin). }
      split; [eapply heap_presx_trans_pres; [exact HPX| eapply heap_pres_sp_mono; [exact HP| lia] | exact SUBL'] |].
      split; [eapply heap_pres_rw_cells; [exact HP| exact FR| apply client_range_stack; lia] |].
      split; [eapply heap_pres_rw_cells; [exact HP| exact CELLS| apply client_range_stack; lia] |].
      split; [exact MI'|]. split; [eapply statics_ok_heap_pres; [exact SO| exact HP| exact SW] | exact ST'].
    Qed.

    (* [comment removed for export] *)
    #[using="HFREE HLS SW DIMG HND"] Lemma heap_pres_of_presx_freed Lall mc moc (hc : HST usegs L HI) buf len m' SP :
      HEAP usegs L HI hc Lall mc moc -> In (buf, len) Lall -> alloc_ceiling <= SP ->
      heap_presx usegs L (lb_remove buf Lall) SP [(buf, buf + len)] mc m' ->
      heap_pres usegs L (lb_remove buf Lall) SP mc m'.
    Proof.
      intros HHc HIN HSP HPX a Ha Hc. apply HPX; [exact Ha| exact Hc|]. cbn [outside]. split; [|exact I].
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR AP]. pose proof (HND _ _ _ _ HHc) as NDL.
      rewrite Forall_forall in BR. destruct (BR _ HIN) as (_ & _ & _ & Bce & Bimg). cbn [fst snd] in Bce, Bimg.
      destruct (Z.lt_ge_cases a buf) as [|G1]; [lia|]. destruct (Z.lt_ge_cases a (buf + len)) as [G2|]; [|lia]. exfalso.
      destruct Hc as [Hs|[[Hd1 Hd2]|(b' & Hb' & Hr)]]; [lia| destruct DIMG; lia|].
      destruct b' as [B k]. cbn [fst snd] in Hr.
      assert (NE : buf <> B) by (intros E; exact (lb_remove_fst_neq _ _ _ NDL Hb' (eq_sym E))).
      pose proof (blocks_apart_in2 _ _ _ _ _ AP HIN (In_lb_remove _ _ _ Hb') NE). lia.
    Qed.
  End Inv.

  (* [comment removed for export] *)
  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LBo LB : list blk) (A : Z) (f : crt_own) (j : crt_junk) (lo : Z).
    Hypothesis HH : HEAP usegs L HI h (LBo ++ LB) m mo.
    Hypothesis OWN : crt_own_ok usegs PK m (LBo ++ LB) A f j.
    Hypothesis HAL : A mod 8 = 0.
    Hypothesis HA : 0 < A.
    Hypothesis AB : A + 744 <= 2 ^ 64.
    Hypothesis SUB : forall b, In b (crt_blocks f) -> In b LBo.
    Hypothesis SPA : bv_unsigned sp <= A.
    Hypothesis ATOP : A + 744 <= heap_top usegs L HI h.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis SLO : lo <= bv_unsigned sp - (32 + 256) - hl_stack L.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis SPTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.

    Let ND : List.NoDup (map fst (crt_blocks f)).
    Proof. ddestruct OWN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N). exact N. Qed.

    Let LOSP : lo <= bv_unsigned sp + -32. Proof. lia. Qed.
    Let CAC := cinv_after_chain sp ra s0 s1 s2 m mo h LBo LB A lo f j SUB ND SPA.
    Let CSI := cinv_seg_in sp ra s0 s1 s2 m mo h LBo LB A lo f j SUB ND.
    Let CCH := cinv_chain sp ra s0 s1 s2 m mo h LBo LB A lo f j SUB ND HH CEIL LOSP SPA.
    Let CSK := cinv_skip sp ra s0 s1 s2 m mo h LBo LB A lo f j.

    Notation CINV := (cinv sp ra s0 s1 s2 m mo h LBo LB A lo f j).
    Notation POST := (x509_crt_free_post2 usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LBo LB A f lo m mo).
    Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).

    (* [comment removed for export] *)
    Definition from (pc : Z) (P : list blk) : Prop :=
      forall Lc mc moc hc (x1 x5 x6 x7 : word) x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        CINV P Lc mc moc hc ->
        aevtM usegs moc POST
          (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None mc (seg_rom usegs)).

    (* [comment removed for export] *)
    Ltac goto L := let K := fresh "K" in pose proof L as K; unfold from in K; eapply K; clear K.

    Ltac cinv_open CI :=
      destruct CI as (HHc & HTc & MFc & SUBLc & KEEPc & RELc & HPXc & FR & CELLS & MIc & SOc & STc);
      unfold crt_cells in CELLS;
      cbn [pk0 co_ob co_rawlen co_rawp co_issuer_next co_issuer co_subject_next co_subject co_pkinfo co_pkctx co_pkowned
           co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts] in CELLS.

    #[using="HMSF HLS HA AB SPA ATOP CEIL SLO SP16 DHI SPR LOSP"] Lemma from_25290 : from 0x26ad0 (crt_blocks f).
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      zstep.                                   (* [comment removed for export] *)
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      apply rw_cells_blob in CELLS. cbn [cells_size csize Nat.add] in CELLS. change 744%nat with (Z.to_nat 744) in CELLS at 1.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut_evt; [exact MK | |].
      { eapply (U_platform_zeroize_spec L) with (A := A) (n := 744) (lo := lo);
          [ exact CELLS | lia | lia | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | rewrite USP; lia | exact SOc | exact HMSF | exact DHI | lia | exact MIc | reflexivity | reflexivity ]. }
      intros ms' PO. ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & CZ2 & ST2 & SO2).
      rewrite USP in MU2, ST2. change (Z.to_nat 744) with 744%nat in CZ2.
      replace (ret_pc (Z_to_bv 64 0x26ae0)) with (Z_to_bv 64 0x26ae0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (rw_cells_transport usegs _ mc m2 _ _ FR MU2 WM2 ltac:(cbn; lia)) as FR2. clear FR CELLS.
      assert (HH2 : HEAP usegs L HI hc (Lc ++ LB) m2 moc).
      { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact MU2 | exact WM2 | exact CEIL |].
        intros a Ha Hna. left. rewrite HTc. cbn [outside] in Hna. first [clear_disj; lia | lia]. }
      zstep. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by lia; lia].
      zstep. zstep. if_cases KZ; zify_cond KZ; [| exfalso; rewrite ?unsigned_lit in KZ by lia; lia].
      zstep. zstep. zstep. zstep. zstep. zstep.  (* [comment removed for export] *)
      release_frame FR2 ST2 (bv_unsigned sp).
      apply aevtM_done. unfold x509_crt_free_post2, CRT_SIZE.
      deexists 15. dexists m2, moc, hc, Lc.
      split; [reflexivity|]. split; [exact MI2|]. split; [exact SO2|]. split; [exact ST2|]. split; [exact MFc|].
      split; [exact HTc|]. split; [exact HH2|]. split; [exact SUBLc|]. split; [exact KEEPc|].
      split; [exact CZ2|].
      split.
      { eapply heap_presx_trans_presx; [eapply heap_presx_weaken; [exact HPXc| intros b Hb; exact Hb| lia| intros x Hx; cbn [outside] in *; split; [clear -Hx; lia| exact I]] | | intros b Hb; exact Hb].
        destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR _].
        eapply heap_presx_of_frame_munch; [exact MU2| exact WM2| exact BR| exact DHI|].
        intros a. cbn [outside]. lia. }
      intros HOB b Hb Hin. ddestruct (RELc b Hb Hin) as (E1 & E2 & E3). destruct HOB as [HOB|HOB]; [exact (E2 HOB)| exact (E3 HOB)].
    Qed.

    (* [comment removed for export] *)
    Definition SNAME (l : list Z) : list blk := map (fun a => (a, NAME_SIZE)) l.
    Definition SSEQ (l : list Z) : list blk := map (fun a => (a, SEQ_SIZE)) l.
    Definition P1 : list blk := co_pkowned f.
    Definition P2 : list blk := P1 ++ oblk (co_sigopts f) 8.
    Definition P3 : list blk := P2 ++ SNAME (co_issuer f).
    Definition P4 : list blk := P3 ++ SNAME (co_subject f).
    Definition P5 : list blk := P4 ++ SSEQ (co_eku f).
    Definition P6 : list blk := P5 ++ SSEQ (co_san f).
    Definition P7 : list blk := P6 ++ SSEQ (co_pol f).
    Definition P8 : list blk := P7 ++ SSEQ (co_akid f).

    Ltac crt_blocks_eq := unfold P8, P7, P6, P5, P4, P3, P2, P1, SNAME, SSEQ, crt_blocks; repeat rewrite <- app_assoc; cbn [map app]; reflexivity.

    #[using="HI PK sp m mo h LBo LB A j HH OWN HA SPR"] Lemma rawp_range : 0 <= co_rawp f < 2 ^ 64 /\ (co_rawp f <> 0 -> co_rawp f + co_rawlen f <= alloc_ceiling /\ 0 <= co_rawlen f).
    Proof.
      ddestruct OWN as (_ & _ & _ & _ & _ & _ & _ & RAW & _).
      pose proof alloc_ceiling_pos as ACP. pose proof alloc_ceiling_bounds as ACP'.
      destruct RAW as [E|(HIN & HLEN & _)]; [rewrite E; lia|].
      destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
      destruct (BR _ HIN) as (B0 & _ & _ & Bce & _). cbn [fst snd] in B0, Bce. lia.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI"] Lemma from_25278 : from 0x26ab8 P8.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof rawp_range as (RB0 & RBnz).
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *)
        goto from_25290. replace (crt_blocks f) with (P8 ++ oblk (co_rawp f) (co_rawlen f)) by crt_blocks_eq.
        apply cinv_skip; [exact CI0|]. intros b _ Hin. exfalso. revert Hin. unfold oblk. rewrite ?unsigned_lit in KR by lia.
        destruct (Z.eqb_spec (co_rawp f) 0); [intros []| lia]. }
      rewrite ?unsigned_lit in KR by lia.
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KO; zify_cond KO.
      { (* [comment removed for export] *)
        goto from_25290. replace (crt_blocks f) with (P8 ++ oblk (co_rawp f) (co_rawlen f)) by crt_blocks_eq.
        apply cinv_skip; [exact CI0|]. intros b _ Hin. unfold oblk in Hin. destruct (Z.eqb_spec (co_rawp f) 0) as [E0|NE0]; [destruct Hin|].
        cbn in Hin. destruct Hin as [Hin|[]]. split; [symmetry; exact Hin|]. split; [exact NE0|].
        intros EOB. rewrite EOB in KO. revert KO. clear. intros KO. exfalso.
        vm_compute in KO. lia. }
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      destruct (RBnz KR) as [RB1 RB2]. clear RBnz.
      assert (E8 : crt_blocks f = P8 ++ map (fun a => (a, co_rawlen f)) [co_rawp f] ++ []).
      { unfold P8, P7, P6, P5, P4, P3, P2, P1, SNAME, SSEQ, crt_blocks. unfold oblk at 2.
        destruct (Z.eqb_spec (co_rawp f) 0); [lia|]. repeat rewrite <- app_assoc. cbn [map app]. reflexivity. }
      assert (HIN : In (co_rawp f, co_rawlen f) (Lc ++ LB)).
      { apply in_or_app. left. eapply (CSI _ _ _ _ _ _ _ CI0 E8). left. reflexivity. }
      ddestruct OWN as (_ & _ & _ & _ & _ & _ & _ & RAW & _).
      destruct RAW as [R0|(_ & _ & RAWC)]; [lia|].
      assert (RAWC1 : rw_cells usegs mc (co_rawp f) [CB (Z.to_nat (co_rawlen f)) (cj_raw j)]).
      { eapply heap_presx_rw_cells; [exact HPXc| exact RAWC| |].
        - eapply client_range_block; [exact HIN| lia| cbn [cells_size csize Nat.add]; lia].
        - cbn [cells_size csize Nat.add disjoint_from]. lia. }
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply ZFREE with (buf := co_rawp f) (len := co_rawlen f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | right; split; [exact HIN| exact RAWC1] | lia
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | exact SOc | exact HMSF | reflexivity | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E & MI' & ST' & MF' & HT' & HH' & HPX' & SO').
      injection E; clear E; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HPX'.
      replace (ret_pc (Z_to_bv 64 0x26ad0)) with (Z_to_bv 64 0x26ad0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (heap_pres_of_presx_freed (Lc ++ LB) mc moc hc (co_rawp f) (co_rawlen f) m' (bv_unsigned sp + -32) HHc HIN ltac:(lia) HPX') as HP'.
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E8 HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25290. replace (crt_blocks f) with (P8 ++ map (fun a => (a, co_rawlen f)) [co_rawp f]) by (rewrite E8, app_nil_r; reflexivity).
      exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH"] Lemma from_25270 : from 0x26ab0 P7.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ CAKID) as NXB.
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (E : crt_blocks f = P7 ++ map (fun a => (a, SEQ_SIZE)) (co_akid f) ++ oblk (co_rawp f) (co_rawlen f)) by crt_blocks_eq.
      pose proof (CCH _ _ _ _ _ _ _ _ _ _ _ CI0 E CAKID ltac:(unfold SEQ_SIZE; lia)) as CH.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply SEQFREE with (a := co_akid_next f) (nodes := co_akid f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact CH | exact (seg_nodup_nodes f ND _ _ _ _ E)
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E0 & MI' & ST' & MF' & HT' & HH' & HP').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26ab8)) with (Z_to_bv 64 0x26ab8 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25278. exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH"] Lemma from_25268 : from 0x26aa8 P6.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ CPOL) as NXB.
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (E : crt_blocks f = P6 ++ map (fun a => (a, SEQ_SIZE)) (co_pol f) ++ (SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (CCH _ _ _ _ _ _ _ _ _ _ _ CI0 E CPOL ltac:(unfold SEQ_SIZE; lia)) as CH.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply SEQFREE with (a := co_pol_next f) (nodes := co_pol f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact CH | exact (seg_nodup_nodes f ND _ _ _ _ E)
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E0 & MI' & ST' & MF' & HT' & HH' & HP').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26ab0)) with (Z_to_bv 64 0x26ab0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25270. exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH"] Lemma from_25260 : from 0x26aa0 P5.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ CSAN) as NXB.
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (E : crt_blocks f = P5 ++ map (fun a => (a, SEQ_SIZE)) (co_san f) ++ (SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (CCH _ _ _ _ _ _ _ _ _ _ _ CI0 E CSAN ltac:(unfold SEQ_SIZE; lia)) as CH.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply SEQFREE with (a := co_san_next f) (nodes := co_san f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact CH | exact (seg_nodup_nodes f ND _ _ _ _ E)
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E0 & MI' & ST' & MF' & HT' & HH' & HP').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26aa8)) with (Z_to_bv 64 0x26aa8 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25268. exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH"] Lemma from_25258 : from 0x26a98 P4.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ CEKU) as NXB.
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (E : crt_blocks f = P4 ++ map (fun a => (a, SEQ_SIZE)) (co_eku f) ++ (SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (CCH _ _ _ _ _ _ _ _ _ _ _ CI0 E CEKU ltac:(unfold SEQ_SIZE; lia)) as CH.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply SEQFREE with (a := co_eku_next f) (nodes := co_eku f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact CH | exact (seg_nodup_nodes f ND _ _ _ _ E)
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E0 & MI' & ST' & MF' & HT' & HH' & HP').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26aa0)) with (Z_to_bv 64 0x26aa0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25260. exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SHALLOW SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH"] Lemma from_25250 : from 0x26a90 P3.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ CSUBJ) as NXB.
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (E : crt_blocks f = P3 ++ map (fun a => (a, NAME_SIZE)) (co_subject f) ++ (SSEQ (co_eku f) ++ SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (CCH _ _ _ _ _ _ _ _ _ _ _ CI0 E CSUBJ ltac:(unfold NAME_SIZE; lia)) as CH.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply SHALLOW with (a := co_subject_next f) (nodes := co_subject f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact CH | exact (seg_nodup_nodes f ND _ _ _ _ E)
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E0 & MI' & ST' & MF' & HT' & HH' & HP').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26a98)) with (Z_to_bv 64 0x26a98 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25258. exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SHALLOW SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH"] Lemma from_25248 : from 0x26a88 P2.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ CISS) as NXB.
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (E : crt_blocks f = P2 ++ map (fun a => (a, NAME_SIZE)) (co_issuer f) ++ (SNAME (co_subject f) ++ SSEQ (co_eku f) ++ SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (CCH _ _ _ _ _ _ _ _ _ _ _ CI0 E CISS ltac:(unfold NAME_SIZE; lia)) as CH.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply SHALLOW with (a := co_issuer_next f) (nodes := co_issuer f) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact CH | exact (seg_nodup_nodes f ND _ _ _ _ E)
          | rewrite USP; exact STc | rewrite USP; lia | exact CEIL
          | rewrite USP, HTc; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | exact DHI | exact TP | exact MIc | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E0 & MI' & ST' & MF' & HT' & HH' & HP').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26a90)) with (Z_to_bv 64 0x26a90 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25250. exact CI1.
    Qed.

    #[using="PK HFREE HMSF HLS SW DIMG HND SHALLOW SEQFREE ZFREE HH OWN HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH CSK"] Lemma from_25240 : from 0x26a80 P1.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof OWN as OWN'. ddestruct OWN' as (_ & _ & _ & _ & _ & _ & SIG & _).
      pose proof alloc_ceiling_pos as ACP.
      assert (SB : 0 <= co_sigopts f < 2 ^ 64).
      { destruct SIG as [E|(HIN & POS)]; [rewrite E; lia|].
        destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
        destruct (BR _ HIN) as (B0 & _ & _ & Bce & _). cbn [fst snd] in B0, Bce. lia. }
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      destruct (Z.eq_dec (co_sigopts f) 0) as [Z0|NZ].
      { (* [comment removed for export] *)
        rewrite Z0.
        eapply aevtM_cut_evt; [exact MK | eapply (heap_free_null usegs L HI); reflexivity |]. intros ms' ->.
        replace (ret_pc (Z_to_bv 64 0x26a88)) with (Z_to_bv 64 0x26a88 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
        goto from_25248. unfold P2. apply CSK; [exact CI0|]. rewrite Z0. unfold oblk. rewrite Z.eqb_refl. intros b _ []. }
      destruct SIG as [E0|(HIN0 & POS)]; [lia|].
      assert (E : crt_blocks f = P1 ++ map (fun a => (a, 8)) [co_sigopts f] ++ (SNAME (co_issuer f) ++ SNAME (co_subject f) ++ SSEQ (co_eku f) ++ SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))).
      { unfold P1, SNAME, SSEQ, crt_blocks. unfold oblk at 1.
        destruct (Z.eqb_spec (co_sigopts f) 0); [lia|]. repeat rewrite <- app_assoc. cbn [map app]. reflexivity. }
      assert (HIN : In (co_sigopts f, 8) (Lc ++ LB)).
      { apply in_or_app. left. eapply (CSI _ _ _ _ _ _ _ CI0 E). left. reflexivity. }
      eapply aevtM_cut.
      { eapply (heap_free usegs L HI) with (A := co_sigopts f) (n := 8) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | exact HIN | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
          | rewrite USP, HTc; lia | reflexivity ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo'
                      & E0 & MI' & ST' & MF' & HP' & h' & HT' & HH').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      replace (ret_pc (Z_to_bv 64 0x26a88)) with (Z_to_bv 64 0x26a88 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      pose proof (CAC _ _ _ _ _ _ _ _ _ _ _ CI0 E HH' HP' HT' MF' MI' ST') as CI1.
      goto from_25248.
      replace P2 with (P1 ++ map (fun a => (a, 8)) [co_sigopts f]); [exact CI1|].
      unfold P2, oblk. destruct (Z.eqb_spec (co_sigopts f) 0); [lia|]. reflexivity.
    Qed.

    (* [comment removed for export] *)
    #[using="PK HFREE HMSF HLS SW DIMG HND PKFREE SHALLOW SEQFREE ZFREE HH OWN HAL HA AB SUB SPA ATOP CEIL SLO SP16 SPTOP DHI TP SPR ND LOSP CAC CSI CCH CSK"] Lemma entry_walk : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      rw_cells usegs m A (crt_cells f j) ->
      stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m -> statics_ok usegs L m ->
      aevtM usegs mo POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26a44) fc None m (seg_rom usegs)).
    Proof.
      intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CELLS ST MI SO.
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof alloc_ceiling_pos as ACP.
      pose proof OWN as OWN'. ddestruct OWN' as (_ & _ & _ & _ & _ & _ & _ & _ & PKR & _).
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      assert (SOK : id (statics_ok usegs L m)) by exact SO.
      unfold crt_cells in CELLS.
      zstep. carve_frame 32%nat ST.            (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.              (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit, ?land_7_mod in KA by lia; lia|].
      zstep. zstep.                            (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      (* [comment removed for export] *)
      pose proof (statics_ok_munch usegs L _ m m0 SOK MU ltac:(intros a Ha Hna; cbn [outside]; split; [lia | exact I])) as SO0.
      assert (HH0 : HEAP usegs L HI h (LBo ++ LB) m0 mo).
      { eapply (heap_frame usegs L HI) with (SP := lo); [exact HH | exact CEIL | | exact WM].
        intros a Ha Hnc; apply MU; cbn [outside]; unfold wa; rewrite unsigned_lit by lia; split; [|exact I].
        intros C; apply Hnc; left; lia. }
      destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR AP].
      assert (PKR0 : pk_rep usegs PK m0 (LBo ++ LB) (A + 360) (co_pkinfo f) (co_pkctx f) (co_pkowned f)).
      { eapply (pk_rep_frame usegs PK); [exact PKR | exact MI | intros b Hb; exact (pk_rep_blocks usegs PK _ _ _ _ _ _ PKR b Hb) |].
        (intros a dd_H; ddestruct dd_H as (b & Hb & Hr)). pose proof (pk_rep_blocks usegs PK _ _ _ _ _ _ PKR b Hb) as HbL.
        rewrite Forall_forall in BR. ddestruct (BR b HbL) as (B0 & _ & _ & Bce & _).
        unfold wa. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [lia | exact I]. }
      change (rw_cells usegs m0 A (crt_pre f j ++ [C8 (Z_to_bv 64 (co_pkinfo f)); C8 (Z_to_bv 64 (co_pkctx f))] ++ crt_suf f j)) in CELLS.
      destruct (rw_cells_split3 usegs m0 A _ _ _ CELLS) as (C1 & CPK & C3). clear CELLS.
      rewrite crt_pre_size in CPK, C3. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (co_pkinfo f)); C8 (Z_to_bv 64 (co_pkctx f))])) with 16 in C3.
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply PKFREE with (LBo := LBo) (LB := LB) (PKA := A + 360) (info := co_pkinfo f) (ctx := co_pkctx f) (owned := co_pkowned f) (lo := lo) (h := h);
          [ exact HH0 | exact CPK | clear - HAL; Z.div_mod_to_equations; lia | exact PKR0
          | intros b Hb; apply SUB; unfold crt_blocks; apply in_or_app; left; exact Hb
          | rewrite USP; lia | lia
          | rewrite USP; exact ST | exact CEIL | rewrite USP; unfold PK_FREE_STACK; lia
          | rewrite USP; clear - SP16 SPR SLO HLS CEIL; Z.div_mod_to_equations; lia
          | rewrite USP; lia | exact DHI | exact MI | exact SO0 | exact TP | reflexivity ]. }
      intros ms' mo'x PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1 & h1 & LB1
                      & E0 & MI1 & SO1 & ST1 & MF1 & HT1 & HH1 & SUB1 & KEEP1 & PKZ & HPX1 & REL1).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HPX1.
      replace (A + 360 + 16) with (A + 376) in HPX1, C3 by lia.
      replace (ret_pc (Z_to_bv 64 0x26a80)) with (Z_to_bv 64 0x26a80 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      goto from_25240.
      (* [comment removed for export] *)
      destruct (heap_blocks usegs L HI _ _ _ _ HH1) as [BR1 _].
      split; [exact HH1|]. split; [exact HT1|]. split; [exact MF1|]. split; [exact SUB1|]. split; [exact KEEP1|].
      split; [intros b Hb Hin; exfalso; exact (REL1 b Hb Hin)|].
      split.
      { eapply heap_presx_trans_presx; [| eapply heap_presx_weaken; [exact HPX1| intros b Hb; exact Hb| lia| intros x Hx; exact Hx] | intros b Hb; exact Hb].
        eapply heap_presx_of_frame_munch; [exact MU| exact WM| exact BR1| exact DHI|].
        intros a. cbn [outside]. lia. }
      split; [eapply heap_presx_rw_cells; [exact HPX1| exact FR| apply client_range_stack; cbn; lia| cbn; lia] |].
      split.
      { rewrite crt_cells_pk0. apply rw_cells_join3; rewrite ?crt_pre_size.
        - eapply heap_presx_rw_cells; [exact HPX1| exact C1| apply client_range_stack; lia| rewrite crt_pre_size; cbn [disjoint_from]; lia].
        - exact PKZ.
        - change (Z.of_nat (cells_size [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])) with 16. replace (A + 360 + 16) with (A + 376) by lia.
          eapply heap_presx_rw_cells; [exact HPX1| exact C3| apply client_range_stack; lia| rewrite crt_suf_size; cbn [disjoint_from]; lia]. }
      split; [exact MI1|]. split; [exact SO1| exact ST1].
    Qed.
  End Body.

  #[using="HFREE HMSF HLS SW DIMG HND PKFREE SHALLOW SEQFREE ZFREE"] Theorem U_x509_crt_free_spec2 : x509_crt_free_stmt2 usegs L HI PK 0x26a44.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LBo LB A f j lo
           HH CA SUB SPA ATOP ST CEIL SLO SP16 SPTOP DHI MI SO TP ->.
    ddestruct CA as (CELLS & HAL & HA & AB & OWN). unfold X509_CRT_FREE_STACK, PK_FREE_STACK, CRT_SIZE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    eapply entry_walk; eassumption.
  Qed.

  #[using="HFREE HMSF HLS SW DIMG HND PKFREE SHALLOW SEQFREE ZFREE"] Theorem U_x509_crt_free_spec : x509_crt_free_stmt usegs L HI PK 0x26a44.
  Proof. apply x509_crt_free_stmt2_1. exact U_x509_crt_free_spec2. Qed.
End Walk.
