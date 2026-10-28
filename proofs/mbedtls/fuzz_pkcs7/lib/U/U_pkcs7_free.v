(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux CellsX Cells Mem Step Frame Tac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_x509_crl_free U_x509_crt_free. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts CrtStmts CrtRelStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import H3Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac al8_close k := exfalso; rewrite ?unsigned_lit in k by lia; change 7 with (Z.ones 3) in k; rewrite Z.land_ones in k by lia; change (2 ^ 3) with 8 in k; lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition p7cells (po : p7_own) (j : p7_junk) (ccs : list cell) (inext : Z) : list cell :=
  [C4 (pj_rawtag j); C4 (pj0 j); C8 (Z_to_bv 64 (po_rawlen po)); C8 (Z_to_bv 64 (po_rawp po)); CB 40 (pj1 j)]
  ++ ccs ++ [CB 8 (pj2 j); CB 416 (zeros 416); CB 8 (pj3 j)] ++ signer_cells inext (po_signers_next po) (pj_s0 j).

Lemma pkcs7_cells_eq po j : pkcs7_cells po j = p7cells po j (crt_cells (po_crt po) (pj_crt j)) (po_issuer0_next po).
Proof. reflexivity. Qed.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable PK : pk_class usegs.
  Hypothesis HFREE : hl_free L = 0x3fa98.
  Hypothesis HMSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis HLSU : hl_stack L <= 10000.     (* [comment removed for export] *)
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis PKFREE : pk_free_stmt2 usegs L HI PK 0x29c28.

  Let CRTFREE : x509_crt_free_stmt usegs L HI PK 0x26a44 := U_x509_crt_free_spec L HI PK HFREE HMSF HLS SW DIMG HND PKFREE.
  Let CRLFREE : x509_crl_free_stmt usegs L 0x3eed4 := U_x509_crl_free_spec L HI HFREE HMSF.

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB LBn : list blk) (A : Z) (po : p7_own) (pj : p7_junk) (lo : Z).
    Hypothesis HH : HEAP usegs L HI h (LBn ++ LB) m mo.
    Hypothesis LIVE : pkcs7_live usegs PK m (LBn ++ LB) A po pj.
    Hypothesis NDn : List.NoDup LBn.
    Hypothesis IFF : forall b, In b LBn <-> In b (p7_blocks po).
    Hypothesis SPA : bv_unsigned sp <= A.
    Hypothesis ATOP : A + 1440 <= heap_top usegs L HI h.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis SLO : lo <= bv_unsigned sp - PKCS7_FREE_STACK.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis SPTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.

    Let ND : List.NoDup (map fst (p7_blocks po)).
    Proof. ddestruct LIVE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N). exact N. Qed.
    Let SUB : forall b, In b (p7_blocks po) -> In b LBn.
    Proof. intros b Hb. apply (proj2 (IFF b)). exact Hb. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L27904923538.5500000;S2sp2lo3SLO". (* [comment removed for export] *)
    Let LOSP : lo <= bv_unsigned sp + -48. Proof. unfold PKCS7_FREE_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L39555328978.5600000;S2sp2lo3SLO". (* [comment removed for export] *)
    Let SLO60 : lo <= bv_unsigned sp - 20000. Proof. unfold PKCS7_FREE_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Notation POST := (pkcs7_free_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB A lo m mo).
    Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
    Notation X0 := [(A, A + 1440)].

    (* [comment removed for export] *)
    Definition pinv (D : list blk) (cs : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST usegs L HI) : Prop :=
      HEAP usegs L HI hc (Lc ++ LB) mc moc
      /\ heap_top usegs L HI hc = heap_top usegs L HI h
      /\ mo_frame mo moc
      /\ (forall b, In b Lc -> In b LBn)
      /\ (forall b, In b LBn -> ~ In (fst b) (map fst D) -> In b Lc)
      /\ heap_presx usegs L (Lc ++ LB) (bv_unsigned sp) X0 m mc
      /\ (exists fj, rw_cells usegs mc (bv_unsigned sp + -48) [CB 8 fj; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      /\ rw_cells usegs mc A cs
      /\ mem_inv usegs mc /\ statics_ok usegs L mc /\ stk usegs mc lo (bv_unsigned sp + -48).

    Ltac pinv_open CI :=
      destruct CI as (HHc & HTc & MFc & SUBLc & KEEPc & HPXc & [fj FR] & CELLS & MIc & SOc & STc).

    
    #[using="PK pj LIVE IFF ND SUB"] Lemma pinv_seg_in D S R cs Lc mc moc hc :
      pinv D cs Lc mc moc hc -> p7_blocks po = D ++ S ++ R -> forall b, In b S -> In b Lc.
    Proof.
      intros CI E b Hb. ddestruct CI as (_ & _ & _ & _ & KEEP & _).
      apply KEEP; [apply SUB; rewrite E; apply in_or_app; right; apply in_or_app; left; exact Hb|].
      pose proof ND as N. rewrite E, !map_app in N.
      apply (NoDup_app_notin_l _ _ (fst b) N). apply in_or_app. left. apply in_map. exact Hb.
    Qed.

    #[using="Type"] Lemma pinv_skip D S cs Lc mc moc hc : pinv D cs Lc mc moc hc -> pinv (D ++ S) cs Lc mc moc hc.
    Proof.
      intros CI. ddestruct CI as (C1 & C2 & C3 & C4 & KEEP & C6).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj _ C6))))).
      intros b Hb Hn. apply KEEP; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
    Qed.

    
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2774356933.95 L49640974865.95000004008S2spS2sp". (* [comment removed for export] *)
    #[using="Type"] Lemma pinv_after D S cs cs' Lc L' mc moc hc m' mo' (h' : HST usegs L HI) X' :
      pinv D cs Lc mc moc hc ->
      (forall b, In b L' -> In b Lc) -> (forall b, In b Lc -> ~ In (fst b) (map fst S) -> In b L') ->
      HEAP usegs L HI h' (L' ++ LB) m' mo' -> heap_top usegs L HI h' = heap_top usegs L HI hc -> mo_frame moc mo' ->
      heap_presx usegs L (L' ++ LB) (bv_unsigned sp + -48) X' mc m' -> sub_fp X' X0 -> disjoint_from X' (bv_unsigned sp + -48) 48 ->
      rw_cells usegs m' A cs' -> mem_inv usegs m' -> statics_ok usegs L m' -> stk usegs m' lo (bv_unsigned sp + -48) ->
      pinv (D ++ S) cs' L' m' mo' h'.
    Proof.
      intros CI HS HK HH' HT' MF' HP' XS XD C' MI' SO' ST'.
      ddestruct CI as (C1 & C2 & C3 & SUBL & KEEP & HPX & [fj FR] & CELLS & MI & SO & ST).
      assert (SUBL' : forall b, In b (L' ++ LB) -> In b (Lc ++ LB)) by (apply lb_sub_app; exact HS).
      split; [exact HH'|]. split; [congruence|]. split; [eapply mo_frame_trans; eassumption|].
      split; [intros b Hb; apply SUBL, HS, Hb|].
      split.
      { intros b Hb Hn. apply HK.
        - apply KEEP; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
        - intros C. apply Hn. rewrite map_app. apply in_or_app. right. exact C. }
      split; [eapply heap_presx_trans_presx; [exact HPX| eapply heap_presx_weaken; [exact HP'| intros b Hb; exact Hb| lia| exact XS] | exact SUBL'] |].
      split; [exists fj; eapply heap_presx_rw_cells; [exact HP'| exact FR| apply client_range_stack; lia| cbn [cells_size csize Nat.add]; exact XD] |].
      split; [exact C'|]. split; [exact MI'|]. split; [exact SO'| exact ST'].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17477028091.8000000:S2sp1A3SPA". (* [comment removed for export] *)
    #[using="PK SW pj LIVE IFF SPA ND SUB"] Lemma pinv_after_free D a n R cs Lc mc moc hc m' mo' (h' : HST usegs L HI) :
      pinv D cs Lc mc moc hc -> p7_blocks po = D ++ [(a, n)] ++ R ->
      HEAP usegs L HI h' (lb_remove a (Lc ++ LB)) m' mo' ->
      heap_pres usegs L (lb_remove a (Lc ++ LB)) (bv_unsigned sp + -48) mc m' ->
      heap_top usegs L HI h' = heap_top usegs L HI hc -> mo_frame moc mo' -> mem_inv usegs m' ->
      stk usegs m' lo (bv_unsigned sp + -48) ->
      pinv (D ++ [(a, n)]) cs (lb_remove a Lc) m' mo' h'.
    Proof.
      intros CI E HH' HP HT' MF' MI' ST'.
      assert (HINa : In a (map fst Lc)).
      { replace a with (fst (a, n)) by reflexivity. apply in_map. eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI E). left. reflexivity. }
      rewrite (lb_remove_app_l a Lc LB HINa) in HH', HP.
      pose proof CI as CI'. ddestruct CI' as (_ & _ & _ & _ & _ & _ & _ & CELLS & _ & SO & _).
      eapply pinv_after with (X' := []); [exact CI| | | exact HH'| exact HT'| exact MF'| apply heap_presx_of_pres; exact HP| intros x _; exact I| exact I
        | eapply heap_pres_rw_cells; [exact HP| exact CELLS| apply client_range_stack; lia] | exact MI'| eapply statics_ok_heap_pres; [exact SO| exact HP| exact SW] | exact ST'].
      - intros b Hb. eapply In_lb_remove. exact Hb.
      - intros b Hb Hn. apply In_lb_remove_keep'; [exact Hb|]. intros C. apply Hn. left. symmetry. exact C.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L17472457818.101L3196848528.101 L5468055284.86  L5744835943.103 L59310683405.105L59310683405.106L59314873579.105L59314873579.11100000:01101T01]02G02l03N03iS2sp1A3SPAS1L2sp1A2lo3SPA3SPR5SLO601a1n2cs3wlo3whi4HWhi3Bce5CEIL'S2sp3SPR1a1n3wlo3whi4HWlo4HWhi1x2HxS2sp1x2HxS1L2sp2lo3SPR5SLO601a1n3Bce5CEIL'1x2Hs3HinS1L3DI13DI22sp3SPR1a1n4Bimg1x3Hd13HinS1L3DI13DI22sp3SPR1a1n4Bimg1x2Hx1HS2sp3SPR1a1n1x1B1k2Hr3Hin1H". (* [comment removed for export] *)
    #[using="PK HFREE HMSF HLS SW DIMG HND PKFREE pj LIVE IFF SPA CEIL SLO SPR ND SUB LOSP SLO60"] Lemma pinv_after_store_free D a n R cs Lc mc moc hc wlo whi m0 m' mo' (h' : HST usegs L HI) :
      pinv D cs Lc mc moc hc -> p7_blocks po = D ++ [(a, n)] ++ R ->
      munch [(wlo, whi)] mc m0 -> wmono usegs mc m0 -> a <= wlo -> whi <= a + n ->
      HEAP usegs L HI h' (lb_remove a (Lc ++ LB)) m' mo' ->
      heap_pres usegs L (lb_remove a (Lc ++ LB)) (bv_unsigned sp + -48) m0 m' ->
      heap_top usegs L HI h' = heap_top usegs L HI hc -> mo_frame moc mo' -> mem_inv usegs m' ->
      stk usegs m' lo (bv_unsigned sp + -48) ->
      pinv (D ++ [(a, n)]) cs (lb_remove a Lc) m' mo' h'.
    Proof.
      intros CI E MU WM HWlo HWhi HH' HP HT' MF' MI' ST'.
      assert (HW : forall x, ~ outside [(wlo, whi)] x -> a <= x < a + n) by (intros x Hx; cbn [outside] in Hx; lia).
      assert (HINb : In (a, n) Lc) by (eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI E); left; reflexivity).
      assert (HINa : In a (map fst Lc)) by (replace a with (fst (a, n)) by reflexivity; apply in_map; exact HINb).
      rewrite (lb_remove_app_l a Lc LB HINa) in HH', HP.
      pose proof CI as CI'. ddestruct CI' as (HHc & _ & _ & _ & _ & _ & _ & CELLS & _ & SO & _).
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR BA].
      pose proof (proj1 (Forall_forall _ _) BR (a, n) (in_or_app _ _ _ (or_introl HINb))) as (Ba0 & _ & Bn0 & Bce & Bimg). cbn [fst snd] in Ba0, Bn0, Bce, Bimg.
      pose proof LOSP as LOSP'. pose proof CEIL as CEIL'. destruct DIMG as [DI1 DI2].
      (* [comment removed for export] *)
      assert (HPX0 : heap_presx usegs L (lb_remove a Lc ++ LB) (bv_unsigned sp + -48) [] mc m0).
      { intros x Hx Hc _. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
        destruct (outside_dec [(wlo, whi)] x) as [Ho|Hno]; [exact Ho| exfalso]. pose proof (HW x Hno) as Hin.
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        assert (Hb0 : In b (Lc ++ LB)).
        { apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; eapply In_lb_remove; exact Hb| right; exact Hb]. }
        destruct b as [B k]. cbn [fst snd] in Hr.
        assert (NE : a <> B).
        { intros ->. rewrite <- (lb_remove_app_l B Lc LB HINa) in Hb.
          exact (lb_remove_fst_neq _ _ _ (HND _ _ _ _ HHc) Hb eq_refl). }
        destruct (blocks_apart_in2 _ _ _ _ _ BA (in_or_app _ _ _ (or_introl HINb)) Hb0 NE); lia. }
      eapply pinv_after with (X' := []); [exact CI| | | exact HH'| exact HT'| exact MF'
        | eapply heap_presx_trans; [exact HPX0| apply heap_presx_of_pres; exact HP] | intros x _; exact I| exact I
        | eapply heap_pres_rw_cells; [exact HP| eapply rw_cells_transport; [exact CELLS| exact MU| exact WM|] | apply client_range_stack; lia]
        | exact MI'
        | eapply statics_ok_heap_pres; [eapply statics_ok_munch; [exact SO| exact MU|] | exact HP| exact SW] | exact ST'].
      - intros b Hb. eapply In_lb_remove. exact Hb.
      - intros b Hb Hn. apply In_lb_remove_keep'; [exact Hb|]. intros C. apply Hn. left. symmetry. exact C.
      - (* [comment removed for export] *)
        cbn [disjoint_from]. lia.
      - intros x Hx _. destruct (outside_dec [(wlo, whi)] x) as [Ho|Hno]; [exact Ho| exfalso]. pose proof (HW x Hno). lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    #[using="Type"] Lemma pinv_bb D cs Lc mc moc hc : pinv D cs Lc mc moc hc -> blocks_below (Lc ++ LB) alloc_ceiling.
    Proof. intros CI. destruct CI as (HHc & _). eapply blocks_below_of_HEAP. exact HHc. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L14975046107.5700000NS1L2sp1A2lo3SPA4CEIL3SPR5SLO60". (* [comment removed for export] *)
    #[using="sp lo SPA CEIL SLO SPR SLO60"] Lemma fpX : fp_above X0 alloc_ceiling.
    Proof. constructor; [cbn; lia| constructor]. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    
    
    Ltac fix_ret pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L10408852475.99 L11741095640.101L24931808778.100L26890167246.122L26924648792.101L27915413305.100L31924382914.99 L35837421921.99 L43654564952.101L51709126249.99 L54394091819.124L5451250215.99  L59499841752.101L65202436964.124L7510805464.101 00000700>00J00Q00X00g01701^01e01l02Y02h02o03T03[S2sp2csS2sp2csS2sp1A2cs2HAS2sp2csS2sp2csS2sp2lo4LOSP2csS2sp1A2lo3SPA2csS1L3DHI2sp1A2lo3SPA3SPR2cs5CEILn6SLO60'S2sp2csS2sp2csS1L2HI2sp1h1A2lo3SPA4ATOP3SPR2cs6SLO60'1a3HnaS2sp2lo4LOSP2csS2sp2csS1L2sp1A2lo3SPA3SPR2cs5CEILn6SLO60'1aS2sp2cs". (* [comment removed for export] *)
    #[using="PK HMSF DHI po pj LIVE SPA ATOP CEIL SLO SP16 SPR LOSP SLO60"] Lemma tail_1d77c : forall D cs Lc mc moc hc (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
      pinv D cs Lc mc moc hc -> Z.of_nat (cells_size cs) = 1440 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1dd2c) fc None mc (seg_rom usegs)).
    Proof.
      intros D cs Lc mc moc hc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 CI SZ. pinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof LOSP as LOSP'. pose proof SLO60 as SLO60'.
      zstep. zstep.                            (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.       (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      release_frame FR STc (bv_unsigned sp).
      apply rw_cells_blob in CELLS. rewrite <- (Nat2Z.id (cells_size cs)) in CELLS. rewrite SZ in CELLS.
      eapply aevtM_cut_evt; [exact MK | |].
      { eapply (U_platform_zeroize_spec L) with (A := A) (n := 1440) (lo := lo);
          [ exact CELLS | lia | ddestruct LIVE as (_ & _ & HA & _); lia | exact STc | lia | exact CEIL
          | exact SP16 | lia | exact SOc | exact HMSF | exact DHI | lia | exact MIc | reflexivity | reflexivity ]. }
      intros ms' PO. ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & CZ2 & ST2 & SO2).
      change (Z.to_nat 1440) with 1440%nat in CZ2.
      assert (HH2 : HEAP usegs L HI hc (Lc ++ LB) m2 moc).
      { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact MU2 | exact WM2 | exact CEIL |].
        intros a Ha Hna. left. rewrite HTc. cbn [outside] in Hna. first [clear_disj; lia | lia]. }
      apply aevtM_done. unfold pkcs7_free_post, P_pkcs7_top.PKCS7_SIZE.
      deexists 15. dexists m2, moc, hc, Lc.
      split; [reflexivity|]. split; [exact MI2|]. split; [exact SO2|]. split; [exact ST2|]. split; [exact MFc|].
      split; [exact HTc|]. split; [exact CZ2|]. split; [exact HH2|].
      eapply heap_presx_trans_presx; [eapply heap_presx_weaken; [exact HPXc| intros b Hb; apply in_or_app; right; exact Hb| lia| intros x Hx; exact Hx] | | intros b Hb; exact Hb].
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR _]. apply Forall_app in BR. destruct BR as [_ BR].
      eapply heap_presx_of_frame_munch; [exact MU2| exact WM2| exact BR| exact DHI|].
      intros a. cbn [outside]. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Ltac goto L := let K := fresh "K" in pose proof L as K; eapply K; clear K.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L12286330749.122L14790993950.121L24748059563.146L29626922815.122L46425565324.149L47028033785.122L47699148558.122L51283986245.122L63528079485.12200000i01b02602J02b03603J04804YS1L2sp1A2lo3SPA3SPR3cur5CEILn6SLO60'4HPOS3pre2nx4post3BceS1L2sp2lo3SPR3cur5CEILn9ACB_CEILn6SLO60'4HPOS3pre2nx4postS2sp3cur3pre2nx4postS2sp3cur3pre2nx4postS2sp3cur3pre2nx4post3NXBS2sp3cur3pre2nx4postS2sp3cur3pre2nx4postS1L4HLSU2sp2lo3SPR3cur6SLO60'4HPOS3pre2nx4postS1L2HI2sp1h5SPTOP3cur3pre2nx4post". (* [comment removed for export] *)
    #[using="PK HFREE HLSU SW pj LIVE IFF SPA CEIL SLO SPTOP TP SPR ND SUB LOSP SLO60"] Lemma loopC : forall (asg nxt : Z) (R : list blk) cs (names : list Z) (cur : Z) D Lc mc moc hc
                         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      names <> [] -> name_chain usegs (fun _ => True) m (LBn ++ LB) cur names ->
      p7_blocks po = D ++ SNAME names ++ R ->
      pinv D cs Lc mc moc hc ->
      (forall Lc' mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word),
          pinv (D ++ SNAME names) cs Lc' mc' moc' hc' ->
          aevtM usegs moc' POST
            (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 A) (Z_to_bv 64 asg) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 nxt) y19 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x1dd50) fc None mc' (seg_rom usegs))) ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 asg) (Z_to_bv 64 cur) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nxt) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1dd78) fc None mc (seg_rom usegs)).
    Proof.
      intros asg nxt R cs names. induction names as [|n1 rest IH];
        intros cur D Lc mc moc hc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 HNE HC E CI K; [congruence|].
      pose proof CI as CI0. pinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof LOSP as LOSP'. pose proof SLO60 as SLO60'.
      destruct (chain_uncons usegs _ _ _ _ _ _ _ _ HC) as (<- & _ & HAL & HPOS & pre & nx & post & H1 & H2 & HNODE & _ & HNX0 & HC').
      unfold NAME_NEXT in HNX0. unfold NAME_SIZE in H2.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite H2 in NB.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HC') as NXB.
      assert (HINc : In (cur, NAME_SIZE) Lc).
      { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 E). unfold SNAME. cbn [map]. left. reflexivity. }
      unfold NAME_SIZE in HINc.
      pose proof (pinv_bb _ _ _ _ _ _ CI0) as BB. destruct (BB _ (in_or_app _ _ _ (or_introl HINc))) as [_ Bce]. cbn [fst snd] in Bce.
      assert (HNX : rw_cells usegs mc (cur + 48) [C8 (Z_to_bv 64 nx)]).
      { eapply heap_presx_rw_cells; [exact HPXc| exact HNX0| |].
        - eapply client_range_block; [apply in_or_app; left; exact HINc| lia| cbn [cells_size csize Nat.add]; lia].
        - cbn [cells_size csize Nat.add disjoint_from]. lia. }
      clear HNX0 HNODE.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
      pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply (heap_free usegs L HI) with (A := cur) (n := 64) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | apply in_or_app; left; exact HINc | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
          | rewrite USP, HTc; lia | reflexivity ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo'
                      & E0 & MI' & ST' & MF' & HP' & h' & HT' & HH').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      fix_ret 0x1dd88.
      assert (E1 : p7_blocks po = D ++ [(cur, 64)] ++ (SNAME rest ++ R)) by (rewrite E; unfold SNAME, NAME_SIZE; cbn [map app]; reflexivity).
      pose proof (pinv_after_free _ _ _ _ _ _ _ _ _ _ _ _ CI0 E1 HH' HP' HT' MF' MI' ST') as CI1.
      clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH') as MK.
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KN by lia.
        destruct (chain_nonnull usegs _ _ _ _ _ _ _ HC' KN) as (a2 & rest2 & ER).
        eapply (IH nx (D ++ [(cur, 64)])); [rewrite ER; congruence| exact HC'| rewrite E1, <- app_assoc; reflexivity| exact CI1|].
        intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 CI'.
        eapply K. rewrite <- app_assoc in CI'. exact CI'.
      - rewrite ?unsigned_lit in KN by lia.
        pose proof (chain_null_inv usegs _ _ _ _ _ _ ltac:(rewrite <- KN; exact HC')) as ER. subst rest.
        zstep.                                 (* [comment removed for export] *)
        eapply K. exact CI1.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L12286330749.122L14790993950.121L29626922815.122L45509373739.146L46425565324.149L47028033785.122L47699148558.122L51283986245.122L63528079485.12200000i01b02602J02b03603J04804YS1L2sp1A2lo3SPA3SPR3cur5CEILn6SLO60'4HPOS3pre2nx4post3BceS1L2sp2lo3SPR3cur5CEILn9ACB_CEILn6SLO60'4HPOS3pre2nx4postS2sp3cur3pre2nx4postS2sp3cur3pre2nx4postS2sp3cur3pre2nx4post3NXBS2sp3cur3pre2nx4postS2sp3cur3pre2nx4postS1L4HLSU2sp2lo3SPR3cur6SLO60'4HPOS3pre2nx4postS1L2HI2sp1h5SPTOP3cur3pre2nx4post". (* [comment removed for export] *)
    #[using="PK HFREE HLSU SW pj LIVE IFF SPA CEIL SLO SPTOP TP SPR ND SUB LOSP SLO60"] Lemma loopA : forall (sgn : Z) (R : list blk) cs (names : list Z) (cur : Z) D Lc mc moc hc
                         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
      names <> [] -> name_chain usegs (fun _ => True) m (LBn ++ LB) cur names ->
      p7_blocks po = D ++ SNAME names ++ R ->
      pinv D cs Lc mc moc hc ->
      (forall Lc' mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word),
          pinv (D ++ SNAME names) cs Lc' mc' moc' hc' ->
          aevtM usegs moc' POST
            (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 A) (Z_to_bv 64 sgn) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x1dd24) fc None mc' (seg_rom usegs))) ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 sgn) (Z_to_bv 64 cur) x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1dd0c) fc None mc (seg_rom usegs)).
    Proof.
      intros sgn R cs names. induction names as [|n1 rest IH];
        intros cur D Lc mc moc hc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 HNE HC E CI K; [congruence|].
      pose proof CI as CI0. pinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof LOSP as LOSP'. pose proof SLO60 as SLO60'.
      destruct (chain_uncons usegs _ _ _ _ _ _ _ _ HC) as (<- & _ & HAL & HPOS & pre & nx & post & H1 & H2 & HNODE & _ & HNX0 & HC').
      unfold NAME_NEXT in HNX0. unfold NAME_SIZE in H2.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite H2 in NB.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HC') as NXB.
      assert (HINc : In (cur, NAME_SIZE) Lc).
      { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 E). unfold SNAME. cbn [map]. left. reflexivity. }
      unfold NAME_SIZE in HINc.
      pose proof (pinv_bb _ _ _ _ _ _ CI0) as BB. destruct (BB _ (in_or_app _ _ _ (or_introl HINc))) as [_ Bce]. cbn [fst snd] in Bce.
      assert (HNX : rw_cells usegs mc (cur + 48) [C8 (Z_to_bv 64 nx)]).
      { eapply heap_presx_rw_cells; [exact HPXc| exact HNX0| |].
        - eapply client_range_block; [apply in_or_app; left; exact HINc| lia| cbn [cells_size csize Nat.add]; lia].
        - cbn [cells_size csize Nat.add disjoint_from]. lia. }
      clear HNX0 HNODE.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
      pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply (heap_free usegs L HI) with (A := cur) (n := 64) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | apply in_or_app; left; exact HINc | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
          | rewrite USP, HTc; lia | reflexivity ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo'
                      & E0 & MI' & ST' & MF' & HP' & h' & HT' & HH').
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
      fix_ret 0x1dd1c.
      assert (E1 : p7_blocks po = D ++ [(cur, 64)] ++ (SNAME rest ++ R)) by (rewrite E; unfold SNAME, NAME_SIZE; cbn [map app]; reflexivity).
      pose proof (pinv_after_free _ _ _ _ _ _ _ _ _ _ _ _ CI0 E1 HH' HP' HT' MF' MI' ST') as CI1.
      clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH') as MK.
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KN by lia.
        destruct (chain_nonnull usegs _ _ _ _ _ _ _ HC' KN) as (a2 & rest2 & ER).
        eapply (IH nx (D ++ [(cur, 64)])); [rewrite ER; congruence| exact HC'| rewrite E1, <- app_assoc; reflexivity| exact CI1|].
        intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 CI'.
        eapply K. rewrite <- app_assoc in CI'. exact CI'.
      - rewrite ?unsigned_lit in KN by lia.
        pose proof (chain_null_inv usegs _ _ _ _ _ _ ltac:(rewrite <- KN; exact HC')) as ER. subst rest.
        eapply K. exact CI1.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Ltac blocks_eq E := rewrite E; cbn [signer_blocks fst snd]; unfold SNAME, SIGNER_SIZE, NAME_SIZE; repeat rewrite <- app_assoc; cbn [map app]; reflexivity.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L14681525816.119L14694013942.146L14790994742.151L19847676908.152L22720121737.152L24425476304.128L38957508073.146L38970257447.119L41659498382.153L48577939243.176L51283986245.152L53517077152.119L5453391314.176 L5734691707.176 L63528079485.152L6393052521.125 L64982566814.119L64986665552.14600000900E01602003003C03O03X03j04604\04h05405@05Y05o06]07NS2sp2cs1aS2sp2cs1a2NBS1L2sp2lo3SPR2cs1a5CEILn9ACB_CEILn6SLO60'4HPOS2NBS1L2sp2lo3SPR2cs1a5CEILn6SLO60'4HPOS3Bce2NB2HB5Ha_st5Hl_stS1L2sp1A2lo3SPA3SPR2cs1a5CEILn6SLO60'4HPOS3Bce2NB2HB5Ha_st5Hl_stS2sp2cs3nxt1a2NB2B2S2sp2cs1a2NBS2sp2cs1aS2sp2cs1a2NB1x3HnxS2sp2cs1a2NBS1L4HLSU2sp2lo3SPR2cs1a6SLO60'4HPOS2NBS2sp2cs1a2NBS2sp2cs1a2NBS2sp2cs1a2NBS1L2HI2sp1h5SPTOP2cs1a2NBS2sp2cs1a5inext2NB3INBS1L2sp1A2lo3SPA3SPR2cs1a5CEILn6SLO60'4HPOS3BceS1L2sp1A2lo3SPA3SPR2cs1a5CEILn6SLO60'4HPOS3Bce2NB". (* [comment removed for export] *)
    #[using="PK HFREE HMSF HLS HLSU SW DIMG DHI HND PKFREE pj LIVE IFF SPA ATOP CEIL SLO SP16 SPTOP TP SPR ND SUB LOSP SLO60"] Lemma loopB : forall cs, Z.of_nat (cells_size cs) = 1440 ->
      forall (sg : list (Z * list Z)) (a : Z) D Lc mc moc hc
             (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
      sg <> [] -> signer_chain usegs m (LBn ++ LB) a sg ->
      p7_blocks po = D ++ signer_blocks sg ++ [] ->
      pinv D cs Lc mc moc hc ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1dd64) fc None mc (seg_rom usegs)).
    Proof.
      intros cs SZ sg. induction sg as [|[a' ns] r IH];
        intros a D Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 HNE HC E CI; [congruence|].
      pose proof CI as CI0. pinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof LOSP as LOSP'. pose proof SLO60 as SLO60'.
      destruct (signer_chain_uncons usegs _ _ _ _ _ _ HC) as (<- & _ & HAL & HPOS & inext & nxt & sj & HNODE0 & HN0 & HC').
      assert (Ea : p7_blocks po = D ++ (SNAME ns ++ [(a, 200)]) ++ (signer_blocks r ++ [])) by blocks_eq E.
      assert (HINc : In (a, 200) Lc).
      { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 Ea). apply in_or_app. right. left. reflexivity. }
      pose proof (pinv_bb _ _ _ _ _ _ CI0) as BB. destruct (BB _ (in_or_app _ _ _ (or_introl HINc))) as [_ Bce]. cbn [fst snd] in Bce.
      assert (HNODE : rw_cells usegs mc a (signer_cells inext nxt sj)).
      { eapply heap_presx_rw_cells; [exact HPXc| exact HNODE0| |].
        - eapply client_range_block; [apply in_or_app; left; exact HINc| lia| cbn [cells_size csize Nat.add signer_cells]; lia].
        - cbn [cells_size csize Nat.add signer_cells disjoint_from]. lia. }
      unfold signer_cells in HNODE.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. cbn [cells_size csize Nat.add] in NB.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HN0) as INB.
      assert (NXB : 0 <= nxt < 2 ^ 64).
      { destruct r as [|[a2 ns2] r2]; [cbn in HC'; subst nxt; lia|].
        destruct (signer_chain_uncons usegs _ _ _ _ _ _ HC') as (<- & _ & _ & _ & i2 & n2 & j2 & HR2 & _).
        pose proof (rw_cells_bound _ _ _ _ HR2) as B2. cbn [cells_size csize Nat.add signer_cells] in B2. lia. }
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (K1710 : forall Lc' mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word),
          pinv (D ++ SNAME ns) cs Lc' mc' moc' hc' ->
          aevtM usegs moc' POST
            (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 A) (Z_to_bv 64 a) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 nxt) y19 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x1dd50) fc None mc' (seg_rom usegs))).
      { intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 CI'.
        pose proof CI' as CI1. clear HHc HTc MFc SUBLc KEEPc HPXc FR CELLS MIc SOc STc MK fj HNODE. pinv_open CI'.
        pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK.
        assert (E2 : p7_blocks po = (D ++ SNAME ns) ++ [(a, 200)] ++ (signer_blocks r ++ [])) by blocks_eq E.
        assert (HINc' : In (a, 200) Lc').
        { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI1 E2). left. reflexivity. }
        assert (HNODE : rw_cells usegs mc' a (signer_cells inext nxt sj)).
        { eapply heap_presx_rw_cells; [exact HPXc| exact HNODE0| |].
          - eapply client_range_block; [apply in_or_app; left; exact HINc'| lia| cbn [cells_size csize Nat.add signer_cells]; lia].
          - cbn [cells_size csize Nat.add signer_cells disjoint_from]. lia. }
        unfold signer_cells in HNODE.
        pose proof (munch_refl [(a + 80, a + 88)] mc') as MU. pose proof (wmono_refl usegs mc') as WM.
        zstep.                                 (* [comment removed for export] *)
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
        assert (HH0 : HEAP usegs L HI hc' (Lc' ++ LB) m0 moc').
        { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact MU | exact WM | exact CEIL |].
          intros x Hx Hnx. right. right. exists (a, 200). split; [apply in_or_app; left; exact HINc'|].
          cbn [outside] in Hnx. cbn [fst snd]. lia. }
        zstep.                                 (* [comment removed for export] *)
        zstep.                                 (* [comment removed for export] *)
        replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
        pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
        eapply aevtM_cut.
        { eapply (heap_free usegs L HI) with (A := a) (n := 200) (lo := lo) (h := hc') (LB := Lc' ++ LB);
            [ exact HH0 | apply in_or_app; left; exact HINc' | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
            | rewrite USP, HTc; lia | reflexivity ]. }
        intros ms' mo'x PO. unfold call_post in PO.
        ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo'
                        & E0 & MI' & ST' & MF' & HP' & h' & HT' & HH').
        injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST', HP'.
        fix_ret 0x1dd5c.
        pose proof (pinv_after_store_free _ _ _ _ _ _ _ _ _ (a + 80) (a + 88) _ _ _ _ CI1 E2 MU WM ltac:(lia) ltac:(lia) HH' HP' HT' MF' MI' ST') as CI2.
        clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH') as MK.
        zstep.                                 (* [comment removed for export] *)
        zstep. if_cases KN; zify_cond KN.
        - rewrite ?unsigned_lit in KN by lia.
          pose proof (signer_chain_null_inv usegs _ _ _ ltac:(rewrite <- KN; exact HC')) as ER. subst r.
          eapply tail_1d77c; [exact CI2| exact SZ].
        - rewrite ?unsigned_lit in KN by lia.
          destruct (signer_chain_nonnull usegs _ _ _ _ HC' KN) as (a2 & ns2 & r2 & ER).
          eapply (IH nxt ((D ++ SNAME ns) ++ [(a, 200)])); [rewrite ER; congruence| exact HC'| blocks_eq E| exact CI2]. }
      zstep. if_cases KI; zify_cond KI.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KI by lia.
        pose proof (chain_null_inv usegs _ _ _ _ _ _ ltac:(rewrite <- KI; exact HN0)) as EN. subst ns.
        eapply K1710. apply pinv_skip. exact CI0.
      - rewrite ?unsigned_lit in KI by lia.
        destruct (chain_nonnull usegs _ _ _ _ _ _ _ HN0 KI) as (n1 & rest & EN).
        eapply (loopC a nxt ([(a, 200)] ++ signer_blocks r ++ []) cs ns inext D);
          [rewrite EN; congruence| exact HN0| blocks_eq E| exact CI0| exact K1710].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Definition RAWC : list cell :=
      [C4 (pj_rawtag pj); C4 (pj0 pj); C8 (Z_to_bv 64 (po_rawlen po)); C8 (Z_to_bv 64 (po_rawp po)); CB 40 (pj1 pj)].
    (* [comment removed for export] *)
    Definition cellsZ (inext : Z) : list cell :=
      RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj); CB 416 (zeros 416); CB 8 (pj3 pj)]
      ++ signer_cells inext (po_signers_next po) (pj_s0 pj).
    Definition D3 : list blk := [(po_rawp po, po_rawlen po)] ++ crt_blocks (po_crt po) ++ SNAME (po_names0 po).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L46961339658.113L52103792382.114L53504623943.106L60837607228.115L63947589230.113L9809183628.112 00000:00f00l01801g02@S1L2sp1A1aS1L3DHI2sp1A2lo3SPA3SPR5CEILn6SLO60'2HA1a2HaS2sp1AS2sp1A2po2B2S1L2HI2sp1A2lo3SPA3SPR2hc6SLO60'2HA5ATOPc1a3HnaS2sp1A3SPA2HB5Ha_st5Hl_st". (* [comment removed for export] *)
    #[using="PK HFREE HMSF HLS HLSU SW DIMG DHI HND PKFREE LIVE IFF SPA ATOP CEIL SLO SP16 SPTOP TP SPR ND SUB LOSP SLO60"] Lemma from_1d774 : forall Lc mc moc hc (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
      pinv D3 (cellsZ (po_issuer0_next po)) Lc mc moc hc ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (po_signers_next po)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1dd24) fc None mc (seg_rom usegs)).
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 CI. pose proof CI as CI0. pinv_open CI.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof LOSP as LOSP'. pose proof SLO60 as SLO60'.
      pose proof LIVE as LV. ddestruct LV as (_ & HAL & HA & AB & RP & RL & _ & _ & _ & HN0 & HSC & _).
      assert (ATOPc : A + 1440 <= heap_top usegs L HI hc) by (rewrite HTc; exact ATOP).
      assert (SNB : 0 <= po_signers_next po < 2 ^ 64).
      { destruct (po_signers po) as [|[a2 ns2] r2] eqn:ES; [cbn in HSC; rewrite HSC; lia|].
        destruct (signer_chain_uncons usegs _ _ _ _ _ _ HSC) as (EE & _ & _ & _ & i2 & n2 & j2 & HR2 & _).
        pose proof (rw_cells_bound _ _ _ _ HR2) as B2. cbn [cells_size csize Nat.add signer_cells] in B2. lia. }
      unfold cellsZ, RAWC, signer_cells in CELLS. cbn [app] in CELLS.
      pose proof (munch_refl [(A + 1320, A + 1328)] mc) as MU. pose proof (wmono_refl usegs mc) as WM.
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR _].
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      assert (HH0 : HEAP usegs L HI hc (Lc ++ LB) m0 moc).
      { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact MU | exact WM | exact CEIL |].
        intros a Ha Hna. left. cbn [outside] in Hna. first [clear_disj; lia | lia]. }
      pose proof (statics_ok_munch usegs L _ mc m0 SOc MU ltac:(intros a Ha Hna; cbn [outside]; split; [lia | exact I])) as SO0.
      assert (HPX0 : heap_presx usegs L (Lc ++ LB) (bv_unsigned sp) X0 m m0).
      { eapply heap_presx_trans_presx; [exact HPXc| | intros b Hb; exact Hb].
        eapply heap_presx_of_frame_munch; [exact MU| exact WM| exact BR| exact DHI|]. intros a. cbn [outside]. lia. }
      assert (CI1 : pinv D3 (cellsZ 0) Lc m0 moc hc).
      { refine (conj HH0 (conj HTc (conj MFc (conj SUBLc (conj KEEPc (conj HPX0 (conj (ex_intro _ fj FR) (conj _ (conj MIc (conj SO0 STc)))))))))).
        unfold cellsZ, RAWC, signer_cells. cbn [app]. exact CELLS. }
      clear HHc SOc HPXc CELLS MK CI0. pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK.
      zstep. if_cases KS; zify_cond KS.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KS by lia.
        destruct (signer_chain_nonnull usegs _ _ _ _ HSC KS) as (a2 & ns2 & r2 & ER).
        eapply (loopB (cellsZ 0) eq_refl (po_signers po) (po_signers_next po) D3);
          [rewrite ER; congruence| exact HSC| unfold D3, p7_blocks; repeat rewrite <- app_assoc; rewrite app_nil_r; reflexivity| exact CI1].
      - rewrite ?unsigned_lit in KS by lia.
        pose proof (signer_chain_null_inv usegs _ _ _ ltac:(rewrite <- KS; exact HSC)) as ER.
        eapply tail_1d77c; [exact CI1| reflexivity].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Definition REST (inext : Z) : list cell := [CB 8 (pj2 pj); CB 416 (zeros 416); CB 8 (pj3 pj)] ++ signer_cells inext (po_signers_next po) (pj_s0 pj).
    Definition D2 : list blk := [(po_rawp po, po_rawlen po)] ++ crt_blocks (po_crt po).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@L10786976548.168L11741095640.100L11801455267.168L11803389859.191L14793074196.102L17472457816.168L19354909044.101L1996204537.168 L24864398257.127L25069551149.191L25382082548.101L2663817593.139 L26924648792.101L27285972791.190L28814043710.101L29152198284.139L31378308326.99 L31392867444.101L32377825311.139L34529705559.102L34529705559.103L37414286068.101L37622523289.170L37622523289.193L41179312816.168L43061431732.97 L43442376564.100L43654564952.101L44284188106.168L4447640620.191 L46961339658.106L51284150373.103L51723161399.168L52103792382.106L5238363032.168 L53517077152.188L54394091819.194L54398102733.108L54976524414.102L54976524414.103L56763568491.107L58042446975.168L59308628179.101L59308632561.102L59499841752.101L60837606325.197L60837742364.102L60837743493.190L63524049123.139L63528247133.103L63987349458.139L64762516557.139L65202436964.192L65655794365.139L66151427842.16 L66151427842.22 L7510805464.101 00000:00@00J00T01=01G01M02402:02D02J02\02b02h03403=03C03I03S04N05R05X06206L06R06`06f06l07207<07a08?08H09009?09E0:>0:i0;E0;j0<50<B0<N0<]0<c0<o0=U0=b0>50>H0>Q0>o0?T0?f0@?0@Z0@`S2sp1A3SPAS2sp1AS2sp1A3SPAS2sp1A3SPAS1L2sp1A2lo3SPR5CEILn9ACB_CEILn6SLO60'2HAS2sp1A3SPAS2sp1AS1L3DHI2sp1A2lo3SPA3SPR5CEILn6SLO60'2HAS2sp1AS2sp1A3SPAS2sp1AS1L2HI2sp1h1A4ATOPS2sp1AS2sp1AS2sp1A2HA2ABS2sp1A2HAS2sp1AS2sp1AS2sp1A3SPAS1L2ra2sp1A2po2lo3SPR5CEILn6SLO60'2HA2RL3RCE2HB5Ha_st5Hl_stS1L2sp2s01A2po2lo3SPR5CEILn6SLO60'2HA2RL3RCE2HB5Ha_st5Hl_st2s12s22s3S2sp1AS2sp1A2po2HA2RP2K02KR1x2HxS2sp1A2po2HA2RP2K02KR1x2HxS2sp1AS2sp1A2lo4LOSPS2sp1AS2sp1AS2sp1AS2sp1A3SPAS1L2sp1A2lo3SPA3SPR5CEILn6SLO60'2HA1aS1L4HLSU2sp1A2lo3SPR6SLO60'2HAS2sp1A2HAS1L3DHI2sp1A2lo3SPR5CEILn6SLO60'2HA1a2HaS2sp1A2lo5SLO60S2sp1AS1L2HI2sp1h1A2po2lo3SPA4ATOP3SPR6SLO60'2HA2RP2K02KR1a3HnaS1L2HI2sp1h1A2lo3SPA4ATOP3SPR6SLO60'2HA1a1CS2ra2sp1A3SPA2HB5Ha_st5Hl_stS2sp2s01A3SPA2HB5Ha_st5Hl_st2s12s22s3S2sp1A1a2HaS2sp1A2lo3SPAS2sp1A2HA2K0S2sp1A2po2RP2KRS2sp1AS2sp1A2po2B9S1L2sp1A2po3SPR9ACB_CEILn2HA2RP2RL3RCES2sp1A2po3INBS1L2HI2sp1h1A5SPTOPS1L2HI2sp1h1A5SPTOPS2sp1A2ABS1L4HLSU2sp1A2lo3SPR6SLO60'2HAS1L2sp1A2lo3SPA3SPR5CEILn6SLO60'2HA1aS1L2sp1A9ACB_CEILnS1A2r03HAL1q1r1H2H02q02H4S2sp2r04SP161q1r1H2H02q02H4S2sp1A". (* [comment removed for export] *)
    #[using="PK HFREE HMSF HLS HLSU SW DIMG DHI HND PKFREE CRTFREE CRLFREE LBn po pj HH LIVE IFF SPA ATOP CEIL SLO SP16 SPTOP TP SPR ND SUB LOSP SLO60"] Lemma entry_live : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m -> statics_ok usegs L m ->
      aevtM usegs mo POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1dcbc) fc None m (seg_rom usegs)).
    Proof.
      intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI SO.
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
      pose proof LOSP as LOSP'. pose proof SLO60 as SLO60'. pose proof alloc_ceiling_pos as ACP.
      pose proof LIVE as LV. ddestruct LV as (CELLS & HAL & HA & AB & RP & RL & RIN & RWC & OWNC & HN0 & HSC & _). unfold RepCrt.PKCS7_SIZE in AB.
      destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR0 _]. pose proof BR0 as BR0'. rewrite Forall_forall in BR0'.
      destruct (BR0' _ RIN) as (_ & _ & _ & RCE & _). cbn [fst snd] in RCE.
      rewrite pkcs7_cells_eq in CELLS. unfold p7cells, crt_cells, signer_cells in CELLS. cbn [app] in CELLS.
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      assert (SOK : id (statics_ok usegs L m)) by exact SO.
      zstep. carve_frame 48%nat ST.            (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.       (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
      zstep.                                   (* [comment removed for export] *)
      zstep. zstep; if_cases KA0; zify_cond KA0; [al8_close KA0|].
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR; [exfalso; rewrite ?unsigned_lit in KR by lia; lia|].
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
      pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
      (* [comment removed for export] *)
      pose proof (statics_ok_munch usegs L _ m m0 SOK MU ltac:(intros a Ha Hna; cbn [outside]; split; [lia | exact I])) as SO0.
      assert (HH0 : HEAP usegs L HI h (LBn ++ LB) m0 mo).
      { eapply (heap_frame usegs L HI) with (SP := lo); [exact HH | exact CEIL | | exact WM].
        intros a Ha Hnc; apply MU; cbn [outside]; unfold wa; rewrite unsigned_lit by lia; split; [|exact I].
        intros C; apply Hnc; left; lia. }
      assert (CI0 : pinv [] (RAWC ++ crt_cells (po_crt po) (pj_crt pj) ++ REST (po_issuer0_next po)) LBn m0 mo h).
      { split; [exact HH0|]. split; [reflexivity|]. split; [apply mo_frame_refl|]. split; [intros b Hb; exact Hb|]. split; [intros b Hb Hn; exact Hb|].
        split; [eapply heap_presx_of_frame_munch; [exact MU| exact WM| exact BR0| exact DHI|]; intros a; cbn [outside]; lia|].
        split; [eexists; exact FR|]. split; [unfold RAWC, REST, crt_cells, signer_cells; cbn [app]; exact CELLS|].
        split; [exact MI|]. split; [exact SO0| exact ST]. }
      clear HH0 SO0 CELLS.
      (* [comment removed for export] *)
      eapply aevtM_cut.
      { eapply (heap_free usegs L HI) with (A := po_rawp po) (n := po_rawlen po) (lo := lo) (h := h) (LB := LBn ++ LB);
          [ exact (proj1 CI0) | exact RIN | rewrite USP; exact ST | exact CEIL | rewrite USP; lia | exact MI | exact TP
          | rewrite USP; lia | reflexivity ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1
                      & E0 & MI1 & ST1 & MF1 & HP1 & h1 & HT1 & HH1).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HP1.
      fix_ret 0x1dcf0.
      assert (E1 : p7_blocks po = [] ++ [(po_rawp po, po_rawlen po)] ++ (crt_blocks (po_crt po) ++ SNAME (po_names0 po) ++ signer_blocks (po_signers po))) by reflexivity.
      pose proof (pinv_after_free _ _ _ _ _ _ _ _ _ _ _ _ CI0 E1 HH1 HP1 HT1 MF1 MI1 ST1) as CI1. cbn [app] in CI1.
      clear MK FR ST MI MU WM HP1. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof CI1 as CI1'. ddestruct CI1' as (HHc & HTc & MFc & SUBLc & KEEPc & HPXc & [fj FR] & CELLS & MIc & SOc & STc).
      change (rw_cells usegs m1 A (RAWC ++ crt_cells (po_crt po) (pj_crt pj) ++ REST (po_issuer0_next po))) in CELLS.
      destruct (rw_cells_split3 usegs m1 A _ _ _ CELLS) as (C1 & C2 & C3). clear CELLS.
      change (Z.of_nat (cells_size RAWC)) with 64 in C2, C3.
      change (Z.of_nat (cells_size (crt_cells (po_crt po) (pj_crt pj)))) with 744 in C3.
      assert (E2 : p7_blocks po = [(po_rawp po, po_rawlen po)] ++ crt_blocks (po_crt po) ++ (SNAME (po_names0 po) ++ signer_blocks (po_signers po))) by reflexivity.
      assert (CRTIN : forall b, In b (crt_blocks (po_crt po)) -> In b (lb_remove (po_rawp po) LBn)).
      { intros b Hb. eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI1 E2). exact Hb. }
      eapply aevtM_cut.
      { eapply CRTFREE with (LBo := lb_remove (po_rawp po) LBn) (LB := LB) (A := A + 64) (f := po_crt po) (j := pj_crt pj) (lo := lo) (h := h1);
          [ exact HHc | | exact CRTIN | rewrite USP; lia | unfold CRT_SIZE; rewrite HTc; lia
          | rewrite USP; exact STc | exact CEIL | rewrite USP; unfold X509_CRT_FREE_STACK, PK_FREE_STACK; lia
          | rewrite USP; clear - SP16 SPR SLO60' CEILn ACB_CEILn; Z.div_mod_to_equations; lia
          | rewrite USP, HTc; lia | exact DHI | exact MIc | exact SOc | exact TP | reflexivity ].
        split; [exact C2|]. split; [clear - HAL; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [unfold CRT_SIZE; lia|].
        eapply crt_own_ok_presx; [exact OWNC| intros b Hb; apply in_or_app; left; exact (CRTIN b Hb)| exact HPXc| eapply blocks_below_of_HEAP; exact HHc| apply fpX| lia| assumption]. }
      intros ms' mo'x PO.
      ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & mo2 & h2 & L2
                      & E0 & MI2 & SO2 & ST2 & MF2 & HT2 & HH2 & SUB2 & KEEP2 & CZ2 & HPX2).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST2, HPX2. unfold CRT_SIZE in HPX2.
      fix_ret 0x1dcf8.
      assert (CI2 : pinv D2 (cellsZ (po_issuer0_next po)) L2 m2 mo2 h2).
      { unfold D2. eapply (pinv_after _ _ _ _ _ _ _ _ _ _ _ _ [(A + 64, A + 64 + 744)] CI1 SUB2 KEEP2 HH2 HT2 MF2 HPX2);
          [ intros x Hx; cbn [outside] in *; split; [lia| exact I] | cbn [disjoint_from]; lia | | exact MI2 | exact SO2 | exact ST2 ].
        unfold cellsZ. apply rw_cells_join3.
        - eapply heap_presx_rw_cells; [exact HPX2| exact C1| apply client_range_stack; lia| cbn [cells_size csize Nat.add disjoint_from RAWC]; lia].
        - change (Z.of_nat (cells_size RAWC)) with 64. exact CZ2.
        - change (Z.of_nat (cells_size RAWC)) with 64. change (Z.of_nat (cells_size [CB 744 (zeros 744)])) with 744.
          eapply heap_presx_rw_cells; [exact HPX2| exact C3| apply client_range_stack; lia| unfold REST; cbn [cells_size csize Nat.add disjoint_from signer_cells app]; lia]. }
      clear MK C1 C2 C3 HHc HTc MFc SUBLc KEEPc HPXc FR MIc SOc STc CI1 fj. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof CI2 as CI2'. ddestruct CI2' as (HHc & HTc & MFc & SUBLc & KEEPc & HPXc & [fj FR] & CELLS & MIc & SOc & STc).
      change (rw_cells usegs m2 A ((RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]) ++ [CB 416 (zeros 416)]
                                   ++ ([CB 8 (pj3 pj)] ++ signer_cells (po_issuer0_next po) (po_signers_next po) (pj_s0 pj)))) in CELLS.
      destruct (rw_cells_split3 usegs m2 A _ _ _ CELLS) as (C1 & C2 & C3). clear CELLS.
      change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816 in C2, C3.
      change (Z.of_nat (cells_size [CB 416 (zeros 416)])) with 416 in C3.
      eapply aevtM_cut_evt; [exact MK | |].
      { eapply CRLFREE with (A := A + 816) (lo := lo);
          [ exact C2 | lia | clear - HAL; Z.div_mod_to_equations; lia | rewrite USP; exact STc | rewrite USP; unfold X509_CRL_FREE_STACK; lia | exact CEIL
          | rewrite USP; clear - SP16 SPR SLO60' CEILn ACB_CEILn; Z.div_mod_to_equations; lia
          | rewrite USP; lia | exact SOc | exact DHI | lia | exact MIc | reflexivity ]. }
      intros ms' PO. ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & CZ3 & ST3 & SO3).
      rewrite USP in MU3, ST3. unfold X509_CRL_FREE_STACK in MU3.
      fix_ret 0x1dd00.
      assert (CI3 : pinv D2 (cellsZ (po_issuer0_next po)) L2 m3 mo2 h2).
      { pose proof (pinv_after _ [] _ (cellsZ (po_issuer0_next po)) _ L2 _ _ _ m3 mo2 h2 [(A + 816, A + 1232)] CI2
                      (fun b Hb => Hb) (fun b Hb _ => Hb)) as PA.
        rewrite app_nil_r in PA. destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR2 _].
        apply PA; clear PA.
        - eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact MU3 | exact WM3 | exact CEIL |].
          intros a Ha Hna. left. rewrite HTc. cbn [outside] in Hna. first [clear_disj; lia | lia].
        - reflexivity.
        - apply mo_frame_refl.
        - eapply heap_presx_of_frame_munch; [exact MU3| exact WM3| exact BR2| exact DHI|]. intros a. cbn [outside]. lia.
        - intros x Hx. cbn [outside] in *. split; [lia| exact I].
        - cbn [disjoint_from]. lia.
        - unfold cellsZ.
          change (rw_cells usegs m3 A ((RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]) ++ [CB 416 (zeros 416)]
                                       ++ ([CB 8 (pj3 pj)] ++ signer_cells (po_issuer0_next po) (po_signers_next po) (pj_s0 pj)))).
          apply rw_cells_join3.
          + eapply rw_cells_transport; [exact C1| exact MU3| exact WM3| cbn [cells_size csize Nat.add disjoint_from RAWC app]; lia].
          + change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816. exact CZ3.
          + change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816. change (Z.of_nat (cells_size [CB 416 (zeros 416)])) with 416.
            eapply rw_cells_transport; [exact C3| exact MU3| exact WM3| cbn [cells_size csize Nat.add disjoint_from signer_cells app]; lia].
        - exact MI3.
        - exact SO3.
        - exact ST3. }
      clear C1 C2 C3 HHc HTc MFc SUBLc KEEPc HPXc FR MIc SOc STc CI2 fj MU3 WM3.
      (* [comment removed for export] *)
      pose proof CI3 as CI3'. ddestruct CI3' as (HHc & HTc & MFc & SUBLc & KEEPc & HPXc & [fj FR] & CELLS & MIc & SOc & STc).
      unfold cellsZ, RAWC, signer_cells in CELLS. cbn [app] in CELLS.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HN0) as INB.
      assert (SNB : 0 <= po_signers_next po < 2 ^ 64).
      { destruct (po_signers po) as [|[a9 ns9] r9] eqn:ES; [cbn in HSC; rewrite HSC; lia|].
        destruct (signer_chain_uncons usegs _ _ _ _ _ _ HSC) as (EE & _ & _ & _ & i9 & n9 & j9 & HR9 & _).
        pose proof (rw_cells_bound _ _ _ _ HR9) as B9. cbn [cells_size csize Nat.add signer_cells] in B9. lia. }
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      assert (ED3 : D3 = D2 ++ SNAME (po_names0 po)) by (unfold D3, D2; rewrite <- app_assoc; reflexivity).
      zstep. if_cases KI; zify_cond KI.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KI by lia.
        pose proof (chain_null_inv usegs _ _ _ _ _ _ ltac:(rewrite <- KI; exact HN0)) as EN.
        eapply from_1d774. rewrite ED3. apply pinv_skip. exact CI3.
      - rewrite ?unsigned_lit in KI by lia.
        destruct (chain_nonnull usegs _ _ _ _ _ _ _ HN0 KI) as (n1 & rest & EN).
        eapply (loopA (po_signers_next po) (signer_blocks (po_signers po) ++ []) (cellsZ (po_issuer0_next po)) (po_names0 po) (po_issuer0_next po) D2);
          [rewrite EN; congruence| exact HN0| unfold D2, p7_blocks; repeat rewrite <- app_assoc; rewrite app_nil_r; reflexivity| exact CI3|].
        intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 CI'.
        eapply from_1d774. rewrite ED3. exact CI'.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L11741095640.79L11741095640.82L19354909044.80L25382082548.80L26924648792.80L26924648792.82L27907151106.81L28814043710.80L31378308326.78L31392867444.80L37414286068.80L43061677065.76L43442376564.79L43654564952.80L43654564952.82L46961339658.83L51711223320.80L52103792382.83L54398102733.85L54976524414.81L54976524414.82L56763568491.84L59308628179.80L59308632561.81L59499841752.80L59499841752.82L7510805464.80 L7510805464.82 00000600<00B00H00N00T00a00m01301901?01L01R01X01^02@02F02k03S03o04T04_04k05405:05@05F05LS2sp1AS2sp1AS2sp1AS2sp1AS2sp1AS2sp1AS2sp1A2lo3SLOS2sp1A2HA2ABS2sp1AS2sp1AS2sp1AS2sp1A2lo3SLOS2sp1AS2sp1AS2sp1AS1L2sp1A2lo2HA3SPA3SLO5CEILn3SPR1aS2sp1AS1L3DHI2sp1A2lo2HA3SLO5CEILn3SPR1a2HaS1L2HI2sp1h1A2lo2HA3SPA4ATOP3SLO3SPR1a1CS2ra2sp1A3SPA2HB5Ha_st5Hl_stS2sp2s01A3SPA2HB5Ha_st5Hl_st2s12s22s3S2sp1A1a2HaS2sp1A2HA2K0S2sp1A2KRS2sp1AS2sp1AS2sp1AS2sp1A". (* [comment removed for export] *)
  #[using="DHI"] Lemma entry_zero : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB LBn : list blk) (A lo : Z),
    HEAP usegs L HI h (LBn ++ LB) m mo -> pkcs7_zero usegs m A -> A mod 8 = 0 -> 0 < A -> A + 1440 <= 2 ^ 64 ->
    bv_unsigned sp <= A -> A + 1440 <= heap_top usegs L HI h ->
    stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PKCS7_FREE_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= heap_top usegs L HI h ->
    mem_inv usegs m -> statics_ok usegs L m -> tp = Z_to_bv 64 (hl_tp L) ->
    aevtM usegs mo (pkcs7_free_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB A lo m mo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1dcbc) fc None m (seg_rom usegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LBn A lo
           HH PZ HAL HA AB SPA ATOP ST CEIL SLO SP16 SPTOP MI SO TP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    unfold PKCS7_FREE_STACK in SLO. unfold pkcs7_zero in PZ.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (SOK : id (statics_ok usegs L m)) by exact SO.
    destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR0 _]. apply Forall_app in BR0. destruct BR0 as [_ BR0].
    zstep. carve_frame 48%nat ST.            (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.       (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep.                                   (* [comment removed for export] *)
    zstep. zstep; if_cases KA0; zify_cond KA0; [al8_close KA0|].
    zstep.                                   (* [comment removed for export] *)
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 16 (zeros 1440))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    zstep. if_cases KR; zify_cond KR; [| exfalso; rewrite ?unsigned_lit in KR by lia; lia].
    zstep. zstep. zstep. zstep. zstep.       (* [comment removed for export] *)
    zstep. zstep.                            (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    lazymatch goal with FRH : rw_cells usegs m0 (bv_unsigned sp + -48) _, STH : stk usegs m0 lo _ |- _ => release_frame FRH STH (bv_unsigned sp) end.
    pose proof (statics_ok_munch usegs L _ m m0 SOK MU ltac:(intros a Ha Hna; cbn [outside]; split; [lia | exact I])) as SO0.
    assert (HH0 : HEAP usegs L HI h (LBn ++ LB) m0 mo).
    { eapply (heap_frame usegs L HI) with (SP := lo); [exact HH | exact CEIL | | exact WM].
      intros a Ha Hnc; apply MU; cbn [outside]; unfold wa; rewrite unsigned_lit by lia; split; [|exact I].
      intros C; apply Hnc; left; lia. }
    apply aevtM_done. unfold pkcs7_free_post, P_pkcs7_top.PKCS7_SIZE.
    deexists 15. dexists m0, mo, h, LBn.
    split; [reflexivity|]. split; [assumption|]. split; [exact SO0|]. split; [assumption|]. split; [apply mo_frame_refl|].
    split; [reflexivity|]. split; [assumption|]. split; [exact HH0|].
    eapply heap_presx_of_frame_munch; [exact MU| exact WM| exact BR0| exact DHI|]. intros a. cbn [outside]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="HFREE HMSF HLS HLSU SW DIMG DHI HND PKFREE CRTFREE CRLFREE"] Theorem U_pkcs7_free_spec : pkcs7_free_stmt usegs L HI (option (p7_own * p7_junk)) (pkcs7_at usegs PK) 0x1dcbc.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LBn A lo st
           HH REP SPA ATOP ST CEIL SLO SP16 SPTOP MI SO TP ->.
    unfold P_pkcs7_top.PKCS7_SIZE in ATOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    destruct st as [[po pj]|].
    - ddestruct REP as (LIVE & NDn & IFF).
      eapply entry_live; eassumption.
    - ddestruct REP as (PZ & HAL & HA & AB). unfold RepCrt.PKCS7_SIZE in AB.
      eapply entry_zero; eassumption.
  Qed.
End Walk.

