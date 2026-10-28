(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Exec CellsX Arr TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons AsanAllocCons2.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain AsUnwind FakeStackRep
     AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepX SecLazy SecGap AsDepotInv AsDepotHash
     AG_WFHit AG_MallocModel AG_Frame AG_WriteSet AW_MallocBase AG_Malloc2 AG_MallocCold AG_MallocLarge3 AG_MallocAll AG_FreeNull
     AG_Free2 AG_FreeTail AG_FreeTop AS_InstDefs AS_InstChain AS_InstLaws2 AS_InstHeap AsWalk CidBits AG_RecycleDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section Free.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rw_cells_transport_vis : forall (P : Z -> Prop) m m' A cs,
    agree_on P m m' -> (forall x : word, P (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) ->
    rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
  Proof.
    intros P m m' A cs AG VS [[Hwf Hb] Hw] HR. split; [split; [exact Hwf|]|].
    - eapply (bytes_at_transport_pt P m m' AG); [exact Hb|]. rewrite cells_bytes_length by assumption. exact HR.
    - destruct Hw as (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros i Hi. apply VS; [| exact (H2 i Hi)].
      unfold wa. rewrite unsigned_lit by lia. apply HR. lia.
  Qed.

  Lemma nodup_map_inj : forall (A B : Type) (f : A -> B) (l : list A) x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    intros A B f l x y ND. induction l as [|z l IH]; [intros []|]. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
    intros [<-|Hx] [<-|Hy] E; [reflexivity| | |exact (IH ND Hx Hy E)]; exfalso; apply NI; [rewrite E| rewrite <- E]; apply in_map; assumption.
  Qed.
  Lemma sh_add8 : forall X k, X mod 8 = 0 -> sh (X + 8 * k) = sh X + k.
  Proof. intros X k H. unfold sh. Z.div_mod_to_equations. lia. Qed.

  Section Gone.
    Variables (s s' : ast).
    Hypothesis PL : placed_ok s.

    Let SEC : forall sc, In sc (as_sec (a_st s)) ->
           sc_map_beg sc mod kPageSize = 0 /\ aapp (sc_map_beg sc) (sc_map_size sc) /\ sc_map_beg sc + sc_map_size sc <= aceil
        /\ 2 * kPageSize <= sc_map_size sc
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_sb s) (kSpaceSize + kPageSize)
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_pa s) kPtrArrayReserve
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_thr s) kPageSize
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_ctx s) 160
        /\ disj (sc_map_beg sc) (sc_map_size sc) (a_fsb s) AFS_SIZE.
    Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.

    Lemma sh_mono : forall x y, x <= y -> sh x <= sh y.
    Proof. intros x y H. unfold sh. Z.div_mod_to_equations. lia. Qed.
    Lemma sh_land2 : forall X k a, AIMG_TOP <= X -> X + k <= aceil -> sh X <= a < sh (X + k) -> ALOWSH_LO <= a < AHI_LO.
    Proof.
      intros X k a H1 H2 Ha. pose proof sh_ceiling_lt_AHI_LO as SC. pose proof (sh_mono _ _ H2). acb.
      unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO in *. Z.div_mod_to_equations. lia.
    Qed.

    Lemma gone_geo : forall sc, In sc (as_sec (a_st s)) ->
      AIMG_TOP <= sc_map_beg sc /\ sc_map_beg sc + sc_map_size sc <= aceil /\ sc_map_beg sc mod kPageSize = 0 /\ aapp (sc_map_beg sc) (sc_map_size sc)
      /\ disj (sc_map_beg sc) (sc_map_size sc) (a_sb s) (kSpaceSize + kPageSize) /\ disj (sc_map_beg sc) (sc_map_size sc) (a_thr s) kPageSize
      /\ disj (sc_map_beg sc) (sc_map_size sc) (a_fsb s) AFS_SIZE.
    Proof.
      intros sc Hin. pose proof (SEC sc Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
      split; [exact (aapp_ge_top _ _ A2)|]. split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. split; [exact A5|]. split; [exact A7| exact A9].
    Qed.

    Lemma secgone_not_image : forall a, AIMG_LO <= a < AIMG_TOP -> ~ secgone s s' a.
    Proof.
      intros a Ha (sc & IN & _ & R). destruct (gone_geo sc IN) as (G1 & G2 & _). acb.
      destruct R as [R|R]; [lia|]. unfold sh, ASHADOW_BASE, AIMG_TOP, AIMG_LO in *. Z.div_mod_to_equations. lia.
    Qed.
    Lemma secgone_not_imgshadow : forall a, sh AIMG_LO <= a < sh AIMG_TOP -> ~ secgone s s' a.
    Proof.
      intros a Ha (sc & IN & _ & R). destruct (gone_geo sc IN) as (G1 & G2 & _ & AP & _). acb.
      destruct R as [R|R].
      - clear - AP R Ha. aunf. unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
      - unfold sh, ASHADOW_BASE, AIMG_TOP, AIMG_LO in *. Z.div_mod_to_equations. lia.
    Qed.
    Lemma secgone_not_stack : forall a lo, aceil <= lo -> lo <= a -> ~ secgone s s' a.
    Proof.
      intros a lo LO Ha (sc & IN & _ & R). destruct (gone_geo sc IN) as (G1 & G2 & _). pose proof sh_ceiling_lt_AHI_LO. acb.
      destruct R as [R|R]; [lia|]. unfold sh, ASHADOW_BASE, AHI_LO in *. Z.div_mod_to_equations. lia.
    Qed.
    (* [comment removed for export] *)
    Lemma secgone_not_obj : forall X k a, akobj X k -> X + k <= aceil ->
      (forall sc, In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) X k) ->
      X <= a < X + k -> ~ secgone s s' a.
    Proof.
      intros X k a AK CE DJ Ha (sc & IN & _ & R). destruct (gone_geo sc IN) as (G1 & G2 & _). pose proof (DJ sc IN) as D.
      destruct R as [R|R]; [clear - D R Ha; unfold disj in D; lia|].
      apply (akobj_not_land X k a AK CE Ha). exact (sh_land2 (sc_map_beg sc) (sc_map_size sc) a G1 G2 R).
    Qed.
    (* [comment removed for export] *)
    Lemma secgone_not_stkshadow : forall a, sh aceil <= a < AHI_LO -> ~ secgone s s' a.
    Proof.
      intros a Ha (sc & IN & _ & R). destruct (gone_geo sc IN) as (G1 & G2 & _ & AP & _). acb.
      destruct R as [R|R].
      - clear - AP R Ha ACEILB. aunf. unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
      - unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
    Qed.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma app_not_land : forall X k a, AIMG_TOP <= X -> X + k <= aceil -> aapp X k -> X <= a < X + k -> ~ (ALOWSH_LO <= a < AHI_LO).
    Proof. intros X k a H1 H2 AP Ha L. clear - AP Ha L H2. aunf. lia. Qed.

    Lemma secgone_not_fsb : forall a, (a_fsb s <= a < a_fsb s + AFS_SIZE \/ sh (a_fsb s) <= a < sh (a_fsb s + AFS_SIZE)) -> ~ secgone s s' a.
    Proof.
      intros a Ha (sc & IN & _ & R). destruct (gone_geo sc IN) as (G1 & G2 & G3 & AP & _ & _ & DF).
      pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _).
      pose proof (aapp_ge_top _ _ F1) as FT. unfold disj in DF.
      destruct Ha as [Ha|Ha]; destruct R as [R|R].
      - lia.
      - apply (app_not_land (a_fsb s) AFS_SIZE a FT F2 F1 Ha). exact (sh_land2 (sc_map_beg sc) (sc_map_size sc) a G1 G2 R).
      - apply (app_not_land (sc_map_beg sc) (sc_map_size sc) a G1 G2 AP R). exact (sh_land2 (a_fsb s) AFS_SIZE a FT F2 Ha).
      - destruct DF as [D|D]; [pose proof (sh_mono _ _ D)| pose proof (sh_mono _ _ D)]; lia.
    Qed.

    Let SEC2 : forall sc sc', In sc (as_sec (a_st s)) -> In sc' (as_sec (a_st s)) -> sc_map_beg sc <> sc_map_beg sc' ->
           disj (sc_map_beg sc) (sc_map_size sc) (sc_map_beg sc') (sc_map_size sc').
    Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.

    (* [comment removed for export] *)
    Lemma secgone_awrit : forall d lo SP a, secgone s s' a -> awrit s s' d lo SP a.
    Proof.
      intros d lo SP a (sc & IN & _ & R). pose proof (SEC sc IN) as (A1 & _).
      unfold awrit. do 5 right; left. exists sc. split; [left; exact IN|].
      destruct R as [R|R]; [left; exact R| right].
      clear - A1 R. unfold sh, ASHADOW_BASE, kPageSize in *. Z.div_mod_to_equations. lia.
    Qed.
    (* [comment removed for export] *)
    Lemma vis_off_awrit : forall d lo SP m m', avis s s' m m' ->
      forall x : word, ~ awrit s s' d lo SP (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.
    Proof. intros d lo SP m m' AV x NW V. destruct (AV x V) as [V'|G]; [exact V'| exfalso; exact (NW (secgone_awrit d lo SP _ G))]. Qed.

    (* [comment removed for export] *)
    Lemma secgone_not_block : forall ch a, WF (a_st s) -> ast_ok s' -> a_sb s' = a_sb s ->
      (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s))) ->
      In ch (chunk_list (a_st s')) ->
      (ch_user_beg ch <= a < ch_user_beg ch + ch_used ch \/ sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch)) ->
      ~ secgone s s' a.
    Proof.
      intros ch a W OK' ESB SUB CHIN Ha (sc & IN & NIN & R).
      destruct (gone_geo sc IN) as (G1 & G2 & G3 & AP & DSB & _).
      pose proof (ext_facts s' OK' ch CHIN) as (X1 & X2 & X3 & XP & XS).
      pose proof (chunk_geom s' OK' ch CHIN) as (C1 & C2 & C3 & C4 & C5 & C6 & _). pose proof (chunk_align s' OK' ch CHIN) as (_ & _ & AL3 & _).
      pose proof (ext_band s' OK' ch CHIN) as EB. cbv zeta in C2, C3, C4, C5, C6.
      destruct W as (_ & _ & _ & _ & _ & NDS & _).
      assert (DJ : ch_end ch <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= ch_lo ch).
      { destruct (ch_primary ch) eqn:E.
        - destruct (XP eq_refl) as (_ & _ & B1 & B2). rewrite ESB in B1, B2. unfold ch_lo. rewrite E.
          clear - B1 B2 DSB. unfold disj, kPageSize in *. lia.
        - destruct (XS eq_refl) as (h & Hh & L0 & E0 & _).
          assert (NE : sc_map_beg h <> sc_map_beg sc).
          { intros EQ. apply NIN. rewrite <- (nodup_map_inj _ _ sc_map_beg (as_sec (a_st s)) h sc NDS (SUB h Hh) IN EQ). exact Hh. }
          pose proof (SEC2 h sc (SUB h Hh) IN NE) as D. clear - D L0 E0. unfold disj in D. lia. }
      assert (UB : ch_lo ch <= ch_user_beg ch /\ ch_user_beg ch + 8 * nsh (ch_used ch) <= ch_end ch /\ ch_used ch <= 8 * nsh (ch_used ch) /\ ch_user_beg ch mod 8 = 0)
        by (clear - X3 C1 C2 C4 C5 C6 AL3; repeat split; try lia; Z.div_mod_to_equations; lia).
      destruct UB as (U1 & U2 & U3 & U4).
      destruct Ha as [Ha|Ha]; destruct R as [R|R].
      - clear - DJ U1 U2 U3 Ha R. lia.
      - apply (app_not_land (ch_lo ch) (ch_end ch - ch_lo ch) a X1 ltac:(clear - X2; lia) EB ltac:(clear - U1 U2 U3 Ha; lia)).
        exact (sh_land2 (sc_map_beg sc) (sc_map_size sc) a G1 G2 R).
      - apply (app_not_land (sc_map_beg sc) (sc_map_size sc) a G1 G2 AP R).
        apply (sh_land2 (ch_user_beg ch) (8 * nsh (ch_used ch)) a ltac:(clear - X1 U1; lia) ltac:(clear - X2 U2; lia)).
        rewrite (sh_add8 _ _ U4). exact Ha.
      - pose proof (sh_add8 (ch_user_beg ch) (nsh (ch_used ch)) U4) as EA.
        destruct DJ as [D|D].
        + pose proof (sh_mono _ _ U2) as M1. pose proof (sh_mono _ _ D) as M2. clear - EA M1 M2 Ha R. lia.
        + pose proof (sh_mono _ _ D) as M1. pose proof (sh_mono _ _ U1) as M2. clear - M1 M2 Ha R. lia.
    Qed.
  End Gone.

  (* [comment removed for export] *)
  Lemma lbp_remove : forall (q : bptr) LB, Forall (fun b => blk_id b = blk_addr b /\ 1 <= blk_size b <= 2 ^ 28) LB ->
    lbp (Ilb_remove q LB) = lb_remove q (lbp LB).
  Proof.
    (* [comment removed for export] *)
    intros q LB F. induction LB as [|b LB IH]; [reflexivity|]. apply Forall_cons_iff in F. destruct F as [[E _] F].
    specialize (IH F). unfold lbp, Ilb_remove, lb_remove in *. cbn. replace (blk_addr b =? q) with (blk_id b =? q) by (rewrite E; reflexivity).
    destruct (decide (negb (blk_id b =? q))) as [y|ny].
    - destruct (blk_id b =? q); [destruct y|]. cbn. f_equal. exact IH.
    - destruct (blk_id b =? q); [| exfalso; apply ny; exact I]. cbn. exact IH.
  Qed.
  Lemma Ilb_remove_incl : forall (q : bptr) LB b, In b (Ilb_remove q LB) -> In b LB /\ blk_id b <> q.
  Proof.
    intros q LB b H. unfold Ilb_remove in H. induction LB as [|c LB IH]; cbn in H; [destruct H|].
    destruct (decide (negb (blk_id c =? q))) as [y|ny].
    - destruct H as [<-|H]; [split; [left; reflexivity|]| destruct (IH H) as [A B]; split; [right; exact A| exact B]].
      intros EQ. rewrite EQ, Z.eqb_refl in y. exact y.
    - destruct (IH H) as [A B]. split; [right; exact A| exact B].
  Qed.
  Lemma Ilb_remove_length : forall (q : bptr) LB, (length (Ilb_remove q LB) <= length LB)%nat.
  Proof.
    intros q LB. unfold Ilb_remove. induction LB as [|b LB IH]; cbn; [apply le_n|].
    destruct (decide (negb (Z.eqb (blk_id b) q))); cbn [length]; [apply le_n_S; exact IH| apply le_S; exact IH].
  Qed.

  Variable p : iparams.

  (* [comment removed for export] *)
  Lemma free_stub_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                               (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m ->
    evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AFREE_ICPT) fc None m (seg_rom asegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AFREE_STUB) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AFREE_STUB, AFREE_ICPT. step. apply evt_done. reflexivity. Qed.

  Theorem inst_free_null_stmt : free_null_stmt_at (KHp p) AFREE_STUB.
  Proof.
    unfold free_null_stmt_at. cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cf as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St KHp].
    intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m x LB lo B errv mo CH.
    intros VIS HP K CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH.
    destruct x as [s d]. cbn [i_s i_d] in *.
    unfold AsSR.VIS in VIS. unfold AsSR.AKREL in K. cbn [i_s cfg_model] in VIS, K. destruct K as [OK IKx]. destruct IKx as (AMX & DCOV & DTV).
    unfold Irauxv_ok in AUX. unfold AFREE_STACK in LO.
    pose proof HP as HP0. unfold IRHEAP in HP. cbn [i_s i_d] in HP.
    destruct HP as (HR & IDS & LEN & AWV & FLX & DEP & DPL & DTR & DF1 & DF2 & EF & MF & DFD & TH & TLS & ASV & DAP & DSEC & [PI IQ]).
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. pose proof (proj2 OKs) as W. pose proof (proj1 OKs) as PL.
    pose proof (nalloc_le_blocks s (lbp LB) m HR) as NAL. unfold lbp in NAL. rewrite zlen_map in NAL. unfold zlen in NAL.
    unfold ILIVE_CNT_MAX, ADRV_CNT in LEN.
    (* [comment removed for export] *)
    unfold AsSR.SR.
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo _ OK VIS); [apply free_stub_evt; exact MI|].
    cbv beta. intros msF1 mo1 OK1 SBM1 _ E1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    (* [comment removed for export] *)
    destruct (fch_of_achain m (bv_unsigned sp) (bv_unsigned s0) (a_top s) (a_bot s) (bv_unsigned ra) lo CH HCH CEIL ltac:(lia) SP16 (bv_unsigned_in_range _ ra))
      as (CHg & FCH & _).
    eapply (free_arep_null ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF1 mo1 _ s (lbp LB) d lo CHg
              HR (conj AWV FLX) AMX1 DEP DPL DCOV1 MI ST CEIL ltac:(clear - LO; lia) SP16 ltac:(clear - AUX SPB; lia) TP FCH OK1).
    { unfold AFREE_ICPT in E1. exact E1. }
    intros msF' mo' PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                    & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & FR' & WM' & CP' & AVX' & MODEL).
    destruct MODEL as (st'' & ev & MK & SBS).
    set (s' := null_s' s) in *.
    (* [comment removed for export] *)
    pose proof (proj1 HR') as R'. pose proof (proj1 R') as OKs'. pose proof (proj2 OKs') as W'. pose proof (proj1 OKs') as PL'.
    assert (E_thr : a_thr s' = a_thr s) by reflexivity. assert (ESB : a_sb s' = a_sb s) by reflexivity. assert (EPA : a_pa s' = a_pa s) by reflexivity.
    assert (PI' : PINVI (a_st s')).
    { assert (SC : same_core (a_st s') st'') by (apply same_core_sbs; unfold same_but_shadow in SBS |- *; intuition congruence).
      split.
      - apply (PINV_core (a_st s') st'' SC). apply (PINV_am_free_full (a_st s) 0 st'' ev W PI ltac:(unfold LIVEB; lia) MK).
      - apply (INITQ_core (a_st s') st'' SC). exact (proj1 (am_free_full_initq (a_st s) 0 st'' ev W IQ MK)). }
    pose proof TH as (TH1 & TH2 & DPOS & DM8 & DCE & AKD).
    pose proof CP' as AG'. unfold acompl in AG'.
    assert (AGR : agree_on (fun a => ~ awrit s s' d lo (bv_unsigned sp) a) m m') by (intros x0 Hx Hr; exact (AG' x0 Hr Hx)).
    assert (DTV1 : dtv_cov p mo1) by (intros x0 Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DTV x0 Hx)).
    assert (IMGW : forall a, AIMG_LO <= a < AIMG_TOP -> ~ astatw a -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a H1 H2. exact (image_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL H1 H2). }
    assert (DSEC' : forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s))) by (intros sc Hsc; exact Hsc).
    assert (DTVW : forall a, ip_D p <= a < ip_D p + 32 -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a Ha. exact (dtv_not_written p s s' d lo (bv_unsigned sp) mo1 mo' a PL PL' E_thr ESB EPA CEIL AKD DCE DPOS DAP DSEC DTV1 AVX' Ha). }
    assert (RH' : IRHEAP p (IST s' d) LB m').
    { unfold IRHEAP. cbn [i_s i_d].
      split; [exact HR'|]. split; [exact IDS|]. split; [unfold ILIVE_CNT_MAX, ADRV_CNT; lia|].
      split; [exact AWV'|]. split; [exact FX'|]. split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DTR|].
      split; [exact DF1|]. split; [exact DF2|]. split; [exact EF|]. split; [exact MF|]. split; [exact DFD|].
      split.
      { unfold ATHR. split; [| split; [| exact (conj DPOS (conj DM8 (conj DCE AKD)))]].
        - eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact TH1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
          intros a Ha. apply IMGW; unfold astatw, ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia.
        - eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact TH2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
          intros a Ha. apply DTVW. lia. }
      split.
      { destruct TLS as (tb & te & TC). exists tb, te. eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact TC|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length]. intros a Ha.
        exact (thread_head_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL ltac:(lia)). }
      split; [exact (proj1 (proj2 (proj1 AMX')))|].
      split; [exact DAP|].
      split; [| exact PI'].
      intros sc Hsc. exact (DSEC sc Hsc). }
    apply sreach_done. unfold AsIface.free_null_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', (IST s' d).
    cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cf as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_FSB KHp i_s i_d].
    split; [unfold AsSR.VIS; cbn [i_s]; exact VIS'|].
    split. { unfold AsSR.AKREL. cbn [i_s i_d cfg_model cfg_ms]. split; [exact OK'|]. split; [exact AMX'|]. split; [exact DCOV'|].
             intros x0 Hx. destruct (proj1 (AVX' x0 (DTV1 x0 Hx))) as [C|(sc & INs & _ & Rx)]; [exact C| exfalso].
             pose proof (DSEC sc INs) as DS. clear - DS Rx Hx. unfold disj, kPageSize in *. lia. }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat mo mo1 SBM1) NV')|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { rewrite TP. unfold wz. rewrite unsigned_lit by (unfold AsIface.ATP; lia). rewrite TP in ERR. rewrite unsigned_lit in ERR by (unfold AsIface.ATP; lia).
             eapply (rw_cells_transport_pt _ m m' AGR WM'); [exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
             intros a Ha. apply IMGW; unfold astatw, AsIface.ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia. }
    split; [exact AUX|].
    split. { intros a Ha CL. split; [| intros Wv; apply WM'; exact Wv]. apply (FR' a Ha).
             unfold aclient_addr in CL. unfold aclient. cbn [as_FSB KHp] in CL.
             destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]]; [left; exact C| right; left; exact C| | | | |].
             - right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [| exact Rb].
               unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
             - right; right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [| exact Rb].
               unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
             - do 4 right; left. rewrite EF. exact C.
             - do 5 right; left. rewrite EF. exact C.
             - do 6 right. exact C. }
    split; [exact RH'|].
    split. { eapply (ACONST_ext m m' AC).
             - intros a Ha HC. apply (AGR a); [| exact Ha]. unfold aconst_addr in HC.
               unfold AsConst.ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AVERBOSITY_CELL,
                 AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL in HC.
               destruct (Z.lt_ge_cases a AIMG_TOP) as [LT|GE].
               + apply IMGW; unfold astatw, sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; clear - HC LT; lia.
               + apply (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL). unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP in *; clear - HC GE; lia.
             - intros a Ha Wv. apply WM'. exact Wv.
             - intros a Ha. destruct AC as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)]. exists b.
               unfold mrd in *. rewrite (AGR a); [exact Hb| | unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia].
               exact (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL Ha). }
    unfold ICf. change (a_AL s') with (a_AL s). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ACONST_ext_pt : forall m m',
    ACONST m ->
    (forall a, 0 <= a < 2^64 -> aconst_addr a -> m' (wa a) = m (wa a)) ->
    (forall a, 0 <= a < 2^64 -> aconst_addr a -> wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None) ->
    (forall a, sh AIMG_LO <= a < sh AIMG_TOP -> exists b, mrd asegs m' (wa a) = Some b) ->
    ACONST m'.
  Proof.
    intros m m' (C1 & C2 & C3) EQ WM RD. split; [|split].
    - apply Forall_forall. intros [a cs] IN. pose proof (proj1 (Forall_forall _ _) C1 _ IN) as RC. cbn in RC |- *.
      assert (R : forall x, a <= x < a + Z.of_nat (cells_size cs) -> aconst_addr x).
      { exact (proj1 (Forall_forall _ _) aconst_cells_in_addr _ IN). }
      destruct RC as [[WF BA] WR]. split; [split; [exact WF|]|].
      + destruct BA as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd. rewrite EQ; [| lia |].
        * apply BB. exact Hi.
        * apply R. rewrite cells_bytes_length in Hi by exact WF. lia.
      + destruct WR as (W0 & W1 & WW). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM; [lia| apply R; lia|]. apply WW. exact Hi.
    - apply Forall_forall. intros [[beg sz] szrz] IN. pose proof (proj1 (Forall_forall _ _) C2 _ IN) as G. cbn in G |- *.
      destruct G as (G0 & G1 & [GB GW]). split; [exact G0|]. split; [exact G1|].
      assert (R : forall x, sh beg <= x < sh beg + Z.of_nat (length (global_shadow sz szrz)) -> aconst_addr x).
      { intros x Hx. unfold aconst_addr. do 16 right.
        pose proof (proj1 (Forall_forall _ _) aglobals_facts _ IN) as IMG. cbn in IMG. destruct IMG as (I1 & I2 & I4 & I5 & I6 & I7).
        rewrite global_shadow_length in Hx by lia.
        unfold sh, nsh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
      split.
      + destruct GB as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd. rewrite EQ; [| lia |].
        * apply BB. exact Hi.
        * apply R. lia.
      + destruct GW as (W0 & W1 & WW). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM; [lia| apply R; lia|]. apply WW. exact Hi.
    - destruct C3 as (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|]. intros a Ha. split.
      + apply WM; [unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia| unfold aconst_addr; do 16 right; exact Ha|]. apply (proj1 (SS a Ha)).
      + apply RD. exact Ha.
  Qed.

  Hypothesis TRLEN : (length (ip_TR p) <= 4000)%nat.   (* [comment removed for export] *)

  Local Ltac tcells := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].

  Theorem inst_free_stmt : free_stmt (KHp p).
  Proof.
    unfold free_stmt, free_stmt_at. cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cf as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_lb_remove KHp].
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m x LB q A n lo B errv mo CH bs sbs.
    intros VIS HP K INB CF BLK SHD SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0.
    destruct x as [s d]. cbn [i_s i_d] in *.
    unfold AsSR.VIS in VIS. unfold AsSR.AKREL in K. cbn [i_s cfg_model] in VIS, K. destruct K as [OK IKx]. destruct IKx as (AMX & DCOV & DTV).
    unfold Irauxv_ok in AUX. unfold AFREE_STACK in LO.
    pose proof HP as HP0. unfold IRHEAP in HP. cbn [i_s i_d] in HP.
    destruct HP as (HR & IDS & LEN & AWV & FLX & DEP & DPL & DTR & DF1 & DF2 & EF & MF & DFD & TH & TLS & ASV & DAP & DSEC & [PI IQ]).
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. pose proof (proj2 OKs) as W. pose proof (proj1 OKs) as PL.
    pose proof (nalloc_le_blocks s (lbp LB) m HR) as NAL. unfold lbp in NAL. rewrite zlen_map in NAL. unfold zlen in NAL.
    unfold ILIVE_CNT_MAX, ADRV_CNT in LEN.
    (* [comment removed for export] *)
    assert (INA : In (A, n) (lbp LB)) by (unfold lbp; apply in_map_iff; exists (q, A, n); split; [reflexivity| exact INB]).
    destruct (alb_In s A n (proj1 (proj2 (proj2 HR) (A, n)) INA)) as (ch & CHIN & ALLOC & EU & EN).
    pose proof (proj1 (Forall_forall _ _) IDS (q, A, n) INB) as [EQA SZB]. cbn [blk_id blk_addr blk_size fst snd] in EQA, SZB.
    (* [comment removed for export] *)
    unfold AsSR.SR.
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo _ OK VIS); [apply free_stub_evt; exact MI|].
    cbv beta. intros msF1 mo1 OK1 SBM1 _ E1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    (* [comment removed for export] *)
    destruct (fch_of_achain m (bv_unsigned sp) (bv_unsigned s0) (a_top s) (a_bot s) (bv_unsigned ra) lo CH HCH CEIL ltac:(lia) SP16 (bv_unsigned_in_range _ ra))
      as (CHg & FCH & UTR).
    assert (PROOM : pusage (a_st s) + COLD_COST <= B_PRIM) by (pose proof (PROOM_of_PINV (a_st s) W PI); unfold COLD_COST; lia).
    assert (ROOM : rg_mapped_user (get_region (a_st s) kBatchClass) + 2 * kUserMapSize <= kFreeArrayOffset).
    { apply (ROOM_of_PINV (a_st s) kBatchClass W PI); [unfold kBatchClass, kNumClasses; lia| vm_compute; discriminate]. }
    subst A n.
    eapply (free_arep ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF1 mo1 _ s (lbp LB) d lo CHg ch bs sbs
              HR CHIN ALLOC (conj AWV FLX) AMX1 DEP DPL (conj DF1 DF2) DCOV1 MI ST CEIL ltac:(clear - LO; lia) SP16 ltac:(clear - AUX SPB; lia) TP
              (dcap_of_tr p TRLEN d DTR) FCH A0 BLK (conj SHD SHL) ltac:(unfold kQuarantineMaxSize; clear - SZB; lia) IQ PI ltac:(unfold LIVEB; clear - NAL LEN; lia) PROOM ROOM OK1).
    { unfold AFREE_ICPT in E1. exact E1. }
    intros msF' mo' PO.
    destruct PO as (s' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
                    & E_thr & E_ctx & E_fsb & E_zr & E_top & E_bot & SUB & AL
                    & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & FR' & AVI' & CP' & AVX' & MODEL).
    destruct MODEL as (st'' & ev & MK & SBS).
    set (T := utrace 1831612 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg)) in *.
    set (d' := d_put d (depot_hash T) (Z.of_nat (length T))) in *.
    set (U := ch_user_beg ch) in *.
    pose proof (proj1 HR') as R'. pose proof (proj1 R') as OKs'. pose proof (proj2 OKs') as W'. pose proof (proj1 OKs') as PL'.
    (* [comment removed for export] *)
    destruct (am_free_full_sbpa (a_st s) U st'' ev W MK) as [ESB0 EPA0].
    pose proof SBS as (Xsb & Xpa & _).
    assert (ESB : a_sb s' = a_sb s) by (unfold a_sb; rewrite <- Xsb; exact ESB0).
    assert (EPA : a_pa s' = a_pa s) by (unfold a_pa; rewrite <- Xpa; exact EPA0).
    assert (PI' : PINVI (a_st s')).
    { assert (SC : same_core (a_st s') st'') by (apply same_core_sbs; unfold same_but_shadow in SBS |- *; intuition congruence).
      split.
      - apply (PINV_core (a_st s') st'' SC). apply (PINV_am_free_full (a_st s) U st'' ev W PI ltac:(unfold LIVEB; clear - NAL LEN; lia) MK).
      - apply (INITQ_core (a_st s') st'' SC). exact (proj1 (am_free_full_initq (a_st s) U st'' ev W IQ MK)). }
    (* [comment removed for export] *)
    pose proof (UTR (ip_TR p) 1831612 30 ltac:(lia) TR) as TIN. fold T in TIN.
    pose proof (utrace_length 1831612 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg) ltac:(lia)) as TL. fold T in TL.
    assert (DTR' : depot_tr p d').
    { apply (depot_tr_put p TRLEN d (depot_hash T) (Z.of_nat (length T)) (proj1 DEP) DTR); [apply in_map_iff; exists T; split; [reflexivity| exact TIN]| lia]. }
    destruct (d_put_blocks d (depot_hash T) (Z.of_nat (length T))) as [DNB DSB]. fold d' in DNB, DSB.
    (* [comment removed for export] *)
    pose proof TH as (TH1 & TH2 & DPOS & DM8 & DCE & AKD).
    pose proof CP' as AG'. unfold acompl in AG'.
    assert (AGR : agree_on (fun a => ~ awrit s s' d lo (bv_unsigned sp) a) m m') by (intros x0 Hx Hr; exact (AG' x0 Hr Hx)).
    pose proof (vis_off_awrit s s' PL d lo (bv_unsigned sp) m m' AVI') as VOFF.
    assert (DTV1 : dtv_cov p mo1) by (intros x0 Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DTV x0 Hx)).
    assert (IMGW : forall a, AIMG_LO <= a < AIMG_TOP -> ~ astatw a -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a H1 H2. exact (image_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL H1 H2). }
    assert (DTVW : forall a, ip_D p <= a < ip_D p + 32 -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a Ha. exact (dtv_not_written p s s' d lo (bv_unsigned sp) mo1 mo' a PL PL' E_thr ESB EPA CEIL AKD DCE DPOS DAP DSEC DTV1 AVX' Ha). }
    assert (ELB : lbp (Ilb_remove q LB) = lb_remove U (lbp LB)) by (rewrite (lbp_remove q LB IDS), EQA; reflexivity).
    assert (RH' : IRHEAP p (IST s' d') (Ilb_remove q LB) m').
    { unfold IRHEAP. cbn [i_s i_d].
      split; [rewrite ELB; exact HR'|].
      split; [apply Forall_forall; intros b Hb; exact (proj1 (Forall_forall _ _) IDS b (proj1 (Ilb_remove_incl q LB b Hb)))|].
      split; [pose proof (Ilb_remove_length q LB) as LL; unfold ILIVE_CNT_MAX, ADRV_CNT; clear - LL LEN; lia|].
      split; [exact AWV'|]. split; [exact FX'|]. split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DTR'|].
      split; [rewrite E_fsb, DNB; exact DF1|]. split; [rewrite E_fsb, DSB; exact DF2|].
      split; [rewrite E_fsb; exact EF|]. split; [exact MF|]. split; [rewrite E_fsb; exact DFD|].
      split.
      { unfold ATHR. split; [| split; [| exact (conj DPOS (conj DM8 (conj DCE AKD)))]].
        - eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF TH1). tcells.
          intros a Ha. apply IMGW; unfold astatw, ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia.
        - eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF TH2). tcells.
          intros a Ha. apply DTVW. lia. }
      split.
      { destruct TLS as (tb & te & TC). exists tb, te. rewrite E_thr. eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF TC). tcells.
        intros a Ha. exact (thread_head_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL ltac:(lia)). }
      split; [exact (proj1 (proj2 (proj1 AMX')))|].
      split; [unfold IDAPART; rewrite ESB, E_thr, EPA, DNB, DSB; exact DAP|].
      split; [| exact PI'].
      intros sc Hsc. exact (DSEC sc (SUB sc Hsc)). }
    apply sreach_done. unfold AsIface.free_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', (IST s' d').
    cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cf as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_FSB as_lb_remove KHp i_s i_d].
    split; [unfold AsSR.VIS; cbn [i_s]; exact VIS'|].
    split. { unfold AsSR.AKREL. cbn [i_s i_d cfg_model cfg_ms]. split; [exact OK'|]. split; [exact AMX'|]. split; [exact DCOV'|].
             intros x0 Hx. destruct (proj1 (AVX' x0 (DTV1 x0 Hx))) as [C|(sc & INs & _ & Rx)]; [exact C| exfalso].
             pose proof (DSEC sc INs) as DS. clear - DS Rx Hx. unfold disj, kPageSize in *. lia. }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat mo mo1 SBM1) NV')|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { rewrite TP. unfold wz. rewrite unsigned_lit by (unfold AsIface.ATP; lia). rewrite TP in ERR. rewrite unsigned_lit in ERR by (unfold AsIface.ATP; lia).
             eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF ERR). tcells.
             intros a Ha. apply IMGW; unfold astatw, AsIface.ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia. }
    split; [exact AUX|].
    split. { (* [comment removed for export] *)
             intros a Ha CL.
             assert (BLKIN : forall b, In b (Ilb_remove q LB) -> In (blk_addr b, blk_size b) (lb_remove U (lbp LB))).
             { intros b Hb. rewrite <- ELB. unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb]. }
             split.
             - apply (FR' a Ha). unfold aclient_addr in CL. unfold aclient. cbn [as_FSB KHp] in CL.
               destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]]; [left; exact C| right; left; exact C| | | | |].
               + right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [exact (BLKIN b Hb)| exact Rb].
               + right; right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [exact (BLKIN b Hb)| exact Rb].
               + do 4 right; left. rewrite EF. exact C.
               + do 5 right; left. rewrite EF. exact C.
               + do 6 right. exact C.
             - intros Wv. destruct (AVI' (wa a) Wv) as [V|G]; [exact V| exfalso]. rewrite wa_unsigned in G by exact Ha.
               revert G. unfold aclient_addr in CL. cbn [as_FSB KHp] in CL.
               destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]].
               + apply (secgone_not_stack s s' PL a lo CEIL). clear - C LO. lia.
               + apply (secgone_not_image s s' PL a). clear - C. unfold aimg_client, AIMG_LO, AIMG_TOP in *. lia.
               + destruct C as (b & Hb & Rb). destruct (alb_In s' _ _ (proj1 (proj2 (proj2 HR') _) (BLKIN b Hb))) as (chb & CHB & _ & EUb & ENb).
                 apply (secgone_not_block s s' PL chb a W OKs' ESB SUB CHB). left. rewrite EUb, ENb. exact Rb.
               + destruct C as (b & Hb & Rb). destruct (alb_In s' _ _ (proj1 (proj2 (proj2 HR') _) (BLKIN b Hb))) as (chb & CHB & _ & EUb & ENb).
                 apply (secgone_not_block s s' PL chb a W OKs' ESB SUB CHB). right. rewrite EUb, ENb. exact Rb.
               + apply (secgone_not_fsb s s' PL a). left. rewrite EF. exact C.
               + apply (secgone_not_fsb s s' PL a). right. rewrite EF. exact C.
               + apply (secgone_not_stkshadow s s' PL a). exact C. }
    split; [exact RH'|].
    split. { (* [comment removed for export] *)
             assert (NWC : forall a, aconst_addr a -> ~ awrit s s' d lo (bv_unsigned sp) a).
             { intros a HC. unfold aconst_addr in HC.
               unfold AsConst.ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AVERBOSITY_CELL,
                 AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL in HC.
               destruct (Z.lt_ge_cases a AIMG_TOP) as [LT|GE].
               + apply IMGW; unfold astatw, sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; clear - HC LT; lia.
               + apply (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL). unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP in *; clear - HC GE; lia. }
             eapply (ACONST_ext_pt m m' AC).
             - intros a Ha HC. apply (AGR a); [exact (NWC a HC)| exact Ha].
             - intros a Ha HC Wv. apply VOFF; [rewrite wa_unsigned by exact Ha; exact (NWC a HC)| exact Wv].
             - intros a Ha. destruct AC as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)]. exists b.
               unfold mrd in *. rewrite (AGR a); [exact Hb| | unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia].
               exact (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL Ha). }
    unfold ICf. unfold FREE_COST in AL. clear - AL. lia.
  Qed.
End Free.
