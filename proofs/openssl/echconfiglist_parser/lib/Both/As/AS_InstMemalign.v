(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Exec CellsX Arr TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain AsUnwind FakeStackRep
     AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepX SecLazy SecGap AsDepotInv AsDepotHash
     AG_WFHit AG_MallocModel AG_Frame AG_WriteSet AW_MallocBase AG_Malloc2 AG_MallocCold AG_MallocLarge3 AG_MallocAll
     AS_InstDefs AS_InstChain AS_InstLaws1 AS_InstLaws2 AS_InstLaws3 AS_InstHeap AsWalk CidBits AW_AllocBaseAl AW_Memalign AG_Memalign2 AG_MemalignCold AG_MemalignTop AsIfaceMemalign AllocWalkKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section Memalign.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.
  Hypothesis TRLEN : (length (ip_TR p) <= 4000)%nat.

  (* [comment removed for export] *)
  Lemma memalign_stub_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                                   (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m ->
    evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 APOSIX_MEMALIGN_ICPT) fc None m (seg_rom asegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 APOSIX_MEMALIGN_STUB) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold APOSIX_MEMALIGN_STUB, APOSIX_MEMALIGN_ICPT. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma le4_surj : forall bs : list byte, length bs = 4%nat -> exists w : word, le4 w = bs.
  Proof.
    intros bs L. exists (Z_to_bv 64 (bytes_le_to_Z bs)). unfold le4. rewrite Z_to_bv_unsigned.
    pose proof (Bytes.le_val_range (map bv_unsigned bs) (Bytes.bytes_ok_map bs)) as R. rewrite <- Bytes.bytes_le_to_Z_le_val in R.
    rewrite length_map, L in R. change (256 ^ Z.of_nat 4) with (2^32) in R.
    change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
  Qed.
  Lemma rw_cells_recell : forall m A cs cs', cells_bytes cs = cells_bytes cs' -> cells_wf cs' -> rw_cells asegs m A cs -> rw_cells asegs m A cs'.
  Proof.
    intros m A cs cs' E WF' [[WF B] W]. split; [split; [exact WF'| rewrite <- E; exact B]|].
    rewrite <- (cells_bytes_length cs' WF'), <- E, (cells_bytes_length cs WF). exact W.
  Qed.
  Lemma stk_C4 : forall m A, stk asegs m A (A + 4) -> exists v, rw_cells asegs m A [C4 v].
  Proof.
    intros m A ST. destruct (stk_cells m A (A + 4) ST ltac:(lia)) as [bs R]. replace (Z.to_nat (A + 4 - A)) with 4%nat in R by lia.
    assert (L : length bs = 4%nat) by (destruct R as [[WF _] _]; exact (proj1 WF)).
    destruct (le4_surj bs L) as [v Ev]. exists v.
    eapply rw_cells_recell; [| | exact R]; [cbn -[le4]; change (cells_bytes [C4 v]) with (le4 v ++ []); rewrite Ev; reflexivity| cbn; repeat split; reflexivity].
  Qed.

  Theorem inst_memalign_stmt : memalign_stmt (KHp p) APOSIX_MEMALIGN_STUB APC0_POSIX_MEMALIGN.
  Proof.
    unfold memalign_stmt. cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cm as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St KHp].
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m x LB MP al n lo B errv mo CH pjunk.
    intros VIS HP K AOK CM AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0 MP8 PW CW ACW MPOFF A1 AL64 A2 SZP.
    destruct x as [s d]. cbn [i_s i_d] in *.
    unfold AsSR.VIS in VIS. unfold AsSR.AKREL in K. cbn [i_s cfg_model] in VIS, K. destruct K as [OK IKx]. destruct IKx as (AMX & DCOV & DTV).
    unfold Ialloc_ok, ILIVE_MAX, ILIVE_CNT_MAX, ADRV_CNT in AOK. destruct AOK as [AOK1 AOK2]. unfold Irauxv_ok in AUX. unfold AMALLOC_STACK in LO.
    pose proof HP as HP0. unfold IRHEAP in HP. cbn [i_s i_d] in HP.
    destruct HP as (HR & IDS & LEN & AWV & FLX & DEP & DPL & DTR & DF1 & DF2 & EF & MF & DFD & TH & TLS & ASV & DAP & DSEC & [PI IQ]).
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. pose proof (proj2 OKs) as W. pose proof (proj1 OKs) as PL.
    pose proof (nalloc_le_blocks s (lbp LB) m HR) as NAL. unfold lbp in NAL. rewrite zlen_map in NAL. unfold zlen in NAL.
    (* [comment removed for export] *)
    unfold AsSR.SR.
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo _ OK VIS); [apply memalign_stub_evt; exact MI|].
    cbv beta. intros msF1 mo1 OK1 SBM1 _ E1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    (* [comment removed for export] *)
    destruct (fch_of_achain m (bv_unsigned sp) (bv_unsigned s0) (a_top s) (a_bot s) (bv_unsigned ra) lo CH HCH CEIL ltac:(lia) SP16 (bv_unsigned_in_range _ ra))
      as (CHg & FCH & UTR).
    (* [comment removed for export] *)
    assert (PR : mprimary n = true) by (rewrite SZP; reflexivity).
    assert (SZ' : 1 <= n /\ round_up (Z.max n 8) 8 + rz_size n <= kMaxSize).
    { rewrite SZP. split; [clear; lia|]. match goal with |- ?x <= ?y => let v := eval vm_compute in x in change x with v end. unfold kMaxSize. clear; lia. }
    assert (PROOM : pusage (a_st s) + COLD_COST <= B_PRIM) by (pose proof (PROOM_of_PINV (a_st s) W PI); unfold COLD_COST; lia).
    assert (ROOM : rg_mapped_user (get_region (a_st s) (class_id (round_up (Z.max n 8) 8 + rz_size n))) + 2 * kUserMapSize <= kFreeArrayOffset).
    { destruct (mneeded_primary n ltac:(lia) PR) as (MN & RP & HC). unfold mneeded in MN, HC. apply (ROOM_of_PINV (a_st s) _ W PI HC). rewrite MN. exact (mused_class_pos n ltac:(lia) RP). }
    (* [comment removed for export] *)
    assert (MPC : forall a, MP <= a < MP + 8 -> aclient s (lbp LB) (bv_unsigned sp) a \/ aceil <= a < lo).
    { intros a Ha. unfold AsIface.aclient_write_ok in CW. cbn [fst snd as_FSB KHp] in CW. unfold aclient.
      destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(b & Hb & B1 & B2)|[C|[C|C]]]]]]; cbn [fst snd] in *.
      - destruct MPOFF as [M|M]; [right; clear - C M Ha CEIL; lia| left; left; clear - M Ha; lia].
      - left. right. left. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, AsIface.ATP in C. clear - C Ha. lia.
      - left. right. right. left. exists (blk_addr b), (blk_size b). split; [unfold lbp; apply in_map_iff; exists b; split; [reflexivity| exact Hb]| clear - B1 B2 Ha; lia].
      - left. do 3 right. left. exists (blk_addr b), (blk_size b). split; [unfold lbp; apply in_map_iff; exists b; split; [reflexivity| exact Hb]| clear - B1 B2 Ha; lia].
      - left. do 4 right. left. rewrite EF. unfold AsIface.AFS_SIZE, AllocRep.AFS_SIZE in *. cbn [as_FSB KHp] in C. clear - C Ha. lia.
      - left. do 5 right. left. rewrite EF. unfold AsIface.AFS_SIZE, AllocRep.AFS_SIZE in *. cbn [as_FSB KHp] in C. clear - C Ha. lia.
      - left. do 6 right. clear - C Ha. lia. }
    assert (MPR : 0 <= MP /\ MP + 8 <= 2^64) by (pose proof (rw_cells_bound _ _ _ _ PW) as BB; cbn in BB; clear - BB; lia).
    eapply (memalign_arep_prim ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF1 mo1 _ s (lbp LB) d lo n CHg
              HR (conj AWV FLX) AMX1 DEP DPL (conj DF1 DF2) DCOV1 MI ST CEIL ltac:(clear - LO; lia) SP16 ltac:(clear - AUX SPB; lia) SZ' TP
              (dcap_of_tr p TRLEN d DTR) FCH PROOM ROOM OK1 E1 MP pjunk A0 ltac:(rewrite A1, AL64; reflexivity) A2 ltac:(constructor; exact SZP) MPR MPC PW).
    intros msF' mo' PO.
    destruct PO as (s' & U & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & m' & E_thr & E_ctx & E_fsb & E_zr & E_top & E_bot & E_sec & AL
                    & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI1 & ST1 & FR' & WM' & CP' & AVX' & [junk BLK] & ADDR & MODEL
                    & UA & MU4 & WM4 & MI4 & PW4 & ST4 & [junk4 BLK4] & ADDR4 & EQM).
    destruct (MODEL 0) as (st'' & ev & MK & SBS).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (T := utrace 1833880 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg)) in *.
    set (d' := d_put d (depot_hash T) (Z.of_nat (length T))) in *.
    pose proof (proj1 HR') as R'. pose proof (proj1 R') as OKs'. pose proof (proj2 OKs') as W'. pose proof (proj1 OKs') as PL'.
    assert (W'' : WF st'') by (exact (WF_sbs st'' (a_st s') SBS W')).
    destruct (am_malloc_k_ptr_array (a_st s) n 0 U st'' ev W MK) as [EPA0 ESB0].
    pose proof SBS as (Xsb & Xpa & _).
    assert (ESB : a_sb s' = a_sb s) by (unfold a_sb; rewrite <- Xsb; exact ESB0).
    assert (EPA : a_pa s' = a_pa s) by (unfold a_pa; rewrite <- Xpa; exact EPA0).
    assert (FIND : exists chn, PositiveMap.find (ckey U) (as_chunks st'') = Some chn /\ ch_user_beg chn = U /\ ch_used chn = rq_size (compute_req n)).
    { destruct (am_malloc_k_frame (a_st s) n 0 U st'' ev W MK) as (st1 & allocated & cls & CORE & EU & _).
      destruct CORE as (_ & _ & _ & _ & _ & _ & _ & CHE & _). cbn [as_chunks upd_chunk set_chunks] in CHE.
      exists (mk_new allocated (compute_req n) cls). rewrite CHE.
      replace (ch_user_beg (mk_new allocated (compute_req n) cls)) with U by (cbn [ch_user_beg mk_new]; lia).
      split; [apply PositiveMap.gss|]. cbn [ch_user_beg ch_used mk_new]. split; [lia| reflexivity]. }
    pose proof (no_live_at_new s s' (lbp LB) m m1 U n st'' HR HR' SBS FIND ltac:(lia)) as NOLIVE.
    assert (PI' : PINVI (a_st s')).
    { assert (SC : same_core (a_st s') st'') by (apply same_core_sbs; unfold same_but_shadow in SBS |- *; intuition congruence).
      split.
      - apply (PINV_core (a_st s') st'' SC). apply (PINV_am_malloc_k (a_st s) n 0 U st'' ev W W'' PI ltac:(unfold LIVEB; lia) NOLIVE MK).
      - apply (INITQ_core (a_st s') st'' SC). exact (am_malloc_k_initq (a_st s) n 0 U st'' ev W IQ MK). }
    pose proof (UTR (ip_TR p) 1833880 30 ltac:(lia) TR) as TIN. fold T in TIN.
    pose proof (utrace_length 1833880 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg) ltac:(lia)) as TL. fold T in TL.
    assert (DTR' : depot_tr p d').
    { apply (depot_tr_put p TRLEN d (depot_hash T) (Z.of_nat (length T)) (proj1 DEP) DTR); [apply in_map_iff; exists T; split; [reflexivity| exact TIN]| lia]. }
    destruct (d_put_blocks d (depot_hash T) (Z.of_nat (length T))) as [DNB DSB]. fold d' in DNB, DSB.
    pose proof TH as (TH1 & TH2 & DPOS & DM8 & DCE & AKD).
    pose proof CP' as AG'. unfold acompl in AG'.
    assert (AGR : agree_on (fun a => ~ awrit s s' d lo (bv_unsigned sp) a) m m1) by (intros x Hx Hr; exact (AG' x Hr Hx)).
    assert (DTV1 : dtv_cov p mo1) by (intros x Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DTV x Hx)).
    assert (IMGW : forall a, AIMG_LO <= a < AIMG_TOP -> ~ astatw a -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a H1 H2. exact (image_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL H1 H2). }
    assert (DTVW : forall a, ip_D p <= a < ip_D p + 32 -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a Ha. exact (dtv_not_written p s s' d lo (bv_unsigned sp) mo1 mo' a PL PL' E_thr ESB EPA CEIL AKD DCE DPOS DAP DSEC DTV1 AVX' Ha). }
    assert (RH1 : IRHEAP p (IST s' d') ((U, U, n) :: LB) m1).
    { unfold IRHEAP. cbn [i_s i_d lbp map blk_addr blk_size blk_id fst snd].
      split; [exact HR'|].
      split; [constructor; [cbn; split; [reflexivity| lia]| exact IDS]|].
      split; [cbn [length]; rewrite Nat2Z.inj_succ; unfold ILIVE_CNT_MAX, ADRV_CNT; lia|].
      split; [exact AWV'|]. split; [exact FX'|]. split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DTR'|].
      split; [rewrite E_fsb, DNB; exact DF1|]. split; [rewrite E_fsb, DSB; exact DF2|].
      split; [rewrite E_fsb; exact EF|]. split; [exact MF|]. split; [rewrite E_fsb; exact DFD|].
      split.
      { unfold ATHR. split; [| split; [| exact (conj DPOS (conj DM8 (conj DCE AKD)))]].
        - eapply (rw_cells_transport_pt _ m m1 AGR WM'); [exact TH1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
          intros a Ha. apply IMGW; unfold astatw, ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia.
        - eapply (rw_cells_transport_pt _ m m1 AGR WM'); [exact TH2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
          intros a Ha. apply DTVW. lia. }
      split.
      { destruct TLS as (tb & te & TC). exists tb, te. rewrite E_thr. eapply (rw_cells_transport_pt _ m m1 AGR WM'); [exact TC|].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length]. intros a Ha.
        exact (thread_head_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL ltac:(lia)). }
      split; [exact (proj1 (proj2 (proj1 AMX')))|].
      split; [unfold IDAPART; rewrite ESB, E_thr, EPA, DNB, DSB; exact DAP|].
      split; [| exact PI'].
      intros sc Hsc. destruct (in_dec schunk_eq_dec sc (as_sec (a_st s))) as [INs|NIs]; [exact (DSEC sc INs)|].
      exfalso. rewrite E_sec in Hsc. exact (NIs Hsc). }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (CW' : AsIface.aclient_write_ok (KHp p) ((U, U, n) :: LB) (MP, MP + 8)).
    { unfold AsIface.aclient_write_ok in CW |- *. cbn [fst snd as_FSB KHp] in CW |- *.
      destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(b & Hb & B1 & B2)|[C|[C|C]]]]]].
      - left; exact C. - right; left; exact C.
      - right; right; left. exists b. split; [right; exact Hb| exact (conj B1 B2)].
      - right; right; right; left. exists b. split; [right; exact Hb| exact (conj B1 B2)].
      - do 4 right; left; exact C. - do 5 right; left; exact C. - do 6 right; exact C. }
    assert (RH4 : IRHEAP p (IST s' d') ((U, U, n) :: LB) m').
    { pose proof (inst_RHEAP_frame p) as RF. unfold RHEAP_frame in RF. cbn [as_RHEAP KHp] in RF.
      apply (RF (IST s' d') ((U, U, n) :: LB) m1 m' [(MP, MP + 8)]%Z RH1 MU4 WM4). constructor; [exact CW'| constructor]. }
    (* [comment removed for export] *)
    assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
    { rewrite TP in ERR |- *. unfold wz. rewrite unsigned_lit in ERR |- * by (unfold AsIface.ATP; lia).
      eapply (rw_cells_transport_pt _ m m1 AGR WM'); [exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length].
      intros a Ha. apply IMGW; unfold astatw, AsIface.ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia. }
    assert (ERR4 : exists errv', rw_cells asegs m' (errno_addr tp) [C4 errv']).
    { rewrite TP in ERR1 |- *. rewrite unsigned_lit in ERR1 |- * by (unfold AsIface.ATP; lia).
      destruct (Z.le_gt_cases (MP + 8) (0xbe1c90 + -164)) as [D1|D1]; [| destruct (Z.le_gt_cases (0xbe1c90 + -164 + 4) MP) as [D2|D2]].
      - exists errv. rewrite EQM. apply rw_cells_frame; [exact ERR1| clear - MPR; lia| cbn; clear - MPR; lia| cbn; unfold AsIface.ATP in *; clear - D1 MPR; lia].
      - exists errv. rewrite EQM. apply rw_cells_frame; [exact ERR1| clear - MPR; lia| cbn; clear - MPR; lia| cbn; unfold AsIface.ATP in *; clear - D1 D2 MPR; lia].
      - (* [comment removed for export] *)
        assert (EMP : MP = 0xbe1c90 + -164 - 4) by (clear - D1 D2 MP8; Z.div_mod_to_equations; lia).
        assert (P8 : rw_cells asegs m' MP [CB 8 (le8 (Z_to_bv 64 U))]) by (eapply rw_cells_recell; [| | exact PW4]; [reflexivity| cbn -[le8]; split; [apply length_le8| exact I]]).
        apply (rw_cells_split_CB asegs _ _ [] 8 (le8 (Z_to_bv 64 U)) [] [4;4]%nat) in P8; [| reflexivity]. cbn [mk_CB_cells app] in P8.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in P8. destruct P8 as [_ P4]. cbn [cells_size csize Nat.add] in P4.
        replace (MP + Z.of_nat 4) with (0xbe1c90 + -164) in P4 by lia.
        lazymatch type of P4 with rw_cells _ _ _ [CB 4 ?bs4] =>
          assert (L4 : length bs4 = 4%nat) by (destruct P4 as [[WF _] _]; exact (proj1 WF));
          destruct (le4_surj _ L4) as [v Ev]; exists v;
          eapply rw_cells_recell; [| | exact P4]; [change (cells_bytes [CB 4 bs4]) with (bs4 ++ []); change (cells_bytes [C4 v]) with (le4 v ++ []); rewrite Ev; reflexivity| cbn; repeat split; reflexivity]
        end. }
    destruct ERR4 as [errv' ERR4].
    (* [comment removed for export] *)
    assert (AC1 : ACONST m1).
    { eapply (ACONST_ext m m1 AC).
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
    assert (LEN8 : length (le8 (wz U)) = 8%nat) by apply length_le8.
    assert (AC4 : ACONST m').
    { eapply (ACONST_ext m1 m' AC1).
      - intros a Ha HC. rewrite EQM. rewrite (write_to_mem_spec (le8 (wz U)) m1 MP (wa a)) by (rewrite ?LEN8; clear - MPR; lia).
        rewrite wa_unsigned by exact Ha. rewrite LEN8.
        replace ((MP <=? a) && (a <? MP + Z.of_nat 8))%bool with false; [reflexivity|].
        symmetry. apply Bool.andb_false_iff. pose proof (ACW a) as NA. cbn [fst snd] in NA.
        destruct (Z.le_gt_cases MP a); [right; apply Z.ltb_ge| left; apply Z.leb_gt; lia]. destruct (Z.lt_ge_cases a (MP + 8)); [exfalso; exact (NA ltac:(lia) HC)| lia].
      - intros a Ha Wv. apply WM4. exact Wv.
      - intros a Ha. destruct AC1 as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)].
        unfold mrd in *. rewrite EQM. rewrite (write_to_mem_spec (le8 (wz U)) m1 MP (wa a)) by (rewrite ?LEN8; clear - MPR; lia).
        assert (Ra : 0 <= a < 2^64) by (unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in Ha; clear - Ha; lia). rewrite wa_unsigned by exact Ra. rewrite LEN8.
        destruct ((MP <=? a) && (a <? MP + Z.of_nat 8))%bool eqn:E.
        + apply andb_prop in E. destruct E as [Ea Eb]. apply Z.leb_le in Ea. apply Z.ltb_lt in Eb.
          destruct (nth_error (le8 (wz U)) (Z.to_nat (a - MP))) as [b'|] eqn:N; [exists b'; reflexivity|].
          exfalso. apply nth_error_None in N. rewrite LEN8 in N. clear - N Ea Eb. lia.
        + exists b. exact Hb. }
    (* [comment removed for export] *)
    apply sreach_done. unfold memalign_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv', U, junk4, U, (IST s' d').
    cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cm as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_FSB KHp i_s i_d].
    split; [unfold AsSR.VIS; cbn [i_s]; exact VIS'|].
    split. { unfold AsSR.AKREL. cbn [i_s i_d cfg_model cfg_ms]. split; [exact OK'|]. split; [exact AMX'|]. split; [exact DCOV'|].
             intros x Hx. destruct (proj1 (AVX' x (DTV1 x Hx))) as [C|(sc & INs & _ & Rx)]; [exact C| exfalso].
             pose proof (DSEC sc INs) as DS. clear - DS Rx Hx. unfold disj, kPageSize in *. lia. }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat mo mo1 SBM1) NV')|].
    split; [exact MI4|]. split; [exact ST4|].
    split; [exact ERR4|].
    split; [exact AUX|].
    split. { (* [comment removed for export] *)
             intros a Ha CL.
             assert (CLa : aclient s (lbp LB) (bv_unsigned sp) a).
             { unfold aclient_addr in CL. unfold aclient. cbn [as_FSB KHp] in CL.
               destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]]; [left; exact C| right; left; exact C| | | | |].
               - right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [| exact Rb].
                 unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
               - right; right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [| exact Rb].
                 unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
               - do 4 right; left. rewrite EF. exact C.
               - do 5 right; left. rewrite EF. exact C.
               - do 6 right. exact C. }
             rewrite EQM. unfold wz.
             rewrite (write_to_mem_spec (le8 (Z_to_bv 64 U)) m1 MP (wa a)), (write_to_mem_spec (le8 (Z_to_bv 64 U)) m MP (wa a)) by (rewrite ?LEN8; clear - MPR; lia).
             rewrite wa_unsigned by exact Ha.
             split.
             - destruct ((MP <=? a) && (a <? MP + Z.of_nat (length (le8 (Z_to_bv 64 U)))))%bool; [reflexivity|]. exact (FR' a Ha CLa).
             - intros Wv. destruct ((MP <=? a) && (a <? MP + Z.of_nat (length (le8 (Z_to_bv 64 U)))))%bool eqn:E.
               + (* [comment removed for export] *)
                 unfold wview. rewrite (write_to_mem_spec (le8 (Z_to_bv 64 U)) m1 MP (wa a)) by (rewrite ?LEN8; clear - MPR; lia). rewrite wa_unsigned by exact Ha. rewrite E.
                 destruct (nth_error (le8 (Z_to_bv 64 U)) (Z.to_nat (a - MP))) as [b'|] eqn:N; [discriminate|].
                 exfalso. apply nth_error_None in N. unfold wz in LEN8. rewrite LEN8 in N, E. apply andb_prop in E. destruct E as [Ea Eb]. apply Z.leb_le in Ea. apply Z.ltb_lt in Eb. clear - N Ea Eb. lia.
               + apply wview_write_mono. apply WM'. revert Wv. unfold wview. rewrite (write_to_mem_spec (le8 (Z_to_bv 64 U)) m MP (wa a)) by (rewrite ?LEN8; clear - MPR; lia).
                 rewrite wa_unsigned by exact Ha. rewrite E. exact (fun H => H). }
    split; [exact (inst_RHEAP_block_range p (IST s' d') ((U, U, n) :: LB) m' (U, U, n) RH4 (or_introl eq_refl))|].
    split; [rewrite AL64; exact UA|].
    split; [exact RH4|].
    split; [exact BLK4|]. split; [exact ADDR4|].
    split; [exact PW4|].
    split; [exact AC4|].
    (* [comment removed for export] *)
    pose proof (proj1 (inst_cost_laws p) (n + al) ltac:(lia)) as CM0. cbn [as_Cm KHp] in CM0 |- *. clear - AL CM0. lia.
  Qed.
End Memalign.
