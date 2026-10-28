(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_ALibMF ECH_ALibOK
  ECH_AC7_new ECH_AC7_newmembuf ECH_AC7_free ECH_AC7_biofreeint ECH_AC7_biofree ECH_AC9_new ECH_AC9_bionew ECH_AC9_free ECH_AC9_biofreeb64 ECH_AC9_freeall.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Hypothesis CFX : cfreeex_stmt H.

  Local Ltac mpacc MPA0 MP := let T := fresh "MPX" in pose proof (ah_mpres_trans H HH _ _ _ MPA0 MP) as T; clear MPA0 MP; rename T into MPA0.
  Local Ltac hlia := first [lia | unfold hidden in *; lia].
  Local Ltac fw := repeat (apply Forall_cons; [try unfold win_lib_ok; cbn [fst snd]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, ATLS_PRIV_LO, ATP, memflag_foot, A_mem_inited; rewrite ?ASHADOW_BASE_val|]); try apply Forall_nil.

  Lemma abiofreeall_spec : biofreeall_stmt H.
  Proof.
    unfold biofreeall_stmt. intros until CH.
    intros VIS A0 BU APART NXT ENC MB MNX MAPART CPH ND7 SHD MSHD ST0 HP KREL AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM METHB METH RL RFS LFB CHN CHS PF HAL RAE.
    unfold BIOFREEALL_STACK, FR_BIO_free_all in LO.
    assert (BST1 : 0 <= BIOFREEINT_B64_STACK).
    { unfold BIOFREEINT_B64_STACK, B64FREE_STACK, ENCFREE_STACK, BIOACC_STACK, CFREE_STACK, AFREE_STACK, AINTRIN_STACK, CFREEEX_STACK, FR_BIO_free_int, FR_b64_free,
        FR_EVP_ENCODE_CTX_free, FR_BIO_set_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETDEFCTX_STACK, FR_CRYPTO_free_ex_data, FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, AFS_STACK. lia. }
    assert (BST2 : 0 <= BIOFREEINT_STACK).
    { unfold BIOFREEINT_STACK, MEMFREE_STACK, BUFFREE_STACK, CFREE_STACK, CFREEEX_STACK, AFREE_STACK, FR_BIO_free_int, FR_mem_free, FR_mem_buf_free, FR_BUF_MEM_free,
        GETGLOBAL_READY_STACK, NEWEX_INNER, GETDEFCTX_STACK, FR_CRYPTO_free_ex_data, FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, AFS_STACK. lia. }
    remember BIOFREEINT_B64_STACK as BS1 eqn:EBS1. remember BIOFREEINT_STACK as BS2 eqn:EBS2.
    unfold BIOFREEALL_COST in HAL. remember (BIOFREEINT_B64_COST H) as CO1 eqn:ECO1. remember (BIOFREE_COST H) as CO2 eqn:ECO2.
    pose proof (ah_costs H HH) as (_ & _ & CF0 & _).
    assert (CO2P : 0 <= CO2).
    { rewrite ECO2. unfold BIOFREE_COST, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      pose proof (CF0 0 ltac:(lia)). pose proof (CF0 16 ltac:(lia)). pose proof (CF0 32 ltac:(lia)). pose proof (CF0 128 ltac:(lia)). lia. }
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ ST0) as [S0LO S0HI]. unfold AAPP_HI in S0HI.
    (* [comment removed for export] *)
    pose proof BU as (BA & _ & BLK). pose proof BLK as (I1 & I2 & I3 & BR1 & BR2 & BR3 & FLR & RTR & NRD & NXR & PRV).
    pose proof BR1 as (AP & AAL & _ & AH & ACE & AFS & AAP). unfold AIMG_TOP in AH. unfold BIO_SIZE in ACE, AFS, AAP, I1. unfold B64CTX_SIZE in I2.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & ATOP & _). unfold AAPP_HI in ATOP.
    pose proof BR2 as (CP & _ & _ & CH0 & CCE & _ & CAP). unfold AIMG_TOP in CH0. unfold B64CTX_SIZE in CCE, CAP.
    pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & CTOP & _). unfold AAPP_HI in CTOP.
    pose proof SHD as (ADA & _). unfold BIO_SIZE in ADA.
    assert (ACCA : accessible m a 128) by (eapply addressable_accessible; [exact ADA| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    pose proof MB as (MBA & MBB & MBM & MBR & J1 & J2 & J3 & J4 & MR1 & MR2 & MR3 & MR4 & POSR & LENR & BUFP & BUFH & MFLR & RDO & F128 & NUMF & NRD1 & NRD2 & MNXR & MPVR).
    hide RDO. hide F128.
    pose proof MR1 as (MP & MAL & _ & MH & MCE & MFS & MAP). pose proof MR2 as (BBP & _ & _ & BBH & BBCE & BBFS & BBAP).
    pose proof MR3 as (BMP & _ & _ & BMH & BMCE & BMFS & BMAP). pose proof MR4 as (RPP & _ & _ & RPH & RPCE & RPFS & RPAP).
    unfold AIMG_TOP in MH, BBH, BMH, RPH. unfold BIO_SIZE in MCE, MFS, MAP, J1. unfold BIOBUFMEM_SIZE in BBCE, BBFS, BBAP, J2. unfold BUFMEM_SIZE in BMCE, BMFS, BMAP, RPCE, RPFS, RPAP, J3, J4.
    hide AFS. hide MFS. hide BBFS. hide BMFS. hide RPFS.
    (* [comment removed for export] *)
    pose proof CPH as CPH0. cbn [CTXPH] in CPH. destruct CPH as [CS [EX (po & pi & O1 & O2)]].
    pose proof EX as (EXI & EXSZ & EXAR & EXMU). unfold MUTEX_SIZE in EXSZ, EXAR. remember (blk_addr (cx_exlock x)) as ea eqn:EA.
    pose proof (ah_blocks H HH _ _ _ _ HP EXI) as (_ & _ & _ & EH2 & ECE2 & EFS2 & EAP2). cbn [blk_size snd] in EH2, ECE2, EFS2, EAP2.
    rewrite <- ?EA, ?EXSZ in EH2. rewrite <- ?EA, ?EXSZ in ECE2. rewrite <- ?EA, ?EXSZ in EFS2. rewrite <- ?EA, ?EXSZ in EAP2. unfold AIMG_TOP in EH2.
    (* [comment removed for export] *)
    assert (NEM1 : blk_id (cx_exlock x) <> mb_id M) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI J1 ltac:(rewrite EXSZ; cbn; lia))).
    assert (NEM2 : blk_id (cx_exlock x) <> mb_bbid M) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI J2 ltac:(rewrite EXSZ; cbn; lia))).
    assert (NEM3 : blk_id (cx_exlock x) <> mb_bmid M) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI J3 ltac:(rewrite EXSZ; cbn; lia))).
    assert (NEM4 : blk_id (cx_exlock x) <> mb_rpid M) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI J4 ltac:(rewrite EXSZ; cbn; lia))).
    pose proof (ah_disj H HH _ _ _ _ _ HP EXI J1 NEM1) as DJ_E_M. pose proof (ah_disj H HH _ _ _ _ _ HP EXI J2 NEM2) as DJ_E_BB.
    pose proof (ah_disj H HH _ _ _ _ _ HP EXI J3 NEM3) as DJ_E_BM. pose proof (ah_disj H HH _ _ _ _ _ HP EXI J4 NEM4) as DJ_E_RP.
    rewrite <- ?EA, ?EXSZ in DJ_E_M. rewrite <- ?EA, ?EXSZ in DJ_E_BB. rewrite <- ?EA, ?EXSZ in DJ_E_BM. rewrite <- ?EA, ?EXSZ in DJ_E_RP.
    cbn [blk_addr blk_size fst snd] in DJ_E_M, DJ_E_BB, DJ_E_BM, DJ_E_RP. hide DJ_E_M. hide DJ_E_BB. hide DJ_E_BM. hide DJ_E_RP.
    hide NEM1. hide NEM2. hide NEM3. hide NEM4.
    hide ND7.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afa_seg1 with (lo := lo) (a := a) (B := b64f_bio R);
      cbn [b64f_bio bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite];
      first [exact A0| exact AAP| exact BA| exact ACCA| exact AC| exact ST| exact CEIL| exact MI| clear - AAL; lia| unfold A_b64_method; lia| lia]|].
    intros msF1 mo1 KREL1 MPA (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FRj1 & SL1 & FRh1). cbn [b64f_bio bio_next] in VIS1. rewrite NXT in VIS1.
    assert (CW1 : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (LW1 : Forall (win_lib_ok LB) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (NSW1 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [cbn; unfold AHI_LO; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| lia]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across7; [exact RL| exact MU1| constructor; [cbn; lia| constructor]]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_across_wins H HH); [exact RFS| exact MU1| exact WM1| constructor; [left; cbn; lia| constructor]]).
    assert (CPH1 : CTXPH LB m1 (CtxReady x)) by (eapply CTXPH_frame; [exact CPH0| eapply (magree_lib_munch H HH); [exact HP| auto| exact MU1| exact WM1| exact LW1]]).
    assert (BU1 : B64F_used H LB m1 a R).
    { destruct BU as (BA0 & (hdr & junk & elen & LH & LJ & ELR & BC) & _). split; [| split; [exists hdr, junk, elen| exact BLK]].
      - eapply rw_cells_transport; [exact BA0| exact MU1| exact WM1| cbn; lia].
      - split; [exact LH|]. split; [exact LJ|]. split; [exact ELR|].
        eapply rw_cells_transport; [exact BC| exact MU1| exact WM1| cbn; lia]. }
    assert (ENC1 : ENCCTX H LB m1 (bf_enc R) d (bf_eid R)).
    { destruct ENC as (raw & line & L80 & FD & ENCC & LR & EIN & EBR & DU). exists raw, line. pose proof EBR as (_ & _ & _ & _ & ECE' & _). unfold ENCCTX_SIZE in ECE'.
      split; [exact L80|]. split; [exact FD|]. split; [eapply rw_cells_transport; [exact ENCC| exact MU1| exact WM1| cbn; lia]|].
      split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DU]. }
    assert (SHD1 : B64F_shad m1 a R).
    { pose proof BR3 as (_ & _ & _ & _ & _ & _ & EAP). destruct SHD as (S1 & S2 & S3).
      split; [| split]; (eapply addressable_across2; [eassumption| eassumption| exact MU1| exact WM1| exact NSW1]). }
    assert (MB1 : MEMBIO H LB m1 mb M) by (eapply MEMBIO_frame_disj7; [exact MB| exact MU1| exact WM1| ..]; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; cbn; lia).
    assert (MSHD1 : MEMBIO_shad m1 mb M) by (eapply MEMBIO_shad_across2; [exact MB| exact MSHD| exact MU1| exact WM1| exact NSW1]).
    assert (ST01 : stack0 m1 lo (bv_unsigned sp)) by (eapply stack0_transport; [exact ST0| exact MU1| exact WM1| constructor; [apply stack0_ok_app; cbn; unfold AHI_LO; lia| constructor]]).
    assert (CHN0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    set (CH1 := (bv_unsigned sp, bv_unsigned ra) :: CH).
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) CH1).
    { eapply (ah_chain_cons H HH); [exact CHN0| lia| lia| exact SPA| lia| lia|].
      pose proof FRh1 as FR. change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp - 16) in FR by (cbn; lia) end. rewrite !Z_to_bv_bv_unsigned. exact FR. }
    assert (CHS1 : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -48 + 16 <= fp') by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (CHR1 : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -36 + 4 <= fp' - 16 \/ fp' <= bv_unsigned sp + -36) by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    clear CHN0 KREL VIS.
    (* [comment removed for export] *)
    pose proof (abiofreeint_b64_spec H HH CFX) as C1. unfold biofreeint_b64_stmt in C1.
    eapply (ah_seq H HH).
    { eapply C1 with (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (a := a) (rbp := bv_unsigned sp + -36) (shi := bv_unsigned sp) (R := R) (d := d) (CH := CH1);
        [exact VIS1| reflexivity| reflexivity| exact SL1| ..]; rewrite ?unsigned_lit by (unfold AFA_RA, R_BIO_free_all_BIO_free_int; clear - SPR LO LO0 BST1 BST2; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- stack0 _ _ _ => exact ST01
           | |- B64F_used _ _ _ _ _ => exact BU1
           | |- B64F_apart _ _ => exact APART
           | |- ENCCTX _ _ _ _ _ _ => exact ENC1
           | |- B64F_shad _ _ _ => exact SHD1
           | |- CTXPH _ _ _ => exact CPH1
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 4 = 0 => clear - SPA SPR; Z.div_mod_to_equations; lia
           | |- ACONST _ => exact AC1
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- METH_b64 _ => exact (METHB_of_relro _ RL1)
           | |- METH_mem _ => exact (METH_of_relro _ RL1)
           | |- arelro_lib _ => exact RL1
           | |- as_RFS _ _ _ => exact RFS1
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- as_chain _ _ _ _ => exact CHN1
           | |- forall fp' ra', In _ _ -> _ + 16 <= fp' => exact CHS1
           | |- forall fp' ra', In _ _ -> _ \/ _ => exact CHR1
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_biofreeall, AFA_RA, pf_shift; intros q Hq; rewrite map_app; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => rewrite <- ?ECO1; clear - HAL CO2P; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | rewrite <- ?EBS1, <- ?EBS2; clear - SPR SPB LO LO0 BST1 BST2 CEIL S0HI; lia]
           end | idtac "C1-FAIL:" G; fail ] end. }
    clear C1. intros [msF2 mo2] PO. unfold biofreeint_b64_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LB1 & XS1 &
                    VIS2 & MP2 & KREL2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & HEAP2 & PERM1 & MF2 & IM2 & GM2 & METHB2 & METH2 & RL2 & CPH2 & SL2 & ST02 & FXS1 & RFS2 & XP2 & AL2). mpacc MPA MP2.
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia). rewrite <- EA in XP2. rewrite <- ?ECO1 in AL2.
    assert (SUB1 : forall b, In b LB1 -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PERM1)); apply in_or_app; right; exact Hb).
    (* [comment removed for export] *)
    assert (JJ : In (mb_id M, mb, 128) LB1 /\ In (mb_bbid M, mb_bb M, 16) LB1 /\ In (mb_bmid M, mb_bm M, 32) LB1 /\ In (mb_rpid M, mb_rp M, 32) LB1).
    { unhide ND7. cbn [map blk_id blocks_B64F blocks_MEMBIO app fst snd] in ND7.
      apply NoDup_cons_iff in ND7 as [N1 ND7]. apply NoDup_cons_iff in ND7 as [N2 ND7]. apply NoDup_cons_iff in ND7 as [N3 _].
      repeat (apply not_in_cons in N1 as [? N1]). repeat (apply not_in_cons in N2 as [? N2]). repeat (apply not_in_cons in N3 as [? N3]).
      assert (KEEP : forall b, In b LB -> b <> (bf_id R, a, 128) -> b <> (bf_cid R, bf_ctx R, 2584) -> b <> (bf_eid R, bf_enc R, 92) -> In b LB1).
      { intros b Hb N1b N2b N3b. pose proof (Permutation_in _ PERM1 Hb) as K. unfold blocks_B64F, BIO_SIZE, B64CTX_SIZE in K. cbn [app] in K.
        destruct K as [K|[K|[K|K]]]; [congruence| congruence| congruence| exact K]. }
      split; [| split; [| split]]; (apply KEEP; [assumption| congruence| congruence| congruence]). }
    destruct JJ as (J1' & J2' & J3' & J4').
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    (* [comment removed for export] *)
    assert (NX2 : forall A n q, ablock_range H A n -> 0 <= n -> n mod 8 = 0 -> sh A <= q < sh A + nsh n ->
              ~ rin_ivs ((bv_unsigned sp + -36, bv_unsigned sp + -36 + 4) :: mutex_foot ea ++ XS1) q).
    { intros A n q BR N0 N8 Hq K. pose proof BR as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). pose proof (sh_aapp_range A n Q7 N0) as (Sa1 & Sa2 & Sa3).
      cbn [rin_ivs fst snd app] in K. unfold mutex_foot in K. cbn [rin_ivs fst snd app] in K.
      destruct K as [K|[K|K]].
      - unfold AHI_LO in Sa3. clear - K Hq Sa2 Sa3 LO CEIL ACEILB BST1 BST2 SPR. lia.
      - pose proof (aapp_not_shadowland _ _ EAP2) as NE_. unfold ALOWSH_LO, AHI_LO in NE_, Sa3. rewrite S0 in Sa1. clear - K Hq Sa1 Sa2 Sa3 NE_. lia.
      - destruct (rin_Forall _ _ _ FXS1 K) as (iv & _ & P & P3). destruct (fs_scratch_apart_blocksh H HH _ _ _ A n RFS2 P BR N8); lia. }
    (* [comment removed for export] *)
    assert (NC2 : forall A n, aapp A n -> 0 <= n -> A + n <= aceil -> (A + n <= as_FSB H \/ as_FSB H + AFS_SIZE <= A) -> (A + n <= ea \/ ea + 40 <= A) ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) ((bv_unsigned sp + -36, bv_unsigned sp + -36 + 4) :: mutex_foot ea ++ XS1)).
    { intros A n AP0 N0 ACE0 AFS0 DJ0. constructor; [cbn; clear - ACE0 LO CEIL BST1 BST2 SPR; lia|]. unfold mutex_foot. constructor; [cbn; clear - DJ0; lia|].
      apply Forall_forall. intros iv Hiv. exact (fs_scratch_apart_app H HH _ _ _ A n RFS2 (proj1 (Forall_forall _ _) FXS1 iv Hiv) AP0 N0 AFS0). }
    assert (MB2 : MEMBIO H LB1 m2 mb M).
    { unhide MFS. unhide BBFS. unhide BMFS. unhide RPFS. unhide DJ_E_M. unhide DJ_E_BB. unhide DJ_E_BM. unhide DJ_E_RP.
      split; [| split; [| split; [| split; [| split; [exact J1'| split; [exact J2'| split; [exact J3'| split; [exact J4'| do 8 (apply proj2 in MB); exact MB]]]]]]]].
      - eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact (proj1 MB1)| eapply aclient_range_block; [exact J1'| lia| cbn; lia]| apply (NC2 mb 128 MAP); lia].
      - eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact (proj1 (proj2 MB1))| eapply aclient_range_block; [exact J2'| lia| cbn; lia]| apply (NC2 (mb_bb M) 16 BBAP); lia].
      - eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact (proj1 (proj2 (proj2 MB1)))| eapply aclient_range_block; [exact J3'| lia| cbn; lia]| apply (NC2 (mb_bm M) 32 BMAP); lia].
      - eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact (proj1 (proj2 (proj2 (proj2 MB1))))| eapply aclient_range_block; [exact J4'| lia| cbn; lia]| apply (NC2 (mb_rp M) 32 RPAP); lia]. }
    assert (MSHD2 : MEMBIO_shad m2 mb M).
    { destruct MSHD1 as (S1 & S2 & S3 & S4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in S1, S2, S3, S4. split; [| split; [| split]].
      - eapply (addressable_xpres_gen H); [exact J1'| unfold AAPP_HI, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; lia| exact S1| exact XP2| intros q Hq; apply (NX2 mb 128 q MR1); [lia| reflexivity| exact Hq]].
      - eapply (addressable_xpres_gen H); [exact J2'| unfold AAPP_HI, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; lia| exact S2| exact XP2| intros q Hq; apply (NX2 (mb_bb M) 16 q MR2); [lia| reflexivity| exact Hq]].
      - eapply (addressable_xpres_gen H); [exact J3'| unfold AAPP_HI, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; lia| exact S3| exact XP2| intros q Hq; apply (NX2 (mb_bm M) 32 q MR3); [lia| reflexivity| exact Hq]].
      - eapply (addressable_xpres_gen H); [exact J4'| unfold AAPP_HI, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; lia| exact S4| exact XP2| intros q Hq; apply (NX2 (mb_rp M) 32 q MR4); [lia| reflexivity| exact Hq]]. }
    assert (X2hi : forall T n, aceil <= T -> T + n <= bv_unsigned sp + -36 -> Forall (fun iv : Z * Z => T + n <= fst iv \/ snd iv <= T) ((bv_unsigned sp + -36, bv_unsigned sp + -36 + 4) :: mutex_foot ea ++ XS1)).
    { intros T n HT HT2. constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; lia|].
      eapply Forall_impl; [| exact FXS1]. intros iv P. pose proof (fs_scratch_below_ceil H HH _ _ _ RFS2 P). lia. }
    assert (FRj2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 12 j]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact FRj1| left; cbn; lia| apply X2hi; cbn; lia]).
    assert (FRh2 : rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact FRh1| left; cbn; lia|].
      constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; lia|]. eapply Forall_impl; [| exact FXS1]. intros iv P. pose proof (fs_scratch_below_ceil H HH _ _ _ RFS2 P). cbn. lia. }
    assert (CHN2 : as_chain H m2 (bv_unsigned sp) CH1).
    { eapply (ah_chain_ext H HH); [exact CHN1|]. intros fp' ra' q IN Hq. pose proof (CHS1 _ _ IN). pose proof (CHR1 _ _ IN).
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 IN) as (R1 & R2 & R3).
      apply XP2; [lia|]. split; [left; lia|].
      cbn [rin_ivs fst snd app]. unfold mutex_foot. cbn [rin_ivs fst snd app]. intros [K|[K|K]]; [lia| lia|].
      destruct (rin_Forall _ _ _ FXS1 K) as (iv & _ & P & P3). pose proof (fs_scratch_below_ceil H HH _ _ _ RFS2 P). lia. }
    assert (ACCM2 : accessible m2 mb 128) by (eapply addressable_accessible; [exact (proj1 MSHD2)| lia| unfold BIO_SIZE; lia| unfold AAPP_HI, BIO_SIZE; lia]).
    clear VIS1 KREL1 MI1 ST1 FRj1 SL1 FRh1 HP1 AUX1 AC1 ERR1 MF1 IM1 GM1 RL1 RFS1 CPH1 BU1 ENC1 SHD1 MB1 MSHD1 ST01 CHN1.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afa_seg2 with (lo := lo) (mb := mb) (B := membio_bio M);
      cbn [membio_bio bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite];
      first [exact MAP| exact (proj1 MB2)| exact ACCM2| exact SL2| exact ST2| exact CEIL| exact MI2| clear - MAL; lia| unfold A_mem_buf_method; lia| unhide RDO; unhide F128; clear - MP MH MCE BBP BBH BBCE MFLR NUMF NRD1 NRD2 MNXR MPVR POSR LENR LO BST1 BST2 SPR; lia]|].
    intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & ST3 & SL3). mpacc MPA MP3. cbn [membio_bio bio_next] in VIS3. rewrite MNX in VIS3.
    set (W3 := [(bv_unsigned sp + -36, bv_unsigned sp + -32)]) in MU3.
    assert (CW3 : Forall (aclient_write_ok H LB1) W3) by (unfold W3; constructor; [left; cbn; lia| constructor]).
    assert (LW3 : Forall (win_lib_ok LB1) W3) by (unfold W3; constructor; [left; cbn; lia| constructor]).
    assert (NSW3 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W3) by (unfold W3; constructor; [cbn; unfold AHI_LO; lia| constructor]).
    assert (HP3 : as_RHEAP H s2' LB1 m3) by (eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]).
    assert (AUX3 : as_rauxv_ok H m3 B) by (eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]).
    assert (AC3 : ACONST m3) by (eapply ACONST_stack_frame; [exact AC2| exact MU3| exact WM3| lia]).
    assert (ERR3 : rw_cells asegs m3 (ATP + -164) [C4 errv2]) by (eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold W3, ATP; cbn; lia]).
    assert (MF3 : MEMFLAG m3 1) by (eapply MEMFLAG_across; [exact MU3| exact WM3| unfold W3, A_mem_inited; cbn; lia| exact MF2]).
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold W3, A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold W3, A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    assert (RL3 : arelro_lib m3) by (eapply arelro_across7; [exact RL2| exact MU3| unfold W3; constructor; [cbn; lia| constructor]]).
    assert (RFS3 : as_RFS H LF m3) by (eapply (RFS_across_wins H HH); [exact RFS2| exact MU3| exact WM3| unfold W3; constructor; [left; cbn; lia| constructor]]).
    assert (CPH3 : CTXPH LB1 m3 (CtxReady x)) by (eapply CTXPH_frame; [exact CPH2| eapply (magree_lib_munch H HH); [exact HEAP2| auto| exact MU3| exact WM3| exact LW3]]).
    assert (MB3 : MEMBIO H LB1 m3 mb M) by (eapply MEMBIO_frame_disj7; [exact MB2| exact MU3| exact WM3| ..]; unfold W3, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; cbn; lia).
    assert (MSHD3 : MEMBIO_shad m3 mb M) by (eapply MEMBIO_shad_across2; [exact MB2| exact MSHD2| exact MU3| exact WM3| exact NSW3]).
    assert (ST03 : stack0 m3 lo (bv_unsigned sp)) by (eapply stack0_transport; [exact ST02| exact MU3| exact WM3| unfold W3; constructor; [apply stack0_ok_app; cbn; unfold AHI_LO; lia| constructor]]).
    apply (rw_cells_transport asegs _ m2 m3 _ _ FRj2) in MU3 as FRj3; [| exact WM3| unfold W3; cbn; lia].
    apply (rw_cells_transport asegs _ m2 m3 _ _ FRh2) in MU3 as FRh3; [| exact WM3| unfold W3; cbn; lia].
    assert (CHN3 : as_chain H m3 (bv_unsigned sp) CH1).
    { eapply (chain_via_munch H HH); [exact CHN2| exact MU3|]. intros fp' ra' Hin. pose proof (CHS1 _ _ Hin). pose proof (CHR1 _ _ Hin). unfold W3. cbn. split; [lia| exact I]. }
    clear VIS2 KREL2 MI2 AC2 ST2 ERR2 AUX2 MF2 IM2 GM2 RL2 RFS2 CPH2 MB2 MSHD2 ST02 FRj2 FRh2 CHN2 ACCM2 SL2.
    (* [comment removed for export] *)
    pose proof (abiofreeint_mem_spec H HH CFX) as C2. unfold biofreeint_mem_stmt in C2.
    eapply (ah_seq H HH).
    { eapply C2 with (lo := lo) (B := B) (LB := LB1) (s := s2') (x := x) (a := mb) (rbp := bv_unsigned sp + -36) (shi := bv_unsigned sp) (R := M) (CH := CH1);
        [exact VIS3| reflexivity| reflexivity| exact SL3| ..]; rewrite ?unsigned_lit by (unfold AFA_RA, R_BIO_free_all_BIO_free_int; clear - SPR LO LO0 BST1 BST2; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- stack0 _ _ _ => exact ST03
           | |- MEMBIO _ _ _ _ _ => exact MB3
           | |- MEMBIO_apart _ _ => exact MAPART
           | |- MEMBIO_shad _ _ _ => exact MSHD3
           | |- CTXPH _ _ _ => exact CPH3
           | |- as_RHEAP _ _ _ _ => exact HP3
           | |- as_AKREL _ _ _ => exact KREL3
           | |- as_rauxv_ok _ _ _ => exact AUX3
           | |- stk _ _ _ _ => exact ST3
           | |- rw_cells _ _ _ [C4 _] => exact ERR3
           | |- mem_inv _ _ => exact MI3
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 4 = 0 => clear - SPA SPR; Z.div_mod_to_equations; lia
           | |- ACONST _ => exact AC3
           | |- MEMFLAG _ _ => exact MF3
           | |- IMPL_mem _ => exact IM3
           | |- GOT_mem _ => exact GM3
           | |- METH_mem _ => exact (METH_of_relro _ RL3)
           | |- arelro_lib _ => exact RL3
           | |- as_RFS _ _ _ => exact RFS3
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- as_chain _ _ _ _ => exact CHN3
           | |- forall fp' ra', In _ _ -> _ + 16 <= fp' => exact CHS1
           | |- forall fp' ra', In _ _ -> _ \/ _ => exact CHR1
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_biofreeall, AFA_RA, pf_shift; intros q Hq; rewrite map_app; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => rewrite <- ?ECO2; clear - HAL AL2 CO2P; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | rewrite <- ?EBS1, <- ?EBS2; clear - SPR SPB LO LO0 BST1 BST2 CEIL S0HI; lia]
           end | idtac "C2-FAIL:" G; fail ] end. }
    clear C2. intros [msF4 mo4] PO. unfold biofreeint_mem_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & s4' & LB2 & XS2 &
                    VIS4 & MP4 & KREL4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & HEAP4 & PERM2 & MF4 & IM4 & GM4 & METH4 & RL4 & CPH4 & SL4 & ST04 & FXS2 & RFS4 & XP4 & AL4). mpacc MPA MP4.
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST4, XP4 by lia. rewrite unsigned_lit in ERR4 by (unfold ATP; lia). rewrite <- EA in XP4. rewrite <- ?ECO2 in AL4.
    assert (SUB2 : forall b, In b LB2 -> In b LB1) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PERM2)); apply in_or_app; right; exact Hb).
    assert (X4hi : forall T n, aceil <= T -> T + n <= bv_unsigned sp + -36 \/ bv_unsigned sp + -32 <= T ->
              Forall (fun iv : Z * Z => T + n <= fst iv \/ snd iv <= T) ((bv_unsigned sp + -36, bv_unsigned sp + -36 + 4) :: mutex_foot ea ++ XS2)).
    { intros T n HT HT2. constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; lia|].
      eapply Forall_impl; [| exact FXS2]. intros iv P. pose proof (fs_scratch_below_ceil H HH _ _ _ RFS4 P). lia. }
    assert (FRj4 : rw_cells asegs m4 (bv_unsigned sp + -48) [CB 12 j]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact FRj3| left; cbn; lia| apply X4hi; cbn; lia]).
    assert (FRh4 : rw_cells asegs m4 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact FRh3| left; cbn; lia| apply X4hi; cbn; lia]).
    clear VIS3 KREL3 MI3 ST3 AC3 ERR3 AUX3 MF3 IM3 GM3 RL3 RFS3 CPH3 MB3 MSHD3 ST03 FRj3 FRh3 CHN3 HP3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply afa_seg3 with (lo := lo); [exact FRj4| exact SL4| exact FRh4| exact ST4| exact CEIL| lia| exact MI4| exact RAE]|].
    intros msF5 mo5 KREL5 MP5 [VIS5 ST5]. mpacc MPA MP5.
    (* [comment removed for export] *)
    apply (ah_done H HH). unfold biofreeall_post. cbn [cfg_ms cfg_model].
    do 15 eexists. exists m4, errv4, s4', LB2, (XS1 ++ XS2).
    split; [exact VIS5|]. split; [exact KREL5|]. split; [exact MPA|]. split; [exact MI4|]. split; [exact AC4|]. split; [exact ST5|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR4|]. split; [exact AUX4|]. split; [exact HEAP4|].
    split; [eapply Permutation_trans; [exact PERM1|]; apply Permutation_app_head; exact PERM2|].
    split; [exact MF4|]. split; [exact IM4|]. split; [exact GM4|]. split; [exact (METHB_of_relro _ RL4)|]. split; [exact METH4|]. split; [exact RL4|]. split; [exact CPH4|].
    split; [exact ST04|]. split; [apply Forall_app; split; [exact FXS1| exact FXS2]|]. split; [exact RFS4|].
    split.
    { rewrite <- EA.
      eapply xpres_trans.
      { eapply (xpres_of_munch H _ LB2 _ _ _ m4 m m1); [exact HH| exact HEAP4| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
      eapply xpres_trans.
      { (* [comment removed for export] *)
        intros q Hq [HC HX]. apply XP2; [exact Hq|]. split.
        - eapply aclient_addr_weaken; [exact HC| lia| exact SUB2].
        - cbn [rin_ivs fst snd app]. intros [K|K].
          + destruct (aclient_cases H HH _ _ _ _ q HEAP4 HC Hq); lia.
          + apply HX. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K| right; apply rin_ivs_app; left; exact K]. }
      eapply xpres_trans.
      { eapply (xpres_of_munch H _ LB2 _ _ _ m4 m2 m3); [exact HH| exact HEAP4| exact MU3| exact WM3|]. unfold W3. constructor; [left; cbn; lia| constructor]. }
      intros q Hq [HC HX]. apply XP4; [exact Hq|]. split; [eapply aclient_addr_weaken; [exact HC| lia| intros b Hb; exact Hb]|].
      cbn [rin_ivs fst snd app]. intros [K|K].
      + destruct (aclient_cases H HH _ _ _ _ q HEAP4 HC Hq); lia.
      + apply HX. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K| right; apply rin_ivs_app; right; exact K]. }
    unfold BIOFREEALL_COST. rewrite <- ?ECO1, <- ?ECO2. clear - HAL AL2 AL4 CO2P. lia.
  Qed.
End W.
