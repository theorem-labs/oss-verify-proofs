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
  ECH_AC1_free ECH_AC8_small ECH_AC7_new ECH_AC7_newmembuf ECH_AC7_free ECH_AC7_biofreeint ECH_AC9_new ECH_AC9_bionew ECH_AC9_free.
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

  (* [comment removed for export] *)
  Lemma b64ctx_used_split : forall m C E hdr junk elen, rw_cells asegs m C (b64ctx_used_cells E hdr junk elen) ->
    rw_cells asegs m C [CB 32 hdr; C8 (wz E); CB 2528 junk] /\ rw_cells asegs m (C + O_B64_ENCBUF) [C8 (wz 0); C8 (wz elen)].
  Proof.
    intros m C E hdr junk elen HB. unfold b64ctx_used_cells in HB.
    change ([CB 32 hdr; C8 (wz E); CB 2528 junk; C8 (wz 0); C8 (wz elen)]) with ([CB 32 hdr; C8 (wz E); CB 2528 junk] ++ [C8 (wz 0); C8 (wz elen)]) in HB.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in HB. destruct HB as [H1 H2]. split; [exact H1|].
    cbn [cells_size csize Nat.add] in H2. unfold O_B64_ENCBUF. exact H2.
  Qed.
  Lemma b64ctx_used_join : forall m C E hdr junk, rw_cells asegs m C [CB 32 hdr; C8 (wz E); CB 2528 junk] ->
    rw_cells asegs m (C + O_B64_ENCBUF) [CB (Z.to_nat 16) (poison_bytes (Z.to_nat 16) 0)] -> rw_cells asegs m C (b64ctx_used_cells E hdr junk 0).
  Proof.
    intros m C E hdr junk H1 H2. unfold b64ctx_used_cells.
    change ([CB 32 hdr; C8 (wz E); CB 2528 junk; C8 (wz 0); C8 (wz 0)]) with ([CB 32 hdr; C8 (wz E); CB 2528 junk] ++ [C8 (wz 0); C8 (wz 0)]).
    apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. unfold O_B64_ENCBUF in H2.
    eapply arw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.

  Lemma abiofreeint_b64_spec : biofreeint_b64_stmt H.
  Proof.
    unfold biofreeint_b64_stmt. intros until CH.
    intros VIS A0 A1 RBC SPRB RBAL RBT SHIB ST0 BU APART ENC SHD CPH HP KREL AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM METHB METH RL RFS LFB CHN CHS CHR PF HAL RAE.
    unfold BIOFREEINT_B64_STACK, B64FREE_STACK, ENCFREE_STACK, BIOACC_STACK, CFREE_STACK, AFREE_STACK, AINTRIN_STACK, FR_BIO_free_int, FR_b64_free,
      FR_EVP_ENCODE_CTX_free, FR_BIO_set_data in LO.
    pose proof (ah_costs H HH) as (_ & _ & CF0 & _). unfold BIOFREEINT_B64_COST, B64FREE_COST, BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE in HAL.
    pose proof (CF0 0 ltac:(lia)) as CF00. pose proof (CF0 92 ltac:(lia)) as CF92. pose proof (CF0 2584 ltac:(lia)) as CF2584. pose proof (CF0 128 ltac:(lia)) as CF128.
    assert (CXS : 0 <= CFREEEX_STACK).
    { unfold CFREEEX_STACK, GETGLOBAL_READY_STACK, NEWEX_INNER, GETDEFCTX_STACK, FR_CRYPTO_free_ex_data, FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, AFS_STACK. lia. }
    remember CFREEEX_STACK as CXST eqn:ECX.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    (* [comment removed for export] *)
    destruct BU as (BA & (hdr & junk & elen & LH & LJ & ELR & BC) & BLK).
    destruct BLK as (I1 & I2 & I3 & BR1 & BR2 & BR3 & FLR & RTR & NRD & NXT & PRV).
    pose proof BR1 as (AP & AAL & _ & AH & ACE & AFS & AAP). pose proof BR2 as (CP & CAL & _ & CH0 & CCE & CFS & CAP). pose proof BR3 as (EP & EAL & _ & EH & ECE' & EFS & EAP).
    unfold AIMG_TOP in AH, CH0, EH. unfold BIO_SIZE in ACE, AFS, AAP, I1. unfold B64CTX_SIZE in CCE, CFS, CAP, I2.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & ATOP & _). pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & CTOP & _). pose proof (aapp_bounds _ _ EAP ltac:(lia)) as (_ & _ & ETOP & _).
    unfold AAPP_HI in ATOP, CTOP, ETOP.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. pose proof (aapp_not_shadowland _ _ CAP) as NSC. pose proof (aapp_not_shadowland _ _ EAP) as NSE.
    unfold ALOWSH_LO, AHI_LO in NSA, NSC, NSE.
    assert (NSWA : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(a, a + 128)]) by (fw; lia).
    assert (NSWC : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bf_ctx R, bf_ctx R + 2584)]) by (fw; lia).
    assert (NSWE : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bf_enc R, bf_enc R + 92)]) by (fw; lia).
    hide NSA. hide NSC. hide NSE. hide AFS. hide CFS. hide EFS.
    pose proof APART as (AP1 & AP2 & AP3). unfold BIO_SIZE, B64CTX_SIZE in AP1, AP2, AP3. hide AP1. hide AP2. hide AP3.
    destruct SHD as (ADA & ADC & ADE). unfold BIO_SIZE in ADA. unfold B64CTX_SIZE in ADC.
    (* [comment removed for export] *)
    destruct ENC as (raw & line & L80 & FD & ENCC & LR & EIN & EBR & DU). unfold ENCCTX_SIZE in EIN, EBR.
    pose proof (stack0_bounds _ _ _ ST0) as [S0LO S0HI]. unfold AAPP_HI in S0HI.
    assert (ACCRB : accessible m rbp 8) by (eapply stack0_accessible; [exact ST0| lia| lia| lia]).
    assert (ACCA : accessible m a 128) by (eapply addressable_accessible; [exact ADA| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCC : accessible m (bf_ctx R) 2584) by (eapply addressable_accessible; [exact ADC| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    cbn [CTXPH] in CPH. destruct CPH as [CS [EX (po & pi & O1 & O2)]].
    pose proof EX as (EXI & EXSZ & EXAR & EXMU). unfold MUTEX_SIZE in EXSZ, EXAR. remember (blk_addr (cx_exlock x)) as ea eqn:EA.
    pose proof (ah_blocks H HH _ _ _ _ HP EXI) as (_ & _ & _ & EH2 & ECE2 & EFS2 & EAP2). cbn [blk_size snd] in EH2, ECE2, EFS2, EAP2.
    rewrite <- ?EA, ?EXSZ in EH2. rewrite <- ?EA, ?EXSZ in ECE2. rewrite <- ?EA, ?EXSZ in EFS2. rewrite <- ?EA, ?EXSZ in EAP2. unfold AIMG_TOP in EH2.
    (* [comment removed for export] *)
    assert (NE12 : bf_id R <> bf_cid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I1 I2 ltac:(cbn; lia))).
    assert (NE13 : bf_id R <> bf_eid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I1 I3 ltac:(cbn; lia))).
    assert (NE23 : bf_cid R <> bf_eid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I2 I3 ltac:(cbn; lia))).
    assert (NEE1 : blk_id (cx_exlock x) <> bf_id R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I1 ltac:(rewrite EXSZ; cbn; lia))).
    assert (NEE2 : blk_id (cx_exlock x) <> bf_cid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I2 ltac:(rewrite EXSZ; cbn; lia))).
    assert (NEE3 : blk_id (cx_exlock x) <> bf_eid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I3 ltac:(rewrite EXSZ; cbn; lia))).
    hide NE12. hide NE13. hide NE23. hide NEE1. hide NEE2. hide NEE3.   (* [comment removed for export] *)
    pose proof (ah_disj H HH _ _ _ _ _ HP EXI I1 NEE1) as DJ_E_A. pose proof (ah_disj H HH _ _ _ _ _ HP EXI I2 NEE2) as DJ_E_C.
    rewrite <- ?EA, ?EXSZ in DJ_E_A. rewrite <- ?EA, ?EXSZ in DJ_E_C. cbn [blk_addr blk_size fst snd] in DJ_E_A, DJ_E_C. hide DJ_E_A. hide DJ_E_C.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply (abf_seg1) with (lo := lo) (R := R) (elen := elen) (hdr := hdr) (junk := junk);
      [exact A0| exact A1| exact AAP| exact CAP| exact AAL| exact CAL| unhide AP1; exact AP1| exact FLR| exact RTR| exact NRD| exact NXT| exact PRV| lia| lia| exact ELR| exact LH| exact LJ
      | exact BA| exact BC| exact RBC| exact SPRB| unfold AAPP_HI; lia| exact RBAL
      | exact ACCA| exact ACCC| exact ACCRB| exact AC| exact METHB| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MPA (m1 & j1 & j2 & VIS1 & MU1 & WM1 & MI1 & ST1 & BA1 & RB1 & F01 & F21).
    set (W1 := [(bv_unsigned sp + -128, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4)]) in MU1.
    assert (CW1 : Forall (aclient_write_ok H LB) W1).
    { unfold W1. constructor; [left; cbn; lia|]. constructor; [right; right; left; exists (bf_id R, a, 128); split; [exact I1| cbn; lia]|].
      constructor; [left; cbn; lia| constructor]. }
    assert (NSW1 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W1).
    { unfold W1. constructor; [cbn; unfold AHI_LO; lia|]. constructor; [pose proof (Forall_inv NSWA) as K; cbn [fst snd] in K |- *; unfold AHI_LO in *; rewrite ?ASHADOW_BASE_val in *; lia|].
      constructor; [cbn; unfold AHI_LO; lia| constructor]. }
    assert (LW1 : Forall (win_lib_ok []) W1).
    { unfold W1. unhide NSA. fw; [left; lia| right; split; [lia| split; [lia| intros q (b & [] & _)]]| left; lia]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame_win; [exact AC| exact MU1| exact WM1|]. unfold W1. fw; [left; lia| right; exists a, 128; split; [exact AAP| lia]| left; lia]. }
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold W1, ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold W1, A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold W1, A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold W1, A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across7; [exact RL| exact MU1| unfold W1; fw; lia]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_across_wins H HH); [exact RFS| exact MU1| exact WM1| unfold W1; unhide AFS; fw; [left; lia| right; lia| left; lia]]).
    assert (CS1 : CTX_statics m1 x) by (eapply (CTX_statics_frame []); [exact CS| eapply (magree_lib_munch H HH) with (L := []); [exact HP| intros b []| exact MU1| exact WM1| exact LW1]]).
    assert (EXMU1 : MUTEX m1 ea 0).
    { unfold MUTEX in *. eapply rw_cells_transport; [exact EXMU| exact MU1| exact WM1|]. unfold W1. unhide DJ_E_A. cbn. lia. }
    assert (ST01 : stack0 m1 lo shi).
    { eapply stack0_transport; [exact ST0| exact MU1| exact WM1|]. unfold W1.
      constructor; [apply stack0_ok_app; unfold AHI_LO; lia|]. constructor; [eapply stack0_ok_aapp; [exact AAP| lia| lia]|].
      constructor; [apply stack0_ok_app; unfold AHI_LO; lia| constructor]. }
    apply (rw_cells_transport asegs _ m m1 _ _ BC) in MU1 as BC1; [| exact WM1| unfold W1; unhide AP1; cbn; lia].
    apply (rw_cells_transport asegs _ m m1 _ _ ENCC) in MU1 as ENC1; [| exact WM1| unfold W1; unhide AP2; cbn; lia].
    assert (ADA1 : addressable m1 a 128) by (eapply addressable_across2; [exact ADA| exact AAP| exact MU1| exact WM1| exact NSW1]).
    assert (ADC1 : addressable m1 (bf_ctx R) 2584) by (eapply addressable_across2; [exact ADC| exact CAP| exact MU1| exact WM1| exact NSW1]).
    assert (ADE1 : addressable m1 (bf_enc R) 92) by (eapply addressable_across2; [exact ADE| exact EAP| exact MU1| exact WM1| exact NSW1]).
    (* [comment removed for export] *)
    assert (CHN0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. unfold W1.
      constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor].
      right. intros fp' ra' Hin. cbn. exact (CHR _ _ Hin). }
    set (CH1 := (bv_unsigned sp, bv_unsigned ra) :: CH). set (CH2 := (bv_unsigned sp + -48, AFI_RA1) :: CH1).
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) CH1).
    { eapply (ah_chain_cons H HH); [exact CHN0| lia| lia| exact SPA| lia| lia|].
      pose proof F01 as FR. change ([CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j1; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp - 16) in FR by (cbn; lia) end. rewrite !Z_to_bv_bv_unsigned. exact FR. }
    assert (CHN2 : as_chain H m1 (bv_unsigned sp + -48) CH2).
    { eapply (ah_chain_cons H HH); [exact CHN1| lia| unfold AFI_RA1, R_BIO_free_int_destroy; lia| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity| lia| lia|].
      pose proof F21 as FR. change ([CB 8 j2; C8 s5; C8 s4; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)])
        with ([CB 8 j2; C8 s5; C8 s4; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a)] ++ [C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -48 - 16) in FR by (cbn; lia) end. rewrite Z_to_bv_bv_unsigned. exact FR. }
    assert (CHS1 : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -48 + 16 <= fp') by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (CHS2 : forall fp' ra', In (fp', ra') CH2 -> bv_unsigned sp + -112 + 16 <= fp') by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS1 _ _ Hin); lia]).
    assert (PF1 : pf_ok (as_TR H) PF_b64free AFI_RA1 CH1).
    { eapply pf_ok_call; [exact PF|]. unfold PF_biofreeint_b64, AFI_RA1. intros q Hq. apply in_or_app; left; exact Hq. }
    clear CHN0 KREL VIS.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv) (CH := CH2);
        [exact VIS1| ..]; rewrite ?unsigned_lit by (unfold ABF_RA2, R_b64_free_CRYPTO_free; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CHN2
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- _ <= as_AL _ _ => clear - HAL CF00 CF92 CF2584 CF128; lia
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold CFREE_STACK, AFREE_STACK; lia]
           end | idtac "CFN-FAIL:" G; fail ] end. }
    intros [msF2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2). mpacc MPA MP2.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
    pose proof (xpres_nil_apres H _ _ _ _ XP2) as AP2'.
    assert (F02 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| constructor]).
    assert (F22 : rw_cells asegs m2 (bv_unsigned sp + -112) [CB 8 j2; C8 s5; C8 s4; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F21| left; cbn; lia| constructor]).
    assert (RB2 : rw_cells asegs m2 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact RB1| left; cbn; lia| constructor]).
    assert (BA2 : rw_cells asegs m2 a (bio_cells (bio_unref (b64f_bio R)))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact BA1| eapply aclient_range_block; [exact I1| lia| cbn; lia]| constructor]).
    assert (BC2 : rw_cells asegs m2 (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen)) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact BC1| eapply aclient_range_block; [exact I2| lia| cbn; lia]| constructor]).
    assert (ENC2 : rw_cells asegs m2 (bf_enc R) [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact ENC1| eapply aclient_range_block; [exact I3| lia| cbn; lia]| constructor]).
    assert (EXMU2 : MUTEX m2 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact EXMU1| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI| lia]| constructor]).
    assert (MF2 : MEMFLAG m2 1) by (eapply (MEMFLAG_apres H); [exact AP2'| exact MF1]).
    assert (RL2 : arelro_lib m2) by (eapply (arelro_xpres H); [exact RL1| exact XP2| constructor]).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| constructor]).
    assert (CS2 : CTX_statics m2 x).
    { eapply (CTX_statics_frame_mv []); [exact CS1|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP2| intros b []| eapply (xpres_nil_X H); exact XP2]. }
    assert (ST02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XP2| exact ST01| constructor]).
    assert (ADA2 : addressable m2 a 128) by (eapply (addressable_xpres_gen H); [exact I1| unfold AAPP_HI; lia| exact ADA1| exact XP2| intros q _ []]).
    assert (ADC2 : addressable m2 (bf_ctx R) 2584) by (eapply (addressable_xpres_gen H); [exact I2| unfold AAPP_HI; lia| exact ADC1| exact XP2| intros q _ []]).
    assert (ADE2 : addressable m2 (bf_enc R) 92) by (eapply (addressable_xpres_gen H); [exact I3| unfold AAPP_HI; lia| exact ADE1| exact XP2| intros q _ []]).
    assert (CHN22 : as_chain H m2 (bv_unsigned sp + -48) CH2) by (eapply (chain_via_apres H HH); [exact CHN2| exact AP2'| exact CHS2]).
    assert (CHS1b : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -112 + 16 <= fp') by (intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia).
    assert (CHN12 : as_chain H m2 (bv_unsigned sp) CH1) by (eapply (chain_via_apres H HH); [exact CHN1| exact AP2'| exact CHS1b]).
    assert (ACCC2 : accessible m2 (bf_ctx R) 2584) by (eapply addressable_accessible; [exact ADC2| lia| lia| unfold AAPP_HI; lia]).
    clear VIS1 KREL1 MI1 ST1 BA1 RB1 F01 F21 HP1 AUX1 AC1 ERR1 MF1 IM1 GM1 RL1 RFS1 CS1 EXMU1 ST01 BC1 ENC1 ADA1 ADC1 ADE1 CHN1 CHN2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply abf_seg2 with (hdr := hdr) (junk := junk) (elen := elen) (E := bf_enc R);
      [lia| exact CAL| exact CAP| lia| lia| exact BC2| exact ACCC2| exact MI2]|].
    intros msF4 mo4 KREL4 MP4 (m4 & VIS4 & MU4 & WM4 & MI4 & BC4). mpacc MPA MP4. unfold O_B64_ENCBUF, B64CTX_SIZE in MU4.
    (* [comment removed for export] *)
    set (W4 := [(bf_ctx R + 2568, bf_ctx R + 2584)]) in MU4.
    assert (CW4 : Forall (aclient_write_ok H LB) W4).
    { unfold W4. constructor; [right; right; left; exists (bf_cid R, bf_ctx R, 2584); split; [exact I2| cbn; lia]| constructor]. }
    assert (NSW4 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W4) by (unfold W4; unhide NSC; fw; lia).
    assert (LW4 : Forall (win_lib_ok []) W4).
    { unfold W4. unhide NSC. fw. right; split; [lia| split; [lia| intros q (b & [] & _)]]. }
    apply (stk_transport_disjoint asegs _ m2 m4 _ _ ST2) in MU4 as ST4; [| exact WM4| unfold W4; cbn; lia].
    assert (AC4 : ACONST m4) by (eapply ACONST_frame; [exact AC2| exact MU4| exact WM4| unfold W4; constructor; [eapply aconst_ok_aapp; [exact CAP| cbn [fst]; lia| cbn [snd]; lia]| constructor]]).
    apply (rw_cells_transport asegs _ m2 m4 _ _ F02) in MU4 as F04; [| exact WM4| unfold W4; cbn; lia].
    apply (rw_cells_transport asegs _ m2 m4 _ _ F22) in MU4 as F24; [| exact WM4| unfold W4; cbn; lia].
    apply (rw_cells_transport asegs _ m2 m4 _ _ RB2) in MU4 as RB4; [| exact WM4| unfold W4; cbn; lia].
    apply (rw_cells_transport asegs _ m2 m4 _ _ BA2) in MU4 as BA4; [| exact WM4| unfold W4; unhide AP1; cbn; lia].
    apply (rw_cells_transport asegs _ m2 m4 _ _ ENC2) in MU4 as ENC4; [| exact WM4| unfold W4; unhide AP3; cbn; lia].
    assert (ERR4 : rw_cells asegs m4 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR2| exact MU4| exact WM4| unfold W4, ATP; cbn; lia]).
    assert (AUX4 : as_rauxv_ok H m4 B) by (eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU4| exact WM4| exact CW4]).
    assert (HEAP4 : as_RHEAP H s2' LB m4) by (eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU4| exact WM4| exact CW4]).
    assert (MF4 : MEMFLAG m4 1) by (eapply MEMFLAG_across; [exact MU4| exact WM4| unfold W4, A_mem_inited; cbn; lia| exact MF2]).
    assert (IM4 : IMPL_mem m4) by (eapply IMPL_across; [exact MU4| exact WM4| unfold W4, A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM4 : GOT_mem m4) by (eapply GOT_across; [exact MU4| exact WM4| unfold W4, A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    assert (RL4 : arelro_lib m4) by (eapply arelro_across7; [exact RL2| exact MU4| unfold W4; fw; lia]).
    assert (RFS4 : as_RFS H LF m4) by (eapply (RFS_across_wins H HH); [exact RFS2| exact MU4| exact WM4| unfold W4; unhide CFS; fw; right; lia]).
    assert (CS4 : CTX_statics m4 x) by (eapply (CTX_statics_frame []); [exact CS2| eapply (magree_lib_munch H HH) with (L := []); [exact HEAP2| intros b []| exact MU4| exact WM4| exact LW4]]).
    assert (EXMU4 : MUTEX m4 ea 0).
    { unfold MUTEX in *. eapply rw_cells_transport; [exact EXMU2| exact MU4| exact WM4|]. unfold W4. unhide DJ_E_C. cbn. lia. }
    assert (ST04 : stack0 m4 lo shi).
    { eapply stack0_transport; [exact ST02| exact MU4| exact WM4|]. unfold W4.
      constructor; [eapply stack0_ok_aapp; [exact CAP| lia| lia]| constructor]. }
    assert (ADA4 : addressable m4 a 128) by (eapply addressable_across2; [exact ADA2| exact AAP| exact MU4| exact WM4| exact NSW4]).
    assert (ADC4 : addressable m4 (bf_ctx R) 2584) by (eapply addressable_across2; [exact ADC2| exact CAP| exact MU4| exact WM4| exact NSW4]).
    assert (ADE4 : addressable m4 (bf_enc R) 92) by (eapply addressable_across2; [exact ADE2| exact EAP| exact MU4| exact WM4| exact NSW4]).
    assert (CHN24 : as_chain H m4 (bv_unsigned sp + -48) CH2).
    { eapply (chain_via_munch H HH); [exact CHN22| exact MU4|]. intros fp' ra' Hin. pose proof (CHS2 _ _ Hin). unfold W4. cbn. split; [lia| exact I]. }
    assert (CHN14 : as_chain H m4 (bv_unsigned sp) CH1).
    { eapply (chain_via_munch H HH); [exact CHN12| exact MU4|]. intros fp' ra' Hin. pose proof (CHS1 _ _ Hin). unfold W4. cbn. split; [lia| exact I]. }
    clear VIS2 KREL2 MI2 AC2 ST2 ERR2 AUX2 F02 F22 RB2 BA2 BC2 ENC2 EXMU2 MF2 RL2 RFS2 CS2 ST02 ADA2 ADC2 ADE2 CHN22 CHN12 ACCC2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply abf_seg3; exact MI4|].
    intros msF5 mo5 KREL5 MP5 VIS5. mpacc MPA MP5.
    (* [comment removed for export] *)
    pose proof (aencfree_spec H HH) as EF. unfold encfree_stmt in EF.
    eapply (ah_seq H HH).
    { eapply EF with (lo := lo) (B := B) (LB := LB) (s := s2') (CH := CH2) (a := bf_enc R) (d := d) (p := bf_eid R); [exact VIS5| reflexivity| ..];
        rewrite ?unsigned_lit by (unfold ABF_RA4, R_b64_free_EVP_ENCODE_CTX_free; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- ENCCTX _ _ _ _ _ _ => exists raw, line; split; [exact L80|]; split; [exact FD|]; split; [exact ENC4|]; split; [exact LR|]; split; [exact I3|]; split; [exact EBR| exact DU]
           | |- addressable _ _ _ => exact ADE4
           | |- as_RHEAP _ _ _ _ => exact HEAP4
           | |- as_AKREL _ _ _ => exact KREL5
           | |- as_rauxv_ok _ _ _ => exact AUX4
           | |- stk _ _ _ _ => exact ST4
           | |- rw_cells _ _ _ [C4 _] => exact ERR4
           | |- mem_inv _ _ => exact MI4
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC4
           | |- as_chain _ _ _ _ => exact CHN24
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_b64free, R_b64_free_EVP_ENCODE_CTX_free, ABF_RA4; intros q Hq; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => unfold ENCCTX_SIZE in *; clear - HAL AL2 CF00 CF92 CF2584 CF128; lia
           | |- IMPL_mem _ => exact IM4
           | |- GOT_mem _ => exact GM4
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold ENCFREE_STACK, FR_EVP_ENCODE_CTX_free, CFREE_STACK, AFREE_STACK; lia]
           end | idtac "EF-FAIL:" G; fail ] end. }
    clear EF. intros [msF6 mo6] PO. unfold encfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m6 & errv6 & s6' &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & HEAP6 & IM6 & GM6 & AL6). mpacc MPA MP6.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST6, XP6 by lia. rewrite unsigned_lit in ERR6 by (unfold ATP; lia). unfold ENCCTX_SIZE in AL6.
    set (L1 := as_lb_remove H (bf_eid R) LB) in *.
    assert (SUB1 : forall b, In b L1 -> In b LB) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HEAP4 I3 Hb))).
    assert (I1' : In (bf_id R, a, 128) L1) by (eapply (in_remove H HH); [exact HEAP4| exact I3| exact I1| exact NE13]).
    assert (I2' : In (bf_cid R, bf_ctx R, 2584) L1) by (eapply (in_remove H HH); [exact HEAP4| exact I3| exact I2| exact NE23]).
    assert (EXI1 : In (cx_exlock x) L1) by (eapply (in_remove H HH); [exact HEAP4| exact I3| exact EXI| exact NEE3]).
    pose proof (xpres_nil_apres H _ _ _ _ XP6) as AP6'.
    assert (F06 : rw_cells asegs m6 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F04| left; cbn; lia| constructor]).
    assert (F26 : rw_cells asegs m6 (bv_unsigned sp + -112) [CB 8 j2; C8 s5; C8 s4; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F24| left; cbn; lia| constructor]).
    assert (RB6 : rw_cells asegs m6 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact RB4| left; cbn; lia| constructor]).
    assert (BA6 : rw_cells asegs m6 a (bio_cells (bio_unref (b64f_bio R)))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact BA4| eapply aclient_range_block; [exact I1'| lia| cbn; lia]| constructor]).
    assert (BC6 : rw_cells asegs m6 (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk 0)) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact BC4| eapply aclient_range_block; [exact I2'| lia| cbn; lia]| constructor]).
    assert (EXMU6 : MUTEX m6 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact EXMU4| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI1| lia]| constructor]).
    assert (MF6 : MEMFLAG m6 1) by (eapply (MEMFLAG_apres H); [exact AP6'| exact MF4]).
    assert (RL6 : arelro_lib m6) by (eapply (arelro_xpres H); [exact RL4| exact XP6| constructor]).
    assert (RFS6 : as_RFS H LF m6) by (eapply (RFS_via_xpres H HH); [exact RFS4| exact XP6| constructor]).
    assert (CS6 : CTX_statics m6 x).
    { eapply (CTX_statics_frame_mv []); [exact CS4|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP6| intros b []| eapply (xpres_nil_X H); exact XP6]. }
    assert (ST06 : stack0 m6 lo shi) by (eapply (stack0_xpres H); [exact XP6| exact ST04| constructor]).
    assert (ADA6 : addressable m6 a 128) by (eapply (addressable_xpres_gen H); [exact I1'| unfold AAPP_HI; lia| exact ADA4| exact XP6| intros q _ []]).
    assert (ADC6 : addressable m6 (bf_ctx R) 2584) by (eapply (addressable_xpres_gen H); [exact I2'| unfold AAPP_HI; lia| exact ADC4| exact XP6| intros q _ []]).
    assert (CHN26 : as_chain H m6 (bv_unsigned sp + -48) CH2) by (eapply (chain_via_apres H HH); [exact CHN24| exact AP6'| exact CHS2]).
    assert (CHN16 : as_chain H m6 (bv_unsigned sp) CH1) by (eapply (chain_via_apres H HH); [exact CHN14| exact AP6'| exact CHS1b]).
    clear VIS4 KREL4 MI4 AC4 ST4 ERR4 AUX4 F04 F24 RB4 BA4 BC4 ENC4 EXMU4 MF4 RL4 RFS4 CS4 ST04 ADA4 ADC4 ADE4 CHN24 CHN14 HEAP2 VIS5 KREL5.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply abf_seg4; exact MI6|].
    intros msF7 mo7 KREL7 MP7 VIS7. mpacc MPA MP7.
    (* [comment removed for export] *)
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L1) (s := s6') (CH := CH2) (n := 2584) (p := bf_cid R); [exact VIS7| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ABF_RA5, R_b64_free_CRYPTO_free_2; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP6
           | |- as_AKREL _ _ _ => exact KREL7
           | |- In _ _ => exact I2'
           | |- as_rauxv_ok _ _ _ => exact AUX6
           | |- stk _ _ _ _ => exact ST6
           | |- rw_cells _ _ _ [C4 _] => exact ERR6
           | |- rw_cells _ _ _ [CB _ _] => exact (rw_cells_as_CB _ _ _ BC6)
           | |- addressable _ _ _ => exact ADC6
           | |- mem_inv _ _ => exact MI6
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC6
           | |- as_chain _ _ _ _ => exact CHN26
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_b64free, R_b64_free_CRYPTO_free_2, ABF_RA5; intros q Hq; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => clear - HAL AL2 AL6 CF00 CF92 CF2584 CF128; lia
           | |- IMPL_mem _ => exact IM6
           | |- GOT_mem _ => exact GM6
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold CFREE_STACK, AFREE_STACK; lia]
           end | idtac "CF1-FAIL:" G; fail ] end. }
    clear CF. intros [msF8 mo8] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m8 & s8' &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & IM8 & GM8 & AL8). mpacc MPA MP8.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST8, XP8 by lia. rewrite unsigned_lit in ERR8 by (unfold ATP; lia).
    set (L2 := as_lb_remove H (bf_cid R) L1) in *.
    assert (SUB2 : forall b, In b L2 -> In b L1) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HEAP6 I2' Hb))).
    assert (I1'' : In (bf_id R, a, 128) L2) by (eapply (in_remove H HH); [exact HEAP6| exact I2'| exact I1'| exact NE12]).
    assert (EXI2 : In (cx_exlock x) L2) by (eapply (in_remove H HH); [exact HEAP6| exact I2'| exact EXI1| exact NEE2]).
    pose proof (xpres_nil_apres H _ _ _ _ XP8) as AP8'.
    assert (F08 : rw_cells asegs m8 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact F06| left; cbn; lia| constructor]).
    assert (F28 : rw_cells asegs m8 (bv_unsigned sp + -112) [CB 8 j2; C8 s5; C8 s4; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact F26| left; cbn; lia| constructor]).
    assert (RB8 : rw_cells asegs m8 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact RB6| left; cbn; lia| constructor]).
    assert (BA8 : rw_cells asegs m8 a (bio_cells (bio_unref (b64f_bio R)))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact BA6| eapply aclient_range_block; [exact I1''| lia| cbn; lia]| constructor]).
    assert (EXMU8 : MUTEX m8 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact EXMU6| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI2| lia]| constructor]).
    assert (MF8 : MEMFLAG m8 1) by (eapply (MEMFLAG_apres H); [exact AP8'| exact MF6]).
    assert (RL8 : arelro_lib m8) by (eapply (arelro_xpres H); [exact RL6| exact XP8| constructor]).
    assert (RFS8 : as_RFS H LF m8) by (eapply (RFS_via_xpres H HH); [exact RFS6| exact XP8| constructor]).
    assert (CS8 : CTX_statics m8 x).
    { eapply (CTX_statics_frame_mv []); [exact CS6|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP8| intros b []| eapply (xpres_nil_X H); exact XP8]. }
    assert (ST08 : stack0 m8 lo shi) by (eapply (stack0_xpres H); [exact XP8| exact ST06| constructor]).
    assert (ADA8 : addressable m8 a 128) by (eapply (addressable_xpres_gen H); [exact I1''| unfold AAPP_HI; lia| exact ADA6| exact XP8| intros q _ []]).
    assert (CHN18 : as_chain H m8 (bv_unsigned sp) CH1) by (eapply (chain_via_apres H HH); [exact CHN16| exact AP8'| exact CHS1b]).
    assert (ACCA8 : accessible m8 a 128) by (eapply addressable_accessible; [exact ADA8| lia| lia| unfold AAPP_HI; lia]).
    clear VIS6 KREL6 MI6 AC6 ST6 ERR6 AUX6 F06 F26 RB6 BA6 BC6 EXMU6 MF6 RL6 RFS6 CS6 ST06 ADA6 ADC6 CHN26 CHN16 VIS7 KREL7.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply abf_seg5 with (lo := lo) (a := a);
      [exact AAP| exact BA8| exact ACCA8| exact AC8| exact F28| exact ST8| exact CEIL| lia| exact MI8| exact AAL]|].
    intros msF9 mo9 KREL9 MP9 (m9 & a3x & VIS9 & MU9 & WM9 & MI9 & ST9 & BA9). mpacc MPA MP9.
    unfold O_BIO_INIT, O_BIO_PTR, O_BIO_EXDATA, CRYPTO_EX_INDEX_BIO in VIS9, MU9.
    set (W9 := [(bv_unsigned sp + -128, bv_unsigned sp + -112); (a + 40, a + 40 + 4); (a + 64, a + 64 + 8)]) in MU9.
    assert (CW9 : Forall (aclient_write_ok H L2) W9).
    { unfold W9. constructor; [left; cbn; lia|]. constructor; [right; right; left; exists (bf_id R, a, 128); split; [exact I1''| cbn; lia]|].
      constructor; [right; right; left; exists (bf_id R, a, 128); split; [exact I1''| cbn; lia]| constructor]. }
    assert (NSW9 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W9) by (unfold W9; unhide NSA; fw; lia).
    assert (LW9 : Forall (win_lib_ok []) W9).
    { unfold W9. unhide NSA. fw; [left; lia| right; split; [lia| split; [lia| intros q (b & [] & _)]]| right; split; [lia| split; [lia| intros q (b & [] & _)]]]. }
    apply (rw_cells_transport asegs _ m8 m9 _ _ F08) in MU9 as F09; [| exact WM9| unfold W9; cbn; lia].
    apply (rw_cells_transport asegs _ m8 m9 _ _ RB8) in MU9 as RB9; [| exact WM9| unfold W9; cbn; lia].
    assert (ERR9 : rw_cells asegs m9 (ATP + -164) [C4 errv6]) by (eapply errno_across; [exact ERR8| exact MU9| exact WM9| unfold W9, ATP; cbn; lia]).
    assert (AUX9 : as_rauxv_ok H m9 B) by (eapply (ah_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9| exact CW9]).
    assert (HEAP9 : as_RHEAP H s8' L2 m9) by (eapply (ah_RHEAP_frame H HH); [exact HEAP8| exact MU9| exact WM9| exact CW9]).
    assert (AC9 : ACONST m9).
    { eapply ACONST_frame_win; [exact AC8| exact MU9| exact WM9|]. unfold W9. fw; [left; lia| right; exists a, 128; split; [exact AAP| lia]| right; exists a, 128; split; [exact AAP| lia]]. }
    assert (MF9 : MEMFLAG m9 1) by (eapply MEMFLAG_across; [exact MU9| exact WM9| unfold W9, A_mem_inited; cbn; lia| exact MF8]).
    assert (IM9 : IMPL_mem m9) by (eapply IMPL_across; [exact MU9| exact WM9| unfold W9, A_malloc_impl; cbn; lia| exact IM8]).
    assert (GM9 : GOT_mem m9) by (eapply GOT_across; [exact MU9| exact WM9| unfold W9, A_got_CRYPTO_malloc; cbn; lia| exact GM8]).
    assert (RL9 : arelro_lib m9) by (eapply arelro_across7; [exact RL8| exact MU9| unfold W9; fw; lia]).
    assert (RFS9 : as_RFS H LF m9) by (eapply (RFS_across_wins H HH); [exact RFS8| exact MU9| exact WM9| unfold W9; unhide AFS; fw; [left; lia| right; lia| right; lia]]).
    assert (CS9 : CTX_statics m9 x) by (eapply (CTX_statics_frame []); [exact CS8| eapply (magree_lib_munch H HH) with (L := []); [exact HEAP8| intros b []| exact MU9| exact WM9| exact LW9]]).
    assert (EXMU9 : MUTEX m9 ea 0).
    { unfold MUTEX in *. eapply rw_cells_transport; [exact EXMU8| exact MU9| exact WM9|]. unfold W9. unhide DJ_E_A. cbn. lia. }
    assert (ST09 : stack0 m9 lo shi).
    { eapply stack0_transport; [exact ST08| exact MU9| exact WM9|]. unfold W9.
      constructor; [apply stack0_ok_app; unfold AHI_LO; lia|]. constructor; [eapply stack0_ok_aapp; [exact AAP| lia| lia]|].
      constructor; [eapply stack0_ok_aapp; [exact AAP| lia| lia]| constructor]. }
    assert (ADA9 : addressable m9 a 128) by (eapply addressable_across2; [exact ADA8| exact AAP| exact MU9| exact WM9| exact NSW9]).
    assert (CHN19 : as_chain H m9 (bv_unsigned sp) CH1).
    { eapply (chain_via_munch H HH); [exact CHN18| exact MU9|]. intros fp' ra' Hin. pose proof (CHS1 _ _ Hin). unfold W9. cbn. split; [lia|]. split; [lia|]. split; [lia| exact I]. }
    destruct (bio_cells_split_ex _ _ _ BA9) as [BA9a EXD9]. unfold O_BIO_EXDATA in EXD9.
    assert (ACCX9 : accessible m9 (a + 112) 16) by (eapply addressable_accessible; [exact ADA9| lia| lia| unfold AAPP_HI; lia]).
    clear VIS8 KREL8 MI8 AC8 ST8 ERR8 AUX8 F08 F28 RB8 BA8 EXMU8 MF8 RL8 RFS8 CS8 ST08 ADA8 CHN18 ACCA8.
    (* [comment removed for export] *)
    pose proof CFX as CX. unfold cfreeex_stmt, exdata_stmt_at in CX.
    eapply (ah_seq H HH).
    { eapply CX with (lo := lo) (B := B) (LB := L2) (s := s8') (x := x) (obj := a) (ad := a + 112) (c0 := 0) (k0 := 0) (LF := LF) (CH := CH1);
        [exact VIS9| ..]; rewrite ?unsigned_lit by (unfold AFI_RA2, R_BIO_free_int_CRYPTO_free_ex_data; clear - SPR LO LO0 CXS AH ACE; lia); try reflexivity.
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- _ = 0 /\ _ = 0 => split; reflexivity
           | |- rw_cells _ _ (_ + 112) _ => exact EXD9
           | |- accessible _ _ _ => exact ACCX9
           | |- ainblk _ _ _ => exists (bf_id R, a, 128); split; [exact I1''| cbn; lia]
           | |- CTX_statics _ _ => exact CS9
           | |- EXLOCK _ _ _ => unfold EXLOCK; rewrite <- EA; split; [exact EXI2| split; [exact EXSZ| split; [exact EXAR| exact EXMU9]]]
           | |- _ + 16 <= blk_addr _ \/ _ => rewrite <- EA; unfold MUTEX_SIZE; unhide DJ_E_A; clear - DJ_E_A; lia
           | |- as_RHEAP _ _ _ _ => exact HEAP9
           | |- as_AKREL _ _ _ => exact KREL9
           | |- as_rauxv_ok _ _ _ => exact AUX9
           | |- stk _ _ _ _ => exact ST9
           | |- rw_cells _ _ _ [C4 _] => exact ERR9
           | |- mem_inv _ _ => exact MI9
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
           | |- ACONST _ => exact AC9
           | |- MEMFLAG _ _ => exact MF9
           | |- IMPL_mem _ => exact IM9
           | |- GOT_mem _ => exact GM9
           | |- arelro_lib _ => exact RL9
           | |- as_RFS _ _ _ => exact RFS9
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- as_chain _ _ _ _ => exact CHN19
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia
           | |- _ <= as_AL _ _ => clear - HAL AL2 AL6 AL8 CF00 CF92 CF2584 CF128; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL AH ACE ECX; lia]
           end | idtac "CX-FAIL:" G; fail ] end. }
    clear CX. intros [msF10 mo10] PO. unfold exdata_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & y3 & y4 & y5 & y6 & m10 & s10' & XS &
                    VIS10 & _ & MP10 & (KREL10 & MI10 & AC10 & ST10 & ERR10 & AUX10 & HEAP10 & MF10 & IM10 & GM10 & RL10) & CS10 & EX10 & EXD10 & FXS & RFS10 & XP10 & AL10). mpacc MPA MP10.
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST10, XP10 by lia. rewrite unsigned_lit in ERR10 by (unfold ATP; lia). rewrite <- EA in XP10.
    (* [comment removed for export] *)
    assert (X10hi : forall T n, aceil <= T -> Forall (fun iv : Z * Z => T + n <= fst iv \/ snd iv <= T) ((a + 112, a + 112 + 16) :: mutex_foot ea ++ XS)).
    { intros T n HT. constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; lia|].
      eapply Forall_impl; [| exact FXS]. intros iv P. pose proof (fs_scratch_below_ceil H HH _ _ _ RFS10 P). lia. }
    assert (F010 : rw_cells asegs m10 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F09| left; cbn; lia| apply X10hi; cbn; lia]).
    assert (RB10 : rw_cells asegs m10 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact RB9| left; cbn; lia| apply X10hi; cbn; lia]).
    assert (BA10a : rw_cells asegs m10 a (firstn 18 (bio_cells (bio_with_init (bio_with_ptr (bio_unref (b64f_bio R)) 0) 0)))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact BA9a| eapply aclient_range_block; [exact I1''| lia| cbn; lia]|].
      constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; unhide DJ_E_A; clear - DJ_E_A; lia|].
      apply Forall_forall. intros iv Hiv. unhide AFS.
      destruct (fs_scratch_apart_app H HH _ _ _ a 112 RFS10 (proj1 (Forall_forall _ _) FXS iv Hiv) ltac:(eapply aapp_sub; [exact AAP| lia| lia]) ltac:(lia) ltac:(clear - AFS; lia)); cbn; lia. }
    pose proof (bio_cells_join_ex _ _ _ BA10a EXD10) as BA10. clear BA10a EXD10.
    assert (ADA10 : addressable m10 a 128).
    { eapply (addressable_xpres_gen H); [exact I1''| unfold AAPP_HI; lia| exact ADA9| exact XP10|].
      intros q Hq K. change (nsh 128) with 16 in Hq. unhide NSA. pose proof (sh_aapp_range a 128 AAP ltac:(lia)) as (Sa1 & Sa2 & Sa3).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      cbn [rin_ivs fst snd app mutex_foot] in K. unfold mutex_foot in K. cbn [rin_ivs fst snd app] in K.
      destruct K as [K|[K|K]].
      - unfold sh, AHI_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. clear - K Hq NSA AH ACE ACEILB. Z.div_mod_to_equations. lia.
      - (* [comment removed for export] *) pose proof (aapp_not_shadowland _ _ EAP2) as NE_. unfold ALOWSH_LO, AHI_LO in *.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. clear - K Hq NSA NE_ AH EH2 ACE ACEILB. Z.div_mod_to_equations. lia.
      - destruct (rin_Forall _ _ _ FXS K) as (iv & _ & P & P3).
        destruct (fs_scratch_apart_blocksh H HH _ _ _ a 128 RFS10 P BR1 ltac:(reflexivity)); change (nsh 128) with 16 in *; lia. }
    assert (ST010 : stack0 m10 lo shi).
    { eapply (stack0_xpres H); [exact XP10| exact ST09|]. constructor; [eapply stack0_ok_aapp; [exact AAP| lia| lia]|].
      unfold mutex_foot. constructor; [eapply stack0_ok_aapp; [exact EAP2| lia| lia]|].
      eapply Forall_impl; [| exact FXS]. intros iv P. exact (fs_scratch_stack0_ok H HH _ _ _ RFS10 P). }
    assert (CHN110 : as_chain H m10 (bv_unsigned sp) CH1).
    { eapply (chain_via_xpres H HH); [exact CHN19| exact XP10| intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia|].
      intros q K. cbn [rin_ivs fst snd app] in K. unfold mutex_foot in K. cbn [rin_ivs fst snd app] in K. destruct K as [K|[K|K]]; [lia| lia|].
      destruct (rin_Forall _ _ _ FXS K) as (iv & _ & P & P3). pose proof (fs_scratch_below_ceil H HH _ _ _ RFS10 P). lia. }
    clear VIS9 KREL9 MI9 ST9 AC9 ERR9 AUX9 IM9 GM9 F09 RB9 BA9 BA9a EXMU9 MF9 RL9 RFS9 CS9 ST09 ADA9 CHN19 ACCX9.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL10| exact VIS10| eapply afi_seg5; exact MI10|].
    intros msF11 mo11 KREL11 MP11 VIS11. mpacc MPA MP11.
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L2) (s := s10') (CH := CH1) (n := 128) (p := bf_id R); [exact VIS11| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AFI_RA3, R_BIO_free_int_CRYPTO_free; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP10
           | |- as_AKREL _ _ _ => exact KREL11
           | |- In _ _ => exact I1''
           | |- as_rauxv_ok _ _ _ => exact AUX10
           | |- stk _ _ _ _ => exact ST10
           | |- rw_cells _ _ _ [C4 _] => exact ERR10
           | |- rw_cells _ _ _ [CB _ _] => exact (rw_cells_as_CB _ _ _ BA10)
           | |- addressable _ _ _ => exact ADA10
           | |- mem_inv _ _ => exact MI10
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC10
           | |- as_chain _ _ _ _ => exact CHN110
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_biofreeint_b64, R_BIO_free_int_CRYPTO_free, AFI_RA3; intros q Hq; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => clear - HAL AL2 AL6 AL8 AL10 CF00 CF92 CF2584 CF128; lia
           | |- IMPL_mem _ => exact IM10
           | |- GOT_mem _ => exact GM10
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold CFREE_STACK, AFREE_STACK; lia]
           end | idtac "CF3-FAIL:" G; fail ] end. }
    clear CF. intros [msF12 mo12] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & f0 & f1' & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m12 & s12' &
                    VIS12 & KREL12 & MP12 & MI12 & AC12 & ST12 & ERR12 & AUX12 & XP12 & HEAP12 & IM12 & GM12 & AL12). mpacc MPA MP12.
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST12, XP12 by lia. rewrite unsigned_lit in ERR12 by (unfold ATP; lia).
    set (L3 := as_lb_remove H (bf_id R) L2) in *.
    assert (SUB3 : forall b, In b L3 -> In b L2) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HEAP10 I1'' Hb))).
    assert (EXI3 : In (cx_exlock x) L3) by (eapply (in_remove H HH); [exact HEAP10| exact I1''| exact EXI2| exact NEE1]).
    pose proof (xpres_nil_apres H _ _ _ _ XP12) as AP12'.
    assert (F012 : rw_cells asegs m12 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP12); [exact F010| left; cbn; lia| constructor]).
    assert (RB12 : rw_cells asegs m12 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP12); [exact RB10| left; cbn; lia| constructor]).
    pose proof EX10 as (_ & _ & _ & EXMU10). rewrite <- EA in EXMU10.
    assert (EXMU12 : MUTEX m12 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP12); [exact EXMU10| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI3| lia]| constructor]).
    assert (MF12 : MEMFLAG m12 1) by (eapply (MEMFLAG_apres H); [exact AP12'| exact MF10]).
    assert (RL12 : arelro_lib m12) by (eapply (arelro_xpres H); [exact RL10| exact XP12| constructor]).
    assert (RFS12 : as_RFS H LF m12) by (eapply (RFS_via_xpres H HH); [exact RFS10| exact XP12| constructor]).
    assert (CS12 : CTX_statics m12 x).
    { eapply (CTX_statics_frame_mv []); [exact CS10|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP12| intros b []| eapply (xpres_nil_X H); exact XP12]. }
    assert (ST012 : stack0 m12 lo shi) by (eapply (stack0_xpres H); [exact XP12| exact ST010| constructor]).
    clear VIS10 MI10 AC10 ST10 ERR10 AUX10 IM10 GM10 RL10 F010 RB10 BA10 ADA10 CHN110 VIS11 KREL11 KREL10.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL12| exact VIS12| eapply afi_seg6 with (lo := lo); [exact F012| exact ST12| exact CEIL| lia| exact MI12]|].
    intros msF13 mo13 KREL13 MP13 [VIS13 ST13]. mpacc MPA MP13.
    (* [comment removed for export] *)
    apply (ah_done H HH). unfold biofreeint_b64_post. cbn [cfg_ms cfg_model].
    do 14 eexists. exists m12, errv6, s12', L3, XS.
    split; [exact VIS13|]. split; [exact MPA|]. split; [exact KREL13|]. split; [exact MI12|]. split; [exact AC12|]. split; [exact ST13|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR12|]. split; [exact AUX12|]. split; [exact HEAP12|].
    split.
    { (* [comment removed for export] *)
      apply (Permutation_trans (l' := (bf_eid R, bf_enc R, 92) :: L1)); [apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HEAP4| exact I3]|].
      apply (Permutation_trans (l' := (bf_eid R, bf_enc R, 92) :: (bf_cid R, bf_ctx R, 2584) :: L2)); [apply perm_skip; apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HEAP6| exact I2']|].
      apply (Permutation_trans (l' := (bf_eid R, bf_enc R, 92) :: (bf_cid R, bf_ctx R, 2584) :: (bf_id R, a, 128) :: L3)); [do 2 apply perm_skip; apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HEAP10| exact I1'']|].
      unfold blocks_B64F, BIO_SIZE, B64CTX_SIZE.
      change (Permutation ([(bf_eid R, bf_enc R, 92); (bf_cid R, bf_ctx R, 2584); (bf_id R, a, 128)] ++ L3) ([(bf_id R, a, 128); (bf_cid R, bf_ctx R, 2584); (bf_eid R, bf_enc R, 92)] ++ L3)).
      apply Permutation_app_tail.
      change (Permutation (rev [(bf_id R, a, 128); (bf_cid R, bf_ctx R, 2584); (bf_eid R, bf_enc R, 92)]) [(bf_id R, a, 128); (bf_cid R, bf_ctx R, 2584); (bf_eid R, bf_enc R, 92)]).
      apply Permutation_sym. apply Permutation_rev. }
    split; [exact MF12|]. split; [exact IM12|]. split; [exact GM12|]. split; [exact (METHB_of_relro _ RL12)|]. split; [exact (METH_of_relro _ RL12)|]. split; [exact RL12|].
    split. { cbn [CTXPH]. split; [exact CS12|]. split.
             - unfold EXLOCK. rewrite <- EA. split; [exact EXI3|]. split; [exact EXSZ|]. split; [exact EXAR| exact EXMU12].
             - exists po, pi.
               assert (OK : forall q c, In (q, c, 40) LB -> In (q, c, 40) L3).
               { intros q c Hq. eapply (in_remove H HH); [exact HEAP10| exact I1''| | exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I1 ltac:(cbn; lia))].
                 eapply (in_remove H HH); [exact HEAP6| exact I2'| | exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I2 ltac:(cbn; lia))].
                 eapply (in_remove H HH); [exact HEAP4| exact I3| exact Hq| exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I3 ltac:(cbn; lia))]. }
               split; apply OK; assumption. }
    split; [exact RB12|]. split; [exact ST012|]. split; [exact FXS|]. split; [exact RFS12|].
    split.
    { (* [comment removed for export] *)
      assert (SUB31 : forall b, In b L3 -> In b L1) by (intros b Hb; apply SUB2, SUB3; exact Hb).
      assert (SUB30 : forall b, In b L3 -> In b LB) by (intros b Hb; apply SUB1, SUB31; exact Hb).
      assert (NA : forall q, a <= q < a + 128 -> aclient_addr H L3 (bv_unsigned sp) q -> False).
      { intros q Hq HC. eapply (afreed_outside H HH) with (L' := L3) (SP := bv_unsigned sp) (a := q); [exact HP| exact I1| | lia| exact HC| unfold BIO_SIZE; exact Hq].
        intros b Hb. split; [apply SUB30; exact Hb|]. exact (proj2 (remove_sub H HH _ _ _ _ _ _ b HEAP10 I1'' Hb)). }
      assert (NC : forall q, bf_ctx R <= q < bf_ctx R + 2584 -> aclient_addr H L3 (bv_unsigned sp) q -> False).
      { intros q Hq HC. eapply (afreed_outside H HH) with (L' := L3) (SP := bv_unsigned sp) (a := q); [exact HP| exact I2| | lia| exact HC| unfold B64CTX_SIZE; exact Hq].
        intros b Hb. split; [apply SUB30; exact Hb|]. exact (proj2 (remove_sub H HH _ _ _ _ _ _ b HEAP6 I2' (SUB3 _ Hb))). }
      eapply xpres_trans.
      { eapply (xpres_of_munch_gen H); [exact MU1| exact WM1|]. intros q Hq [HC HX]. unfold W1. cbn.
        split; [destruct (aclient_cases H HH _ _ _ _ q HEAP12 HC Hq); lia|].
        split; [intros K; exact (NA q ltac:(lia) HC)|].
        split; [intros K; apply HX; cbn; left; cbn; lia| exact I]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP2| lia| exact SUB30| intros q0 K0; cbn in K0; destruct K0]|].
      eapply xpres_trans.
      { eapply (xpres_of_munch_gen H); [exact MU4| exact WM4|]. intros q Hq [HC HX]. unfold W4. cbn.
        split; [intros K; exact (NC q ltac:(lia) HC)| exact I]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP6| lia| exact SUB31| intros q0 K0; cbn in K0; destruct K0]|].
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP8| lia| exact SUB3| intros q0 K0; cbn in K0; destruct K0]|].
      eapply xpres_trans.
      { eapply (xpres_of_munch_gen H); [exact MU9| exact WM9|]. intros q Hq [HC HX]. unfold W9. cbn.
        split; [destruct (aclient_cases H HH _ _ _ _ q HEAP12 HC Hq); lia|].
        split; [intros K; exact (NA q ltac:(lia) HC)|].
        split; [intros K; exact (NA q ltac:(lia) HC)| exact I]. }
      eapply xpres_trans.
      { eapply (xpres_X_mono H); [eapply (xpres_drop_win H) with (SP := bv_unsigned sp + -48); [exact XP10| exact SUB3| lia| intros q Hq HC; exact (NA q ltac:(lia) HC)]|].
        intros q Hq. rewrite <- EA. cbn. right. exact Hq. }
      eapply (xpres_weaken H); [exact XP12| lia| auto| intros q0 K0; cbn in K0; destruct K0]. }
    unfold BIOFREEINT_B64_COST, B64FREE_COST, BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE. clear - AL2 AL6 AL8 AL10 AL12. lia.
  Qed.
End W.
