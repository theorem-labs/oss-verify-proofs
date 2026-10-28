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
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_ALibMF ECH_ALibOK
  ECH_AC1_free ECH_AC6_buf ECH_AC7_new ECH_AC7_newmembuf ECH_AC7_free.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section K3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma afreed_outside : forall s LB m0 p A n L' SP a,
    as_RHEAP H s LB m0 -> In (p, A, n) LB -> (forall b, In b L' -> In b LB /\ blk_id b <> p) -> aceil <= SP ->
    aclient_addr H L' SP a -> A <= a < A + n -> False.
  Proof.
    intros s LB m0 p A n L' SP a RH IN SUB CE HC Ha. acb.
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    assert (QC : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; lia). pose proof (sh_below_aceil aceil QC) as SHC.
    assert (QB : 0 <= as_FSB H + AFS_SIZE < AAPP_HI) by (unfold AAPP_HI, AFS_SIZE, AIMG_TOP in *; lia). pose proof (sh_below_app (as_FSB H + AFS_SIZE) QB) as SB.
    assert (SH0 : forall x, 0 <= x -> ASHADOW_BASE <= sh x) by (intros x Hx; unfold sh; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia).
    unfold aapp, aapp_lo, aapp_hi in B7. unfold aclient_addr, aimg_client, in_block, in_block_sh in HC.
    unfold AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO in *. rewrite ASHADOW_BASE_val in SH0.
    destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]].
    - lia.
    - lia.
    - destruct (SUB _ Hb) as [HbL NE].
      pose proof (ah_disj H HH _ _ _ _ _ RH HbL IN NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
    - destruct (SUB _ Hb) as [HbL _]. pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4). pose proof (SH0 (blk_addr b) ltac:(lia)).
      unfold AHI_LO in S4. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - lia.
    - pose proof (SH0 (as_FSB H) ltac:(unfold AIMG_TOP in F1; lia)). unfold AHI_LO in SB. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - assert (QA : 0 <= aceil) by lia. pose proof (SH0 aceil QA). destruct B7 as [[P1 P2]|[P1 P2]]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_drop_win : forall L L' SP SP' wlo whi X m m',
    xpres H L SP ((wlo, whi) :: X) m m' -> (forall b, In b L' -> In b L) -> SP <= SP' ->
    (forall q, wlo <= q < whi -> aclient_addr H L' SP' q -> False) -> xpres H L' SP' X m m'.
  Proof.
    intros L L' SP SP' wlo whi X m m' XP SUB LE NC a Ha [HC HX]. apply XP; [exact Ha|]. split.
    - eapply aclient_addr_weaken; [exact HC| exact LE| exact SUB].
    - cbn. intros [K|K]; [exact (NC a K HC)| exact (HX K)].
  Qed.

  (* [comment removed for export] *)
  Lemma ids_ne_of_size : forall s LB m0 b1 b2, as_RHEAP H s LB m0 -> In b1 LB -> In b2 LB -> blk_size b1 <> blk_size b2 -> blk_id b1 <> blk_id b2.
  Proof.
    intros s LB m0 b1 b2 HP I1 I2 NS E. apply NS. rewrite (nodup_id_inj LB b1 b2 (ah_nodup H HH _ _ _ HP) I1 I2 E). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ids_ne_of_addr : forall s LB m0 b1 b2, as_RHEAP H s LB m0 -> In b1 LB -> In b2 LB -> blk_addr b1 <> blk_addr b2 -> blk_id b1 <> blk_id b2.
  Proof.
    intros s LB m0 b1 b2 HP I1 I2 NS E. apply NS. rewrite (nodup_id_inj LB b1 b2 (ah_nodup H HH _ _ _ HP) I1 I2 E). reflexivity.
  Qed.

  Lemma in_remove : forall s L m0 q B k b, as_RHEAP H s L m0 -> In (q, B, k) L -> In b L -> blk_id b <> q -> In b (as_lb_remove H q L).
  Proof.
    intros s L m0 q B k b HP IN Hb NE. destruct (alb_remove_exact H HH q B k L (ah_nodup H HH _ _ _ HP) IN) as (_ & _ & E). apply (proj2 (E b)). split; assumption.
  Qed.
  Lemma remove_sub : forall s L m0 q B k b, as_RHEAP H s L m0 -> In (q, B, k) L -> In b (as_lb_remove H q L) -> In b L /\ blk_id b <> q.
  Proof.
    intros s L m0 q B k b HP IN Hb. destruct (alb_remove_exact H HH q B k L (ah_nodup H HH _ _ _ HP) IN) as (_ & _ & E). exact (proj1 (E b) Hb).
  Qed.
  Lemma remove_len : forall s L m0 q B k, as_RHEAP H s L m0 -> In (q, B, k) L ->
    lb_bytes (as_lb_remove H q L) = lb_bytes L - k /\ (S (length (as_lb_remove H q L)) = length L)%nat.
  Proof.
    intros s L m0 q B k HP IN. destruct (alb_remove_exact H HH q B k L (ah_nodup H HH _ _ _ HP) IN) as (E1 & E2 & _). split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_scratch_stack0_ok : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> stack0_ok iv.
  Proof.
    intros LF m iv R SC. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4).
    destruct SC as [->|(k & ff & fp & FF & E)].
    - eapply stack0_ok_aapp; [exact F4| lia| unfold AFS_FLAGS, AFS_SIZE; lia].
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [-> |[-> | ->]].
      + eapply stack0_ok_aapp; [exact P9| lia| lia].
      + eapply stack0_ok_aapp; [exact P9| lia| lia].
      + rewrite fshn_nsh by lia. apply stack0_ok_sh; acb; unfold AIMG_TOP in *; lia.
  Qed.
End K3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Hypothesis CFX : cfreeex_stmt H.

  Local Ltac mpacc MPA0 MP := let T := fresh "MPX" in pose proof (ah_mpres_trans H HH _ _ _ MPA0 MP) as T; clear MPA0 MP; rename T into MPA0.
  Local Ltac fw := repeat (apply Forall_cons; [try unfold win_lib_ok; cbn [fst snd]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, ATLS_PRIV_LO, ATP, memflag_foot, A_mem_inited; rewrite ?ASHADOW_BASE_val|]); try apply Forall_nil.

  Lemma abiofreeint_mem_spec : biofreeint_mem_stmt H.
  Proof.
    unfold biofreeint_mem_stmt. intros until CH.
    intros VIS A0 A1 RBC SPRB RBT SHIB RBAL ST0 MB APART SHD CPH HP KREL AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM METH RL RFS LFB CHN CHS CHR PF HAL RAE.
    unfold BIOFREEINT_STACK, MEMFREE_STACK, BUFFREE_STACK, CFREE_STACK, AFREE_STACK, FR_BIO_free_int, FR_mem_free, FR_mem_buf_free, FR_BUF_MEM_free in LO.
    pose proof (ah_costs H HH) as (_ & _ & CF0 & _). unfold BIOFREE_COST, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in HAL.
    pose proof (CF0 0 ltac:(lia)) as CF00. pose proof (CF0 16 ltac:(lia)) as CF16. pose proof (CF0 32 ltac:(lia)) as CF32. pose proof (CF0 128 ltac:(lia)) as CF128.
    assert (CXS : 0 <= CFREEEX_STACK).
    { unfold CFREEEX_STACK, GETGLOBAL_READY_STACK, NEWEX_INNER, GETDEFCTX_STACK, FR_CRYPTO_free_ex_data, FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, AFS_STACK. lia. }
    remember CFREEEX_STACK as CXST eqn:ECX.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    (* [comment removed for export] *)
    destruct MB as (BA & BB & BM & RP & I1 & I2 & I3 & I4 & BR1 & BR2 & BR3 & BR4 & POSR & LENR & BUFP & BUFH & FLR & RDO & F128 & NUMF & NRD1 & NRD2 & NXT & PRV).
    hide RDO. hide F128.
    pose proof BR1 as (AP & AAL & _ & AH & ACE & AFS & AAP). pose proof BR2 as (BBP & BBAL & _ & BBH & BBCE & BBFS & BBAP).
    pose proof BR3 as (BMP & BMAL & _ & BMH & BMCE & BMFS & BMAP). pose proof BR4 as (RPP & RPAL & _ & RPH & RPCE & RPFS & RPAP).
    unfold AIMG_TOP in AH, BBH, BMH, RPH.
    pose proof (aapp_bounds _ _ AAP ltac:(unfold BIO_SIZE; lia)) as (_ & _ & ATOP & _). pose proof (aapp_bounds _ _ BBAP ltac:(unfold BIOBUFMEM_SIZE; lia)) as (_ & _ & BBTOP & _).
    pose proof (aapp_bounds _ _ BMAP ltac:(unfold BUFMEM_SIZE; lia)) as (_ & _ & BMTOP & _). pose proof (aapp_bounds _ _ RPAP ltac:(unfold BUFMEM_SIZE; lia)) as (_ & _ & RPTOP & _).
    unfold AAPP_HI in ATOP, BBTOP, BMTOP, RPTOP. unfold BIO_SIZE in ACE, AFS, ATOP. unfold BIOBUFMEM_SIZE in BBCE, BBFS, BBTOP. unfold BUFMEM_SIZE in BMCE, BMFS, BMTOP, RPCE, RPFS, RPTOP.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. pose proof (aapp_not_shadowland _ _ BBAP) as NSB. pose proof (aapp_not_shadowland _ _ BMAP) as NSM. pose proof (aapp_not_shadowland _ _ RPAP) as NSR.
    unfold ALOWSH_LO, AHI_LO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in NSA, NSB, NSM, NSR.
    assert (NSWA : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(a, a + 128)]) by (fw; lia).
    assert (NSWB : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(mb_bb R, mb_bb R + 16)]) by (fw; lia).
    assert (NSWM : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(mb_bm R, mb_bm R + 32)]) by (fw; lia).
    assert (NSWR : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(mb_rp R, mb_rp R + 32)]) by (fw; lia).
    hide NSA. hide NSB. hide NSM. hide NSR. hide AFS. hide BBFS. hide BMFS. hide RPFS.
    pose proof APART as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6.
    hide AP1. hide AP2. hide AP3. hide AP4. hide AP5. hide AP6.
    destruct SHD as (ADA & ADB & ADM & ADR). unfold BIO_SIZE in ADA. unfold BIOBUFMEM_SIZE in ADB. unfold BUFMEM_SIZE in ADM, ADR.
    pose proof (stack0_bounds _ _ _ ST0) as [S0LO S0HI]. unfold AAPP_HI in S0HI.
    assert (ACCRB : accessible m rbp 8) by (eapply stack0_accessible; [exact ST0| lia| lia| lia]).
    assert (ACCA : accessible m a 128) by (eapply addressable_accessible; [exact ADA| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCB : accessible m (mb_bb R) 16) by (eapply addressable_accessible; [exact ADB| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCM : accessible m (mb_bm R) 32) by (eapply addressable_accessible; [exact ADM| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    cbn [CTXPH] in CPH. destruct CPH as [CS [EX (po & pi & O1 & O2)]].
    pose proof EX as (EXI & EXSZ & EXAR & EXMU). unfold MUTEX_SIZE in EXSZ, EXAR. remember (blk_addr (cx_exlock x)) as ea eqn:EA.
    pose proof (ah_blocks H HH _ _ _ _ HP EXI) as (_ & _ & _ & EH & ECE & EFS & EAP). cbn [blk_size snd] in EH, ECE, EFS, EAP. rewrite <- ?EA, ?EXSZ in EH. rewrite <- ?EA, ?EXSZ in ECE. rewrite <- ?EA, ?EXSZ in EFS. rewrite <- ?EA, ?EXSZ in EAP. unfold AIMG_TOP in EH.
    (* [comment removed for export] *)
    assert (NE13 : mb_id R <> mb_bmid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I1 I3 ltac:(cbn; unfold BIO_SIZE, BUFMEM_SIZE; lia))).
    assert (NE43 : mb_rpid R <> mb_bmid R).
    { exact (ids_ne_of_addr H HH _ _ _ _ _ HP I4 I3 ltac:(cbn [blk_addr fst snd]; unhide AP6; lia)). }
    assert (NE23 : mb_bbid R <> mb_bmid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I2 I3 ltac:(cbn; unfold BIOBUFMEM_SIZE, BUFMEM_SIZE; lia))).
    assert (NE24 : mb_bbid R <> mb_rpid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I2 I4 ltac:(cbn; unfold BIOBUFMEM_SIZE, BUFMEM_SIZE; lia))).
    assert (NE14 : mb_id R <> mb_rpid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I1 I4 ltac:(cbn; unfold BIO_SIZE, BUFMEM_SIZE; lia))).
    assert (NE12 : mb_id R <> mb_bbid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP I1 I2 ltac:(cbn; unfold BIO_SIZE, BIOBUFMEM_SIZE; lia))).
    assert (NEE1 : blk_id (cx_exlock x) <> mb_id R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I1 ltac:(rewrite EXSZ; cbn; unfold BIO_SIZE; lia))).
    assert (NEE2 : blk_id (cx_exlock x) <> mb_bbid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I2 ltac:(rewrite EXSZ; cbn; unfold BIOBUFMEM_SIZE; lia))).
    assert (NEE3 : blk_id (cx_exlock x) <> mb_bmid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I3 ltac:(rewrite EXSZ; cbn; unfold BUFMEM_SIZE; lia))).
    assert (NEE4 : blk_id (cx_exlock x) <> mb_rpid R) by (exact (ids_ne_of_size H HH _ _ _ _ _ HP EXI I4 ltac:(rewrite EXSZ; cbn; unfold BUFMEM_SIZE; lia))).
    hide NE13. hide NE43. hide NE23. hide NE24. hide NE14. hide NE12. hide NEE1. hide NEE2. hide NEE3. hide NEE4.   (* [comment removed for export] *)
    pose proof (ah_disj H HH _ _ _ _ _ HP EXI I1 NEE1) as DJ_E_A. pose proof (ah_disj H HH _ _ _ _ _ HP EXI I3 NEE3) as DJ_E_M.
    rewrite <- ?EA, ?EXSZ in DJ_E_A. rewrite <- ?EA, ?EXSZ in DJ_E_M. cbn [blk_addr blk_size fst snd] in DJ_E_A, DJ_E_M. unfold BIO_SIZE in DJ_E_A. unfold BUFMEM_SIZE in DJ_E_M. hide DJ_E_A. hide DJ_E_M.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply (afi_seg1) with (lo := lo) (R := R);
      [exact A0| exact A1| exact AAP| exact BBAP| exact BMAP| exact AAL| exact BBAL| exact BMAL| exact APART| exact POSR| exact LENR| exact BUFP| exact BUFH| exact FLR| unhide RDO; exact RDO
      | clear - NRD1 NRD2 POSR; lia| exact NXT| exact PRV| exact NUMF| lia| exact BA| exact BB| exact BM| exact RBC| exact SPRB| unfold AAPP_HI; lia| exact RBAL
      | exact ACCA| exact ACCB| exact ACCM| exact ACCRB| exact AC| exact METH| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MPA (m1 & j1 & t1x & VIS1 & MU1 & WM1 & MI1 & ST1 & BA1 & BB1 & BM1 & RB1 & F01 & F11).
    set (W1 := [(bv_unsigned sp + -96, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4); (mb_bm R + 8, mb_bm R + 16)]) in MU1.
    assert (CW1 : Forall (aclient_write_ok H LB) W1).
    { unfold W1. constructor; [left; cbn; lia|]. constructor; [right; right; left; exists (mb_id R, a, BIO_SIZE); split; [exact I1| cbn; unfold BIO_SIZE; lia]|].
      constructor; [left; cbn; lia|]. constructor; [right; right; left; exists (mb_bmid R, mb_bm R, BUFMEM_SIZE); split; [exact I3| cbn; unfold BUFMEM_SIZE; lia]| constructor]. }
    assert (NSW1 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W1).
    { unfold W1. constructor; [cbn; unfold AHI_LO; lia|]. constructor; [pose proof (Forall_inv NSWA) as K; cbn [fst snd] in K |- *; unfold AHI_LO in *; rewrite ?ASHADOW_BASE_val in *; lia|].
      constructor; [cbn; unfold AHI_LO; lia|]. constructor; [pose proof (Forall_inv NSWM) as K; cbn [fst snd] in K |- *; unfold AHI_LO in *; rewrite ?ASHADOW_BASE_val in *; lia| constructor]. }
    assert (LW1 : Forall (win_lib_ok []) W1).
    { unfold W1. unhide NSA. unhide NSM. fw; [left; lia| right; split; [lia| split; [lia| intros q (b & [] & _)]]| left; lia| right; split; [lia| split; [lia| intros q (b & [] & _)]]]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame_win; [exact AC| exact MU1| exact WM1|]. unfold W1. fw; [left; lia| right; exists a, 128; split; [exact AAP| lia]| left; lia| right; exists (mb_bm R), 32; split; [exact BMAP| lia]]. }
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold W1, ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold W1, A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold W1, A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold W1, A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across7; [exact RL| exact MU1| unfold W1; fw; lia]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_across_wins H HH); [exact RFS| exact MU1| exact WM1| unfold W1; unhide AFS; unhide BMFS; fw; [left; lia| right; lia| left; lia| right; lia]]).
    assert (CS1 : CTX_statics m1 x) by (eapply (CTX_statics_frame []); [exact CS| eapply (magree_lib_munch H HH) with (L := []); [exact HP| intros b []| exact MU1| exact WM1| exact LW1]]).
    assert (EXMU1 : MUTEX m1 ea 0).
    { unfold MUTEX in *. eapply rw_cells_transport; [exact EXMU| exact MU1| exact WM1|]. unfold W1. unhide DJ_E_A. unhide DJ_E_M. cbn. lia. }
    assert (ST01 : stack0 m1 lo shi).
    { eapply stack0_transport; [exact ST0| exact MU1| exact WM1|]. unfold W1.
      constructor; [apply stack0_ok_app; unfold AHI_LO; lia|]. constructor; [eapply stack0_ok_aapp; [exact AAP| lia| unfold BIO_SIZE; lia]|].
      constructor; [apply stack0_ok_app; unfold AHI_LO; lia|]. constructor; [eapply stack0_ok_aapp; [exact BMAP| lia| unfold BUFMEM_SIZE; lia]| constructor]. }
    apply (rw_cells_transport asegs _ m m1 _ _ RP) in MU1 as RP1; [| exact WM1| unfold W1; unhide AP3; unhide AP6; cbn; lia].
    assert (ADA1 : addressable m1 a 128) by (eapply addressable_across2; [exact ADA| exact AAP| exact MU1| exact WM1| exact NSW1]).
    assert (ADB1 : addressable m1 (mb_bb R) 16) by (eapply addressable_across2; [exact ADB| exact BBAP| exact MU1| exact WM1| exact NSW1]).
    assert (ADM1 : addressable m1 (mb_bm R) 32) by (eapply addressable_across2; [exact ADM| exact BMAP| exact MU1| exact WM1| exact NSW1]).
    assert (ADR1 : addressable m1 (mb_rp R) 32) by (eapply addressable_across2; [exact ADR| exact RPAP| exact MU1| exact WM1| exact NSW1]).
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. unfold W1.
      constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor; [left; cbn; lia| constructor]].
      right. intros fp' ra' Hin. cbn. exact (CHR _ _ Hin). }
    set (CH1 := (bv_unsigned sp, bv_unsigned ra) :: CH). set (CH2 := (bv_unsigned sp + -48, AFI_RA1) :: CH1).
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) CH1).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof F01 as FR. change ([CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j1; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp - 16) in FR by (cbn; lia) end. rewrite !Z_to_bv_bv_unsigned. exact FR. }
    assert (CHN2 : as_chain H m1 (bv_unsigned sp + -48) CH2).
    { eapply (ah_chain_cons H HH); [exact CHN1| lia| unfold AFI_RA1, R_BIO_free_int_destroy; lia| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity| lia| lia|].
      pose proof F11 as FR. change ([C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) with ([C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a)] ++ [C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -48 - 16) in FR by (cbn; lia) end. rewrite Z_to_bv_bv_unsigned. exact FR. }
    assert (CHS1 : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -48 + 16 <= fp') by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (CHS2 : forall fp' ra', In (fp', ra') CH2 -> bv_unsigned sp + -80 + 16 <= fp') by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS1 _ _ Hin); lia]).
    assert (PF1 : pf_ok (as_TR H) PF_memfree AFI_RA1 CH1).
    { eapply pf_ok_call; [exact PF|]. unfold PF_biofreeint, AFI_RA1. intros q Hq. apply in_or_app; left; exact Hq. }
    assert (PF2 : pf_ok (as_TR H) PF_buffree AMF_RA1 CH2).
    { eapply pf_ok_call; [exact PF1|]. unfold PF_memfree, AMF_RA1. intros q Hq. apply in_or_app; left; exact Hq. }
    clear CH0 KREL VIS.
    (* [comment removed for export] *)
    pose proof (abuffree_spec H HH) as BF. unfold buffree_stmt in BF.
    eapply (ah_seq H HH).
    { eapply BF with (lo := lo) (B := B) (LB := LB) (s := s) (CH := CH2); [exact VIS1| reflexivity| exact I3| exact BM1| exact ADM1| ..]; rewrite ?unsigned_lit by (unfold AMF_RA1, R_mem_free_mem_buf_free; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CHN2
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => exact PF2
           | |- _ <= as_AL _ _ => unfold BUFMEM_SIZE; clear - HAL CF00 CF16 CF32 CF128; lia
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL POSR LENR BUFP BUFH; unfold BUFFREE_STACK, FR_BUF_MEM_free, CFREE_STACK, AFREE_STACK; lia]
           end | idtac "BF-FAIL:" G; fail ] end. }
    clear BF. intros [msF2 mo2] PO. unfold buffree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2). mpacc MPA MP2.
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
    set (L1 := as_lb_remove H (mb_bmid R) LB) in *.
    assert (SUB1 : forall b, In b L1 -> In b LB) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HP I3 Hb))).
    assert (I1' : In (mb_id R, a, BIO_SIZE) L1) by (eapply (in_remove H HH); [exact HP| exact I3| exact I1| exact NE13]).
    assert (I2' : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L1) by (eapply (in_remove H HH); [exact HP| exact I3| exact I2| exact NE23]).
    assert (I4' : In (mb_rpid R, mb_rp R, BUFMEM_SIZE) L1) by (eapply (in_remove H HH); [exact HP| exact I3| exact I4| exact NE43]).
    assert (EXI1 : In (cx_exlock x) L1) by (eapply (in_remove H HH); [exact HP| exact I3| exact EXI| exact NEE3]).
    pose proof (xpres_nil_apres H _ _ _ _ XP2) as AP2'.
    assert (F02 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| constructor]).
    assert (F12 : rw_cells asegs m2 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F11| left; cbn; lia| constructor]).
    assert (RB2 : rw_cells asegs m2 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact RB1| left; cbn; lia| constructor]).
    assert (BA2 : rw_cells asegs m2 a (bio_cells (bio_unref (membio_bio R)))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact BA1| eapply aclient_range_block; [exact I1'| lia| cbn; unfold BIO_SIZE; lia]| constructor]).
    assert (BB2 : rw_cells asegs m2 (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact BB1| eapply aclient_range_block; [exact I2'| lia| cbn; unfold BIOBUFMEM_SIZE; lia]| constructor]).
    assert (RP2 : rw_cells asegs m2 (mb_rp R) (buf_cells (mkBUF (mb_len R) (mb_buf R) (mb_len R) 0))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact RP1| eapply aclient_range_block; [exact I4'| lia| cbn; unfold BUFMEM_SIZE; lia]| constructor]).
    assert (EXMU2 : MUTEX m2 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact EXMU1| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI1| lia]| constructor]).
    assert (MF2 : MEMFLAG m2 1) by (eapply (MEMFLAG_apres H); [exact AP2'| exact MF1]).
    assert (RL2 : arelro_lib m2) by (eapply (arelro_xpres H); [exact RL1| exact XP2| constructor]).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| constructor]).
    assert (CS2 : CTX_statics m2 x).
    { eapply (CTX_statics_frame_mv []); [exact CS1|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP2| intros b []| eapply (xpres_nil_X H); exact XP2]. }
    assert (ST02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XP2| exact ST01| constructor]).
    assert (ADA2 : addressable m2 a 128) by (eapply (addressable_xpres_gen H); [exact I1'| unfold AAPP_HI, BIO_SIZE; lia| exact ADA1| exact XP2| intros q _ []]).
    assert (ADB2 : addressable m2 (mb_bb R) 16) by (eapply (addressable_xpres_gen H); [exact I2'| unfold AAPP_HI, BIOBUFMEM_SIZE; lia| exact ADB1| exact XP2| intros q _ []]).
    assert (ADR2 : addressable m2 (mb_rp R) 32) by (eapply (addressable_xpres_gen H); [exact I4'| unfold AAPP_HI, BUFMEM_SIZE; lia| exact ADR1| exact XP2| intros q _ []]).
    assert (CHS2a : forall fp' ra', In (fp', ra') CH2 -> bv_unsigned sp + -80 + 16 <= fp') by (intros fp' ra' Hin; pose proof (CHS2 _ _ Hin); lia).
    assert (CHN22 : as_chain H m2 (bv_unsigned sp + -48) CH2) by (eapply (chain_via_apres H HH); [exact CHN2| exact AP2'| exact CHS2a]).
    assert (ACCB2 : accessible m2 (mb_bb R) 16) by (eapply addressable_accessible; [exact ADB2| lia| lia| unfold AAPP_HI; lia]).
    assert (CHS1a : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -80 + 16 <= fp') by (intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia).
    assert (CHS1b : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -80 + 16 <= fp') by (intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia).
    assert (CHN12 : as_chain H m2 (bv_unsigned sp) CH1) by (eapply (chain_via_apres H HH); [exact CHN1| exact AP2'| exact CHS1a]).
    clear VIS1 KREL1 MI1 ST1 BA1 BB1 BM1 RB1 F01 F11 HP1 AUX1 AC1 ERR1 MF1 IM1 GM1 RL1 RFS1 CS1 EXMU1 ST01 RP1 ADA1 ADB1 ADM1 ADR1 CHN1 CHN2 PF2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afi_seg2 with (lo := lo) (rp := mb_rp R) (bm := mb_bm R); [exact BBAP| lia| exact BB2| exact ACCB2| exact BBAL| exact ST2| exact CEIL| lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3. mpacc MPA MP3.
    assert (ST3 : stk asegs m2 lo (bv_unsigned sp + -80)).
    { exact ST2. }
    (* [comment removed for export] *)
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L1) (s := s2') (CH := CH2) (n := 32); [exact VIS3| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AMF_RA2, R_mem_free_CRYPTO_free; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP2
           | |- as_AKREL _ _ _ => exact KREL3
           | |- In _ _ => exact I4'
           | |- as_rauxv_ok _ _ _ => exact AUX2
           | |- stk _ _ _ _ => exact ST3
           | |- rw_cells _ _ _ [C4 _] => exact ERR2
           | |- rw_cells _ _ _ [CB _ _] => exact (rw_cells_as_CB _ _ _ RP2)
           | |- addressable _ _ _ => exact ADR2
           | |- mem_inv _ _ => exact MI2
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC2
           | |- as_chain _ _ _ _ => exact CHN22
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_memfree, R_mem_free_CRYPTO_free, AMF_RA2; intros q Hq; apply in_or_app; right; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => unfold BUFMEM_SIZE in *; clear - HAL AL2 CF00 CF16 CF32 CF128; lia
           | |- IMPL_mem _ => exact IM2
           | |- GOT_mem _ => exact GM2
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold CFREE_STACK, AFREE_STACK; lia]
           end | idtac "CF1-FAIL:" G; fail ] end. }
    clear CF. intros [msF4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & s4' &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4 & AL4). mpacc MPA MP4.
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST4, XP4 by lia. rewrite unsigned_lit in ERR4 by (unfold ATP; lia).
    set (L2 := as_lb_remove H (mb_rpid R) L1) in *.
    assert (SUB2 : forall b, In b L2 -> In b L1) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HEAP2 I4' Hb))).
    assert (I1'' : In (mb_id R, a, BIO_SIZE) L2) by (eapply (in_remove H HH); [exact HEAP2| exact I4'| exact I1'| exact NE14]).
    assert (I2'' : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L2) by (eapply (in_remove H HH); [exact HEAP2| exact I4'| exact I2'| exact NE24]).
    assert (EXI2 : In (cx_exlock x) L2) by (eapply (in_remove H HH); [exact HEAP2| exact I4'| exact EXI1| exact NEE4]).
    pose proof (xpres_nil_apres H _ _ _ _ XP4) as AP4'.
    assert (F04 : rw_cells asegs m4 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact F02| left; cbn; lia| constructor]).
    assert (F14 : rw_cells asegs m4 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact F12| left; cbn; lia| constructor]).
    assert (RB4 : rw_cells asegs m4 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact RB2| left; cbn; lia| constructor]).
    assert (BA4 : rw_cells asegs m4 a (bio_cells (bio_unref (membio_bio R)))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact BA2| eapply aclient_range_block; [exact I1''| lia| cbn; unfold BIO_SIZE; lia]| constructor]).
    assert (BB4 : rw_cells asegs m4 (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact BB2| eapply aclient_range_block; [exact I2''| lia| cbn; unfold BIOBUFMEM_SIZE; lia]| constructor]).
    assert (EXMU4 : MUTEX m4 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact EXMU2| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI2| lia]| constructor]).
    assert (MF4 : MEMFLAG m4 1) by (eapply (MEMFLAG_apres H); [exact AP4'| exact MF2]).
    assert (RL4 : arelro_lib m4) by (eapply (arelro_xpres H); [exact RL2| exact XP4| constructor]).
    assert (RFS4 : as_RFS H LF m4) by (eapply (RFS_via_xpres H HH); [exact RFS2| exact XP4| constructor]).
    assert (CS4 : CTX_statics m4 x).
    { eapply (CTX_statics_frame_mv []); [exact CS2|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP4| intros b []| eapply (xpres_nil_X H); exact XP4]. }
    assert (ST04 : stack0 m4 lo shi) by (eapply (stack0_xpres H); [exact XP4| exact ST02| constructor]).
    assert (ADA4 : addressable m4 a 128) by (eapply (addressable_xpres_gen H); [exact I1''| unfold AAPP_HI, BIO_SIZE; lia| exact ADA2| exact XP4| intros q _ []]).
    assert (ADB4 : addressable m4 (mb_bb R) 16) by (eapply (addressable_xpres_gen H); [exact I2''| unfold AAPP_HI, BIOBUFMEM_SIZE; lia| exact ADB2| exact XP4| intros q _ []]).
    assert (CHN24 : as_chain H m4 (bv_unsigned sp + -48) CH2) by (eapply (chain_via_apres H HH); [exact CHN22| exact AP4'| exact CHS2]).
    assert (CHN14 : as_chain H m4 (bv_unsigned sp) CH1) by (eapply (chain_via_apres H HH); [exact CHN12| exact AP4'| exact CHS1b]).
    clear VIS2 KREL2 MI2 ST2 AC2 ERR2 AUX2 IM2 GM2 F02 F12 RB2 BA2 BB2 RP2 EXMU2 MF2 RL2 RFS2 CS2 ST02 ADA2 ADB2 ADR2 CHN22 ACCB2 VIS3 KREL3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply afi_seg3; exact MI4|].
    intros msF5 mo5 KREL5 MP5 VIS5. mpacc MPA MP5.
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L2) (s := s4') (CH := CH2) (n := 16); [exact VIS5| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AMF_RA3, R_mem_free_CRYPTO_free_2; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP4
           | |- as_AKREL _ _ _ => exact KREL5
           | |- In _ _ => exact I2''
           | |- as_rauxv_ok _ _ _ => exact AUX4
           | |- stk _ _ _ _ => exact ST4
           | |- rw_cells _ _ _ [C4 _] => exact ERR4
           | |- rw_cells _ _ _ [CB _ _] => exact (rw_cells_as_CB _ _ _ BB4)
           | |- addressable _ _ _ => exact ADB4
           | |- mem_inv _ _ => exact MI4
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC4
           | |- as_chain _ _ _ _ => exact CHN24
           | |- forall fp' ra', In _ _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_memfree, R_mem_free_CRYPTO_free_2, AMF_RA3; intros q Hq; apply in_or_app; right; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => unfold BUFMEM_SIZE in *; clear - HAL AL2 AL4 CF00 CF16 CF32 CF128; lia
           | |- IMPL_mem _ => exact IM4
           | |- GOT_mem _ => exact GM4
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold CFREE_STACK, AFREE_STACK; lia]
           end | idtac "CF2-FAIL:" G; fail ] end. }
    clear CF. intros [msF6 mo6] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & s6' &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & HEAP6 & IM6 & GM6 & AL6). mpacc MPA MP6.
    rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST6, XP6 by lia. rewrite unsigned_lit in ERR6 by (unfold ATP; lia).
    set (L3 := as_lb_remove H (mb_bbid R) L2) in *.
    assert (SUB3 : forall b, In b L3 -> In b L2) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HEAP4 I2'' Hb))).
    assert (I1x : In (mb_id R, a, BIO_SIZE) L3) by (eapply (in_remove H HH); [exact HEAP4| exact I2''| exact I1''| exact NE12]).
    assert (EXI3 : In (cx_exlock x) L3) by (eapply (in_remove H HH); [exact HEAP4| exact I2''| exact EXI2| exact NEE2]).
    pose proof (xpres_nil_apres H _ _ _ _ XP6) as AP6'.
    assert (F06 : rw_cells asegs m6 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F04| left; cbn; lia| constructor]).
    assert (F16 : rw_cells asegs m6 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F14| left; cbn; lia| constructor]).
    assert (RB6 : rw_cells asegs m6 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact RB4| left; cbn; lia| constructor]).
    assert (BA6 : rw_cells asegs m6 a (bio_cells (bio_unref (membio_bio R)))) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact BA4| eapply aclient_range_block; [exact I1x| lia| cbn; unfold BIO_SIZE; lia]| constructor]).
    assert (EXMU6 : MUTEX m6 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact EXMU4| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI3| lia]| constructor]).
    assert (MF6 : MEMFLAG m6 1) by (eapply (MEMFLAG_apres H); [exact AP6'| exact MF4]).
    assert (RL6 : arelro_lib m6) by (eapply (arelro_xpres H); [exact RL4| exact XP6| constructor]).
    assert (RFS6 : as_RFS H LF m6) by (eapply (RFS_via_xpres H HH); [exact RFS4| exact XP6| constructor]).
    assert (CS6 : CTX_statics m6 x).
    { eapply (CTX_statics_frame_mv []); [exact CS4|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP6| intros b []| eapply (xpres_nil_X H); exact XP6]. }
    assert (ST06 : stack0 m6 lo shi) by (eapply (stack0_xpres H); [exact XP6| exact ST04| constructor]).
    assert (ADA6 : addressable m6 a 128) by (eapply (addressable_xpres_gen H); [exact I1x| unfold AAPP_HI, BIO_SIZE; lia| exact ADA4| exact XP6| intros q _ []]).
    assert (CHN16 : as_chain H m6 (bv_unsigned sp) CH1) by (eapply (chain_via_apres H HH); [exact CHN14| exact AP6'| exact CHS1b]).
    clear VIS4 KREL4 MI4 ST4 AC4 ERR4 AUX4 IM4 GM4 F04 F14 RB4 BA4 BB4 EXMU4 MF4 RL4 RFS4 CS4 ST04 ADA4 ADB4 CHN24 CHN14 VIS5 KREL5.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply afi_seg4 with (lo := lo) (a := a); [lia| lia| exact F16| exact ST6| exact CEIL| lia| exact MI6]|].
    intros msF7 mo7 KREL7 MP7 VIS7. mpacc MPA MP7. unfold O_BIO_EXDATA in VIS7.
    assert (ST7 : stk asegs m6 lo (bv_unsigned sp + -48)).
    { pose proof (stk_release asegs m6 lo _ _ ST6 F16 ltac:(lia)) as K. lazymatch type of K with stk _ _ _ ?hi => replace hi with (bv_unsigned sp + -48) in K by (cbn; lia) end. exact K. }
    destruct (bio_cells_split_ex _ _ _ BA6) as [BA6a EXD6]. unfold O_BIO_EXDATA in EXD6.
    assert (ACCX6 : accessible m6 (a + 112) 16) by (eapply addressable_accessible; [exact ADA6| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    pose proof CFX as CX. unfold cfreeex_stmt, exdata_stmt_at in CX.
    eapply (ah_seq H HH).
    { eapply CX with (lo := lo) (B := B) (LB := L3) (s := s6') (x := x) (obj := a) (ad := a + 112) (c0 := 0) (k0 := 0) (LF := LF) (CH := CH1);
        [exact VIS7| ..]; rewrite ?unsigned_lit by (unfold AFI_RA2, R_BIO_free_int_CRYPTO_free_ex_data; clear - SPR LO LO0 CXS AH ACE; lia); try reflexivity.
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- _ = 0 /\ _ = 0 => split; reflexivity
           | |- rw_cells _ _ (_ + 112) _ => exact EXD6
           | |- accessible _ _ _ => exact ACCX6
           | |- ainblk _ _ _ => exists (mb_id R, a, BIO_SIZE); split; [exact I1x| cbn; unfold BIO_SIZE; lia]
           | |- CTX_statics _ _ => exact CS6
           | |- EXLOCK _ _ _ => unfold EXLOCK; rewrite <- EA; split; [exact EXI3| split; [exact EXSZ| split; [exact EXAR| exact EXMU6]]]
           | |- _ + 16 <= blk_addr _ \/ _ => rewrite <- EA; unfold MUTEX_SIZE; unhide DJ_E_A; clear - DJ_E_A; lia
           | |- as_RHEAP _ _ _ _ => exact HEAP6
           | |- as_AKREL _ _ _ => exact KREL7
           | |- as_rauxv_ok _ _ _ => exact AUX6
           | |- stk _ _ _ _ => exact ST7
           | |- rw_cells _ _ _ [C4 _] => exact ERR6
           | |- mem_inv _ _ => exact MI6
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
           | |- ACONST _ => exact AC6
           | |- MEMFLAG _ _ => exact MF6
           | |- IMPL_mem _ => exact IM6
           | |- GOT_mem _ => exact GM6
           | |- arelro_lib _ => exact RL6
           | |- as_RFS _ _ _ => exact RFS6
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- as_chain _ _ _ _ => exact CHN16
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia
           | |- _ <= as_AL _ _ => unfold BUFMEM_SIZE, BIOBUFMEM_SIZE in *; clear - HAL AL2 AL4 AL6 CF00 CF16 CF32 CF128; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL AH ACE ECX; lia]
           end | idtac "CX-FAIL:" G; fail ] end. }
    clear CX. intros [msF8 mo8] PO. unfold exdata_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m8 & s8' & XS &
                    VIS8 & _ & MP8 & (KREL8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & HEAP8 & MF8 & IM8 & GM8 & RL8) & CS8 & EX8 & EXD8 & FXS & RFS8 & XP8 & AL8). mpacc MPA MP8.
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST8, XP8 by lia. rewrite unsigned_lit in ERR8 by (unfold ATP; lia). rewrite <- EA in XP8.
    (* [comment removed for export] *)
    assert (X8hi : forall T n, aceil <= T -> Forall (fun iv : Z * Z => T + n <= fst iv \/ snd iv <= T) ((a + 112, a + 112 + 16) :: mutex_foot ea ++ XS)).
    { intros T n HT. constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; lia|].
      eapply Forall_impl; [| exact FXS]. intros iv P. pose proof (fs_scratch_below_ceil H HH _ _ _ RFS8 P). lia. }
    assert (F08 : rw_cells asegs m8 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact F06| left; cbn; lia| apply X8hi; cbn; lia]).
    assert (RB8 : rw_cells asegs m8 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact RB6| left; cbn; lia| apply X8hi; cbn; lia]).
    assert (BA8a : rw_cells asegs m8 a (firstn 18 (bio_cells (bio_unref (membio_bio R))))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP8); [exact BA6a| eapply aclient_range_block; [exact I1x| lia| cbn; unfold BIO_SIZE; lia]|].
      constructor; [cbn; lia|]. unfold mutex_foot. constructor; [cbn; unhide DJ_E_A; clear - DJ_E_A; lia|].
      apply Forall_forall. intros iv Hiv. unhide AFS.
      destruct (fs_scratch_apart_app H HH _ _ _ a 112 RFS8 (proj1 (Forall_forall _ _) FXS iv Hiv) ltac:(eapply aapp_sub; [exact AAP| lia| unfold BIO_SIZE; lia]) ltac:(lia) ltac:(clear - AFS; lia)); cbn; lia. }
    pose proof (bio_cells_join_ex _ _ _ BA8a EXD8) as BA8. clear BA8a EXD8.
    assert (ADA8 : addressable m8 a 128).
    { eapply (addressable_xpres_gen H); [exact I1x| unfold AAPP_HI, BIO_SIZE; lia| exact ADA6| exact XP8|].
      intros q Hq K. change (nsh 128) with 16 in Hq. unhide NSA. pose proof (sh_aapp_range a 128 AAP ltac:(lia)) as (Sa1 & Sa2 & Sa3).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      cbn [rin_ivs fst snd app mutex_foot] in K. unfold mutex_foot in K. cbn [rin_ivs fst snd app] in K.
      destruct K as [K|[K|K]].
      - unfold sh, AHI_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. clear - K Hq NSA AH ACE ACEILB. Z.div_mod_to_equations. lia.
      - (* [comment removed for export] *) pose proof (aapp_not_shadowland _ _ EAP) as NE_. unfold ALOWSH_LO, AHI_LO in *.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. clear - K Hq NSA NE_ AH EH ACE ACEILB. Z.div_mod_to_equations. lia.
      - destruct (rin_Forall _ _ _ FXS K) as (iv & _ & P & P3).
        destruct (fs_scratch_apart_blocksh H HH _ _ _ a 128 RFS8 P BR1 ltac:(reflexivity)); change (nsh 128) with 16 in *; lia. }
    assert (ST08 : stack0 m8 lo shi).
    { eapply (stack0_xpres H); [exact XP8| exact ST06|]. constructor; [eapply stack0_ok_aapp; [exact AAP| lia| unfold BIO_SIZE; lia]|].
      unfold mutex_foot. constructor; [eapply stack0_ok_aapp; [exact EAP| lia| lia]|].
      eapply Forall_impl; [| exact FXS]. intros iv P. exact (fs_scratch_stack0_ok H HH _ _ _ RFS8 P). }
    assert (CHN18 : as_chain H m8 (bv_unsigned sp) CH1).
    { eapply (chain_via_xpres H HH); [exact CHN16| exact XP8| intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia|].
      intros q K. cbn [rin_ivs fst snd app] in K. unfold mutex_foot in K. cbn [rin_ivs fst snd app] in K. destruct K as [K|[K|K]]; [lia| lia|].
      destruct (rin_Forall _ _ _ FXS K) as (iv & _ & P & P3). pose proof (fs_scratch_below_ceil H HH _ _ _ RFS8 P). lia. }
    clear VIS6 KREL6 MI6 ST6 AC6 ERR6 AUX6 IM6 GM6 F06 F16 RB6 BA6 BA6a EXMU6 MF6 RL6 RFS6 CS6 ST06 ADA6 CHN16 ACCX6 ST7 VIS7 KREL7.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply afi_seg5; exact MI8|].
    intros msF9 mo9 KREL9 MP9 VIS9. mpacc MPA MP9.
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L3) (s := s8') (CH := CH1) (n := 128); [exact VIS9| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AFI_RA3, R_BIO_free_int_CRYPTO_free; clear - SPR LO LO0 CXS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP8
           | |- as_AKREL _ _ _ => exact KREL9
           | |- In _ _ => exact I1x
           | |- as_rauxv_ok _ _ _ => exact AUX8
           | |- stk _ _ _ _ => exact ST8
           | |- rw_cells _ _ _ [C4 _] => exact ERR8
           | |- rw_cells _ _ _ [CB _ _] => exact (rw_cells_as_CB _ _ _ BA8)
           | |- addressable _ _ _ => exact ADA8
           | |- mem_inv _ _ => exact MI8
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC8
           | |- as_chain _ _ _ _ => exact CHN18
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); lia
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_biofreeint, R_BIO_free_int_CRYPTO_free, AFI_RA3; intros q Hq; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE in *; clear - HAL AL2 AL4 AL6 AL8 CF00 CF16 CF32 CF128; lia
           | |- IMPL_mem _ => exact IM8
           | |- GOT_mem _ => exact GM8
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 CXS CEIL; unfold CFREE_STACK, AFREE_STACK; lia]
           end | idtac "CF3-FAIL:" G; fail ] end. }
    clear CF. intros [msF10 mo10] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & f0 & f1' & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m10 & s10' &
                    VIS10 & KREL10 & MP10 & MI10 & AC10 & ST10 & ERR10 & AUX10 & XP10 & HEAP10 & IM10 & GM10 & AL10). mpacc MPA MP10.
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST10, XP10 by lia. rewrite unsigned_lit in ERR10 by (unfold ATP; lia).
    set (L4 := as_lb_remove H (mb_id R) L3) in *.
    assert (SUB4 : forall b, In b L4 -> In b L3) by (intros b Hb; exact (proj1 (remove_sub H HH _ _ _ _ _ _ b HEAP8 I1x Hb))).
    assert (EXI4 : In (cx_exlock x) L4) by (eapply (in_remove H HH); [exact HEAP8| exact I1x| exact EXI3| exact NEE1]).
    pose proof (xpres_nil_apres H _ _ _ _ XP10) as AP10'.
    assert (F010 : rw_cells asegs m10 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F08| left; cbn; lia| constructor]).
    assert (RB10 : rw_cells asegs m10 rbp [C4 (wz 0)]) by (eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact RB8| left; cbn; lia| constructor]).
    pose proof EX8 as (_ & _ & _ & EXMU8). rewrite <- EA in EXMU8.
    assert (EXMU10 : MUTEX m10 ea 0) by (unfold MUTEX in *; eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact EXMU8| right; right; left; exists (cx_exlock x); rewrite <- EA, EXSZ; cbn; split; [exact EXI4| lia]| constructor]).
    assert (MF10 : MEMFLAG m10 1) by (eapply (MEMFLAG_apres H); [exact AP10'| exact MF8]).
    assert (RL10 : arelro_lib m10) by (eapply (arelro_xpres H); [exact RL8| exact XP10| constructor]).
    assert (RFS10 : as_RFS H LF m10) by (eapply (RFS_via_xpres H HH); [exact RFS8| exact XP10| constructor]).
    assert (CS10 : CTX_statics m10 x).
    { eapply (CTX_statics_frame_mv []); [exact CS8|]. apply magree_mv_of_mf. eapply (magree_mf_of_xpres H) with (L := []); [exact HEAP10| intros b []| eapply (xpres_nil_X H); exact XP10]. }
    assert (ST010 : stack0 m10 lo shi) by (eapply (stack0_xpres H); [exact XP10| exact ST08| constructor]).
    clear VIS8 MI8 AC8 ST8 ERR8 AUX8 IM8 GM8 RL8 F08 RB8 BA8 ADA8 CHN18 VIS9 KREL9 KREL8.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL10| exact VIS10| eapply afi_seg6 with (lo := lo); [exact F010| exact ST10| exact CEIL| lia| exact MI10]|].
    intros msF11 mo11 KREL11 MP11 [VIS11 ST11]. mpacc MPA MP11.
    (* [comment removed for export] *)
    apply (ah_done H HH). unfold biofreeint_mem_post. cbn [cfg_ms cfg_model].
    do 14 eexists. exists m10, errv, s10', L4, XS.
    split; [exact VIS11|]. split; [exact MPA|]. split; [exact KREL11|]. split; [exact MI10|]. split; [exact AC10|]. split; [exact ST11|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR10|]. split; [exact AUX10|]. split; [exact HEAP10|].
    split.
    { (* [comment removed for export] *)
      apply (Permutation_trans (l' := (mb_bmid R, mb_bm R, BUFMEM_SIZE) :: L1)); [apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HP| exact I3]|].
      apply (Permutation_trans (l' := (mb_bmid R, mb_bm R, BUFMEM_SIZE) :: (mb_rpid R, mb_rp R, BUFMEM_SIZE) :: L2)); [apply perm_skip; apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HEAP2| exact I4']|].
      apply (Permutation_trans (l' := (mb_bmid R, mb_bm R, BUFMEM_SIZE) :: (mb_rpid R, mb_rp R, BUFMEM_SIZE) :: (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) :: L3)); [do 2 apply perm_skip; apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HEAP4| exact I2'']|].
      apply (Permutation_trans (l' := (mb_bmid R, mb_bm R, BUFMEM_SIZE) :: (mb_rpid R, mb_rp R, BUFMEM_SIZE) :: (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) :: (mb_id R, a, BIO_SIZE) :: L4)); [do 3 apply perm_skip; apply Permutation_sym; eapply (alb_remove_perm H HH); [exact HEAP8| exact I1x]|].
      unfold blocks_MEMBIO. change (Permutation ([(mb_bmid R, mb_bm R, BUFMEM_SIZE); (mb_rpid R, mb_rp R, BUFMEM_SIZE); (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE); (mb_id R, a, BIO_SIZE)] ++ L4)
                                             ([(mb_id R, a, BIO_SIZE); (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE); (mb_bmid R, mb_bm R, BUFMEM_SIZE); (mb_rpid R, mb_rp R, BUFMEM_SIZE)] ++ L4)).
      apply Permutation_app_tail. apply Permutation_sym.
      apply (Permutation_trans (l' := [(mb_id R, a, BIO_SIZE); (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE); (mb_rpid R, mb_rp R, BUFMEM_SIZE); (mb_bmid R, mb_bm R, BUFMEM_SIZE)])); [apply perm_skip, perm_skip, perm_swap|].
      change (Permutation [(mb_id R, a, BIO_SIZE); (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE); (mb_rpid R, mb_rp R, BUFMEM_SIZE); (mb_bmid R, mb_bm R, BUFMEM_SIZE)]
                          (rev [(mb_id R, a, BIO_SIZE); (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE); (mb_rpid R, mb_rp R, BUFMEM_SIZE); (mb_bmid R, mb_bm R, BUFMEM_SIZE)])).
      apply Permutation_rev. }
    split; [exact MF10|]. split; [exact IM10|]. split; [exact GM10|]. split; [exact (METH_of_relro _ RL10)|]. split; [exact RL10|].
    split. { cbn [CTXPH]. split; [exact CS10|]. split.
             - unfold EXLOCK. rewrite <- EA. split; [exact EXI4|]. split; [exact EXSZ|]. split; [exact EXAR| exact EXMU10].
             - exists po, pi.
               assert (OK : forall q c, In (q, c, 40) LB -> In (q, c, 40) L4).
               { intros q c Hq. eapply (in_remove H HH); [exact HEAP8| exact I1x| | exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I1 ltac:(cbn; unfold BIO_SIZE; lia))].
                 eapply (in_remove H HH); [exact HEAP4| exact I2''| | exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I2 ltac:(cbn; unfold BIOBUFMEM_SIZE; lia))].
                 eapply (in_remove H HH); [exact HEAP2| exact I4'| | exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I4 ltac:(cbn; unfold BUFMEM_SIZE; lia))].
                 eapply (in_remove H HH); [exact HP| exact I3| exact Hq| exact (ids_ne_of_size H HH _ _ _ _ _ HP Hq I3 ltac:(cbn; unfold BUFMEM_SIZE; lia))]. }
               split; apply OK; assumption. }
    split; [exact RB10|]. split; [exact ST010|]. split; [exact FXS|]. split; [exact RFS10|].
    split.
    { (* [comment removed for export] *)
      assert (SUB41 : forall b, In b L4 -> In b L1) by (intros b Hb; apply SUB2, SUB3, SUB4; exact Hb).
      assert (NA : forall q, a <= q < a + 128 -> aclient_addr H L4 (bv_unsigned sp) q -> False).
      { intros q Hq HC. eapply (afreed_outside H HH) with (L' := L4) (SP := bv_unsigned sp) (a := q); [exact HP| exact I1| | lia| exact HC| unfold BIO_SIZE; exact Hq].
        intros b Hb. split; [apply SUB1, SUB41; exact Hb|]. exact (proj2 (remove_sub H HH _ _ _ _ _ _ b HEAP8 I1x Hb)). }
      assert (NM : forall q, mb_bm R <= q < mb_bm R + 32 -> aclient_addr H L4 (bv_unsigned sp) q -> False).
      { intros q Hq HC. eapply (afreed_outside H HH) with (L' := L4) (SP := bv_unsigned sp) (a := q); [exact HP| exact I3| | lia| exact HC| unfold BUFMEM_SIZE; exact Hq].
        intros b Hb. split; [apply SUB1, SUB41; exact Hb|]. exact (proj2 (remove_sub H HH _ _ _ _ _ _ b HP I3 (SUB41 _ Hb))). }
      eapply xpres_trans.
      { eapply (xpres_of_munch_gen H); [exact MU1| exact WM1|]. intros q Hq [HC HX]. unfold W1. cbn.
        split; [destruct (aclient_cases H HH _ _ _ _ q HEAP10 HC Hq); lia|].
        split; [intros K; exact (NA q ltac:(lia) HC)|].
        split; [intros K; apply HX; cbn; left; cbn; lia|].
        split; [intros K; exact (NM q ltac:(lia) HC)| exact I]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP2| lia| exact SUB41| intros q0 K0; cbn in K0; destruct K0]|].
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP4| lia| intros b Hb; apply SUB3, SUB4; exact Hb| intros q0 K0; cbn in K0; destruct K0]|].
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP6| lia| exact SUB4| intros q0 K0; cbn in K0; destruct K0]|].
      eapply xpres_trans.
      { eapply (xpres_X_mono H); [eapply (xpres_drop_win H) with (SP := bv_unsigned sp + -48); [exact XP8| exact SUB4| lia| intros q Hq HC; exact (NA q ltac:(lia) HC)]|].
        intros q Hq. rewrite <- EA. cbn. right. exact Hq. }
      eapply (xpres_weaken H); [exact XP10| lia| auto| intros q0 K0; cbn in K0; destruct K0]. }
    unfold BIOFREE_COST, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. clear - AL2 AL4 AL6 AL8 AL10. lia.
  Qed.
End W.
