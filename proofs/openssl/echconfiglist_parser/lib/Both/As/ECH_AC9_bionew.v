(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_ALibMF ECH_ALibOK
  ECH_AC1_zalloc ECH_AC8_small ECH_AC7_new ECH_AC7_newmembuf ECH_AC9_new.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CNX : cnewex_stmt H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  Local Ltac mpacc MPA0 MP := let T := fresh "MPX" in pose proof (ah_mpres_trans H HH _ _ _ MPA0 MP) as T; clear MPA0 MP; rename T into MPA0.
  Local Ltac hlia := first [lia | unfold hidden in *; lia].
  Local Ltac fw := repeat (apply Forall_cons; [try unfold win_lib_ok; cbn [fst snd]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, ATLS_PRIV_LO, ATP, memflag_foot, A_mem_inited; rewrite ?ASHADOW_BASE_val|]); try apply Forall_nil.

  (* [comment removed for export] *)
  Lemma METHB_of_relro : forall m, arelro_lib m -> METH_b64 m.
  Proof.
    intros m RL. unfold METH_b64, O_METH_BREAD, A_b64_method. eapply relro_cell7; [exact RL| lia| cbn; lia| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
  (* [comment removed for export] *)

  Lemma abionew_b64_spec : bionew_b64_stmt H.
  Proof.
    unfold bionew_b64_stmt. intros until CH.
    intros VIS A0 HP KREL BUD BUDC AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM METH RL CPH RFS LFB CHN CHS PF HAL RAE.
    pose proof (ctxph_nonneg H HH (CtxReady x)) as (PHB & PHC & PHS & PHK). set (XST := CNEWEX_STACK (CtxReady x)) in *.
    unfold BIONEW_B64_STACK, B64NEW_STACK, ENCNEW_STACK, BIOACC_STACK, CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, AINTRIN_STACK, FR_BIO_new_ex, FR_b64_new,
      FR_CRYPTO_zalloc, FR_CRYPTO_malloc, FR_EVP_ENCODE_CTX_new, FR_BIO_set_data in LO.
    unfold B64F_BYTES, BIO_SIZE, B64CTX_SIZE in BUD.
    pose proof (ah_costs H HH) as (CM0 & _ & CF0 & _). unfold BIONEW_B64_COST, BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE in HAL.
    pose proof (CM0 92 ltac:(lia)) as CM92. pose proof (CM0 2584 ltac:(lia)) as CM2584. pose proof (CM0 128 ltac:(lia)) as CM128. pose proof (CF0 0 ltac:(lia)) as CF00.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply abn_seg1 with (lo := lo); [exact A0| exact AC| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MPA (m1 & j1 & VIS1 & MU1 & WM1 & MI1 & ST1 & F01).
    assert (CW1 : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| lia]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across7; [exact RL| exact MU1| fw; hlia]).
    assert (MT1 : METH_b64 m1) by (unfold METH_b64 in *; eapply rw_cells_transport; [exact METH| exact MU1| exact WM1| unfold A_b64_method, O_METH_BREAD; cbn; lia]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_across_wins H HH); [exact RFS| exact MU1| exact WM1| fw; left; hlia]).
    assert (CPH1 : CTXPH LB m1 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPH|]. eapply (magree_lib_munch H HH); [exact HP| auto| exact MU1| exact WM1| fw; left; hlia]. }
    assert (XP1 : forall X, xpres H LB (bv_unsigned sp) X m m1).
    { intros X. eapply (xpres_of_munch H s LB _ X _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    set (CH1 := (bv_unsigned sp, bv_unsigned ra) :: CH).
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) CH1).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof F01 as FR. change ([CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp - 16) in FR by (cbn; lia) end. rewrite !Z_to_bv_bv_unsigned. exact FR. }
    assert (CHS1 : forall fp' ra', In (fp', ra') CH1 -> bv_unsigned sp + -64 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    assert (PF1 : pf_ok (as_TR H) (PF_bionew_b64 x) (bv_unsigned ra) CH) by exact PF.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 128) (size := 1) (CH := CH1);
        [exact VIS1| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold ANEX_RA1; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CHN1
           | |- forall fp' ra', In (fp', ra') _ -> _ => exact CHS1
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_bionew_b64, R_BIO_new_ex_CRYPTO_zalloc, ANEX_RA1; intros q Hq; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => clear - HAL CM92 CM2584 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- lb_bytes _ + _ <= _ => clear - BUD PHB; lia
           | |- Z.of_nat (length _) + _ <= _ => clear - BUDC PHC; lia
           | |- _ => first [exact CEIL | unfold CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; clear - SPR SPB LO LO0 PHS CEIL; lia]
           end | idtac "CZ1-FAIL:" G; fail ] end. }
    clear CZ. intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p1 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR1 & HEAP2 & BLK2 & ADDR2 & MF2 & IM2 & GM2 & AL2). mpacc MPA MP2.
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
    pose proof BR1 as (AP & AAL & _ & AH & ACE & AFS & AAP). unfold AIMG_TOP in AH.
    pose proof (aapp_bounds A 128 AAP ltac:(lia)) as (_ & _ & ATOP & _ & _). unfold AAPP_HI in ATOP.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA. hide NSA. hide AFS.
    set (LB1 := (p1, A, 128) :: LB) in *.
    assert (SUB01 : forall b, In b LB -> In b LB1) by (intros b Hb; right; exact Hb).
    assert (AIN1 : In (p1, A, 128) LB1) by (left; reflexivity).
    assert (F02 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact F01| left; cbn; lia| fw; hlia]. }
    assert (RL2 : arelro_lib m2) by (eapply (arelro_xpres H); [exact RL1| exact XP2| fw; hlia]).
    assert (MT2 : METH_b64 m2) by (apply METHB_of_relro; exact RL2).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| fw; hlia]).
    assert (CPH2 : CTXPH LB m2 (CtxReady x)) by (eapply CTXPH_frame_mf; [exact CPH1| eapply (magree_mf_of_xpres H); [exact HP1| auto| exact XP2]]).
    assert (CHN3 : as_chain H m2 (bv_unsigned sp) CH1) by (eapply (chain_via_xpres H HH); [exact CHN1| exact XP2| exact CHS1| apply rin_memflag_low]).
    apply bio_zero_recut in BLK2.
    assert (ACC2 : accessible m2 A 128) by (eapply addressable_accessible; [exact ADDR2| lia| lia| unfold AAPP_HI; lia]).
    clear VIS1 KREL1 HP1 AUX1 AC1 ERR1 MF1 IM1 GM1 RL1 RFS1 CPH1 CH0 CHN1 MI1 ST1 F01 MT1.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply (anm_seg2) with (mt := A_b64_method); [exact AP| exact AAL| exact ACE| exact AAP| exact BLK2| exact ACC2| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & BA3). unfold BIO_SIZE in MU3. mpacc MPA MP3.
    assert (CW3 : Forall (aclient_write_ok H LB1) [(A, A + 128)]).
    { constructor; [| constructor]. right; right; left. exists (p1, A, 128). split; [exact AIN1| cbn; hlia]. }
    assert (NSWA : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(A, A + 128)]) by (fw; hlia).
    apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; hlia].
    apply (rw_cells_transport asegs _ m2 m3 _ _ F02) in MU3 as F03; [| exact WM3| cbn; hlia].
    assert (ERR3 : rw_cells asegs m3 (ATP + -164) [C4 errv2]) by (eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]).
    assert (AUX3 : as_rauxv_ok H m3 B) by (eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]).
    assert (HEAP3 : as_RHEAP H s2' LB1 m3) by (eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]).
    assert (AC3 : ACONST m3) by (eapply ACONST_frame; [exact AC2| exact MU3| exact WM3| constructor; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]| constructor]]).
    assert (MF3 : MEMFLAG m3 1) by (eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]).
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    assert (RL3 : arelro_lib m3) by (eapply arelro_across7; [exact RL2| exact MU3| fw; hlia]).
    assert (RFS3 : as_RFS H LF m3) by (eapply (RFS_across_wins H HH); [exact RFS2| exact MU3| exact WM3| fw; right; hlia]).
    assert (CPH3 : CTXPH LB1 m3 (CtxReady x)).
    { apply (CTXPH_mono LB LB1 SUB01). eapply CTXPH_frame; [exact CPH2|]. eapply (magree_lib_munch H HH); [exact HEAP2| exact SUB01| exact MU3| exact WM3|].
      fw. right. split; [hlia|]. split; [hlia|]. intros a (b & Hb & R).
      destruct (Z.lt_ge_cases a A) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (A + 128) a) as [K2|K2]; [right; exact K2|].
      exfalso. eapply (afresh_outside H HH); [exact HEAP2| exact CEIL| right; right; left; exists b; split; [exact Hb| exact R]| lia]. }
    assert (ADDR3 : addressable m3 A 128) by (eapply addressable_across2; [exact ADDR2| exact AAP| exact MU3| exact WM3| exact NSWA]).
    assert (CHN4 : as_chain H m3 (bv_unsigned sp) CH1).
    { eapply (chain_via_munch H HH); [exact CHN3| exact MU3|]. intros fp' ra' Hin. pose proof (CHS1 _ _ Hin). cbn. split; [lia| exact I]. }
    assert (XP3 : xpres H LB (bv_unsigned sp) memflag_foot m2 m3).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    destruct (bio_cells_split_ex _ _ _ BA3) as [BA3a EXD3].
    assert (ACC3x : accessible m3 (A + 112) 16) by (eapply accessible_sub; [eapply accessible_across2; [exact ACC2| exact MU3| exact NSWA]| lia| lia| lia]).
    clear VIS2 KREL2 MI2 AC2 ST2 ERR2 AUX2 MF2 IM2 GM2 RL2 RFS2 CPH2 CHN3 ACC2 BLK2 F02 BA3 MT2.
    (* [comment removed for export] *)
    assert (EXSEP : forall x0, CtxReady x = CtxReady x0 -> A + 112 + 16 <= blk_addr (cx_exlock x0) \/ blk_addr (cx_exlock x0) + MUTEX_SIZE <= A + 112).
    { intros x0 Hph. assert (EX : x0 = x) by congruence. subst x0. pose proof CPH3 as C. cbn [CTXPH] in C. destruct C as [_ [[BIN [BSZ BREST]] _]].
      destruct BIN as [EQ|BIN]; [rewrite <- EQ in BSZ; cbn in BSZ; unfold MUTEX_SIZE in BSZ; lia|].
      destruct (cx_exlock x) as [[q ea] en]. cbn [blk_addr blk_size fst snd] in *.
      pose proof (afresh_apart H HH _ _ _ _ _ _ lo ea MUTEX_SIZE HEAP2 CEIL
                    ltac:(eapply aclient_range_block; [exact BIN| lia| rewrite BSZ; lia]) ltac:(unfold MUTEX_SIZE; lia) ltac:(lia)) as D.
      unfold MUTEX_SIZE in *. lia. }
    (* [comment removed for export] *)
    pose proof CNX as CN. unfold cnewex_stmt in CN.
    eapply (ah_seq H HH).
    { eapply CN with (lo := lo) (B := B) (LB := LB1) (s := s2') (ph := CtxReady x) (obj := A) (ad := A + O_BIO_EXDATA) (c0 := 0) (k0 := 0) (LF := LF) (CH := CH1);
        [exact VIS3| ..]; unfold O_BIO_EXDATA; rewrite ?unsigned_lit by (unfold ANEX_RA2; clear - SPR LO LO0 PHS ACE AH; lia); try reflexivity.
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- rw_cells _ _ (_ + 112) _ => exact EXD3
           | |- xclient_range _ _ _ _ _ _ => eapply (ashobj_xclient_range H); [left; exists (p1, A, 128); split; [exact AIN1| cbn; lia]|];
                                            eapply Forall_impl; [| exact CTX_X_range]; intros iv K; cbn beta in K; unfold AIMG_TOP in K; lia
           | |- ainblk _ _ _ => exists (p1, A, 128); split; [exact AIN1| cbn; lia]
           | |- ctxph_sh0 _ _ _ _ => exact I
           | |- ctxph_closed_ok _ _ => exact I
           | |- accessible _ _ _ => exact ACC3x
           | |- forall x0, _ = CtxReady x0 -> _ => exact EXSEP
           | |- as_RHEAP _ _ _ _ => exact HEAP3
           | |- as_AKREL _ _ _ => exact KREL3
           | |- lb_bytes _ + _ <= _ => unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd ctxph_bytes]; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB1; cbn [length ctxph_cnt]; lia
           | |- as_rauxv_ok _ _ _ => exact AUX3
           | |- stk _ _ _ _ => exact ST3
           | |- rw_cells _ _ _ [C4 _] => exact ERR3
           | |- mem_inv _ _ => exact MI3
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 8 = 0 => clear - AAL; replace (A + 112) with (A + 8 * 14) by lia; rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia; Z.div_mod_to_equations; lia
           | |- ACONST _ => exact AC3
           | |- MEMFLAG _ _ => exact MF3
           | |- IMPL_mem _ => exact IM3
           | |- GOT_mem _ => exact GM3
           | |- arelro_lib _ => exact RL3
           | |- CTXPH _ _ _ => exact CPH3
           | |- as_RFS _ _ _ => exact RFS3
           | |- (_ <= AFS_MAXLIVE)%nat => cbn [ctxph_frames]; exact LFB
           | |- as_chain _ _ _ _ => exact CHN4
           | |- forall fp' ra', In (fp', ra') _ -> _ => exact CHS1
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF1|]; unfold PF_bionew_b64, R_BIO_new_ex_CRYPTO_new_ex_data, ANEX_RA2; intros q Hq;
                                 apply in_or_app; right; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => cbn [ctxph_cost] in HAL |- *; clear - AL2 HAL CM92 CM2584 CM128 CF00 PHK; lia
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 PHS CEIL ACE AH; lia]
           end | idtac "CNX-FAIL:" G; fail ] end. }
    clear CN. intros [msF4 mo4] PO. unfold cnewex_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & s4' & LBN & x4 & XS4 &
                    VIS4 & MP4 & (KREL4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & HEAP4 & MF4 & IM4 & GM4 & RL4) & DELTA & ADN4 & CPH4 & KEYS4 & EXD4 & FXS4 & RFS4 & XP4 & AL4). mpacc MPA MP4.
    cbn [ctxph_delta] in DELTA. destruct DELTA as [-> LBN0]. subst LBN. cbn [app] in HEAP4, CPH4.
    unfold O_BIO_EXDATA in *. rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST4, XP4 by lia. rewrite unsigned_lit in ERR4 by (unfold ATP; lia).
    pose proof (fun a => X4_low H HH LF m4 XS4 (CtxReady x) A a RFS4 FXS4 ACE) as X4L.  (* [comment removed for export] *)
    assert (F04 : rw_cells asegs m4 (bv_unsigned sp + -64) [CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact F03| left; cbn; lia|]. constructor; [cbn; lia| eapply (X4_apart_hi H HH _ _ _ (CtxReady x)); [exact RFS4| exact FXS4| cbn; lia]]. }
    assert (BA4a : rw_cells asegs m4 A (firstn 18 (bio_cells (bio_hdr1 A_b64_method)))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP4); [exact BA3a| eapply aclient_range_block; [exact AIN1| lia| cbn; lia]|].
      constructor; [cbn; lia| eapply (X4_apart_blk H HH _ _ _ (CtxReady x) A 128); [exact RFS4| exact FXS4| exact BR1| cbn; lia]]. }
    assert (ADDR4 : addressable m4 A 128).
    { eapply (addressable_xpres_gen H); [exact AIN1| unfold AAPP_HI; lia| exact ADDR3| exact XP4| eapply (X4_apart_shA H HH); [exact RFS4| exact FXS4| exact BR1]]. }
    assert (ACC4 : accessible m4 A 128) by (eapply addressable_accessible; [exact ADDR4| lia| lia| unfold AAPP_HI; lia]).
    assert (CHN5 : as_chain H m4 (bv_unsigned sp) CH1) by (eapply (chain_via_xpres H HH); [exact CHN4| exact XP4| exact CHS1| exact X4L]).
    assert (MT4 : METH_b64 m4) by (apply METHB_of_relro; exact RL4).
    assert (PF3 : pf_ok (as_TR H) PF_b64new ANEX_RA3 CH1).
    { eapply pf_ok_call; [exact PF1|]. unfold PF_bionew_b64, R_BIO_new_ex_create, ANEX_RA3. intros q Hq. apply in_or_app; right; apply in_or_app; right; exact Hq. }
    clear VIS3 KREL3 MI3 ST3 ERR3 AUX3 HEAP3 AC3 MF3 IM3 GM3 RL3 RFS3 CPH3 ADDR3 CHN4 ACC3x EXD3 BA3a F03.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply abn_seg3 with (lo := lo) (A := A);
      [exact AC4| exact MT4| rewrite unsigned_lit by lia; exact ST4| exact CEIL| rewrite unsigned_lit by lia; lia| exact MI4]|].
    intros msF5 mo5 KREL5 MP5 (m5 & j5 & VIS5 & MU5 & WM5 & MI5 & ST5 & F35). mpacc MPA MP5.
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in MU5, ST5, F35, VIS5 by lia.
    replace (bv_unsigned sp + -64 + -48) with (bv_unsigned sp + -112) in MU5 by lia. replace (bv_unsigned sp + -64 + -48) with (bv_unsigned sp + -112) in ST5 by lia.
    replace (bv_unsigned sp + -64 + -48) with (bv_unsigned sp + -112) in F35 by lia. replace (bv_unsigned sp + -64 + -48) with (bv_unsigned sp + -112) in VIS5 by lia.
    assert (CW5 : Forall (aclient_write_ok H LB1) [(lo, bv_unsigned sp + -64)]) by (constructor; [left; cbn; lia| constructor]).
    assert (NSW5 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -64)]) by (fw; hlia).
    apply (rw_cells_transport asegs _ m4 m5 _ _ F04) in MU5 as F05; [| exact WM5| cbn; hlia].
    apply (rw_cells_transport asegs _ m4 m5 _ _ BA4a) in MU5 as BA5a; [| exact WM5| cbn; hlia].
    apply (rw_cells_transport asegs _ m4 m5 _ _ EXD4) in MU5 as EXD5; [| exact WM5| cbn; hlia].
    assert (ERR5 : rw_cells asegs m5 (ATP + -164) [C4 errv4]) by (eapply errno_across; [exact ERR4| exact MU5| exact WM5| unfold ATP; cbn; lia]).
    assert (AUX5 : as_rauxv_ok H m5 B) by (eapply (ah_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5| exact CW5]).
    assert (HEAP5 : as_RHEAP H s4' LB1 m5) by (eapply (ah_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5| exact CW5]).
    assert (AC5 : ACONST m5) by (eapply ACONST_stack_frame; [exact AC4| exact MU5| exact WM5| exact CEIL]).
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]).
    assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]).
    assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4]).
    assert (RL5 : arelro_lib m5) by (eapply arelro_across7; [exact RL4| exact MU5| fw; hlia]).
    assert (RFS5 : as_RFS H LF m5) by (eapply (RFS_across_wins H HH); [exact RFS4| exact MU5| exact WM5| fw; left; hlia]).
    assert (CPH5 : CTXPH LB m5 (CtxReady x)).
    { pose proof CPH4 as C. apply (CTXPH_frame LB m4 m5) . 2: { eapply (magree_lib_munch H HH); [exact HEAP4| exact SUB01| exact MU5| exact WM5| fw; left; hlia]. }
      (* [comment removed for export] *)
      cbn [CTXPH] in C |- *. destruct C as [CS [[BIN [BSZ [BRR BMX]]] (po & pi & O1 & O2)]].
      assert (DROP : forall q a n, In (q, a, n) LB1 -> n <> 128 -> In (q, a, n) LB).
      { intros q a n Hin Hn. unfold LB1 in Hin. destruct Hin as [Hin|Hin]; [exfalso; injection Hin; lia| exact Hin]. }
      split; [exact CS|]. split.
      - split; [| split; [exact BSZ| split; [exact BRR| exact BMX]]]. destruct (cx_exlock x) as [[q a] n]. cbn [blk_size snd] in BSZ. apply DROP; [exact BIN| unfold MUTEX_SIZE in BSZ; lia].
      - exists po, pi. split; apply DROP; try assumption; lia. }
    assert (ADDR5 : addressable m5 A 128) by (eapply addressable_across2; [exact ADDR4| exact AAP| exact MU5| exact WM5| exact NSW5]).
    set (CH2 := (bv_unsigned sp + -64, ANEX_RA3) :: CH1).
    assert (CHN5b : as_chain H m5 (bv_unsigned sp) CH1).
    { eapply (achain_below H HH m4 m5); [exact CHN5| exact CHS1| exact MU5|]. constructor; [right; intros fp' ra' Hin; pose proof (CHS1 _ _ Hin); cbn; lia| constructor]. }
    assert (CHN6 : as_chain H m5 (bv_unsigned sp + -64) CH2).
    { eapply (ah_chain_cons H HH); [exact CHN5b| lia| unfold ANEX_RA3; lia| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity| lia| lia|].
      pose proof F35 as FR.
      change ([CB 8 j5; C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_b64_method + 72)); C8 (Z_to_bv 64 A); C8 sp; C8 (Z_to_bv 64 ANEX_RA3)])
        with ([CB 8 j5; C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_b64_method + 72)); C8 (Z_to_bv 64 A)] ++ [C8 sp; C8 (Z_to_bv 64 ANEX_RA3)]) in FR.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [_ FR].
      lazymatch type of FR with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -64 - 16) in FR by (cbn; lia) end.
      rewrite Z_to_bv_bv_unsigned. exact FR. }
    assert (CHS2 : forall fp' ra', In (fp', ra') CH2 -> bv_unsigned sp + -112 + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS1 _ _ Hin); lia]. }
    clear VIS4 KREL4 MI4 AC4 ST4 ERR4 AUX4 MF4 IM4 GM4 RL4 RFS4 CPH4 CHN5 CHN5b F04 BA4a EXD4 ADDR4 ACC4 MT4.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB1) (s := s4') (v := 1) (num := 2584) (size := 1) (CH := CH2);
        [exact VIS5| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold ABN_RA1, R_b64_new_CRYPTO_zalloc; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP5
           | |- as_AKREL _ _ _ => exact KREL5
           | |- as_rauxv_ok _ _ _ => exact AUX5
           | |- stk _ _ _ _ => exact ST5
           | |- rw_cells _ _ _ [C4 _] => exact ERR5
           | |- mem_inv _ _ => exact MI5
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC5
           | |- as_chain _ _ _ _ => exact CHN6
           | |- forall fp' ra', In (fp', ra') _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF3|]; unfold PF_b64new, R_b64_new_CRYPTO_zalloc, ABN_RA1; intros q Hq; apply in_or_app; left; exact Hq
           | |- _ <= as_AL _ _ => cbn [ctxph_cost] in AL4; clear - AL2 AL4 HAL CM92 CM2584 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF5
           | |- IMPL_mem _ => exact IM5
           | |- GOT_mem _ => exact GM5
           | |- lb_bytes _ + _ <= _ => unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd]; clear - BUD; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB1; cbn [length]; clear - BUDC; lia
           | |- _ => first [exact CEIL | unfold CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; clear - SPR SPB LO LO0 PHS CEIL; lia]
           end | idtac "CZ2-FAIL:" G; fail ] end. }
    clear CZ. intros [msF6 mo6] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv6 & C & p2 & s6' &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & BR2 & HEAP6 & BLK6 & ADDC6 & MF6 & IM6 & GM6 & AL6). mpacc MPA MP6.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST6, XP6 by lia. rewrite unsigned_lit in ERR6 by (unfold ATP; lia).
    pose proof BR2 as (CP & CAL & _ & CH0 & CCE & CFS & CAP). unfold AIMG_TOP in CH0.
    pose proof (aapp_bounds C 2584 CAP ltac:(lia)) as (_ & _ & CTOP & _ & _). unfold AAPP_HI in CTOP.
    pose proof (aapp_not_shadowland _ _ CAP) as NSC. unfold ALOWSH_LO, AHI_LO in NSC. hide NSC. hide CFS.
    set (LB2 := (p2, C, 2584) :: LB1) in *.
    assert (SUB12 : forall b, In b LB1 -> In b LB2) by (intros b Hb; right; exact Hb).
    assert (AIN2 : In (p1, A, 128) LB2) by (apply SUB12; exact AIN1). assert (CIN2 : In (p2, C, 2584) LB2) by (left; reflexivity).
    (* [comment removed for export] *)
    assert (DJ_AC : A + 128 <= C \/ C + 2584 <= A).
    { pose proof (ah_nodup H HH _ _ _ HEAP6) as ND. cbn [map blk_id fst snd] in ND. inversion ND as [|q l NI ND']; subst.
      assert (NE : blk_id (p2, C, 2584) <> blk_id (p1, A, 128)) by (cbn; intros E; apply NI; rewrite E; left; reflexivity).
      pose proof (ah_disj H HH _ _ _ _ _ HEAP6 CIN2 AIN2 NE) as D. cbn [blk_addr blk_size fst snd] in D. lia. }
    hide DJ_AC.
    assert (F06 : rw_cells asegs m6 (bv_unsigned sp + -64) [CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F05| left; cbn; lia| fw; hlia]. }
    assert (F36 : rw_cells asegs m6 (bv_unsigned sp + -112) [CB 8 j5; C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_b64_method + 72)); C8 (Z_to_bv 64 A); C8 sp; C8 (Z_to_bv 64 ANEX_RA3)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact F35| left; cbn; lia| fw; hlia]. }
    assert (BA6a : rw_cells asegs m6 A (firstn 18 (bio_cells (bio_hdr1 A_b64_method)))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact BA5a| eapply aclient_range_block; [exact AIN1| lia| cbn; lia]| fw; hlia]. }
    assert (EXD6 : rw_cells asegs m6 (A + 112) [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP6); [exact EXD5| eapply aclient_range_block; [exact AIN1| lia| cbn; lia]| fw; hlia]. }
    assert (ADDR6 : addressable m6 A 128).
    { eapply (addressable_xpres_gen H); [exact AIN1| unfold AAPP_HI; lia| exact ADDR5| exact XP6|].
      intros a Ha K. pose proof (sh_aapp_range A 128 AAP ltac:(lia)) as (S1 & S2 & S3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      unfold memflag_foot, A_mem_inited in K. cbn [rin_ivs fst snd] in K. rewrite S0 in S1. clear - K S1 Ha. lia. }
    assert (RL6 : arelro_lib m6) by (eapply (arelro_xpres H); [exact RL5| exact XP6| fw; hlia]).
    assert (MT6 : METH_b64 m6) by (apply METHB_of_relro; exact RL6).
    assert (RFS6 : as_RFS H LF m6) by (eapply (RFS_via_xpres H HH); [exact RFS5| exact XP6| fw; hlia]).
    assert (CPH6 : CTXPH LB m6 (CtxReady x)) by (eapply CTXPH_frame_mf; [exact CPH5| eapply (magree_mf_of_xpres H); [exact HEAP5| exact SUB01| exact XP6]]).
    assert (CHN7 : as_chain H m6 (bv_unsigned sp + -64) CH2) by (eapply (chain_via_xpres H HH); [exact CHN6| exact XP6| exact CHS2| apply rin_memflag_low]).
    apply b64ctx_zero_recut in BLK6.
    assert (ACCC6 : accessible m6 C 2584) by (eapply addressable_accessible; [exact ADDC6| lia| lia| unfold AAPP_HI; lia]).
    clear VIS5 KREL5 HEAP5 AUX5 AC5 ERR5 MF5 IM5 GM5 RL5 RFS5 CPH5 CHN6 MI5 ST5 F05 F35 BA5a EXD5 ADDR5.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply abn_seg4; [exact CP| exact CAL| exact CCE| exact CAP| exact BLK6| exact ACCC6| exact MI6]|].
    intros msF7 mo7 KREL7 MP7 (m7 & VIS7 & MU7 & WM7 & MI7 & BC7). unfold B64CTX_SIZE in MU7. mpacc MPA MP7.
    assert (CW7 : Forall (aclient_write_ok H LB2) [(C, C + 2584)]).
    { constructor; [| constructor]. right; right; left. exists (p2, C, 2584). split; [exact CIN2| cbn; hlia]. }
    assert (NSWC : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(C, C + 2584)]) by (fw; hlia).
    apply (stk_transport_disjoint asegs _ m6 m7 _ _ ST6) in MU7 as ST7; [| exact WM7| cbn; hlia].
    apply (rw_cells_transport asegs _ m6 m7 _ _ F06) in MU7 as F07; [| exact WM7| cbn; hlia].
    apply (rw_cells_transport asegs _ m6 m7 _ _ F36) in MU7 as F37; [| exact WM7| cbn; hlia].
    apply (rw_cells_transport asegs _ m6 m7 _ _ BA6a) in MU7 as BA7a; [| exact WM7| unhide DJ_AC; cbn; hlia].
    apply (rw_cells_transport asegs _ m6 m7 _ _ EXD6) in MU7 as EXD7; [| exact WM7| unhide DJ_AC; cbn; hlia].
    assert (ERR7 : rw_cells asegs m7 (ATP + -164) [C4 errv6]) by (eapply errno_across; [exact ERR6| exact MU7| exact WM7| unfold ATP; cbn; lia]).
    assert (AUX7 : as_rauxv_ok H m7 B) by (eapply (ah_rauxv_frame H HH); [exact AUX6| exact MU7| exact WM7| exact CW7]).
    assert (HEAP7 : as_RHEAP H s6' LB2 m7) by (eapply (ah_RHEAP_frame H HH); [exact HEAP6| exact MU7| exact WM7| exact CW7]).
    assert (AC7 : ACONST m7) by (eapply ACONST_frame; [exact AC6| exact MU7| exact WM7| constructor; [eapply aconst_ok_aapp; [exact CAP| cbn; lia| cbn; lia]| constructor]]).
    assert (MF7 : MEMFLAG m7 1) by (eapply MEMFLAG_across; [exact MU7| exact WM7| unfold A_mem_inited; cbn; lia| exact MF6]).
    assert (IM7 : IMPL_mem m7) by (eapply IMPL_across; [exact MU7| exact WM7| unfold A_malloc_impl; cbn; lia| exact IM6]).
    assert (GM7 : GOT_mem m7) by (eapply GOT_across; [exact MU7| exact WM7| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM6]).
    assert (RL7 : arelro_lib m7) by (eapply arelro_across7; [exact RL6| exact MU7| fw; hlia]).
    assert (RFS7 : as_RFS H LF m7) by (eapply (RFS_across_wins H HH); [exact RFS6| exact MU7| exact WM7| unhide CFS; fw; right; hlia]).
    assert (CPH7 : CTXPH LB m7 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPH6|]. eapply (magree_lib_munch H HH); [exact HEAP6| intros b Hb; apply SUB12, SUB01; exact Hb| exact MU7| exact WM7|].
      fw. right. split; [hlia|]. split; [hlia|]. intros a (b & Hb & R).
      destruct (Z.lt_ge_cases a C) as [K|K]; [left; exact K|]. destruct (Z.le_gt_cases (C + 2584) a) as [K2|K2]; [right; exact K2|].
      exfalso. eapply (afresh_outside H HH); [exact HEAP6| exact CEIL| right; right; left; exists b; split; [apply SUB01; exact Hb| exact R]| lia]. }
    assert (ADDR7 : addressable m7 A 128) by (eapply addressable_across2; [exact ADDR6| exact AAP| exact MU7| exact WM7| exact NSWC]).
    assert (ADDC7 : addressable m7 C 2584) by (eapply addressable_across2; [exact ADDC6| exact CAP| exact MU7| exact WM7| exact NSWC]).
    assert (CHN8 : as_chain H m7 (bv_unsigned sp + -64) CH2).
    { eapply (chain_via_munch H HH); [exact CHN7| exact MU7|]. intros fp' ra' Hin. pose proof (CHS2 _ _ Hin). cbn. split; [lia| exact I]. }
    destruct (b64ctx_cs_split _ _ BC7) as [BC7a ENB7].
    assert (ACCC7 : accessible m7 C 2584) by (eapply addressable_accessible; [exact ADDC7| lia| lia| unfold AAPP_HI; lia]).
    clear VIS6 KREL6 MI6 AC6 ST6 ERR6 AUX6 MF6 IM6 GM6 RL6 RFS6 CPH6 CHN7 ACCC6 BLK6 F06 F36 BA6a EXD6 ADDR6 ADDC6 MT6 BC7.
    (* [comment removed for export] *)
    rename msF7 into msF8, mo7 into mo8, KREL7 into KREL8, VIS7 into VIS8, m7 into m8, MI7 into MI8.
    rename AC7 into AC8, ST7 into ST8, ERR7 into ERR8, AUX7 into AUX8, HEAP7 into HEAP8, MF7 into MF8, IM7 into IM8, GM7 into GM8.
    rename RL7 into RL8, RFS7 into RFS8, CPH7 into CPH8, F07 into F08, F37 into F38, BA7a into BA8a, EXD7 into EXD8.
    rename BC7a into BC8a, ENB7 into ENB8, ADDR7 into ADDR8, ADDC7 into ADDC8, CHN8 into CHN9.
    pose proof (munch_refl [(C + 2568, C + 2568 + 16); (bv_unsigned sp + -112 - 4096, bv_unsigned sp + -112)] m8) as MU8.
    pose proof (wmono_refl asegs m8) as WM8.
    assert (MT8 : METH_b64 m8) by (apply METHB_of_relro; exact RL8).
    clear ACCC7.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply abn_seg5; exact MI8|].
    intros msF9 mo9 KREL9 MP9 VIS9. mpacc MPA MP9.
    (* [comment removed for export] *)
    pose proof (aencnew_spec H HH) as EN. unfold encnew_stmt in EN.
    eapply (ah_seq H HH).
    { eapply EN with (lo := lo) (B := B) (LB := LB2) (s := s6') (v := 1) (CH := CH2);
        [exact VIS9| ..]; rewrite ?unsigned_lit by (unfold ABN_RA3, R_b64_new_EVP_ENCODE_CTX_new; clear - SPR LO LO0 PHS; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HEAP8
           | |- as_AKREL _ _ _ => exact KREL9
           | |- as_rauxv_ok _ _ _ => exact AUX8
           | |- stk _ _ _ _ => exact ST8
           | |- rw_cells _ _ _ [C4 _] => exact ERR8
           | |- mem_inv _ _ => exact MI8
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- ACONST _ => exact AC8
           | |- as_chain _ _ _ _ => exact CHN9
           | |- forall fp' ra', In (fp', ra') _ -> _ => exact CHS2
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF3|]; unfold PF_b64new, R_b64_new_EVP_ENCODE_CTX_new, ABN_RA3; intros q Hq; apply in_or_app; right; exact Hq
           | |- _ <= as_AL _ _ => unfold ENCCTX_SIZE; cbn [ctxph_cost] in AL4; clear - AL2 AL4 AL6 HAL CM92 CM2584 CM128 CF00 PHK; lia
           | |- MEMFLAG _ _ => exact MF8
           | |- IMPL_mem _ => exact IM8
           | |- GOT_mem _ => exact GM8
           | |- _ mod 2 = 0 => unfold ABN_RA3, R_b64_new_EVP_ENCODE_CTX_new; reflexivity
           | |- lb_bytes _ + _ <= _ => unfold LB2, LB1, ENCCTX_SIZE; rewrite !lb_bytes_cons; cbn [blk_size snd]; clear - BUD; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB2, LB1; cbn [length]; clear - BUDC; lia
           | |- _ => first [exact CEIL | unfold ENCNEW_STACK, CZALLOC_STACK, CMALLOC_STACK, AMALLOC_STACK, FR_EVP_ENCODE_CTX_new, FR_CRYPTO_zalloc, FR_CRYPTO_malloc; clear - SPR SPB LO LO0 PHS CEIL; lia
                            | match goal with |- ?G => idtac "ENLEFT=" G end]
           end | idtac "EN-FAIL:" G; fail ] end. }
    clear EN. intros [msF10 mo10] PO. unfold encnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m10 & errv10 & E & p3 & s10' &
                    VIS10 & KREL10 & MP10 & MI10 & AC10 & ST10 & ERR10 & AUX10 & XP10 & HEAP10 & ENC10 & ADDE10 & MF10 & IM10 & GM10 & AL10). mpacc MPA MP10.
    rewrite (unsigned_lit (bv_unsigned sp + -112)) in ST10, XP10 by lia. rewrite unsigned_lit in ERR10 by (unfold ATP; lia).
    pose proof ENC10 as (rawE & lineE & LR1 & LR2 & ENCB10 & LIN & EIN & BR3 & DU).
    pose proof BR3 as (EP & EAL & _ & EH0 & ECE & EFS & EAP). unfold ENCCTX_SIZE in ECE, EAP, EFS. unfold AIMG_TOP in EH0.
    pose proof (aapp_not_shadowland _ _ EAP) as NSE. unfold ALOWSH_LO, AHI_LO in NSE. hide NSE. hide EFS.
    set (LB3 := (p3, E, ENCCTX_SIZE) :: LB2) in *.
    assert (SUB23 : forall b, In b LB2 -> In b LB3) by (intros b Hb; right; exact Hb).
    assert (EIN3 : In (p3, E, 92) LB3) by (left; reflexivity).
    assert (DJ_AE : A + 128 <= E \/ E + 92 <= A).
    { pose proof (ah_nodup H HH _ _ _ HEAP10) as ND. cbn [map blk_id fst snd] in ND. inversion ND as [|q l NI ND']; subst.
      assert (NE : blk_id (p3, E, 92) <> blk_id (p1, A, 128)) by (cbn; intros EE; apply NI; rewrite EE; right; left; reflexivity).
      pose proof (ah_disj H HH _ _ _ _ _ HEAP10 EIN3 (SUB23 _ AIN2) NE) as D. cbn [blk_addr blk_size fst snd] in D. lia. }
    assert (DJ_CE : C + 2584 <= E \/ E + 92 <= C).
    { pose proof (ah_nodup H HH _ _ _ HEAP10) as ND. cbn [map blk_id fst snd] in ND. inversion ND as [|q l NI ND']; subst.
      assert (NE : blk_id (p3, E, 92) <> blk_id (p2, C, 2584)) by (cbn; intros EE; apply NI; rewrite EE; left; reflexivity).
      pose proof (ah_disj H HH _ _ _ _ _ HEAP10 EIN3 (SUB23 _ CIN2) NE) as D. cbn [blk_addr blk_size fst snd] in D. lia. }
    hide DJ_AE. hide DJ_CE.
    assert (F010 : rw_cells asegs m10 (bv_unsigned sp + -64) [CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F08| left; cbn; lia| fw; hlia]. }
    assert (F310 : rw_cells asegs m10 (bv_unsigned sp + -112) [CB 8 j5; C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_b64_method + 72)); C8 (Z_to_bv 64 A); C8 sp; C8 (Z_to_bv 64 ANEX_RA3)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact F38| left; cbn; lia| fw; hlia]. }
    assert (BA10a : rw_cells asegs m10 A (firstn 18 (bio_cells (bio_hdr1 A_b64_method)))).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact BA8a| eapply aclient_range_block; [exact AIN2| lia| cbn; lia]| fw; hlia]. }
    assert (EXD10 : rw_cells asegs m10 (A + 112) [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact EXD8| eapply aclient_range_block; [exact AIN2| lia| cbn; lia]| fw; hlia]. }
    assert (BC10a : rw_cells asegs m10 C (firstn 10 b64ctx_cs_cells)).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact BC8a| eapply aclient_range_block; [exact CIN2| lia| cbn; lia]| fw; hlia]. }
    assert (ENB10 : rw_cells asegs m10 (C + 2568) [CB (Z.to_nat 16) (poison_bytes (Z.to_nat 16) 0)]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP10); [exact ENB8| eapply aclient_range_block; [exact CIN2| lia| cbn; lia]| fw; hlia]. }
    assert (SHI : forall a Q n, aapp Q n -> 0 <= n -> sh Q <= a < sh Q + nsh n -> ~ rin_ivs memflag_foot a).
    { intros a Q n QAP Qn Ha K. pose proof (sh_aapp_range Q n QAP Qn) as (S1 & S2 & S3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      unfold memflag_foot, A_mem_inited in K. cbn [rin_ivs fst snd] in K. rewrite S0 in S1. clear - K S1 Ha. lia. }
    assert (ADDR10 : addressable m10 A 128) by (eapply (addressable_xpres_gen H); [exact AIN2| unfold AAPP_HI; lia| exact ADDR8| exact XP10| intros a Ha; exact (SHI a A 128 AAP ltac:(lia) Ha)]).
    assert (ADDC10 : addressable m10 C 2584) by (eapply (addressable_xpres_gen H); [exact CIN2| unfold AAPP_HI; lia| exact ADDC8| exact XP10| intros a Ha; exact (SHI a C 2584 CAP ltac:(lia) Ha)]).
    assert (RL10 : arelro_lib m10) by (eapply (arelro_xpres H); [exact RL8| exact XP10| fw; hlia]).
    assert (MT10 : METH_b64 m10) by (apply METHB_of_relro; exact RL10).
    assert (RFS10 : as_RFS H LF m10) by (eapply (RFS_via_xpres H HH); [exact RFS8| exact XP10| fw; hlia]).
    assert (CPH10 : CTXPH LB m10 (CtxReady x)) by (eapply CTXPH_frame_mf; [exact CPH8| eapply (magree_mf_of_xpres H); [exact HEAP8| intros b Hb; apply SUB12, SUB01; exact Hb| exact XP10]]).
    assert (CHN11 : as_chain H m10 (bv_unsigned sp + -64) CH2) by (eapply (chain_via_xpres H HH); [exact CHN9| exact XP10| exact CHS2| apply rin_memflag_low]).
    assert (ACCA10 : accessible m10 A 128) by (eapply addressable_accessible; [exact ADDR10| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCC10 : accessible m10 C 2584) by (eapply addressable_accessible; [exact ADDC10| lia| lia| unfold AAPP_HI; lia]).
    clear VIS8 KREL8 MI8 ST8 ERR8 AUX8 MF8 IM8 GM8 RL8 RFS8 CPH8 CHN9 F08 F38 BA8a EXD8 BC8a ENB8 ADDR8 ADDC8 MT8 AC8 VIS9 KREL9.
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL10| exact VIS10| eapply abn_seg6 with (A := A) (C := C) (E := E) (lo := lo) (j1 := j1) (j2 := j5) (i1 := p1) (i2 := p2) (i3 := p3);
      [exact AAP| exact CAP| exact AP| exact AAL| exact CP| exact EP| exact ECE| unhide DJ_AC; exact DJ_AC| exact BA10a| exact ACCA10| exact BC10a| exact ACCC10| exact AC10| exact MT10
      | exact F010| exact F310| exact ST10| exact CEIL| clear - LO; lia| exact MI10| exact RAE]|].
    intros msF11 mo11 KREL11 MP11 (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m11 & VIS11 & MU11 & WM11 & MI11 & ST11 & BA11a & BC11a). mpacc MPA MP11.
    unfold O_BIO_EXDATA, O_B64_ENCBUF in MU11.
    assert (AIN3 : In (p1, A, 128) LB3) by (apply SUB23; exact AIN2). assert (CIN3 : In (p2, C, 2584) LB3) by (apply SUB23; exact CIN2).
    assert (CW11 : Forall (aclient_write_ok H LB3) [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 112); (C, C + 2568)]).
    { constructor; [left; cbn; lia|]. constructor; [right; right; left; exists (p1, A, 128); split; [exact AIN3| cbn; lia]|].
      constructor; [right; right; left; exists (p2, C, 2584); split; [exact CIN3| cbn; lia]| constructor]. }
    assert (NSW11 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 112); (C, C + 2568)]) by (unhide NSA; unhide NSC; fw; hlia).
    apply (rw_cells_transport asegs _ m10 m11 _ _ EXD10) in MU11 as EXD11; [| exact WM11| unhide DJ_AC; cbn; hlia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ ENB10) in MU11 as ENB11; [| exact WM11| unhide DJ_AC; cbn; hlia].
    apply (rw_cells_transport asegs _ m10 m11 _ _ ENCB10) in MU11 as ENCB11; [| exact WM11| unhide DJ_AE; unhide DJ_CE; cbn; hlia].
    assert (ERR11 : rw_cells asegs m11 (ATP + -164) [C4 errv10]) by (eapply errno_across; [exact ERR10| exact MU11| exact WM11| unfold ATP; cbn; lia]).
    assert (AUX11 : as_rauxv_ok H m11 B) by (eapply (ah_rauxv_frame H HH); [exact AUX10| exact MU11| exact WM11| exact CW11]).
    assert (HEAP11 : as_RHEAP H s10' LB3 m11) by (eapply (ah_RHEAP_frame H HH); [exact HEAP10| exact MU11| exact WM11| exact CW11]).
    assert (AC11 : ACONST m11).
    { eapply ACONST_frame_win; [exact AC10| exact MU11| exact WM11|].
      fw; [left; lia| right; exists A, 128; split; [exact AAP| lia]| right; exists C, 2584; split; [exact CAP| lia]]. }
    assert (MF11 : MEMFLAG m11 1) by (eapply MEMFLAG_across; [exact MU11| exact WM11| unfold A_mem_inited; cbn; lia| exact MF10]).
    assert (IM11 : IMPL_mem m11) by (eapply IMPL_across; [exact MU11| exact WM11| unfold A_malloc_impl; cbn; lia| exact IM10]).
    assert (GM11 : GOT_mem m11) by (eapply GOT_across; [exact MU11| exact WM11| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM10]).
    assert (RL11 : arelro_lib m11) by (eapply arelro_across7; [exact RL10| exact MU11| fw; hlia]).
    assert (RFS11 : as_RFS H LF m11).
    { eapply (RFS_across_wins H HH); [exact RFS10| exact MU11| exact WM11|]. unhide AFS. unhide CFS. fw; [left; lia| right; lia| right; lia]. }
    assert (CPH11 : CTXPH LB m11 (CtxReady x)).
    { eapply CTXPH_frame; [exact CPH10|]. eapply (magree_lib_munch H HH); [exact HEAP10| intros b Hb; apply SUB23, SUB12, SUB01; exact Hb| exact MU11| exact WM11|].
      unhide NSA. unhide NSC. fw; [left; lia| right| right].
      - split; [hlia|]. split; [hlia|]. intros a (b & Hb & R).
        destruct (Z.lt_ge_cases a A) as [K|K]; [left; lia|]. destruct (Z.le_gt_cases (A + 128) a) as [K2|K2]; [right; lia|].
        exfalso. eapply (afresh_outside H HH); [exact HEAP2| exact CEIL| right; right; left; exists b; split; [exact Hb| exact R]| lia].
      - split; [hlia|]. split; [hlia|]. intros a (b & Hb & R).
        destruct (Z.lt_ge_cases a C) as [K|K]; [left; lia|]. destruct (Z.le_gt_cases (C + 2584) a) as [K2|K2]; [right; lia|].
        exfalso. eapply (afresh_outside H HH); [exact HEAP6| exact CEIL| right; right; left; exists b; split; [apply SUB01; exact Hb| exact R]| lia]. }
    assert (ADDR11 : addressable m11 A 128) by (eapply addressable_across2; [exact ADDR10| exact AAP| exact MU11| exact WM11| exact NSW11]).
    assert (ADDC11 : addressable m11 C 2584) by (eapply addressable_across2; [exact ADDC10| exact CAP| exact MU11| exact WM11| exact NSW11]).
    assert (ADDE11 : addressable m11 E 92) by (eapply addressable_across2; [exact ADDE10| exact EAP| exact MU11| exact WM11| exact NSW11]).
    pose proof (bio_cells_join_ex _ _ _ BA11a EXD11) as BA11.
    replace (poison_bytes (Z.to_nat 16) 0) with (zeros 16) in ENB11 by reflexivity.
    pose proof (b64ctx_fresh_join _ _ _ BC11a ENB11) as BC11.
    (* [comment removed for export] *)
    assert (XPT : xpres H LB (bv_unsigned sp) (memflag_foot ++ XS4) m10 m11).
    { eapply (xpres_of_munch_gen H); [exact MU11| exact WM11|]. intros a Ha [HC _]. cbn.
      destruct (aclient_cases H HH _ _ _ _ a HP HC Ha) as [K|K].
      - acb. split; [lia|]. split; [lia|]. split; [lia| exact I].
      - split; [lia|].
        split; [intros R; eapply (afresh_outside H HH); [exact HEAP2| exact CEIL| eapply aclient_addr_weaken; [exact HC| lia| auto]| lia]|].
        split; [intros R; eapply (afresh_outside H HH); [exact HEAP6| exact CEIL| eapply aclient_addr_weaken; [exact HC| lia| exact SUB01]| lia]| exact I]. }
    (* [comment removed for export] *)
    unfold bionew_b64_post. cbn [cfg_ms cfg_model].
    do 14 eexists. exists m11, errv10, s10', A, (abn_R C E p1 p2 p3), XS4.
    split; [exact VIS11|]. split; [exact KREL11|]. split; [exact MPA|].
    split; [exact MI11|]. split; [exact AC11|]. split; [exact ST11|]. split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR11|]. split; [exact AUX11|].
    split.
    { eapply PERM; [exact HEAP11|]. unfold LB3, LB2, LB1, blocks_B64F, abn_R, ENCCTX_SIZE. cbn [bf_id bf_cid bf_eid bf_ctx bf_enc].
      change (Permutation ((rev [(p1, A, 128); (p2, C, 2584); (p3, E, 92)]) ++ LB) ([(p1, A, 128); (p2, C, 2584); (p3, E, 92)] ++ LB)).
      apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev. }
    split. { eapply CTXPH_mono; [| exact CPH11]. intros b Hb. apply in_or_app. right. exact Hb. }
    split. { unfold b64f_bio, abn_R. cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx]. exact BA11. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split. { exists (zeros 2528). split; [vm_compute; reflexivity|]. unfold abn_R. cbn [bf_ctx bf_enc]. exact BC11. }
    split. { unfold B64F_blocks, abn_R, blocks_B64F, ENCCTX_SIZE. cbn [bf_id bf_cid bf_eid bf_ctx bf_enc bf_flags bf_retry bf_nread bf_next bf_prev].
             split; [apply in_or_app; left; left; reflexivity|]. split; [apply in_or_app; left; right; left; reflexivity|]. split; [apply in_or_app; left; right; right; left; reflexivity|].
             split; [exact BR1|]. split; [exact BR2|]. split; [exact BR3|]. lia. }
    split. { unfold B64F_apart, abn_R, BIO_SIZE, B64CTX_SIZE. cbn [bf_ctx bf_enc]. unhide DJ_AC. unhide DJ_AE. unhide DJ_CE. clear - DJ_AC DJ_AE DJ_CE. lia. }
    split. { unfold ENCCTX, abn_R. cbn [bf_enc bf_eid]. exists rawE, lineE. split; [exact LR1|]. split; [exact LR2|]. split; [exact ENCB11|].
             split; [exact LIN|]. split; [apply in_or_app; left; unfold blocks_B64F; cbn; right; right; left; reflexivity|]. split; [exact BR3| exact DU]. }
    split; [exact AP|].
    split. { unfold B64F_shad, abn_R, BIO_SIZE, B64CTX_SIZE. cbn [bf_ctx bf_enc]. split; [exact ADDR11|]. split; [exact ADDC11| exact ADDE11]. }
    split; [exact MF11|]. split; [exact IM11|]. split; [exact GM11|]. split; [exact (METHB_of_relro _ RL11)|]. split; [exact RL11|].
    split; [exact FXS4|]. split; [exact RFS11|].
    split.
    { eapply xpres_trans; [exact (XP1 _)|].
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP2| lia| auto| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans; [eapply (xpres_X_mono H); [exact XP3| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans.
      { eapply (xpres_X_mono H); [eapply (xpres_drop_fresh H HH) with (SP := bv_unsigned sp + -64); [exact HEAP2| lia| lia| | | exact XP4]; cbn; lia|].
        intros q Hq. apply rin_ivs_app. right. cbn [ctxph_foot app] in Hq. exact Hq. }
      eapply xpres_trans.
      { eapply (xpres_of_munch H s LB _ _ _ m m4 m5); [exact HH| exact HP| exact MU5| exact WM5|]. constructor; [left; cbn; lia| constructor]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP6| lia| exact SUB01| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans.
      { eapply (xpres_weaken H); [eapply (xpres_of_munch_fresh H HH) with (SP := bv_unsigned sp) (X := memflag_foot ++ XS4); [exact HEAP6| lia| exact MU7| exact WM7|]| lia| exact SUB01| auto].
        constructor; [right; left; cbn; lia| constructor]. }
      eapply xpres_trans.
      { eapply (xpres_weaken H); [eapply (xpres_of_munch_fresh H HH) with (SP := bv_unsigned sp) (X := memflag_foot ++ XS4); [exact HEAP6| lia| exact MU8| exact WM8|]| lia| exact SUB01| auto].
        constructor; [right; left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      eapply xpres_trans; [eapply (xpres_weaken H); [exact XP10| lia| intros b Hb; apply SUB12, SUB01; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      exact XPT. }
    unfold BIONEW_B64_COST, BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE. cbn [ctxph_cost]. cbn [ctxph_cost] in AL4. unfold ENCCTX_SIZE in AL10. clear - AL2 AL4 AL6 AL10. lia.
  Qed.

End W.
