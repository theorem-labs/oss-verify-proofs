(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AStmt_C1 ECH_AC1_malloc ECH_AC1_free ECH_AC1_freeopt ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_frame ECH_AC4_egs
  N6_strcpy ECH_AC4_debug.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_nil0 : forall m A, 0 <= A <= 2^64 -> rw_cells asegs m A [].
Proof.
  intros m A HA. split; [split; [exact I|]|].
  - unfold bytes_at. cbn [length cells_bytes]. repeat split; try lia.
  - unfold wr_at. cbn [cells_size]. repeat split; try lia.
Qed.

Lemma rin_ivs_in : forall (X : list (Z * Z)) iv a, In iv X -> fst iv <= a < snd iv -> rin_ivs X a.
Proof.
  induction X as [|[u v] X IH]; intros iv a Hin Ha; [destruct Hin|]. cbn. destruct Hin as [<-|Hin]; [left; cbn in Ha; lia| right; eapply IH; [exact Hin| exact Ha]].
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let PERM : rheap_perm H := HHx_rheap_perm H HHx.

  Lemma aerrdebug_spec : errdebug_stmt H.
  Proof.
    unfold errdebug_stmt. intros until CH.
    intros VIS A0 A1 A2 LNR RSF FSN FSL FPOS RSG GSN GSL GPOS SEMP HP KREL BY CN AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM RL EP EXR CBL LS CP RFS LFN CHN CHS PF AL RAE.
    assert (EETA : E = mkERRST (es_slots E) (es_top E) (es_bottom E)) by (destruct E; reflexivity).
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STK : 96 + 8240 <= bv_unsigned sp - lo /\ lo <= bv_unsigned sp - (FR_ERR_set_debug + EGS_STACK)).
    { revert LO. unfold ERRDEBUG_STACK, FR_ERR_set_debug, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK,
        CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK. clear; intros LO; lia. }
    destruct STK as [STK LOA].
    set (SB := blocks_ERRST E) in *. set (es := blk_addr (ec_es c)) in *. set (top := es_top E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (SUBs : forall b, In b SB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; left; exact Hb).
    cbn [ERRPH CTXPH] in EP, CP. pose proof EP as [ES EC]. pose proof CP as [CS CBK].
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBx _ I5)) as BR5. rewrite Z5 in BR5. fold es in BR5. unfold ERRST_SIZE in BR5.
    pose proof BR5 as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_bounds _ _ B7 ltac:(lia)) as (_ & _ & T5 & _). unfold AAPP_HI in T5.
    destruct EXR as (EST & ESZ & ESHs & ESC). apply ERRST_split in EST. destruct EST as [EM OWN]. fold es in EM.
    pose proof EM as (SL & TR & _). fold top in TR.
    pose proof (slot_at_own _ E top OWN SL TR) as [OF OG]. destruct SEMP as [FE GE]. fold top in FE, GE.
    rewrite FE in OF. rewrite GE in OG. cbn [ofield] in OF, OG.
    pose proof (estrs_pos E) as POSE.
    pose proof RSF as ((RFL & RFH & _) & _ & RFL2 & RFH2). pose proof RSG as ((RGL & RGH & _) & _ & RGL2 & RGH2).
    unfold IMG_LO, IMG_HI, AIMG_LO, AIMG_TOP in RFL, RFH, RGL, RGH, RFL2, RFH2, RGL2, RGH2.
    assert (CW0 : AC4W LB m (ErrReady c) x) by (split; [exact MF| split; [exact IM| split; [exact GM| split; [exact RL| split; [exact EP| exact CP]]]]]).
    pose proof (chain_apl_of_RHEAP H HH _ _ _ _ _ HP EC SUBx) as CA.
    pose proof (ah_thr H HH _ _ _ HP) as THR.
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    set (n1 := Z.of_nat (length fs) + 1) in *. set (n2 := Z.of_nat (length gs) + 1) in *.
    subst tp.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS
      | eapply (aed_segA H HHx) with (lo := lo) (c := c) (exl := x) (LB := LB) (E := E) (LF := LF);
        [exact A0| exact A1| exact A2| exact LNR| lia| lia| reflexivity| exact ERR| exact CS| exact ES| exact EC| exact CBL| exact CA| exact LS
        | exact EM| exact AC| exact RL| exact RFS| lia| exact THR| exact SPA| exact ST| exact CEIL| exact LOA| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (u0 & u1 & u2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m1 & XS & j0 &
                             VIS1 & FXS & MU1 & WM1 & MI1 & ST1 & FR1 & ERR1 & CS1 & ES1 & EC1 & LS1 & EM1 & ACC1 & RFS1 & AC1 & RL1).
    fold es in VIS1, EM1, ACC1. fold top in VIS1.
    rewrite OF in VIS1.
    (* [comment removed for export] *)
    pose proof (write_ok_scratch H _ (SB ++ LB) lo (bv_unsigned sp) XS FXS CEIL) as WOK1.
    assert (HP1 : as_RHEAP H s (SB ++ LB) m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact WOK1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH) with (LB := SB ++ LB); [exact AUX| exact MU1| exact WM1| exact WOK1]).
    assert (CW1 : AC4W LB m1 (ErrReady c) x).
    { eapply (AC4W_foot H HH) with (XS := XS) (LIT := ERRNO_X); [exact RFS| exact FXS| apply errno_lowr| exact CEIL| exact HP| exact SUBx| exact MU1| exact WM1| exact CW0]. }
    assert (AGL1 : magree (lib_addr (SB ++ LB)) m m1).
    { eapply (lib_magree_scratch H HH) with (W := XS ++ ERRNO_X); [exact RFS| | exact MU1| exact WM1| exact CEIL|].
      - apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP| exact Hb].
      - apply Forall_app. split; [apply scr_ok_of_scratch; exact FXS| apply Forall_cons; [right; apply errno_low_ok| apply Forall_nil]]. }
    destruct (estrs_agree (SB ++ LB) m m1 E SUBs (fun b Hb => proj1 (POSE b ESZ Hb)) AGL1 ESHs ESC) as [ESH1 ESC1].
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_app. split.
      - eapply Forall_impl; [| exact FXS]. intros iv SC. right. intros fp' ra' Hin.
        pose proof (fs_scratch_range H HH _ _ _ RFS SC). pose proof (ah_chain_range H HH _ _ _ _ _ CHN Hin). lia.
      - apply Forall_cons; [| apply Forall_nil]. right. intros fp' ra' Hin. pose proof (ah_chain_range H HH _ _ _ _ _ CHN Hin).
        unfold ARERRNO, ATP. cbn. lia. }
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR1 as FR2. unfold aed_frame in FR2.
      change (CB 8 j0 :: [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        with ([CB 8 j0; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + 80) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -96 + 16 <= fp').
    { intros fp' ra' [E0|Hin]; [injection E0 as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    clear CH0.
    pose proof CW1 as (MF1 & IM1 & GM1 & RL1' & EP1 & CP1).
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (LB := SB ++ LB) (lo := lo) (B := B) (s := s) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS1| exact HP1| exact KREL1| exact AUX1
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact ST1| exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; unfold CFREE_STACK, AFREE_STACK; lia
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR1| exact MI1| reflexivity
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | exact AC1| exact CHN1
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact CHS1
        | pose proof (CF0 0 ltac:(lia)); pose proof (CM0 (n1 + n2) ltac:(lia)); unfold ERRDEBUG_COST in AL; lia
        | exact IM1| exact GM1 ]. }
    intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HP2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST2, XP2 by lia. rewrite (unsigned_lit ATP) in ERR2 by (unfold ATP; lia).
    destruct (afree_world H _ _ _ m2 _ _ _ _ _ _ CW1 XP2 SUBx FR1 ltac:(lia) EM1 ltac:(lia) ltac:(unfold ERRST_SIZE; lia) LS1) as (CW2 & FR2 & EM2 & LS2).
    fold es in EM2.
    destruct (estrs_agree (SB ++ LB) m1 m2 E SUBs (fun b Hb => proj1 (POSE b ESZ Hb)) (magree_lib_xpres H _ _ _ _ XP2) ESH1 ESC1) as [ESH2 ESC2].
    assert (CHN2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN1|]. intros fp' ra' a Hin Ha. apply XP2; [| split; [left; specialize (CHS1 _ _ Hin); lia| intros []]].
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 Hin) as (Q1 & _). lia. }
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| apply Forall_nil]).
    pose proof CW2 as (MF2 & _ & _ & RL2 & EP2 & CP2).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2
      | eapply (aed_segB H HHx) with (lo := lo) (fs := fs) (fsl := fsl);
        [exact RSF| exact FSN| exact FSL| exact FPOS| exact AC2| exact ST2| exact CEIL| unfold AINTRIN_STACK; lia| exact MI2| lia]|].
    intros msF3 mo3 KREL3 MP3 (w0 & w1 & w2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 & AC3).
    unfold AINTRIN_STACK in MU3.
    assert (W3ok : Forall (aclient_write_ok H (SB ++ LB)) [(bv_unsigned sp + -96 - 4096, bv_unsigned sp + -96)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (HP3 : as_RHEAP H s2' (SB ++ LB) m3) by (eapply (ah_RHEAP_frame H HH); [exact HP2| exact MU3| exact WM3| exact W3ok]).
    assert (AUX3 : as_rauxv_ok H m3 B) by (eapply (ah_rauxv_frame H HH) with (LB := SB ++ LB); [exact AUX2| exact MU3| exact WM3| exact W3ok]).
    assert (MU3' : munch ((bv_unsigned sp + -96 - 4096, bv_unsigned sp + -96) :: [] ++ []) m2 m3) by exact MU3.
    assert (CW3 : AC4W LB m3 (ErrReady c) x).
    { eapply (AC4W_foot H HH) with (XS := []) (LIT := []); [exact RFS2| apply Forall_nil| apply Forall_nil| | exact HP2| exact SUBx| exact MU3'| exact WM3| exact CW2]. lia. }
    assert (AGL3 : magree (lib_addr (SB ++ LB)) m2 m3).
    { eapply (lib_magree_scratch H HH) with (W := []); [exact RFS2| | exact MU3| exact WM3| lia| apply Forall_nil].
      apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP2| exact Hb]. }
    clear MU3'.
    destruct (estrs_agree (SB ++ LB) m2 m3 E SUBs (fun b Hb => proj1 (POSE b ESZ Hb)) AGL3 ESH2 ESC2) as [ESH3 ESC3].
    assert (EM3 : ERRSTm m3 es E).
    { eapply ERRSTm_agree; [exact AGL3| exact EM2|]. intros a' Ha'. right; left. exists (ec_es c). split; [apply SUBx; exact I5| rewrite Z5; revert Ha'; fold es; unfold ERRST_SIZE; intros Ha'; lia]. }
    assert (LS3 : lib_shad (chain_blocks c) m3).
    { eapply lib_shad_frame; [exact LS2|]. eapply magree_mono; [exact AGL3|]. intros a' Ha'. eapply lib_addr_mono; [| exact Ha']. intros b Hb. apply SUBx. eapply chain_blocks_in; [exact EC| exact Hb]. }
    assert (ERR3 : rw_cells asegs m3 ARERRNO [C4 errv]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; cbn; unfold ARERRNO, ATP; lia).
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -96) (CB 8 j0 :: aed_frame s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn; lia).
    assert (RFS3 : as_RFS H LF m3) by (eapply (RFS_stack H HH); [exact RFS2| exact MU3| exact WM3| lia]).
    assert (CHN3 : as_chain H m3 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (achain_below H HH m2 m3); [exact CHN2| exact CHS1| exact MU3|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    pose proof CW3 as (MF3 & IM3 & GM3 & RL3 & EP3 & CP3).
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { pose proof (acmalloc_spec H HH) as CMx. unfold cmalloc_stmt, cmalloc_stmt_at in CMx.
      eapply CMx with (n := n1) (v := 1) (lo := lo) (B := B) (LB := SB ++ LB) (s := s2') (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS3| reflexivity| unfold n1; lia| exact HP3| exact KREL3
        | unfold n1, ERRDEBUG_BYTES in *; lia| lia| exact AUX3
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact ST3| exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; unfold CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK; lia
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR3| exact MI3| reflexivity
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | exact AC3| exact CHN3
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact CHS1
        | rewrite (unsigned_lit AED_RA_M1) by (unfold AED_RA_M1; lia); eapply pf_ok_call; [exact PF|];
          unfold PF_errdebug, PF_ERRDEBUG, PF_cmalloc, pf_shift, AED_RA_M1, R_CRYPTO_malloc_malloc; cbn; intros pp [<-|[]]; cbn; right; right; left; reflexivity
        | unfold ERRDEBUG_COST in AL; pose proof (CMM n1 (n1 + n2) ltac:(unfold n1, n2; lia)); pose proof (CF0 0 ltac:(lia)); lia
        | exact MF3| exact IM3| exact GM3 ]. }
    intros [ms4 mo4] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m4 & errv4 & A1v & junk1 & p1 & s4' &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & RB1 & HP4 & BK1 & AD1 & MF4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST4, XP4 by lia. rewrite (unsigned_lit ATP) in ERR4 by (unfold ATP; lia).
    destruct (amalloc_world H HH _ _ _ _ m4 _ _ (bv_unsigned sp + -96) _ _ _ HP3 SUBx ltac:(lia) CW3 XP4 MF4 FR3 ltac:(lia) EM3 LS3) as (CW4 & FR4 & EM4 & LS4).
    fold es in EM4.
    destruct (estrs_agree (SB ++ LB) m3 m4 E SUBs (fun b Hb => proj1 (POSE b ESZ Hb)) (magree_lib_xpres_mf H _ _ _ _ XP4 MF3 MF4) ESH3 ESC3) as [ESH4 ESC4].
    assert (CHN4 : as_chain H m4 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN3|]. intros fp' ra' a Hin Ha. pose proof (ah_chain_range H HH _ _ _ _ _ CHN3 Hin) as (Q1 & _).
      apply XP4; [lia| split; [left; specialize (CHS1 _ _ Hin); lia| unfold memflag_foot, A_mem_inited; cbn; lia]]. }
    assert (RFS4 : as_RFS H LF m4).
    { eapply (RFS_via_xpres H HH); [exact RFS3| exact XP4|]. unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    set (bk1 := (p1, A1v, n1)) in *.
    pose proof (ah_nodup H HH _ _ _ HP4) as ND4. cbn [map] in ND4. inversion ND4 as [|z l NI1 ND4']; subst z l.
    assert (NB1 : ~ In bk1 (SB ++ LB)) by (intros K; apply NI1; apply (in_map blk_id) in K; exact K).
    assert (NB1' : ~ In bk1 LB) by (intros K; apply NB1; apply SUBx; exact K).
    assert (SUB4 : forall b, In b (SB ++ LB) -> In b (bk1 :: SB ++ LB)) by (intros b Hb; right; exact Hb).
    assert (SUB4x : forall b, In b LB -> In b (bk1 :: SB ++ LB)) by (intros b Hb; right; apply SUBx; exact Hb).
    assert (SUB4s : forall b, In b SB -> In b (bk1 :: SB ++ LB)) by (intros b Hb; right; apply SUBs; exact Hb).
    pose proof (ablocks_apart_notin H HH _ _ _ _ _ _ HP4 (or_introl eq_refl) NB1 (SUBx _ I5) SUB4) as DJ1.
    cbn [blk_addr blk_size bk1 fst snd] in DJ1. rewrite Z5 in DJ1. fold es in DJ1. unfold ERRST_SIZE in DJ1.
    pose proof RB1 as (R1 & R2 & R3 & R4 & R5 & R6 & R7). pose proof (aapp_bounds _ _ R7 ltac:(lia)) as (_ & _ & U1 & _). unfold AAPP_HI in U1.
    assert (SHV1 : shvis m4 A1v (A1v + Z.of_nat (length fs) + 1)).
    { replace (A1v + Z.of_nat (length fs) + 1) with (A1v + n1) by (unfold n1; lia). eapply (ah_blk_shvis H HH); [exact HP4| left; reflexivity]. }
    assert (ACA1 : accessible m4 A1v n1) by (eapply addressable_accessible; [exact AD1| lia| lia| unfold AAPP_HI; lia]).
    assert (ACC4 : accessible m4 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS4 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
      unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    replace (Z.to_nat n1) with (S (length fs)) in BK1 by (unfold n1; lia).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4
      | eapply aed_segC with (lo := lo) (E := E) (fsl := fsl) (junk := junk1) (fo := Some (p1, n1));
        [ exact RSF| exact FSN| exact FSL| exact FPOS| exact LNR| exact EM4| reflexivity| lia| lia| exact B2| exact B7| exact ACC4| lia
        | exact BK1| lia| unfold n1 in *; lia| exact R7| exact ACA1| exact SHV1| unfold n1 in DJ1; lia
        | exact AC4| exact ST4| exact CEIL| unfold ASTRCPY_STACK; lia| exact MI4 ]|].
    intros msF5 mo5 KREL5 MP5 (z0 & z1 & z2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & EM5 & BK1' & ACC5 & AC5).
    unfold ASTRCPY_STACK in MU5. fold es in VIS5, MU5, EM5, ACC5. fold top in VIS5, EM5.
    replace (A1v + Z.of_nat (length fs) + 1) with (A1v + n1) in MU5 by (unfold n1; lia).
    destruct (aheapw_world H HH s4' (bk1 :: SB ++ LB) LB m4 m5 c x lo (bv_unsigned sp + -96 - 8192) (bv_unsigned sp + -96) B errv4 (bv_unsigned sp + -96) _ bk1
                HP4 SUB4x (or_introl eq_refl) NB1' CW4 AUX4 ERR4 FR4 LS4 CEIL ltac:(lia) ltac:(lia) ltac:(lia) MU5 WM5) as (HP5 & CW5 & AUX5 & ERR5 & FR5 & LS5).
    pose proof (lib_magree_dbg H HH s4' (bk1 :: SB ++ LB) (SB ++ LB) SB m4 m5 (ec_es c) bk1 (bv_unsigned sp + -96 - 8192) (bv_unsigned sp + -96) HP4 SUB4 SUBs (SUB4x _ I5) Z5
                  (fun b Hb => POSE b ESZ Hb) (or_introl eq_refl) NB1 ltac:(lia) MU5 WM5) as AGL5.
    destruct (estrs_agree SB m4 m5 E (fun b Hb => Hb) (fun b Hb => proj1 (POSE b ESZ Hb)) AGL5 ESH4 ESC4) as [ESH5 ESC5].
    assert (RFS5 : as_RFS H LF m5).
    { eapply (RFS_dbg H HH) with (L := bk1 :: SB ++ LB) (es := ec_es c) (bk := bk1); [exact RFS4| exact HP4| exact (SUB4x _ I5)| exact Z5| left; reflexivity| | exact MU5| exact WM5]. lia. }
    assert (CHN5 : as_chain H m5 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (achain_below H HH m4 m5); [exact CHN4| exact CHS1| exact MU5|].
      apply Forall_cons; [right; intros fp' ra' Hin; pose proof (ah_chain_range H HH _ _ _ _ _ CHN4 Hin); cbn; lia|].
      apply Forall_cons; [right; intros fp' ra' Hin; pose proof (ah_chain_range H HH _ _ _ _ _ CHN4 Hin); cbn; lia|].
      apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    rewrite OG in VIS5.
    assert (NSW5 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904); (A1v, A1v + n1); (bv_unsigned sp + -96 - 8192, bv_unsigned sp + -96)]).
    { apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ B7)|]. apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ R7)|].
      apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO; lia| apply Forall_nil]. }
    assert (ADb5 : addressable m5 A1v n1) by (eapply addressable_acrossW; [exact AD1| exact R7| exact MU5| exact WM5| exact NSW5]).
    assert (CFZ : as_Cf H 0 = 0) by (pose proof (CFS 0 0 ltac:(lia) ltac:(lia)) as K; change (0 + 0) with 0 in K; pose proof (CF0 0 ltac:(lia)); lia).
    pose proof (CMS n1 n2 ltac:(unfold n1; lia) ltac:(unfold n2; lia)) as CM12. pose proof (CM0 n2 ltac:(unfold n2; lia)) as CM2. unfold ERRDEBUG_COST in AL.
    pose proof CW5 as (MF5 & IM5 & GM5 & RL5 & EP5 & CP5).
    set (E5 := es_with_slot E top (slot_setfile (slot_at E top) A1v (Some (p1, n1)) line)) in *.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_null_spec H HH) with (LB := bk1 :: SB ++ LB) (lo := lo) (B := B) (s := s4') (errv := errv4) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS5| exact HP5| exact KREL5| exact AUX5
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact ST5| exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; unfold CFREE_STACK, AFREE_STACK; lia
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR5| exact MI5| reflexivity
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | exact AC5| exact CHN5
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact CHS1
        | lia
        | exact IM5| exact GM5 ]. }
    intros [ms6 mo6] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0' & v1' & v2' & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & v3' & v4' & v5' & v6' & m6 & s6' &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & HP6 & IM6 & GM6 & AL6).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST6, XP6 by lia. rewrite (unsigned_lit ATP) in ERR6 by (unfold ATP; lia).
    destruct (afree_world H _ _ _ m6 _ _ _ _ _ _ CW5 XP6 SUB4x FR5 ltac:(lia) EM5 ltac:(lia) ltac:(unfold ERRST_SIZE; lia) LS5) as (CW6 & FR6 & EM6 & LS6).
    fold es in EM6.
    pose proof (magree_lib_xpres H _ _ _ _ XP6) as AGL6.
    destruct (estrs_agree (bk1 :: SB ++ LB) m5 m6 E SUB4s (fun b Hb => proj1 (POSE b ESZ Hb)) AGL6 ESH5 ESC5) as [ESH6 ESC6].
    pose proof (addressable_agree _ _ _ bk1 AGL6 (or_introl eq_refl) ADb5) as ADb6. cbn [blk_addr blk_size bk1 fst snd] in ADb6.
    assert (BKc6 : rw_cells asegs m6 A1v [CB (S (length fs)) (fs ++ [Z_to_bv 8 0])]).
    { eapply rw_cells_agree; [exact AGL6| exact BK1'|]. intros a' Ha'. right; left. exists bk1. split; [left; reflexivity|].
      unfold in_range in Ha'. revert Ha'. cbn [cells_size csize blk_addr blk_size bk1 fst snd]. rewrite Nat.add_0_r. unfold n1. intros Ha'. lia. }
    assert (CHN6 : as_chain H m6 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN5|]. intros fp' ra' a Hin Ha. apply XP6; [| split; [left; specialize (CHS1 _ _ Hin); lia| intros []]].
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN5 Hin) as (Q1 & _). lia. }
    assert (RFS6 : as_RFS H LF m6) by (eapply (RFS_via_xpres H HH); [exact RFS5| exact XP6| apply Forall_nil]).
    pose proof CW6 as (MF6 & _ & _ & RL6 & EP6 & CP6).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6
      | eapply (aed_segD H HHx) with (lo := lo) (gs := gs) (gsl := gsl);
        [exact RSG| exact GSN| exact GSL| exact GPOS| exact AC6| exact ST6| exact CEIL| unfold AINTRIN_STACK; lia| exact MI6| lia]|].
    intros msF7 mo7 KREL7 MP7 (w0' & w1' & w2' & e3' & e4' & e5' & e6' & e7' & w3' & w4' & w5' & w6' & m7 & VIS7 & MU7 & WM7 & MI7 & ST7 & AC7).
    unfold AINTRIN_STACK in MU7.
    assert (W7ok : Forall (aclient_write_ok H (bk1 :: SB ++ LB)) [(bv_unsigned sp + -96 - 4096, bv_unsigned sp + -96)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (HP7 : as_RHEAP H s6' (bk1 :: SB ++ LB) m7) by (eapply (ah_RHEAP_frame H HH); [exact HP6| exact MU7| exact WM7| exact W7ok]).
    assert (AUX7 : as_rauxv_ok H m7 B) by (eapply (ah_rauxv_frame H HH) with (LB := bk1 :: SB ++ LB); [exact AUX6| exact MU7| exact WM7| exact W7ok]).
    assert (MU7' : munch ((bv_unsigned sp + -96 - 4096, bv_unsigned sp + -96) :: [] ++ []) m6 m7) by exact MU7.
    assert (CW7 : AC4W LB m7 (ErrReady c) x).
    { eapply (AC4W_foot H HH) with (XS := []) (LIT := []); [exact RFS6| apply Forall_nil| apply Forall_nil| | exact HP6| exact SUB4x| exact MU7'| exact WM7| exact CW6]. lia. }
    assert (AGL7 : magree (lib_addr (bk1 :: SB ++ LB)) m6 m7).
    { eapply (lib_magree_scratch H HH) with (W := []); [exact RFS6| | exact MU7| exact WM7| lia| apply Forall_nil].
      apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP6| exact Hb]. }
    clear MU7'.
    destruct (estrs_agree (bk1 :: SB ++ LB) m6 m7 E SUB4s (fun b Hb => proj1 (POSE b ESZ Hb)) AGL7 ESH6 ESC6) as [ESH7 ESC7].
    pose proof (addressable_agree _ _ _ bk1 AGL7 (or_introl eq_refl) ADb6) as ADb7. cbn [blk_addr blk_size bk1 fst snd] in ADb7.
    assert (BKc7 : rw_cells asegs m7 A1v [CB (S (length fs)) (fs ++ [Z_to_bv 8 0])]).
    { eapply rw_cells_agree; [exact AGL7| exact BKc6|]. intros a' Ha'. right; left. exists bk1. split; [left; reflexivity|].
      unfold in_range in Ha'. revert Ha'. cbn [cells_size csize blk_addr blk_size bk1 fst snd]. rewrite Nat.add_0_r. unfold n1. intros Ha'. lia. }
    assert (EM7 : ERRSTm m7 es E5).
    { eapply ERRSTm_agree; [exact AGL7| exact EM6|]. intros a' Ha'. right; left. exists (ec_es c). split; [apply SUB4x; exact I5| rewrite Z5; revert Ha'; fold es; unfold ERRST_SIZE; intros Ha'; lia]. }
    assert (LS7 : lib_shad (chain_blocks c) m7).
    { eapply lib_shad_frame; [exact LS6|]. eapply magree_mono; [exact AGL7|]. intros a' Ha'. eapply lib_addr_mono; [| exact Ha']. intros b Hb. apply SUB4x. eapply chain_blocks_in; [exact EC| exact Hb]. }
    assert (ERR7 : rw_cells asegs m7 ARERRNO [C4 errv4]) by (eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]; cbn; unfold ARERRNO, ATP; lia).
    assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -96) (CB 8 j0 :: aed_frame s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      by (eapply rw_cells_transport; [exact FR6| exact MU7| exact WM7|]; cbn; lia).
    assert (RFS7 : as_RFS H LF m7) by (eapply (RFS_stack H HH); [exact RFS6| exact MU7| exact WM7| lia]).
    assert (CHN7 : as_chain H m7 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (achain_below H HH m6 m7); [exact CHN6| exact CHS1| exact MU7|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    pose proof CW7 as (MF7 & IM7 & GM7 & RL7 & EP7 & CP7).
    (* [comment removed for export] *)
    assert (LB1 : lb_bytes (bk1 :: SB ++ LB) = n1 + lb_bytes (SB ++ LB)) by reflexivity.
    eapply (ah_seq H HH).
    { pose proof (acmalloc_spec H HH) as CMx. unfold cmalloc_stmt, cmalloc_stmt_at in CMx.
      eapply CMx with (n := n2) (v := 1) (lo := lo) (B := B) (LB := bk1 :: SB ++ LB) (s := s6') (errv := errv4) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS7| reflexivity| unfold n2; lia| exact HP7| exact KREL7
        | rewrite LB1; unfold n1, n2, ERRDEBUG_BYTES in *; lia| cbn [length]; lia| exact AUX7
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact ST7| exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; unfold CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK; lia
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR7| exact MI7| reflexivity
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | exact AC7| exact CHN7
        | rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia; exact CHS1
        | rewrite (unsigned_lit AED_RA_M2) by (unfold AED_RA_M2; lia); eapply pf_ok_call; [exact PF|];
          unfold PF_errdebug, PF_ERRDEBUG, PF_cmalloc, pf_shift, AED_RA_M2, R_CRYPTO_malloc_malloc; cbn; intros pp [<-|[]]; cbn; right; right; right; left; reflexivity
        | lia
        | exact MF7| exact IM7| exact GM7 ]. }
    intros [ms8 mo8] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0' & y1' & y2' & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3' & y4' & y5' & y6' & m8 & errv8 & A2v & junk2 & p2 & s8' &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & RB2 & HP8 & BK2 & AD2 & MF8 & IM8 & GM8 & AL8).
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST8, XP8 by lia. rewrite (unsigned_lit ATP) in ERR8 by (unfold ATP; lia).
    destruct (amalloc_world H HH _ _ _ _ m8 _ _ (bv_unsigned sp + -96) _ _ _ HP7 SUB4x ltac:(lia) CW7 XP8 MF8 FR7 ltac:(lia) EM7 LS7) as (CW8 & FR8 & EM8 & LS8).
    fold es in EM8.
    pose proof (magree_lib_xpres_mf H _ _ _ _ XP8 MF7 MF8) as AGL8.
    destruct (estrs_agree (bk1 :: SB ++ LB) m7 m8 E SUB4s (fun b Hb => proj1 (POSE b ESZ Hb)) AGL8 ESH7 ESC7) as [ESH8 ESC8].
    pose proof (addressable_agree _ _ _ bk1 AGL8 (or_introl eq_refl) ADb7) as ADb8. cbn [blk_addr blk_size bk1 fst snd] in ADb8.
    assert (BKc8 : rw_cells asegs m8 A1v [CB (S (length fs)) (fs ++ [Z_to_bv 8 0])]).
    { eapply rw_cells_agree; [exact AGL8| exact BKc7|]. intros a' Ha'. right; left. exists bk1. split; [left; reflexivity|].
      unfold in_range in Ha'. revert Ha'. cbn [cells_size csize blk_addr blk_size bk1 fst snd]. rewrite Nat.add_0_r. unfold n1. intros Ha'. lia. }
    assert (CHN8 : as_chain H m8 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN7|]. intros fp' ra' a Hin Ha. pose proof (ah_chain_range H HH _ _ _ _ _ CHN7 Hin) as (Q1 & _).
      apply XP8; [lia| split; [left; specialize (CHS1 _ _ Hin); lia| unfold memflag_foot, A_mem_inited; cbn; lia]]. }
    assert (RFS8 : as_RFS H LF m8).
    { eapply (RFS_via_xpres H HH); [exact RFS7| exact XP8|]. unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    set (bk2 := (p2, A2v, n2)) in *.
    pose proof (ah_nodup H HH _ _ _ HP8) as ND8. cbn [map] in ND8. inversion ND8 as [|z l NI2 ND8']; subst z l.
    assert (NB2 : ~ In bk2 (bk1 :: SB ++ LB)) by (intros K; apply NI2; apply (in_map blk_id) in K; exact K).
    assert (NB2' : ~ In bk2 LB) by (intros K; apply NB2; apply SUB4x; exact K).
    assert (SUB8 : forall b, In b (bk1 :: SB ++ LB) -> In b (bk2 :: bk1 :: SB ++ LB)) by (intros b Hb; right; exact Hb).
    assert (SUB8x : forall b, In b LB -> In b (bk2 :: bk1 :: SB ++ LB)) by (intros b Hb; right; apply SUB4x; exact Hb).
    pose proof (ablocks_apart_notin H HH _ _ _ _ _ _ HP8 (or_introl eq_refl) NB2 (SUB4x _ I5) SUB8) as DJ2.
    cbn [blk_addr blk_size bk2 fst snd] in DJ2. rewrite Z5 in DJ2. fold es in DJ2. unfold ERRST_SIZE in DJ2.
    pose proof RB2 as (R1' & R2' & R3' & R4' & R5' & R6' & R7'). pose proof (aapp_bounds _ _ R7' ltac:(lia)) as (_ & _ & U2 & _). unfold AAPP_HI in U2.
    assert (SHV2 : shvis m8 A2v (A2v + Z.of_nat (length gs) + 1)).
    { replace (A2v + Z.of_nat (length gs) + 1) with (A2v + n2) by (unfold n2; lia). eapply (ah_blk_shvis H HH); [exact HP8| left; reflexivity]. }
    assert (ACA2 : accessible m8 A2v n2) by (eapply addressable_accessible; [exact AD2| lia| lia| unfold AAPP_HI; lia]).
    assert (ACC8 : accessible m8 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS8 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
      unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    replace (Z.to_nat n2) with (S (length gs)) in BK2 by (unfold n2; lia).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8
      | eapply aed_segE with (lo := lo) (E := E5) (gsl := gsl) (junk := junk2) (go := Some (p2, n2));
        [ exact RSG| exact GSN| exact GSL| exact GPOS| exact EM8| reflexivity| lia| lia| exact B2| exact B7| exact ACC8| lia
        | exact BK2| lia| unfold n2 in *; lia| exact R7'| exact ACA2| exact SHV2| unfold n2 in DJ2; lia
        | exact AC8| exact ST8| exact CEIL| unfold ASTRCPY_STACK; lia| exact MI8| exact FR8| exact RAE ]|].
    intros msF9 mo9 KREL9 MP9 (z0' & z1' & z2' & f1' & f2' & f3' & f4' & f5' & f6' & f7' & z3' & z4' & z5' & z6' & m9 & VIS9 & MU9 & WM9 & MI9 & ST9 & EM9 & BK2' & AC9).
    unfold ASTRCPY_STACK in MU9. fold es in VIS9, MU9, EM9. fold top in EM9.
    replace (A2v + Z.of_nat (length gs) + 1) with (A2v + n2) in MU9 by (unfold n2; lia).
    destruct (aheapw_world H HH s8' (bk2 :: bk1 :: SB ++ LB) LB m8 m9 c x lo (bv_unsigned sp - 8192) (bv_unsigned sp) B errv8 (bv_unsigned sp) [] bk2
                HP8 SUB8x (or_introl eq_refl) NB2' CW8 AUX8 ERR8 ltac:(apply rw_cells_nil0; lia) LS8 CEIL ltac:(lia) ltac:(lia) ltac:(lia) MU9 WM9) as (HP9 & CW9 & AUX9 & ERR9 & _ & LS9).
    assert (SMALL1 : forall b, In b (bk1 :: SB) -> 0 <= blk_size b <= 32).
    { intros b [<-|Hb]; [cbn [blk_size bk1 snd]; unfold n1; lia| exact (POSE b ESZ Hb)]. }
    assert (SUB1s : forall b, In b (bk1 :: SB) -> In b (bk1 :: SB ++ LB)) by (intros b [<-|Hb]; [left; reflexivity| right; apply SUBs; exact Hb]).
    pose proof (lib_magree_dbg H HH s8' (bk2 :: bk1 :: SB ++ LB) (bk1 :: SB ++ LB) (bk1 :: SB) m8 m9 (ec_es c) bk2 (bv_unsigned sp - 8192) (bv_unsigned sp)
                  HP8 SUB8 SUB1s (SUB8x _ I5) Z5 SMALL1 (or_introl eq_refl) NB2 ltac:(lia) MU9 WM9) as AGL9.
    destruct (estrs_agree (bk1 :: SB) m8 m9 E (fun b Hb => or_intror Hb) (fun b Hb => proj1 (POSE b ESZ Hb)) AGL9 ESH8 ESC8) as [ESH9 ESC9].
    pose proof (addressable_agree _ _ _ bk1 AGL9 (or_introl eq_refl) ADb8) as ADb9. cbn [blk_addr blk_size bk1 fst snd] in ADb9.
    assert (BKc9 : rw_cells asegs m9 A1v [CB (S (length fs)) (fs ++ [Z_to_bv 8 0])]).
    { eapply rw_cells_agree; [exact AGL9| exact BKc8|]. intros a' Ha'. right; left. exists bk1. split; [left; reflexivity|].
      unfold in_range in Ha'. revert Ha'. cbn [cells_size csize blk_addr blk_size bk1 fst snd]. rewrite Nat.add_0_r. unfold n1. intros Ha'. lia. }
    assert (NSW9 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904); (A2v, A2v + n2); (bv_unsigned sp - 8192, bv_unsigned sp)]).
    { apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ B7)|]. apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ R7')|].
      apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO; lia| apply Forall_nil]. }
    assert (ADc9 : addressable m9 A2v n2) by (eapply addressable_acrossW; [exact AD2| exact R7'| exact MU9| exact WM9| exact NSW9]).
    assert (RFS9 : as_RFS H LF m9).
    { eapply (RFS_dbg H HH) with (L := bk2 :: bk1 :: SB ++ LB) (es := ec_es c) (bk := bk2); [exact RFS8| exact HP8| exact (SUB8x _ I5)| exact Z5| left; reflexivity| | exact MU9| exact WM9]. lia. }
    pose proof CW9 as (MF9 & IM9 & GM9 & RL9 & EP9 & CP9).
    (* [comment removed for export] *)
    assert (SL1 : length (es_slots E) = 16%nat) by exact SL.
    unfold E5 in EM9. rewrite (slot_at_upd E top _ SL1 TR) in EM9. rewrite (es_with_slot_twice E top _ _ SL1 TR) in EM9.
    change (es_with_slot E top (slot_setfunc (slot_setfile (slot_at E top) A1v (Some (p1, n1)) line) A2v (Some (p2, n2))))
      with (errst_debug E A1v (Some (p1, n1)) line A2v (Some (p2, n2))) in EM9.
    set (E' := errst_debug E A1v (Some (p1, n1)) line A2v (Some (p2, n2))) in *.
    set (sl' := mkSLOT (sl_flags (slot_at E top)) (sl_buffer (slot_at E top)) A1v (Some (p1, n1)) line A2v (Some (p2, n2))).
    pose proof (blocks_slots_fill_perm (es_slots E) (Z.to_nat top) sl' (slot_clear 0) ltac:(rewrite SL1; lia)) as PFm.
    fold (slot_at E top) in PFm. unfold blocks_slot at 1 in PFm. rewrite FE, GE in PFm. specialize (PFm eq_refl).
    assert (EB : blocks_ERRST E' = blocks_slots (slot_upd (es_slots E) (Z.to_nat top) sl')) by reflexivity.
    assert (PMF : Permutation (bk2 :: bk1 :: SB ++ LB) (blocks_ERRST E' ++ LB)).
    { rewrite EB. eapply Permutation_trans; [apply perm_swap|]. change (bk1 :: bk2 :: SB ++ LB) with ((bk1 :: bk2 :: SB) ++ LB).
      apply Permutation_app_tail. exact PFm. }
    assert (INE' : forall b, In b (blocks_ERRST E') -> b = bk1 \/ b = bk2 \/ In b SB).
    { intros b Hb. rewrite EB in Hb. pose proof (Permutation_in _ (Permutation_sym PFm) Hb) as K. cbn [app blocks_of sl' sl_file sl_file_o sl_func sl_func_o] in K.
      destruct K as [K|[K|K]]; [left; symmetry; exact K| right; left; symmetry; exact K| right; right; exact K]. }
    apply (ah_done H HH). unfold errdebug_post. cbn [cfg_ms cfg_model].
    exists z0', z1', z2', (Z_to_bv 64 A2v), f1', f2', f3', f4', f5', f6', f7', z3', z4', z5', z6', m9, errv8, s8', A1v, A2v, p1, p2, XS.
    cbv zeta. fold n1 n2. fold E'.
    split; [exact VIS9|].
    split. { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); [exact MP2|]. eapply (ah_mpres_trans H HH); [exact MP3|].
             eapply (ah_mpres_trans H HH); [exact MP4|]. eapply (ah_mpres_trans H HH); [exact MP5|]. eapply (ah_mpres_trans H HH); [exact MP6|].
             eapply (ah_mpres_trans H HH); [exact MP7|]. eapply (ah_mpres_trans H HH); [exact MP8| exact MP9]. }
    split. { unfold c4_frame. cbn [cfg_model]. split; [exact KREL9|]. split; [exact MI9|]. split; [exact AC9|]. split; [exact ST9|]. split; [exact AUX9|].
             split; [eapply PERM; [exact HP9| exact PMF]|]. split; [exact MF9|]. split; [exact IM9|]. split; [exact GM9| exact RL9]. }
    split; [rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR9|]. split; [exact RB1|]. split; [exact RB2|].
    split; [exact EP9|]. split; [exact CP9|].
    split.
    { split; [| split; [| split]].
      - apply ERRST_split. split; [exact EM9|].
        pose proof OWN as OWN'. rewrite EETA in OWN'. fold top in OWN'.
        rewrite EB. unfold E', errst_debug. cbv zeta. fold top. fold sl'.
        apply (ERROWN_upd SB (es_slots E) (Z.to_nat top) sl' top (es_bottom E) top (es_bottom E)); [exact OWN'|].
        intros LBx HIN. cbn [sl' sl_file sl_file_o sl_func sl_func_o ofield].
        split; (split; [lia|]; split; [unfold n1, n2; lia|]); apply HIN; cbn [blocks_slot sl' sl_file sl_file_o sl_func sl_func_o blocks_of app]; [left| right; left]; reflexivity.
      - unfold estrs_ok, E', errst_debug. cbv zeta. cbn [es_slots]. apply own_slot_upd; [exact ESZ| cbn [sl_file_o sl_func_o oszb]; unfold n1, n2; lia].
      - unfold lib_shad. apply Forall_forall. intros b Hb. destruct (INE' b Hb) as [->|[->|HbS]]; [exact ADb9| exact ADc9| exact (proj1 (Forall_forall _ _) ESH9 _ HbS)].
      - unfold estrs_cells. apply Forall_forall. intros b Hb. destruct (INE' b Hb) as [->|[->|HbS]].
        + exists (fs ++ [Z_to_bv 8 0]). cbn [blk_addr blk_size bk1 fst snd]. replace (Z.to_nat n1) with (S (length fs)) by (unfold n1; lia). exact BKc9.
        + exists (gs ++ [Z_to_bv 8 0]). cbn [blk_addr blk_size bk2 fst snd]. replace (Z.to_nat n2) with (S (length gs)) by (unfold n2; lia). exact BK2'.
        + exact (proj1 (Forall_forall _ _) ESC9 _ HbS). }
    split; [exact LS9|]. split; [exact FXS|].
    split.
    { set (X := XS ++ ERRNO_X ++ memflag_foot ++ errph_foot (ErrReady c)).
      assert (XSTK : forall ma mb slo shi, munch [(slo, shi)] ma mb -> wmono asegs ma mb -> as_RHEAP H s (SB ++ LB) m -> aceil <= slo -> shi <= bv_unsigned sp ->
                xpres H LB (bv_unsigned sp) X ma mb).
      { intros ma mb slo shi MUx WMx HPx CEx SHx. eapply (xpres_weaken H (SB ++ LB) LB); [| apply Z.le_refl| exact SUBx| intros ax K; exact K].
        eapply (xpres_of_munch H s (SB ++ LB)); [exact HH| exact HPx| exact MUx| exact WMx|]. apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      assert (XFR : forall L' ma mb, xpres H L' (bv_unsigned sp + -96) [] ma mb -> (forall b, In b LB -> In b L') -> xpres H LB (bv_unsigned sp) X ma mb).
      { intros L' ma mb XPx SUBx'. eapply xpres_weaken; [exact XPx| lia| exact SUBx'| intros a []]. }
      assert (XMF : forall L' ma mb, xpres H L' (bv_unsigned sp + -96) memflag_foot ma mb -> (forall b, In b LB -> In b L') -> xpres H LB (bv_unsigned sp) X ma mb).
      { intros L' ma mb XPx SUBx'. eapply xpres_weaken; [exact XPx| lia| exact SUBx'|].
        intros a Ka. unfold X. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). left. exact Ka. }
      assert (XE : forall a, blk_addr (ec_es c) <= a < blk_addr (ec_es c) + 904 -> rin_ivs X a).
      { intros a Ha. unfold X. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). right.
        cbn. left. unfold ERRST_SIZE. lia. }
      eapply xpres_trans.
      { eapply (xpres_weaken H (SB ++ LB) LB); [| apply Z.le_refl| exact SUBx| intros ax K; exact K].
        eapply (xpres_of_munch H s (SB ++ LB)); [exact HH| exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_app. split.
        - apply Forall_forall. intros iv Hiv. right. intros a Ha. unfold X. apply (proj2 (rin_ivs_app _ _ _)). left. eapply rin_ivs_in; [exact Hiv| exact Ha].
        - apply Forall_cons; [| apply Forall_nil]. right. intros a Ha. unfold X. apply (proj2 (rin_ivs_app _ _ _)). right. apply (proj2 (rin_ivs_app _ _ _)). left.
          cbn. cbn in Ha. left. lia. }
      eapply xpres_trans; [apply (XFR _ _ _ XP2 SUBx)|].
      eapply xpres_trans; [apply (XSTK _ _ _ _ MU3 WM3 HP ltac:(lia) ltac:(lia))|].
      eapply xpres_trans; [apply (XMF _ _ _ XP4 SUBx)|].
      eapply xpres_trans; [eapply (xpres_dbgw H HH) with (L := bk1 :: SB ++ LB) (bk := bk1); [exact HP4| exact SUB4x| left; reflexivity| exact NB1'| exact XE| | | | exact MU5| exact WM5]; lia|].
      eapply xpres_trans; [apply (XFR _ _ _ XP6 SUB4x)|].
      eapply xpres_trans; [apply (XSTK _ _ _ _ MU7 WM7 HP ltac:(lia) ltac:(lia))|].
      eapply xpres_trans; [apply (XMF _ _ _ XP8 SUB4x)|].
      eapply (xpres_dbgw H HH) with (L := bk2 :: bk1 :: SB ++ LB) (bk := bk2); [exact HP8| exact SUB8x| left; reflexivity| exact NB2'| exact XE| | | | exact MU9| exact WM9]; lia. }
    split; [exact RFS9|].
    unfold ERRDEBUG_COST. lia.
  Qed.
End W.
