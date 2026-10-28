(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsCall AsWalk AsStack0 ECH_AImg ECH_Xpres ECH_ARep
  ECH_ALib ECH_Iface ECH_AKit ECH_AsKit ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C1 ECH_AC1_free ECH_AStmt_C2 ECH_AC2_small ECH_AStmt_C5 ECH_AC5_small
  ECH_AStmt_C3 ECH_AC3_ready ECH_AC4_frame ECH_AKitS ECH_AC3_newex ECH_AC3_newexW ECH_AC3_newex2 ECH_AC3_phase.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis GDF : getdefctx_fresh_stmt H.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma not_rin_of_Forall : forall XS a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) XS -> ~ rin_ivs XS a.
  Proof.
    intros XS a F Ha. induction XS as [|iv XS IH]; cbn in Ha; [tauto|].
    pose proof (Forall_inv F) as F1. cbn in F1. pose proof (Forall_inv_tail F) as F2. destruct Ha as [R|R]; [lia | exact (IH F2 R)].
  Qed.


  (* [comment removed for export] *)
  Lemma Forall_of_dj : forall XS A n, disjoint_from XS A n -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XS.
  Proof. intros XS A n. induction XS as [|[l h] XS IH]; cbn; intros D; constructor; [cbn; tauto| apply IH; tauto]. Qed.
  Lemma not_rin_of_dj : forall XS A n a, disjoint_from XS A n -> A <= a < A + n -> ~ rin_ivs XS a.
  Proof.
    intros XS A n a D Ha. apply not_rin_of_Forall. eapply Forall_impl; [| exact (Forall_of_dj _ _ _ D)]. cbn beta. intros iv K. lia.
  Qed.
  Lemma nodup_ids_app_ne3 : forall (l1 l2 : list block) b1 b2,
    List.NoDup (map blk_id (l1 ++ l2)) -> In b1 l1 -> In b2 l2 -> blk_id b1 <> blk_id b2.
  Proof.
    induction l1 as [|c l1 IH]; intros l2 b1 b2 ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct H1 as [->|H1]; [| exact (IH _ _ _ ND' H1 H2)].
    intros E. apply NI. rewrite map_app. apply in_or_app. right. rewrite E. apply in_map. exact H2.
  Qed.
  (* [comment removed for export] *)
  Lemma asegs_find_none_high3 : forall a n, 1 <= n -> 12599296 <= a -> find_segment asegs a n = None.
  Proof.
    intros a n Hn Ha. unfold asegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
    cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
         AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
         AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
    destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 1593344)); cbn [andb]; try (exfalso; lia).
    destruct (Z.leb_spec 1658880 a); destruct (Z.leb_spec (a + n) (1658880 + 4046848)); cbn [andb]; try (exfalso; lia).
    destruct (Z.leb_spec 5705728 a); destruct (Z.leb_spec (a + n) (5705728 + 495616)); cbn [andb]; try (exfalso; lia).
    destruct (Z.leb_spec 6201344 a); destruct (Z.leb_spec (a + n) (6201344 + 6397952)); cbn [andb]; try (exfalso; lia).
    reflexivity.
  Qed.
  Lemma amrd_raw : forall m (x : word), 12599296 <= bv_unsigned x -> mrd asegs m x = m x.
  Proof.
    intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. unfold seg_rom, memory_read.
    rewrite asegs_find_none_high3; [reflexivity| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma rw_cells_same_raw : forall m m' A cs a,
    rw_cells asegs m A cs -> rw_cells asegs m' A cs -> 12599296 <= A -> A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a).
  Proof.
    intros m m' A cs a [[W1 B1] _] [[W2 B2] _] HA Ha.
    pose proof (cells_bytes_length cs W1) as CL.
    destruct B1 as (HA1 & HL & R1). destruct B2 as (_ & _ & R2).
    specialize (R1 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)). specialize (R2 (Z.to_nat (a - A)) ltac:(rewrite CL; lia)).
    rewrite Z2Nat.id in R1, R2 by lia. replace (A + (a - A)) with a in R1, R2 by lia.
    rewrite amrd_raw in R1 by (unfold wa; rewrite unsigned_lit by lia; lia).
    rewrite amrd_raw in R2 by (unfold wa; rewrite unsigned_lit by lia; lia).
    congruence.
  Qed.
  Lemma xpres_of_munch_eq : forall LB SP X W m m',
    munch W m m' -> wmono asegs m m' ->
    (forall a, 0 <= a < 2^64 -> xclient H LB SP X a -> outside W a \/ m' (wa a) = m (wa a)) ->
    xpres H LB SP X m m'.
  Proof.
    intros LB SP X W m m' MU WM HO a Ha HC. split.
    - destruct (HO a Ha HC) as [O|E]; [| exact E]. unfold wa. apply MU. rewrite unsigned_lit by lia. exact O.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma outside_of_dj : forall W A n a, disjoint_from W A n -> A <= a < A + n -> outside W a.
  Proof. intros W A n a. induction W as [|[l h] W IH]; cbn; intros D Ha; [exact I|]. split; [lia| apply IH; tauto]. Qed.
  Lemma sh_in_block : forall B k x, B mod 8 = 0 -> B <= x < B + k -> sh B <= sh x < sh B + nsh k.
  Proof. intros B k x M Hx. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.

  Lemma chain_via_xpres : forall LB SP X m m' cur CH,
    as_chain H m cur CH -> xpres H LB SP X m m' -> (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) ->
    (forall a, rin_ivs X a -> a < aceil) -> as_chain H m' cur CH.
  Proof.
    intros LB SP X m m' cur CH C XP HS HX. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3). acb.
    apply XP; [lia|]. split; [left; lia|]. intros K. pose proof (HX _ K). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_miss_foot : forall LF FOOT XS B k x,
    Forall (fun iv : Z * Z => snd iv <= AIMG_TOP) FOOT -> Forall (fs_scratch H LF) XS ->
    aapp (as_FSB H) AFS_SIZE ->
    AIMG_TOP <= B -> B + k < AAPP_HI -> (B + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= B - 16) ->
    B <= x < B + k -> ~ rin_ivs (FOOT ++ XS) (sh x).
  Proof.
    intros LF FOOT XS B k x FF FX F4 BT BH BFS Hx R. apply rin_ivs_app in R.
    pose proof (aapp_not_shadowland _ _ F4) as F5.
    assert (SX : sh AIMG_TOP <= sh x /\ sh x < AHI_LO).
    { split; [apply sh_mono; lia|]. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    assert (STOP : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite STOP in SX. unfold AIMG_TOP, AHI_LO, ALOWSH_LO, AFS_SIZE, AAPP_HI in *.
    destruct R as [R|R].
    - revert R. apply not_rin_of_Forall. eapply Forall_impl; [| exact FF]. cbn beta. intros iv K. lia.
    - revert R. apply not_rin_of_Forall. eapply Forall_impl; [| exact FX]. cbn beta. intros iv K.
      destruct K as [->|(k' & ff & fp & FR & K)]; [cbn [fst snd]; unfold AFS_FLAGS; clear - SX F5; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FR) as (K0 & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & _).
      unfold AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP in R1, R2, P1, P2, P3, P4, P5, P6.
      assert (FS : fsz k' = 8 * fshn k' /\ 0 <= fshn k') by (unfold fsz, fshn; split; [lia| apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]]).
      destruct K as [->|[->| ->]]; cbn [fst snd]; [clear - SX F5 P5 P6 FS; lia| clear - SX F5 P3 P4; lia|].
      unfold sh. rewrite ASHADOW_BASE_val. clear SX. destruct BFS as [D|D].
      + assert (Q : x / 8 + 3 <= ff / 8).
        { replace (x / 8 + 3) with ((x + 24) / 8) by (rewrite <- (Z.div_add x 3 8) by lia; reflexivity). apply Z.div_le_mono; lia. }
        lia.
      + assert (Q : ff / 8 + (fshn k' + 2) <= x / 8).
        { replace (ff / 8 + (fshn k' + 2)) with ((ff + (fshn k' + 2) * 8) / 8) by (rewrite <- (Z.div_add ff (fshn k' + 2) 8) by lia; reflexivity).
          apply Z.div_le_mono; lia. }
        lia.
  Qed.
  (* [comment removed for export] *)
  Lemma cnewex_spec : cnewex_stmt H.
  Proof.
    unfold cnewex_stmt. intros until CH.
    intros VIS A0 A1 A2 AD XR AD8 ADB ACC AIN SEPR HP KREL BUD BUDC AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL CPH RFS LFN CHN CHS PF CLO HAL RAE.
    subst a0 a1 a2. subst tp. unfold errno_addr in ERR |- *.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). acb.
    assert (STK0 : 0 <= ctxph_stack ph).
    { destruct ph; cbn [ctxph_stack]; unfold CTXINIT_STACK, AREALLOC_STACK, GETDEFCTX_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_get_default_context; lia. }
    assert (LO' : lo <= bv_unsigned sp - 8432 /\ lo <= bv_unsigned sp - 240 - ctxph_stack ph).
    { revert LO STK0. unfold CNEWEX_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, GETGLOBAL_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
        CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
        FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock. clear. intros LO STK0. split; lia. }
    destruct LO' as [LO' LOg].
    (* [comment removed for export] *)
    destruct AIN as ([[bp bA] bN] & BIN & BLO & BHI). cbn [blk_addr blk_size fst snd] in BLO, BHI.
    pose proof (ah_blocks H HH _ _ _ _ HP BIN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5, B6, B7.
    unfold AIMG_TOP in B4. unfold AFS_SIZE in B6.
    pose proof (ah_thr H HH _ _ _ HP) as THR.
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AFS_SIZE, AIMG_TOP in F1, F2. pose proof (aapp_not_shadowland _ _ F4) as F5. unfold AFS_SIZE, ALOWSH_LO, AHI_LO in F5.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply anx_pre; [exact ST| exact CEIL| | exact SPA| exact MI]|].
    { unfold CNEWEX_READY_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
        CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
        FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock. clear - LO' STK0. lia. }
    intros msF1 mo1 KREL1 MP1 (sp1 & jl & gapc & m1 & VIS1 & MU1 & WM1 & MI1 & FR1 & LOC1 & GAP1 & GSZ & SP1 & SP32 & ST1).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| |].
    { eapply anx_segA1 with (lo := lo) (bA := bA) (bN := bN); try eassumption; try reflexivity; try lia.
      pose proof (gdf_frames_lt ph). destruct ph; cbn [ctxph_frames] in LFN; lia. }
    clear VIS VIS1 KREL.
    intros msF2 mo2 KREL2 MP2 PO. unfold anx_m1 in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & j0 & j1 & j2 & hj & sj
                    & VIS2 & MU2 & WM2 & MI2 & ST2 & AC2 & RFS2 & FRESH & FR2 & LOC2 & GAP2 & FF2 & SH2 & FP2).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & _ & _ & _).
    change (fsz 2) with 256 in R2, P6. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP in R1, R2, P1, P2, P3, P4, P5, P6.
    assert (SHIN : sh (as_FSB H) <= sh ff /\ sh ff + 32 <= sh (as_FSB H + AFS_SIZE))
      by (unfold sh, AFS_SIZE; clear - P5 P6 M64; Z.div_mod_to_equations; lia).
    set (shf := sh ff) in *.
    assert (SHFB : 2148993224 <= shf /\ shf + 32 <= AHI_LO)
      by (subst shf; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - R1 R2 ACEILB; Z.div_mod_to_equations; lia). unfold AHI_LO in SHFB.
    pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FXS4. change (fsz 2) with 256 in FXS4. change (fshn 2) with 32 in FXS4. fold shf in FXS4. unfold AFS_FLAGS in FXS4.
    (* [comment removed for export] *)
    assert (CW2 : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)]).
    { unfold aclient_write_ok, AFS_FLAGS, AFS_SIZE in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; right; left. exact SHIN. }
    assert (HP2 : as_RHEAP H s LB m2) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU2| exact WM2| exact CW2]).
    assert (AUX2 : as_rauxv_ok H m2 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU2| exact WM2| exact CW2]).
    assert (DJimg : forall A n, A + n <= 12599296 -> disjoint_from [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] A n)
      by (intros A' n' K; cbn; clear - K CEIL ACEILB F1 P1 R1 SHFB; repeat split; lia).
    assert (ERR2 : rw_cells asegs m2 (ATP + -164) [C4 errv]).
    { revert ERR. rewrite unsigned_lit by (unfold ATP; lia). intros ERR. eapply errno_across; [exact ERR| exact MU2| exact WM2| apply DJimg; unfold ATP; lia]. }
    assert (IM2 : IMPL_mem m2) by (eapply IMPL_across; [exact MU2| exact WM2| apply DJimg; unfold A_malloc_impl; lia| exact IM]).
    assert (GM2 : GOT_mem m2) by (eapply GOT_across; [exact MU2| exact WM2| apply DJimg; unfold A_got_CRYPTO_malloc; lia| exact GM]).
    assert (MF2 : MEMFLAG m2 1) by (eapply MEMFLAG_across; [exact MU2| exact WM2| apply DJimg; unfold A_mem_inited; lia| exact MF]).
    assert (RL2 : arelro_lib m2).
    { eapply arelro_across; [exact RL| exact MU2| unfold AFS_FLAGS; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - CEIL ACEILB F1 P1 R1 SHFB; lia]. }
    assert (AGL2 : magree (lib_addr LB) m m2).
    { eapply (lib_magree_scratch H HH) with (LF := LF) (lo := lo) (hi := bv_unsigned sp); [exact RFS| | exact MU2| exact WM2| exact CEIL| apply (scr_ok_of_scratch H); exact FXS4].
      apply Forall_forall. intros b Hb. exact (ah_blocks H HH _ _ _ _ HP Hb). }
    assert (CPH2 : CTXPH LB m2 ph) by (eapply CTXPH_frame; [exact CPH| exact AGL2]).
    assert (XP2 : xpres H LB (bv_unsigned sp) ((ad, ad + 16) :: ctxph_foot ph ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)]) m m2).
    { eapply (xpres_of_munch H s LB _ _ _ m m m2); [exact HH| exact HP| exact MU2| exact WM2|]. unfold AFS_FLAGS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd app];
        first [ left; lia | right; intros q Hq; cbn; right; apply rin_ivs_app; right; cbn; lia ]. }
    assert (CH0 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m2); [exact CHN| exact CHS| exact MU2|]. unfold AFS_FLAGS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; clear - LO' STK0 F1 F2 P1 P2 P4 P6 R1 R2 SHFB CEIL SPR ACEILB; lia. }
    assert (CH1 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR2 as FRl.
      lazymatch type of FRl with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
        change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: rest) with ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ rest) in FRl end.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRl. destruct FRl as [_ FRl]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FRl.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -104 + 88) by lia.
      first [exact FRl | revert FRl; rewrite !Z_to_bv_bv_unsigned; intros FRl; exact FRl]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> sp1 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : sp1 mod 16 = 0) by (clear - SP32; Z.div_mod_to_equations; lia).
    assert (SH02 : ctxph_sh0 ph m2 lo (Z_to_bv 64 sp1)).
    { destruct ph; [| exact I]. cbn [ctxph_sh0] in SH0 |- *. rewrite unsigned_lit by lia.
      eapply stack0_sub; [eapply stack0_transport; [exact SH0| exact MU2| exact WM2|]| lia| lia| clear - SP32; Z.div_mod_to_equations; lia].
      unfold AFS_FLAGS. repeat apply Forall_cons; try apply Forall_nil.
      - apply stack0_ok_app. unfold AHI_LO. lia.
      - eapply stack0_ok_aapp; [exact F4| lia| unfold AFS_SIZE; lia].
      - eapply stack0_ok_aapp; [exact F4| lia| unfold AFS_SIZE; lia].
      - eapply stack0_ok_aapp; [exact F4| lia| unfold AFS_SIZE; lia].
      - right. cbn [fst snd]. subst shf. replace (sh ff + 32) with (sh (ff + 256)) by (unfold sh; clear - M8; Z.div_mod_to_equations; lia). apply sh_mono. clear - R2; lia. }
    (* [comment removed for export] *)
    pose proof (getglobal_spec H HHx GDF) as GG. unfold getglobal_stmt, getdefctx_stmt_at, getdefctx_stmt_for in GG.
    eapply (ah_seq H HH).
    { eapply (GG ph) with (lo := lo) (B := B) (LB := LB) (s := s) (LF := (2, ff, fp) :: LF) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS2| ..];
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP2| exact KREL2| exact BUD| exact BUDC| exact AUX2| exact ST2| exact CEIL| exact SH02| exact ERR2| exact MI2| exact AC2| exact MF2| exact IM2| exact GM2| exact RL2
                     | exact CPH2| exact RFS2| exact CH1| exact CHS1| exact CLO].
      all: match goal with
           | |- _ mod 16 = 0 => exact SP16'
           | |- (_ <= AFS_MAXLIVE)%nat => cbn [length]; pose proof (gdf_frames_lt ph); lia
           | |- pf_ok _ _ _ _ => unfold pf_ok; destruct ph; cbn [PF_ctx PF_ctxinit]; apply Forall_nil
           | |- _ <= as_AL _ _ => pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 0 ltac:(lia)); lia
           | |- _ mod 2 = 0 => unfold ANX_RA_GG; rewrite unsigned_lit by lia; reflexivity
           | |- _ <= _ - GETGLOBAL_STACK _ => revert LOg STK0; unfold GETGLOBAL_STACK, FR_ossl_lib_ctx_get_ex_data_global; clear - SP1; cbn [ctxph_stack]; intros; lia
           | |- _ <= _ => lia
           | |- _ => idtac
           end.
    }
    clear GG. intros [msFg mog] PO. unfold getdefctx_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & mg & errvg & sg & LBN & x & XSg &
                    VISg & MPg & (KRELg & MIg & ACg & STg & ERRg & AUXg & HEAPg & MFg & IMg & GMg & RLg) & DELTA & ADDN & CPHg & KEYS & FXSg & RFSg & XPg & ALg).
    rewrite (unsigned_lit sp1) in STg, XPg by lia. rewrite unsigned_lit in ERRg by (unfold ATP; lia).
    unfold ANX_RA_GG in VISg. replace (ret_pc (Z_to_bv 64 0x1fd794)) with (Z_to_bv 64 0x1fd794) in VISg by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [CTXPH] in CPHg. destruct CPHg as (CSg & EXg & OIg).
    assert (SUBN : forall b, In b LB -> In b (LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof EXg as EXg'. destruct EXg' as (XIN & XSZ & XRR & XMg). destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *. subst xn. unfold MUTEX_SIZE in *.
    pose proof (ah_blocks H HH _ _ _ _ HEAPg XIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). cbn [blk_addr blk_size fst snd] in X1, X2, X3, X4, X5, X6, X7.
    unfold AIMG_TOP in X4, X5. unfold AFS_SIZE in X6.
    assert (SEP : ad + 16 <= xa \/ xa + 40 <= ad).
    { destruct ph as [|x0].
      - cbn [ctxph_delta] in DELTA. destruct DELTA as (_ & _ & BNEW & _). rewrite Hx in BNEW.
        assert (NE : blk_id (bp, bA, bN) <> blk_id (xp, xa, 40)).
        { intros E. eapply (nodup_ids_app_ne3 LBN LB); [exact (ah_nodup H HH _ _ _ HEAPg)| exact BNEW| exact BIN| symmetry; exact E]. }
        pose proof (ah_disj H HH _ _ _ _ _ HEAPg (SUBN _ BIN) XIN NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
      - cbn [ctxph_delta] in DELTA. destruct DELTA as [-> ->]. specialize (SEPR x0 eq_refl). rewrite Hx in SEPR. cbn [blk_addr fst snd] in SEPR. exact SEPR. }
    (* [comment removed for export] *)
    assert (XDhi : forall A n, aceil <= A -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (ctxph_foot ph ++ XSg)).
    { intros A n HA. apply Forall_app. split.
      - eapply Forall_impl; [| exact (ctxph_foot_rangeX ph)]. cbn beta. intros iv [K1 K2]. unfold AIMG_TOP in K2. lia.
      - apply Forall_of_dj. eapply (dj_scratch_hi H HH); [exact RFSg| exact FXSg| exact HA]. }
    assert (XDimg : forall A n, 0xc04000 <= A -> disjoint_from XSg A n -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (ctxph_foot ph ++ XSg)).
    { intros A n HA D. apply Forall_app. split.
      - eapply Forall_impl; [| exact (ctxph_foot_rangeX ph)]. cbn beta. intros iv [K1 K2]. unfold AIMG_TOP in K2. lia.
      - apply Forall_of_dj. exact D. }
    assert (T : forall A cs, rw_cells asegs m2 A cs -> aclient_range H LB sp1 A (Z.of_nat (cells_size cs)) ->
                 Forall (fun iv : Z * Z => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) (ctxph_foot ph ++ XSg) -> rw_cells asegs mg A cs)
      by (intros A cs Hc Hr HX; eapply (xpres_rw_cells' H); [exact XPg| exact Hc| exact Hr| exact HX]).
    apply T in FR2; [| left; cbn; lia| apply XDhi; lia]. apply T in LOC2; [| left; cbn; lia| apply XDhi; lia]. apply T in GAP2; [| left; lia| apply XDhi; lia].
    apply T in FF2; [| right; right; right; right; left; cbn; unfold AFS_SIZE; lia| apply XDimg; [lia| cbn; eapply (dj_scratch_live H HH); [exact RFSg| left; reflexivity| exact FXSg| lia| change (fsz 2) with 256; lia]]].
    apply T in SH2; [| right; right; right; right; right; left; cbn; exact SHIN| apply XDimg; [lia| cbn; eapply (dj_scratch_live_sh H HH); [exact RFSg| left; reflexivity| exact FXSg| subst shf; lia| change (fshn 2) with 32; subst shf; lia]]].
    apply T in FP2; [| right; right; right; right; left; cbn; unfold AFS_SIZE; lia| apply XDimg; [lia| cbn; eapply (dj_scratch_live_flag H HH); [exact RFSg| left; reflexivity| exact FXSg]]].
    (* [comment removed for export] *)
    pose proof (aapp_not_shadowland _ _ B7) as BNS. unfold ALOWSH_LO, AHI_LO in BNS.
    assert (DJad4 : disjoint_from [(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] ad 16).
    { eapply (dj_scratch_placed H HH); [exact RFS| exact FXS4| exact (ah_blocks H HH _ _ _ _ HP BIN)| cbn; exact BLO| cbn; exact BHI]. }
    assert (DJadsh4 : disjoint_from [(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] (sh bA) (nsh bN)).
    { eapply (dj_scratch_placed_sh H HH); [exact RFS| exact FXS4| exact (ah_blocks H HH _ _ _ _ HP BIN)| cbn; lia| cbn; lia]. }
    assert (AD2 : rw_cells asegs m2 ad [C8 (wz c0); C8 (wz k0)]).
    { eapply rw_cells_transport; [exact AD| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. apply dj_cons; [lia| unfold AFS_FLAGS; exact DJad4]. }
    assert (ACC2 : accessible m2 ad 16).
    { eapply accessible_transport; [exact ACC| exact MU2|]. intros q Hq. pose proof (sh_in_block bA bN q ltac:(clear - B2; Z.div_mod_to_equations; lia) ltac:(lia)) as SQ.
      pose proof (sh_aapp_range bA bN B7 ltac:(lia)) as (_ & SQ2 & SQ3). unfold AHI_LO in SQ3.
      split; [clear - SQ SQ2 SQ3 CEIL ACEILB; lia|]. eapply outside_of_dj; [exact DJadsh4| exact SQ]. }
    assert (ADg : rw_cells asegs mg ad [C8 (wz c0); C8 (wz k0)]).
    { apply T; [exact AD2| right; right; left; exists (bp, bA, bN); split; [exact BIN| cbn; lia]|].
      apply XDimg; [cbn; lia| cbn; eapply (dj_scratch_placed H HH); [exact RFSg| exact FXSg| exact (ah_blocks H HH _ _ _ _ HP BIN)| cbn; exact BLO| cbn; exact BHI]]. }
    assert (ACCg : accessible mg ad 16).
    { pose proof ACC2 as (Q0 & Q1 & QA). split; [exact Q0|]. split; [exact Q1|]. intros q Hq. destruct (QA q Hq) as (v & V1 & RD & OK).
      exists v. split; [exact V1|]. split; [| exact OK]. unfold mrd in *.
      pose proof (sh_in_block bA bN q ltac:(clear - B2; Z.div_mod_to_equations; lia) ltac:(lia)) as SQ.
      pose proof (sh_aapp_range bA bN B7 ltac:(lia)) as (SQ1 & SQ2 & SQ3). unfold AHI_LO in SQ3. assert (STOP : sh AIMG_TOP = 0x80178800) by reflexivity.
      destruct (XPg (sh q)) as [E _]; [clear - SQ SQ1 SQ2 SQ3 STOP; lia| | rewrite E; exact RD].
      split; [right; right; right; left; exists (bp, bA, bN); split; [exact BIN| cbn; lia]|].
      intros R. apply rin_ivs_app in R. destruct R as [R|R].
      - revert R. apply not_rin_of_Forall. eapply Forall_impl; [| exact (ctxph_foot_rangeX ph)]. cbn beta. intros iv [K1 K2]. unfold AIMG_TOP in K2. lia.
      - revert R. eapply not_rin_of_dj; [| exact SQ]. eapply (dj_scratch_placed_sh H HH); [exact RFSg| exact FXSg| exact (ah_blocks H HH _ _ _ _ HP BIN)| cbn; lia| cbn; lia]. }
    clear T.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KRELg| exact VISg| |].
    { eapply anx_segA2 with (lo := lo) (LB := LBN ++ LB) (xp := xp) (bA := bA) (bN := bN) (x := x); try eassumption; try reflexivity; try lia.
      all: lazymatch goal with
           | |- MUTEX _ _ _ => exact XMg
           | |- _ \/ (exists c1 k1, _) => right; exists c0, k0; exact ADg
           end.
    }
    clear VISg.
    intros msF4 mo4 KREL4 MP4 PO. unfold anx_mid2 in PO.
    destruct PO as (v0 & v1 & v2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & j0' & j1'
                    & VIS4 & MU4 & WM4 & MI4 & ST4 & AC4 & RFS4 & FR4 & LOC4 & GAP4 & FF4 & SH4 & FP4 & AD4 & CS4 & XM4).
    assert (CW4 : Forall (aclient_write_ok H (LBN ++ LB)) [(lo, bv_unsigned sp); (ad, ad + 16); (xa + 4, xa + 8)]).
    { unfold aclient_write_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - right; right; left. exists (bp, bA, bN). split; [exact (SUBN _ BIN)| cbn; lia].
      - right; right; left. exists (xp, xa, 40). split; [exact XIN| cbn; lia]. }
    assert (HP4 : as_RHEAP H sg (LBN ++ LB) m4) by (eapply (ah_RHEAP_frame H HH); [exact HEAPg| exact MU4| exact WM4| exact CW4]).
    assert (AUX4 : as_rauxv_ok H m4 B) by (eapply (ah_rauxv_frame H HH); [exact AUXg| exact MU4| exact WM4| exact CW4]).
    assert (DJimg4 : forall A n, A + n <= 12599296 -> disjoint_from [(lo, bv_unsigned sp); (ad, ad + 16); (xa + 4, xa + 8)] A n)
      by (intros A' n' K; cbn; clear - K CEIL ACEILB B4 BLO X4; repeat split; lia).
    assert (ERR4 : rw_cells asegs m4 (ATP + -164) [C4 errvg]) by (eapply errno_across; [exact ERRg| exact MU4| exact WM4| apply DJimg4; unfold ATP; lia]).
    assert (IM4 : IMPL_mem m4) by (eapply IMPL_across; [exact MU4| exact WM4| apply DJimg4; unfold A_malloc_impl; lia| exact IMg]).
    assert (GM4 : GOT_mem m4) by (eapply GOT_across; [exact MU4| exact WM4| apply DJimg4; unfold A_got_CRYPTO_malloc; lia| exact GMg]).
    assert (MF4 : MEMFLAG m4 1) by (eapply MEMFLAG_across; [exact MU4| exact WM4| apply DJimg4; unfold A_mem_inited; lia| exact MFg]).
    assert (RL4 : arelro_lib m4) by (eapply arelro_across; [exact RLg| exact MU4| repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - CEIL ACEILB B4 BLO X4; lia]).
    assert (KEYS4 : ph = CtxFresh -> CTX_keys m4).
    { intros E. pose proof (KEYS E) as (K1 & K2 & K3 & K4). unfold CTX_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_keys in *.
      repeat split; (eapply rw_cells_transport; [eassumption| exact MU4| exact WM4| apply DJimg4; cbn; lia]). }
    assert (CH0g : as_chain H m4 (bv_unsigned s0) CH).
    { eapply (achain_below H HH mg m4); [| exact CHS| exact MU4| repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; clear - B5 BHI X5 CEIL SPR LO'; lia].
      eapply chain_via_xpres; [exact CH0| exact XPg| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia|].
      intros q R. destruct (Z_lt_dec q aceil) as [Lq|Lq]; [exact Lq|]. exfalso. eapply not_rin_of_Forall; [| exact R].
      eapply Forall_impl; [| exact (XDhi q 1 ltac:(lia))]. cbn beta. intros iv K. lia. }
    assert (CH1g : as_chain H m4 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0g| lia| lia| exact SPA| lia| lia|].
      pose proof FR4 as FRl.
      lazymatch type of FRl with rw_cells _ _ _ (?c1 :: ?c2 :: ?q3 :: ?q4 :: ?q5 :: ?q6 :: ?q7 :: ?q8 :: ?q9 :: ?q10 :: ?q11 :: ?rest) =>
        change (c1 :: c2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: rest) with ([c1; c2; q3; q4; q5; q6; q7; q8; q9; q10; q11] ++ rest) in FRl end.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRl. destruct FRl as [_ FRl]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FRl.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -104 + 88) by lia.
      first [exact FRl | revert FRl; rewrite !Z_to_bv_bv_unsigned; intros FRl; exact FRl]. }
    (* [comment removed for export] *)
    pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LBN ++ LB) (s := sg) (errv := errvg) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS4| ..];
        rewrite ?unsigned_lit by lia.
      all: first [exact HP4| exact KREL4| exact AUX4| exact ST4| exact CEIL| exact ERR4| exact MI4| reflexivity| exact SP16'| exact AC4| exact CH1g| exact CHS1
                 | exact IM4| exact GM4| unfold CFREE_STACK, AFREE_STACK; lia| lia
                 | pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 0 ltac:(lia)); cbn [ctxph_cost] in ALg |- *; lia]. }
    clear CF.
    intros [msF5 mo5] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0' & w1' & w2' & d0 & d1' & d2' & d3' & d4' & d5' & d6' & d7' & w3' & w4' & w5' & w6' & m5 & sx5 &
                    VIS5 & KREL5 & MP5 & MI5 & AC5 & ST5 & ERR5 & AUX5 & XP5 & HP5 & IM5 & GM5 & AL5).
    rewrite (unsigned_lit sp1) in ST5, XP5 by lia.
    unfold ANX_RA_CF in VIS5. replace (ret_pc (Z_to_bv 64 2087464)) with (Z_to_bv 64 2087464) in VIS5 by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (T5 : forall A cs, rw_cells asegs m4 A cs -> aclient_range H (LBN ++ LB) sp1 A (Z.of_nat (cells_size cs)) -> rw_cells asegs m5 A cs)
      by (intros A cs Hc Hr; eapply (xpres_rw_cells' H); [exact XP5| exact Hc| exact Hr| apply Forall_nil]).
    apply T5 in FR4; [| left; cbn; lia]. apply T5 in LOC4; [| left; cbn; lia]. apply T5 in GAP4; [| left; lia].
    apply T5 in FF4; [| right; right; right; right; left; cbn; unfold AFS_SIZE; lia].
    apply T5 in SH4; [| right; right; right; right; right; left; cbn; exact SHIN].
    apply T5 in FP4; [| right; right; right; right; left; cbn; unfold AFS_SIZE; lia].
    apply T5 in AD4; [| right; right; left; exists (bp, bA, bN); split; [exact (SUBN _ BIN)| cbn; lia]].
    pose proof XM4 as XM4g. unfold MUTEX in XM4g.
    unfold MUTEX in XM4. apply T5 in XM4; [| right; right; left; exists (xp, xa, 40); split; [exact XIN| cbn; lia]]. clear T5.
    assert (RFS5 : as_RFS H ((2, ff, fp) :: LF) m5) by (eapply (RFS_via_xpres H HH); [exact RFS4| exact XP5| apply Forall_nil]).
    assert (CS5 : CTX_statics m5 x).
    { eapply (CTX_statics_frame []); [exact CS4|]. eapply magree_mono; [eapply (magree_lib_xpres H); exact XP5|].
      intros a Ha. eapply lib_addr_mono; [| exact Ha]. intros b Hb. destruct Hb. }
    assert (KEYS5 : ph = CtxFresh -> CTX_keys m5).
    { intros E. eapply (CTX_keys_frame []); [exact (KEYS4 E)|]. eapply magree_mono; [eapply (magree_lib_xpres H); exact XP5|].
      intros a Ha. eapply lib_addr_mono; [| exact Ha]. intros b Hb. destruct Hb. }
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_xpres0; [exact XP5| exact MF4]).
    assert (RL5 : arelro_lib m5) by (eapply arelro_xpres0; [exact RL4| exact XP5]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| |].
    { eapply (anx_segC H HHx) with (lo := lo); try eassumption; try lia.
      all: (unfold CNEWEX_READY_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
        CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
        FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; clear - LO'; lia).
    }
    clear VIS2 VIS4 VIS5 KREL1 KREL2 KRELg KREL4.
    intros msF6 mo6 KREL6 MP6 PO. unfold anx_final in PO.
    destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m6 & VIS6 & MU6 & WM6 & MI6 & ST6 & RFS6 & AC6).
    fold shf in MU6.
    assert (CW6 : Forall (aclient_write_ok H (LBN ++ LB)) [(fp, fp + 1); (ff, ff + 256); (shf, shf + 32)]).
    { unfold aclient_write_ok, AFS_SIZE in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right; right; right; right; left. lia.
      - right; right; right; right; left. lia.
      - right; right; right; right; right; left. exact SHIN. }
    assert (DJimg6 : forall A n, A + n <= 12599296 -> disjoint_from [(fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] A n)
      by (intros A' n' K; cbn; clear - K P1 R1 SHFB; repeat split; lia).
    apply (ah_done H HH). unfold cnewex_post, c3_frame. cbv beta. cbn [cfg_ms cfg_model].
    exists y0, y1, y2, e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, m6, errvg, sx5, LBN, x.
    exists (XSg ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 2); (sh ff, sh ff + fshn 2)]).
    split; [exact VIS6|].
    split; [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact MPg]| exact MP4]| exact MP5]| exact MP6]|].
    split.
    { split; [exact KREL6|]. split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
      split; [rewrite unsigned_lit by (unfold ATP; lia); eapply errno_across; [exact ERR5| exact MU6| exact WM6| apply DJimg6; unfold ATP; lia]|].
      split; [eapply (ah_rauxv_frame H HH); [exact AUX5| exact MU6| exact WM6| exact CW6]|].
      split; [eapply (ah_RHEAP_frame H HH); [exact HP5| exact MU6| exact WM6| exact CW6]|].
      split; [eapply MEMFLAG_across; [exact MU6| exact WM6| apply DJimg6; unfold A_mem_inited; lia| exact MF5]|].
      split; [eapply IMPL_across; [exact MU6| exact WM6| apply DJimg6; unfold A_malloc_impl; lia| exact IM5]|].
      split; [eapply GOT_across; [exact MU6| exact WM6| apply DJimg6; unfold A_got_CRYPTO_malloc; lia| exact GM5]|].
      eapply arelro_across; [exact RL5| exact MU6| repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - P1 R1 SHFB; lia]. }
    split; [exact DELTA|].
    change (fsz 2) with 256. change (fshn 2) with 32. fold shf.
    (* [comment removed for export] *)
    assert (ADDRT : forall b, In b (LBN ++ LB) -> addressable mg (blk_addr b) (blk_size b) -> addressable m6 (blk_addr b) (blk_size b)).
    { intros b Hb AB. pose proof (ah_blocks H HH _ _ _ _ HEAPg Hb) as BRb. pose proof BRb as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      pose proof (sh_aapp_range _ _ Q7 Q3) as (S1 & S2 & S3). assert (STOP : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite STOP in S1.
      unfold AHI_LO in S3. pose proof (aapp_not_shadowland _ _ X7) as XNS. unfold ALOWSH_LO, AHI_LO in XNS.
      assert (AB4 : addressable m4 (blk_addr b) (blk_size b)).
      { eapply addressable_transport; [exact AB| exact MU4| exact WM4|]. cbn.
        repeat split; clear - S1 S2 S3 XNS BNS BLO BHI CEIL ACEILB; lia. }
      assert (AB5 : addressable m5 (blk_addr b) (blk_size b)).
      { eapply (ashobj_addressable_xpres H HH) with (LB := LBN ++ LB) (LB2 := LBN ++ LB) (SP := sp1) (X := []);
          [exact HP4| intros b' Hb'; exact Hb'| lia| left; exists b; split; [exact Hb| lia]| unfold AAPP_HI; clear - Q5 ACEILB; lia| exact AB4| exact XP5| apply Forall_nil]. }
      eapply addressable_transport; [exact AB5| exact MU6| exact WM6|].
      eapply (dj_scratch_placed_sh H HH); [exact RFS| exact (Forall_inv_tail FXS4)| exact BRb| lia| lia]. }
    split. { apply Forall_forall. intros b Hb. apply ADDRT; [apply in_or_app; left; exact Hb| exact (proj1 (Forall_forall _ _) ADDN b Hb)]. }
    split.
    { cbn [CTXPH]. split.
      - eapply CTX_statics_across; [exact CS5| exact MU6| exact WM6|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - P1 R1 F1 SHFB; lia.
      - split; [| exact OIg]. rewrite Hx. unfold EXLOCK. cbn [blk_addr blk_size fst snd]. unfold MUTEX_SIZE.
        split; [exact XIN|]. split; [reflexivity|]. split; [exact XRR|]. unfold MUTEX.
        eapply rw_cells_transport; [exact XM4| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add].
        eapply (dj_scratch_placed H HH); [exact RFS| exact (Forall_inv_tail FXS4)| exact (ah_blocks H HH _ _ _ _ HEAPg XIN)| cbn; lia| cbn; lia]. }
    split.
    { intros E. pose proof (KEYS5 E) as (K1 & K2 & K3 & K4). unfold CTX_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_keys in *.
      repeat split; (eapply rw_cells_transport; [eassumption| exact MU6| exact WM6| apply DJimg6; cbn; lia]). }
    split. { eapply rw_cells_transport; [exact AD4| exact MU6| exact WM6| exact (proj2 DJad4)]. }
    split. { apply Forall_app. split; [exact (fs_scratch_mono_Forall H _ _ _ FXSg)| exact FXS4]. }
    split; [exact RFS6|].
    split.
    { set (XF := (ad, ad + 16) :: ctxph_foot ph ++ XSg ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)]).
      assert (XPa : xpres H LB (bv_unsigned sp) XF m m2).
      { eapply (xpres_X_mono H); [exact XP2|]. intros q R. subst XF. destruct R as [R|R]; [left; exact R| right].
        apply rin_ivs_app in R. apply rin_ivs_app. destruct R as [R|R]; [left; exact R| right]. apply rin_ivs_app. right. exact R. }
      assert (XPb : xpres H LB (bv_unsigned sp) XF m2 mg).
      { eapply (xpres_weaken H); [exact XPg| lia| intros b' Hb'; exact Hb'|]. intros q R. subst XF. right.
        apply rin_ivs_app in R. apply rin_ivs_app. destruct R as [R|R]; [left; exact R| right]. apply rin_ivs_app. left. exact R. }
      assert (XPc' : xpres H (LBN ++ LB) (bv_unsigned sp) (XF ++ [(xa + 4, xa + 8)]) mg m4).
      { eapply (xpres_of_munch H sg (LBN ++ LB) _ _ _ mg mg m4); [exact HH| exact HEAPg| exact MU4| exact WM4|]. subst XF.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        - left. lia.
        - right. intros q Hq. cbn. left. exact Hq.
        - right. intros q Hq. apply rin_ivs_app. right. cbn. left. exact Hq. }
      assert (XPc : xpres H LB (bv_unsigned sp) XF mg m4).
      { intros q Hq [HC HX].
        destruct (Z.le_gt_cases (xa + 4) q) as [L1|L1]; [destruct (Z.lt_ge_cases q (xa + 8)) as [L2|L2]|].
        1: { split; [| intros Hw; apply WM4; exact Hw].
             eapply (rw_cells_same_raw mg m4); [exact XMg| exact XM4g| lia| cbn [cells_size csize Nat.add length Pos.to_nat]; lia]. }
        all: apply XPc'; [exact Hq| split; [eapply aclient_addr_weaken; [exact HC| lia| intros b' Hb'; apply in_or_app; right; exact Hb']|]];
             intros R; apply rin_ivs_app in R; destruct R as [R|R]; [exact (HX R)| cbn in R; lia]. }
      assert (XPd : xpres H LB (bv_unsigned sp) XF m4 m5).
      { eapply (xpres_weaken H); [exact XP5| lia| intros b' Hb'; apply in_or_app; right; exact Hb'| intros q R; destruct R]. }
      assert (XPe : xpres H LB (bv_unsigned sp) XF m5 m6).
      { eapply (xpres_of_munch H s LB _ _ _ m m5 m6); [exact HH| exact HP| exact MU6| exact WM6|]. subst XF.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; right; intros q Hq; cbn; right; apply rin_ivs_app; right; apply rin_ivs_app; right; cbn; lia. }
      eapply (xpres_trans H); [exact XPa|]. eapply (xpres_trans H); [exact XPb|]. eapply (xpres_trans H); [exact XPc|]. eapply (xpres_trans H); [exact XPd| exact XPe]. }
    cbn [ctxph_cost] in ALg |- *. clear - ALg AL5. lia.
  Qed.
End S.
