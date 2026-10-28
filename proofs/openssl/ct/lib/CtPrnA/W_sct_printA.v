(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG CtSizes CtWire CtTime CtModel BnBase BnModel BnTree ApBase ApState ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA UnwindX EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2 W_bio_vprintfG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA W_crypto_reallocA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_prefix_create W_strdup W_obj_free W_asn1_stringA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_time_leavesA W_snprintfA W_time_from_tmA W_gentime_adjA W_time_to_tm_frontA W_gentime_set_stringA W_time_printA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnFmtA W_bio_hex_stringA PrnSctFmtA Fr_SCT_print PrnSctKitA PrnStmtA PrnSctTsA PrnSctTailA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma uw_chain_rebase : forall (m m' : mem) f fp r ras (v8 vra : word),
  uw_chain USTACK_TOP m f fp (r :: ras) ->
  rw_cells ctasegs m (fp + -16) [C8 v8; C8 vra] -> rw_cells ctasegs m' (fp + -16) [C8 v8; C8 vra] ->
  agree_on (fun a => fp <= a < USTACK_TOP) m m' -> uw_chain USTACK_TOP m' f fp (r :: ras).
Proof.
  intros m m' f fp r ras v8 vra UW R1 R2 AG. cbn [uw_chain] in UW |- *. destruct UW as (H1 & H2 & H3 & fp' & R & RC & CH).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact R|]. split.
  - pose proof (rw_cells_bytes_at _ _ _ _ RC) as B1. pose proof (rw_cells_bytes_at _ _ _ _ R1) as B2.
    assert (E : cells_bytes [C8 (Z_to_bv 64 fp'); C8 (Z_to_bv 64 r)] = cells_bytes [C8 v8; C8 vra]).
    { apply (bytes_at_detP m (fp + -16)); [exact B1| exact B2|]. rewrite !cells_bytes_length; [reflexivity| exact (proj1 (proj1 R1))| exact (proj1 (proj1 RC))]. }
    destruct R2 as [[WF B] W]. split; [split; [exact (proj1 (proj1 RC))| rewrite E; exact B]| exact W].
  - eapply uw_chain_agree; [exact CH| exact AG].
Qed.

Section OffBlock.
Context {AR : ARun}.
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
(* [comment removed for export] *)
Lemma aclient_addr_mono : forall (L L' : list block) SP a, (forall b, In b L -> In b L') -> aclient_addr L SP a -> aclient_addr L' SP a.
Proof.
  intros L L' SP a HL [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha| right; left; exact Ha| right; right; exists b; split; [exact (HL b Hb)| exact Hr]].
Qed.

(* [comment removed for export] *)
Lemma aclient_off_blockA : forall Σ OWX LBX m SP L (b : block) a,
  AHEAP Σ OWX LBX m -> In b (OWX ++ LBX) -> ACEIL <= SP ->
  (forall b', In b' L -> In b' (OWX ++ LBX) /\ blk_id b' <> blk_id b) ->
  aclient_addr L SP a -> ~ (blk_addr b <= a < blk_addr b + blk_size b).
Proof.
  intros Σ OWX LBX m SP L b a HEAP Hb CE HL Ha.
  pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (B0 & _ & _ & BC & BI).
  destruct Ha as [Ha|[Ha|(b' & Hb' & Hr)]].
  - clear - Ha BC CE. unfold BnHeapA.ACEIL in *. lia.
  - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr BI; lia.
  - destruct (HL b' Hb') as [Hin NE]. pose proof (AH_disjoint_gen _ _ _ _ b' b HEAP Hin Hb NE) as DJ. clear - DJ Hr. lia.
Qed.

End OffBlock.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.

(* [comment removed for export] *)
Definition sct_print_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RTS) (OW LB : list block) (lo out pv : Z) (m : mem) (cost : Z) (Σ' : rts RTS) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' nw',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ AHEAP Σ' OW LB m' /\ rt_credit RTS Σ - cost <= rt_credit RTS Σ'
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ mem_inv ctasegs m'
    /\ apres_ex LB OW (bv_unsigned sp) [(out, out + 128)]%Z m m'
    /\ 0 <= nw' < 2^64 /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv nw').

(* [comment removed for export] *)
Lemma SCT_print_nv1A : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (pb : bptr) (out pv nw : Z) (adr : bptr -> Z) (x : sctr bptr) (st : ap_st bptr)
    (Q : unit * ap_st bptr -> rts RTS -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + SCT_PRINT_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (S (S (length FRM)))) < FRAMES_MAX)%nat -> sct_print_costA x <= rt_credit RTS Σ ->
  sct_repA m (OW ++ LB) adr x -> sc_version x <> 0 ->
  In (pb, out, BIO_SIZE) OW -> ~ In pb (map blk_id (sct_blocks adr x)) ->
  rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
  (forall Σ' ms', sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms' -> Q (tt, st) Σ' ms') ->
  implAp (sct_print x st) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_PRINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED REP NV HBIN NPB HB NW -> -> -> -> KQ.
  unfold sct_print. rewrite (proj2 (Z.eqb_neq (sc_version x) 0) NV). unfold aret.
  pose proof LO as LO'. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (OB0 & _ & _ & OBC & _). cbn [blk_addr blk_size fst snd] in OB0, OBC. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu.
  assert (CX : 0 <= HX_CRED (prn_item_wt x)).
  { unfold HX_CRED, prn_item_wt. rewrite (proj2 (Z.eqb_neq (sc_version x) 0) NV). unfold sc_bloblen.
    pose proof REP as (_ & _ & _ & _ & _ & _ & A4 & _). destruct (sc_blob x) as [[q n]|]; [destruct A4 as (N0 & _); clear - N0; lia| clear; lia]. }
  eapply (implAp_step (ARet (tt, st)) Σ Q _ (fun Σ' ms' => sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms'));
    [| intros Σ' ms' PO; apply implAp_ret; exact (KQ Σ' ms' PO)].
  (* [comment removed for export] *)
  change (wz SCT_PRINT_A) with (wz SCTP_ENTRY).
  eapply (sctp_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold SCTP_FRAME, RT_STACK; clear - LO'; lia| exact TOP| exact AL16| exact MI| reflexivity| clear - FLEN; lia
    | unfold sct_print_costA, SCT_PRINT_BASE_A in CRED; clear - CRED CX; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 jf24 jf32 jf52 jst
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold SCTP_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (adr (sc_blk x)))) 7)) with (Z_to_bv 64 0).
  2:{ pose proof REP as (HSINz & AL16z & _). pose proof (AH_range_gen _ _ _ _ _ HEAP HSINz) as (BSz0 & _ & _ & BSzC & _). cbn [blk_addr blk_size fst snd] in BSz0, BSzC. unfold BnHeapA.ACEIL in BSzC.
      f_equal. rewrite unsigned_lit by (clear - BSz0 BSzC Cq3; unfold BnHeapA.ACEIL, SCT_SIZE in *; cbn [ar_SP0 push amb] in *; lia). change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2 ^ 3) with 8.
      revert AL16z. uchk_open. clear. intros AL16z. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (AG3 : agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(out, out + 128)]%Z a) m m3)
    by (eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha).
  assert (REP3 : sct_repA m3 (OW ++ LB) adr x).
  { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AGF|]. intros a Ha.
    destruct (sct_addr_block _ _ _ _ _ REP Ha) as (b & _ & HL & Hr). right; right. exists b. split; [exact HL| exact Hr]. }
  apply (rw_cells_agree _ _ _ _ _ AGF) in HB; [| intros xa Hxa; unfold bio_null_cells, bio_cells in Hxa; cbn in Hxa; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Hxa; lia]].
  (* [comment removed for export] *)
  pose proof (@sc_seg0 (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as S0.
  cbn [ar_RT ar_PMc ar_FR push amb] in S0.
  eapply S0 with (nw := nw) (c24 := CB 8 j24) (lv := rt_live RTS Σ) (budget := sct_print_costA x - 1); clear S0;
    first [exact HEAP3| exact CEIL| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact HBIN| exact REP3| exact NPB| idtac].
  - unfold SC_BODY_STACK_A, RT_STACK. clear - LO' SPAL. lia.
  - cbn [ar_FR push amb length]. clear - FLEN. lia.
  - (* [comment removed for export] *)
    split; [exact HEAP3|]. split; [exact LIVE1|]. split; [exact MI3|]. split; [exact ST3|]. split; [intros a _; reflexivity|].
    split; [exact LOW|]. split; [reflexivity|]. split; [exact HIGH|]. split; [exact REP3| intros b Hb; exact Hb].
  - split; [exact NW| exact HB].
  - clear; lia.
  - unfold sct_print_costA, SCT_PRINT_BASE_A. clear - CX; lia.
  - rewrite CR1. clear - CRED; lia.
  - (* [comment removed for export] *) intros. exfalso. exact (NV ltac:(assumption)).
  - (* [comment removed for export] *)
    intros x1' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Fc' fc' m4 Σ4 nw4 _ INV4 BIO4 CR4.
    pose proof (@sc_nv1 (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as S1.
    cbn [ar_RT ar_PMc ar_FR push amb] in S1.
    eapply S1 with (used := 6) (budget := sct_print_costA x - 1); clear S1;
      first [exact HEAP3| exact CEIL| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact HBIN| exact REP3| exact NPB| exact NV| exact INV4| exact BIO4| exact CR4| idtac].
    + unfold SC_BODY_STACK_A, RT_STACK. clear - LO' SPAL. lia.
    + cbn [ar_FR push amb length]. clear - FLEN. lia.
    + clear; lia.
    + unfold sct_print_costA, SCT_PRINT_BASE_A, prn_item_wt. rewrite (proj2 (Z.eqb_neq (sc_version x) 0) NV). clear; lia.
    + rewrite CR1. clear - CRED; lia.
    + (* [comment removed for export] *)
    unfold at_exit. intros x1e v0 v1 v2 e0 e1 e2 e3 e4 e5 e6 e7 x19e x20e x21e x22e x23e x24e x27e v3 v4 v5 v6 Fce fce m5 Σ5 nw5 INV5 BIO5 CR5.
    destruct INV5 as (HEAP5 & LIVE5 & MI5 & ST5 & AGR5 & FRL5 & _ & FRH5 & REP5 & _). destruct BIO5 as [NW5 HB5].
    unfold sc_lo in FRL5. cbn [ar_RT ar_PMc push amb] in CR5, LIVE5 |- *.
    eapply (sctp_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST5| exact CEIL| clear - LO' SPAL; lia
      | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI5| exact FRL5| exact FRH5| reflexivity|].
    intros Σ6 m6 x10' HEAP6 CR6 LIVE6 ST6 MI6 AG6.
    apply cps_post. intros c Hc. exists Σ6. split; [| rewrite LIVE6; exact LIVE5].
    eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold sct_print_postA, MallocRep.wz.
    do 15 eexists. exists Fce, fce, m6, nw5. split; [reflexivity|].
    split; [exact HEAP6|]. split; [rewrite CR6; clear - CR5 CR1; lia|].
    split; [exact ST6|]. split; [exact MI6|].
    split.
    { unfold apres_ex. eapply agree_on_trans; [exact AG3|]. eapply agree_on_trans; [exact AGR5|].
      eapply agree_on_mono; [exact AG6|]. intros a [Ha _]. destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Ha]. }
    split; [exact NW5|].
    eapply rw_cells_agree; [exact AG6| exact HB5|]. intros a Ha. unfold bio_null_cells, bio_cells in Ha. cbn in Ha. right; right. exists (pb, out, 128). split; [exact HBIN'| cbn; clear - Ha; lia].
Qed.
Ltac kit_hyps := first [assumption | eassumption | idtac].

Section V1.
Hypothesis REA : realloc_contract_gen RTS.

(* [comment removed for export] *)
Lemma SCT_print_v1okA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (pb : bptr) (out pv nw : Z) (adr : bptr -> Z) (x : sctr bptr) (st : ap_st bptr) (t : tm6) (ras : list Z)
    (Q : unit * ap_st bptr -> rts RTS -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + SCT_PRINT_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (S (S (length FRM)))) < FRAMES_MAX)%nat -> sct_print_costA x <= rt_credit RTS Σ ->
  crypto_statics m -> realloc_statics m ->
  sct_repA m (OW ++ LB) adr x -> sc_version x = 0 -> gentime_adj (sc_ts x) = Some t ->
  In (pb, out, BIO_SIZE) OW -> ~ In pb (map blk_id (sct_blocks adr x)) ->
  rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_PRINT_A (bv_unsigned ra :: ras) ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
  (forall Σ' ms', sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms' -> Q (tt, st) Σ' ms') ->
  implAp (sct_print x st) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_PRINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED CS RS REP V0 GA HBIN NPB HB NW UW CTX -> -> -> -> KQ.
  unfold sct_print. rewrite V0, Z.eqb_refl. unfold timestamp_print.
  assert (PR : printable (sc_ts x) = true) by (unfold printable; rewrite GA; reflexivity). rewrite PR.
  pose proof LO as LO'. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (OB0 & _ & _ & OBC & _). cbn [blk_addr blk_size fst snd] in OB0, OBC. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu.
  assert (CX : HX_CRED (prn_item_wt x) = HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) + HX_CRED (sc_extlen x) + HX_CRED (sc_siglen x)).
  { unfold prn_item_wt, HX_CRED. rewrite V0, Z.eqb_refl. clear; lia. }
  assert (HX0 : 0 <= HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) /\ 0 <= HX_CRED (sc_extlen x) /\ 0 <= HX_CRED (sc_siglen x)).
  { pose proof REP as (_ & _ & _ & _ & A2 & A3 & _ & _ & _ & _ & _ & _ & _ & EXL & _). unfold HX_CRED, CtSctP.SctRep.logid_len, CT_V1_HASHLEN, sc_siglen. rewrite EXL. unfold CtSctP.SctRep.olen.
    repeat split; [destruct (sc_logid x); clear; lia| destruct (sc_ext x) as [[q n]|]; [destruct A2 as (N0 & _); clear - N0; lia| clear; lia]| destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0; lia| clear; lia]]. }
  destruct HX0 as (HXL & HXE & HXS).
  intros XX Φ Dl SAFE LINK.
  (* [comment removed for export] *)
  change (wz SCT_PRINT_A) with (wz SCTP_ENTRY).
  eapply (sctp_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold SCTP_FRAME, RT_STACK; clear - LO'; lia| exact TOP| exact AL16| exact MI| reflexivity| clear - FLEN; lia
    | unfold sct_print_costA, SCT_PRINT_BASE_A in CRED; clear - CRED CX HXL HXE HXS; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 jf24 jf32 jf52 jst
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold SCTP_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (adr (sc_blk x)))) 7)) with (Z_to_bv 64 0).
  2:{ pose proof REP as (HSINz & AL16z & _). pose proof (AH_range_gen _ _ _ _ _ HEAP HSINz) as (BSz0 & _ & _ & BSzC & _). cbn [blk_addr blk_size fst snd] in BSz0, BSzC. unfold BnHeapA.ACEIL in BSzC.
      f_equal. rewrite unsigned_lit by (clear - BSz0 BSzC Cq3; unfold BnHeapA.ACEIL, SCT_SIZE in *; cbn [ar_SP0 push amb] in *; lia). change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2 ^ 3) with 8.
      revert AL16z. uchk_open. clear. intros AL16z. Z.div_mod_to_equations. lia. }
  assert (AG3 : agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(out, out + 128)]%Z a) m m3)
    by (eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha).
  assert (REP3 : sct_repA m3 (OW ++ LB) adr x).
  { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AGF|]. intros a Ha.
    destruct (sct_addr_block _ _ _ _ _ REP Ha) as (b & _ & HL & Hr). right; right. exists b. split; [exact HL| exact Hr]. }
  assert (CS3 : crypto_statics m3) by (exact (crypto_statics_agree _ m m3 AGF (fun a Ha => or_intror (or_introl (ar_LIBW_cs a Ha))) CS)).
  assert (RS3 : realloc_statics m3).
  { unfold realloc_statics in *. eapply ro_cells_agree; [exact AGF| exact RS|]. intros a Ha. cbn in Ha. unfold CR_REALLOC_IMPL in Ha. right; left. apply ar_LIBW_cs. unfold LIBW_A. cbn [rin_ivs fst snd]. clear - Ha. lia. }
  apply (rw_cells_agree _ _ _ _ _ AGF) in HB; [| intros xa Hxa; unfold bio_null_cells, bio_cells in Hxa; cbn in Hxa; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Hxa; lia]].
  assert (UW3 : uw_chain USTACK_TOP m3 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { eapply (uw_call m m3 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
      [exact UW| eapply agree_on_mono; [exact AGF| intros a Ha; left; exact Ha]| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia
      | clear - TOPu; unfold USTACK_TOP; lia| apply bv_unsigned_in_range| rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact HIGH]. }
  set (budget := sct_print_costA x - 1).
  assert (BUD : budget <= rt_credit RTS Σ1) by (subst budget; rewrite CR1; clear - CRED; lia).
  assert (BUDE : budget = 47 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) + HX_CRED (sc_extlen x) + HX_CRED (sc_siglen x)) by (subst budget; unfold sct_print_costA, SCT_PRINT_BASE_A; rewrite CX; clear; lia).
  assert (INV3 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [] LB (CB 8 j24) (rt_live RTS Σ) Σ1 m3).
  { split; [exact HEAP3|]. split; [exact LIVE1|]. split; [exact MI3|]. split; [exact ST3|]. split; [intros a _; reflexivity|].
    split; [exact LOW|]. split; [reflexivity|]. split; [exact HIGH|]. split; [exact REP3| intros b Hb; exact Hb]. }
  assert (BIO3 : sc_bio out pv m3 nw) by (split; [exact NW| exact HB]).
  (* [comment removed for export] *)
  assert (LOB : lo + SC_BODY_STACK_A <= spa) by (unfold SC_BODY_STACK_A, RT_STACK; clear - LO' SPAL; lia).
  assert (FLENB : (S (S (S (length ((f, 1%nat) :: FRM)))) < FRAMES_MAX)%nat) by (cbn [length]; clear - FLEN; lia).
  assert (HFR : In (f, 1%nat) ((f, 1%nat) :: FRM)) by (left; reflexivity).
  pose proof (@sc_seg0 (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as S0. cbn [ar_RT ar_PMc ar_FR push amb] in S0.
  assert (CRc : rt_credit RTS Σ1 <= rt_credit RTS Σ1) by (clear; lia).
  eapply S0 with (nw := nw) (c24 := CB 8 j24) (lv := rt_live RTS Σ) (budget := budget); clear S0; kit_hyps; try (clear - BUDE HXL HXE HXS BUD CRc; lia);
    [| intros; exfalso; match goal with H : sc_version x <> 0 |- _ => exact (H V0) end].
  clear CRc INV3 BIO3. intros x1a u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Fca fca m4 Σ4 nw4 _ INV4 BIO4 CRc.
  pose proof (@sc_v1a (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as S1. cbn [ar_RT ar_PMc ar_FR push amb] in S1.
  eapply S1 with (used := 6) (budget := budget) (j24 := j24); clear S1; kit_hyps; try (clear - BUDE HXL HXE HXS BUD CRc; lia).
  clear dependent m4. clear dependent Σ4. try clear CRc. try clear nw4.
  intros v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 Fcb fcb m4 Σ4 nw4 INV4 BIO4 CR4.
  (* [comment removed for export] *)
  pose proof INV4 as (HEAP4 & LIVE4 & MI4 & ST4 & AGR4 & FRL4 & SZ4 & FRH4 & REP4 & LBI4).
  assert (UW4 : uw_chain USTACK_TOP m4 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { eapply (uw_chain_rebase m3 m4); [exact UW3| exact HIGH| exact FRH4|]. eapply agree_on_mono; [exact AGR4|]. intros a Ha.
    split; [left; exact Ha| cbn [outside fst snd]; split; [clear - Ha OBCu CEILu LO' SPAL SPAH; lia| exact I]]. }
  eapply (implAp_elim _ Σ Σ4 Q _ XX Φ Dl); [| exact SAFE| exact LINK| exact LIVE4].
  unfold abind. cbn [apbind amalloc].
  pose proof (@sc_gtnew (push AR f 1) UK BE sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as SG. cbn [ar_RT ar_PMc ar_FR push amb] in SG.
  eapply SG with (nw := nw4) (lv := rt_live RTS Σ) (c24 := C8 (Z_to_bv 64 f)); clear SG; kit_hyps.
  clear HEAP4 LIVE4 MI4 ST4 AGR4 FRL4 SZ4 FRH4 REP4 LBI4.
  intros pg Σ5 ms5 Hpg PO. cbn [apbind fst snd].
  destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F5 & fc5 & m5 & G & -> & MI5 & ST5 & AG5 & CR5 & GR & HEAP5 & ACC5 & GC5).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0 SPAL SPAH; lia).
  rewrite ESPA in ST5, AG5. rewrite (ret_pc_even 0x337fc8) by (clear; lia). unfold MallocRep.wz.
  assert (INV5 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [(pg, G, 24)] LB (C8 (Z_to_bv 64 f)) (rt_live RTS Σ5) Σ5 m5).
  { pose proof (@sc_inv_xfer (push AR f 1) sp spa f lo g OW LB pb out adr x m3 Σ1 ra s0 j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
    eapply L; clear L; first [exact INV4| exact HEAP5| kit_hyps]. }
  assert (BIO5 : sc_bio out pv m5 nw4) by (exact (sc_bio_xfer spa OW LB pb out pv HBIN m4 m5 nw4 BIO4 AG5)).
  assert (UW5 : uw_chain USTACK_TOP m5 spa (bv_unsigned sp) (bv_unsigned ra :: ras)) by (exact (sc_uw_xfer sp spa OW LB SPAH m4 m5 _ UW4 AG5)).
  assert (GRu : 0 < G < 2 ^ 64) by (destruct GR as (GR0 & _ & _ & GRC & _); change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in GRC; clear - GR0 GRC Cq3; lia).
  clear MI5 ST5 AG5 ACC5 INV4 BIO4 UW4. clear dependent m4.
  (* [comment removed for export] *)
  intros X1 Φ1 D1 S1 L1.
  pose proof (@sc_ts1 (push AR f 1) sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4); clear L; first [exact INV5| exact BIO5| exact GRu| kit_hyps].
  intros w0' w1' w2' d4' d5' d6' d7' w3' w4' w5' w6' m6 INV6 BIO6 SH6 AG6.
  (* [comment removed for export] *)
  pose proof INV6 as (HEAP6 & LIVE6 & MI6 & ST6 & AGR6 & FRL6 & SZ6 & FRH6 & REP6 & LBI6).
  destruct (bptr_fresh (map blk_id (((pg, G, 24) :: OW) ++ LB))) as [q Hq].
  assert (OFFL : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
  pose proof (@sc_genstr_open (push AR f 1) f GEO HFR Σ5 ((pg, G, 24) :: OW) LB m6 q HEAP6 OFFL SH6 Hq) as HEAP6o.
  assert (INV6o : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [(pg, G, 24)] ((q, f + 32, 20) :: LB) (C8 (Z_to_bv 64 f)) (rt_live RTS Σ5) Σ5 m6).
  { split; [exact HEAP6o|]. split; [exact LIVE6|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact AGR6|]. split; [exact FRL6|]. split; [exact SZ6|]. split; [exact FRH6|].
    split; [exact REP6| intros b Hb; right; exact Hb]. }
  pose proof GEO as (Ge1 & Ge2 & Ge3 & Ge4 & Ge5). change (fs_size 1) with 128 in Ge3, Ge5. unfold BnHeapA.ACEIL in Ge3. unfold SEGTOP_A in Ge4.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. clear - Ge1 Ge3 Ge4 Cq3. unfold BnHeapA.ACEIL in *. Z.div_mod_to_equations. lia. }
  pose proof (AH_offsh _ _ _ _ (pg, G, 24) HEAP5 (or_introl eq_refl)) as OFSG. cbn [blk_addr blk_size fst snd] in OFSG. unfold SHLO, SHHI in OFSG.
  assert (GC6 : rw_cells ctasegs m6 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0)).
  { eapply rw_cells_agree; [exact AG6| exact GC5|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha. cbv beta. clear - Ha OFSG SHR. lia. }
  assert (UW6 : uw_chain USTACK_TOP m6 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { eapply uw_chain_agree; [exact UW5|]. eapply agree_on_mono; [exact AG6|]. intros a Ha. cbv beta. clear - Ha SHR Cq2 CEILu LOB. unfold BnHeapA.ACEIL, SC_BODY_STACK_A, RT_STACK in *. lia. }
  clear HEAP6 LIVE6 MI6 ST6 AGR6 FRL6 SZ6 FRH6 REP6 LBI6 HEAP6o SH6 AG6 INV6 GC5 HEAP5 UW5 INV5 BIO5. clear dependent m5.
  (* [comment removed for export] *)
  eapply (implAp_elim _ Σ5 Σ5 Q _ X1 Φ1 D1); [| exact S1| exact L1| reflexivity].
  pose proof (@sc_ts2ok (push AR f 1) UK BE PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  change (mcost 24) with 0 in CR5. cbn [ar_RT push amb] in CR5.
  eapply L with (nw := nw4) (t := t) (LBc := (q, f + 32, 20) :: LB); clear L; first [exact INV6o| exact BIO6| exact GC6| exact UW6| exact GA| kit_hyps];
    [clear - CR4 CR5 BUD BUDE HXE HXS; lia|].
  intros pd Σ7 ms7 Hpd PO. cbn [apbind areallocI fst snd].
  clear w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F5 fc5. try clear x1a u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Fca fca v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 Fcb fcb.
  destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F7 & fc7 & m7 & D & junk4 & -> & MI7 & ST7 & AB7 & CR7 & DR & HEAP7 & GC7 & DC7 & J4).
  rewrite ESPA in ST7, AB7. rewrite (ret_pc_even 0x338028) by (clear; lia). unfold MallocRep.wz. change (2 + mcost 20) with 2 in CR7. cbn [ar_RT push amb] in CR7.
  assert (INCL7 : forall b, In b (OW ++ LB) -> In b (((pg, G, 24) :: OW) ++ (q, f + 32, 20) :: LB)).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; right; exact Hb]. }
  assert (AG7 : agree_on (aclient_addr (OW ++ LB) spa) m6 m7).
  { unfold apres_but, ASN1_STRING_SIZE in AB7. eapply agree_on_mono; [exact AB7|]. intros a Ha. cbv beta. split; [exact (aclient_addr_mono _ _ _ _ INCL7 Ha)|].
    apply (@aclient_off_blockA (push AR f 1) Σ5 ((pg, G, 24) :: OW) ((q, f + 32, 20) :: LB) m6 spa (OW ++ LB) (pg, G, 24) a (proj1 INV6o));
      [left; reflexivity| clear - CEILu LOB; unfold BnHeapA.ACEIL, SC_BODY_STACK_A, RT_STACK in *; cbn [ar_SP0 push amb] in *; lia| | exact Ha].
    intros b' Hb'. split; [exact (INCL7 b' Hb')|]. cbn [blk_id fst]. intros E. apply Hpg. rewrite <- E. apply in_map. exact Hb'. }
  assert (INV7 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [(pd, D, 20); (pg, G, 24)] ((q, f + 32, 20) :: LB) (C8 (Z_to_bv 64 f)) (rt_live RTS Σ7) Σ7 m7).
  { pose proof (@sc_inv_xfer (push AR f 1) sp spa f lo g OW LB pb out adr x m3 Σ1 ra s0 j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
    eapply L; clear L; first [exact INV6o| exact HEAP7| exact AG7| kit_hyps]. }
  assert (BIO7 : sc_bio out pv m7 nw4) by (exact (sc_bio_xfer spa OW LB pb out pv HBIN m6 m7 nw4 BIO6 AG7)).
  assert (UW7 : uw_chain USTACK_TOP m7 spa (bv_unsigned sp) (bv_unsigned ra :: ras)) by (exact (sc_uw_xfer sp spa OW LB SPAH m6 m7 _ UW6 AG7)).
  assert (HpdO : ~ In pd (map blk_id ((pg, G, 24) :: OW))) by (intros Hi; apply Hpd; rewrite map_app; apply in_or_app; left; exact Hi).
  assert (NEgd : pg <> pd) by (intros E; apply Hpd; cbn [map app blk_id fst]; left; exact E).
  clear MI7 ST7 AB7 INV6o BIO6 UW6 GC6 HEAP7. clear dependent m6.
  (* [comment removed for export] *)
  intros X2 Φ2 D2 S2 L2.
  pose proof (@sc_ts3ok (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4) (t := t); clear L; first [exact INV7| exact BIO7| exact GRu| exact GA| exact GC7| exact DC7| exact J4| exact UW7| kit_hyps].
  clear w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F7 fc7.
  intros w0 w1 w2 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F8 fc8 m8 INV8 BIO8 GC8 DC8 GS8 UW8.
  (* [comment removed for export] *)
  eapply (implAp_elim _ Σ7 Σ7 Q _ X2 Φ2 D2); [| exact S2| exact L2| reflexivity].
  pose proof (@sc_ts4ok (push AR f 1) UK BE sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4) (t := t) (junk4 := junk4); clear L; first [exact INV8| exact BIO8| exact GA| exact NEgd| exact GC8| exact DC8| exact GS8| exact UW8| kit_hyps];
    [clear - CR4 CR5 CR7 BUD BUDE HXE HXS; lia|].
  clear INV7 BIO7 UW7 GC7 DC7. clear dependent m7.
  intros pd' Σ9 ms9 Hpd' PO. cbn [apbind afree fst snd].
  clear w0 w1 w2 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F8 fc8.
  destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F9 & fc9 & m9 & D' & -> & MI9 & ST9 & AB9 & CR9 & DR' & HEAP9 & GC9 & DC9).
  rewrite ESPA in ST9, AB9. rewrite (ret_pc_even 0x33807c) by (clear; lia). unfold MallocRep.wz, afree. cbn [ar_RT push amb] in CR9. change (mcost 19) with 0 in CR9.
  rewrite lb_remove_cons in AB9, HEAP9. cbn [blk_id fst] in AB9, HEAP9. rewrite bptr_eqb_refl in AB9, HEAP9. rewrite (lb_remove_notin pd _ HpdO) in AB9, HEAP9.
  assert (INCL9 : forall b, In b (OW ++ LB) -> In b (((pd, D, 20) :: (pg, G, 24) :: OW) ++ (q, f + 32, 20) :: LB)).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; right; exact Hb| right; right; exact Hb]. }
  assert (AG9 : agree_on (aclient_addr (OW ++ LB) spa) m8 m9).
  { unfold apres_but, ASN1_STRING_SIZE in AB9. eapply agree_on_mono; [exact AB9|]. intros a Ha. cbv beta. split; [exact (aclient_addr_mono _ _ _ _ INCL7 Ha)|].
    apply (@aclient_off_blockA (push AR f 1) Σ7 ((pd, D, 20) :: (pg, G, 24) :: OW) ((q, f + 32, 20) :: LB) m8 spa (OW ++ LB) (pg, G, 24) a (proj1 INV8));
      [right; left; reflexivity| clear - CEILu LOB; unfold BnHeapA.ACEIL, SC_BODY_STACK_A, RT_STACK in *; cbn [ar_SP0 push amb] in *; lia| | exact Ha].
    intros b' Hb'. split; [exact (INCL9 b' Hb')|]. cbn [blk_id fst]. intros E. apply Hpg. rewrite <- E. apply in_map. exact Hb'. }
  assert (INV9 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [(pd', D', 19); (pg, G, 24)] ((q, f + 32, 20) :: LB) (C8 (Z_to_bv 64 f)) (rt_live RTS Σ9) Σ9 m9).
  { pose proof (@sc_inv_xfer (push AR f 1) sp spa f lo g OW LB pb out adr x m3 Σ1 ra s0 j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
    eapply L; clear L; first [exact INV8| exact HEAP9| exact AG9| kit_hyps]. }
  assert (BIO9 : sc_bio out pv m9 nw4) by (exact (sc_bio_xfer spa OW LB pb out pv HBIN m8 m9 nw4 BIO8 AG9)).
  assert (UW9 : uw_chain USTACK_TOP m9 spa (bv_unsigned sp) (bv_unsigned ra :: ras)) by (exact (sc_uw_xfer sp spa OW LB SPAH m8 m9 _ UW8 AG9)).
  assert (Hpd'O : ~ In pd' (map blk_id OW)) by (intros Hi; apply Hpd'; cbn [map app blk_id fst]; right; right; rewrite map_app; apply in_or_app; left; exact Hi).
  assert (HpgO : ~ In pg (map blk_id OW)) by (intros Hi; apply Hpg; rewrite map_app; apply in_or_app; left; exact Hi).
  assert (NEgd' : pg <> pd') by (intros E; apply Hpd'; cbn [map app blk_id fst]; right; left; exact E).
  clear MI9 ST9 AB9 INV8 BIO8 UW8 GC8 DC8 GS8 HEAP9. clear dependent m8.
  (* [comment removed for export] *)
  intros X3 Φ3 D3 S3 L3.
  pose proof (@sc_ts5ok (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4) (t := t) (LBc := (q, f + 32, 20) :: LB); clear L; first [exact INV9| exact BIO9| exact GA| exact GC9| exact DC9| exact UW9| kit_hyps];
    [clear - CR4 CR5 CR7 CR9 BUD BUDE HXE HXS; lia| intros b [<-|Hb]; [right; reflexivity| left; exact Hb]|].
  clear w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F9 fc9.
  intros w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F10 fc10 m10 Σ10 nw10 INV10 BIO10 CR10 LIVE10 GC10 UW10.
  (* [comment removed for export] *)
  eapply (implAp_elim _ Σ9 Σ10 Q _ X3 Φ3 D3); [| exact S3| exact L3| exact LIVE10].
  pose proof (@sc_gtfree_dyn (push AR f 1) UK BE sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw10) (LBc := (q, f + 32, 20) :: LB); clear L; first [exact INV10| exact BIO10| exact NEgd'| exact GC10| exact UW10| kit_hyps].
  clear INV9 BIO9 UW9 GC9 DC9. clear dependent m9.
  intros Σ11 ms11 PO.
  clear w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F10 fc10.
  destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F11 & fc11 & m11 & -> & MI11 & ST11 & AP11 & CR11 & HEAP11 & _).
  rewrite ESPA in ST11, AP11. rewrite (ret_pc_even 0x338094) by (clear; lia). unfold MallocRep.wz. cbn [ar_RT push amb] in CR11.
  rewrite (ts_list_back OW pg pd' G D' HpgO Hpd'O NEgd') in AP11, HEAP11.
  assert (AG11 : agree_on (aclient_addr (OW ++ LB) spa) m10 m11).
  { unfold apres in AP11. eapply agree_on_mono; [exact AP11|]. intros a Ha. cbv beta. apply (aclient_addr_mono (OW ++ LB)); [| exact Ha].
    intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
  assert (INV11 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [] ((q, f + 32, 20) :: LB) (C8 (Z_to_bv 64 f)) (rt_live RTS Σ11) Σ11 m11).
  { pose proof (@sc_inv_xfer (push AR f 1) sp spa f lo g OW LB pb out adr x m3 Σ1 ra s0 j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
    eapply L; clear L; first [exact INV10| exact HEAP11| exact AG11| kit_hyps]. }
  assert (BIO11 : sc_bio out pv m11 nw10) by (exact (sc_bio_xfer spa OW LB pb out pv HBIN m10 m11 nw10 BIO10 AG11)).
  clear MI11 ST11 AP11 INV10 BIO10 UW10 GC10 HEAP11. clear dependent m10.
  (* [comment removed for export] *)
  eapply (implAp_step (ARet (tt, st)) Σ11 Q _ (fun Σ' ms' => sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms'));
    [| intros Σ' ms' PO; apply implAp_ret; exact (KQ Σ' ms' PO)].
  pose proof (@sc_ts6 (push AR f 1) sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw10); clear L; first [exact INV11| exact BIO11| kit_hyps].
  intros m12 INV12 BIO12 AG12.
  pose proof (@sc_tail1 (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw10) (used := 24 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x))) (budget := budget); clear L; first [exact V0| exact INV12| exact BIO12| kit_hyps];
    try (clear - CR4 CR5 CR7 CR9 CR10 CR11 BUD BUDE HXL HXE HXS; lia).
  (* [comment removed for export] *)
  unfold at_exit. intros x1e v0 v1 v2 e0 e1 e2 e3 e4 e5 e6 e7 x19e x20e x21e x22e x23e x24e x27e v3 v4 v5 v6 Fce fce mx Σx nwx INVx BIOx CRx.
  destruct INVx as (HEAPx & LIVEx & MIx & STx & AGRx & FRLx & _ & FRHx & REPx & _). destruct BIOx as [NWx HBx].
  unfold sc_lo in FRLx. cbn [ar_RT ar_PMc push amb] in CRx, LIVEx |- *.
  (* [comment removed for export] *)
  eapply (sctp_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAPx| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STx| exact CEIL| clear - LO' SPAL; lia
    | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIx| exact (rw_cells_merge _ _ _ [CB 8 j0; CB 8 j8; CB 8 j16] [C8 (Z_to_bv 64 f)] _ FRLx)| exact FRHx| reflexivity|].
  intros Σe me x10' HEAPe CRe LIVEe STe MIe AGe.
  apply cps_post. intros c Hc. exists Σe. split; [| rewrite LIVEe; exact LIVEx].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold sct_print_postA, MallocRep.wz.
  do 15 eexists. exists Fce, fce, me, nwx. split; [reflexivity|].
  split; [exact HEAPe|]. split; [rewrite CRe; subst budget; clear - CRx CR1; lia|].
  split; [exact STe|]. split; [exact MIe|].
  split.
  { unfold apres_ex. eapply agree_on_trans; [exact AG3|]. eapply agree_on_trans; [exact AGRx|].
    eapply agree_on_mono; [exact AGe|]. intros a [Ha _]. destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Ha]. }
  split; [exact NWx|].
  eapply rw_cells_agree; [exact AGe| exact HBx|]. intros a Ha. unfold bio_null_cells, bio_cells in Ha. cbn in Ha. right; right. exists (pb, out, 128). split; [exact HBIN'| cbn; clear - Ha; lia].
Qed.

(* [comment removed for export] *)
Lemma SCT_print_v1failA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (pb : bptr) (out pv nw : Z) (adr : bptr -> Z) (x : sctr bptr) (st : ap_st bptr) (ras : list Z)
    (Q : unit * ap_st bptr -> rts RTS -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + SCT_PRINT_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (S (S (length FRM)))) < FRAMES_MAX)%nat -> sct_print_costA x <= rt_credit RTS Σ ->
  crypto_statics m -> realloc_statics m ->
  sct_repA m (OW ++ LB) adr x -> sc_version x = 0 -> gentime_adj (sc_ts x) = None ->
  In (pb, out, BIO_SIZE) OW -> ~ In pb (map blk_id (sct_blocks adr x)) ->
  rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_PRINT_A (bv_unsigned ra :: ras) ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
  (forall Σ' ms', sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms' -> Q (tt, st) Σ' ms') ->
  implAp (sct_print x st) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_PRINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED CS RS REP V0 GA HBIN NPB HB NW UW CTX -> -> -> -> KQ.
  unfold sct_print. rewrite V0, Z.eqb_refl. unfold timestamp_print.
  assert (PR : printable (sc_ts x) = false) by (unfold printable; rewrite GA; reflexivity). rewrite PR.
  pose proof LO as LO'. unfold SCT_PRINT_STACK_A, SC_BODY_STACK_A, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (OB0 & _ & _ & OBC & _). cbn [blk_addr blk_size fst snd] in OB0, OBC. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu.
  assert (CX : HX_CRED (prn_item_wt x) = HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) + HX_CRED (sc_extlen x) + HX_CRED (sc_siglen x)).
  { unfold prn_item_wt, HX_CRED. rewrite V0, Z.eqb_refl. clear; lia. }
  assert (HX0 : 0 <= HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) /\ 0 <= HX_CRED (sc_extlen x) /\ 0 <= HX_CRED (sc_siglen x)).
  { pose proof REP as (_ & _ & _ & _ & A2 & A3 & _ & _ & _ & _ & _ & _ & _ & EXL & _). unfold HX_CRED, CtSctP.SctRep.logid_len, CT_V1_HASHLEN, sc_siglen. rewrite EXL. unfold CtSctP.SctRep.olen.
    repeat split; [destruct (sc_logid x); clear; lia| destruct (sc_ext x) as [[q n]|]; [destruct A2 as (N0 & _); clear - N0; lia| clear; lia]| destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0; lia| clear; lia]]. }
  destruct HX0 as (HXL & HXE & HXS).
  intros XX Φ Dl SAFE LINK.
  (* [comment removed for export] *)
  change (wz SCT_PRINT_A) with (wz SCTP_ENTRY).
  eapply (sctp_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold SCTP_FRAME, RT_STACK; clear - LO'; lia| exact TOP| exact AL16| exact MI| reflexivity| clear - FLEN; lia
    | unfold sct_print_costA, SCT_PRINT_BASE_A in CRED; clear - CRED CX HXL HXE HXS; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 jf24 jf32 jf52 jst
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold SCTP_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (adr (sc_blk x)))) 7)) with (Z_to_bv 64 0).
  2:{ pose proof REP as (HSINz & AL16z & _). pose proof (AH_range_gen _ _ _ _ _ HEAP HSINz) as (BSz0 & _ & _ & BSzC & _). cbn [blk_addr blk_size fst snd] in BSz0, BSzC. unfold BnHeapA.ACEIL in BSzC.
      f_equal. rewrite unsigned_lit by (clear - BSz0 BSzC Cq3; unfold BnHeapA.ACEIL, SCT_SIZE in *; cbn [ar_SP0 push amb] in *; lia). change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2 ^ 3) with 8.
      revert AL16z. uchk_open. clear. intros AL16z. Z.div_mod_to_equations. lia. }
  assert (AG3 : agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(out, out + 128)]%Z a) m m3)
    by (eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha).
  assert (REP3 : sct_repA m3 (OW ++ LB) adr x).
  { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AGF|]. intros a Ha.
    destruct (sct_addr_block _ _ _ _ _ REP Ha) as (b & _ & HL & Hr). right; right. exists b. split; [exact HL| exact Hr]. }
  assert (CS3 : crypto_statics m3) by (exact (crypto_statics_agree _ m m3 AGF (fun a Ha => or_intror (or_introl (ar_LIBW_cs a Ha))) CS)).
  assert (RS3 : realloc_statics m3).
  { unfold realloc_statics in *. eapply ro_cells_agree; [exact AGF| exact RS|]. intros a Ha. cbn in Ha. unfold CR_REALLOC_IMPL in Ha. right; left. apply ar_LIBW_cs. unfold LIBW_A. cbn [rin_ivs fst snd]. clear - Ha. lia. }
  apply (rw_cells_agree _ _ _ _ _ AGF) in HB; [| intros xa Hxa; unfold bio_null_cells, bio_cells in Hxa; cbn in Hxa; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Hxa; lia]].
  assert (UW3 : uw_chain USTACK_TOP m3 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { eapply (uw_call m m3 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
      [exact UW| eapply agree_on_mono; [exact AGF| intros a Ha; left; exact Ha]| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia
      | clear - TOPu; unfold USTACK_TOP; lia| apply bv_unsigned_in_range| rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact HIGH]. }
  set (budget := sct_print_costA x - 1).
  assert (BUD : budget <= rt_credit RTS Σ1) by (subst budget; rewrite CR1; clear - CRED; lia).
  assert (BUDE : budget = 47 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) + HX_CRED (sc_extlen x) + HX_CRED (sc_siglen x)) by (subst budget; unfold sct_print_costA, SCT_PRINT_BASE_A; rewrite CX; clear; lia).
  assert (INV3 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [] LB (CB 8 j24) (rt_live RTS Σ) Σ1 m3).
  { split; [exact HEAP3|]. split; [exact LIVE1|]. split; [exact MI3|]. split; [exact ST3|]. split; [intros a _; reflexivity|].
    split; [exact LOW|]. split; [reflexivity|]. split; [exact HIGH|]. split; [exact REP3| intros b Hb; exact Hb]. }
  assert (BIO3 : sc_bio out pv m3 nw) by (split; [exact NW| exact HB]).
  (* [comment removed for export] *)
  assert (LOB : lo + SC_BODY_STACK_A <= spa) by (unfold SC_BODY_STACK_A, RT_STACK; clear - LO' SPAL; lia).
  assert (FLENB : (S (S (S (length ((f, 1%nat) :: FRM)))) < FRAMES_MAX)%nat) by (cbn [length]; clear - FLEN; lia).
  assert (HFR : In (f, 1%nat) ((f, 1%nat) :: FRM)) by (left; reflexivity).
  pose proof (@sc_seg0 (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as S0. cbn [ar_RT ar_PMc ar_FR push amb] in S0.
  assert (CRc : rt_credit RTS Σ1 <= rt_credit RTS Σ1) by (clear; lia).
  eapply S0 with (nw := nw) (c24 := CB 8 j24) (lv := rt_live RTS Σ) (budget := budget); clear S0; kit_hyps; try (clear - BUDE HXL HXE HXS BUD CRc; lia);
    [| intros; exfalso; match goal with H : sc_version x <> 0 |- _ => exact (H V0) end].
  clear CRc INV3 BIO3. intros x1a u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Fca fca m4 Σ4 nw4 _ INV4 BIO4 CRc.
  pose proof (@sc_v1a (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as S1. cbn [ar_RT ar_PMc ar_FR push amb] in S1.
  eapply S1 with (used := 6) (budget := budget) (j24 := j24); clear S1; kit_hyps; try (clear - BUDE HXL HXE HXS BUD CRc; lia).
  clear dependent m4. clear dependent Σ4. try clear CRc. try clear nw4.
  intros v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 Fcb fcb m4 Σ4 nw4 INV4 BIO4 CR4.
  (* [comment removed for export] *)
  pose proof INV4 as (HEAP4 & LIVE4 & MI4 & ST4 & AGR4 & FRL4 & SZ4 & FRH4 & REP4 & LBI4).
  assert (UW4 : uw_chain USTACK_TOP m4 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { eapply (uw_chain_rebase m3 m4); [exact UW3| exact HIGH| exact FRH4|]. eapply agree_on_mono; [exact AGR4|]. intros a Ha.
    split; [left; exact Ha| cbn [outside fst snd]; split; [clear - Ha OBCu CEILu LO' SPAL SPAH; lia| exact I]]. }
  eapply (implAp_elim _ Σ Σ4 Q _ XX Φ Dl); [| exact SAFE| exact LINK| exact LIVE4].
  unfold abind. cbn [apbind amalloc].
  pose proof (@sc_gtnew (push AR f 1) UK BE sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as SG. cbn [ar_RT ar_PMc ar_FR push amb] in SG.
  eapply SG with (nw := nw4) (lv := rt_live RTS Σ) (c24 := C8 (Z_to_bv 64 f)); clear SG; kit_hyps.
  clear HEAP4 LIVE4 MI4 ST4 AGR4 FRL4 SZ4 FRH4 REP4 LBI4.
  intros pg Σ5 ms5 Hpg PO. cbn [apbind fst snd]. unfold afree.
  destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F5 & fc5 & m5 & G & -> & MI5 & ST5 & AG5 & CR5 & GR & HEAP5 & ACC5 & GC5).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0 SPAL SPAH; lia).
  rewrite ESPA in ST5, AG5. rewrite (ret_pc_even 0x337fc8) by (clear; lia). unfold MallocRep.wz.
  assert (INV5 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [(pg, G, 24)] LB (C8 (Z_to_bv 64 f)) (rt_live RTS Σ5) Σ5 m5).
  { pose proof (@sc_inv_xfer (push AR f 1) sp spa f lo g OW LB pb out adr x m3 Σ1 ra s0 j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
    eapply L; clear L; first [exact INV4| exact HEAP5| kit_hyps]. }
  assert (BIO5 : sc_bio out pv m5 nw4) by (exact (sc_bio_xfer spa OW LB pb out pv HBIN m4 m5 nw4 BIO4 AG5)).
  assert (UW5 : uw_chain USTACK_TOP m5 spa (bv_unsigned sp) (bv_unsigned ra :: ras)) by (exact (sc_uw_xfer sp spa OW LB SPAH m4 m5 _ UW4 AG5)).
  assert (GRu : 0 < G < 2 ^ 64) by (destruct GR as (GR0 & _ & _ & GRC & _); change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in GRC; clear - GR0 GRC Cq3; lia).
  clear MI5 ST5 AG5 ACC5 INV4 BIO4 UW4. clear dependent m4.
  (* [comment removed for export] *)
  intros X1 Φ1 D1 S1 L1.
  pose proof (@sc_ts1 (push AR f 1) sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4); clear L; first [exact INV5| exact BIO5| exact GRu| kit_hyps].
  intros w0' w1' w2' d4' d5' d6' d7' w3' w4' w5' w6' m6 INV6 BIO6 SH6 AG6.
  (* [comment removed for export] *)
  pose proof INV6 as (HEAP6 & LIVE6 & MI6 & ST6 & AGR6 & FRL6 & SZ6 & FRH6 & REP6 & LBI6).
  destruct (bptr_fresh (map blk_id (((pg, G, 24) :: OW) ++ LB))) as [q Hq].
  assert (OFFL : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
  pose proof (@sc_genstr_open (push AR f 1) f GEO HFR Σ5 ((pg, G, 24) :: OW) LB m6 q HEAP6 OFFL SH6 Hq) as HEAP6o.
  assert (INV6o : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [(pg, G, 24)] ((q, f + 32, 20) :: LB) (C8 (Z_to_bv 64 f)) (rt_live RTS Σ5) Σ5 m6).
  { split; [exact HEAP6o|]. split; [exact LIVE6|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact AGR6|]. split; [exact FRL6|]. split; [exact SZ6|]. split; [exact FRH6|].
    split; [exact REP6| intros b Hb; right; exact Hb]. }
  pose proof GEO as (Ge1 & Ge2 & Ge3 & Ge4 & Ge5). change (fs_size 1) with 128 in Ge3, Ge5. unfold BnHeapA.ACEIL in Ge3. unfold SEGTOP_A in Ge4.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. clear - Ge1 Ge3 Ge4 Cq3. unfold BnHeapA.ACEIL in *. Z.div_mod_to_equations. lia. }
  pose proof (AH_offsh _ _ _ _ (pg, G, 24) HEAP5 (or_introl eq_refl)) as OFSG. cbn [blk_addr blk_size fst snd] in OFSG. unfold SHLO, SHHI in OFSG.
  assert (GC6 : rw_cells ctasegs m6 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0)).
  { eapply rw_cells_agree; [exact AG6| exact GC5|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha. cbv beta. clear - Ha OFSG SHR. lia. }
  assert (UW6 : uw_chain USTACK_TOP m6 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { eapply uw_chain_agree; [exact UW5|]. eapply agree_on_mono; [exact AG6|]. intros a Ha. cbv beta. clear - Ha SHR Cq2 CEILu LOB. unfold BnHeapA.ACEIL, SC_BODY_STACK_A, RT_STACK in *. lia. }
  clear HEAP6 LIVE6 MI6 ST6 AGR6 FRL6 SZ6 FRH6 REP6 LBI6 HEAP6o SH6 AG6 INV6 GC5 HEAP5 UW5 INV5 BIO5. clear dependent m5.
  (* [comment removed for export] *)
  pose proof (@sc_ts2fail (push AR f 1) sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  change (mcost 24) with 0 in CR5. cbn [ar_RT push amb] in CR5.
  eapply L with (nw := nw4) (LBc := (q, f + 32, 20) :: LB); clear L; first [exact INV6o| exact BIO6| exact GA| kit_hyps];
    [clear - CR4 CR5 BUD BUDE HXE HXS; lia| clear - GRu; lia|].
  clear w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F5 fc5.
  intros y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F7 fc7 m7 Σ7 INV7 BIO7 CR7 AB7.
  try clear x1a u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Fca fca v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 Fcb fcb.
  assert (INCL7 : forall b, In b (OW ++ LB) -> In b (((pg, G, 24) :: OW) ++ (q, f + 32, 20) :: LB)).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; right; exact Hb]. }
  assert (AG7 : agree_on (aclient_addr (OW ++ LB) spa) m6 m7) by (eapply agree_on_mono; [exact AB7|]; intros a Ha; exact (aclient_addr_mono _ _ _ _ INCL7 Ha)).
  assert (GC7 : rw_cells ctasegs m7 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0)).
  { eapply rw_cells_agree; [exact AB7| exact GC6|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha. right; right. exists (pg, G, 24). split; [apply in_or_app; left; left; reflexivity| cbn; clear - Ha; lia]. }
  assert (UW7 : uw_chain USTACK_TOP m7 spa (bv_unsigned sp) (bv_unsigned ra :: ras)) by (exact (sc_uw_xfer sp spa OW LB SPAH m6 m7 _ UW6 AG7)).
  pose proof (proj1 (proj2 INV7)) as LIVE7. cbn [ar_RT push amb] in CR7, LIVE7.
  clear AB7 INV6o BIO6 UW6 GC6. clear dependent m6.
  (* [comment removed for export] *)
  pose proof (@sc_ts3fail (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4); clear L; first [exact INV7| exact BIO7| exact GRu| exact GA| exact GC7| exact UW7| kit_hyps].
  clear y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F7 fc7. try clear w0' w1' w2' d4' d5' d6' d7' w3' w4' w5' w6'.
  intros w0 w1 w2 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F8 fc8 m8 gtail INV8 BIO8 GC8 GS8 UW8.
  (* [comment removed for export] *)
  pose proof (@sc_ts4fail (push AR f 1) sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4) (gtail := gtail); clear L; first [exact INV8| exact BIO8| exact GA| exact GRu| exact GC8| exact GS8| exact UW8| kit_hyps];
    [clear - CR4 CR5 CR7 BUD BUDE HXE HXS; lia|].
  clear INV7 BIO7 UW7 GC7. clear dependent m7.
  clear w0 w1 w2 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F8 fc8.
  intros w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F10 fc10 m10 Σ10 INV10 BIO10 CR10 LIVE10 GC10 UW10.
  (* [comment removed for export] *)
  eapply (implAp_elim _ Σ5 Σ10 Q _ X1 Φ1 D1); [| exact S1| exact L1| rewrite LIVE10; exact LIVE7].
  pose proof (@sc_gtfree_nodata (push AR f 1) UK BE sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk (bv_unsigned ra :: ras)) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw4) (LBc := (q, f + 32, 20) :: LB); clear L; first [exact INV10| exact BIO10| exact GC10| exact UW10| kit_hyps].
  clear INV8 BIO8 UW8 GC8 GS8. clear dependent m8.
  intros Σ11 ms11 PO.
  clear w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F10 fc10.
  destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F11 & fc11 & m11 & -> & MI11 & ST11 & AP11 & CR11 & HEAP11 & _).
  rewrite ESPA in ST11, AP11. rewrite (ret_pc_even 0x338094) by (clear; lia). unfold MallocRep.wz. cbn [ar_RT push amb] in CR11.
  assert (HpgO : ~ In pg (map blk_id OW)) by (intros Hi; apply Hpg; rewrite map_app; apply in_or_app; left; exact Hi).
  rewrite lb_remove_cons in AP11, HEAP11. cbn [blk_id fst] in AP11, HEAP11. rewrite bptr_eqb_refl in AP11, HEAP11. rewrite (lb_remove_notin pg OW HpgO) in AP11, HEAP11.
  assert (AG11 : agree_on (aclient_addr (OW ++ LB) spa) m10 m11).
  { unfold apres in AP11. eapply agree_on_mono; [exact AP11|]. intros a Ha. cbv beta. apply (aclient_addr_mono (OW ++ LB)); [| exact Ha].
    intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
  assert (INV11 : @sc_inv (push AR f 1) sp spa f lo g OW LB out adr x m3 ra s0 j0 j8 j16 j32 j40 junk [] ((q, f + 32, 20) :: LB) (C8 (Z_to_bv 64 f)) (rt_live RTS Σ11) Σ11 m11).
  { pose proof (@sc_inv_xfer (push AR f 1) sp spa f lo g OW LB pb out adr x m3 Σ1 ra s0 j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
    eapply L; clear L; first [exact INV10| exact HEAP11| exact AG11| kit_hyps]. }
  assert (BIO11 : sc_bio out pv m11 nw4) by (exact (sc_bio_xfer spa OW LB pb out pv HBIN m10 m11 nw4 BIO10 AG11)).
  clear MI11 ST11 AP11 INV10 BIO10 UW10 GC10 HEAP11. clear dependent m10.
  rename nw4 into nw10.
  assert (CR9 : True) by exact I.
  (* [comment removed for export] *)
  eapply (implAp_step (ARet (tt, st)) Σ11 Q _ (fun Σ' ms' => sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms'));
    [| intros Σ' ms' PO; apply implAp_ret; exact (KQ Σ' ms' PO)].
  pose proof (@sc_ts6 (push AR f 1) sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw10); clear L; first [exact INV11| exact BIO11| kit_hyps].
  intros m12 INV12 BIO12 AG12.
  pose proof (@sc_tail1 (push AR f 1) PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 ra s0 gp j0 j8 j16 j32 j40 junk) as L. cbn [ar_RT ar_PMc ar_FR push amb] in L.
  eapply L with (nw := nw10) (used := 24 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x))) (budget := budget); clear L; first [exact V0| exact INV12| exact BIO12| kit_hyps];
    try (clear - CR4 CR5 CR7 CR9 CR10 CR11 BUD BUDE HXL HXE HXS; lia).
  (* [comment removed for export] *)
  unfold at_exit. intros x1e v0 v1 v2 e0 e1 e2 e3 e4 e5 e6 e7 x19e x20e x21e x22e x23e x24e x27e v3 v4 v5 v6 Fce fce mx Σx nwx INVx BIOx CRx.
  destruct INVx as (HEAPx & LIVEx & MIx & STx & AGRx & FRLx & _ & FRHx & REPx & _). destruct BIOx as [NWx HBx].
  unfold sc_lo in FRLx. cbn [ar_RT ar_PMc push amb] in CRx, LIVEx |- *.
  (* [comment removed for export] *)
  eapply (sctp_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAPx| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STx| exact CEIL| clear - LO' SPAL; lia
    | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIx| exact (rw_cells_merge _ _ _ [CB 8 j0; CB 8 j8; CB 8 j16] [C8 (Z_to_bv 64 f)] _ FRLx)| exact FRHx| reflexivity|].
  intros Σe me x10' HEAPe CRe LIVEe STe MIe AGe.
  apply cps_post. intros c Hc. exists Σe. split; [| rewrite LIVEe; exact LIVEx].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold sct_print_postA, MallocRep.wz.
  do 15 eexists. exists Fce, fce, me, nwx. split; [reflexivity|].
  split; [exact HEAPe|]. split; [rewrite CRe; subst budget; clear - CRx CR1; lia|].
  split; [exact STe|]. split; [exact MIe|].
  split.
  { unfold apres_ex. eapply agree_on_trans; [exact AG3|]. eapply agree_on_trans; [exact AGRx|].
    eapply agree_on_mono; [exact AGe|]. intros a [Ha _]. destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Ha]. }
  split; [exact NWx|].
  eapply rw_cells_agree; [exact AGe| exact HBx|]. intros a Ha. unfold bio_null_cells, bio_cells in Ha. cbn in Ha. right; right. exists (pb, out, 128). split; [exact HBIN'| cbn; clear - Ha; lia].
Qed.

(* [comment removed for export] *)
Lemma SCT_print_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (pb : bptr) (out pv nw : Z) (adr : bptr -> Z) (x : sctr bptr) (st : ap_st bptr) (ras : list Z)
    (Q : unit * ap_st bptr -> rts RTS -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + SCT_PRINT_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (S (S (length FRM)))) < FRAMES_MAX)%nat -> sct_print_costA x <= rt_credit RTS Σ ->
  crypto_statics m -> realloc_statics m ->
  sct_repA m (OW ++ LB) adr x ->
  In (pb, out, BIO_SIZE) OW -> ~ In pb (map blk_id (sct_blocks adr x)) ->
  rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_PRINT_A (bv_unsigned ra :: ras) ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
  (forall Σ' ms', sct_print_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo out pv m (sct_print_costA x) Σ' ms' -> Q (tt, st) Σ' ms') ->
  implAp (sct_print x st) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_PRINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED CS RS REP HBIN NPB HB NW UW CTX A0 A1 A2 A3 KQ.
  destruct (Z.eq_dec (sc_version x) 0) as [V0|NV].
  - destruct (gentime_adj (sc_ts x)) as [t|] eqn:GA.
    + exact (SCT_print_v1okA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo pb out pv nw adr x st t ras Q
               HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED CS RS REP V0 GA HBIN NPB HB NW UW CTX A0 A1 A2 A3 KQ).
    + exact (SCT_print_v1failA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo pb out pv nw adr x st ras Q
               HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED CS RS REP V0 GA HBIN NPB HB NW UW CTX A0 A1 A2 A3 KQ).
  - exact (SCT_print_nv1A ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo pb out pv nw adr x st Q
             HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED REP NV HBIN NPB HB NW A0 A1 A2 A3 KQ).
Qed.
End V1.

End WithRT.
