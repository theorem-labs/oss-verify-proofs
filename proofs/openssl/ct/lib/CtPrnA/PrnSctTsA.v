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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA RtGenStmtA W_crypto_reallocA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_prefix_create W_strdup W_obj_free W_asn1_stringA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_time_leavesA W_snprintfA W_time_from_tmA W_gentime_adjA W_time_to_tm_frontA W_gentime_set_stringA W_time_printA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnFmtA W_bio_hex_stringA PrnSctFmtA PrnSctKitA PrnStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv W_sct_print_B1 PrnLeaf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeFmtPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Import ListNotations.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_detP : forall (m : mem) a (bs1 bs2 : list BvBase.byte), bytes_at ctasegs m a bs1 -> bytes_at ctasegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i) Hi), (proj2 (nth_error_None bs2 i) ltac:(lia)). reflexivity.
Qed.

Section SNP.
Context {AR : ARun}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.
Lemma snprintf_vargs_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo D nD A : Z) (bd : block)
    (fmt : list Z) (args : list parg) (o : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp <= USTACK_TOP - 16 -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= D -> D + nD <= blk_addr bd + blk_size bd ->
  vfmtA_ok A fmt args o -> zlength o <= nD - 1 -> 1 <= nD -> nD < 2^31 ->
  vargs_okx RTS Σ m sp lo D nD [a3; a4; a5; a6; a7] args (vcovs fmt args) ->
  a0 = wz D -> a1 = wz nD -> a2 = wz A ->
  cps ctasegs (ASTA RTS Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_snprintf) fc None m (seg_rom ctasegs))))
      (ASTA RTS Σ PMc (snp_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo D o m)).
Proof.
  intros until o. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 VF OLEN N1 N2 VARGS -> -> ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & BDI).
  pose proof (blk_checked_dst Σ OW LB m sp bd D nD HEAP IND D1 D2 ltac:(lia)) as CD.
  eapply cps_conseq; [ eapply (rc_snprintf _ PFC Σ PMc) with (D := D) (n := nD) (A := A) (fmt := fmt) (stk := []) (args := args) (o := o) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact (vfmtA_vfmt AR Σ OW LB m A fmt args o VF HEAP MI).
  - unfold va_area. cbn [u64s map concat]. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - unfold USTACK_TOP, zlength. cbn. lia.
  - left. reflexivity.
  - rewrite app_nil_r. exact VARGS.
  - exact N1.
  - exact N2.
  - exact OLEN.
  - lia.
  - unfold BnHeapA.ACEIL, USTACK_TOP in *. lia.
  - unfold SEGTOP_A. unfold BnHeapA.ACEIL in *. lia.
  - exact CD.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold snp_postA, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split; [exact (AH_same' _ _ _ _ _ _ _ _ bd HEAP ART2 WM2 PRES IND D1 ltac:(lia))|].
    split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    exact BZ.
Qed.
End SNP.

Section TS.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.          (* [comment removed for export] *)
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.

Variables (sp : word) (spa f lo : Z) (g : nat) (OW LB : list block) (pb : bptr) (out pv : Z) (adr : bptr -> Z) (x : sctr bptr).
Variables (m3 : mem) (Σ1 : rts RTS) (vra v8 gp : word) (j0 j8 j16 j32 j40 junk : list (bv 8)) (ras1 : list Z).

Hypothesis HEAP3 : AHEAP Σ1 OW LB m3.
Hypothesis CEIL : ACEIL <= lo.
Hypothesis LO : lo + SC_BODY_STACK_A <= spa.
Hypothesis SPAL : bv_unsigned sp - 176 <= spa.
Hypothesis SPAH : spa <= bv_unsigned sp - 160.
Hypothesis SPA32 : spa mod 32 = 0.
Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 72.
Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis FLEN : (S (S (S (length FRM))) < FRAMES_MAX)%nat.
Hypothesis HBIN : In (pb, out, BIO_SIZE) OW.
Hypothesis REP3 : sct_repA m3 (OW ++ LB) adr x.
Hypothesis NPB : ~ In pb (map blk_id (sct_blocks adr x)).
Hypothesis GEO : fr_geo f 1.
Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 1 b.
Hypothesis CS3 : crypto_statics m3.
Hypothesis CTX : uk_ctx SCT_PRINT_A ras1.
Hypothesis HFR : In (f, 1%nat) FRM.
Hypothesis RS3 : realloc_statics m3.
Hypothesis REA : realloc_contract_gen RTS.

Local Notation sc_invL := (sc_inv sp spa f lo g OW LB out adr x m3 vra v8 j0 j8 j16 j32 j40 junk).
Local Notation sc_bioL := (sc_bio out pv).

Local Ltac facts :=
  pose proof (sc_factsA sp OW LB pb out adr x m3 Σ1 HEAP3 HBIN REP3 NPB) as (OB0 & OBC & Cq1 & Cq2 & Cq3 & SCTA); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3;
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  pose proof LO as LO'; unfold SC_BODY_STACK_A, RT_STACK in LO';
  pose proof CEIL as CEILu; unfold BnHeapA.ACEIL in CEILu; pose proof TOP as TOPu; unfold USTACK_TOP in TOPu;
  pose proof OBC as OBCu; unfold BnHeapA.ACEIL in OBCu;
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0 SPAL SPAH; lia).

Lemma sc_bio_img : out + 128 <= 65536 \/ 12365824 <= out.
Proof.
  pose proof (AH_range_gen _ _ _ _ _ HEAP3 (in_or_app _ _ _ (or_introl HBIN))) as (_ & _ & _ & _ & BI). cbn [blk_addr blk_size fst snd] in BI. unfold BIO_SIZE in BI. exact BI.
Qed.

(* [comment removed for export] *)
Lemma sc_cs : forall OWx LBc c24 lv Σc m, sc_invL OWx LBc c24 lv Σc m -> crypto_statics m.
Proof.
  intros OWx LBc c24 lv Σc m INV. destruct INV as (HEAP & _ & _ & _ & AGR & _).
  pose proof (sc_factsA sp OW LB pb out adr x m3 Σ1 HEAP3 HBIN REP3 NPB) as (OB0 & OBC & Cq1 & _).
  assert (HP : forall a, libw a -> aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(out, out + 128)]%Z a).
  { intros a Ha. split; [right; left; exact (ar_LIBW_cs a Ha)|].
    pose proof sc_bio_img as BI. unfold libw, LIBW_A in Ha. cbn [rin_ivs fst snd outside] in Ha |- *. split; [| exact I]. clear - Ha BI. lia. }
  exact (crypto_statics_agree _ m3 m AGR HP CS3).
Qed.

(* [comment removed for export] *)
Lemma libw_clientP : forall a, libw a -> aclient_addr (OW ++ LB) spa a /\ outside [(out, out + 128)]%Z a.
Proof.
  pose proof (sc_factsA sp OW LB pb out adr x m3 Σ1 HEAP3 HBIN REP3 NPB) as (OB0 & OBC & Cq1 & _).
  pose proof LO as LO'. unfold SC_BODY_STACK_A, RT_STACK in LO'. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. unfold BnHeapA.ACEIL, SEGTOP_A in Cq1.
  intros a Ha. split; [left; unfold libw, LIBW_A in Ha; cbn [rin_ivs fst snd] in Ha; unfold USTACK_TOP; clear - Ha Cq1 CEILu LO'; lia|] || (split; [right; left; exact (ar_LIBW_cs a Ha)|]).
  pose proof sc_bio_img as BI. unfold libw, LIBW_A in Ha. cbn [rin_ivs fst snd outside] in Ha |- *. split; [| exact I]. clear - Ha BI. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_gtnew : forall {X : Type} (k : option bptr -> aprog bptr X) (Q : X -> rts RTS -> machine_state -> Prop)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x18 x23 x24 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (c24 : cell),
  sc_invL [] LB c24 lv Σc m -> sc_bioL m nw ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA (Z_to_bv 64 0x337fc8) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) x18 (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB)
                  Σc OW LB 24 lo m (fun A m' => rw_cells ctasegs m' A (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0)) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc 24 k) Σc Q
    (MS (mkR (Z_to_bv 64 0x337fc8) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x247010) fc None m (seg_rom ctasegs)).
Proof.
  intros until c24. intros INV BIO UW K. pose proof (sc_cs _ _ _ _ _ _ INV) as CS. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). facts.
  pose proof (munch_refl [(spa - 16, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 5 zstep. do 2 zstep. release_frame FR ST spa. zstep. zstep.
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σc OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) spa) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  apply evt_done. change (Z_to_bv 64 2247428) with (wz ASN1_STRING_TYPE_NEW_A).
  eapply (ASN1_STRING_type_new_walkA) with (lo := lo) (OW := OW) (LB := LB) (ty := 24) (ras := ras1); rewrite ?ESPA; try reflexivity.
  - exact HEAP1.
  - exact ST.
  - exact CEIL.
  - unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI1.
  - exact (crypto_statics_agree _ m m1 AG1 (fun a Ha => proj1 (libw_clientP a Ha)) CS).
  - clear; lia.
  - eapply uw_chain_agreeP; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact UW|]. intros a _ Ha. cbn [outside fst snd]. clear - Ha SPAH; lia.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_tail _ _ _ E_ASN1_GENERALIZEDTIME_new_24a164 (uk_ctx_call _ _ _ _ E_SCT_print_34c3ec CTX)).
  - intros p Σ' ms' Hp PO. apply (K p Σ' ms' Hp).
    unfold calloc_postA in PO |- *. rewrite ?ESPA in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & A & -> & MI' & ST' & AG' & CR' & RA & HEAP' & ACC' & INIT').
    do 14 eexists. exists F', fc', m', A. rewrite ?ESPA. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split; [| split; [exact CR'| split; [exact RA| split; [exact HEAP'| split; [exact ACC'| exact INIT']]]]].
    eapply agree_on_trans; [exact AG1| exact AG'].
Qed.
(* [comment removed for export] *)
Lemma ro_C8_of_imageA : forall m A v, mem_inv ctasegs m -> ro_bytes_b ctasegs A (le8 (Z_to_bv 64 v)) = true -> 0 <= A -> A + 8 <= 2^64 ->
  ro_cells ctasegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v MI RB A0 A8. split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  apply ro_bytes_at; [exact MI| lia| rewrite length_le8; lia|]. apply ro_bytes_b_sound. exact RB.
Qed.
Lemma magicA_cells : forall m, mem_inv ctasegs m ->
  ro_cells ctasegs m 0x10418 [C8 (Z_to_bv 64 13992196986280431)] /\ ro_cells ctasegs m 0x10478 [C8 (Z_to_bv 64 2361183241434822607)].
Proof. intros m MI. split; (apply ro_C8_of_imageA; [exact MI| vm_compute; reflexivity| clear; lia| clear; lia]). Qed.

(* [comment removed for export] *)
Lemma sc_ts1 : forall (Q : config -> Prop) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 x24 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg : bptr) (G : Z) (c24 : cell),
  sc_invL [(pg, G, 24)] LB c24 lv Σc m -> sc_bioL m nw -> 0 < G < 2^64 ->
  (forall (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
     sc_invL [(pg, G, 24)] LB c24 lv Σc m' -> sc_bioL m' nw ->
     rw_cells ctasegs m' (shad f + 4) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4)] ->
     agree_on (fun a => ~ (shad f <= a < shad f + 16)) m m' ->
     cps ctasegs (ASTA RTS Σc PMc (eq
       (MS (mkR (Z_to_bv 64 0x338028) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 0) (Z_to_bv 64 (ts_day (sc_ts x))) (Z_to_bv 64 (ts_sec (sc_ts x))) a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc (Z_to_bv 64 0x270c5c) fc None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x337fc8) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until c24. intros INV BIO GR K. pose proof INV as INV'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. 
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof LO as LO'. unfold SC_BODY_STACK_A, RT_STACK in LO'. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. unfold SEGTOP_A in G4.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  pose proof (ts_day_range (sc_ts x)) as DR. pose proof (ts_sec_range (sc_ts x)) as SR.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  (* [comment removed for export] *)
  destruct (AH_fr_wr _ _ _ _ f 1%nat HEAP HFR) as [_ WS]. change (fs_size 1 / 8) with 16 in WS.
  destruct (wr_at_rw_CB m (shad f) _ WS ltac:(clear; lia)) as (js & FRS). change (Z.to_nat 16) with 16%nat in FRS. clear WS.
  apply (rw_cells_split_CB ctasegs _ _ [] 16 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. clear - G1 G3 G4 Cq3. unfold BnHeapA.ACEIL in *. Z.div_mod_to_equations. lia. }
  destruct (magicA_cells m MI) as [MG1 MG2].
  pose proof (munch_refl [(spa, spa); (f, f + 0); (shad f, shad f + 16)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof (AH_offsh _ _ _ _ _ HEAP3 (in_or_app _ _ _ (or_introl HBIN))) as OFFB. cbn [blk_addr blk_size fst snd] in OFFB. unfold BIO_SIZE, SHLO, SHHI in OFFB.
  lazymatch type of HB with ?T => change (frozen T) in HB end.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. sbstep. sbstep. sbstep.
  unfold frozen in HB.
  match goal with MUx : munch _ m ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUx)) in HB; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa OFFB SHR; repeat split; try exact I; lia] end.
  zstep. if_cases Kg; zify_cond Kg; [exfalso; rewrite ?unsigned_lit in Kg by (clear - GR; lia); clear - Kg GR; lia|]. try clear Kg.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (day_reg (sc_ts x) TSR). rewrite (sec_reg (sc_ts x) TSR). rewrite Z.add_0_r, swrap32_sint32. change (sint32 (sc_ts x / 86400000)) with (ts_day (sc_ts x)).
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (OFFL : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
  assert (HEAP1 : AHEAP Σc ((pg, G, 24) :: OW) LB m1).
  { eapply (fr3_heap Σc ((pg, G, 24) :: OW) LB m m1 f 1%nat spa spa 0 16 HFR HEAP MU1 WM1);
      [unfold BnHeapA.ACEIL; clear - CEILu LO'; lia| unfold USTACK_TOP; clear - TOPu SPAH; lia| change (fs_size 1) with 128; clear; lia| change (fs_size 1) with 128; clear; lia| exact OFFL]. }
  assert (OWoff : forall b, In b (((pg, G, 24) :: OW) ++ LB) -> off_fr f 1 b).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (AH_ow_off_fr Σc ((pg, G, 24) :: OW) LB m f 1%nat b HEAP HFR Hb)| exact (OFFL b Hb)]. }
  assert (AG1 : agree_on (aclient_addr (((pg, G, 24) :: OW) ++ LB) spa) m m1).
  { eapply (fr3_agree Σc ((pg, G, 24) :: OW) LB m m m1 f 1%nat spa spa 0 16 (((pg, G, 24) :: OW) ++ LB) HEAP MU1 GEO);
      [change (fs_size 1) with 128; clear; lia| change (fs_size 1) with 128; clear; lia| unfold BnHeapA.ACEIL; clear - CEILu LO'; lia| clear; lia| intros b Hb; exact Hb| exact OWoff]. }
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (((pg, G, 24) :: OW) ++ LB) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact Hb]. }
  pose proof (sc_factsA sp OW LB pb out adr x m3 Σ1 HEAP3 HBIN REP3 NPB) as (_ & _ & _ & _ & _ & SCTA).
  lazymatch goal with FRS : rw_cells _ m1 (shad f) (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) |- _ =>
    destruct (proj1 (OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA.ApWalkTac.rw_cells_app m1 (shad f) [c0; c1; c2; c3] (c4 :: c5 :: c6 :: rest)) FRS) as [_ FRS2];
    destruct (proj1 (OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA.ApWalkTac.rw_cells_app m1 _ [c4; c5; c6] rest) FRS2) as [FRS3 _]; clear FRS2 end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS3.
  apply evt_done. eapply K.
  - split; [exact HEAP1|]. split; [exact LIVE|]. split; [exact MI1|]. split; [exact ST1|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AG1|]. intros a [Ha _]. exact (LBI' a Ha). }
    split; [assumption|]. split; [exact SZ|]. split; [assumption|].
    split; [| exact LBI]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG1|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (LBI' a C).
  - split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; assumption].
  - first [exact FRS3| eapply rw_cells_recast; [exact FRS3| cbn; tauto| reflexivity| reflexivity]].
  - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. clear - Ha. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
Lemma sc_rs : forall OWx LBc c24 lv Σc m, sc_invL OWx LBc c24 lv Σc m -> realloc_statics m.
Proof.
  intros OWx LBc c24 lv Σc m INV. destruct INV as (HEAP & _ & _ & _ & AGR & _).
  unfold realloc_statics in *. eapply ro_cells_agree; [exact AGR| exact RS3|].
  intros a Ha. cbn in Ha. unfold CR_REALLOC_IMPL in Ha. pose proof sc_bio_img as BI.
  pose proof (sc_factsA sp OW LB pb out adr x m3 Σ1 HEAP3 HBIN REP3 NPB) as (OB0 & OBC & Cq1 & _).
  split.
  - right; left. apply ar_LIBW_cs. unfold LIBW_A. cbn [rin_ivs fst snd]. clear - Ha. lia.
  - cbn [outside fst snd]. split; [| exact I]. clear - Ha BI. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_genstr_open : forall Σc OWf LBc m q,
  AHEAP Σc OWf LBc m -> (forall b, In b LBc -> off_fr f 1 b) ->
  rw_cells ctasegs m (shad f + 4) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4)] -> ~ In q (map blk_id (OWf ++ LBc)) ->
  AHEAP Σc OWf ((q, f + 32, 20) :: LBc) m.
Proof.
  intros Σc OWf LBc m q HEAP OFFL FRS Hq.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (frame_obj_open Σc OWf LBc m f 1%nat q (f + 32) 20 HFR HEAP); [clear; lia| change (fs_size 1) with 128; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m (shad f + 4) _ 0%nat (f + 32) 20 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (OFFL b Hb) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 1) with 128 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_ts2ok : forall {X : Type} (k : option bptr -> aprog bptr X) (Q : X -> rts RTS -> machine_state -> Prop)
    (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg : bptr) (G : Z) (c24 : cell) (t : tm6) (LBc : list block),
  sc_invL [(pg, G, 24)] LBc c24 lv Σc m -> sc_bioL m nw -> 2 <= rt_credit RTS Σc ->
  rw_cells ctasegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) -> gentime_adj (sc_ts x) = Some t ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall p Σ' ms', ~ In p (map blk_id (((pg, G, 24) :: OW) ++ LBc)) ->
     gentime_adj_postA (Z_to_bv 64 0x338028) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB)
                       Σc ((pg, G, 24) :: OW) LBc G lo m t (2 + mcost 20) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc 20 k) Σc Q
    (MS (mkR (Z_to_bv 64 0x338028) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 0) (Z_to_bv 64 (ts_day (sc_ts x))) (Z_to_bv 64 (ts_sec (sc_ts x))) a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x270c5c) fc None m (seg_rom ctasegs)).
Proof.
  intros until LBc. intros INV BIO CR2 HG GA UW K. pose proof (sc_cs _ _ _ _ _ _ INV) as CS. pose proof (sc_rs _ _ _ _ _ _ INV) as RS.
  destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  assert (MC0 : mcost 20 = 0) by reflexivity.
  change (Z_to_bv 64 0x270c5c) with (wz ASN1_GENERALIZEDTIME_ADJ_A).
  eapply (gentime_adj_okA PFC) with (lo := lo) (OW := (pg, G, 24) :: OW) (LB := LBc) (gb := pg) (ts := sc_ts x) (t := t) (ras := ras1); rewrite ?ESPA; try reflexivity.
  - exact HEAP.
  - exact ST.
  - exact CEIL.
  - unfold GENTIME_ADJ_STACK_A, FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS.
  - exact RS.
  - clear - FLEN. lia.
  - rewrite MC0. clear - CR2. lia.
  - left. reflexivity.
  - exact HG.
  - exact TSR.
  - exact GA.
  - exact UW.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_SCT_print_34c44c CTX).
  - exact K.
Qed.

(* [comment removed for export] *)
Lemma sc_ts2fail : forall (Q : config -> Prop) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg : bptr) (G : Z) (c24 : cell) (LBc : list block),
  sc_invL [(pg, G, 24)] LBc c24 lv Σc m -> sc_bioL m nw -> 2 <= rt_credit RTS Σc -> gentime_adj (sc_ts x) = None -> 0 <= G < 2^64 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS),
     sc_invL [(pg, G, 24)] LBc c24 lv Σc' m' -> sc_bioL m' nw -> rt_credit RTS Σc - 2 <= rt_credit RTS Σc' ->
     agree_on (aclient_addr (((pg, G, 24) :: OW) ++ LBc) spa) m m' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR (Z_to_bv 64 0x338028) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x338028) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR (Z_to_bv 64 0x338028) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 0) (Z_to_bv 64 (ts_day (sc_ts x))) (Z_to_bv 64 (ts_sec (sc_ts x))) a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x270c5c) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until LBc. intros INV BIO CR2 GA GR K. pose proof INV as INV'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (((pg, G, 24) :: OW) ++ LBc) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact (LBI b Hb)]. }
  change (Z_to_bv 64 0x270c5c) with (wz ASN1_GENERALIZEDTIME_ADJ_A).
  eapply (gentime_adj_failA) with (lo := lo) (OW := (pg, G, 24) :: OW) (LB := LBc) (ts := sc_ts x); rewrite ?ESPA; try reflexivity.
  - exact HEAP.
  - exact ST.
  - exact CEIL.
  - unfold GENTIME_ADJ_STACK_A, FROM_TM_STACK_A, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI.
  - clear - FLEN. lia.
  - exact CR2.
  - exact TSR.
  - exact GA.
  - intros Σ' m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' HEAP' CR' LIVE' ST' MI' AG'.
    rewrite (ret_pc_even 0x338028) by (clear; lia). unfold MallocRep.wz.
    assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
    eapply K.
    + split; [exact HEAP'|]. split; [rewrite LIVE'; exact LIVE|]. split; [exact MI'|]. split; [exact ST'|].
      split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. exact (LBI' a Ha). }
      split. { eapply rw_cells_agree; [exact AG'| exact FRL|]. intros xa Hxa. rewrite SZL in Hxa. left. unfold USTACK_TOP. clear - Hxa TOPu SPAH SPAL GSZ. lia. }
      split; [exact SZ|].
      split. { eapply rw_cells_agree; [exact AG'| exact FRH|]. intros xa Hxa. cbn in Hxa. left. unfold USTACK_TOP. clear - Hxa TOPu SPAH. lia. }
      split; [| exact LBI]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG'|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (LBI' a C).
    + split; [exact NW|]. eapply rw_cells_agree; [exact AG'| exact HB|]. intros xa Hxa. unfold bio_null_cells, bio_cells in Hxa. cbn in Hxa. right; right.
      exists (pb, out, 128). split; [apply in_or_app; left; right; exact HBIN| cbn; clear - Hxa; lia].
    + clear - CR'. lia.
    + exact AG'.
Qed.

(* [comment removed for export] *)
Lemma vfmtA_C18 : forall gs ms, zlength gs = 15 -> 0 <= ms < 1000 -> vfmtA_ok A_C18_A FMT_C18 [PA_s gs; PA_i ms] (ct_genstr gs ms).
Proof.
  intros gs ms Hg Hms. destruct (printf_piecesx_C18 gs ms ltac:(rewrite Hg; clear; lia) Hms) as (ps & P & CC). rewrite <- CC.
  eapply (vfmtA_of_pieces _ _ _ _ _ (0xa7d60, 12, 32) fmt_C18_roA fmt_bytes_C18 pass1x_ok_C18); [vm_compute; reflexivity| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia
    | cbv -[Z.le Z.lt Z.add]; clear; lia| exact P| clear; lia| apply fp_callsx_nog; repeat constructor| reflexivity| vm_compute; reflexivity].
Qed.
Lemma vfmtA_C18_null : forall ms, 0 <= ms < 1000 -> vfmtA_ok A_C18_A FMT_C18 [PA_sn; PA_i ms] (ct_genstr_null ms).
Proof.
  intros ms Hms. destruct (printf_piecesx_C18_null ms Hms) as (ps & P & CC). rewrite <- CC.
  eapply (vfmtA_of_pieces _ _ _ _ _ (0xa7d60, 12, 32) fmt_C18_roA fmt_bytes_C18 pass1x_ok_C18); [vm_compute; reflexivity| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia
    | cbv -[Z.le Z.lt Z.add]; clear; lia| exact P| clear; lia| apply fp_callsx_nog; repeat constructor| reflexivity| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma sc_ts3ok : forall (Q : config -> Prop) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg pd : bptr) (G D : Z) (c24 : cell) (t : tm6) (junk4 : list (bv 8)) (q : bptr),
  sc_invL [(pd, D, 20); (pg, G, 24)] ((q, f + 32, 20) :: LB) c24 lv Σc m -> sc_bioL m nw -> 0 < G < 2^64 -> gentime_adj (sc_ts x) = Some t ->
  rw_cells ctasegs m G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0) ->
  rw_cells ctasegs m D [CB 20%nat (zb (gen15 t) ++ Z_to_bv 8 0 :: junk4)] -> length junk4 = 4%nat ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     sc_invL [(pd, D, 20); (pg, G, 24)] ((q, f + 32, 20) :: LB) c24 lv Σc m' -> sc_bioL m' nw ->
     rw_cells ctasegs m' G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0) ->
     rw_cells ctasegs m' D [CB 20%nat (zb (gen15 t) ++ Z_to_bv 8 0 :: junk4)] ->
     rw_cells ctasegs m' (f + 32) [CB 20%nat (zb (genstr (sc_ts x)) ++ [Z_to_bv 8 0])] ->
     uw_chain USTACK_TOP m' spa (bv_unsigned sp) ras1 ->
     cps ctasegs (ASTA RTS Σc PMc (eq
       (MS (mkR (Z_to_bv 64 0x33807c) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x270a34) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x338028) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until q. intros INV BIO GR GA HG HD J4 UW K. pose proof INV as INV'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  pose proof (ts_ms_range (sc_ts x)) as MSR0. assert (MSR : 0 <= ts_ms (sc_ts x) < 1000) by (clear - MSR0; lia). clear MSR0. pose proof (gentime_adj_valid _ _ GA) as TV.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. unfold SEGTOP_A in G4.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  set (OWf := (pd, D, 20) :: (pg, G, 24) :: OW) in *.
  assert (HGIN : In (pg, G, 24) (OWf ++ (q, f + 32, 20) :: LB)) by (apply in_or_app; left; right; left; reflexivity).
  assert (HDIN : In (pd, D, 20) (OWf ++ (q, f + 32, 20) :: LB)) by (apply in_or_app; left; left; reflexivity).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HGIN) as (BG0 & _ & _ & BGC & BGI). cbn [blk_addr blk_size fst snd] in BG0, BGC, BGI. unfold BnHeapA.ACEIL in BGC.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HDIN) as (BD0 & _ & _ & BDC & BDI). cbn [blk_addr blk_size fst snd] in BD0, BDC, BDI. unfold BnHeapA.ACEIL in BDC.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP (or_intror (or_introl eq_refl)))) as ALG.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP (or_introl eq_refl))) as ALD.
  lazymatch type of BGI with ?T => change (frozen T) in BGI end. lazymatch type of BDI with ?T => change (frozen T) in BDI end.
  destruct (magicA_cells m MI) as [MG1 MG2].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof (munch_refl [(spa - 16, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply evt_cut.
  { eapply (ASN1_STRING_get0_data_specA) with (lo := lo) (OW := OWf) (LB := (q, f + 32, 20) :: LB) (xb := pg) (A := G) (len := 15) (ty := V_ASN1_GENERALIZEDTIME) (d := D) (fl := 0); rewrite ?ESPA;
      [exact HEAP| exact ST| exact MI| exact CEIL| clear - LO'; lia| exact HGIN| clear - ALG; uchk_open; Z.div_mod_to_equations; lia| exact HG| clear - BD0 BDC Cq3; unfold BnHeapA.ACEIL in *; lia| reflexivity]. }
  intros ms' PO. unfold leaf16A_post, leafA_post in PO. rewrite ?ESPA in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & _).
  rewrite (ret_pc_even 0x338034) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (AH_offsh _ _ _ _ _ HEAP3 (in_or_app _ _ _ (or_introl HBIN))) as OFFB. cbn [blk_addr blk_size fst snd] in OFFB. unfold BIO_SIZE, SHLO, SHHI in OFFB.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. clear - G1 G3 G4 Cq3. unfold BnHeapA.ACEIL in *. Z.div_mod_to_equations. lia. }
  assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  pose proof (agree_on_of_munch_nw _ _ _ MU1) as AG1.
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; cbn [outside fst snd]; clear - Hxa; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa SPAH; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in HB; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa OBCu CEILu LO'; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa BGC CEILu LO'; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in HD; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa BDC CEILu LO'; split; [lia| exact I]].
  assert (HEAP1 : AHEAP Σc OWf ((q, f + 32, 20) :: LB) m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (STK1 : forall a, aclient_addr (OWf ++ (q, f + 32, 20) :: LB) spa a -> outside [(spa - 16, spa)]%Z a).
  { intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OWf ++ (q, f + 32, 20) :: LB) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; right; exact Hb| right; exact (LBI b Hb)]. }
  assert (REP1 : sct_repA m1 (OW ++ LB) adr x).
  { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG1|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (STK1 a (LBI' a C)). }
  assert (UW1 : uw_chain USTACK_TOP m1 spa (bv_unsigned sp) ras1).
  { eapply uw_chain_agreeP; [exact AG1| exact UW|]. intros a _ Ha. cbn [outside fst snd]. clear - Ha SPAH; lia. }
  clear HEAP ST MI UW MU WM MG1 MG2. destruct (magicA_cells m1 MI1) as [MG1 MG2].
  pose proof (munch_refl [(spa - 16, spa)]%Z m1) as MU. pose proof (wmono_refl ctasegs m1) as WM.
  (* [comment removed for export] *)
  do 14 zstep.
  rewrite (ms_reg' (sc_ts x) TSR).
  (* [comment removed for export] *)
  pose proof HEAP1 as HEAPo.
  assert (HINT : In (q, f + 32, 20) (OWf ++ (q, f + 32, 20) :: LB)) by (apply in_or_app; right; left; reflexivity).
  assert (HDINo : In (pd, D, 20) (OWf ++ (q, f + 32, 20) :: LB)) by (apply in_or_app; left; left; reflexivity).
  pose proof (AH_ow_off_fr Σc OWf ((q, f + 32, 20) :: LB) m1 f 1%nat (pd, D, 20) HEAP1 HFR (or_introl eq_refl)) as OFD. unfold off_fr in OFD. change (fs_size 1) with 128 in OFD. cbn [blk_addr blk_size fst snd] in OFD.
  pose proof (AH_ow_off_fr Σc OWf ((q, f + 32, 20) :: LB) m1 f 1%nat (pg, G, 24) HEAP1 HFR (or_intror (or_introl eq_refl))) as OFG. unfold off_fr in OFG. change (fs_size 1) with 128 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  apply evt_done. eapply cps_step_same.
  { eapply (snprintf_vargs_cpsA PFC) with (lo := lo) (OW := OWf) (LB := (q, f + 32, 20) :: LB) (D := f + 32) (nD := 20) (A := A_C18_A) (bd := (q, f + 32, 20))
        (fmt := FMT_C18) (args := [PA_s (gen15 t); PA_i (ts_ms (sc_ts x))]) (o := ct_genstr (gen15 t) (ts_ms (sc_ts x))); rewrite ?ESPA; try reflexivity.
    - exact HEAPo.
    - exact ST1.
    - exact CEIL.
    - unfold RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI1.
    - exact HINT.
    - apply vfmtA_C18; [apply gen15_zlength| exact MSR].
    - rewrite zlength_ct_genstr by (first [rewrite gen15_zlength; clear; lia| exact MSR]). clear; lia.
    - clear; lia.
    - change (vcovs FMT_C18 _) with [@None Z; None]. cbn [vargs_okx varg_okx vhd_cov tl app].
      split; [| split; [| exact I]].
      + left. cbn [varg_ok]. exists junk4. rewrite unsigned_lit by (clear - BD0 BDC Cq3; unfold BnHeapA.ACEIL in *; lia). rewrite gen15_zlength.
        replace (zlength junk4) with 4 by (unfold zlength; rewrite J4; reflexivity).
        split; [destruct HD as [[_ BY] _]; cbn [cells_bytes cbytes app] in BY; rewrite app_nil_r in BY; exact BY|].
        split; [exact (gen15_tm_bytes t TV)|]. split; [clear; lia|]. split; [clear - ALD; uchk_open; Z.div_mod_to_equations; lia|].
        split; [exact BD0|]. split; [unfold USTACK_TOP; clear - BDC Cq3; unfold BnHeapA.ACEIL in *; lia|]. split; [left; clear - BDC CEILu; lia|]. split; [clear - OFD; lia|].
        split; [eapply acc_sub; [exact (proj2 (AH_acc _ _ _ _ _ HEAPo HDINo))| cbn; clear; lia| cbn; clear; lia]|].
        exact (proj1 (AH_rng _ _ _ _ spa (pd, D, 20) D 16 HEAPo HDINo ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))).
      + cbn [varg_ok]. rewrite unsigned_lit by (clear - MSR; lia). clear - MSR. split; [lia| reflexivity]. }
  intros msS PO. unfold snp_postA in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BZ).
  rewrite (ret_pc_even 0x338070) by (clear; lia). unfold MallocRep.wz.
  rewrite zlength_ct_genstr in AG2 by (first [rewrite gen15_zlength; clear; lia| exact MSR]).
  assert (CL2 : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OWf ++ (q, f + 32, 20) :: LB) spa a /\ ~ (f + 32 <= a < f + 32 + (19 + 1))).
  { intros a Ha. split.
    - exact (LBI' a Ha).
    - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO' SPAH SPAL; lia| |].
      + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
      + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
  apply (rw_cells_agree _ _ _ _ _ AG2) in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in FRH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HB; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pb, out, 128); split; [apply in_or_app; left; right; right; exact HBIN| cbn; clear - Hxa; lia]| pose proof (FRESH _ (in_or_app _ _ _ (or_introl HBIN))) as O; unfold off_fr, BIO_SIZE in O; change (fs_size 1) with 128 in O; cbn [blk_addr blk_size fst snd] in O; clear - Hxa O; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; split; [right; right; exists (pg, G, 24); split; [apply in_or_app; left; right; left; reflexivity| cbn; clear - Hxa; lia]| clear - Hxa OFG; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HD; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pd, D, 20); split; [exact HDINo| cbn; clear - Hxa; lia]| clear - Hxa OFD; lia]].
  assert (HGS : rw_cells ctasegs m2 (f + 32) [CB 20%nat (zb (genstr (sc_ts x)) ++ [Z_to_bv 8 0])]).
  { rewrite <- (genstr_some _ _ GA). pose proof (zlength_ct_genstr (gen15 t) (ts_ms (sc_ts x)) ltac:(rewrite gen15_zlength; clear; lia) MSR) as OL. unfold zlength in OL.
    split; [split; [cbn [cells_wf cell_wf]; rewrite length_app; unfold zb; rewrite length_map; cbn [length]; split; [clear - OL; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ]|].
    exact (proj1 (AH_acc _ _ _ _ _ HEAP2 HINT)). }
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  apply evt_done. eapply K.
  - split; [exact HEAP2|]. split; [exact LIVE|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_trans; [eapply agree_on_mono; [exact AG1| intros a [Ha _]; exact (STK1 a (LBI' a Ha))]|].
             eapply agree_on_mono; [exact AG2|]. intros a [Ha _]. exact (CL2 a Ha). }
    split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|].
    split; [| exact LBI]. eapply sct_repA_agree; [exact REP1|]. eapply agree_on_mono; [exact AG2|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (CL2 a C).
  - split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB].
  - exact HG.
  - exact HD.
  - exact HGS.
  - eapply uw_chain_agreeP; [exact AG2| exact UW1|]. intros a _ Ha. split; [left; clear - Ha SPAH; lia| clear - Ha G3 CEILu LO' SPAL SPAH; lia].
Qed.

(* [comment removed for export] *)
Lemma sc_ts3fail : forall (Q : config -> Prop) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg : bptr) (G : Z) (c24 : cell) (q : bptr),
  sc_invL [(pg, G, 24)] ((q, f + 32, 20) :: LB) c24 lv Σc m -> sc_bioL m nw -> 0 < G < 2^64 -> gentime_adj (sc_ts x) = None ->
  rw_cells ctasegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (gtail : list (bv 8)),
     sc_invL [(pg, G, 24)] ((q, f + 32, 20) :: LB) c24 lv Σc m' -> sc_bioL m' nw ->
     rw_cells ctasegs m' G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
     rw_cells ctasegs m' (f + 32) [CB 20%nat (zb (genstr (sc_ts x)) ++ Z_to_bv 8 0 :: gtail)] ->
     uw_chain USTACK_TOP m' spa (bv_unsigned sp) ras1 ->
     cps ctasegs (ASTA RTS Σc PMc (eq
       (MS (mkR (Z_to_bv 64 0x33807c) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x270a34) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x338028) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until q. intros INV BIO GR GA HG UW K. pose proof INV as INV'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  pose proof (ts_ms_range (sc_ts x)) as MSR0. assert (MSR : 0 <= ts_ms (sc_ts x) < 1000) by (clear - MSR0; lia). clear MSR0.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. unfold SEGTOP_A in G4.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  set (OWf := (pg, G, 24) :: OW) in *.
  assert (HGIN : In (pg, G, 24) (OWf ++ (q, f + 32, 20) :: LB)) by (apply in_or_app; left; left; reflexivity).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HGIN) as (BG0 & _ & _ & BGC & BGI). cbn [blk_addr blk_size fst snd] in BG0, BGC, BGI. unfold BnHeapA.ACEIL in BGC.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP (or_introl eq_refl))) as ALG.
  lazymatch type of BGI with ?T => change (frozen T) in BGI end.
  destruct (magicA_cells m MI) as [MG1 MG2].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof (munch_refl [(spa - 16, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply evt_cut.
  { eapply (ASN1_STRING_get0_data_specA) with (lo := lo) (OW := OWf) (LB := (q, f + 32, 20) :: LB) (xb := pg) (A := G) (len := 0) (ty := V_ASN1_GENERALIZEDTIME) (d := 0) (fl := 0); rewrite ?ESPA;
      [exact HEAP| exact ST| exact MI| exact CEIL| clear - LO'; lia| exact HGIN| clear - ALG; uchk_open; Z.div_mod_to_equations; lia| exact HG| clear; lia| reflexivity]. }
  intros ms' PO. unfold leaf16A_post, leafA_post in PO. rewrite ?ESPA in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & _).
  rewrite (ret_pc_even 0x338034) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (AH_offsh _ _ _ _ _ HEAP3 (in_or_app _ _ _ (or_introl HBIN))) as OFFB. cbn [blk_addr blk_size fst snd] in OFFB. unfold BIO_SIZE, SHLO, SHHI in OFFB.
  assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  pose proof (agree_on_of_munch_nw _ _ _ MU1) as AG1.
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; cbn [outside fst snd]; clear - Hxa; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa SPAH; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in HB; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa OBCu CEILu LO'; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa BGC CEILu LO'; split; [lia| exact I]].
  assert (HEAP1 : AHEAP Σc OWf ((q, f + 32, 20) :: LB) m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (STK1 : forall a, aclient_addr (OWf ++ (q, f + 32, 20) :: LB) spa a -> outside [(spa - 16, spa)]%Z a).
  { intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OWf ++ (q, f + 32, 20) :: LB) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact (LBI b Hb)]. }
  assert (REP1 : sct_repA m1 (OW ++ LB) adr x).
  { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG1|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (STK1 a (LBI' a C)). }
  assert (UW1 : uw_chain USTACK_TOP m1 spa (bv_unsigned sp) ras1).
  { eapply uw_chain_agreeP; [exact AG1| exact UW|]. intros a _ Ha. cbn [outside fst snd]. clear - Ha SPAH; lia. }
  clear HEAP ST MI UW MU WM MG1 MG2. destruct (magicA_cells m1 MI1) as [MG1 MG2].
  pose proof (munch_refl [(spa - 16, spa)]%Z m1) as MU. pose proof (wmono_refl ctasegs m1) as WM.
  (* [comment removed for export] *)
  do 14 zstep.
  rewrite (ms_reg' (sc_ts x) TSR).
  (* [comment removed for export] *)
  pose proof HEAP1 as HEAPo.
  assert (HINT : In (q, f + 32, 20) (OWf ++ (q, f + 32, 20) :: LB)) by (apply in_or_app; right; left; reflexivity).
  pose proof (AH_ow_off_fr Σc OWf ((q, f + 32, 20) :: LB) m1 f 1%nat (pg, G, 24) HEAP1 HFR (or_introl eq_refl)) as OFG. unfold off_fr in OFG. change (fs_size 1) with 128 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  apply evt_done. eapply cps_step_same.
  { eapply (snprintf_vargs_cpsA PFC) with (lo := lo) (OW := OWf) (LB := (q, f + 32, 20) :: LB) (D := f + 32) (nD := 20) (A := A_C18_A) (bd := (q, f + 32, 20))
        (fmt := FMT_C18) (args := [PA_sn; PA_i (ts_ms (sc_ts x))]) (o := ct_genstr_null (ts_ms (sc_ts x))); rewrite ?ESPA; try reflexivity.
    - exact HEAPo.
    - exact ST1.
    - exact CEIL.
    - unfold RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI1.
    - exact HINT.
    - apply vfmtA_C18_null. exact MSR.
    - rewrite zlength_ct_genstr_null by (exact MSR). clear; lia.
    - clear; lia.
    - change (vcovs FMT_C18 _) with [@None Z; None]. cbn [vargs_okx varg_okx vhd_cov tl app].
      split; [| split; [| exact I]].
      + cbn [varg_ok]. rewrite unsigned_lit by (clear; lia). reflexivity.
      + cbn [varg_ok]. rewrite unsigned_lit by (clear - MSR; lia). clear - MSR. split; [lia| reflexivity]. }
  intros msS PO. unfold snp_postA in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BZ).
  rewrite (ret_pc_even 0x338070) by (clear; lia). unfold MallocRep.wz.
  rewrite zlength_ct_genstr_null in AG2 by (exact MSR).
  assert (CL2 : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OWf ++ (q, f + 32, 20) :: LB) spa a /\ ~ (f + 32 <= a < f + 32 + (11 + 1))).
  { intros a Ha. split.
    - exact (LBI' a Ha).
    - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO' SPAH SPAL; lia| |].
      + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
      + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
  apply (rw_cells_agree _ _ _ _ _ AG2) in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in FRH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HB; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pb, out, 128); split; [apply in_or_app; left; right; exact HBIN| cbn; clear - Hxa; lia]| pose proof (FRESH _ (in_or_app _ _ _ (or_introl HBIN))) as O; unfold off_fr, BIO_SIZE in O; change (fs_size 1) with 128 in O; cbn [blk_addr blk_size fst snd] in O; clear - Hxa O; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; split; [right; right; exists (pg, G, 24); split; [apply in_or_app; left; left; reflexivity| cbn; clear - Hxa; lia]| clear - Hxa OFG; lia]].
  (* [comment removed for export] *)
  destruct (wr_at_rw_CB m2 (f + 32) 20 (proj1 (AH_acc _ _ _ _ _ HEAP2 HINT)) ltac:(clear; lia)) as (js & JS). change (Z.to_nat 20) with 20%nat in JS.
  pose proof JS as JS2. apply (rw_cells_split_CB ctasegs _ _ [] 20 _ [] [12; 8]%nat) in JS2; [| reflexivity]. cbn [mk_CB_cells app] in JS2.
  destruct (proj1 (OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA.ApWalkTac.rw_cells_app m2 _ [CB 12 (firstn 12 js)] [CB 8 (firstn 8 (skipn 12 js))]) JS2) as [JS1 _].
  pose proof (rw_cells_bytes_at _ _ _ _ JS1) as BY1. cbn [cells_bytes cbytes app] in BY1. rewrite app_nil_r in BY1.
  pose proof (zlength_ct_genstr_null (ts_ms (sc_ts x)) MSR) as OL. unfold zlength in OL.
  assert (E12 : firstn 12 js = zb (ct_genstr_null (ts_ms (sc_ts x))) ++ [Z_to_bv 8 0]).
  { apply (bytes_at_detP m2 (f + 32)); [exact BY1| exact BZ|]. destruct JS1 as [[WF1 _] _]. cbn [cells_wf cell_wf] in WF1. destruct WF1 as [WF1 _]. rewrite WF1.
    rewrite length_app. unfold zb. rewrite length_map. cbn [length]. clear - OL. lia. }
  assert (HGS : rw_cells ctasegs m2 (f + 32) [CB 20%nat (zb (genstr (sc_ts x)) ++ Z_to_bv 8 0 :: skipn 12 js)]).
  { rewrite <- (genstr_none _ GA). rewrite <- (firstn_skipn 12 js) in JS. rewrite E12, <- app_assoc in JS. cbn [app] in JS. exact JS. }
  clear JS JS2 JS1 BY1 E12.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  apply evt_done. eapply K.
  - split; [exact HEAP2|]. split; [exact LIVE|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_trans; [eapply agree_on_mono; [exact AG1| intros a [Ha _]; exact (STK1 a (LBI' a Ha))]|].
             eapply agree_on_mono; [exact AG2|]. intros a [Ha _]. exact (CL2 a Ha). }
    split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|].
    split; [| exact LBI]. eapply sct_repA_agree; [exact REP1|]. eapply agree_on_mono; [exact AG2|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (CL2 a C).
  - split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB].
  - exact HG.
  - exact HGS.
  - eapply uw_chain_agreeP; [exact AG2| exact UW1|]. intros a _ Ha. split; [left; clear - Ha SPAH; lia| clear - Ha G3 CEILu LO' SPAL SPAH; lia].
Qed.

(* [comment removed for export] *)
Lemma sc_ts4ok : forall {X : Type} (k : option bptr -> aprog bptr X) (Q : X -> rts RTS -> machine_state -> Prop)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg pd : bptr) (G D : Z) (c24 : cell) (t : tm6) (junk4 : list (bv 8)) (q : bptr),
  sc_invL [(pd, D, 20); (pg, G, 24)] ((q, f + 32, 20) :: LB) c24 lv Σc m -> sc_bioL m nw -> 2 <= rt_credit RTS Σc ->
  gentime_adj (sc_ts x) = Some t -> pg <> pd ->
  rw_cells ctasegs m G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0) ->
  rw_cells ctasegs m D [CB 20%nat (zb (gen15 t) ++ Z_to_bv 8 0 :: junk4)] ->
  rw_cells ctasegs m (f + 32) [CB 20%nat (zb (genstr (sc_ts x)) ++ [Z_to_bv 8 0])] ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall p' Σ' ms', ~ In p' (map blk_id (((pd, D, 20) :: (pg, G, 24) :: OW) ++ (q, f + 32, 20) :: LB)) ->
     gentime_setstr_postA (Z_to_bv 64 0x33807c) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB)
                          Σc ((pd, D, 20) :: (pg, G, 24) :: OW) ((q, f + 32, 20) :: LB) G pd lo (sc_ts x) m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (AReallocI pd 19 k) Σc Q
    (MS (mkR (Z_to_bv 64 0x33807c) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x270a34) fc None m (seg_rom ctasegs)).
Proof.
  intros until q. intros INV BIO CR2 GA NE HG HD HGS UW K. pose proof (sc_rs _ _ _ _ _ _ INV) as RS.
  destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  assert (MC0 : mcost 19 = 0) by reflexivity.
  change (Z_to_bv 64 0x270a34) with (Z_to_bv 64 ASN1_GENERALIZEDTIME_SET_STRING_A).
  eapply (gentime_setstr_okA REA) with (lo := lo) (gb := pg) (dp := pd) (qs := q) (G := G) (D := D) (fq := f) (ts := sc_ts x) (t := t) (djunk := zb (gen15 t) ++ Z_to_bv 8 0 :: junk4) (ras := ras1);
    rewrite ?ESPA; try reflexivity.
  - exact HEAP.
  - exact ST.
  - exact CEIL.
  - unfold GENTIME_SETSTR_STACK_A, T2T_STACK_A, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact RS.
  - clear - FLEN. lia.
  - rewrite MC0. clear - CR2. lia.
  - right; left; reflexivity.
  - left; reflexivity.
  - exact NE.
  - exact HG.
  - exact HD.
  - exact HFR.
  - left; reflexivity.
  - exact HGS.
  - exact GA.
  - exact TSR.
  - exact UW.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_SCT_print_34c4a0 CTX).
  - exact K.
Qed.

(* [comment removed for export] *)
Lemma sc_ts4fail : forall (Q : config -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg : bptr) (G : Z) (c24 : cell) (gtail : list (bv 8)) (q : bptr),
  sc_invL [(pg, G, 24)] ((q, f + 32, 20) :: LB) c24 lv Σc m -> sc_bioL m nw -> 2 <= rt_credit RTS Σc ->
  gentime_adj (sc_ts x) = None -> 0 < G < 2^64 ->
  rw_cells ctasegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  rw_cells ctasegs m (f + 32) [CB 20%nat (zb (genstr (sc_ts x)) ++ Z_to_bv 8 0 :: gtail)] ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS),
     sc_invL [(pg, G, 24)] ((q, f + 32, 20) :: LB) c24 (rt_live RTS Σc') Σc' m' -> sc_bioL m' nw -> rt_credit RTS Σc - 2 <= rt_credit RTS Σc' -> rt_live RTS Σc' = rt_live RTS Σc ->
     rw_cells ctasegs m' G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
     uw_chain USTACK_TOP m' spa (bv_unsigned sp) ras1 ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x247034) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR (Z_to_bv 64 0x33807c) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x270a34) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until q. intros INV BIO CR2 GA GR HG HGS UW K. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. unfold SEGTOP_A in G4.
  assert (PR : printable (sc_ts x) = false) by (unfold printable; rewrite GA; reflexivity).
  assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  pose proof (AH_ow_off_fr Σc ((pg, G, 24) :: OW) ((q, f + 32, 20) :: LB) m f 1%nat (pg, G, 24) HEAP HFR (or_introl eq_refl)) as OFG. unfold off_fr in OFG. change (fs_size 1) with 128 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (((pg, G, 24) :: OW) ++ (q, f + 32, 20) :: LB) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact (LBI _ Hb)]. }
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  eapply (gentime_setstr_failA) with (lo := lo) (OW := (pg, G, 24) :: OW) (LB := (q, f + 32, 20) :: LB) (bs := (q, f + 32, 20)) (G := G) (GS := f + 32) (ts := sc_ts x) (gtail := gtail);
    rewrite ?ESPA; try reflexivity.
  - exact HEAP.
  - exact ST.
  - exact CEIL.
  - unfold GENTIME_SETSTR_STACK_A, T2T_STACK_A, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI.
  - clear - FLEN. lia.
  - exact CR2.
  - apply in_or_app. right. left. reflexivity.
  - exact HGS.
  - exact PR.
  - exact TSR.
  - clear - GR; lia.
  - intros Σ' m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' HEAP' CR' LIVE' ST' MI' AG'.
    rewrite (ret_pc_even 0x33807c) by (clear; lia). unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AG') in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG') in FRH; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG') in HB; [| intros xa Hxa; cbn in Hxa; right; right; exists (pb, out, 128); split; [apply in_or_app; left; right; exact HBIN| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG') in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; right; right; exists (pg, G, 24); split; [apply in_or_app; left; left; reflexivity| cbn; clear - Hxa; lia]].
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. brc. zstep. zstep.
    apply evt_done. eapply K.
    + split; [exact HEAP'|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. exact (LBI' a Ha). }
      split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|].
      split; [| exact LBI]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG'|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (LBI' a C).
    + split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB].
    + clear - CR'; lia.
    + exact LIVE'.
    + exact HG.
    + eapply uw_chain_agreeP; [exact AG'| exact UW|]. intros a _ Ha. left. clear - Ha SPAH; lia.
Qed.

(* [comment removed for export] *)
Lemma sc_ts5ok : forall (Q : config -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg pd' : bptr) (G D' : Z) (c24 : cell) (t : tm6) (LBc : list block),
  sc_invL [(pd', D', 19); (pg, G, 24)] LBc c24 lv Σc m -> sc_bioL m nw -> 5 <= rt_credit RTS Σc ->
  gentime_adj (sc_ts x) = Some t ->
  rw_cells ctasegs m G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D' 0) -> rw_cells ctasegs m D' [CB 19%nat (zb (genstr (sc_ts x)))] ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall b, In b LBc -> In b LB \/ b = (fst (fst b), f + 32, 20)) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS) (nw' : Z),
     sc_invL [(pd', D', 19); (pg, G, 24)] LBc c24 (rt_live RTS Σc') Σc' m' -> sc_bioL m' nw' -> rt_credit RTS Σc - 5 <= rt_credit RTS Σc' -> rt_live RTS Σc' = rt_live RTS Σc ->
     rw_cells ctasegs m' G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D' 0) ->
     uw_chain USTACK_TOP m' spa (bv_unsigned sp) ras1 ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x247034) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR (Z_to_bv 64 0x33807c) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x33807c) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until LBc. intros INV BIO CR5 GA HG HD UW HLB K. pose proof INV as INV'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSR & _).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. unfold SEGTOP_A in G4.
  assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  pose proof (AH_ow_off_fr Σc ((pd', D', 19) :: (pg, G, 24) :: OW) LBc m f 1%nat (pg, G, 24) HEAP HFR (or_intror (or_introl eq_refl))) as OFG. unfold off_fr in OFG. change (fs_size 1) with 128 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  pose proof (AH_range_gen _ _ _ _ (pg, G, 24) HEAP (in_or_app ((pd', D', 19) :: (pg, G, 24) :: OW) LBc (pg, G, 24) (or_introl (or_intror (or_introl eq_refl))))) as (BG0 & _ & _ & BGC & _). cbn [blk_addr blk_size fst snd] in BG0, BGC. unfold BnHeapA.ACEIL in BGC.
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (((pd', D', 19) :: (pg, G, 24) :: OW) ++ LBc) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; right; exact Hb| right; exact (LBI _ Hb)]. }
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. brc. zstep. zstep. zstep.
  apply evt_done. eapply cps_step_rt.
  { pose proof (gentime_printA PFC) as HP.
    eapply HP with (lo := lo) (OW := ((pd', D', 19) :: (pg, G, 24) :: OW)) (LB := LBc) (gb := pg) (pd := pd') (pb := pb) (G := G) (D := D') (out := out) (pv := pv) (nw := nw) (ts := sc_ts x) (t := t);
      clear HP; rewrite ?ESPA; try reflexivity.
    - exact HEAP.
    - exact ST.
    - exact CEIL.
    - unfold GENTIME_PRINT_STACK_A, BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI.
    - exact FLEN.
    - exact CR5.
    - right; left; reflexivity.
    - exact HG.
    - left; reflexivity.
    - exact HD.
    - exact GA.
    - exact TSR.
    - right; right; exact HBIN.
    - exact HB.
    - exact NW.
    - intros Σ' m' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' r Hr HEAP' CR' LIVE' ST' MI' AP' HB'.
      apply cps_post. intros c Hc. exists Σ'. split; [| exact LIVE'].
      eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
      instantiate (1 := fun Σ' ms0 => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' m' r, ms0 = MS (mkR (Z_to_bv 64 0x33808c) (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) u3 u4 u5 u6) F' (Z_to_bv 64 0x33808c) fc' None m' (seg_rom ctasegs)
                /\ 0 <= r <= 28 /\ AHEAP Σ' ((pd', D', 19) :: (pg, G, 24) :: OW) LBc m' /\ rt_credit RTS Σc - 5 <= rt_credit RTS Σ' /\ stk ctasegs m' lo spa /\ mem_inv ctasegs m' /\ apres_ex LBc ((pd', D', 19) :: (pg, G, 24) :: OW) spa [(out, out + BIO_SIZE)]%Z m m'
                /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv (nw + r))).
      cbv beta. do 14 eexists. exists F', fc', m', r. rewrite (ret_pc_even 0x33808c) by (clear; lia). split; [reflexivity|].
      split; [exact Hr|]. split; [exact HEAP'|]. split; [exact CR'|]. split; [exact ST'|]. split; [exact MI'|]. split; [exact AP'| exact HB']. }
  intros Σ6 ms6 PO6 LIVE6. cbv beta in PO6.
  destruct PO6 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F6 & fc6 & m6 & r & -> & Hr & HEAP6 & CR6 & ST6 & MI6 & AP6 & HB6).
  unfold apres_ex, BIO_SIZE in AP6.
  assert (NEG : G + 24 <= out \/ out + 128 <= G).
  { assert (HB' : In (pb, out, 128) (((pd', D', 19) :: (pg, G, 24) :: OW) ++ LBc)) by (apply in_or_app; left; right; right; exact HBIN).
    assert (HG' : In (pg, G, 24) (((pd', D', 19) :: (pg, G, 24) :: OW) ++ LBc)) by (apply in_or_app; left; right; left; reflexivity).
    assert (NE : blk_id (pg, G, 24) <> blk_id (pb, out, 128)).
    { cbn [blk_id fst]. intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. cbn [map app blk_id fst] in ND.
      apply List.NoDup_cons_iff in ND as [_ ND]. apply List.NoDup_cons_iff in ND as [NG _]. apply NG. rewrite map_app. apply in_or_app. left. rewrite E. apply in_map_iff. exists (pb, out, 128). split; [reflexivity| exact HBIN]. }
    pose proof (AH_disjoint_gen _ _ _ _ _ _ HEAP HG' HB' NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. exact DJ. }
  apply (rw_cells_agree _ _ _ _ _ AP6) in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia| split; [clear - Hxa OBCu CEILu LO' SPAL; lia| exact I]]].
  apply (rw_cells_agree _ _ _ _ _ AP6) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| split; [clear - Hxa OBCu CEILu LO' SPAL SPAH; lia| exact I]]].
  apply (rw_cells_agree _ _ _ _ _ AP6) in HG; [| intros xa Hxa; unfold asn1_string_cells in Hxa; cbn in Hxa; cbn [outside fst snd]; split; [right; right; exists (pg, G, 24); split; [apply in_or_app; left; right; left; reflexivity| cbn; clear - Hxa; lia]| split; [clear - Hxa NEG; lia| exact I]]].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  apply evt_done. eapply K.
  - split; [exact HEAP6|]. split; [reflexivity|]. split; [exact MI6|]. split; [exact ST6|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AP6|]. intros a [Ha Ho]. split; [exact (LBI' a Ha)| exact Ho]. }
    split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|].
    split; [| exact LBI]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AP6|]. intros a Ha. destruct (SCTA a Ha) as (_ & O & C). split; [exact (LBI' a C)| exact O].
  - instantiate (1 := (nw + r) mod 2 ^ 64). split; [apply Z.mod_pos_bound; clear; lia| rewrite bio_null_cells_mod; exact HB6].
  - clear - CR6; lia.
  - exact LIVE6.
  - exact HG.
  - eapply uw_chain_agreeP; [exact AP6| exact UW|]. intros a _ Ha. cbn [outside fst snd]. split; [left; clear - Ha SPAH; lia| split; [clear - Ha OBCu CEILu LO' SPAL SPAH; lia| exact I]].
Qed.

(* [comment removed for export] *)
Lemma sc_gtfree_dyn : forall {X : Type} (k : aprog bptr X) (Q : X -> rts RTS -> machine_state -> Prop)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg pd' : bptr) (G D' : Z) (c24 : cell) (LBc : list block),
  sc_invL [(pd', D', 19); (pg, G, 24)] LBc c24 lv Σc m -> sc_bioL m nw -> pg <> pd' ->
  rw_cells ctasegs m G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D' 0) ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall Σ' ms', vfree_postA (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB)
                    Σc (lb_remove pg (lb_remove pd' ((pd', D', 19) :: (pg, G, 24) :: OW))) LBc lo m (fun _ => True) Σ' ms' ->
     implAp k Σ' Q ms') ->
  implAp (AFree pd' (AFree pg k)) Σc Q
    (MS (mkR (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x247034) fc None m (seg_rom ctasegs)).
Proof.
  intros until LBc. intros INV BIO NE HG UW K. pose proof (sc_cs _ _ _ _ _ _ INV) as CS.
  destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). facts.
  pose proof (AH_range_gen _ _ _ _ (pg, G, 24) HEAP (in_or_app ((pd', D', 19) :: (pg, G, 24) :: OW) LBc (pg, G, 24) (or_introl (or_intror (or_introl eq_refl))))) as (BG0 & _ & _ & BGC & _).
  cbn [blk_addr blk_size fst snd] in BG0, BGC. unfold BnHeapA.ACEIL in BGC. unfold asn1_string_cells, MallocRep.wz in HG.
  pose proof (munch_refl [(spa - 16, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. do 2 zstep. release_frame FR ST spa. zstep. zstep.
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σc ((pd', D', 19) :: (pg, G, 24) :: OW) LBc m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (((pd', D', 19) :: (pg, G, 24) :: OW) ++ LBc) spa) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  apply evt_done. change (Z_to_bv 64 2246688) with (wz ASN1_STRING_FREE_A).
  eapply (ASN1_STRING_free_dyn_walkA) with (lo := lo) (OW := ((pd', D', 19) :: (pg, G, 24) :: OW)) (LB := LBc) (pblk := pg) (pdata := pd') (A := G) (D := D') (alloc := 19) (len := 19) (ty := V_ASN1_GENERALIZEDTIME) (ras := ras1);
    rewrite ?ESPA; try reflexivity.
  - exact HEAP1.
  - exact ST.
  - exact CEIL.
  - unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI1.
  - assert (HPl : forall a, libw a -> aclient_addr (((pd', D', 19) :: (pg, G, 24) :: OW) ++ LBc) spa a).
    { intros a Ha. destruct (proj1 (libw_clientP a Ha)) as [H|[H|(b & Hb & Hr)]]; [left; exact H| right; left; exact H| right; right; exists b; split; [| exact Hr]].
      apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; right; exact Hb| right; exact (LBI _ Hb)]. }
    exact (crypto_statics_agree _ m m1 AG1 HPl CS).
  - right; left; reflexivity.
  - left; reflexivity.
  - exact NE.
  - exact HG.
  - eapply uw_chain_agreeP; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact UW|]. intros a _ Ha. cbn [outside fst snd]. clear - Ha SPAH; lia.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_tail _ _ _ E_ASN1_GENERALIZEDTIME_free_24a184 (uk_ctx_call _ _ _ _ E_SCT_print_34c4bc CTX)).
  - intros Σ' ms' PO. apply (K Σ' ms').
    unfold vfree_postA in PO |- *. rewrite ?ESPA in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & -> & MI' & ST' & AP' & CR' & HEAP' & _).
    do 15 eexists. exists F', fc', m'. rewrite ?ESPA. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split; [| split; [exact CR'| split; [exact HEAP'| exact I]]].
    unfold apres in AP' |- *. eapply agree_on_trans; [| exact AP']. eapply agree_on_mono; [exact AG1|].
    intros a Ha. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left| right; exact Hb]. apply lb_remove_incl in Hb. apply lb_remove_incl in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma sc_gtfree_nodata : forall {X : Type} (k : aprog bptr X) (Q : X -> rts RTS -> machine_state -> Prop)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (pg : bptr) (G : Z) (c24 : cell) (LBc : list block),
  sc_invL [(pg, G, 24)] LBc c24 lv Σc m -> sc_bioL m nw ->
  rw_cells ctasegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 ->
  (forall Σ' ms', vfree_postA (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB)
                    Σc (lb_remove pg ((pg, G, 24) :: OW)) LBc lo m (fun _ => True) Σ' ms' ->
     implAp k Σ' Q ms') ->
  implAp (AFree pg k) Σc Q
    (MS (mkR (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 G) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x247034) fc None m (seg_rom ctasegs)).
Proof.
  intros until LBc. intros INV BIO HG UW K. pose proof (sc_cs _ _ _ _ _ _ INV) as CS.
  destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). facts.
  pose proof (AH_range_gen _ _ _ _ (pg, G, 24) HEAP (in_or_app ((pg, G, 24) :: OW) LBc (pg, G, 24) (or_introl (or_introl eq_refl)))) as (BG0 & _ & _ & BGC & _).
  cbn [blk_addr blk_size fst snd] in BG0, BGC. unfold BnHeapA.ACEIL in BGC. unfold asn1_string_cells, MallocRep.wz in HG.
  pose proof (munch_refl [(spa - 16, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. do 2 zstep. release_frame FR ST spa. zstep. zstep.
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σc ((pg, G, 24) :: OW) LBc m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (((pg, G, 24) :: OW) ++ LBc) spa) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  apply evt_done. change (Z_to_bv 64 2246688) with (wz ASN1_STRING_FREE_A).
  eapply (ASN1_STRING_free_nodata_walkA) with (lo := lo) (OW := ((pg, G, 24) :: OW)) (LB := LBc) (pblk := pg) (A := G) (len := 0) (ty := V_ASN1_GENERALIZEDTIME) (ras := ras1);
    rewrite ?ESPA; try reflexivity.
  - exact HEAP1.
  - exact ST.
  - exact CEIL.
  - unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI1.
  - assert (HPl : forall a, libw a -> aclient_addr (((pg, G, 24) :: OW) ++ LBc) spa a).
    { intros a Ha. destruct (proj1 (libw_clientP a Ha)) as [H|[H|(b & Hb & Hr)]]; [left; exact H| right; left; exact H| right; right; exists b; split; [| exact Hr]].
      apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact (LBI _ Hb)]. }
    exact (crypto_statics_agree _ m m1 AG1 HPl CS).
  - left; reflexivity.
  - exact HG.
  - eapply uw_chain_agreeP; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact UW|]. intros a _ Ha. cbn [outside fst snd]. clear - Ha SPAH; lia.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_tail _ _ _ E_ASN1_GENERALIZEDTIME_free_24a184 (uk_ctx_call _ _ _ _ E_SCT_print_34c4bc CTX)).
  - intros Σ' ms' PO. apply (K Σ' ms').
    unfold vfree_postA in PO |- *. rewrite ?ESPA in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & -> & MI' & ST' & AP' & CR' & HEAP' & _).
    do 15 eexists. exists F', fc', m'. rewrite ?ESPA. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split; [| split; [exact CR'| split; [exact HEAP'| exact I]]].
    unfold apres in AP' |- *. eapply agree_on_trans; [| exact AP']. eapply agree_on_mono; [exact AG1|].
    intros a Ha. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left| right; exact Hb]. apply lb_remove_incl in Hb. exact Hb.
Qed.


(* [comment removed for export] *)
Lemma ts_list_back : forall (pg pd' : bptr) (G D' : Z),
  ~ In pg (map blk_id OW) -> ~ In pd' (map blk_id OW) -> pg <> pd' ->
  lb_remove pg (lb_remove pd' ((pd', D', 19) :: (pg, G, 24) :: OW)) = OW.
Proof.
  intros pg pd' G D' NG ND NE.
  rewrite lb_remove_cons. cbn [blk_id fst]. rewrite bptr_eqb_refl.
  rewrite lb_remove_cons. cbn [blk_id fst]. rewrite (bptr_eqb_neq pg pd' NE). rewrite (lb_remove_notin pd' OW ND).
  rewrite lb_remove_cons. cbn [blk_id fst]. rewrite bptr_eqb_refl. exact (lb_remove_notin pg OW NG).
Qed.

(* [comment removed for export] *)
Lemma sc_ts6 : forall (Q : config -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x24 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (q : bptr) (c24 : cell),
  sc_invL [] ((q, f + 32, 20) :: LB) c24 lv Σc m -> sc_bioL m nw ->
  (forall (m' : mem),
     sc_invL [] LB c24 lv Σc m' -> sc_bioL m' nw -> agree_on (fun a => ~ (shad f <= a < shad f + 16)) m m' ->
     cps ctasegs (ASTA RTS Σc PMc (eq
       (MS (mkR (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
           Fc (Z_to_bv 64 0x3380a4) fc None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR (Z_to_bv 64 0x338094) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x338094) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until c24. intros INV BIO K. destruct INV as (HEAPq & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. unfold SEGTOP_A in G4.
  (* [comment removed for export] *)
  pose proof HEAPq as HEAP. eapply (frame_obj_close) in HEAP; [| exact HFR| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
  (* [comment removed for export] *)
  destruct (AH_fr_wr _ _ _ _ f 1%nat HEAP HFR) as [_ WS]. change (fs_size 1 / 8) with 16 in WS.
  destruct (wr_at_rw_CB m (shad f) _ WS ltac:(clear; lia)) as (js & FRS). change (Z.to_nat 16) with 16%nat in FRS. clear WS.
  apply (rw_cells_split_CB ctasegs _ _ [] 16 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. clear - G1 G3 G4 Cq3. unfold BnHeapA.ACEIL in *. Z.div_mod_to_equations. lia. }
  pose proof (AH_offsh _ _ _ _ _ HEAP3 (in_or_app _ _ _ (or_introl HBIN))) as OFFB. cbn [blk_addr blk_size fst snd] in OFFB. unfold BIO_SIZE, SHLO, SHHI in OFFB.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  lazymatch type of HB with ?T => change (frozen T) in HB end.
  pose proof (munch_refl [(spa, spa); (f, f + 0); (shad f, shad f + 16)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. sbstep. sbstep. sbstep.
  unfold frozen in HB.
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in HB; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa OFFB SHR; repeat split; try exact I; lia].
  assert (OFFL : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
  assert (HEAP1 : AHEAP Σc OW LB m1).
  { eapply (fr3_heap Σc OW LB m m1 f 1%nat spa spa 0 16 HFR HEAP MU1 WM1);
      [unfold BnHeapA.ACEIL; clear - CEILu LO'; lia| unfold USTACK_TOP; clear - TOPu SPAH; lia| change (fs_size 1) with 128; clear; lia| change (fs_size 1) with 128; clear; lia| exact OFFL]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) spa) m m1).
  { eapply (fr3_agree Σc OW LB m m m1 f 1%nat spa spa 0 16 (OW ++ LB) HEAP MU1 GEO);
      [change (fs_size 1) with 128; clear; lia| change (fs_size 1) with 128; clear; lia| unfold BnHeapA.ACEIL; clear - CEILu LO'; lia| clear; lia| intros b Hb; exact Hb| exact FRESH]. }
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) spa a).
  { intros a [Ha|[Ha|Hb]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Hb]. }
  apply evt_done. eapply (K m1).
  - split; [exact HEAP1|]. split; [exact LIVE|]. split; [exact MI1|]. split; [exact ST1|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AG1|]. intros a [Ha _]. exact (LBI' a Ha). }
    split; [assumption|]. split; [exact SZ|]. split; [assumption|].
    split; [| intros b Hb; exact Hb]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG1|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (LBI' a C).
  - split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB].
  - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. clear - Ha. repeat split; try exact I; lia.
Qed.

End TS.
