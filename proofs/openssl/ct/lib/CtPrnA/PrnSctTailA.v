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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtObjA Require Import ObjTabA ObjLookupStmtA W_nid2objA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApObjRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnFmtA W_bio_hex_stringA PrnSctFmtA PrnSctKitA PrnStmtA W_sk_leavesA.
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
Lemma sig_nid_cases : forall h g, sig_nid 0 h g <> NID_undef -> sig_nid 0 h g = NID_ecdsa_with_SHA256 \/ sig_nid 0 h g = NID_sha256WithRSAEncryption.
Proof.
  intros h g NZ. unfold sig_nid in *. rewrite Z.eqb_refl in *. cbn [andb] in *.
  destruct (h =? 4); [| exfalso; apply NZ; reflexivity]. destruct (g =? 3); [left; reflexivity|]. destruct (g =? 1); [right; reflexivity| exfalso; apply NZ; reflexivity].
Qed.
Lemma static_obj_794 : static_obj_ok NID_ecdsa_with_SHA256 17.
Proof. exists 733, [42; 134; 72; 206; 61; 4; 3; 2]. split; [unfold NUM_OBJ; lia|]. split; [vm_compute; reflexivity| discriminate]. Qed.
Lemma static_obj_668 : static_obj_ok NID_sha256WithRSAEncryption 23.
Proof. exists 944, [42; 134; 72; 134; 247; 13; 1; 1; 11]. split; [unfold NUM_OBJ; lia|]. split; [vm_compute; reflexivity| discriminate]. Qed.

Definition LN794_A : Z := 0x5f640.      (* [comment removed for export] *)
Definition LN668_A : Z := 0x5d840.      (* [comment removed for export] *)
Definition ln_addrA (nid : Z) : Z := if nid =? NID_ecdsa_with_SHA256 then LN794_A else LN668_A.
Definition ln_lenA (nid : Z) : Z := if nid =? NID_ecdsa_with_SHA256 then 17 else 23.

Lemma ln794_roA : ro_bytes ctasegs LN794_A (zb LNS_794 ++ Z_to_bv 8 0 :: zb [0; 0; 0; 0; 0; 0; 0]). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma ln668_roA : ro_bytes ctasegs LN668_A (zb LNS_668 ++ Z_to_bv 8 0 :: zb [0; 0; 0; 0; 0; 0; 0]). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ln_vargA : forall OW LB m nid, nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption ->
  vargA_ok OW LB m (Z_to_bv 64 (ln_addrA nid)) (PA_s (ln_str nid)).
Proof.
  intros OW LB m nid Hn. unfold vargA_ok, ln_addrA, ln_str, LN794_A, LN668_A, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption in *.
  destruct Hn as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - rewrite (unsigned_lit 390720) by (clear; lia). exists (zb [0; 0; 0; 0; 0; 0; 0]). change (zlength LNS_794) with 17. change (zlength (zb [0; 0; 0; 0; 0; 0; 0])) with 7.
    split; [unfold LNS_794; repeat constructor|]. split; [clear; lia|]. split; [clear; cbn; lia|].
    right. split; [clear; lia|]. split; [cbv; discriminate|]. split; [exact ln794_roA|].
    intros AR' Σ' m' H'. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x5f640, 18, 64)); [exact (@AH_art AR' _ _ _ _ H')| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia].
  - rewrite (unsigned_lit 383040) by (clear; lia). exists (zb [0; 0; 0; 0; 0; 0; 0]). change (zlength LNS_668) with 23. change (zlength (zb [0; 0; 0; 0; 0; 0; 0])) with 7.
    split; [unfold LNS_668; repeat constructor|]. split; [clear; lia|]. split; [clear; cbn; lia|].
    right. split; [clear; lia|]. split; [cbv; discriminate|]. split; [exact ln668_roA|].
    intros AR' Σ' m' H'. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x5d840, 24, 64)); [exact (@AH_art AR' _ _ _ _ H')| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia].
Qed.
Lemma vfmtA_C10_ln : forall nid, nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption -> vfmtA_ok A_C10_A FMT_C10 [PA_s (ln_str nid)] (ln_str nid).
Proof. intros nid [-> | ->]; apply vfmtA_C10; cbv; discriminate. Qed.
Lemma zlength_ln_str : forall nid, nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption -> zlength (ln_str nid) = ln_lenA nid.
Proof. intros nid [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ln_cellA : forall (AR : CtKitA.ARun.ARun) Σ OW LB m nid, @BnHeapA.AHEAP AR Σ OW LB m -> nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption ->
  ro_cells ctasegs m (A_NID_OBJS_VA + 40 * nid + 8) [C8 (Z_to_bv 64 (ln_addrA nid))].
Proof.
  intros AR Σ OW LB m nid HEAP Hn. pose proof (af_relro _ (@ar_AF AR) Σ m (@AH_art AR _ _ _ _ HEAP)) as R.
  unfold ln_addrA, LN794_A, LN668_A, A_NID_OBJS_VA, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption in *.
  destruct Hn as [-> | ->]; cbn [Z.eqb Pos.eqb]; (apply (relro_ro_cells m _ _ R); [cbn; tauto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| vm_compute; reflexivity]).
Qed.

Section TL.
Context {AR : CtKitA.ARun.ARun} {UK : UnwindKit} {BE : BnEdges}.          (* [comment removed for export] *)
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.

Variables (sp : word) (spa f lo : Z) (g : nat) (OW LB : list block) (pb : bptr) (out pv : Z) (adr : bptr -> Z) (x : sctr bptr).
Variables (m3 : mem) (Σ1 : rts RTS) (vra v8 gp : word) (j0 j8 j16 j32 j40 junk : list (bv 8)).

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

Local Notation sc_invL := (sc_inv sp spa f lo g OW LB out adr x m3 vra v8 j0 j8 j16 j32 j40 junk).
Local Notation sc_bioL := (sc_bio out pv).

Local Ltac facts :=
  pose proof (sc_factsA sp OW LB pb out adr x m3 Σ1 HEAP3 HBIN REP3 NPB) as (OB0 & OBC & Cq1 & Cq2 & Cq3 & SCTA); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3;
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  pose proof LO as LO'; unfold SC_BODY_STACK_A, RT_STACK in LO';
  pose proof CEIL as CEILu; unfold BnHeapA.ACEIL in CEILu; pose proof TOP as TOPu; unfold USTACK_TOP in TOPu;
  pose proof OBC as OBCu; unfold BnHeapA.ACEIL in OBCu;
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0 SPAL SPAH; lia).

(* [comment removed for export] *)
Lemma sc_nid2ln : forall (Q : config -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x23 x24 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (c24 : cell) (nid used budget : Z),
  sc_invL [] LB c24 lv Σc m -> sc_bioL m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used -> used + 1 <= budget -> budget <= rt_credit RTS Σ1 ->
  nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS),
     sc_invL [] LB c24 lv Σc' m' -> sc_bioL m' nw -> rt_credit RTS Σ1 - (used + 1) <= rt_credit RTS Σc' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR (Z_to_bv 64 0x338150) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 (ln_addrA nid)) a1' a2' a3' a4' a5' a6' a7'
                x18 (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x338150) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR (Z_to_bv 64 0x338150) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 nid) a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x21f7b4) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros INV BIO CR U0 U1 CRED Hn K. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  assert (NR : 0 < nid < 1503) by (unfold NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption in *; clear - Hn; lia).
  assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof (munch_refl [(spa - 32, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. zstep. zstep. zstep. zstep. zstep.
  match goal with MUx : munch _ m ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    destruct (shb_cells_munch _ _ _ _ _ (AH_shb _ _ _ _ HEAP) MUx ltac:(intros xx Hx; cbn [outside fst snd]; clear - Hx Cq1 CEILu LO'; unfold BnHeapA.ACEIL in *; split; [lia| exact I])) as [SHB1 SHB2] end.
  zstep.
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end.
  assert (ESP1 : bv_unsigned (Z_to_bv 64 (spa + -32)) = spa + -32) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0 SPAL SPAH; lia).
  assert (HEAP1 : AHEAP Σc OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (STK1 : forall a, aclient_addr (OW ++ LB) spa a -> outside [(spa - 32, spa)]%Z a).
  { intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) spa a).
  { intros a [Ha|[Ha|Hb]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Hb]. }
  apply evt_done. eapply cps_step_rt.
  { pose proof (@OBJ_nid2obj_walkA AR) as HP. unfold OBJ_nid2obj_stmtA in HP.
    eapply HP with (lo := lo) (OW := OW) (LB := LB) (n := nid) (lnlen := ln_lenA nid); clear HP; rewrite ?ESP1; try reflexivity.
    - exact HEAP1.
    - exact ST1.
    - exact CEIL.
    - unfold N2O_STACK_A, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI1.
    - clear - FLEN. lia.
    - clear - CR U0 U1 CRED. lia.
    - unfold NUM_NID; clear - NR; lia.
    - unfold ln_lenA. destruct Hn as [-> | ->]; [exact static_obj_794| exact static_obj_668]. }
  intros Σ2 msP PO LEN2. unfold lk_postA in PO. rewrite ?ESP1 in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & HEAP2 & LIVE2 & CR2).
  rewrite (ret_pc_even 0x21f7d8) by (clear; lia). unfold MallocRep.wz.
  assert (AG2' : agree_on (aclient_addr (OW ++ LB) spa) m1 m2) by (eapply agree_on_mono; [exact AG2|]; intros a [Ha|Hb]; [left; clear - Ha; lia| right; exact Hb]).
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2') in FRL; [| intros xa Hxa; rewrite SZL in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2') in FRH; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2') in HB; [| intros xa Hxa; cbn in Hxa; right; right; exists (pb, out, 128); split; [apply in_or_app; left; exact HBIN| cbn; clear - Hxa; lia]].
  (* [comment removed for export] *)
  assert (ACCO : acc ctasegs m2 (A_NID_OBJS_VA + 40 * nid) 40).
  { eapply (af_lib_acc_lit _ (@ar_AF AR) Σ2 m2 A_NIDOBJS_G); [exact (AH_art _ _ _ _ HEAP2)| exact A_NIDOBJS_G_memb| unfold A_NID_OBJS_VA; cbn; clear - NR; lia| unfold A_NID_OBJS_VA, NUM_NID in *; cbn; clear - NR; lia]. }
  pose proof (ln_cellA AR Σ2 OW LB m2 nid HEAP2 Hn) as RLN. unfold A_NID_OBJS_VA in *.
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU2. assert (OFFW : offshW ([] : list (Z * Z))) by exact I.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. if_cases Kz; zify_cond Kz; [exfalso; clear - Kz NR; lia|]. try clear Kz.
  zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. release_frame FR ST2 spa. zstep. zstep.
  try rewrite (ret_pc_even 0x338150) by (clear; lia).
  apply evt_done. eapply K.
  - split; [exact HEAP2|]. split; [rewrite LIVE2; exact LIVE|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a [Ha _]; exact (STK1 a (LBI' a Ha))]|].
             eapply agree_on_mono; [exact AG2'|]. intros a [Ha _]. exact (LBI' a Ha). }
    split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|].
    split; [| exact LBI]. eapply sct_repA_agree; [exact REP|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a Ha; destruct (SCTA a Ha) as (_ & _ & C); exact (STK1 a (LBI' a C))]|].
    eapply agree_on_mono; [exact AG2'|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (LBI' a C).
  - split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB].
  - clear - CR CR2. lia.
Qed.
Local Notation at_exitL := (at_exit sp spa f lo g OW LB out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk).

(* [comment removed for export] *)
Lemma sc_tail2 : forall (Q : config -> Prop) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x24 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (used budget : Z),
  sc_version x = 0 ->
  sc_invL [] LB (C8 (Z_to_bv 64 f)) lv Σc m -> sc_bioL m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used ->
  used + 10 + HX_CRED (sc_siglen x) <= budget -> budget <= rt_credit RTS Σ1 ->
  at_exitL Q (C8 (Z_to_bv 64 f)) lv budget ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x338120) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros V0 INV BIO CR U0 UB CRED KX. pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (HSIN & AL16s & CELLS & _ & _ & A3 & _ & _ & VR & NID & HR & GR & _ & _ & _ & SL & _).
  assert (HXN : 0 <= HX_CRED (sc_siglen x)) by (unfold HX_CRED, sc_siglen; destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0; lia| clear; lia]).
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply (sc_printf PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
      (nw := nw) (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (A := A_C9_A) (fmt := FMT_C9) (args := [PA_i 8; PA_s []]) (o := O_C9) (retpc := 0x33813c) (used := used) (budget := budget);
    first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CR| exact U0| exact CRED| exact vfmtA_C9| idtac];
    [clear - UB HXN; lia| rewrite zlength_O_C9; clear; lia
    | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fcb fcb m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW LBI SZ.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof REP as (_ & _ & CELLS & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN) as (BS0 & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BS0, BSC, BSI. unfold BnHeapA.ACEIL in BSC. unfold SCT_SIZE in BSC, BSI.
  lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS. rewrite V0 in CELLS. change (CtSctP.SctRep.u32 0) with 0 in CELLS.
  (* [comment removed for export] *)
  pose proof (proj1 CELLS) as ROS.
  lazymatch type of ROS with cells_at _ _ _ (?c0 :: ?rest) =>
    pose proof (proj1 (proj1 (OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA.ApWalkTac.rw_cells_app m (adr (sc_blk x)) [c0] rest) CELLS)) as RV end.
  lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
    pose proof (proj2 (proj1 (OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA.ApWalkTac.rw_cells_app m (adr (sc_blk x)) [c0; c1; c2; c3; c4; c5; c6; c7; c8] (c9 :: c10 :: rest)) CELLS)) as RA0;
    pose proof (proj1 (proj1 (OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA.ApWalkTac.rw_cells_app m _ [c9; c10] rest) RA0)) as RA; clear RA0 end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in RA.
  pose proof (munch_refl [(spa - 16, spa)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply evt_cut.
  { eapply (SCT_get_signature_nid_specA) with (lo := lo) (OW := OW) (LB := LB) (xb := sc_blk x) (A := adr (sc_blk x)) (v := 0) (h := sc_hash x) (g := sc_sigalg x); rewrite ?ESPA;
      [exact HEAP| exact ST| exact MI| exact CEIL| clear - LO'; lia| unfold SCT_SIZE; exact HSIN| clear - AL16s; uchk_open; Z.div_mod_to_equations; lia
      | unfold SCTO_VERSION; rewrite Z.add_0_r; exact (proj1 RV)| unfold SCTO_ALGS; exact (proj1 RA)| left; reflexivity| exact HR| exact GR| reflexivity]. }
  intros ms' PO. unfold leaf16A_post, leafA_post in PO. rewrite ?ESPA in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & _).
  rewrite (ret_pc_even 0x338144) by (clear; lia). cbn [Z.eqb Pos.eqb].
  assert (NZ : sig_nid 0 (sc_hash x) (sc_sigalg x) <> NID_undef) by (pose proof (NID V0) as X; unfold sct_nid in X; rewrite V0 in X; exact X).
  pose proof (sig_nid_cases _ _ NZ) as Hn. set (nid := sig_nid 0 (sc_hash x) (sc_sigalg x)) in *.
  assert (NR : 0 < nid < 1503) by (unfold NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption in Hn; clear - Hn; lia).
  (* [comment removed for export] *)
  assert (SZL : Z.of_nat (cells_size (sc_lo f g j0 j8 j16 j32 j40 junk (C8 (Z_to_bv 64 f)))) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; clear; lia).
  pose proof (agree_on_of_munch_nw _ _ _ MU1) as AG1.
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRL; [| intros xa Hxa; unfold sc_lo in SZL; rewrite SZL in Hxa; cbn [outside fst snd]; clear - Hxa; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa SPAH; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in HB; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa OBCu CEILu LO'; split; [lia| exact I]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in CELLS; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; clear - Hxa BSC CEILu LO'; split; [lia| exact I]].
  assert (HEAP1 : AHEAP Σc OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (STK1 : forall a, aclient_addr (OW ++ LB) spa a -> outside [(spa - 16, spa)]%Z a).
  { intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; unfold BnHeapA.ACEIL in *; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia. }
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) spa a).
  { intros a [Ha|[Ha|Hb]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Hb]. }
  assert (INV1 : sc_invL [] LB (C8 (Z_to_bv 64 f)) lv Σc m1).
  { split; [exact HEAP1|]. split; [exact LIVE|]. split; [exact MI1|]. split; [exact ST1|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AG1|]. intros a [Ha _]. exact (STK1 a (LBI' a Ha)). }
    split; [unfold sc_lo; exact FRL|]. split; [reflexivity|]. split; [exact FRH|]. split; [| exact LBI].
    eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG1|]. intros a Ha. destruct (SCTA a Ha) as (_ & _ & C). exact (STK1 a (LBI' a C)). }
  assert (BIO1 : sc_bioL m1 ((nw + zlength O_C9) mod 2 ^ 64)) by (split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]).
  clear HEAP ST MI MU WM AG1 HEAP1 STK1 FRL FRH HB REP AGR.
  (* [comment removed for export] *)
  zstep. if_cases Kz; zify_cond Kz; [exfalso; apply NZ; unfold NID_undef; rewrite ?unsigned_lit in Kz by (clear - NR; lia); clear - Kz NR; lia|]. try clear Kz.
  zstep.
  apply evt_done.
  eapply sc_nid2ln with (used := used + 3) (budget := budget); [exact INV1| exact BIO1| exact CR| clear - U0; lia| clear - UB HXN; lia| exact CRED| exact Hn|].
  clear dependent m1. clear dependent Σc. clear dependent m. clear LBI SZ NW. try clear INV1. try clear BIO1. try clear LIVE.
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fcc fcc m Σc INV BIO CR.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ' & FRH & REP & LBI). destruct BIO as [NW' HB].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply (sc_printf PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
      (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (A := A_C10_A) (fmt := FMT_C10) (args := [PA_s (ln_str nid)]) (o := ln_str nid) (retpc := 0x338164) (used := used + 4) (budget := budget);
    first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CRED| idtac];
    try (clear - CR U0 UB HXN; lia); try match goal with |- _ = _ => reflexivity end.
  1: exact (vfmtA_C10_ln nid Hn).
  1: rewrite (zlength_ln_str nid Hn); unfold ln_lenA; destruct (nid =? NID_ecdsa_with_SHA256); clear; lia.
  1: cbn [vargsA_ok]; split; [apply ln_vargA; exact Hn| exact I].
  intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fcd fcd m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW' LBI SZ'.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ' & FRH & REP & LBI). destruct BIO as [NW' HB].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply (sc_printf PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
      (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (A := A_C11_A) (fmt := FMT_C11) (args := [PA_i 8; PA_s []]) (o := O_C11) (retpc := 0x3381c4) (used := used + 7) (budget := budget);
    first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CRED| exact vfmtA_C11| idtac];
    try (clear - CR U0 UB HXN; lia); try match goal with |- _ = _ => reflexivity end.
  1: rewrite zlength_O_C11; clear; lia.
  1: cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I].
  intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fce fce m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW' LBI SZ'.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ' & FRH & REP & LBI). destruct BIO as [NW' HB].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof REP as (_ & _ & CELLS & _ & _ & A3 & _). clear BSI.
  ablock HEAP HSIN ACCS OFFS. unfold SCT_SIZE in ACCS, OFFS.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN) as (_ & _ & _ & _ & BSI). cbn [blk_addr blk_size fst snd] in BSI. unfold SCT_SIZE in BSI.
  lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU.
  assert (OFFW : offshW [(spa, spa + 56)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu SPAL SPAH; alia).
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS.
  assert (SLR : 0 <= sc_siglen x <= MAX_SCT_SIZE).
  { unfold sc_siglen. unfold CtSctP.SctRep.olen in SL. destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0 SL; lia| clear; unfold MAX_SCT_SIZE; lia]. }
  unfold MAX_SCT_SIZE in SLR.
  lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: C8 (Z_to_bv 64 (sc_siglen x)) :: ?rest) =>
    apply (c8_small_as_c4 m _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] (sc_siglen x) rest) in CELLS; [| clear - SLR; lia] end.
  cbn [app] in CELLS.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. try rewrite (sx32_small (sc_siglen x)) by (clear - SLR; lia). zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply (sc_hex PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
      (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (o := sc_sig x) (D := CtRepP.ApCells.optr adr (sc_sig x)) (len := sc_siglen x) (retpc := 0x338204) (used := used + 10) (budget := budget);
    first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CRED| idtac];
    try (clear - CR U0 UB SLR; lia); try match goal with |- _ = _ => reflexivity end.
  1: right; right; left; reflexivity.
  intros t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f Fcf fcf m' Σc' nw' INV BIO CR' _.
  eapply KX; [exact INV| exact BIO| clear - CR' UB; lia].
Qed.

(* [comment removed for export] *)
Lemma sc_tail1 : forall (Q : config -> Prop) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x24 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (used budget : Z),
  sc_version x = 0 ->
  sc_invL [] LB (C8 (Z_to_bv 64 f)) lv Σc m -> sc_bioL m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used ->
  used + 16 + HX_CRED (sc_extlen x) + HX_CRED (sc_siglen x) <= budget -> budget <= rt_credit RTS Σ1 ->
  at_exitL Q (C8 (Z_to_bv 64 f)) lv budget ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x3380a4) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros V0 INV BIO CR U0 UB CRED KX. pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB]. facts.
  pose proof REP as (HSIN & AL16s & _ & _ & A2 & A3 & _ & _ & VR & NID & HR & GR & _ & EXL & EL & SL & _).
  assert (HXE : 0 <= HX_CRED (sc_extlen x)) by (rewrite EXL; unfold HX_CRED, CtSctP.SctRep.olen; destruct (sc_ext x) as [[q n]|]; [destruct A2 as (N0 & _); clear - N0; lia| clear; lia]).
  assert (HXS : 0 <= HX_CRED (sc_siglen x)) by (unfold HX_CRED, sc_siglen; destruct (sc_sig x) as [[q n]|]; [destruct A3 as (N0 & _); clear - N0; lia| clear; lia]).
  assert (ELR : 0 <= sc_extlen x <= MAX_SCT_SIZE).
  { rewrite EXL. unfold CtSctP.SctRep.olen in EL |- *. destruct (sc_ext x) as [[q n]|]; [destruct A2 as (N0 & _); clear - N0 EL; lia| clear; unfold MAX_SCT_SIZE; lia]. }
  unfold MAX_SCT_SIZE in ELR.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply (sc_printf PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
      (nw := nw) (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (A := A_C7_A) (fmt := FMT_C7) (args := [PA_i 8; PA_s []]) (o := O_C7) (retpc := 0x3380c0) (used := used) (budget := budget);
    first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CRED| exact vfmtA_C7| idtac];
    try (clear - CR U0 UB HXE HXS; lia); try match goal with |- _ = _ => reflexivity end.
  1: rewrite zlength_O_C7; clear; lia.
  1: cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I].
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fcb fcb m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW LBI SZ.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI). destruct BIO as [NW HB].
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof REP as (_ & _ & CELLS & _).
  ablock HEAP HSIN ACCS OFFS. unfold SCT_SIZE in ACCS, OFFS.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN) as (BS0 & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BS0, BSC, BSI. unfold BnHeapA.ACEIL in BSC. unfold SCT_SIZE in BSC, BSI.
  lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU.
  assert (OFFW : offshW [(spa, spa + 56)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu SPAL SPAH; alia).
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. ab_shload 8. zstep. step. rewrite ?zxb_z8, ?sxb_z8. if_false. zstep. zstep. if_cases Ke; zify_cond Ke; rewrite ?unsigned_lit in Ke by (clear - ELR; lia).
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    apply evt_done.
    eapply (sc_printf PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
        (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (A := A_C8_A) (fmt := FMT_C8) (args := []) (o := O_C8) (retpc := 0x338120) (used := used + 3) (budget := budget);
      first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CRED| exact vfmtA_C8| exact I| idtac];
      try (clear - CR U0 UB HXE HXS; lia); try match goal with |- _ = _ => reflexivity end.
    1: rewrite zlength_O_C8; clear; lia.
    intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fcc fcc m' Σc' INV BIO CR' _.
    eapply sc_tail2 with (used := used + 6) (budget := budget); [exact V0| exact INV| exact BIO| clear - CR'; lia| clear - U0; lia| clear - UB HXE; lia| exact CRED| exact KX].
  - (* [comment removed for export] *)
    zstep. zstep. try rewrite (sx32_small (sc_extlen x)) by (clear - ELR; lia). try rewrite (swrap32_small (sc_extlen x)) by (clear - ELR; lia). zstep. zstep. zstep. zstep.
    apply evt_done.
    eapply (sc_hex PFC sp spa f lo g OW LB pb out pv adr x m3 Σ1 vra v8 gp j0 j8 j16 j32 j40 junk) with
        (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (o := sc_ext x) (D := CtRepP.ApCells.optr adr (sc_ext x)) (len := sc_extlen x) (retpc := 0x33810c) (used := used + 3) (budget := budget);
      first [exact HEAP3| exact CEIL| exact LO| exact SPAL| exact SPAH| exact SPA32| exact GSZ| exact TOP| exact FLEN| exact HBIN| exact REP3| exact NPB| exact INV'| exact BIO'| exact CRED| idtac];
      try (clear - CR U0 UB HXE HXS ELR; lia); try match goal with |- _ = _ => reflexivity end.
    1: right; left; reflexivity.
    1: exact EXL.
    1: rewrite Z.add_0_r, (swrap32_small (sc_extlen x)) by (clear - ELR; lia); reflexivity.
    intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fcc fcc m' Σc' nw' INV BIO CR' _.
    pose proof INV as INVc. destruct INV as (_ & _ & _ & _ & _ & FRLc & _). unfold sc_lo in FRLc.
    apply cps_from_evt'. zstep. apply evt_done.
    eapply sc_tail2 with (used := used + 3 + HX_CRED (sc_extlen x)) (budget := budget); [exact V0| exact INVc| exact BIO| clear - CR'; lia| clear - U0 HXE; lia| clear - UB; lia| exact CRED| exact KX].
Qed.

End TL.
