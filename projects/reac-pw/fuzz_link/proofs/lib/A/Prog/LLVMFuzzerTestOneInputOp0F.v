(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 750 of its 811 lines of code are new or changed and 1271 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: the end of the arm, +0xf7c .. +0x1110
   (listing (internal path) (internal record, sha256 e84d6f0c6974)):
     +0xf7c  mv a0, s7; jal wrapper_free (0x83754)          the kind buffer (text_buf(kc), NULL when kc = 0)
     +0xf84  mv a0, s10; jal wrapper_free (0x8375c)         the alias buffer (text_buf(ac), NULL when ac = 0)
     +0xf8c  sb s8, 0x60(s3); sb s8, 0x66(s3) .. 0x6a(s3); sb s8, 0x5c(s3) .. 0x5f(s3)
                                                            wk and wa marked unusable again (shadow 0xf8)
     +0xfb4  ld s10, 0x78(s1); ld s7, 0xf0(s1); j +0x1110   LF_tail
   From Op0V.v's cut at check_requests' return to lf_tail_inv i. The frees run while wk and wa are in scope (the
   frame's shadow is Op0Cut.v SH_R), so the free steps are Txa.v's lf_free_blk_step / lf_free_null_step at
   Chk.v's chk_cut, the cut at any frame shadow.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputArmK
  LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmH LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputFree
  LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputChk LLVMFuzzerTestOneInputOp1E LLVMFuzzerTestOneInputOp0Cut
  LLVMFuzzerTestOneInputOp0Z LLVMFuzzerTestOneInputOp0V LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputOp3T.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the runner's state from +0xf8c: wk's and wa's five shadow bytes (atom 19 = the frame's shadow) as two write
   windows, and the slots s1 + 0x78 (F + 0x20, atom 32) and s1 + 0xf0 (g_nl + 0x40000, atom 33) *)
Definition f_sh_rg (lo hi : Z) : YP09.region := YP09.mkRegion (Some 19%nat) lo hi lo hi [].
Definition f_sl_rg (off : Z) (a : nat) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff a 0))].
Definition f_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2);
           (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition f_ss (pc : Z) : sstate :=
  mkSS pc sr_atoms [f_sh_rg 92 97; f_sh_rg 102 107; f_sl_rg LS_WA 32; f_sl_rg LS_GNL40 33] None f_facts.

Definition LR_f1 : Z := AF_LLVMFuzzerTestOneInput + 0xf84.     (* 0x83758 the first free has returned *)
Definition LR_f2 : Z := AF_LLVMFuzzerTestOneInput + 0xf8c.     (* 0x83760 the second free has returned *)

(* the registers the end keeps (all but a0, ra, s7, s10 and the temporaries), and those of the two frees *)
Definition F_R : list Z := [2; 3; 4; 8; 9; 19; 21; 22; 24; 25; 27].
Definition F_R1 : list Z := [2; 3; 4; 8; 9; 19; 21; 22; 24; 25; 26; 27].
Lemma F_R_low : forall r, In r F_R -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.
Lemma F_R1_low : forall r, In r F_R1 -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.
Lemma F_R1_saved : forall r, In r F_R1 -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.
Lemma f_keep_sub : forall a b, d4_keepL F_R1 a b -> d4_keepL F_R a b.
Proof. intros a b H r Hr. apply H. cbn in Hr |- *. tauto. Qed.

(* the shadow bytes of wk (92 .. 96) and wa (102 .. 106) are 0xf8 in LF_SH0; every other byte of SH_R is LF_SH0's *)
Lemma f_sh0_wk : forall i, ((92 <= i < 97) \/ (102 <= i < 107))%nat -> nth i LF_SH0 0 = 248.
Proof.
  intros i Hi.
  assert (Hi' : (i = 92 \/ i = 93 \/ i = 94 \/ i = 95 \/ i = 96 \/
                 i = 102 \/ i = 103 \/ i = 104 \/ i = 105 \/ i = 106)%nat) by lia.
  repeat (destruct Hi' as [-> | Hi']; [reflexivity|]). subst i. reflexivity.
Qed.
Lemma f_shr_out : forall i, (i < 112)%nat -> ~ (92 <= i < 97)%nat -> ~ (102 <= i < 107)%nat ->
  nth i LF_SH0 0 = nth i SH_R 0.
Proof.
  intros i Hi H1 H2. rewrite (SH_R_nth i Hi), (SH_W_nth i Hi).
  destruct (Nat.leb_spec 102 i), (Nat.ltb_spec i 107); cbn [andb]; try lia;
  destruct (Nat.leb_spec 92 i), (Nat.ltb_spec i 97); cbn [andb]; try lia; reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
(* the allocator's free rules and the free sites' traces (Free.v, open item W1) *)
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

#[local] Abbreviation BASEF cx :=
  (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Notation CHK := (chk_cut SK B MT MS la_nul).

(* the frame's shadow after a run that stored v at the indices of two ranges *)
Lemma f_fsh_upd2 : forall cx fp (W : world SEGS) ms ms' (X : Z -> Prop) sh sh'
    lo1 hi1 lo2 hi2 v,
  lf_fshadow cx fp W ms sh -> kagree pa_segs X (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  length sh' = length sh ->
  (forall i, (i < length sh)%nat -> ~ (lo1 <= Z.of_nat i < hi1) -> ~ (lo2 <= Z.of_nat i < hi2) ->
     ~ X (lf_SH cx fp + Z.of_nat i) /\ nth i sh' 0 = nth i sh 0) ->
  (forall i, (i < length sh)%nat -> (lo1 <= Z.of_nat i < hi1) \/ (lo2 <= Z.of_nat i < hi2) ->
     aview pa_segs (w_H W) (ms_mem ms') (lf_SH cx fp + Z.of_nat i) = Some v /\ nth i sh' 0 = v) ->
  lf_fshadow cx fp W ms' sh'.
Proof.
  intros cx fp W ms ms' X sh sh' lo1 hi1 lo2 hi2 v Hf KA Hl Hout Hin i Hi. rewrite Hl in Hi.
  destruct (Z_lt_le_dec (Z.of_nat i) lo1) as [A1 | A1];
    [|destruct (Z_lt_le_dec (Z.of_nat i) hi1) as [A2 | A2];
      [destruct (Hin i Hi (or_introl (conj A1 A2))) as (Hv & Ne); rewrite Ne; exact Hv|]];
  (destruct (Z_lt_le_dec (Z.of_nat i) lo2) as [B1 | B1];
    [|destruct (Z_lt_le_dec (Z.of_nat i) hi2) as [B2 | B2];
      [destruct (Hin i Hi (or_intror (conj B1 B2))) as (Hv & Ne); rewrite Ne; exact Hv|]]);
  destruct (Hout i Hi ltac:(lia) ltac:(lia)) as (NX & Ne); rewrite Ne;
  rewrite (aview_of_kagree pa_segs X _ _ _ _ _ KA NX); exact (Hf i Hi).
Qed.


(* ==========================================================================
   The frees at any frame shadow (Txa.v's free steps, at chk_cut)
   ========================================================================== *)

(* the bytes of a heap block apart from the call's two blocks, its FILE block and its input miss the cut's
   footprint (Txa.v ak_cut_fp_not_blk, whose proof reads only the journal, the frame list, lf_jbk and lf_blocks) *)
Lemma f_fp_not_blk : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W (ms : machine_state) mdl b,
  MS = link_amf -> la_nul = LA_NUL -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S)) ->
  AR SEGS B ly S W (ms_mem ms) mdl ->
  CHK cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms mdl ->
  In b (ablocks B ly S) ->
  (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
     zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) ->
  forall a, fst b <= a < fst b + req_size (snd b) -> ~ lf_cut_fp MS la_nul cx fp md mk T3 a.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms mdl [p n] HMS HLA HPB HAR
    (HJ & Hfr & _ & _ & _ & _ & Hjbk & Hblk & _) Hb HD a Ha Hfp.
  cbn [fst snd] in *.
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLA) as (HIMG & HREL).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (H16 & H4096 & Hc & Happ & _ & _ & Hn).
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR ltac:(left; exists p, n; split; [exact Hb | lia])) as (_ & Hni).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _).
  pose proof HJ as Hrow. eapply ajournal_gx_row in Hrow. destruct Hrow as (Hc0 & H47 & Hlo & Hhi).
  assert (Hs1 : spZ (c_regs cx) - 416 - 31 <= lf_sp1 cx).
  { unfold lf_sp1, lf_sp1_of, LF_MFRAME.
    pose proof (Z.div_mod (spZ (c_regs cx) - 416) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 416) 32 ltac:(lia)).
    lia. }
  unfold LLVMF_STK in Hlo. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  assert (GAP : forall x, 0x7fff7000 <= x < 0x10007fff8000 -> ~ (p <= x < p + req_size n)) by lia.
  assert (IMG : forall x, lf_img_fp MS la_nul x -> x <> a) by (intros x Hx ->; exact (Hni (proj1 (HIMG a Hx)))).
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> in_img SEGS x).
  { intros x [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HREL x Hr)]. }
  assert (DJ : forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
                 ~ (fst c <= a < fst c + req_size (snd c))).
  { intros c Hc' Hac. pose proof (HD c Hc') as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
  unfold lf_cut_fp in Hfp.
  destruct Hfp as [Hf | [Hf | [Hf | [Hf | [Hf | [Hf | Hf]]]]]].
  - unfold lf_saved_fp in Hf. lia.
  - unfold lf_header_fp in Hf. pose proof LF_frame_slot as (FB & _).
    destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (HP & _).
    pose proof (pairwise_In zdisjoint _ (p, req_size n) (frame_addr ly LF_CID fp, fs_frame_bytes LF_CID) _ _ eq_refl HP
      ltac:(apply in_map_iff; exists (p, n); split; [reflexivity | exact Hb])
      ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | rewrite Hfr; left; reflexivity])) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold lf_F in Hf. rewrite <- (Hfa LF_CID fp) in Hf. rewrite FB in *.
    destruct Hf as [Hf | Hf]; lia.
  - unfold lf_fshadow_fp, lf_SH, shadow_of_addr, SHADOW_OFF in Hf.
    destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HS). rewrite Forall_forall in HS.
    pose proof (HS (LF_CID, fp) ltac:(rewrite Hfr; left; reflexivity)) as (F1 & F2). cbn [fst snd] in F1, F2.
    unfold lf_F in Hf. rewrite <- (Hfa LF_CID fp) in Hf. apply (GAP a); [|lia].
    pose proof (Z.div_le_mono (frame_addr ly LF_CID fp) alloc_ceiling 8 ltac:(lia)
      ltac:(pose proof LF_frame_slot as (FB & _); lia)).
    lia.
  - unfold lf_slots_fp in Hf. lia.
  - unfold lf_jbk_fp in Hf.
    destruct Hf as [[Hf | [Hf | (f & m & Hin & Hf)]] | [Hf | [Hf | Hf]]].
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + destruct Hgi as [(_ & ->) | (f0 & _ & -> & _)]; [destruct Hin|].
      destruct Hin as [E | []]. injection E as <- <-.
      apply (DJ (f0, AMF_BLOCK) ltac:(right; right; left; left; reflexivity)). cbn [fst snd].
      unfold req_size, AMF_BLOCK in *. cbn. lia.
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + exact (Hni (RO a Hf)).
    + apply (DJ (c_p cx, c_n cx) ltac:(right; right; right; split; [lia | reflexivity])). cbn [fst snd].
      unfold req_size. destruct (c_n cx =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
  - unfold lf_blocks_fp in Hf. pose proof Hblk as (Hmd & Hmk & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmd) as (_ & Hd4 & Hcd & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmk) as (_ & Hk4 & Hck & _).
    unfold req_size, MD_SIZE, MK_SIZE in Hcd, Hck. cbn in Hcd, Hck.
    destruct Hf as [(x & Hx & Ex) | (x & Hx & Ex)]; subst a;
      (apply (GAP (shadow_of_addr SHADOW_OFF x)); [|exact Ha]);
      unfold shadow_of_addr, SHADOW_OFF, MD_SIZE, MK_SIZE in *; lia.
  - unfold lf_data_fp in Hf.
    destruct Hf as [Hf | [Hf | [Hf | [Hf | [Hf | Hf]]]]].
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + destruct (Z_lt_le_dec a (LA_LONG_ALIAS + 301)) as [L | L].
      * exact (IMG a ltac:(unfold lf_img_fp; right; right; left; lia) eq_refl).
      * exact (Hni (la_slack_img XM_LIB XN_LIB la_nul HSEGS a ltac:(lia))).
    + apply (DJ (md, MD_SIZE) ltac:(left; reflexivity)). cbn [fst snd]. unfold req_size, MD_SIZE in *. cbn. lia.
    + apply (DJ (mk, MK_SIZE) ltac:(right; left; reflexivity)). cbn [fst snd]. unfold req_size, MK_SIZE in *. cbn. lia.
    + exact (Hni (RO a Hf)).
Qed.

(* a free of one of the call's own blocks b at a free site, at any frame shadow (Txa.v lf_free_blk_step) *)
Lemma f_free_blk : forall (fy : YK11.FPState) cx fp md mk kbs mbs gbs T3 o1 b o2 ev mo wl lv k sh ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  BASEF cx -> (length sh = 112)%nat ->
  CHK cx fp md mk kbs mbs gbs T3 (o1 ++ b :: o2) ev mo wl lv k sh ly3 S3 W3 ms3 md3 ->
  In b (ablocks B ly3 S3) -> ~ In b (ablocks B (c_ly cx) (c_S cx)) ->
  (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
     zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 (fst b) -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     aregs_preserved regs regs2 ->
     CHK cx fp md mk kbs mbs gbs T3 (o1 ++ o2) (ev + 1) mo' wl lv (k + 1) sh ly2 S2 W2
       (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ->
     lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun a => fst b <= a < fst b + req_size (snd b)) ->
     (forall c, In c (ablocks B ly3 S3) -> c <> b -> In c (ablocks B ly2 S2)) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp md mk kbs mbs gbs T3 o1 [pa n] o2 ev mo wl lv k sh ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB Hsh HC Hb Hnb HD Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  cbn [fst snd] in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  pose proof HC as (HJ & Hfr & HSAV & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (Hkev & Hbb & Hfa & _ & Hfd & Hfs & _ & Hwl & _ & _ & Hbl & Hinc & _).
  pose proof HBLK as (Hmd & Hmk & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  unfold LLVMF_STK in *.
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  destruct (lf_saved_ra_s0 cx W3 ms3 HSAV) as (H8 & H16w).
  assert (Hra : raZ regs = link_text + rao)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- (lv_text LV). apply ret_ok_codeptr_v.
    - unfold LF_FREE_RAS, link_text in *. cbn in Hsite. lia.
    - unfold LF_FREE_RAS, link_text in Hsite. cbn in Hsite.
      destruct Hsite as [E | [E | [E | [E | [E | [E | [E | []]]]]]]];
        (assert (rao = 0x82e70 - 0x821cc \/ rao = 0x82e78 - 0x821cc \/ rao = 0x83758 - 0x821cc \/
                 rao = 0x83760 - 0x821cc \/ rao = 0x838dc - 0x821cc \/ rao = 0x83b8c - 0x821cc \/
                 rao = 0x83b94 - 0x821cc) as Er by lia);
        destruct Er as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity. }
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k regs HB HJ H8 H16w ltac:(lia) Hs0 Hra4) as (HCH & _).
  pose proof (lf_free_trace SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB
    LF_TRACE_FREE ltac:(rewrite Hra; exact Hsite)) as HTR.
  replace (pa_sigma LS___interceptor_trampoline_free) with (pc_wrap_free (as_code B))
    by (rewrite (lv_sigma LV), (ts_code B TB); reflexivity).
  eapply SRr_bind.
  { apply (@aj_gx_free_w fy rc SK SEGS B MT LAWS pa_segs_low (AFREE4W fy) G_HARNESS 0 [] W3 regs (ms_mem ms3)
      LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 md3 k pa n (getr regs 1) (lf_chain cx) HJ Hb R10).
    - rewrite Hsp. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D. rewrite D.
      replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. unfold LLVMF_STK, ASTACK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact HGP.
    - rewrite R4. exact HTP.
    - reflexivity.
    - exact Hret.
    - unfold EV_LIB in *. lia.
    - exact HCH.
    - exact HTR.
    - intros Hin. contradiction.
    - apply MT_OK. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & Hl1 & Hl2) & Hfr2 & HK & _ & HW & Hio).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (same_io_fds_fs md3 md2 Hio) as (Hfd2 & Hfs2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & _ & _ & _ & _ & _ & Hn).
  assert (Hr1 : 1 <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> c <> (pa, n) -> In c (ablocks B ly2 S2))
    by (intros c Hc Hne; rewrite Hl2; rewrite Hl1 in Hc; exact (in_remove1 c (pa, n) l1 l2 Hc Hne)).
  assert (HKP : akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (lf_sp1 cx - ASTACK) (lf_sp1 cx)
                  (fun a => pa <= a < pa + req_size n)).
  { rewrite <- Hsp. apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK). intros a Ha; exact Ha. }
  assert (HCALL : lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun a => pa <= a < pa + req_size n)).
  { split; [unfold ASTACK; lia|]. split; [unfold ASTACK; lia|]. split; [exact HKP|].
    exact (ashadow_kept_of_AR B LAWS ly3 S3 W3 (ms_mem ms3) md3 ly2 S2 W2 mem2 md2 HAR3 HAR2). }
  assert (Hne : forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
                  c <> (pa, n))
    by (intros c Hc; exact (zdisjoint_self_ne c (pa, n) Hr1 (HD c Hc))).
  destruct (chk_cut_callee SK B MT XM_LIB XN_LIB MS la_nul LAWS TB HSEGS MT_LE cx fp md mk kbs mbs gbs T3
    (o1 ++ (pa, n) :: o2)
    ev mo wl lv k sh ly3 S3 W3 ms3 md3 (o1 ++ o2) (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
    (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ASTACK (fun a => pa <= a < pa + req_size n)
    HMSE HLAN HPB Hsh HC HJ2 ltac:(rewrite Hfr2; reflexivity) HAR2 HCALL) as (HC2 & _).
  - intros a Ha. exact (f_fp_not_blk cx fp md mk kbs mbs gbs T3 _ ev mo wl lv k sh ly3 S3 W3 ms3 md3 (pa, n)
      HMSE HLAN HPB HAR3 HC Hb HD a Ha).
  - intros a Ha Hro.
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR3 ltac:(left; exists pa, n; split; [exact Hb | exact Ha]))
      as (_ & Hni).
    apply Hni. destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
    exact (proj2 (lf_img_facts B MS la_nul HSEGS TB HMSE HLAN) a Hr).
  - rewrite Hfd2. exact eq_refl.
  - rewrite Hfs2. exact eq_refl.
  - exact (Hsub _ Hmd (Hne _ ltac:(left; reflexivity))).
  - exact (Hsub _ Hmk (Hne _ ltac:(right; left; reflexivity))).
  - lia.
  - rewrite (blocks_bytes_bsum B ly2 S2), Hl2. rewrite (blocks_bytes_bsum B ly3 S3), Hl1 in Hbb.
    rewrite bsum_app in *. rewrite bsum_cons in Hbb. cbn [snd] in Hbb. lia.
  - lia.
  - exact (lf_bl_remove B cx o1 o2 T3 ly3 S3 ly2 S2 (pa, n) l1 l2 Hbl Hl1 Hl2).
  - intros c Hc. exact (Hsub c (Hinc c Hc) (Hne c ltac:(right; right; left; exact Hc))).
  - exact (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HCALL Hsub).
Qed.

(* a free of NULL at a free site, at any frame shadow (Txa.v lf_free_null_step) *)
Lemma f_free_null : forall (fy : YK11.FPState) cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  BASEF cx -> (length sh = 112)%nat ->
  CHK cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 0 -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     aregs_preserved regs regs2 ->
     CHK cx fp md mk kbs mbs gbs T3 own (ev + 1) mo' wl lv (k + 1) sh ly2 S2 W2
       (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ->
     lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun _ => False) ->
     Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB Hsh HC Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  pose proof HC as (HJ & Hfr & HSAV & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (Hkev & Hbb & Hfa & _ & Hfd & Hfs & _ & Hwl & _ & _ & Hbl & Hinc & _).
  pose proof HBLK as (Hmd & Hmk & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  unfold LLVMF_STK in *.
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  destruct (lf_saved_ra_s0 cx W3 ms3 HSAV) as (H8 & H16w).
  assert (Hra : raZ regs = link_text + rao)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- (lv_text LV). apply ret_ok_codeptr_v.
    - unfold LF_FREE_RAS, link_text in *. cbn in Hsite. lia.
    - unfold LF_FREE_RAS, link_text in Hsite. cbn in Hsite.
      destruct Hsite as [E | [E | [E | [E | [E | [E | [E | []]]]]]]];
        (assert (rao = 0x82e70 - 0x821cc \/ rao = 0x82e78 - 0x821cc \/ rao = 0x83758 - 0x821cc \/
                 rao = 0x83760 - 0x821cc \/ rao = 0x838dc - 0x821cc \/ rao = 0x83b8c - 0x821cc \/
                 rao = 0x83b94 - 0x821cc) as Er by lia);
        destruct Er as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity. }
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k regs HB HJ H8 H16w ltac:(lia) Hs0 Hra4) as (HCH & _).
  pose proof (lf_free_trace SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB
    LF_TRACE_FREE ltac:(rewrite Hra; exact Hsite)) as HTR.
  replace (pa_sigma LS___interceptor_trampoline_free) with (pc_wrap_free (as_code B))
    by (rewrite (lv_sigma LV), (ts_code B TB); reflexivity).
  eapply SRr_bind.
  { apply (@aj_gx_free_null_w fy rc SK SEGS B MT LAWS pa_segs_low (AFREENULL4W fy) G_HARNESS 0 [] W3 regs (ms_mem ms3)
      LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 md3 k (getr regs 1) (lf_chain cx) HJ R10).
    - rewrite Hsp. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D. rewrite D.
      replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. unfold LLVMF_STK, ASTACK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact HGP.
    - rewrite R4. exact HTP.
    - reflexivity.
    - exact Hret.
    - unfold EV_LIB in *. lia.
    - exact HCH.
    - exact HTR.
    - apply MT_OK. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & HPerm & Hfr2 & HK & _ & HW & Hio).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (same_io_fds_fs md3 md2 Hio) as (Hfd2 & Hfs2).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in c (Permutation_sym HPerm) Hc)).
  assert (HKP : akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (lf_sp1 cx - ASTACK) (lf_sp1 cx) (fun _ => False)).
  { rewrite <- Hsp. apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK). intros a Ha; exact Ha. }
  assert (HCALL : lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun _ => False)).
  { split; [unfold ASTACK; lia|]. split; [unfold ASTACK; lia|]. split; [exact HKP|].
    exact (ashadow_kept_of_AR B LAWS ly3 S3 W3 (ms_mem ms3) md3 ly2 S2 W2 mem2 md2 HAR3 HAR2). }
  destruct (chk_cut_callee SK B MT XM_LIB XN_LIB MS la_nul LAWS TB HSEGS MT_LE cx fp md mk kbs mbs gbs T3 own ev mo
    wl lv k sh ly3 S3 W3 ms3 md3 own (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
    (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ASTACK (fun _ => False)
    HMSE HLAN HPB Hsh HC HJ2 ltac:(rewrite Hfr2; reflexivity) HAR2 HCALL) as (HC2 & _).
  - intros a [].
  - intros a [].
  - rewrite Hfd2. exact eq_refl.
  - rewrite Hfs2. exact eq_refl.
  - exact (Hsub _ Hmd).
  - exact (Hsub _ Hmk).
  - lia.
  - rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B ly3 S3). exact Hbb.
  - lia.
  - exact (lf_bl_perm B cx own T3 ly3 S3 ly2 S2 Hbl HPerm).
  - intros c Hc. exact (Hsub c (Hinc c Hc)).
  - exact (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HCALL HPerm).
Qed.

(* the free of a text_buf answer (Op0Cut.v tb_nb: NULL, or the fresh block), at any frame shadow *)
Lemma f_free_tb : forall (fy : YK11.FPState) cx fp md mk kbs mbs gbs T3 o1 nb o2 cap t ev mo wl lv k sh ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  BASEF cx -> (length sh = 112)%nat ->
  CHK cx fp md mk kbs mbs gbs T3 (o1 ++ nb ++ o2) ev mo wl lv k sh ly3 S3 W3 ms3 md3 ->
  tb_nb cap t nb ->
  (forall b, In b nb -> In b (ablocks B ly3 S3) /\ ~ In b (ablocks B (c_ly cx) (c_S cx)) /\
     (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
        zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))) ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 t -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     aregs_preserved regs regs2 ->
     CHK cx fp md mk kbs mbs gbs T3 (o1 ++ o2) (ev + 1) mo' wl lv (k + 1) sh ly2 S2 W2
       (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ->
     (exists E : Z -> Prop, lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E /\
        (forall a, E a -> a < alloc_ceiling)) ->
     (forall c, In c (ablocks B ly3 S3) -> ~ In c nb -> In c (ablocks B ly2 S2)) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp md mk kbs mbs gbs T3 o1 nb o2 cap t ev mo wl lv k sh ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB Hsh HC Hnb Hblk Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  destruct Hnb as [(_ & -> & ->) | (Hc1 & H4096 & ->)].
  - cbn [app] in HC.
    apply (f_free_null fy cx fp md mk kbs mbs gbs T3 (o1 ++ o2) ev mo wl lv k sh ly3 S3 W3 ms3 md3 regs rao mo' Q
      HB Hsh HC Hk R10 Hsp Hs0 R3 R4 R1 Hsite).
    intros W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HCALL HPerm.
    apply (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2).
    + exists (fun _ => False). split; [exact HCALL | intros a []].
    + intros c Hc _. exact (Permutation_in c (Permutation_sym HPerm) Hc).
  - destruct (Hblk (t, cap + 1) ltac:(left; reflexivity)) as (Hb & Hnb & HD).
    cbn [app] in HC.
    apply (f_free_blk fy cx fp md mk kbs mbs gbs T3 o1 (t, cap + 1) o2 ev mo wl lv k sh ly3 S3 W3 ms3 md3 regs rao mo'
      Q HB Hsh HC Hb Hnb HD Hk R10 Hsp Hs0 R3 R4 R1 Hsite).
    intros W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HCALL Hsub.
    apply (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2).
    + exists (fun a => fst (t, cap + 1) <= a < fst (t, cap + 1) + req_size (snd (t, cap + 1))).
      split; [exact HCALL|].
      intros a Ha. pose proof HC as (HJ & _).
      destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
        (ms_mem ms3) md3 k HB HJ) as (_ & _ & _ & _ & _ & _ & HAR3).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & _ & Hc & _). cbn [fst snd] in *. lia.
    + intros c Hc Hcn. apply (Hsub c Hc). intros E. apply Hcn. left. symmetry. exact E.
Qed.

(* the live bytes at a cut whose own list is the two blocks: at most the kept FILE block more (lf_jbk's amf_gi) *)
Lemma f_live_held : forall cx md mk T3 ly S (m : word -> option byte),
  amf_gi SEGS MS T3 m -> lf_bl B cx [(md, MD_SIZE); (mk, MK_SIZE)] T3 ly S ->
  blocks_bytes S <= blocks_bytes (c_S cx) + LF_LIVE_HELD.
Proof.
  intros cx md mk T3 ly S m Hgi Hbl.
  destruct (lf_bl_bytes B cx _ T3 ly S Hbl) as (D & HT & Hb).
  assert (HD : bsum D <= AMF_BLOCK).
  { destruct Hgi as [(_ & ->) | (f & _ & -> & _)].
    - symmetry in HT. apply app_eq_nil in HT as (_ & ->). cbn. unfold AMF_BLOCK. lia.
    - destruct (c_T cx) as [|c0 cT]; cbn [app] in HT.
      + subst D. cbn. lia.
      + injection HT as _ HD. symmetry in HD. apply app_eq_nil in HD as (_ & ->). cbn. unfold AMF_BLOCK. lia. }
  rewrite Hb. unfold LF_LIVE_HELD, bsum in *. cbn [fold_right snd] in *. unfold MD_SIZE, MK_SIZE in *. lia.
Qed.

(* the runner's entry state at +0xf8c *)
Lemma f_entry : forall (fy : YK11.FPState) cx fp (W : world SEGS) ms pc v32 v33,
  getr (ms_regs ms) 9 = w64 (lf_sp1 cx) -> getr (ms_regs ms) 19 = w64 (lf_SH cx fp) ->
  alloc_ceiling + LLVMF_STK - 432 <= lf_sp1 cx -> lf_sp1 cx + 0x128 <= 2 ^ 47 ->
  kLowMemEnd + 512 <= lf_SH cx fp -> lf_SH cx fp + 128 <= kHighMemBeg -> lf_SH cx fp mod 4 = 0 ->
  4096 <= lf_F cx fp -> lf_F cx fp + 1024 <= alloc_ceiling ->
  (forall i, 0 <= i < 128 -> apresent (w_H W) (ms_mem ms) (lf_SH cx fp + i)) ->
  0 <= v32 < 2 ^ 64 -> 0 <= v33 < 2 ^ 64 ->
  lf_slot cx W ms LS_WA v32 -> lf_slot cx W ms LS_GNL40 v33 ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg (ms_regs ms) [Z_to_bv 64 v32; Z_to_bv 64 v33])) (f_ss pc)
    (restrict (w_H W) (@mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS))).
Proof.
  intros fy cx fp W ms pc v32 v33 R9 R19 Hlo H47 SH1 SH2 SH4 F4 Fc Fshp Hv32 Hv33 Hs32 Hs33.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  set (E := Eimg (Ereg (ms_regs ms) [Z_to_bv 64 v32; Z_to_bv 64 v33])).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 v32)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 v33)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp)
    by (rewrite E19; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  assert (U32 : bv_unsigned (ew E 32) = v32) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = v33) by (rewrite E33; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold f_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, f_sh_rg, f_sl_rg;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [unfold kLowMemEnd in *; clia|]. split; [unfold kHighMemBeg in *; clia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clia.
    + rewrite U19. split; [unfold kLowMemEnd in *; clia|]. split; [unfold kHighMemBeg in *; clia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clia.
    + rewrite U9. split; [unfold LS_WA, LLVMF_STK in *; clia|]. split; [unfold LS_WA, LLVMF_STK in *; clia|].
      split; [intros o Ho; clia|]. apply Forall_cons; [|apply Forall_nil].
      apply (u_slot_chunk E cx W ms LS_WA _ v32); [|exact Hs32].
      rewrite (lf_sv_off E 32 v32 0 E32) by clia. rewrite Z.add_0_r. reflexivity.
    + rewrite U9. split; [unfold LS_GNL40, LLVMF_STK in *; clia|]. split; [unfold LS_GNL40, LLVMF_STK in *; clia|].
      split; [intros o Ho; clia|]. apply Forall_cons; [|apply Forall_nil].
      apply (u_slot_chunk E cx W ms LS_GNL40 _ v33); [|exact Hs33].
      rewrite (lf_sv_off E 33 v33 0 E33) by clia. rewrite Z.add_0_r. reflexivity.
  - apply pairwise_disjoint_of_extents. unfold f_sh_rg, f_sl_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold LS_WA, LS_GNL40, kLowMemEnd, kHighMemBeg, LLVMF_STK in *. repeat split; clia.
  - split; [|split; exact I]. cbn [f_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U32, U33. assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, LLVMF_STK in *.
    split; [split; [clia|]; split; [unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
            apply Z_mod_mult | clia]|].
    split; [split; [clia|]; split; [exact SH4 | clia]|].
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | clia].
Qed.

(* ==========================================================================
   The end of op_read: +0xf7c .. LF_tail
   ========================================================================== *)
Lemma r_fin : forall POST i,
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_v SK B MT MS la_nul LF_MO_SET LF_MO_OP LR_e r_q5 i).
Proof.
  intros POST i HT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HV.
  destruct HV as (Hsh & md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hkc & Hac & Hi & Hcore & HC & Hcur & Hop & Hrq & Hext & Hq).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R23 & R24 & R25 & R26).
  pose proof Hq as (R21 & R22 & R27).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  pose proof Hext as (Hbufs & _).
  pose proof Hbufs as (Hnb1 & Hnb2 & Hbin & Hb12).
  pose proof HC as (_ & _ & _ & _ & _ & _ & Hjbk & _ & _).
  pose proof Hjbk as (Hkev & _).
  (* ---- +0xf7c .. +0xf80: a0 := s7 (kind), jal wrapper_free ---- *)
  rewrite (lf_shape_eta fy LR_e ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_e) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_e)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ F_R1 HS EL F_R1_low ltac:(d4chk)) as KRA.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (chk_cut_run SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 msA md3 mdA
    SH_R_len HC HJ KA (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  clear HC Hcur.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  ew_reg EL 23%nat (23%bv : bv 5) Q10. rewrite R23 in Q10. rewrite HBASE in Q1.
  kreg KRA 2 (2%bv : bv 5) A2. kreg KRA 3 (3%bv : bv 5) A3. kreg KRA 4 (4%bv : bv 5) A4.
  kreg KRA 8 (8%bv : bv 5) A8.
  apply (f_free_tb fy cx fp md mk kbs' mbs gbs T3 nb2 nb1 [(md, MD_SIZE); (mk, MK_SIZE)] kc t1 _ _ _ _ k2 SH_R
    ly3 S3 W3 msA mdA (ms_regs msA) 5516 (lf_mo LF_MO_SET LF_MO_OP i) (POST cx) HB SH_R_len HCA Hnb1
    (fun b Hb => Hbin b (in_or_app _ _ _ (or_introl Hb)))).
  { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia. }
  { exact Q10. }
  { unfold spZ. rewrite A2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { unfold s0Z. rewrite A8, R8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { rewrite A3. exact R3. }
  { rewrite A4. exact R4. }
  { exact Q1. }
  { unfold LF_FREE_RAS, link_text. right; right; left. reflexivity. }
  intros W2 ly2 S2 regs2 mem2 md2 Hle2 HP2 HC2 (E2 & HCALL2 & HE2) Hsub2.
  set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)) in *.
  pose proof (lf_cur_callee B cx ASTACK ly3 S3 ly2 S2 W3 msA W2 ms2 E2 P N HCALL2
    (fun a Ha HEa => ltac:(pose proof (HE2 a HEa); unfold lf_cur_fp in Ha; unfold LS_P, LS_N, LLVMF_STK in *; lia))
    HcurA) as Hcur2.
  pose proof (d4_keep_pres F_R1 _ _ F_R1_saved HP2) as KP2.
  pose proof (d4_keep_trans F_R1 _ _ _ KRA KP2) as K2T.
  (* ---- +0xf84 .. +0xf88: a0 := s10 (alias), jal wrapper_free ---- *)
  assert (HPC2 : getr (ms_regs msA) 1 = Z_to_bv 64 (BASE + LR_f1)) by (rewrite Q1, HBASE; reflexivity).
  pose proof HC2 as (HJ2 & Hfr2 & _).
  unfold ms2. rewrite HPC2.
  clear HS SHOK HEI EL.
  pose proof (d4_entry fy W2 regs2 mem2 LR_f1) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs2 []))
    (mrestrict (w_H W2) (ms_mem (@mkst fy regs2 (Z_to_bv 64 (BASE + LR_f1)) mem2 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  remember (Eimg (Ereg regs2 [])) as E2x eqn:HEdef.
  assert (EL2 : forall n, (n < A_TEXT)%nat -> ew E2x n = ew (Ereg regs2 []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ2 SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (d4_keep_run fy W2 _ _ msB regs2 _ F_R1 HS EL2 F_R1_low ltac:(d4chk)) as KRB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
  assert (FdB : m_fds mdB = m_fds md2) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
  assert (FsB : m_fs mdB = m_fs md2) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
  pose proof (chk_cut_run SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ (k2 + 1) SH_R ly2 S2 W2 ms2 msB md2
    mdB SH_R_len HC2 HJ2 KB (fun x Hx => HGB x Hx) FdB FsB) as HCB.
  pose proof (lf_cur_keep (fun _ => False) cx W2 ms2 W2 msB P N KB (fun a _ H => H) Hcur2) as HcurB.
  clear HC2 Hcur2.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1B. prreg HS (10%bv : bv 5) Q10B.
  ew_reg EL2 26%nat (26%bv : bv 5) Q10B. rewrite HBASE in Q1B.
  kreg K2T 26 (26%bv : bv 5) T26. rewrite T26, R26 in Q10B.
  pose proof (d4_keep_trans F_R1 _ _ _ K2T KRB) as K3T.
  kreg K3T 2 (2%bv : bv 5) B2. kreg K3T 3 (3%bv : bv 5) B3. kreg K3T 4 (4%bv : bv 5) B4.
  kreg K3T 8 (8%bv : bv 5) B8.
  (* the alias's block is still a block of the state, and not the kind's *)
  assert (Hbin2 : forall b, In b nb2 -> In b (ablocks B ly2 S2) /\ ~ In b (ablocks B (c_ly cx) (c_S cx)) /\
     (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
        zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))).
  { intros b Hb. destruct (Hbin b (in_or_app _ _ _ (or_intror Hb))) as (Hb3 & Hb0 & HbD).
    split; [|split; [exact Hb0 | exact HbD]].
    apply (Hsub2 b Hb3). intros Hb1. pose proof (Hb12 b b Hb1 Hb) as D.
    destruct Hnb2 as [(_ & _ & ->) | (_ & _ & ->)]; [destruct Hb|].
    destruct Hb as [<- | []]. unfold zdisjoint in D. cbn [fst snd] in D. unfold req_size in D.
    destruct (ac + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]. }
  apply (f_free_tb fy cx fp md mk kbs' mbs gbs T3 [] nb2 [(md, MD_SIZE); (mk, MK_SIZE)] ac t2 _ _ _ _ (k2 + 1) SH_R
    ly2 S2 W2 msB mdB (ms_regs msB) 5524 (lf_mo LF_MO_SET LF_MO_OP i) (POST cx) HB SH_R_len HCB Hnb2 Hbin2).
  { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia. }
  { exact Q10B. }
  { unfold spZ. rewrite B2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { unfold s0Z. rewrite B8, R8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { rewrite B3. exact R3. }
  { rewrite B4. exact R4. }
  { exact Q1B. }
  { unfold LF_FREE_RAS, link_text. right; right; right; left. reflexivity. }
  intros W9 ly9 S9 regs9 mem9 md9 Hle9 HP9 HC9 (E9 & HCALL9 & HE9) Hsub9.
  set (ms9 := @mkst fy regs9 (getr (ms_regs msB) 1) mem9 (seg_rom SEGS)) in *.
  pose proof (lf_cur_callee B cx ASTACK ly2 S2 ly9 S9 W2 msB W9 ms9 E9 P N HCALL9
    (fun a Ha HEa => ltac:(pose proof (HE9 a HEa); unfold lf_cur_fp in Ha; unfold LS_P, LS_N, LLVMF_STK in *; lia))
    HcurB) as Hcur9.
  pose proof (d4_keep_pres F_R1 _ _ F_R1_saved HP9) as KP9.
  pose proof (d4_keep_trans F_R1 _ _ _ K3T KP9) as K9T.
  (* ---- +0xf8c .. +0xfbc: wk's and wa's shadow bytes := 0xf8, s10 := [s1 + 0x78], s7 := [s1 + 0xf0]; LF_tail ---- *)
  assert (HPC9 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + LR_f2)) by (rewrite Q1B, HBASE; reflexivity).
  pose proof HC9 as (HJ9 & Hfr9 & Hsv9 & Hhd9 & Hfs9 & Hsl9 & Hjbk9 & Hblk9 & Hdat9).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly9 S9 W9 (ms_mem ms9) md9 _ HB HJ9 Hfr9) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg /\ lf_SH cx fp mod 4 = 0).
  { rewrite HFS. assert (D1 : 4096 / 8 <= lf_F cx fp / 8) by (apply Z.div_le_mono; clia).
    assert (D2 : lf_F cx fp / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; clia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    pose proof (Z.div_mod (lf_F cx fp) 32 ltac:(clia)) as D. rewrite F32, Z.add_0_r in D.
    assert (Q : lf_F cx fp / 8 = 4 * (lf_F cx fp / 32)) by (rewrite D at 1; replace (32 * (lf_F cx fp / 32)) with
      ((4 * (lf_F cx fp / 32)) * 8) by clia; apply Z.div_mul; clia).
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. split; [clia|]. split; [clia|].
    rewrite Q. replace (2147450880 + 4 * (lf_F cx fp / 32)) with ((536862720 + lf_F cx fp / 32) * 4) by clia.
    apply Z_mod_mult. }
  pose proof Hsl9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SWA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & SG40 & _).
  kreg K9T 9 (9%bv : bv 5) T9. kreg K9T 19 (19%bv : bv 5) T19. kreg K9T 24 (24%bv : bv 5) T24.
  assert (R9_9 : getr regs9 9 = w64 (lf_sp1 cx)) by (rewrite T9; exact R9).
  assert (R19_9 : getr regs9 19 = w64 (lf_SH cx fp)) by (rewrite T19; exact R19).
  assert (R24_9 : getr regs9 24 = w64 (2 ^ 64 - 8)) by (rewrite T24; exact R24).
  clear HS SHOK.
  pose proof (f_entry fy cx fp W9 ms9 LR_f2 (lf_F cx fp + LO_WA) (LA_G_NL + 0x40000) R9_9 R19_9 Hlo
    ltac:(unfold LLVMF_STK in *; clia) (proj1 SHB) (proj1 (proj2 SHB)) (proj2 (proj2 SHB)) F4 Fc Fshp
    ltac:(unfold LO_WA; clia) ltac:(unfold LA_G_NL; lia) SWA SG40) as HS.
  unfold ms9. rewrite HPC9.
  change (ms_regs ms9) with regs9 in HS. change (ms_mem ms9) with mem9 in HS.
  set (E3 := Eimg (Ereg regs9 [Z_to_bv 64 (lf_F cx fp + LO_WA); Z_to_bv 64 (LA_G_NL + 0x40000)])) in HS.
  assert (HEI3 : img_env pa_val A_LIM E3) by apply Eimg_env.
  assert (EL3 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs9 r).
  { intros n r Hn Hr. unfold E3. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (EL3' : forall n, (n < A_TEXT)%nat ->
      ew E3 n = ew (Ereg regs9 [Z_to_bv 64 (lf_F cx fp + LO_WA); Z_to_bv 64 (LA_G_NL + 0x40000)]) n)
    by (intros n Hn; unfold E3; apply Eimg_low; exact Hn).
  assert (U19 : bv_unsigned (ew E3 19) = lf_SH cx fp)
    by (rewrite (EL3 19%nat 19%bv ltac:(lia) eq_refl), R19_9; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  assert (E332 : ew E3 32 = Z_to_bv 64 (lf_F cx fp + LO_WA))
    by (unfold E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs9 _ 0)).
  assert (E333 : ew E3 33 = Z_to_bv 64 (LA_G_NL + 0x40000))
    by (unfold E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs9 _ 1)).
  assert (E324 : ew E3 24 = Z_to_bv 64 (2 ^ 64 - 8)) by (rewrite (EL3 24%nat 24%bv ltac:(lia) eq_refl); exact R24_9).
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E3
    (mrestrict (w_H W9) (ms_mem (@mkst fy regs9 (Z_to_bv 64 (BASE + LR_f2)) mem9 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ9 as HJ9a.
  paj_run_to_tok RUNTO HS HJ9 SHOK (0, 0) LF_tail.
  { cbn [ss_mem f_ss].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base f_sh_rg base_val] in Ha. rewrite U19 in Ha.
      left. split; [|unfold LLVMF_STK, kHighMemBeg in *; clia]. right; right; right. exists LF_CID, fp.
      split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID / 8) with 128.
      unfold shadow_addr. rewrite <- HFS. clia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base f_sh_rg base_val] in Ha. rewrite U19 in Ha.
      left. split; [|unfold LLVMF_STK, kHighMemBeg in *; clia]. right; right; right. exists LF_CID, fp.
      split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID / 8) with 128.
      unfold shadow_addr. rewrite <- HFS. clia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base f_sl_rg base_val] in Ha. clia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base f_sl_rg base_val] in Ha. clia. }
  rename ms into msZ, HF into HFZ, HFr into HFrZ, HG into HGZ.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssZ := ssx) in HS end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdZ := mdx) in * end.
  assert (FdZ : m_fds mdZ = m_fds md9) by (subst mdZ; rewrite !lf_wvb_fds; reflexivity).
  assert (FsZ : m_fs mdZ = m_fs md9) by (subst mdZ; rewrite !lf_wvb_fs; reflexivity).
  set (X := fun a => lf_SH cx fp + 92 <= a mod 2 ^ 64 < lf_SH cx fp + 97 \/
                     lf_SH cx fp + 102 <= a mod 2 ^ 64 < lf_SH cx fp + 107).
  assert (KZ : kagree SEGS X (rdW W9 mem9) (rdW W9 (ms_mem msZ))).
  { apply (u_kagree_frame E3 (ss_mem (f_ss LR_f2)) _ _ X HFrZ). intros a (r & Hr & Hw). unfold X.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem f_ss In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base f_sh_rg f_sl_rg base_val] in Hw;
      [rewrite U19 in Hw; left; clia | rewrite U19 in Hw; right; clia | clia | clia]. }
  assert (HXr : forall a, 0 <= a < 2 ^ 64 -> X a -> lf_SH cx fp <= a < lf_SH cx fp + 128)
    by (intros a Ha HXa; unfold X in HXa; rewrite Z.mod_small in HXa by exact Ha; clia).
  destruct (r_shadow_keep SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
    X cx fp _ _ _ _ _ md mk kbs' mbs gbs T3 _ ly9 S9 W9 ms9 md9 msZ mdZ P N HB HJ9a Hfr9 KZ HGZ FdZ FsZ HXr
    Hsv9 Hhd9 Hsl9 Hcur9 Hjbk9 Hblk9 Hdat9) as (HsvZ & HhdZ & HslZ & HcurZ & HjbkZ & HblkZ & HdatZ).
  assert (RG0 : region_ok SEGS E3 (rdW W9 (ms_mem msZ)) (nth 0 (ss_mem ssZ) (f_sh_rg 0 0)))
    by exact (st_ok_pi_region_nth E3 ssZ (restrict (w_H W9) msZ) 0 _ HS eq_refl).
  assert (RG1 : region_ok SEGS E3 (rdW W9 (ms_mem msZ)) (nth 1 (ss_mem ssZ) (f_sh_rg 0 0)))
    by exact (st_ok_pi_region_nth E3 ssZ (restrict (w_H W9) msZ) 1 _ HS eq_refl).
  assert (Hc24 : bv_unsigned (sv_denot E3 (SOff 24 0)) mod 256 = 248).
  { rewrite (lf_sv_off E3 24 _ 0 E324) by lia. rewrite Z.add_0_r, Z_to_bv_unsigned. reflexivity. }
  assert (HfsZ : lf_fshadow cx fp W9 msZ LF_SH0).
  { apply (f_fsh_upd2 cx fp W9 ms9 msZ X SH_R LF_SH0 92 97 102 107 248 Hfs9 KZ); [reflexivity | |].
    - intros i0 Hi0 Hn1 Hn2. rewrite SH_R_len in Hi0. split.
      + unfold X. rewrite Z.mod_small by (unfold kHighMemBeg in *; clia). clia.
      + apply f_shr_out; lia.
    - intros i0 Hi0 Hin. rewrite SH_R_len in Hi0. split; [|apply f_sh0_wk; lia].
      destruct Hin as [Hin | Hin].
      + apply (u_byte_sv E3 (w_H W9) (ms_mem msZ) _ (lf_SH cx fp) (Z.of_nat i0) (SOff 24 0) 248 RG0).
        * cbn [nth ss_mem ssZ setpc YP09.r_base base_val]. exact U19.
        * assert (Hc : forall k, 92 <= k < 97 ->
              In (YP09.mkChunk k (CVal 1 (SOff 24 0))) (YP09.r_chunks (nth 0 (ss_mem ssZ) (f_sh_rg 0 0)))).
          { intros k Hk. cbn [nth ss_mem ssZ setpc YP09.r_chunks].
            assert (Hk' : k = 92 \/ k = 93 \/ k = 94 \/ k = 95 \/ k = 96) by lia.
            repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst k. cbn [In]. tauto. }
          apply Hc. lia.
        * exact Hc24.
      + apply (u_byte_sv E3 (w_H W9) (ms_mem msZ) _ (lf_SH cx fp) (Z.of_nat i0) (SOff 24 0) 248 RG1).
        * cbn [nth ss_mem ssZ setpc YP09.r_base base_val]. exact U19.
        * assert (Hc : forall k, 102 <= k < 107 ->
              In (YP09.mkChunk k (CVal 1 (SOff 24 0))) (YP09.r_chunks (nth 1 (ss_mem ssZ) (f_sh_rg 0 0)))).
          { intros k Hk. cbn [nth ss_mem ssZ setpc YP09.r_chunks].
            assert (Hk' : k = 102 \/ k = 103 \/ k = 104 \/ k = 105 \/ k = 106) by lia.
            repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst k. cbn [In]. tauto. }
          apply Hc. lia.
        * exact Hc24. }
  (* the frame's shadow is LF_SH0 again: the cut is ArmK.v's ak_cut; its counters re-set for operation i + 1 *)
  pose proof HjbkZ as (HkZ & _ & _ & _ & _ & _ & _ & HwlZ & HgiZ & _ & HblZ & _).
  assert (HCZ : ak_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 [(md, MD_SIZE); (mk, MK_SIZE)]
    (lf_ev i + 2 + 1 + 1) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) (k2 + 1 + 1)
    ly9 S9 W9 msZ mdZ)
    by exact (conj HJ9 (conj Hfr9 (conj HsvZ (conj HhdZ (conj HfsZ (conj HslZ (conj HjbkZ (conj HblkZ HdatZ)))))))).
  pose proof (ak_cut_counters SK B MT MS la_nul MT_LE cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ _ ly9 S9 W9 msZ mdZ
    (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD HCZ) as HCZ'.
  specialize (HCZ' ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia)
    (f_live_held cx md mk T3 ly9 S9 _ HgiZ HblZ)
    ltac:(unfold lf_wl, LF_WILD_OP in *; rewrite Z2Nat.inj_add by lia; cbn [Z.to_nat Pos.to_nat]; lia)).
  clear HCZ.
  destruct HCZ' as (HJZ & HFRZ & HSAVZ & HHDRZ & HFSHZ & HSLZ & HJBKZ' & HBLKZ & HDATAZ).
  (* the registers at the cut *)
  pose proof (d4_keep_run_pi fy W9 _ _ msZ regs9 _ F_R HS EL3' F_R_low ltac:(d4chk)) as KRZ.
  pose proof (d4_keep_trans F_R _ _ _ (f_keep_sub _ _ K9T) KRZ) as KAZ.
  kreg KAZ 2 (2%bv : bv 5) Z2. kreg KAZ 3 (3%bv : bv 5) Z3. kreg KAZ 4 (4%bv : bv 5) Z4.
  kreg KAZ 8 (8%bv : bv 5) Z8. kreg KAZ 9 (9%bv : bv 5) Z9. kreg KAZ 19 (19%bv : bv 5) Z19.
  kreg KAZ 21 (21%bv : bv 5) Z21. kreg KAZ 22 (22%bv : bv 5) Z22. kreg KAZ 24 (24%bv : bv 5) Z24.
  kreg KAZ 25 (25%bv : bv 5) Z25. kreg KAZ 27 (27%bv : bv 5) Z27.
  assert (Q26 : getr (ms_regs msZ) 26 = Z_to_bv 64 (lf_F cx fp + LO_WA)).
  { rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W9) E3 ssZ msZ 26%bv HS).
    replace (sr_get (ss_regs ssZ) 26%bv) with (SOff 32 0) by (vm_compute; reflexivity).
    cbn [sv_denot]. rewrite E332, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (Q23 : getr (ms_regs msZ) 23 = Z_to_bv 64 (LA_G_NL + 0x40000)).
  { rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W9) E3 ssZ msZ 23%bv HS).
    replace (sr_get (ss_regs ssZ) 23%bv) with (SOff 33 0) by (vm_compute; reflexivity).
    cbn [sv_denot]. rewrite E333, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  apply (HT cx fy fp (k2 + 1 + 1) ly9 S9 W9 msZ mdZ HB Hfx HJZ HFRZ).
  exists md, mk, P, N, kbs', mbs, gbs, T3.
  split; [exact Hi|].
  split; [exact (lf_shape_of_st_ok fy W9 _ _ msZ HS eq_refl)|].
  split; [split; [rewrite Z2; exact R2|]; split; [rewrite Z8; exact R8|]; split; [rewrite Z9; exact R9|];
          split; [rewrite Z3; exact R3 | rewrite Z4; exact R4]|].
  split; [split; [rewrite Z19; exact R19|]; split; [rewrite Z21; exact R21|];
          split; [rewrite Z22; exact R22|]; split; [rewrite Q23; reflexivity|];
          split; [rewrite Z24; exact R24|]; split; [rewrite Z25; exact R25|];
          split; [rewrite Q26; reflexivity | rewrite Z27; exact R27]|].
  split; [exact HSAVZ|]. split; [exact HHDRZ|]. split; [exact HFSHZ|]. split; [exact HSLZ|].
  split; [exact HcurZ|]. split; [exact HJBKZ'|]. split; [exact HBLKZ|]. split; [exact HDATAZ|].
  lia.
Qed.

End a.
