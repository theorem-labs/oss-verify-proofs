(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 463 of its 519 lines of code are new or changed and 348 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE BLOCKS PHASE of
   the walk, +0x494 .. +0x598 (0x82c68 .. 0x82d6c), against the cut interface lib/A/Prog/LLVMFuzzerTestOneInputDefs.v:

     +0x494 .. +0x4b4   the two callocs (LLVMFuzzerTestOneInputBlkCa.v bk_callocs)
     +0x4b4  bnez s6, +8 / j +0x1440       the model block is not NULL: refuted from the rule's 4096 <= res
     +0x4bc  bnez a0, +8 / j +0x1440       the marks block is not NULL: the same
     +0x4c4 .. +0x594                      the 26 constant spill slots of lf_slots (19 written here, 7 kept from
                                           the set-up), s9 := 0, s8 := -8, s5 := m + MD_N_MARK,
                                           s7 := g_nl + 0x40000; s6 = m, s3 = shadow(F), s10 = F + 0x20 and
                                           s11 = the shadow base are kept from +0x4b4 (bk_mid)
     +0x598  the loop head of operation 0

     lf_blk : forall POST, FROM POST (LH 0) -> FROM POST CA

   lf_lh_inv 0: the model and the marks block are the two fresh blocks, all zero (calloc), so model_wf, marks_wf,
   marks_are and nk_opened kbs <= 0 hold of the zero bytes (bl_model_wf0 .. by computation); lf_blocks is the two
   blocks' ledger membership (the rule's block equation), their separation and shadow (AR's laws at the state).
   The run writes only the spill window [s1 + 0x18, s1 + 0xf8), so every other memory clause of the cut is kept
   (LLVMFuzzerTestOneInputKeep.v); the slots are read off the runner's final spill region (bl_slot_of), and .str.1
   and the jump table are image objects 8 and 9 (LinkVals' object table, bl_obj).

   Section hypotheses (discharged by the image instance):
     LAWS, TB, HSEGS, LV, MT_LE, MT_OK;
     ACALLOC4W (the raw calloc rule, open item W1) and LF_TRACE_CALLOC (the two calloc sites' wild traces are in
     the universe: the depot count of the malloc depot shape, open item W1), both as in
     LLVMFuzzerTestOneInputBlkCa.v.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputExit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputBlkCa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the spill region at +0x4b4: the twelve slots the set-up left, the window the run writes *)
Definition bl_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_J18 (LS_N + 8) LS_J18 (LS_GNL40 + 8)
    [YP09.mkChunk LS_F (CVal 8 (SOff 32 0)); YP09.mkChunk LS_FK (CVal 8 (SOff 32 0));
     YP09.mkChunk LS_B1A0 (CVal 8 (SOff 32 LO_B1A0)); YP09.mkChunk LS_ODD (CVal 8 (SLit LA_ODD));
     YP09.mkChunk LS_B160 (CVal 8 (SOff 32 LO_B160)); YP09.mkChunk LS_WA (CVal 8 (SOff 32 LO_WA));
     YP09.mkChunk LS_B330 (CVal 8 (SOff 32 LO_B330)); YP09.mkChunk LS_B2E0 (CVal 8 (SOff 32 LO_B2E0));
     YP09.mkChunk LS_SHB (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk LS_F0 (CVal 8 (SOff 32 0));
     YP09.mkChunk LS_P (CVal 8 (SOff 33 0)); YP09.mkChunk LS_N (CVal 8 (SOff 34 0))].
Definition bl_ss0 : sstate :=
  mkSS LF_ca2_ra sr_atoms [bl_spill] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).

(* the values the run leaves: (x mod 8) + 3 and the shadow address x / 8 + SHADOW_OFF of x = v + c *)
Lemma bl_and7 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit 7)) (SLit 3)) = Z_to_bv 64 ((v + c) mod 8 + 3).
Proof.
  intros E n v c H Hv Hc. pose proof (Z.mod_pos_bound (v + c) 8 ltac:(lia)) as M.
  apply bv_eq. rewrite (unsigned_lit_small ((v + c) mod 8 + 3)) by lia.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit 7)) (SLit 3))))
    with (U E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit 7)) (SLit 3))).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia. rewrite (U_atom_off E n v c H Hv Hc), U_lit by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma bl_srl3 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SLit 2147450880)) =
  Z_to_bv 64 (shadow_of_addr SHADOW_OFF (v + c)).
Proof.
  intros E n v c H Hv Hc. pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)) as D0.
  pose proof (Z.div_le_upper_bound (v + c) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as D1.
  unfold shadow_of_addr, SHADOW_OFF.
  apply bv_eq. rewrite (unsigned_lit_small (2147450880 + (v + c) / 8)) by lia.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SLit 2147450880))))
    with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SLit 2147450880))).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, (U_atom_off E n v c H Hv ltac:(lia)), U_lit by lia.
  rewrite Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.

(* zero bytes, from the views calloc's rule states *)
Definition bl_zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).

Lemma bl_abytes_zero : forall segs H (mem : word -> option byte) p n, 0 <= p -> p + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> aview segs H mem (p + i) = Some 0) ->
  abytes segs (mrestrict H mem) p (bl_zeros n).
Proof.
  intros segs H mem p n Hp Hpn Hn Hz. unfold bl_zeros. split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
  specialize (Hz (Z.of_nat i) ltac:(lia)). unfold aview in Hz.
  destruct (mbyte segs (mrestrict H mem) (p + Z.of_nat i)) as [b|] eqn:Eb; cbn in Hz; [|discriminate].
  injection Hz as Hz. f_equal. apply bv_eq. rewrite Hz. reflexivity.
Qed.

Lemma bl_md_fields : md_n_req (bl_zeros MD_SIZE) = 0 /\ md_next (bl_zeros MD_SIZE) = 0 /\
  md_socket_errno (bl_zeros MD_SIZE) = 0 /\ md_send_errno (bl_zeros MD_SIZE) = 0 /\
  md_n_mark (bl_zeros MD_SIZE) = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma bl_mk_n : mk_n (bl_zeros MK_SIZE) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bl_model_wf0 : model_wf (bl_zeros MD_SIZE).
Proof.
  pose proof bl_md_fields as (A1 & A2 & A3 & A4 & A5). unfold model_wf, model_marks_wf, slots_terminated.
  rewrite A1, A2, A3, A4, A5. unfold NL_SENT_MAX, MARKS_MAX.
  repeat split; try lia; intros i Hi; lia.
Qed.
Lemma bl_marks_wf0 : marks_wf (bl_zeros MK_SIZE).
Proof. unfold marks_wf, slots_terminated. rewrite bl_mk_n. unfold MARKS_MAX. repeat split; try lia; intros i Hi; lia. Qed.
Lemma bl_marks_are0 : marks_are (bl_zeros MK_SIZE) (bl_zeros MD_SIZE).
Proof. unfold marks_are. split; vm_compute; reflexivity. Qed.

(* a spill slot from the final state's spill region (Head.v hd_slot_of) *)
Lemma bl_slot_of : forall {rc : YM05.RunCeil} {PI : PAImg link_listing} (fy : YK11.FPState) (W : world pa_segs)
    EB ss ms cx (i : nat) r off e v,
  st_ok_pi (fx := fy) pa_segs pa_val EB ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> r_base r = Some 9%nat -> bv_unsigned (ew EB 9) = lf_sp1 cx ->
  In (YP09.mkChunk off (CVal 8 e)) (r_chunks r) -> sv_denot EB e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  lf_slot cx W ms off v.
Proof.
  intros rc PI fy W EB ss ms cx i r off e v HS Hn Hb H9 Hc He Hv.
  pose proof (st_ok_pi_region_nth EB ss _ i r HS Hn) as (_ & _ & _ & Hch).
  rewrite Forall_forall in Hch. pose proof (Hch _ Hc) as Hok.
  assert (Eb : base_val EB (r_base r) = lf_sp1 cx) by (rewrite Hb; exact H9). rewrite Eb in Hok.
  pose proof (val_of_chunk_ok pa_segs EB _ (lf_sp1 cx) off 8 e v Hok He ltac:(cbn; lia) ltac:(cbn; lia)) as Hvm.
  unfold lf_slot, lf_at. exact (rdword_of_val_mem pa_segs (w_H W) (ms_mem ms) _ v Hvm Hv).
Qed.

Ltac bl_inch := cbn [r_chunks In]; repeat (first [left; reflexivity | right]).
(* a slot of the final spill region: its chunk (found by unification), its value, its range *)
Ltac bl_sl SL := eapply SL; [cbn [In]; repeat (first [left; reflexivity | right]) | |].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Variable LF_CALLOC_RA0 : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis ACALLOC4W : forall fy : YK11.FPState,
  acalloc04_rule_w (fx := fy) SK SEGS B MT (pa_sigma LS___interceptor_trampoline_calloc) LF_CALLOC_RA0 8856 2192.
Hypothesis LF_TRACE_CALLOC : lf_trace_calloc B LF_CALLOC_RA0.

#[local] Notation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* an image object's address, as the run's auipc atoms carry it (img_env and LinkVals' object table) *)
Lemma bl_obj : forall E i, img_env pa_val A_LIM E -> (i < link_nobj)%nat -> (A_OBJ i < A_LIM)%nat ->
  0 <= link_obj i < 2 ^ 64 -> sv_denot E (SOff (A_OBJ i) 0) = Z_to_bv 64 (link_obj i).
Proof.
  intros E i HE Hi Hl Hb. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)), (lv_obj LV i Hi). reflexivity.
Qed.

Lemma bl_final : forall POST, FROM POST (lf_lh_inv B MT MS la_nul LF_MO_SET LF_MO_OP 0) ->
  forall cx fy fp k2 ly S W ms mdl T3 md mk kbs, BASEF cx -> @BoxBase.fxr fx fy ->
  bk_mid SK B MT MS la_nul cx fy fp k2 ly S W ms mdl T3 md mk kbs -> SRr SEGS W (mkCfg ms mdl) (POST cx).
Proof.
  intros POST HLH cx fy fp k2 ly S W ms mdl T3 md mk kbs HB Hfx
    (Hsh & Hcore & R18 & R19 & R20 & R22 & R10 & R26 & R27 & Hmd4 & Hmk4 & HC & Hwf & Ho & Hmi & Hoc & Hop0).
  pose proof HC as (HJ & Hfr & Hsv & Hhd & Hfs & HSL & Hcur & Hjbk & Hdat & Hown).
  pose proof HJ as HJ0.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof HB as (_ & _ & HGX & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W
    (ms_mem ms) mdl (k2 + 2) HB HJ) as (H16 & Hceil & _ & Hshi & Hs47 & Hpres & HAR).
  pose proof (lf_sp1_le cx) as (SP1 & SP2). pose proof (ex_sp1 cx) as SP3.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (S1r : alloc_ceiling <= lf_sp1 cx) by (unfold LLVMF_STK, LF_MFRAME in *; lia).
  assert (S1u : bv_unsigned (getr (ms_regs ms) 9) = lf_sp1 cx).
  { rewrite C9. unfold w64. apply unsigned_lit_small. unfold LF_MFRAME in *. lia. }
  pose proof Hcur as (HcP & HcN & _).
  set (F := lf_F cx fp) in *.
  assert (SV : forall off v, In (off, v) (bk_slotvals cx fp) -> lf_slot cx W ms off v) by exact HSL.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) (ms_mem ms)) HcP) as RP.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) (ms_mem ms)) HcN) as RN.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) (ms_mem ms))
    (SV LS_F F ltac:(unfold bk_slotvals; cbn [In]; tauto))) as RF.
  rewrite (lf_shape_eta fy LF_ca2_ra ms Hsh).
  set (E := Eimg (Ereg (ms_regs ms) [w64 F; w64 (c_p cx); w64 (c_n cx)])).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms) r)
    by (intros n r Hr; subst E; exact (ew_Eimg_Ereg_nat _ _ n r Hr)).
  assert (E32 : ew E 32 = w64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (E33 : ew E 33 = w64 (c_p cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (E34 : ew E 34 = w64 (c_n cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (E9 : ew E 9 = getr (ms_regs ms) 9) by exact (EREG 9%nat 9%bv eq_refl).
  pose proof (ex_env_agree (ms_regs ms) [w64 F; w64 (c_p cx); w64 (c_n cx)]) as HA. fold E in HA.
  assert (HinF : In (LF_CID, fp) (frames S)) by (rewrite Hfr; left; reflexivity).
  pose proof Hjbk as (Hkev & Hbb & Hfa & _ & Hfd & Hfs3 & _ & Hwl & Hgi & _ & Hbl & Hinc & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ LF_CID fp HAR HinF) as (HF4096 & HFceil & _).
  pose proof LF_frame_slot as (FB & _).
  assert (EF : frame_addr ly LF_CID fp = F) by (unfold F, lf_F; apply Hfa).
  rewrite EF, FB in HFceil. rewrite EF in HF4096.
  assert (SOF : forall c, 0 <= c <= 0x330 -> sv_denot E (SOff 32 c) = Z_to_bv 64 (F + c))
    by (intros c Hc; exact (lf_sv_off E 32 F c ltac:(exact E32) ltac:(lia) ltac:(lia))).
  assert (SVc : forall off v e, In (off, v) (bk_slotvals cx fp) -> sv_denot E e = Z_to_bv 64 v ->
    YP09.chunk_ok SEGS E (rdW W (ms_mem ms)) (lf_sp1 cx) (YP09.mkChunk off (CVal 8 e)))
    by (intros off v e Hin He; exact (ex_chunk cx W ms E off e v (SV off v Hin) He)).
  assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E bl_ss0
    (restrict (w_H W) (@mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + LF_ca2_ra)) (ms_mem ms) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor; [|constructor].
      unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks bl_spill base_val]. rewrite E9, S1u.
      split; [unfold LS_J18, LS_N, LLVMF_STK, LF_MFRAME in *; lia|].
      split; [unfold LS_J18, LS_N, LLVMF_STK, LF_MFRAME in *; lia|]. split.
      + intros o Ho'. apply (apresent_writable SEGS). apply Hpres. unfold LS_J18, LS_GNL40, LLVMF_STK, LF_MFRAME in *. lia.
      + repeat apply Forall_cons; try apply Forall_nil.
        * apply (SVc LS_F F); [unfold bk_slotvals; cbn [In]; tauto | rewrite SOF by lia; f_equal; lia].
        * apply (SVc LS_FK F); [unfold bk_slotvals; cbn [In]; tauto | rewrite SOF by lia; f_equal; lia].
        * apply (SVc LS_B1A0 (F + LO_B1A0)); [unfold bk_slotvals; cbn [In]; tauto | apply SOF; unfold LO_B1A0; lia].
        * apply (SVc LS_ODD LA_ODD); [unfold bk_slotvals; cbn [In]; tauto | reflexivity].
        * apply (SVc LS_B160 (F + LO_B160)); [unfold bk_slotvals; cbn [In]; tauto | apply SOF; unfold LO_B160; lia].
        * apply (SVc LS_WA (F + LO_WA)); [unfold bk_slotvals; cbn [In]; tauto | apply SOF; unfold LO_WA; lia].
        * apply (SVc LS_B330 (F + LO_B330)); [unfold bk_slotvals; cbn [In]; tauto | apply SOF; unfold LO_B330; lia].
        * apply (SVc LS_B2E0 (F + LO_B2E0)); [unfold bk_slotvals; cbn [In]; tauto | apply SOF; unfold LO_B2E0; lia].
        * apply (SVc LS_SHB SHADOW_OFF); [unfold bk_slotvals; cbn [In]; tauto | reflexivity].
        * apply (SVc LS_F0 F); [unfold bk_slotvals; cbn [In]; tauto | rewrite SOF by lia; f_equal; lia].
        * apply (ex_chunk cx W ms E LS_P (SOff 33 0) (c_p cx) HcP).
          rewrite (lf_sv_off E 33 (c_p cx) 0 ltac:(exact E33) ltac:(lia) ltac:(lia)). f_equal; lia.
        * apply (ex_chunk cx W ms E LS_N (SOff 34 0) (c_n cx) HcN).
          rewrite (lf_sv_off E 34 (c_n cx) 0 ltac:(exact E34) ltac:(lia) ltac:(lia)). f_equal; lia.
    - cbn. tauto.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9, S1u.
      split; [unfold LF_MFRAME, LLVMF_STK in *; lia|]. split; [|unfold LF_MFRAME, LLVMF_STK in *; lia].
      unfold lf_sp1, lf_sp1_of. rewrite Z.mul_comm. change (2 ^ 5) with 32. apply Z_mod_mult. }
  (* the registers the run reads as literals: s2 = g_nl, s4 = 0x2000, s11 = the shadow base *)
  pose proof (st_ok_pi_set_reg E bl_ss0 _ 18%bv (SLit LA_G_NL) HS
    ltac:(intros Habs; apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; exact R18)) as HS1.
  clear HS. cbn [sr_set] in HS1.
  lazymatch type of HS1 with st_ok_pi _ _ _ ?ss1 _ =>
    pose proof (st_ok_pi_set_reg E ss1 _ 20%bv (SLit 0x2000) HS1
      ltac:(intros Habs; apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs)
      ltac:(cbn [sv_denot ms_regs restrict mkst]; exact R20)) as HS2 end.
  clear HS1.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
    pose proof (st_ok_pi_set_reg E ss2 _ 27%bv (SLit SHADOW_OFF) HS2
      ltac:(intros Habs; apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs)
      ltac:(cbn [sv_denot ms_regs restrict mkst]; exact R27)) as HS end.
  clear HS2. clearbody E.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W) (ms_mem (@mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + LF_ca2_ra)) (ms_mem ms) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (E22 : ew E 22 = Z_to_bv 64 md) by (rewrite (EREG 22%nat 22%bv eq_refl), R22; reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 mk) by (rewrite (EREG 10%nat 10%bv eq_refl), R10; reflexivity).
  pose proof Hown (md, MD_SIZE) ltac:(cbn [In]; tauto) as (Hmd & Hmdc & HmdT & Hmdz).
  pose proof Hown (mk, MK_SIZE) ltac:(cbn [In]; tauto) as (Hmk & Hmkc & HmkT & Hmkz).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmd) as (Hmd16 & _ & Hmdc' & Hmdapp & Hmdpres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmk) as (Hmk16 & _ & Hmkc' & Hmkapp & Hmkpres & _).
  change (req_size MD_SIZE) with MD_SIZE in *. change (req_size MK_SIZE) with MK_SIZE in *.
  (* +0x4b4 bnez s6: taken, md <> 0 *)
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  2: { exfalso. rewrite branch_ne_U, (U_atom E 22 md E22), U_lit in Hc by (unfold MD_SIZE in *; lia).
       apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia. }
  (* +0x4bc bnez a0: taken, mk <> 0 *)
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    cbn [r_base r_wlo r_whi base_val bl_spill]. rewrite E9, S1u. intros a Ha.
    left. split; [left; unfold LS_J18, LS_GNL40, LLVMF_STK, LF_MFRAME in *; lia | lia]. }
  rename ms0 into msA, HF into HFA, HFr into HFrA, HG into HGA, Hc into Hc1.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  2: { exfalso. rewrite branch_ne_U in Hc.
       lazymatch type of Hc with context [U ?E' (SOff 10 0)] =>
         assert (E10' : ew E' 10 = Z_to_bv 64 mk) by (repeat rewrite ew_ewset_other by lia; exact E10);
         rewrite (U_atom E' 10 mk E10'), U_lit in Hc by (unfold MK_SIZE in *; lia) end.
       apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia. }
  (* +0x4c4 .. +0x594, to the loop head *)
  rename Hc into Hc2.
  lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
    assert (E9' : ew E' 9 = getr (ms_regs ms) 9) by (repeat rewrite ew_ewset_other by lia; exact E9) end.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LF_lh.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    cbn [r_base r_wlo r_whi base_val bl_spill]. rewrite E9', S1u. intros a Ha.
    left. split; [left; unfold LS_J18, LS_GNL40, LLVMF_STK, LF_MFRAME in *; lia | lia]. }
  rename ms0 into msB, HF into HFB, HFr into HFrB, HG into HGB.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds mdl) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs mdl) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  (* ---- the memory the run changed: the spill window only ---- *)
  set (Y := fun a => lf_sp1 cx + LS_J18 <= a < lf_sp1 cx + LS_GNL40 + 8).
  assert (KA : kagree SEGS (fun a => Y (a mod 2 ^ 64)) (rdW W (ms_mem ms)) (rdW W (ms_mem msA))).
  { apply (lf_frame_kagree _ _ _ _ Y HFrA). intros a _ (r & Hi & Hr). cbn in Hi.
    destruct Hi as [<- | []]. cbn [bl_spill r_base r_wlo r_whi base_val] in Hr.
    lazymatch type of Hr with context [ew ?E0 9] =>
      assert (EE : ew E0 9 = getr (ms_regs ms) 9) by (repeat rewrite ew_ewset_other by lia; exact E9) end.
    rewrite EE, S1u in Hr. unfold Y. unfold LS_J18, LS_GNL40 in *. lia. }
  assert (KB : kagree SEGS (fun a => Y (a mod 2 ^ 64)) (rdW W (ms_mem msA)) (rdW W (ms_mem msB))).
  { apply (lf_frame_kagree _ _ _ _ Y HFrB). intros a _ (r & Hi & Hr). cbn in Hi.
    destruct Hi as [<- | []]. cbn [bl_spill r_base r_wlo r_whi base_val] in Hr.
    lazymatch type of Hr with context [ew ?E0 9] =>
      assert (EE : ew E0 9 = getr (ms_regs ms) 9) by (repeat rewrite ew_ewset_other by lia; exact E9) end.
    rewrite EE, S1u in Hr. unfold Y. unfold LS_J18, LS_GNL40 in *. lia. }
  assert (K : kagree SEGS (fun a => Y (a mod 2 ^ 64)) (rdW W (ms_mem ms)) (rdW W (ms_mem msB)))
    by (intros a Ha; rewrite (KB a Ha); exact (KA a Ha)).
  assert (GR : mem_grows (rdW W (ms_mem ms)) (rdW W (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
  assert (XL : forall a, 0 <= a < alloc_ceiling -> ~ Y (a mod 2 ^ 64)).
  { intros a Ha. rewrite Z.mod_small by lia. unfold Y, LS_J18, LS_GNL40. lia. }
  assert (XS : forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> ~ Y (a mod 2 ^ 64)).
  { intros a Ha. pose proof alloc_ceiling_value as (_ & A4096).
    rewrite Z.mod_small by (unfold LF_MFRAME in *; lia). unfold Y, LS_J18, LS_GNL40, LF_MFRAME in *. lia. }
  assert (LOWF : forall a, (lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_jbk_fp MS la_nul cx T3 a \/
      lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> 0 <= a < alloc_ceiling)
    by (intros a Ha; exact (lf_cut_fp_low SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp
          (k2 + 2) ly S W (ms_mem ms) mdl _ _ _ _ ms mdl md mk T3 _ a HB HJ0 HinF Hjbk Hmd Hmk Ha)).
  (* ---- the blocks and the data before the run ---- *)
  assert (Hpin : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))).
  { pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & Hpin0 & _).
    intros Hcn0; destruct Hpin0 as [(Hz & _) | (_ & Hi)]; [lia | exact Hi]. }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly S W
              (ms_mem ms) mdl (k2 + 2) HB HJ0).
  assert (APB : forall p n, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B (c_ly cx) (c_S cx)) ->
    0 < c_n cx -> apart p n (c_p cx) (c_n cx)).
  { intros p n Hb Hnc Hcn.
    assert (Hne : (p, n) <> (c_p cx, c_n cx)) by (intros Heq; apply Hnc; rewrite Heq; exact (Hpin Hcn)).
    pose proof (ex_blk_apart B LAWS ly S W (ms_mem ms) mdl _ _ HAR Hb (HPB Hcn) Hne) as D.
    unfold zdisjoint, apart in *. cbn [fst snd] in D.
    assert (R1 : n <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]).
    assert (R2 : c_n cx <= req_size (c_n cx))
      by (unfold req_size; destruct (c_n cx =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]).
    lia. }
  pose proof (blk_off_imgP B ly S W (ms_mem ms) mdl md MD_SIZE HAR Hmd) as OFFmd.
  pose proof (blk_off_imgP B ly S W (ms_mem ms) mdl mk MK_SIZE HAR Hmk) as OFFmk.
  change (req_size MD_SIZE) with MD_SIZE in OFFmd. change (req_size MK_SIZE) with MK_SIZE in OFFmk.
  assert (Hblk0 : lf_blocks B cx md mk T3 ly S (rdW W (ms_mem ms))).
  { unfold lf_blocks.
    split; [exact Hmd|]. split; [exact Hmk|]. split; [exact Hmdc|]. split; [exact Hmkc|].
    split; [exact HmdT|]. split; [exact HmkT|]. split; [exact Hmd16|]. split; [exact Hmk16|].
    split; [exact OFFmd|]. split; [exact OFFmk|].
    split.
    { assert (Hne : (md, MD_SIZE) <> (mk, MK_SIZE)) by (intros Heq; injection Heq as _ E2; unfold MD_SIZE, MK_SIZE in E2; lia).
      pose proof (ex_blk_apart B LAWS ly S W (ms_mem ms) mdl _ _ HAR Hmd Hmk Hne) as D.
      unfold zdisjoint, apart in *. cbn [fst snd] in D. change (req_size MD_SIZE) with MD_SIZE in D.
      change (req_size MK_SIZE) with MK_SIZE in D. lia. }
    split; [exact (APB md MD_SIZE Hmd Hmdc)|]. split; [exact (APB mk MK_SIZE Hmk Hmkc)|].
    split; [rewrite ard_aview; eapply range_addressable_of_block;
            [eassumption | eassumption | exact Hmd | lia | change (req_size MD_SIZE) with MD_SIZE; lia]|].
    split; [rewrite ard_aview; eapply range_addressable_of_block;
            [eassumption | eassumption | exact Hmk | lia | change (req_size MK_SIZE) with MK_SIZE; lia]|].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hmdapp, Hmkapp.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. split; lia. }
  assert (Hdat0 : lf_data cx md mk kbs (bl_zeros MD_SIZE) (bl_zeros MK_SIZE) (rdW W (ms_mem ms))).
  { pose proof Hdat as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    assert (WR : forall p n, In (p, n) (ablocks B ly S) -> awrange SEGS (rdW W (ms_mem ms)) p n).
    { intros p n Hb i Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & _ & _ & _ & Hp & _).
      destruct (Hp (p + i) ltac:(unfold req_size; destruct (n =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]))
        as (Hpr & _).
      exact (apresent_writable SEGS (w_H W) (ms_mem ms) (p + i) Hpr). }
    unfold lf_data.
    split; [exact D1|]. split; [exact Hwf|]. split; [exact D2|]. split; [exact Ho|]. split; [exact Hmi|].
    split; [exact Hoc|].
    split.
    { split; [|unfold bl_zeros; rewrite repeat_length; unfold MD_SIZE; lia]. split.
      - apply bl_abytes_zero; [lia | unfold MD_SIZE in *; lia | unfold MD_SIZE; lia|]. exact Hmdz.
      - unfold bl_zeros. rewrite repeat_length, Z2Nat.id by (unfold MD_SIZE; lia). exact (WR _ _ Hmd). }
    split; [exact bl_model_wf0|].
    split.
    { split; [|unfold bl_zeros; rewrite repeat_length; unfold MK_SIZE; lia]. split.
      - apply bl_abytes_zero; [lia | unfold MK_SIZE in *; lia | unfold MK_SIZE; lia|]. exact Hmkz.
      - unfold bl_zeros. rewrite repeat_length, Z2Nat.id by (unfold MK_SIZE; lia). exact (WR _ _ Hmk). }
    split; [exact bl_marks_wf0|]. split; [exact bl_marks_are0|].
    exact (conj D3 (conj D4 (conj D5 (conj D6 (conj D7 D8))))). }
  (* ---- the cut's memory clauses at the loop head ---- *)
  assert (Hsv' : lf_saved cx W msB)
    by (apply (lf_saved_keep _ cx W ms W msB K); [intros a Ha; apply XS; exact Ha | exact Hsv]).
  assert (Hhd' : lf_header cx fp W msB)
    by (apply (lf_header_keep _ cx fp W ms W msB K); [intros a Ha; apply XL, LOWF; left; exact Ha | exact Hhd]).
  assert (Hfs' : lf_fshadow cx fp W msB LF_SH0).
  { apply (lf_fshadow_keep _ cx fp W ms W msB LF_SH0 K); [|exact Hfs].
    intros a Ha. apply XL, LOWF. right; left. rewrite LF_SH0_len in Ha. exact Ha. }
  assert (Hblk' : lf_blocks B cx md mk T3 ly S (rdW W (ms_mem msB))).
  { apply (lf_blocks_keep B _ _ _ cx md mk T3 ly S K); [|exact Hblk0].
    intros a Ha. apply XL, LOWF. right; right; right; left. exact Ha. }
  assert (Hdat' : lf_data cx md mk kbs (bl_zeros MD_SIZE) (bl_zeros MK_SIZE) (rdW W (ms_mem msB))).
  { apply (lf_data_keep _ _ _ cx md mk kbs _ _ K (wcarry_on_grows _ _ _ GR)); [|exact Hdat0].
    intros a Ha. apply XL, LOWF. right; right; right; right. exact Ha. }
  assert (Hjbk' : lf_jbk B MT MS la_nul cx fp (k2 + 2) (lf_ev 0) (lf_mo LF_MO_SET LF_MO_OP 0) (lf_wl 0) LF_LIVE_HELD
                    ly S W msB md4 T3 [(md, MD_SIZE); (mk, MK_SIZE)]).
  { eapply lf_jbk_restate; [exact MT_LE | | | | | | | ].
    - apply (lf_jbk_keep B MT MS la_nul _ cx fp (k2 + 2) 2 0 0%nat (MD_SIZE + MK_SIZE) ly S W ms mdl T3 _ W msB md4 K Fd Fs);
        [|exact Hjbk].
      intros a Ha. apply XL, LOWF. right; right; left. exact Ha.
    - exact Hfa.
    - unfold lf_ev, LF_EV_SET, LF_EV_OP. lia.
    - unfold LF_LIVE_HELD, AMF_BLOCK. lia.
    - unfold lf_wl. cbn. lia.
    - destruct Hbl as (D & HT & HP). exists D. split; [exact HT|]. eapply perm_trans; [exact HP|].
      apply perm_swap.
    - exact Hinc. }
  (* ---- the registers and the spill slots ---- *)
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite E9; exact S1u).
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms) r)
    by (intros r Hr; exact (lf_reg_atom fy W E ssB msB _ r HS HA Hr)).
  assert (RV : forall (r : bv 5) e, sr_get (ss_regs ssB) r = e -> getr (ms_regs msB) r = sv_denot E e)
    by (intros r e He; rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W) E ssB msB r HS), He; reflexivity).
  assert (Md : 0 <= md /\ md + MD_SIZE < 2 ^ 47) by (unfold MD_SIZE in *; lia).
  assert (SLOT : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (r_chunks (nth 0 (ss_mem ssB) bl_spill)) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lf_slot cx W msB off v).
  { intros off e v Hin He Hv.
    exact (bl_slot_of fy W E ssB msB cx 0%nat _ off e v HS eq_refl eq_refl U9 Hin He Hv). }
  assert (A7 : forall c, 0 <= c <= MD_SIZE ->
    sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 22 c) (SLit 7)) (SLit 3)) = Z_to_bv 64 ((md + c) mod 8 + 3))
    by (intros c Hc; apply bl_and7; [exact E22 | lia | unfold MD_SIZE in *; lia]).
  assert (S3 : forall c, 0 <= c <= MD_SIZE ->
    sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 c) (SLit 3)) (SLit 2147450880)) =
    Z_to_bv 64 (shadow_of_addr SHADOW_OFF (md + c)))
    by (intros c Hc; apply bl_srl3; [exact E22 | lia | unfold MD_SIZE in *; lia]).
  assert (OF : forall c, 0 <= c <= MD_SIZE -> sv_denot E (SOff 22 c) = Z_to_bv 64 (md + c))
    by (intros c Hc; exact (lf_sv_off E 22 md c E22 ltac:(lia) ltac:(unfold MD_SIZE in *; lia))).
  assert (SHB : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64).
  { intros x Hx. unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
  assert (Mk : 0 <= mk /\ mk + MK_SIZE < 2 ^ 47) by (unfold MK_SIZE in *; lia).
  assert (FL : 0 <= F /\ F + 1024 < 2 ^ 47) by lia.
  assert (NC : 0 <= c_n cx) by (pose proof Hcur as (_ & _ & (q0 & Hq0 & _)); lia).
  apply (HLH cx fy fp (k2 + 2) ly S W msB md4 HB Hfx HJ Hfr).
  exists md, mk, (c_p cx), (c_n cx), kbs, (bl_zeros MD_SIZE), (bl_zeros MK_SIZE), T3.
  split; [lia|].
  split.
  { pose proof (lf_shape_of_st_ok fy W E ssB msB HS eq_refl) as SH.
    replace (ss_pc ssB) with LF_lh in SH by (vm_compute; reflexivity). exact SH. }
  split.
  { unfold lf_core. rewrite !KR by (vm_compute; reflexivity). exact Hcore. }
  split.
  { unfold lf_lregs.
    split; [rewrite KR by (vm_compute; reflexivity); exact R19|].
    split; [rewrite (RV 21%bv (SOff 22 8852)) by (vm_compute; reflexivity);
            rewrite OF by (unfold MD_SIZE; lia); reflexivity|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
    split; [rewrite (RV 23%bv (SLit 6408896)) by (vm_compute; reflexivity); reflexivity|].
    split; [rewrite (RV 24%bv (SLit 18446744073709551608)) by (vm_compute; reflexivity); reflexivity|].
    split; [rewrite (RV 25%bv (SLit 0)) by (vm_compute; reflexivity); reflexivity|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
    rewrite (RV 27%bv (SLit 2147450880)) by (vm_compute; reflexivity); reflexivity. }
  split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|].
  assert (CH : r_chunks (nth 0 (ss_mem ssB) bl_spill) =
    [YP09.mkChunk 152 (CVal 8 (SOff 22 8852)); YP09.mkChunk 240 (CVal 8 (SLit 6408896));
     YP09.mkChunk 232 (CVal 8 (SOff 22 0)); YP09.mkChunk 208 (CVal 8 (SOff 22 8336));
     YP09.mkChunk 24 (CVal 8 (SAlu ALU_ADD (SAlu ALU_AND (SOff 22 8336) (SLit 7)) (SLit 3)));
     YP09.mkChunk 160 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 8336) (SLit 3)) (SLit 2147450880)));
     YP09.mkChunk 32 (CVal 8 (SAlu ALU_ADD (SAlu ALU_AND (SOff 22 8) (SLit 7)) (SLit 3)));
     YP09.mkChunk 168 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 8) (SLit 3)) (SLit 2147450880)));
     YP09.mkChunk 40 (CVal 8 (SAlu ALU_ADD (SAlu ALU_AND (SOff 22 4) (SLit 7)) (SLit 3)));
     YP09.mkChunk 176 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 4) (SLit 3)) (SLit 2147450880)));
     YP09.mkChunk 88 (CVal 8 (SOff 22 8340)); YP09.mkChunk 184 (CVal 8 (SOff 250 0));
     YP09.mkChunk 96 (CVal 8 (SOff 249 0)); YP09.mkChunk 192 (CVal 8 (SLit 6417088));
     YP09.mkChunk 216 (CVal 8 (SOff 22 8)); YP09.mkChunk 224 (CVal 8 (SOff 22 4));
     YP09.mkChunk 48 (CVal 8 (SAlu ALU_ADD (SAlu ALU_AND (SOff 22 0) (SLit 7)) (SLit 3)));
     YP09.mkChunk 200 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SLit 2147450880)));
     YP09.mkChunk 144 (CVal 8 (SOff 10 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0));
     YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 72 (CVal 8 (SOff 32 416));
     YP09.mkChunk 80 (CVal 8 (SLit 661344)); YP09.mkChunk 104 (CVal 8 (SOff 32 352));
     YP09.mkChunk 120 (CVal 8 (SOff 32 32)); YP09.mkChunk 128 (CVal 8 (SOff 32 816));
     YP09.mkChunk 136 (CVal 8 (SOff 32 736)); YP09.mkChunk 248 (CVal 8 (SLit 2147450880));
     YP09.mkChunk 272 (CVal 8 (SOff 32 0)); YP09.mkChunk 280 (CVal 8 (SOff 33 0));
     YP09.mkChunk 288 (CVal 8 (SOff 34 0))]) by (vm_compute; reflexivity).
  rewrite CH in SLOT. clear CH.
  assert (OBJ8 : sv_denot E (SOff 249 0) = Z_to_bv 64 LA_STR1).
  { change 249%nat with (A_OBJ 8). assert (V : link_obj 8 = LA_STR1) by (vm_compute; reflexivity).
    rewrite (bl_obj E 8 HEI); [rewrite V; reflexivity | unfold link_nobj; lia | unfold A_OBJ, A_LIM; lia
                              | rewrite V; unfold LA_STR1; lia]. }
  assert (OBJ9 : sv_denot E (SOff 250 0) = Z_to_bv 64 LA_JT).
  { change 250%nat with (A_OBJ 9). assert (V : link_obj 9 = LA_JT) by (vm_compute; reflexivity).
    rewrite (bl_obj E 9 HEI); [rewrite V; reflexivity | unfold link_nobj; lia | unfold A_OBJ, A_LIM; lia
                              | rewrite V; unfold LA_JT; lia]. }
  assert (OK10 : sv_denot E (SOff 10 0) = Z_to_bv 64 mk)
    by (rewrite (lf_sv_off E 10 mk 0 E10) by (unfold MK_SIZE in *; lia); rewrite Z.add_0_r; reflexivity).
  assert (P33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (c_p cx))
    by (rewrite (lf_sv_off E 33 (c_p cx) 0 ltac:(exact E33)) by lia; rewrite Z.add_0_r; reflexivity).
  assert (N34 : sv_denot E (SOff 34 0) = Z_to_bv 64 (c_n cx))
    by (rewrite (lf_sv_off E 34 (c_n cx) 0 ltac:(exact E34)) by lia; rewrite Z.add_0_r; reflexivity).
  split.
  { unfold lf_slots.
    split; [bl_sl SLOT; [rewrite A7 by (unfold MD_SIZE; lia); reflexivity
                        | pose proof (Z.mod_pos_bound (md + MD_N_REQ) 8 ltac:(lia)); lia]|].
    split; [bl_sl SLOT; [rewrite A7 by (unfold MD_SIZE; lia); reflexivity
                        | pose proof (Z.mod_pos_bound (md + MD_NEXT) 8 ltac:(lia)); lia]|].
    split; [bl_sl SLOT; [rewrite A7 by (unfold MD_SIZE; lia); reflexivity
                        | pose proof (Z.mod_pos_bound (md + MD_SEND_ERRNO) 8 ltac:(lia)); lia]|].
    split; [bl_sl SLOT; [rewrite A7 by (unfold MD_SIZE; lia); rewrite Z.add_0_r; reflexivity
                        | pose proof (Z.mod_pos_bound md 8 ltac:(lia)); lia]|].
    split; [bl_sl SLOT; [rewrite SOF by lia; rewrite Z.add_0_r; reflexivity | lia]|].
    split; [bl_sl SLOT; [rewrite SOF by lia; rewrite Z.add_0_r; reflexivity | lia]|].
    split; [bl_sl SLOT; [rewrite SOF by (unfold LO_B1A0; lia); reflexivity | unfold LO_B1A0; lia]|].
    split; [bl_sl SLOT; [reflexivity | unfold LA_ODD; lia]|].
    split; [bl_sl SLOT; [rewrite OF by (unfold MD_SIZE; lia); reflexivity | unfold MD_MARK, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [exact OBJ8 | unfold LA_STR1; lia]|].
    split; [bl_sl SLOT; [rewrite SOF by (unfold LO_B160; lia); reflexivity | unfold LO_B160; lia]|].
    split; [bl_sl SLOT; [rewrite SOF by (unfold LO_WA; lia); reflexivity | unfold LO_WA; lia]|].
    split; [bl_sl SLOT; [rewrite SOF by (unfold LO_B330; lia); reflexivity | unfold LO_B330; lia]|].
    split; [bl_sl SLOT; [rewrite SOF by (unfold LO_B2E0; lia); reflexivity | unfold LO_B2E0; lia]|].
    split; [bl_sl SLOT; [exact OK10 | unfold MK_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite OF by (unfold MD_SIZE; lia); reflexivity | unfold MD_N_MARK, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite S3 by (unfold MD_SIZE; lia); reflexivity
                        | apply SHB; unfold MD_N_REQ, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite S3 by (unfold MD_SIZE; lia); reflexivity
                        | apply SHB; unfold MD_NEXT, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite S3 by (unfold MD_SIZE; lia); reflexivity
                        | apply SHB; unfold MD_SEND_ERRNO, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [exact OBJ9 | unfold LA_JT; lia]|].
    split; [bl_sl SLOT; [reflexivity | unfold LA_G_NL; lia]|].
    split; [bl_sl SLOT; [rewrite S3 by (unfold MD_SIZE; lia); rewrite Z.add_0_r; reflexivity
                        | apply SHB; unfold MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite OF by (unfold MD_SIZE; lia); reflexivity | unfold MD_N_REQ, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite OF by (unfold MD_SIZE; lia); reflexivity | unfold MD_NEXT, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite OF by (unfold MD_SIZE; lia); reflexivity | unfold MD_SEND_ERRNO, MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [rewrite OF by (unfold MD_SIZE; lia); rewrite Z.add_0_r; reflexivity | unfold MD_SIZE in *; lia]|].
    split; [bl_sl SLOT; [reflexivity | unfold LA_G_NL; lia]|].
    split; [bl_sl SLOT; [reflexivity | unfold SHADOW_OFF; lia]|].
    bl_sl SLOT; [rewrite SOF by lia; rewrite Z.add_0_r; reflexivity | lia]. }
  split.
  { split; [bl_sl SLOT; [exact P33 | lia]|].
    split; [bl_sl SLOT; [exact N34 | lia]|].
    exists 0. lia. }
  split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdat'|]. lia.
Qed.

(* the whole blocks phase *)
Lemma lf_blk : forall POST, FROM POST (lf_lh_inv B MT MS la_nul LF_MO_SET LF_MO_OP 0) ->
  FROM POST (lf_ca_inv B MT MS la_nul).
Proof.
  intros POST HLH.
  eapply bk_callocs.
  all: try eassumption.
  intros cx fy fp k2 ly S W ms mdl T3 md mk kbs HB Hfx HM.
  exact (bl_final POST HLH cx fy fp k2 ly S W ms mdl T3 md mk kbs HB Hfx HM).
Qed.
End a.
