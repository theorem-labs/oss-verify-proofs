(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 876 of its 941 lines of code are new or changed and 1267 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: the two frame objects wk (F + 0x2e0) and
   wa (F + 0x330) put in scope and zeroed (+0xe34 .. +0xe80: their shadow bytes := 0, checked_memset(wk, 0, 40) at
   0x8362c, checked_memset(wa, 0, 40) at 0x83654), then `opened := g_nl.opened` into the slot s1 + 0x70
   (+0xe84 .. +0xe8c), from the cut r_t_inv to the cut r_z_inv at +0xe90. checked_memset is the intrinsic rule
   AMSET (lib/A/AE2r.v asan_memset_realizes), lifted onto the walk's journal by link_ajkit.v aj_gx_intrin_at as
   the entry lifts its g_nl memset.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputOp0Cut LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputOp0T LLVMFuzzerTestOneInputBlk LLVMFuzzerTestOneInputChk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the runner's states: the frame's shadow (atom 19) with the object's five bytes as the write window, and the
   spill slot that holds the object's address (atom 32 = F) *)
Definition z_fs_rg (lo hi : Z) : YP09.region := YP09.mkRegion (Some 19%nat) 0 112 lo hi [].
Definition z_slot_rg (off c : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 c))].
Definition z_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2);
           (32%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition z_ss (pc lo hi off c : Z) : sstate :=
  mkSS pc sr_atoms [z_fs_rg lo hi; z_slot_rg off c] None z_facts.

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
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes, in YG0d.v's aintrin_realizes shape; the entry's
   LLVMFuzzerTestOneInputEntry.v lf_memset_intrin gives it from its CMS *)
Hypothesis AMSET : forall fy : YK11.FPState, aintrin_realizes (fx := fy) pa_segs B OSet 0x53214.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* a frame object whose shadow bytes lo .. lo + cnt - 1 are 0: addressable, and its shadow hull visible *)
Lemma r_buf_shadow : forall cx fp (W : world SEGS) ms sh lo cnt,
  lf_fshadow cx fp W ms sh -> (length sh = 112)%nat ->
  lf_F cx fp mod 32 = 0 -> 4096 <= lf_F cx fp -> lf_F cx fp + 1024 <= alloc_ceiling ->
  4 <= lo -> 1 <= cnt -> lo + cnt <= 108 ->
  (forall j, (Z.to_nat lo <= j < Z.to_nat (lo + cnt))%nat -> nth j sh 0 = 0) ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (lf_F cx fp + 8 * lo) (8 * cnt) /\
  shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) (lf_F cx fp + 8 * lo) (8 * cnt).
Proof.
  intros cx fp W ms sh lo cnt Hfs' Hl F32 F4 Fc Hlo Hc Hhi Hz.
  pose proof asan_consts as ((C1a & C1b) & _).
  set (F := lf_F cx fp) in *.
  assert (Fm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
  assert (SHF : lf_SH cx fp = SHADOW_OFF + F / 8) by reflexivity.
  assert (S4 : lf_SH cx fp mod 4 = 0).
  { rewrite SHF. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D.
    assert (Q : F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia;
      apply Z.div_mul; lia).
    rewrite Q. unfold SHADOW_OFF. replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia.
    apply Z_mod_mult. }
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite Fm8, Z.add_0_r in DF.
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr.
    assert (Hix : lo <= x / 8 - F / 8 < lo + cnt).
    { assert (A1 : F / 8 + lo <= x / 8) by (apply Z.div_le_lower_bound; lia).
      assert (A2 : x / 8 < F / 8 + (lo + cnt)) by (apply Z.div_lt_upper_bound; lia). lia. }
    replace (SHADOW_OFF + x / 8) with (lf_SH cx fp + Z.of_nat (Z.to_nat (x / 8 - F / 8))) by (rewrite SHF; lia).
    rewrite (Hfs' (Z.to_nat (x / 8 - F / 8)) ltac:(rewrite Hl; lia)).
    rewrite (Hz (Z.to_nat (x / 8 - F / 8)) ltac:(lia)). reflexivity.
  - intros s Hs. unfold shadow_addr in Hs.
    assert (A1 : (F + 8 * lo) / 8 = F / 8 + lo) by (rewrite DF at 1; replace (8 * (F / 8) + 8 * lo) with ((F / 8 + lo) * 8) by lia;
      apply Z.div_mul; lia).
    assert (A2 : (F + 8 * lo + 8 * cnt - 1) / 8 = F / 8 + (lo + cnt - 1))
      by (rewrite DF at 1; replace (8 * (F / 8) + 8 * lo + 8 * cnt - 1) with (7 + (F / 8 + (lo + cnt - 1)) * 8) by lia;
          rewrite Z.div_add by lia; reflexivity).
    rewrite A1, A2 in Hs.
    replace (SHADOW_OFF + (F / 8 + lo)) with (lf_SH cx fp + lo) in Hs by (rewrite SHF; lia).
    replace (SHADOW_OFF + (F / 8 + (lo + cnt - 1))) with (lf_SH cx fp + (lo + cnt - 1)) in Hs by (rewrite SHF; lia).
    assert (Hlow : lf_SH cx fp <= (lf_SH cx fp + lo) / 8 * 8)
      by (pose proof (Z.div_mod (lf_SH cx fp + lo) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (lf_SH cx fp + lo) 8 ltac:(lia));
          pose proof (Z.div_mod (lf_SH cx fp) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (lf_SH cx fp) 8 ltac:(lia));
          assert (lf_SH cx fp mod 8 = 0 \/ lf_SH cx fp mod 8 = 4) by (rewrite <- (Z.mod_mod (lf_SH cx fp) 8) by lia;
            clear - S4; lia); lia).
    assert (Hu : (lf_SH cx fp + (lo + cnt - 1)) / 8 * 8 + 8 <= lf_SH cx fp + 112)
      by (pose proof (Z.div_mod (lf_SH cx fp + (lo + cnt - 1)) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (lf_SH cx fp + (lo + cnt - 1)) 8 ltac:(lia));
          pose proof (Z.div_mod (lf_SH cx fp) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (lf_SH cx fp) 8 ltac:(lia));
          assert (lf_SH cx fp mod 8 = 0 \/ lf_SH cx fp mod 8 = 4) by (rewrite <- (Z.mod_mod (lf_SH cx fp) 8) by lia;
            clear - S4; lia); lia).
    replace s with (lf_SH cx fp + Z.of_nat (Z.to_nat (s - lf_SH cx fp))) by lia.
    rewrite (Hfs' (Z.to_nat (s - lf_SH cx fp)) ltac:(rewrite Hl; lia)). discriminate.
Qed.
#[local] Notation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* checked_memset of frame-body bytes [d, d + n), as a callee: its post (link_ajkit.v aj_gx_intrin_at) is an lf_call
   whose write set is those bytes and whose stack window is ESTACK bytes below s1 *)
Lemma r_memset_lfcall : forall cx fp k ly S (W : world SEGS) memT mdT (regsT : bvmap 5 word) mem2 d n,
  BASEF cx -> JRN cx fp ly S W memT mdT k -> frames S = [(LF_CID, fp)] ->
  spZ regsT = lf_sp1 cx ->
  lf_F cx fp + 24 <= d -> d + n <= lf_F cx fp + 1016 -> 0 <= n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
  lf_call B cx ESTACK ly S ly S W memT W mem2 (fun a => d <= a < d + n).
Proof.
  intros cx fp k ly S W memT mdT regsT mem2 d n HB HJ Hfr Hsp Hd1 Hd2 Hn Hpost Hpres.
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W memT mdT k
    HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly S W memT mdT k HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  rewrite Hsp in Hpost.
  assert (FD : lf_F cx fp / 8 <= CEIL_MAX / 8) by (apply Z.div_le_mono; lia).
  assert (F0 : 0 <= lf_F cx fp / 8) by (apply Z.div_pos; lia).
  unfold ESTACK, LLVMF_STK in *.
  split; [lia|]. split; [lia|]. split; [|].
  - split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha Hw HE. apply Hpost; [lia | exact HE | lia].
    + intros b m i Hin Hi HE.
      destruct (al_blocks _ _ LAWS ly S W memT mdT b m HAR Hin) as (_ & Bb4 & Bceil & _).
      apply Hpost; [lia | exact HE | lia].
    + intros a Hi _ _ HE. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
      apply Hpost; [lia | exact HE | lia].
    + intros cid pos a Hin Ha HE. rewrite Hfr in Hin. destruct Hin as [Hq | []]. injection Hq as <- <-.
      unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite HFa in Ha.
      change (fs_frame_bytes LF_CID) with 1024 in Ha. change (1024 / 8) with 128 in Ha. unfold shadow_addr in Ha.
      apply Hpost; [unfold SHADOW_OFF in *; lia | exact HE | unfold SHADOW_OFF in *; lia].
    + intros a _ _ Hp. exact (Hpres a Hp).
    + intros a Ha. apply Hpres. apply HP. lia.
  - intros b m a Hin _ Ha.
    destruct (al_blocks _ _ LAWS ly S W memT mdT b m HAR Hin) as (_ & Bb4 & Bceil & _).
    assert (AD : a / 8 <= CEIL_MAX / 8) by (apply Z.div_le_mono; lia).
    assert (A0 : 0 <= a / 8) by (apply Z.div_pos; lia).
    unfold shadow_addr. apply Hpost; [unfold SHADOW_OFF in *; lia | | unfold SHADOW_OFF in *; lia].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the cut across a callee whose writes are bytes of the frame's body: every clause kept, the model too *)
Lemma r_body_after : forall cx fp K ly3 S3 ly2 S2 (W3 : world SEGS) ms3 md3 (W2 : world SEGS) ms2 md2 (E : Z -> Prop)
    k2 ev mo wl lv md mk kbs mbs gbs T3 own P N sh,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> lf_F cx fp + 24 <= a < lf_F cx fp + 1016) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) (lf_data_fp_w md mk) ->
  (length sh <= 128)%nat ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 sh -> lf_slots cx md mk fp W3 ms3 ->
  lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 sh /\ lf_slots cx md mk fp W2 ms2 /\
  lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs mbs gbs (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp K ly3 S3 ly2 S2 W3 ms3 md3 W2 ms2 md2 E k2 ev mo wl lv md mk kbs mbs gbs T3 own P N sh
    HB HJ Hfr LC HE Fd Fs Pmd Pmk WC Hshl Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat.
  pose proof Hdat as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & _).
  pose proof Hblk as (Bmd & _).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (_ & _ & _ & _ & _ & _ & _ & Fsep).
  pose proof (Fsep md MD_SIZE Bmd) as DmF. unfold zdisjoint in DmF. cbn [fst snd] in DmF.
  change (req_size MD_SIZE) with 8856 in DmF.
  assert (Dmd2 : amodel_at SEGS (rdW W2 (ms_mem ms2)) md mbs).
  { apply (amodel_keep SEGS _ _ _ md mbs (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC));
      [| |exact Dmd].
    - apply (wcarry_on_sub _ _ _ md MD_SIZE WC). intros i Hi. right; right; right; left. lia.
    - intros i Hi. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E md MD_SIZE (md + i) Bmd ltac:(lia)).
      intros HEa. specialize (HE _ HEa). unfold MD_SIZE in *. lia. }
  exact (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
    cx fp K ly3 S3 ly2 S2 W3 ms3 md3 W2 ms2 md2 E k2 ev mo wl lv md mk kbs mbs gbs mbs T3 own P N sh
    HB HJ Hfr LC (fun a Ha => or_intror (HE a Ha)) Fd Fs Pmd Pmk WC Hshl Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat
    Dmd2 Dmwf eq_refl eq_refl).
Qed.

(* a byte of a block of the state is an application byte, so it is not a byte of the frame's shadow *)
Lemma r_blk_not_sh : forall cx fp ly S (W : world SEGS) mem mdl k b m a,
  BASEF cx -> JRN cx fp ly S W mem mdl k -> frames S = [(LF_CID, fp)] ->
  In (b, m) (ablocks B ly S) -> b <= a < b + req_size m ->
  0 <= a < 2 ^ 64 /\ ~ (lf_SH cx fp <= a < lf_SH cx fp + 128).
Proof.
  intros cx fp ly S W mem mdl k b m a HB HJ Hfr Hin Ha.
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  destruct (al_blocks _ _ LAWS ly S W mem mdl b m HAR Hin) as (_ & Bb4 & Bceil & Bapp & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly S W mem mdl k HB HJ Hfr) as (_ & F32 & F4 & Fc & Fapp & _).
  assert (FD : lf_F cx fp / 8 <= CEIL_MAX / 8) by (apply Z.div_le_mono; lia).
  assert (F0 : 512 <= lf_F cx fp / 8) by (apply Z.div_le_lower_bound; lia).
  unfold lf_SH, shadow_of_addr, in_app, amem_range, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL,
    SHADOW_OFF in *.
  split; [lia|]. lia.
Qed.

(* the cut across a run that writes only bytes of the frame's shadow *)
Lemma r_shadow_keep : forall (X : Z -> Prop) cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 (W3 : world SEGS)
    ms3 md3 ms' md' P N,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) -> mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> X a -> lf_SH cx fp <= a < lf_SH cx fp + 128) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W3 ms' /\ lf_header cx fp W3 ms' /\ lf_slots cx md mk fp W3 ms' /\ lf_cur cx W3 ms' P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms' md' T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms')) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms')).
Proof.
  intros X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 ms' md' P N
    HB HJ Hfr KA HGA Fd Fs HX Hsv Hhd Hsl Hcur Hjbk Hblk Hdat.
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> X a ->
     ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_slots_fp cx a /\
     ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\ ~ lf_data_fp md mk a).
  { intros a Hf HXa. pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
      LAWS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Hf) as R.
    exact (u_fs_out SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk (HX a (proj1 R) HXa)). }
  split; [exact (lf_saved_keep X cx W3 ms3 W3 ms' KA
    (fun a Ha HXa => proj1 (NX a ltac:(tauto) HXa) Ha) Hsv)|].
  split; [exact (lf_header_keep X cx fp W3 ms3 W3 ms' KA
    (fun a Ha HXa => proj1 (proj2 (NX a ltac:(tauto) HXa)) Ha) Hhd)|].
  split; [exact (lf_slots_keep X cx md mk fp W3 ms3 W3 ms' KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (NX a ltac:(tauto) HXa))) Ha) Hsl)|].
  split; [exact (lf_cur_keep X cx W3 ms3 W3 ms' P N KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))) Ha) Hcur)|].
  split; [exact (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 ms' md' KA Fd Fs
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))) Ha) Hjbk)|].
  split; [exact (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hblk)|].
  exact (lf_data_keep X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    (fun a Ha HXa => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hdat).
Qed.

(* a text buffer across a byte agreement off X, when X misses its bytes *)
Lemma r_atbuf_keep : forall (X : Z -> Prop) (W : world SEGS) m m' t cap bs,
  kagree SEGS X (rdW W m) (rdW W m') -> mem_grows (rdW W m) (rdW W m') ->
  (forall i, 0 <= i < cap + 1 -> ~ X (t + i)) ->
  atbuf_at SEGS (rdW W m) t cap bs -> atbuf_at SEGS (rdW W m') t cap bs.
Proof.
  intros X W m m' t cap bs HK HG HX (Hu & Hl). split; [|exact Hl].
  apply (au8arr_keep SEGS _ _ _ _ _ HK (wcarry_of_grows SEGS _ _ _ _ HG)); [|exact Hu].
  intros i Hi. apply HX. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

(* bytes whose view is unchanged *)
Lemma r_abytes_aview_keep : forall H H' (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview SEGS H' m' (a + i) = aview SEGS H m (a + i)) ->
  abytes SEGS (mrestrict H m) a bs -> abytes SEGS (mrestrict H' m') a bs.
Proof.
  intros H H' m m' a bs HV (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (mbyte_of_aview SEGS H H' m m' (a + Z.of_nat i) (HV (Z.of_nat i) ltac:(lia))). exact (H2 i Hi).
Qed.

(* bytes a memset left all zero *)
Lemma r_abytes_zero : forall H (m : word -> option byte) d n,
  0 <= d -> d + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> aview SEGS H m (d + i) = Some (0 mod 256)) ->
  abytes SEGS (mrestrict H m) d (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
  intros H m d n H0 H1 Hn HV. split; [exact H0|]. rewrite repeat_length. split; [lia|].
  intros i Hi. rewrite nth_error_repeat by exact Hi.
  specialize (HV (Z.of_nat i) ltac:(lia)).
  change (aview SEGS H m (d + Z.of_nat i)) with
    (option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict H m) (d + Z.of_nat i))) in HV.
  destruct (mbyte SEGS (mrestrict H m) (d + Z.of_nat i)) as [b|]; cbn [option_map] in HV; [|discriminate HV].
  injection HV as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* the runner's entry state of a stretch that puts a frame object in scope: the frame's shadow, with the
   object's shadow bytes [lo, hi) as the write window, and the slot at s1 + off that holds its address F + c *)
Lemma z_entry : forall (fy : YK11.FPState) cx fp (W : world SEGS) ms pc lo hi off c,
  regions_wf [z_fs_rg lo hi; z_slot_rg off c] = true ->
  getr (ms_regs ms) 9 = w64 (lf_sp1 cx) -> getr (ms_regs ms) 19 = w64 (lf_SH cx fp) ->
  alloc_ceiling + LLVMF_STK - 432 <= lf_sp1 cx -> lf_sp1 cx + 0x128 <= 2 ^ 47 ->
  lf_F cx fp mod 32 = 0 -> 4096 <= lf_F cx fp -> lf_F cx fp + 1024 <= alloc_ceiling ->
  kLowMemEnd + 512 <= lf_SH cx fp -> lf_SH cx fp + 128 <= kHighMemBeg -> lf_SH cx fp mod 4 = 0 ->
  (forall i, 0 <= i < 128 -> apresent (w_H W) (ms_mem ms) (lf_SH cx fp + i)) ->
  0 <= lo -> lo <= hi -> hi <= 112 -> 0x18 <= off -> off + 8 <= 0x100 -> 0 <= c -> c + 8 <= 1024 ->
  lf_slot cx W ms off (lf_F cx fp + c) ->
  st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms) [Z_to_bv 64 (lf_F cx fp)])) (z_ss pc lo hi off c)
    (restrict (w_H W) (@mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS))).
Proof.
  intros fy cx fp W ms pc lo hi off c Hwf R9 R19 Hlo H47 F32 F4 Fc SH1 SH2 SH4 Fshp Hl1 Hl2 Hl3 Ho1 Ho2 Hc1 Hc2 Hslot.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  set (F := lf_F cx fp) in *.
  set (E := Eimg (Ereg (ms_regs ms) [Z_to_bv 64 F])).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp)
    by (rewrite E19; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; clia).
  rewrite restrict_mkst_fx. unfold z_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - exact Hwf.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, z_fs_rg, z_slot_rg;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [unfold kLowMemEnd in *; clia|]. split; [unfold kHighMemBeg in *; clia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clia.
    + rewrite U9. split; [unfold LLVMF_STK in *; clia|]. split; [unfold LLVMF_STK in *; clia|].
      split; [intros o Ho; clia|]. apply Forall_cons; [|apply Forall_nil].
      apply (u_slot_chunk E cx W ms off _ (F + c)); [|exact Hslot].
      rewrite (lf_sv_off E 32 F c E32) by clia. reflexivity.
  - apply pairwise_disjoint_of_extents. unfold z_fs_rg, z_slot_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowMemEnd, kHighMemBeg, LLVMF_STK in *. repeat split; clia.
  - split; [|split; exact I]. cbn [z_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U32. assert (HFS : lf_SH cx fp = SHADOW_OFF + F / 8) by reflexivity.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, LLVMF_STK in *.
    split; [split; [clia|]; split; [unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
            apply Z_mod_mult | clia]|].
    split; [split; [clia|]; split; [exact SH4 | clia]|].
    split; [|exact I]. split; [clia|]. split; [exact F32 | clia].
Qed.

(* the bounds of a slot address s1 + off + i *)
Ltac slot_rng :=
  unfold LS_J18, LS_J20, LS_J28, LS_J30, LS_F, LS_FK, LS_B1A0, LS_ODD, LS_MARK0, LS_STR1, LS_B160, LS_NIF, LS_WA,
    LS_B330, LS_B2E0, LS_MK, LS_NMARK, LS_SH_NREQ, LS_SH_NEXT, LS_SH_SE, LS_JT, LS_GNL42, LS_SH_M, LS_NREQ, LS_NEXT,
    LS_SE, LS_M, LS_GNL40, LS_SHB, LS_F0, LLVMF_STK in *; lia.

(* the cut across a run that writes only the slot s1 + 0x70 (opened), which no cut clause reads *)
Lemma r_nif_keep : forall (X : Z -> Prop) cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 (W3 : world SEGS)
    ms3 md3 ms' md' P N sh,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) -> mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 -> (length sh <= 112)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> X a -> lf_sp1 cx + LS_NIF <= a < lf_sp1 cx + LS_NIF + 8) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 sh -> lf_slots cx md mk fp W3 ms3 ->
  lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W3 ms' /\ lf_header cx fp W3 ms' /\ lf_fshadow cx fp W3 ms' sh /\ lf_slots cx md mk fp W3 ms' /\
  lf_cur cx W3 ms' P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms' md' T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms')) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms')).
Proof.
  intros X cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own ly3 S3 W3 ms3 md3 ms' md' P N sh
    HB HJ Hfr KA HGA Fd Fs Hl HX Hsv Hhd Hfs Hsl Hcur Hjbk Hblk Hdat.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof Hblk as (Bmd & Bmk & _).
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (LOW : forall a, (lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_jbk_fp MS la_nul cx T3 a \/
      lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> ~ X a).
  { intros a Ha HXa. pose proof (lf_cut_fp_low SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
      LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ ms3 md3 md mk T3 _ a HB HJ Hin Hjbk Bmd Bmk Ha) as R.
    specialize (HX a ltac:(lia) HXa). unfold LS_NIF, LLVMF_STK in *. lia. }
  split; [apply (lf_saved_keep X cx W3 ms3 W3 ms' KA); [|exact Hsv];
          intros a Ha HXa; unfold lf_saved_fp in Ha; specialize (HX a ltac:(unfold LLVMF_STK in *; lia) HXa);
          unfold LS_NIF in *; lia|].
  split; [apply (lf_header_keep X cx fp W3 ms3 W3 ms' KA); [|exact Hhd]; intros a Ha; apply LOW; left; exact Ha|].
  split; [apply (lf_fshadow_keep X cx fp W3 ms3 W3 ms' sh KA); [|exact Hfs];
          intros a Ha; apply LOW; right; left; unfold lf_fshadow_fp in *; lia|].
  split.
  { unfold lf_slots in *. repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    repeat split; (eapply (lf_slot_keep X cx W3 ms3 W3 ms'); [exact KA | | eassumption]);
      intros j Hj HXj; apply HX in HXj; slot_rng. }
  split; [apply (lf_cur_keep X cx W3 ms3 W3 ms' P N KA); [|exact Hcur];
          intros a Ha HXa; unfold lf_cur_fp in Ha; specialize (HX a ltac:(unfold LLVMF_STK in *; lia) HXa);
          unfold LS_NIF in *; lia|].
  split; [exact (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 ms' md' KA Fd Fs
    (fun a Ha => LOW a (or_intror (or_intror (or_introl Ha)))) Hjbk)|].
  split; [exact (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA
    (fun a Ha => LOW a (or_intror (or_intror (or_intror (or_introl Ha))))) Hblk)|].
  exact (lf_data_keep X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    (fun a Ha => LOW a (or_intror (or_intror (or_intror (or_intror Ha))))) Hdat).
Qed.

(* the runner's state of +0xe84 .. +0xe8c: the slot window s1 + 0x70, the slot s1 + 0xf0 (g_nl + 0x40000, atom 32)
   and g_nl.opened (atom 33) *)
Definition o_slot_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x70 0xf8 0x70 0x78 [YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0))].
Definition o_gnl_rg : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x218 0x21c 0x218 0x218 [YP09.mkChunk 0x218 (CVal 4 (SOff 33 0))].
Definition o_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (33%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] [].
Definition o_ss (pc : Z) : sstate := mkSS pc sr_atoms [o_slot_rg; o_gnl_rg] None o_facts.
Definition o_extra (kbs : list byte) : list word := [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (nk_opened kbs)].

Lemma o_entry : forall (fy : YK11.FPState) cx (W : world SEGS) ms pc md mk kbs mbs gbs,
  getr (ms_regs ms) 9 = w64 (lf_sp1 cx) ->
  alloc_ceiling + LLVMF_STK - 432 <= lf_sp1 cx -> lf_sp1 cx + 0x128 <= 2 ^ 47 ->
  (forall a, lf_sp1 cx + 0x70 <= a < lf_sp1 cx + 0x78 -> apresent (w_H W) (ms_mem ms) a) ->
  lf_slot cx W ms LS_GNL40 (LA_G_NL + 0x40000) ->
  lf_data cx md mk kbs mbs gbs (rdW W (ms_mem ms)) ->
  st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms) (o_extra kbs))) (o_ss pc)
    (restrict (w_H W) (@mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS))).
Proof.
  intros fy cx W ms pc md mk kbs mbs gbs R9 Hlo H47 Hstk Hslot Hdat.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hdat as (Dk & Dwf & _).
  set (E := Eimg (Ereg (ms_regs ms) (o_extra kbs))).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (o_extra kbs) (Z_to_bv 64 0)).
  { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). apply ew_Ereg_extra. }
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 (LA_G_NL + 0x40000)) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_opened kbs)) by exact (EX 1%nat ltac:(lia)).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  assert (U32 : bv_unsigned (ew E 32) = LA_G_NL + 0x40000)
    by (rewrite E32; apply unsigned_lit_small; unfold LA_G_NL; clia).
  pose proof Dwf as (_ & _ & _ & _ & _ & ROP & _).
  rewrite restrict_mkst_fx. unfold o_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, o_slot_rg, o_gnl_rg;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [unfold LLVMF_STK in *; clia|]. split; [unfold LLVMF_STK in *; clia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hstk; clia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (u_slot_chunk E cx W ms 0xf0 _ (LA_G_NL + 0x40000)); [|exact Hslot].
      rewrite (lf_sv_off E 32 _ 0 E32) by (unfold LA_G_NL; clia). rewrite Z.add_0_r. reflexivity.
    + rewrite U32. split; [unfold LA_G_NL; clia|]. split; [unfold LA_G_NL; clia|]. split; [intros o Ho; clia|].
      apply Forall_cons; [|apply Forall_nil]. destruct Dk as ((Hb & _) & HL).
      apply (chunk_ok_val SEGS E _ _ 0x218 4 (SOff 33 0) (nk_opened kbs));
        [rewrite (lf_sv_off E 33 _ 0 E33) by clia; rewrite Z.add_0_r; reflexivity | cbn; clia | cbn; clia |].
      replace (LA_G_NL + 262144 + 0x218) with (LA_G_NL + NK_OPENED) by (unfold NK_OPENED; clia).
      exact (val_mem_of_abytes SEGS _ LA_G_NL kbs NK_OPENED 4 Hb ltac:(unfold NK_OPENED; lia)
        ltac:(unfold NK_OPENED, NK_SIZE in *; lia)).
  - apply pairwise_disjoint_of_extents. unfold o_slot_rg, o_gnl_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold LA_G_NL, LLVMF_STK in *. repeat split; clia.
  - split; [|split; exact I]. cbn [o_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U32, E33, unsigned_lit_small by clia. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold LLVMF_STK in *.
    split; [split; [clia|]; split; [unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
            apply Z_mod_mult | clia]|].
    split; [unfold LA_G_NL; repeat split; first [exact I | clia]|].
    split; [repeat split; first [exact I | clia] | exact I].
Qed.

Lemma r_zero : forall POST i,
  FROM POST (r_z_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_t_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HZ cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HT.
  destruct HT as (md & mk & P & N & kbs & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hsh & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & HC & Hcur & Hop & Hns & Hrq & Hks & Hra & Hbufs & Hb1 & Hb2).
  destruct HC as (_ & _ & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
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
  pose proof Hsl as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17
    & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29).
  set (F := lf_F cx fp) in *.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 F])).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp)
    by (rewrite E19; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; clia).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E (z_ss LR_t 92 97 0x88 736)
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_t)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold z_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, z_fs_rg, z_slot_rg;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U19. split; [unfold kLowMemEnd in *; clia|]. split; [unfold kHighMemBeg in *; clia|].
        split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clia.
      + rewrite U9. split; [unfold LLVMF_STK in *; clia|]. split; [unfold LLVMF_STK in *; clia|].
        split; [intros o Ho; clia|]. apply Forall_cons; [|apply Forall_nil].
        apply (u_slot_chunk E cx W3 ms3 0x88 _ (F + LO_B2E0)); [|exact S14].
        rewrite (lf_sv_off E 32 F 736 E32) by (unfold LO_B2E0; clia). reflexivity.
    - apply pairwise_disjoint_of_extents. unfold z_fs_rg, z_slot_rg, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold kLowMemEnd, kHighMemBeg, LLVMF_STK in *. repeat split; clia.
    - split; [|split; exact I]. cbn [z_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U19, U32. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, LLVMF_STK in *.
      split; [split; [clia|]; split; [unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
              apply Z_mod_mult | clia]|].
      split; [split; [clia|]; split; [exact (proj2 (proj2 SHB)) | clia]|].
      split; [|exact I]. split; [clia|]. split; [exact F32 | clia]. }
  rewrite (lf_shape_eta fy LR_t ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_t)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { cbn [ss_mem z_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base z_fs_rg base_val] in Ha. rewrite U19 in Ha.
      left. split; [|clia]. right; right; right. exists LF_CID, fp. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID / 8) with 128.
      unfold shadow_addr. rewrite <- HFS. clia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base z_slot_rg base_val] in Ha. clia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (mdA := mdB) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  set (X1 := fun a => lf_SH cx fp + 92 <= a mod 2 ^ 64 < lf_SH cx fp + 97).
  assert (KA : kagree SEGS X1 (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem (z_ss LR_t 92 97 0x88 736)) _ _ X1 HFrA). intros a (r & Hr & Hw). unfold X1.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem z_ss In] in Hr. destruct Hr as [<- | [<- | []]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base z_fs_rg z_slot_rg base_val] in Hw; [rewrite U19 in Hw; clia | clia]. }
  assert (HXr : forall a, 0 <= a < 2 ^ 64 -> X1 a -> lf_SH cx fp <= a < lf_SH cx fp + 128)
    by (intros a Ha HXa; unfold X1 in HXa; rewrite Z.mod_small in HXa by exact Ha; clia).
  destruct (r_shadow_keep X1 cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3 msA mdA P N HB HJ0 Hfr KA HGA
    FdA FsA HXr Hsv Hhd Hsl Hcur Hjbk Hblk Hdat) as (HsvA & HhdA & HslA & HcurA & HjbkA & HblkA & HdatA).
  assert (RG0 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 0 (ss_mem ssA) (z_fs_rg 0 0)))
    by exact (st_ok_region_nth E ssA (restrict (w_H W3) msA) 0 _ HS eq_refl).
  assert (HfsA : lf_fshadow cx fp W3 msA SH_W).
  { apply (u_fsh_upd cx fp W3 ms3 msA X1 LF_SH0 SH_W 92 97 0 Hfs KA); [reflexivity | |].
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0. split;
        [|rewrite (SH_W_nth i0 Hi1); destruct (Nat.leb_spec 92 i0), (Nat.ltb_spec i0 97); cbn [andb]; try reflexivity;
          clia].
      unfold X1. rewrite Z.mod_small by (unfold kHighMemBeg in *; clia). clia.
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0. split;
        [|rewrite (SH_W_nth i0 Hi1); destruct (Nat.leb_spec 92 i0), (Nat.ltb_spec i0 97); cbn [andb]; try reflexivity;
          clia].
      apply (u_byte_lit E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) 0 RG0).
      + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
      + assert (Hc : forall k, 92 <= k < 97 ->
            In (YP09.mkChunk k (CVal 1 (SLit 0))) (YP09.r_chunks (nth 0 (ss_mem ssA) (z_fs_rg 0 0)))).
        { intros k Hk. cbn [nth ss_mem ssA setpc YP09.r_chunks].
          assert (Hk' : k = 92 \/ k = 93 \/ k = 94 \/ k = 95 \/ k = 96) by clia.
          repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst k. cbn [In]. tauto. }
        apply Hc. clia.
      + clia. }
  (* the two text buffers: block bytes, off the shadow *)
  pose proof Hbufs as (Hnb1 & Hnb2 & Hbin & Hbap).
  assert (IN1 : 1 <= kc -> In (t1, kc + 1) (ablocks B ly3 S3)).
  { intros H1. destruct Hnb1 as [(E0 & _) | (_ & _ & ->)]; [clia|].
    apply (Hbin (t1, kc + 1)). apply in_or_app. left. left. reflexivity. }
  assert (IN2 : 1 <= ac -> In (t2, ac + 1) (ablocks B ly3 S3)).
  { intros H1. destruct Hnb2 as [(E0 & _) | (_ & _ & ->)]; [clia|].
    apply (Hbin (t2, ac + 1)). apply in_or_app. right. left. reflexivity. }
  assert (RQ : forall c, 0 <= c -> req_size (c + 1) = c + 1)
    by (intros c Hc; unfold req_size; destruct (c + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; clia | clia]).
  assert (BX1 : forall b n x, In (b, n) (ablocks B ly3 S3) -> b <= x < b + req_size n -> ~ X1 x).
  { intros b n x Hin Hx HXx.
    destruct (r_blk_not_sh cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 b n x HB HJ0 Hfr Hin Hx) as (R & NS).
    unfold X1 in HXx. rewrite Z.mod_small in HXx by exact R. apply NS. clia. }
  assert (Hb1A : 1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem msA)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))).
  { intros H1. apply (r_atbuf_keep X1 W3 _ _ t1 kc _ KA HGA); [|exact (Hb1 H1)].
    intros j Hj. apply (BX1 t1 (kc + 1)); [exact (IN1 H1) | rewrite RQ by clia; clia]. }
  assert (Hb2A : 1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem msA)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))).
  { intros H1. apply (r_atbuf_keep X1 W3 _ _ t2 ac _ KA HGA); [|exact (Hb2 H1)].
    intros j Hj. apply (BX1 t2 (ac + 1)); [exact (IN2 H1) | rewrite RQ by clia; clia]. }
  (* ---- checked_memset(wk, 0, 40) at 0x8362c ---- *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  try rewrite (img_env_codeptr E HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4. rewrite U32 in Q10.
  pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (HspA : spZ (ms_regs msA) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (ZS1 : range_addressable (aview SEGS (w_H W3) (ms_mem msA)) SHADOW_OFF (F + 736) 40 /\
    shadow_hull_vis (aview SEGS (w_H W3) (ms_mem msA)) (F + 736) 40).
  { pose proof (r_buf_shadow cx fp W3 msA SH_W 92 5 HfsA SH_W_len F32 F4 Fc ltac:(lia) ltac:(lia) ltac:(lia)) as ZS.
    replace (lf_F cx fp + 8 * 92) with (F + 736) in ZS by (unfold F; lia). change (8 * 5) with 40 in ZS. apply ZS.
    intros j Hj. change (Z.to_nat 92) with 92%nat in Hj. change (Z.to_nat (92 + 5)) with 97%nat in Hj.
    rewrite (SH_W_nth j ltac:(lia)). destruct (Nat.leb_spec 92 j), (Nat.ltb_spec j 97); cbn [andb]; [reflexivity | lia..]. }
  assert (Hpc : ss_pc ssA = pa_sigma LS___asan_memset) by reflexivity.
  rewrite Hpc, (lv_sigma LV). replace (link_sigma LS___asan_memset) with 0x53214 by reflexivity.
  eapply SRr_bind.
  { apply (@aj_gx_intrin_at fy rc SK SEGS B LAWS pa_segs_low OSet 0x53214 (AMSET fy) G_HARNESS 0 [] W3 (ms_regs msA)
      (ms_mem msA) LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(LF_CID, fp)] ly3 S3 _ k2 (F + 736) 0 40 (getr (ms_regs msA) 1) HGX HJ).
    - rewrite Q10. reflexivity.
    - rewrite Q11. reflexivity.
    - rewrite Q12. reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite HspA. exact H16.
    - rewrite HspA. unfold ESTACK, LLVMF_STK in *. lia.
    - rewrite HspA. lia.
    - rewrite Q3. exact Gp.
    - rewrite Q4. exact Tp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. left. split; [|split; [lia | rewrite HspA; unfold ESTACK, LLVMF_STK in *; lia]].
      right; right; right. exists LF_CID, fp. split; [left; reflexivity|]. left.
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID) with 1024. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
    - exact (proj1 ZS1).
    - intros _. exact (proj2 ZS1).
    - exact I. }
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & H10m & Hset & Heff & Hpres4 & Hsame4).
  (* the registers the first run left *)
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl), R8 in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl), R9 in Q9.
  rewrite U32 in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl), R19 in Q19.
  rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl), R21 in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl), R22 in Q22.
  rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl), R23 in Q23. rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl), R24 in Q24.
  rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl), R25 in Q25. rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl), R26 in Q26.
  rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl), R27 in Q27.
  (* ---- the first memset's return: the cut, the buffers and wk = 0 ---- *)
  pose proof (ar_pres _ _ HP4) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
  set (ms4 := @mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS)).
  pose proof HJ4 as HJ4m. change mem4 with (ms_mem ms4) in HJ4, Hset, Heff, Hpres4.
  pose proof (r_memset_lfcall cx fp k2 ly3 S3 W3 (ms_mem msA) mdA (ms_regs msA) (ms_mem ms4) (F + 736) 40
    HB HJ Hfr HspA ltac:(unfold F in *; lia) ltac:(unfold F in *; lia) ltac:(lia) Heff Hpres4) as LC1.
  assert (Fd4 : m_fds md4 = m_fds mdA /\ m_fs md4 = m_fs mdA)
    by (rewrite (same_but_materialized_wvb _ _ Hsame4), lf_wvb_fds, lf_wvb_fs; split; reflexivity).
  pose proof HJ4 as (_ & _ & (memS4 & HJi4 & _) & _). pose proof HJi4 as (HAR4 & _).
  pose proof HblkA as (BmdA & BmkA & _).
  pose proof (ak_wcarry_callee B LAWS HSEGS ly3 S3 W3 (ms_mem ms4) md4 (rdW W3 (ms_mem msA)) md mk HAR4 BmdA BmkA)
    as WC4.
  destruct (r_body_after cx fp ESTACK ly3 S3 ly3 S3 W3 msA mdA W3 ms4 md4 _ k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N SH_W
    HB HJ Hfr LC1 ltac:(intros a Ha; cbv beta in Ha; unfold F in *; lia) (proj1 Fd4) (proj2 Fd4) BmdA BmkA WC4
    ltac:(rewrite SH_W_len; lia) HsvA HhdA HfsA HslA HcurA HjbkA HblkA HdatA)
    as (Hsv4 & Hhd4 & Hfs4 & Hsl4 & Hcur4 & Hjbk4 & Hblk4 & Hdat4 & HRO4).
  assert (FB : forall b n x, In (b, n) (ablocks B ly3 S3) -> b <= x < b + req_size n ->
      ~ (F + 736 <= x < F + 856)).
  { intros b n x Hin Hx Hx2. pose proof (Fsep b n Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    unfold F in *. lia. }
  assert (Hb1_4 : 1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem ms4)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))).
  { intros H1. apply (r_atbuf_callee B LAWS cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem msA) W3 (ms_mem ms4) _ md4 t1 kc _
      LC1 HAR4 (IN1 H1) (IN1 H1)); [| lia | exact (Hb1A H1)].
    intros a Ha Ha2. cbv beta in Ha2. apply (FB t1 (kc + 1) a (IN1 H1)); [rewrite RQ by lia; lia | lia]. }
  assert (Hb2_4 : 1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem ms4)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))).
  { intros H1. apply (r_atbuf_callee B LAWS cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem msA) W3 (ms_mem ms4) _ md4 t2 ac _
      LC1 HAR4 (IN2 H1) (IN2 H1)); [| lia | exact (Hb2A H1)].
    intros a Ha Ha2. cbv beta in Ha2. apply (FB t2 (ac + 1) a (IN2 H1)); [rewrite RQ by lia; lia | lia]. }
  assert (ZW4 : abytes SEGS (rdW W3 (ms_mem ms4)) (F + LO_B2E0) (repeat (Z_to_bv 8 0) 40)).
  { change 40%nat with (Z.to_nat 40). unfold LO_B2E0.
    apply (r_abytes_zero (w_H W3) (ms_mem ms4) (F + 736) 40); [lia | lia | lia |].
    intros j Hj. exact (Hset j Hj). }
  (* ---- +0xe5c .. +0xe80: wa's five shadow bytes := 0, s4 := wa; to the second checked_memset ---- *)
  unfold ms4. rewrite Q1. clear HS SHOK.
  assert (R9_4 : getr regs4 9 = w64 (lf_sp1 cx)) by (rewrite P9; exact Q9).
  assert (R19_4 : getr regs4 19 = w64 (lf_SH cx fp)) by (rewrite P19; exact Q19).
  assert (Hsh4 : forall j, 0 <= j < 128 -> apresent (w_H W3) mem4 (lf_SH cx fp + j))
    by (intros j Hj; apply Hpres4; apply (apresent_grows _ _ _ _ HGA); apply Fshp; lia).
  pose proof Hsl4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S13' & _).
  unfold LS_B330, LO_B330 in S13'.
  pose proof (z_entry fy cx fp W3 (@mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS)) 5220 102 107 0x80 816
    ltac:(vm_compute; reflexivity) R9_4 R19_4 Hlo ltac:(unfold LLVMF_STK in *; lia) F32 F4 Fc
    (proj1 SHB) (proj1 (proj2 SHB)) (proj2 (proj2 SHB)) Hsh4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S13') as HS.
  change (ms_regs (@mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS))) with regs4 in HS.
  change (ms_mem (@mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS))) with mem4 in HS.
  set (E2 := Eimg (Ereg regs4 [Z_to_bv 64 (lf_F cx fp)])) in HS.
  assert (EL2 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs4 r).
  { intros n r Hn Hr. unfold E2. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (U19b : bv_unsigned (ew E2 19) = lf_SH cx fp)
    by (rewrite (EL2 19%nat 19%bv ltac:(lia) eq_refl), R19_4; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  assert (U32b : bv_unsigned (ew E2 32) = F)
    by (unfold E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply unsigned_lit_small; unfold F; clia).
  assert (HEI2 : img_env pa_val A_LIM E2) by apply Eimg_env.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E2
    (mrestrict (w_H W3) (ms_mem (@mkst fy regs4 (Z_to_bv 64 (BASE + 5220)) mem4 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ4m SHOK (0, 0).
  { cbn [ss_mem z_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base z_fs_rg base_val] in Ha. rewrite U19b in Ha.
      left. split; [|clia]. right; right; right. exists LF_CID, fp. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID / 8) with 128.
      unfold shadow_addr. rewrite <- HFS. clia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base z_slot_rg base_val] in Ha. clia. }
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  lazymatch type of HS with st_ok _ _ ?ssx _ => set (ssB := ssx) in HS end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
  assert (FdB : m_fds mdB = m_fds md4) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
  assert (FsB : m_fs mdB = m_fs md4) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
  set (X2 := fun a => lf_SH cx fp + 102 <= a mod 2 ^ 64 < lf_SH cx fp + 107).
  assert (KB : kagree SEGS X2 (rdW W3 mem4) (rdW W3 (ms_mem msB))).
  { apply (u_kagree_frame E2 (ss_mem (z_ss 5220 102 107 0x80 816)) _ _ X2 HFrB). intros a (r & Hr & Hw). unfold X2.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem z_ss In] in Hr. destruct Hr as [<- | [<- | []]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base z_fs_rg z_slot_rg base_val] in Hw; [rewrite U19b in Hw; clia | clia]. }
  change mem4 with (ms_mem ms4) in KB, HGB.
  assert (HXr2 : forall a, 0 <= a < 2 ^ 64 -> X2 a -> lf_SH cx fp <= a < lf_SH cx fp + 128)
    by (intros a Ha HXa; unfold X2 in HXa; rewrite Z.mod_small in HXa by exact Ha; clia).
  destruct (r_shadow_keep X2 cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms4 md4 msB mdB P N HB HJ4 Hfr KB HGB
    FdB FsB HXr2 Hsv4 Hhd4 Hsl4 Hcur4 Hjbk4 Hblk4 Hdat4) as (HsvB & HhdB & HslB & HcurB & HjbkB & HblkB & HdatB).
  assert (RGB : region_ok SEGS E2 (rdW W3 (ms_mem msB)) (nth 0 (ss_mem ssB) (z_fs_rg 0 0)))
    by exact (st_ok_region_nth E2 ssB (restrict (w_H W3) msB) 0 _ HS eq_refl).
  assert (HfsB : lf_fshadow cx fp W3 msB SH_R).
  { apply (u_fsh_upd cx fp W3 ms4 msB X2 SH_W SH_R 102 107 0 Hfs4 KB); [reflexivity | |].
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0. split;
        [|rewrite (SH_R_nth i0 Hi1); destruct (Nat.leb_spec 102 i0), (Nat.ltb_spec i0 107); cbn [andb]; try reflexivity;
          clia].
      unfold X2. rewrite Z.mod_small by (unfold kHighMemBeg in *; clia). clia.
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0. split;
        [|rewrite (SH_R_nth i0 Hi1); destruct (Nat.leb_spec 102 i0), (Nat.ltb_spec i0 107); cbn [andb]; try reflexivity;
          clia].
      apply (u_byte_lit E2 (w_H W3) (ms_mem msB) _ (lf_SH cx fp) (Z.of_nat i0) 0 RGB).
      + cbn [nth ss_mem ssB setpc YP09.r_base base_val]. exact U19b.
      + assert (Hc : forall k, 102 <= k < 107 ->
            In (YP09.mkChunk k (CVal 1 (SLit 0))) (YP09.r_chunks (nth 0 (ss_mem ssB) (z_fs_rg 0 0)))).
        { intros k Hk. cbn [nth ss_mem ssB setpc YP09.r_chunks].
          assert (Hk' : k = 102 \/ k = 103 \/ k = 104 \/ k = 105 \/ k = 106) by clia.
          repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst k. cbn [In]. tauto. }
        apply Hc. clia.
      + clia. }
  assert (BX2 : forall b n x, In (b, n) (ablocks B ly3 S3) -> b <= x < b + req_size n -> ~ X2 x).
  { intros b n x Hin Hx HXx.
    destruct (r_blk_not_sh cx fp ly3 S3 W3 (ms_mem ms4) md4 k2 b n x HB HJ4 Hfr Hin Hx) as (R & NS).
    unfold X2 in HXx. rewrite Z.mod_small in HXx by exact R. apply NS. clia. }
  assert (Hb1B : 1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem msB)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))).
  { intros H1. apply (r_atbuf_keep X2 W3 _ _ t1 kc _ KB HGB); [|exact (Hb1_4 H1)].
    intros j Hj. apply (BX2 t1 (kc + 1)); [exact (IN1 H1) | rewrite RQ by clia; clia]. }
  assert (Hb2B : 1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem msB)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))).
  { intros H1. apply (r_atbuf_keep X2 W3 _ _ t2 ac _ KB HGB); [|exact (Hb2_4 H1)].
    intros j Hj. apply (BX2 t2 (ac + 1)); [exact (IN2 H1) | rewrite RQ by clia; clia]. }
  assert (FNS : forall x, F <= x < F + 1024 -> ~ X2 x /\ ~ (lf_SH cx fp <= x < lf_SH cx fp + 128)).
  { intros x Hx. unfold X2. rewrite Z.mod_small by (unfold F in *; clia).
    unfold F, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. split; clia. }
  assert (ZWB : abytes SEGS (rdW W3 (ms_mem msB)) (F + LO_B2E0) (repeat (Z_to_bv 8 0) 40)).
  { apply (abytes_keep SEGS X2 _ _ _ _ KB); [|exact ZW4].
    intros j Hj. rewrite repeat_length in Hj.
    apply (proj1 (FNS (F + LO_B2E0 + j) ltac:(unfold LO_B2E0 in *; clia))). }
  (* ---- checked_memset(wa, 0, 40) at 0x83654 ---- *)
  pmkst HS.
  prreg HS (1%bv : bv 5) B1. prreg HS (2%bv : bv 5) B2. prreg HS (3%bv : bv 5) B3. prreg HS (4%bv : bv 5) B4.
  prreg HS (8%bv : bv 5) B8. prreg HS (9%bv : bv 5) B9.
  prreg HS (10%bv : bv 5) B10. prreg HS (11%bv : bv 5) B11. prreg HS (12%bv : bv 5) B12.
  prreg HS (18%bv : bv 5) B18. prreg HS (19%bv : bv 5) B19. prreg HS (20%bv : bv 5) B20.
  prreg HS (21%bv : bv 5) B21. prreg HS (22%bv : bv 5) B22. prreg HS (23%bv : bv 5) B23.
  prreg HS (24%bv : bv 5) B24. prreg HS (25%bv : bv 5) B25. prreg HS (26%bv : bv 5) B26. prreg HS (27%bv : bv 5) B27.
  try rewrite (img_env_codeptr E2 HEI2) in B1.
  rewrite (EL2 2%nat 2%bv ltac:(lia) eq_refl), P2, Q2 in B2. rewrite (EL2 3%nat 3%bv ltac:(lia) eq_refl), P3, Q3 in B3.
  rewrite (EL2 4%nat 4%bv ltac:(lia) eq_refl), P4, Q4 in B4. rewrite (EL2 8%nat 8%bv ltac:(lia) eq_refl), P8, Q8 in B8.
  rewrite (EL2 9%nat 9%bv ltac:(lia) eq_refl), P9, Q9 in B9. rewrite U32b in B10, B20.
  rewrite (EL2 18%nat 18%bv ltac:(lia) eq_refl), P18, Q18 in B18.
  rewrite (EL2 19%nat 19%bv ltac:(lia) eq_refl), P19, Q19 in B19.
  rewrite (EL2 21%nat 21%bv ltac:(lia) eq_refl), P21, Q21 in B21.
  rewrite (EL2 22%nat 22%bv ltac:(lia) eq_refl), P22, Q22 in B22.
  rewrite (EL2 23%nat 23%bv ltac:(lia) eq_refl), P23, Q23 in B23.
  rewrite (EL2 24%nat 24%bv ltac:(lia) eq_refl), P24, Q24 in B24.
  rewrite (EL2 25%nat 25%bv ltac:(lia) eq_refl), P25, Q25 in B25.
  rewrite (EL2 26%nat 26%bv ltac:(lia) eq_refl), P26, Q26 in B26.
  rewrite (EL2 27%nat 27%bv ltac:(lia) eq_refl), P27, Q27 in B27.
  assert (HspB : spZ (ms_regs msB) = lf_sp1 cx)
    by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  assert (ZS2 : range_addressable (aview SEGS (w_H W3) (ms_mem msB)) SHADOW_OFF (F + 816) 40 /\
    shadow_hull_vis (aview SEGS (w_H W3) (ms_mem msB)) (F + 816) 40).
  { pose proof (r_buf_shadow cx fp W3 msB SH_R 102 5 HfsB SH_R_len F32 F4 Fc ltac:(lia) ltac:(lia) ltac:(lia)) as ZS.
    replace (lf_F cx fp + 8 * 102) with (F + 816) in ZS by (unfold F; lia). change (8 * 5) with 40 in ZS. apply ZS.
    intros j Hj. change (Z.to_nat 102) with 102%nat in Hj. change (Z.to_nat (102 + 5)) with 107%nat in Hj.
    rewrite (SH_R_nth j ltac:(lia)). destruct (Nat.leb_spec 102 j), (Nat.ltb_spec j 107); cbn [andb];
      [reflexivity | lia..]. }
  assert (HpcB : ss_pc ssB = pa_sigma LS___asan_memset) by reflexivity.
  rewrite HpcB, (lv_sigma LV). replace (link_sigma LS___asan_memset) with 0x53214 by reflexivity.
  eapply SRr_bind.
  { apply (@aj_gx_intrin_at fy rc SK SEGS B LAWS pa_segs_low OSet 0x53214 (AMSET fy) G_HARNESS 0 [] W3 (ms_regs msB)
      (ms_mem msB) LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(LF_CID, fp)] ly3 S3 _ k2 (F + 816) 0 40 (getr (ms_regs msB) 1) HGX HJ4m).
    - rewrite B10. reflexivity.
    - rewrite B11. reflexivity.
    - rewrite B12. reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite HspB. exact H16.
    - rewrite HspB. unfold ESTACK, LLVMF_STK in *. lia.
    - rewrite HspB. lia.
    - rewrite B3. exact Gp.
    - rewrite B4. exact Tp.
    - reflexivity.
    - rewrite B1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. left. split; [|split; [lia | rewrite HspB; unfold ESTACK, LLVMF_STK in *; lia]].
      right; right; right. exists LF_CID, fp. split; [left; reflexivity|]. left.
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID) with 1024. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
    - exact (proj1 ZS2).
    - intros _. exact (proj2 ZS2).
    - exact I. }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & H10m5 & Hset5 & Heff5 & Hpres5 & Hsame5).
  (* ---- the second memset's return: the cut, the buffers, wk and wa = 0 ---- *)
  pose proof (ar_pres _ _ HP5) as (P2' & P3' & P4' & P8' & P9' & P18' & P19' & P20' & P21' & P22' & P23' & P24'
    & P25' & P26' & P27').
  set (ms5 := @mkst fy regs5 (getr (ms_regs msB) 1) mem5 (seg_rom SEGS)).
  pose proof HJ5 as HJ5m. change mem5 with (ms_mem ms5) in HJ5, Hset5, Heff5, Hpres5.
  pose proof (r_memset_lfcall cx fp k2 ly3 S3 W3 (ms_mem msB) mdB (ms_regs msB) (ms_mem ms5) (F + 816) 40
    HB HJ4m Hfr HspB ltac:(unfold F in *; lia) ltac:(unfold F in *; lia) ltac:(lia) Heff5 Hpres5) as LC2.
  assert (Fd5 : m_fds md5 = m_fds mdB /\ m_fs md5 = m_fs mdB)
    by (rewrite (same_but_materialized_wvb _ _ Hsame5), lf_wvb_fds, lf_wvb_fs; split; reflexivity).
  pose proof HJ5 as (_ & _ & (memS5 & HJi5 & _) & _). pose proof HJi5 as (HAR5 & _).
  pose proof HblkB as (BmdB & BmkB & _).
  pose proof (ak_wcarry_callee B LAWS HSEGS ly3 S3 W3 (ms_mem ms5) md5 (rdW W3 (ms_mem msB)) md mk HAR5 BmdB BmkB)
    as WC5.
  destruct (r_body_after cx fp ESTACK ly3 S3 ly3 S3 W3 msB mdB W3 ms5 md5 _ k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N SH_R
    HB HJ4m Hfr LC2 ltac:(intros a Ha; cbv beta in Ha; unfold F in *; lia) (proj1 Fd5) (proj2 Fd5) BmdB BmkB WC5
    ltac:(rewrite SH_R_len; lia) HsvB HhdB HfsB HslB HcurB HjbkB HblkB HdatB)
    as (Hsv5 & Hhd5 & Hfs5 & Hsl5 & Hcur5 & Hjbk5 & Hblk5 & Hdat5 & HRO5).
  assert (Hb1_5 : 1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem ms5)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))).
  { intros H1. apply (r_atbuf_callee B LAWS cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem msB) W3 (ms_mem ms5) _ md5 t1 kc _
      LC2 HAR5 (IN1 H1) (IN1 H1)); [| lia | exact (Hb1B H1)].
    intros a Ha Ha2. cbv beta in Ha2. apply (FB t1 (kc + 1) a (IN1 H1)); [rewrite RQ by lia; lia | lia]. }
  assert (Hb2_5 : 1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem ms5)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))).
  { intros H1. apply (r_atbuf_callee B LAWS cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem msB) W3 (ms_mem ms5) _ md5 t2 ac _
      LC2 HAR5 (IN2 H1) (IN2 H1)); [| lia | exact (Hb2B H1)].
    intros a Ha Ha2. cbv beta in Ha2. apply (FB t2 (ac + 1) a (IN2 H1)); [rewrite RQ by lia; lia | lia]. }
  assert (ZW5 : abytes SEGS (rdW W3 (ms_mem ms5)) (F + LO_B2E0) (repeat (Z_to_bv 8 0) 40)).
  { apply (r_abytes_aview_keep (w_H W3) (w_H W3) (ms_mem msB) (ms_mem ms5)); [|exact ZWB].
    intros j Hj. rewrite repeat_length in Hj. apply Heff5; rewrite ?HspB; unfold LO_B2E0, ESTACK, LLVMF_STK in *; lia. }
  assert (ZA5 : abytes SEGS (rdW W3 (ms_mem ms5)) (F + LO_B330) (repeat (Z_to_bv 8 0) 40)).
  { change 40%nat with (Z.to_nat 40). unfold LO_B330.
    apply (r_abytes_zero (w_H W3) (ms_mem ms5) (F + 816) 40); [lia | lia | lia |].
    intros j Hj. exact (Hset5 j Hj). }
  (* ---- +0xe84 .. +0xe8c: opened := g_nl.opened, into the slot s1 + 0x70; to the cut at +0xe90 ---- *)
  unfold ms5. rewrite B1. clear HS SHOK.
  assert (R9_5 : getr regs5 9 = w64 (lf_sp1 cx)) by (rewrite P9'; exact B9).
  assert (HP5s : forall a, lf_sp1 cx + 0x70 <= a < lf_sp1 cx + 0x78 -> apresent (w_H W3) mem5 a).
  { pose proof HJ5m as (_ & _ & (memSx & HJix & _) & _).
    destruct HJix as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPx & _).
    intros a Ha. apply HPx. unfold LLVMF_STK in *. lia. }
  pose proof Hsl5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & S27' & _).
  pose proof (o_entry fy cx W3 ms5 5260 md mk kbs mbs gbs R9_5 Hlo ltac:(unfold LLVMF_STK in *; lia) HP5s S27' Hdat5)
    as HS.
  change (ms_regs ms5) with regs5 in HS. change (ms_mem ms5) with mem5 in HS.
  set (E3 := Eimg (Ereg regs5 (o_extra kbs))) in HS.
  assert (HEI3 : img_env pa_val A_LIM E3) by apply Eimg_env.
  assert (EL3 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs5 r).
  { intros n r Hn Hr. unfold E3. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (U9c : bv_unsigned (ew E3 9) = lf_sp1 cx)
    by (rewrite (EL3 9%nat 9%bv ltac:(lia) eq_refl), R9_5; apply unsigned_lit_small; unfold LLVMF_STK in *; clia).
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E3
    (mrestrict (w_H W3) (ms_mem (@mkst fy regs5 (Z_to_bv 64 (BASE + 5260)) mem5 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  paj_run_to_tok RUNTO HS HJ5m SHOK (0, 0) LR_z.
  { cbn [ss_mem o_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base o_slot_rg base_val] in Ha. rewrite U9c in Ha.
      left. split; [left; unfold LLVMF_STK in *; clia | clia].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base o_gnl_rg base_val] in Ha. clia. }
  rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdC := mdx) in * end.
  assert (FdC : m_fds mdC = m_fds md5) by (subst mdC; rewrite !lf_wvb_fds; reflexivity).
  assert (FsC : m_fs mdC = m_fs md5) by (subst mdC; rewrite !lf_wvb_fs; reflexivity).
  set (X3 := fun a => lf_sp1 cx + 0x70 <= a mod 2 ^ 64 < lf_sp1 cx + 0x78).
  assert (KC : kagree SEGS X3 (rdW W3 mem5) (rdW W3 (ms_mem msC))).
  { apply (u_kagree_frame E3 (ss_mem (o_ss 5260)) _ _ X3 HFrC). intros a (r & Hr & Hw). unfold X3.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem o_ss In] in Hr. destruct Hr as [<- | [<- | []]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base o_slot_rg o_gnl_rg base_val] in Hw; [rewrite U9c in Hw; clia | clia]. }
  change mem5 with (ms_mem ms5) in KC, HGC.
  assert (HXr3 : forall a, 0 <= a < 2 ^ 64 -> X3 a -> lf_sp1 cx + LS_NIF <= a < lf_sp1 cx + LS_NIF + 8)
    by (intros a Ha HXa; unfold X3 in HXa; rewrite Z.mod_small in HXa by exact Ha; unfold LS_NIF; clia).
  destruct (r_nif_keep X3 cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms5 md5 msC mdC P N SH_R HB HJ5 Hfr KC HGC
    FdC FsC ltac:(rewrite SH_R_len; lia) HXr3 Hsv5 Hhd5 Hfs5 Hsl5 Hcur5 Hjbk5 Hblk5 Hdat5)
    as (HsvC & HhdC & HfsC & HslC & HcurC & HjbkC & HblkC & HdatC).
  pose proof alloc_ceiling_value as ((Cmin' & Cmax') & _).
  assert (BX3 : forall b n x, In (b, n) (ablocks B ly3 S3) -> b <= x < b + req_size n -> ~ X3 x).
  { intros b n x Hin Hx HXx.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms5) md5 b n HAR5 Hin) as (_ & Bb4 & Bceil & _).
    unfold X3 in HXx. rewrite Z.mod_small in HXx by clia. unfold LLVMF_STK in *. clia. }
  assert (Hb1C : 1 <= kc -> atbuf_at SEGS (rdW W3 (ms_mem msC)) t1 kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))).
  { intros H1. apply (r_atbuf_keep X3 W3 _ _ t1 kc _ KC HGC); [|exact (Hb1_5 H1)].
    intros j Hj. apply (BX3 t1 (kc + 1)); [exact (IN1 H1) | rewrite RQ by clia; clia]. }
  assert (Hb2C : 1 <= ac -> atbuf_at SEGS (rdW W3 (ms_mem msC)) t2 ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))).
  { intros H1. apply (r_atbuf_keep X3 W3 _ _ t2 ac _ KC HGC); [|exact (Hb2_5 H1)].
    intros j Hj. apply (BX3 t2 (ac + 1)); [exact (IN2 H1) | rewrite RQ by clia; clia]. }
  assert (FX3 : forall x, F <= x < F + 1024 -> ~ X3 x).
  { intros x Hx HXx. unfold X3 in HXx. rewrite Z.mod_small in HXx by (unfold F in *; clia).
    unfold F, LLVMF_STK in *. clia. }
  assert (ZWC : abytes SEGS (rdW W3 (ms_mem msC)) (F + LO_B2E0) (repeat (Z_to_bv 8 0) 40)).
  { apply (abytes_keep SEGS X3 _ _ _ _ KC); [|exact ZW5].
    intros j Hj. rewrite repeat_length in Hj. apply FX3. unfold LO_B2E0 in *. clia. }
  assert (ZAC : abytes SEGS (rdW W3 (ms_mem msC)) (F + LO_B330) (repeat (Z_to_bv 8 0) 40)).
  { apply (abytes_keep SEGS X3 _ _ _ _ KC); [|exact ZA5].
    intros j Hj. rewrite repeat_length in Hj. apply FX3. unfold LO_B330 in *. clia. }
  (* the slot s1 + 0x70 now holds opened *)
  assert (EX3 : forall j, (j < 2)%nat -> ew E3 (32 + j) = nth j (o_extra kbs) (Z_to_bv 64 0)).
  { intros j Hj. unfold E3. rewrite Eimg_low by (unfold A_TEXT; clia). apply ew_Ereg_extra. }
  pose proof Hdat5 as (_ & Dwf5 & _). pose proof Dwf5 as (_ & _ & _ & _ & _ & ROP & _).
  assert (NIF : lf_slot cx W3 msC LS_NIF (nk_opened kbs)).
  { apply (bl_slot_of fy W3 E3 ssC msC cx 0 _ LS_NIF (SOff 33 0) (nk_opened kbs) HS eq_refl eq_refl U9c).
    - vm_compute. left. reflexivity.
    - rewrite (lf_sv_off E3 33 (nk_opened kbs) 0 (EX3 1%nat ltac:(lia))) by clia. rewrite Z.add_0_r. reflexivity.
    - clia. }
  (* the registers at the cut *)
  prreg HS (2%bv : bv 5) RC2. prreg HS (3%bv : bv 5) RC3. prreg HS (4%bv : bv 5) RC4.
  prreg HS (8%bv : bv 5) RC8. prreg HS (9%bv : bv 5) RC9.
  prreg HS (18%bv : bv 5) RC18. prreg HS (19%bv : bv 5) RC19. prreg HS (20%bv : bv 5) RC20.
  prreg HS (21%bv : bv 5) RC21. prreg HS (22%bv : bv 5) RC22. prreg HS (23%bv : bv 5) RC23.
  prreg HS (24%bv : bv 5) RC24. prreg HS (25%bv : bv 5) RC25. prreg HS (26%bv : bv 5) RC26. prreg HS (27%bv : bv 5) RC27.
  rewrite (EL3 2%nat 2%bv ltac:(lia) eq_refl), P2', B2 in RC2. rewrite (EL3 3%nat 3%bv ltac:(lia) eq_refl), P3', B3 in RC3.
  rewrite (EL3 4%nat 4%bv ltac:(lia) eq_refl), P4', B4 in RC4. rewrite (EL3 8%nat 8%bv ltac:(lia) eq_refl), P8', B8 in RC8.
  rewrite (EL3 9%nat 9%bv ltac:(lia) eq_refl), P9', B9 in RC9.
  rewrite (EL3 18%nat 18%bv ltac:(lia) eq_refl), P18', B18 in RC18.
  rewrite (EL3 19%nat 19%bv ltac:(lia) eq_refl), P19', B19 in RC19.
  rewrite (EL3 20%nat 20%bv ltac:(lia) eq_refl), P20', B20 in RC20.
  rewrite (EL3 21%nat 21%bv ltac:(lia) eq_refl), P21', B21 in RC21.
  rewrite (EL3 22%nat 22%bv ltac:(lia) eq_refl), P22', B22 in RC22.
  rewrite (EL3 23%nat 23%bv ltac:(lia) eq_refl), P23', B23 in RC23.
  rewrite (EL3 24%nat 24%bv ltac:(lia) eq_refl), P24', B24 in RC24.
  rewrite (EL3 25%nat 25%bv ltac:(lia) eq_refl), P25', B25 in RC25.
  rewrite (EL3 26%nat 26%bv ltac:(lia) eq_refl), P26', B26 in RC26.
  rewrite (EL3 27%nat 27%bv ltac:(lia) eq_refl), P27', B27 in RC27.
  apply (HZ cx fy fp k2 ly3 S3 W3 msC mdC HB Hfx HJ5m Hfr).
  exists md, mk, P, N, kbs, mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
  split; [exact (lf_shape_of_st_ok fy W3 _ _ msC HS eq_refl)|].
  split; [unfold r_regs4; rewrite RC18, RC19, RC20, RC21, RC22, RC23, RC24, RC25, RC26, RC27;
          repeat split; first [reflexivity | assumption]|].
  split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
  split; [unfold lf_core; rewrite RC2, RC8, RC9, RC3, RC4; repeat split; reflexivity|].
  split; [unfold chk_cut; split; [exact HJ5m|]; split; [exact Hfr|];
          exact (conj HsvC (conj HhdC (conj HfsC (conj HslC (conj HjbkC (conj HblkC HdatC))))))|].
  split; [exact HcurC|]. split; [exact Hop|]. split; [exact Hns|]. split; [exact Hrq|]. split; [exact Hks|].
  split; [exact Hra|]. split; [exact Hbufs|]. split; [exact Hb1C|]. split; [exact Hb2C|].
  split; [exact ZWC|]. split; [exact ZAC | exact NIF].
Qed.

End a.
