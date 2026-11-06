(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 523 of its 575 lines of code are new or changed and 1280 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   from +0xb54 (Op2Cut.v o2_n_inv, the name t not empty) through the frame objects put in scope
   (+0xb54 .. +0xbe0: shadow indices 0x2c .. 0x2f, F + 0x160, and 0x34 .. 0x53, F + 0x1a0, := 0) and the call
   model_read(m, name, F + 0x160, 32, F + 0x1a0, 256) at 0x833d4 (+0xc00), to its return o2_r_inv (+0xc04).
   The shape is op_unmark's turn (Op3B.v u_head): the run's frame-shadow region, ar_leaf_call
   over model_read_c.v's contract (the Section hypothesis MODEL_READ, discharged by model_read's lane), Mdl.v's
   pieces for the Pre and lf_model_after for the cut after the call. The name's facts are Op2Nm.v's.

   o2_rd : forall POST i, FROM POST (o2_r_inv i) -> FROM POST (o2_n_inv i).

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
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the runner's state at +0xb54: the frame's shadow in two regions (their windows the two objects' 4 and 32
   granules; the 4 between are not written) and the slot of F + 0x1a0 *)
Definition o2r_fs1 : YP09.region := YP09.mkRegion (Some 19%nat) 0 48 44 48 [].
Definition o2r_fs2 : YP09.region := YP09.mkRegion (Some 19%nat) 52 112 52 84 [].
Definition o2r_sl_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_B1A0 (LS_B1A0 + 8) LS_B1A0 LS_B1A0 [YP09.mkChunk LS_B1A0 (CVal 8 (SOff 26 0x180))].
Definition o2r_facts : facts :=
  mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition o2r_ss : sstate := mkSS LO2_n sr_atoms [o2r_fs1; o2r_fs2; o2r_sl_rg] None o2r_facts.

Lemma SH_M_nth : forall i, (i < 112)%nat ->
  nth i SH_M 0 = if (((44 <=? i) && (i <? 48)) || ((52 <=? i) && (i <? 84)))%nat then 0 else nth i LF_SH0 0.
Proof. intros i Hi. do 112 (destruct i as [|i]; [reflexivity|]). lia. Qed.

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
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the two objects in scope: their bytes addressable, their shadow visible (op_unmark's u_buf_shadow) *)
Lemma o2r_buf_shadow : forall cx fp (W : world SEGS) ms o n,
  lf_fshadow cx fp W ms SH_M -> lf_F cx fp mod 32 = 0 -> 4096 <= lf_F cx fp -> lf_F cx fp + 1024 <= alloc_ceiling ->
  ((o = LO_B160 /\ n = 32) \/ (o = LO_B1A0 /\ n = 256)) ->
  range_addressable (ard SEGS (rdW W (ms_mem ms))) SHADOW_OFF (lf_F cx fp + o) n /\
  shadow_hull_vis (ard SEGS (rdW W (ms_mem ms))) (lf_F cx fp + o) n.
Proof.
  intros cx fp W ms o n Hfs' F32 F4 Fc Ho.
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
  assert (Ho0 : 0 <= o <= 416 /\ 0 < n <= 256) by (destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0; lia).
  assert (Hlo : forall x, F + o <= x < F + o + n -> o / 8 <= x / 8 - F / 8 < (o + n) / 8).
  { intros x Hx. destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0 in *;
      (split; [apply (Z.le_add_le_sub_r); apply Z.div_le_lower_bound; lia |
               apply (Z.lt_sub_lt_add_r); apply Z.div_lt_upper_bound; lia]). }
  assert (Hin : forall i, (o / 8 <= Z.of_nat i < (o + n) / 8) -> nth i SH_M 0 = 0).
  { intros i Hi. assert (Hi112 : (i < 112)%nat) by (destruct Ho as [(-> & ->) | (-> & ->)];
      unfold LO_B160, LO_B1A0 in *; cbn in Hi; lia).
    rewrite (SH_M_nth i Hi112). destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0 in *; cbn in Hi.
    - replace ((44 <=? i) && (i <? 48))%nat with true
        by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
      reflexivity.
    - replace ((52 <=? i) && (i <? 84))%nat with true
        by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
      rewrite Bool.orb_true_r. reflexivity. }
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    rewrite ard_aview. unfold shadow_of_addr.
    pose proof (Hlo x Hx) as Hix.
    replace (SHADOW_OFF + x / 8) with (lf_SH cx fp + Z.of_nat (Z.to_nat (x / 8 - F / 8))) by (rewrite SHF; lia).
    assert (Hi112 : (Z.to_nat (x / 8 - F / 8) < 112)%nat)
      by (destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0 in *; cbn in Hix; lia).
    rewrite (Hfs' (Z.to_nat (x / 8 - F / 8)) ltac:(rewrite SH_M_len; lia)).
    rewrite (Hin (Z.to_nat (x / 8 - F / 8))) by lia. reflexivity.
  - intros s Hs. rewrite ard_aview. unfold shadow_addr in Hs.
    assert (A1 : (F + o) / 8 = F / 8 + o / 8)
      by (destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0; rewrite DF at 1;
          [replace (8 * (F / 8) + 352) with ((F / 8 + 44) * 8) by lia | replace (8 * (F / 8) + 416) with ((F / 8 + 52) * 8) by lia];
          rewrite Z.div_mul by lia; lia).
    assert (A2 : (F + o + n - 1) / 8 = F / 8 + (o + n) / 8 - 1)
      by (destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0; rewrite DF at 1;
          [replace (8 * (F / 8) + 352 + 32 - 1) with (7 + (F / 8 + 47) * 8) by lia
          | replace (8 * (F / 8) + 416 + 256 - 1) with (7 + (F / 8 + 83) * 8) by lia];
          rewrite Z.div_add by lia; lia).
    rewrite A1, A2 in Hs.
    replace (SHADOW_OFF + (F / 8 + o / 8)) with (lf_SH cx fp + o / 8) in Hs by (rewrite SHF; lia).
    replace (SHADOW_OFF + (F / 8 + (o + n) / 8 - 1)) with (lf_SH cx fp + ((o + n) / 8 - 1)) in Hs by (rewrite SHF; lia).
    assert (Hl : lf_SH cx fp <= (lf_SH cx fp + o / 8) / 8 * 8)
      by (pose proof (Z.div_mod (lf_SH cx fp) 8 ltac:(lia)) as DS; pose proof (Z.mod_pos_bound (lf_SH cx fp) 8 ltac:(lia));
          assert (lf_SH cx fp mod 8 = 0 \/ lf_SH cx fp mod 8 = 4) by (rewrite <- (Z.mod_mod (lf_SH cx fp) 8) by lia;
            clear - S4; lia);
          destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0; cbn; lia).
    assert (Hu : (lf_SH cx fp + ((o + n) / 8 - 1)) / 8 * 8 + 8 <= lf_SH cx fp + 112)
      by (pose proof (Z.div_mod (lf_SH cx fp + ((o + n) / 8 - 1)) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (lf_SH cx fp + ((o + n) / 8 - 1)) 8 ltac:(lia));
          destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0 in *; cbn in *; lia).
    replace s with (lf_SH cx fp + Z.of_nat (Z.to_nat (s - lf_SH cx fp))) by lia.
    rewrite (Hfs' (Z.to_nat (s - lf_SH cx fp)) ltac:(rewrite SH_M_len; lia)). discriminate.
Qed.

(* the frame's shadow after a run that stored 0 at the indices where X holds *)
Lemma o2r_fsh_upd : forall cx fp (W : world SEGS) ms ms' (X : Z -> Prop) sh sh',
  lf_fshadow cx fp W ms sh -> kagree SEGS X (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  length sh' = length sh ->
  (forall i, (i < length sh)%nat ->
     (~ X (lf_SH cx fp + Z.of_nat i) /\ nth i sh' 0 = nth i sh 0) \/
     aview SEGS (w_H W) (ms_mem ms') (lf_SH cx fp + Z.of_nat i) = Some (nth i sh' 0)) ->
  lf_fshadow cx fp W ms' sh'.
Proof.
  intros cx fp W ms ms' X sh sh' Hf KA Hl Hc i Hi. rewrite Hl in Hi.
  destruct (Hc i Hi) as [(NX & Ne) | Hv]; [|exact Hv].
  rewrite Ne. rewrite (aview_of_kagree SEGS X _ _ _ _ _ KA NX). exact (Hf i Hi).
Qed.

(* a present range as an abuf (op_unmark's u_abuf) *)
Lemma o2r_abuf : forall H (mem : word -> option byte) a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> apresent H mem x) -> abuf SEGS (mrestrict H mem) a n.
Proof.
  intros H mem a n H0 H1 H2 HP. exists (abytes_of SEGS (mrestrict H mem) a (Z.to_nat n)).
  rewrite abytes_of_length. split; [lia|]. split.
  - apply abytes_of_abytes; [lia | lia|]. intros k Hk.
    destruct (HP (a + Z.of_nat k) ltac:(lia)) as (Hh & b & Hb). exists b. unfold mbyte, mrestrict. rewrite Hh, Hb.
    reflexivity.
  - rewrite abytes_of_length. intros k Hk. apply (apresent_writable SEGS). apply HP. lia.
Qed.

(* the facts the strcmp wrapper asks of a string, from the ones the string wrappers ask *)
Lemma o2r_cmp_of_rt : forall (regs : bvmap 5 word) K (m : word -> option byte) p (l : list byte),
  astr_rt_ok SEGS regs K m p l -> astrcmp_arg SEGS regs K m p l.
Proof.
  intros regs K m p l (H0 & H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact H0|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [exact H3|]. split; [exact H4|]. split; [exact H6 | exact H5].
Qed.

Lemma o2_rd : forall POST i,
  FROM POST (o2_r_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_n_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HR cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HN.
  destruct HN as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R18 & R21 & R22 & R26 & HM
    & Hare & Hreq0 & Hks).
  destruct HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof (lf_data_of_nm _ _ _ _ _ _ _ Hdatn Hare) as Hdat.
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)
    as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
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
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & SB1A0 & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp)
    by (rewrite E19; apply unsigned_lit_small; clear - SHB; unfold kHighMemBeg, kLowMemEnd in *; lia).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
    by (rewrite E9; apply unsigned_lit_small; clear - Hsp146 Hsp1r H470; lia).
  assert (E26 : ew E 26 = Z_to_bv 64 (lf_F cx fp + LO_WA)) by (rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl); exact R26).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2r_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_n)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2r_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, o2r_fs1, o2r_fs2, o2r_sl_rg;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U19. split; [clear - SHB; unfold kLowMemEnd in *; lia|]. split; [clear - SHB; unfold kHighMemBeg in *; lia|].
        split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clear - Ho; lia.
      + rewrite U19. split; [clear - SHB; unfold kLowMemEnd in *; lia|]. split; [clear - SHB; unfold kHighMemBeg in *; lia|].
        split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clear - Ho; lia.
      + rewrite U9. unfold LS_B1A0. split; [clear - Hsp146; lia|].
        split; [clear - Hsp146 Hsp1r H470; lia|]. split; [intros o Ho; clear - Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        unfold lf_slot, lf_at in SB1A0. unfold LS_B1A0.
        apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x48 8 (SOff 26 0x180) (lf_F cx fp + LO_B1A0));
          [ cbn [sv_denot]; rewrite E26; unfold LO_WA, LO_B1A0;
            rewrite unsigned_lit_small by (pose proof alloc_ceiling_lt; clear - F4 Fc H; lia); f_equal; lia
          | pose proof alloc_ceiling_lt; clear - F4 Fc H; unfold LO_B1A0; cbn; lia | cbn; lia
          | exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SB1A0) ].
    - apply pairwise_disjoint_of_extents. unfold o2r_fs1, o2r_fs2, o2r_sl_rg, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - SHB Hsp146 Hsp1r H470 Hal0 Hceil0. pose proof alloc_ceiling_lt as CL. unfold kHighMemBeg, kLowMemEnd, LLVMF_STK, LS_B1A0 in *. repeat split; lia.
    - split; [|split; exact I]. cbn [o2r_facts f_atoms atoms_ok]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. split; [clia|]. split; [exact (proj2 (proj2 SHB))|]. clia.
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. clear - Hsp146 Hsp1r H470 Hsp132.
        change (2 ^ 5) with 32. lia. }
  rewrite (lf_shape_eta fy LO2_n ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_n)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { cbn [ss_mem o2r_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]].
    1, 2: intros a Ha; cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2r_fs1 o2r_fs2 base_val] in Ha; rewrite U19 in Ha;
      left; split; [|clia]; right; right; right; exists LF_CID, fp; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite HFa; change (fs_frame_bytes LF_CID / 8) with 128;
      unfold shadow_addr; rewrite <- HFS; clia.
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2r_sl_rg base_val] in Ha. unfold LS_B1A0 in Ha. clia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  set (X := fun a => (lf_SH cx fp + 44 <= a mod 2 ^ 64 < lf_SH cx fp + 48) \/
                     (lf_SH cx fp + 52 <= a mod 2 ^ 64 < lf_SH cx fp + 84)).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem o2r_ss) _ _ X HFrA). intros a (r & Hr & Hw0). unfold X.
    rewrite Z_to_bv_unsigned in Hw0. unfold bv_wrap in Hw0. change (bv_modulus 64) with (2 ^ 64) in Hw0.
    cbn [ss_mem o2r_ss In] in Hr. destruct Hr as [<- | [<- | [<- | []]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2r_fs1 o2r_fs2 o2r_sl_rg base_val] in Hw0; rewrite ?U19 in Hw0;
      unfold LS_B1A0 in *; clia. }
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> X a ->
     ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_slots_fp cx a /\
     ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\ ~ lf_data_fp md mk a).
  { intros a Hf HXa. pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
      LAWS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk Hf) as R.
    unfold X in HXa. rewrite !Z.mod_small in HXa by exact (proj1 R).
    exact (u_fs_out SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk ltac:(clia)). }
  pose proof (lf_saved_keep X cx W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (NX a ltac:(tauto) HXa) Ha) Hsv) as Hsv'.
  pose proof (lf_header_keep X cx fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (NX a ltac:(tauto) HXa)) Ha) Hhd) as Hhd'.
  pose proof (lf_slots_keep X cx md mk fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (NX a ltac:(tauto) HXa))) Ha) Hsl) as Hsl'.
  pose proof (lf_cur_keep X cx W3 ms3 W3 msA P N KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))) Ha) Hcur) as Hcur'.
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))) Ha) Hjbk) as Hjbk'.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hblk) as Hblk'.
  pose proof (lf_data_keep X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    (fun a Ha HXa => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hdat) as Hdat'.
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
  assert (RG0 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 0 (ss_mem ssA) o2r_fs1))
    by exact (st_ok_region_nth E ssA (restrict (w_H W3) msA) 0 _ HS eq_refl).
  assert (RG1 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 1 (ss_mem ssA) o2r_fs1))
    by exact (st_ok_region_nth E ssA (restrict (w_H W3) msA) 1 _ HS eq_refl).
  assert (Hfs' : lf_fshadow cx fp W3 msA SH_M).
  { apply (o2r_fsh_upd cx fp W3 ms3 msA X LF_SH0 SH_M Hfs KA); [reflexivity|].
    intros i0 Hi0. assert (Hi1 : (i0 < 112)%nat) by exact Hi0.
    destruct (Nat.lt_ge_cases i0 44) as [L1 | L1];
      [left; split; [unfold X; rewrite Z.mod_small by (unfold kHighMemBeg in *; clia); clia
                    | rewrite (SH_M_nth i0 Hi1); destruct (Nat.leb_spec 44 i0), (Nat.ltb_spec i0 48), (Nat.leb_spec 52 i0),
                        (Nat.ltb_spec i0 84); cbn [andb orb]; try reflexivity; clia]|].
    destruct (Nat.lt_ge_cases i0 48) as [L2 | L2].
    { right. rewrite (SH_M_nth i0 Hi1).
      replace ((44 <=? i0) && (i0 <? 48))%nat with true
        by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
      cbn [orb].
      apply (u_byte_lit E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) 0 RG0).
      + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
      + cbn [nth ss_mem ssA setpc YP09.r_chunks].
        assert (Hk' : i0 = 44%nat \/ i0 = 45%nat \/ i0 = 46%nat \/ i0 = 47%nat) by lia.
        repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst i0. cbn [In]. tauto.
      + lia. }
    destruct (Nat.lt_ge_cases i0 52) as [L3 | L3];
      [left; split; [unfold X; rewrite Z.mod_small by (unfold kHighMemBeg in *; clia); clia
                    | rewrite (SH_M_nth i0 Hi1); destruct (Nat.leb_spec 44 i0), (Nat.ltb_spec i0 48), (Nat.leb_spec 52 i0),
                        (Nat.ltb_spec i0 84); cbn [andb orb]; try reflexivity; clia]|].
    destruct (Nat.lt_ge_cases i0 84) as [L4 | L4];
      [|left; split; [unfold X; rewrite Z.mod_small by (unfold kHighMemBeg in *; clia); clia
                     | rewrite (SH_M_nth i0 Hi1); destruct (Nat.leb_spec 44 i0), (Nat.ltb_spec i0 48), (Nat.leb_spec 52 i0),
                         (Nat.ltb_spec i0 84); cbn [andb orb]; try reflexivity; clia]].
    right. rewrite (SH_M_nth i0 Hi1).
    replace ((52 <=? i0) && (i0 <? 84))%nat with true
      by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    rewrite Bool.orb_true_r.
    apply (u_byte_lit E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) 0 RG1).
    + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
    + cbn [nth ss_mem ssA setpc YP09.r_chunks].
      assert (Hk' : exists k, (k < 32)%nat /\ i0 = (52 + k)%nat) by (exists (i0 - 52)%nat; lia).
      destruct Hk' as (k & Hk & ->).
      do 32 (destruct k as [|k]; [cbn [In Nat.add]; repeat (first [left; reflexivity | right])|]). lia.
    + lia. }
  (* the call of model_read at 0x833d4 *)
  pmkst HS.
  assert (Hpc : ss_pc ssA = pa_sigma LS_model_read) by reflexivity.
  rewrite Hpc, (lv_sigma LV).
  replace (link_sigma LS_model_read) with MODEL_READ_A by reflexivity.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  try rewrite (img_env_codeptr E HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl), R22 in Q10.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl), R20 in Q11. rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl), R18 in Q12.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9.
  rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20.
  rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  set (F := lf_F cx fp) in *.
  assert (Fb : 4096 <= F /\ F + 1024 <= alloc_ceiling) by (split; assumption).
  pose proof alloc_ceiling_lt as CL.
  assert (W14 : getr (ms_regs msA) 14 = w64 (F + LO_B1A0)).
  { rewrite Q14. cbn [sv_denot]. rewrite E26. unfold w64, LO_WA, LO_B1A0.
    rewrite unsigned_lit_small by (clear - Fb CL; lia). f_equal. lia. }
  assert (W21 : getr (ms_regs msA) 21 = w64 (F + LO_B1A0)).
  { rewrite Q21. cbn [sv_denot]. rewrite E26. unfold w64, LO_WA, LO_B1A0.
    rewrite unsigned_lit_small by (clear - Fb CL; lia). f_equal. lia. }
  pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  pose proof (lv_text LV) as HBASE.
  pose proof Hblk' as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
    & Bamm & Bamk).
  pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) md4 md MD_SIZE HARA Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite Q2. unfold w64. apply unsigned_lit_small. clear - Hsp146 Hsp1r H470. lia. }
  assert (Ra0 : aarg (ms_regs msA) 0 = md) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; clia).
  pose proof Hjbk' as (Jk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hdat' as (Dk & Dwf & Dtab & _ & _ & _ & Dmd & Dmwf & _ & _ & (Dmn & Dmm) & _ & Dgn & _).
  assert (HK8 : 0 <= MODEL_READ_AK <= LLVMF_STK - 448) by (rewrite MODEL_READ_AK_val; unfold LLVMF_STK; lia).
  assert (HKc : alloc_ceiling <= spZ (ms_regs msA) - MODEL_READ_AK)
    by (rewrite Rsp, MODEL_READ_AK_val; clear - Hsp1r Hceil0; unfold LLVMF_STK in *; lia).
  destruct (o2_name_rt B TB HSEGS ly3 S3 W3 (ms_mem msA) md4 (ms_regs msA) MODEL_READ_AK s t HARA HRO Dgn HKc Hw)
    as (Hac & Hrt & Hs16 & Hl11 & Hloc).
  assert (Hsb : 0x10000 <= s < 0x654000) by (clear - Hs16 Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia).
  assert (Hsg : s + Z.of_nat (length t) + 1 <= LA_G_NL \/ LA_G_NL + NK_SIZE <= s).
  { clear - Hs16 Hloc. unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE, NK_SIZE in *. lia. }
  assert (Ra1 : aarg (ms_regs msA) 1 = s) by (rewrite ar_aarg1, Q11; unfold w64; apply unsigned_lit_small; clear - Hsb; lia).
  assert (Ra2 : aarg (ms_regs msA) 2 = F + LO_B160)
    by (rewrite ar_aarg2, Q12; unfold w64; apply unsigned_lit_small; unfold LO_B160; clear - Fb CL; lia).
  assert (Ra3 : aarg (ms_regs msA) 3 = 32) by (rewrite ar_aarg3, Q13; reflexivity).
  assert (Ra4 : aarg (ms_regs msA) 4 = F + LO_B1A0)
    by (rewrite ar_aarg4, W14; unfold w64; apply unsigned_lit_small; unfold LO_B1A0; clear - Fb CL; lia).
  assert (Ra5 : aarg (ms_regs msA) 5 = 256) by (rewrite ar_aarg5, Q15; reflexivity).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem msA) md4 k2 HB HJ Hfr) as (HFa2 & _ & _ & _ & _ & Fpres2 & Fshp2 & Fsep2).
  pose proof (Fsep2 md MD_SIZE Bmd) as DmF. unfold zdisjoint in DmF. cbn [fst snd] in DmF.
  change (req_size MD_SIZE) with 8856 in DmF.
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) MODEL_READ_AK HB HJ Hblk' Rsp HK8)
    as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  assert (BUFI : forall x, F + LO_B160 <= x < F + LO_B1A0 + 256 -> ~ in_img SEGS x /\ apresent (w_H W3) (ms_mem msA) x)
    by (intros x Hx; destruct (Fpres2 x ltac:(unfold LO_B160, LO_B1A0 in *; clia)) as (P1 & P2); exact (conj P2 P1)).
  assert (NIMG : forall x, s <= x < s + Z.of_nat (length t) + 1 -> in_img SEGS x)
    by (intros x Hx; exact (proj1 (o2_name_img B TB HSEGS MS la_nul s t HMS HLN Hw x Hx))).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 MODEL_READ_A) (ms_mem msA) (seg_rom SEGS)) md4)
    with (@cfg_at fy SEGS MODEL_READ_A (ms_regs msA) (ms_mem msA) md4).
  assert (Hj0 : F + LO_B160 =? 0 = false) by (apply Z.eqb_neq; unfold LO_B160; clear - Fb; lia).
  assert (Hj1 : F + LO_B1A0 =? 0 = false) by (apply Z.eqb_neq; unfold LO_B1A0; clear - Fb; lia).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (MODEL_READ fy).
  - exact HB.
  - exact HJ.
  - exact HRO.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite Q3. exact Gp.
  - rewrite Q4. exact Tp.
  - exact Rsp.
  - exact HK8.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
  - apply (ar_side_room S3 fp _ Hfr). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
    rewrite Hj0, Hj1 in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Bmd Bmc). unfold MD_SIZE in *. clia.
    + apply (ar_ajw_frame B); [rewrite HFa2; change (fs_frame_bytes LF_CID) with 1024; unfold LO_B160 in *; clia|].
      intros Hs0. unfold LLVMF_STK, LO_B160 in *. clia.
    + apply (ar_ajw_frame B); [rewrite HFa2; change (fs_frame_bytes LF_CID) with 1024; unfold LO_B1A0 in *; clia|].
      intros Hs0. unfold LLVMF_STK, LO_B1A0 in *. clia.
  - intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
    rewrite Hj0, Hj1 in Hin.
    intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in *. clia.
    + destruct (BUFI a ltac:(unfold LO_B160, LO_B1A0 in *; clia)) as (NI & _). apply NI.
      destruct Hro as [(s0 & Hs0 & _ & Hsr) | Hr2]; [exists s0; split; [exact Hs0 | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2).
    + destruct (BUFI a ltac:(unfold LO_B160, LO_B1A0 in *; clia)) as (NI & _). apply NI.
      destruct Hro as [(s0 & Hs0 & _ & Hsr) | Hr2]; [exists s0; split; [exact Hs0 | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2).
  - (* the read set: the name, the table strings *)
    intros a [(H1 & s0 & Hs0 & Ha) | (bs & i0 & p & s0 & Hbs & Hi0 & Hp & Hs0 & Ha)].
    + rewrite Ra1 in Hs0, Ha. pose proof (kp_acstr_unique _ _ _ _ _ Hs0 Hac) as Es. subst s0.
      right; right; left. exact (o2_name_img B TB HSEGS MS la_nul s t HMS HLN Hw a ltac:(clia)).
    + exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs _ _ HB HJ HRO Hdat' bs i0 p s0 a Hbs Hi0 Hp Hs0 Ha).
  - (* the Pre *)
    destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & _).
    destruct (o2r_buf_shadow cx fp W3 msA LO_B160 32 Hfs' F32 F4 Fc ltac:(left; split; reflexivity)) as (BRA0 & BHV0).
    destruct (o2r_buf_shadow cx fp W3 msA LO_B1A0 256 Hfs' F32 F4 Fc ltac:(right; split; reflexivity)) as (BRA1 & BHV1).
    fold F in BRA0, BHV0, BRA1, BHV1.
    exists mbs, kbs, lf_tab, (Some t).
    rewrite Ra0, Ra1, Ra2, Ra3, Ra4, Ra5.
    split; [exact Dmd|]. split; [exact Dmwf|]. split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dtab|].
    split; [split; [clear - Hsb; lia | exact Hac]|].
    split; [intros _ _; apply o2r_abuf; [unfold LO_B160; clear - Fb; lia | lia | unfold LO_B160; clear - Fb CL; lia |];
      intros x Hx; exact (proj2 (BUFI x ltac:(unfold LO_B160, LO_B1A0 in *; clia)))|].
    split; [intros _ _; apply o2r_abuf; [unfold LO_B1A0; clear - Fb; lia | lia | unfold LO_B1A0; clear - Fb CL; lia |];
      intros x Hx; exact (proj2 (BUFI x ltac:(unfold LO_B160, LO_B1A0 in *; clia)))|].
    split; [exact M1|]. split; [exact M2|].
    split; [intros s1 Hs1'; injection Hs1' as <-; exact (o2r_cmp_of_rt _ _ _ _ _ Hrt)|].
    split.
    { intros i0 n2 ix p Hn Hp Rp.
      exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs (ms_regs msA) MODEL_READ_AK HB HJ HRO Hdat' Rsp HK8
        i0 n2 ix p Hn Hp Rp)). }
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].
    split; [exact M8|]. split; [exact M9|].
    split; [intros _; unfold apart_frame; left; rewrite Rsp; rewrite MODEL_READ_AK_val; unfold LO_B160, LLVMF_STK in *; clia|].
    split; [intros _; unfold apart_frame; left; rewrite Rsp; rewrite MODEL_READ_AK_val; unfold LO_B1A0, LLVMF_STK in *; clia|].
    split; [rewrite (ts_errno B TB); unfold apart, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO,
      MD_SIZE in *; clia|].
    split; [intros _ _; apply md_apart_of_disj; [lia | lia|]; intros x H1 H2;
      exact (proj1 (BUFI x ltac:(unfold LO_B160, LO_B1A0 in *; clia)) (md_errno_img B TB HSEGS x H1))|].
    split; [intros _ _; apply md_apart_of_disj; [lia | lia|]; intros x H1 H2;
      exact (proj1 (BUFI x ltac:(unfold LO_B160, LO_B1A0 in *; clia)) (md_errno_img B TB HSEGS x H1))|].
    assert (BUFD : forall o n, ((o = LO_B160 /\ n = 32) \/ (o = LO_B1A0 /\ n = 256)) ->
      apart_gnl LA_G_NL (F + o) n /\ apart (F + o) n md MD_SIZE /\
      (forall i0 n2 ix p, nth_error lf_tab i0 = Some (n2, ix) ->
         au64_at SEGS (rdW W3 (ms_mem msA)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i0) p ->
         apart (F + o) n p (Z.of_nat (length n2) + 1)) /\
      amem_range (F + o) n).
    { intros o n Ho. assert (Hon : F + LO_B160 <= F + o /\ F + o + n <= F + LO_B1A0 + 256 /\ 0 < n)
        by (destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0; lia).
      split.
      { assert (Ap : apart (F + o) n LA_G_NL NK_SIZE).
        { apply md_apart_of_disj; [lia | unfold NK_SIZE; lia|]. intros x H1 H2.
          apply (proj1 (BUFI x ltac:(clia))). apply (proj1 (IMG x ltac:(left; exact H2))). }
        unfold apart in Ap. unfold apart_gnl. exact Ap. }
      split; [unfold apart, LO_B160, LO_B1A0, MD_SIZE in *; clia|].
      split.
      { intros i0 n2 ix p Hn Hp.
        pose proof (lf_tab_names_short) as Hsn. rewrite forallb_forall in Hsn.
        specialize (Hsn (n2, ix) (nth_error_In _ _ Hn)). apply Nat.leb_le in Hsn. cbn [fst] in Hsn.
        destruct (Z_lt_le_dec p 0) as [Hp0 | Hp0]; [clear - Hp0 Hon Hsn Fb; unfold apart, LO_B160, LO_B1A0 in *; lia|].
        destruct (Z_lt_le_dec p (2 ^ 64)) as [Hp1 | Hp1];
          [|clear - Hp1 Hon Hsn Fb CL; unfold apart, LO_B160, LO_B1A0 in *; lia].
        destruct (lf_tab_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs HB HJ HRO Hdat' i0 n2 ix p Hn Hp ltac:(lia))
          as (_ & _ & _ & _ & _ & _ & _ & C7).
        apply md_apart_of_disj; [lia | lia|]. intros x H1 H2.
        exact (proj1 (BUFI x ltac:(clia)) (proj1 (C7 x ltac:(lia)))). }
      destruct Fapp as (Fa1 & Fa2); unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
        kHighMemEnd, ASAN_CEIL, LO_B160, LO_B1A0 in *; clia. }
    destruct (BUFD LO_B160 32 ltac:(left; split; reflexivity)) as (G0 & D0 & T0 & A0).
    destruct (BUFD LO_B1A0 256 ltac:(right; split; reflexivity)) as (G1 & D1 & T1 & A1).
    split; [intros _ _; split; [exact G0|]; split; [exact D0|]; split; [exact T0|]; split; [exact A0|];
      split; [exact BRA0 | exact BHV0]|].
    split; [intros _ _; split; [exact G1|]; split; [exact D1|]; split; [exact T1|]; split; [exact A1|];
      split; [exact BRA1 | exact BHV1]|].
    split.
    { intros s1 Hs1'. injection Hs1' as <-. split.
      - intros _ _. apply md_apart_of_disj; [lia | lia|]. intros x H1 H2.
        exact (proj1 (BUFI x ltac:(unfold LO_B160, LO_B1A0 in *; clia)) (NIMG x ltac:(clear - H2; lia))).
      - intros _ _. apply md_apart_of_disj; [lia | lia|]. intros x H1 H2.
        exact (proj1 (BUFI x ltac:(unfold LO_B160, LO_B1A0 in *; clia)) (NIMG x ltac:(clear - H2; lia))). }
    intros _ _ _ _. unfold apart, LO_B160, LO_B1A0. lia.
  - (* the return, +0xc04 *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (model_read_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (LC : lf_call B cx MODEL_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
    { split; [lia|]. split; [rewrite MODEL_READ_AK_val; unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
    assert (HE : forall a, Er a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)).
    { intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
      rewrite Hj0, Hj1 in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn in Hr; [left; exact Hr | right; unfold LO_B160 in *; fold F; clia
        | right; unfold LO_B1A0 in *; fold F; clia]. }
    pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
    assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
    assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
    pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msA)) md mk HAR2 Pmd Pmk) as WC.
    specialize (Hpost mbs kbs lf_tab (Some t)). rewrite Ra0, Ra1, Ra2, Ra3, Ra4, Ra5 in Hpost.
    destruct (Hpost Dmd Dk Dtab ltac:(split; [clear - Hsb; lia | exact Hac]))
      as (Hrc & (mbs' & Hmd2 & Hmwf2 & Hnx2 & Hso2 & Hse2 & Hrq2 & Hnr2 & Hnm2 & Hmm2) & Hkd & Hal & Hkb & Hab).
    clear Hpost.
    destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp MODEL_READ_AK ly3 S3 ly2 S2 W3 msA md4 W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs' T3 _ P N SH_M
      HB HJ Hfr LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(rewrite SH_M_len; lia) Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat'
      Hmd2 Hmwf2 Hnm2 Hmm2) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
    pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
      ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
    pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    apply (HR cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, s, t, kbs, mbs', gbs, T3.
    assert (HRR : o2_RR t kbs = read_model lf_tab (Some t) 32 256 (md_reqs mbs) (md_kstate mbs kbs))
      by (unfold o2_RR; rewrite Hreq0, Hks; reflexivity).
    rewrite HRR.
    pose proof Hdat2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hare2 & _).
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1. unfold LO2_r, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    cbn [ms_regs ms2 mkst].
    split; [rewrite P20, Q20; exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite P18, Q18; exact R18|]. split; [rewrite P21; exact W21|].
    split; [rewrite P22, Q22; exact R22|]. split; [rewrite P26, Q26; exact R26|].
    split.
    { split; [exact Hi|]. split.
      { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
        rewrite R8, R9. repeat split; assumption. }
      split.
      { unfold o2_kregs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P24, P25, P27, Q19, Q24, Q25, Q27.
        repeat split; assumption. }
      split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hcur2|].
      split; [exact Hjbk3|]. split; [exact Hblk3|]. split; [exact (lf_data_nm_of _ _ _ _ _ _ _ Hdat2)|].
      split; [exact Hop | exact Hns]. }
    split; [exact Hare2|].
    split; [exact Hrc|].
    cbn [read_model r_rc r_kind r_alias r_reqs r_state] in Hnx2, Hso2, Hse2, Hrq2, Hkd, Hal, Hkb, Hab |- *.
    split; [exact Hrq2|].
    split.
    { destruct (u_read_ce lf_tab (Some t) 32 256 (md_reqs mbs) (md_kstate mbs kbs)) as (Ce & Ee).
      apply u_md_kstate_of; [exact Hnx2 | exact Hso2 | exact Hse2 | rewrite Ce; reflexivity | rewrite Ee; reflexivity]. }
    split; [exact (Hkd ltac:(unfold LO_B160; clia) ltac:(lia))|].
    split; [exact (Hal ltac:(unfold LO_B1A0; clia) ltac:(lia))|].
    split; [exact (Hkb ltac:(unfold LO_B160; clia) ltac:(lia)) | exact (Hab ltac:(unfold LO_B1A0; clia) ltac:(lia))].
Qed.

End a.
