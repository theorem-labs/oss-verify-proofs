(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module names changed; 802 of its 861 lines of code are new or changed and 299 lines of the source are left out. *)
(* model_read on image A: the tail of its walk, from the branch on name at +0x15c (model_readDefs.v MR_AT15C, the
   frame's regions set aside) to the exit: the -EINVAL refusals (no name, an empty name), the call of index_of and
   the -ENODEV refusal, and the read (checked_memset, the request in the frame, talk) to the exit +0x208, where
   model_readExit.v mr_exit_d ends every path.
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs model_readExit model_readKit PaJournalFs model_readStr model_readCall LinkWalkZsh model_readWr model_readRq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis TB : PcapSyms B.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes *)
Hypothesis AMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
(* the two own callees *)
Hypothesis IDX : forall rlo rhi, index_of_acontract SK pa_segs rlo rhi B.
Hypothesis TALK : forall rlo rhi, talk_acontract SK pa_segs rlo rhi B.

Lemma mr_tail : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md S1 pos
    m120 md1,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  MR_AT15C SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md S1 pos m120 md1 ->
  SRr pa_segs W (mkCfg ms md) (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof using LAWS TL LV HSEGS TB AMSET IDX TALK.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md S1 pos m120 md1 HENT
  (HEI & HAE & E32 & E44 & E60 & E61 & E62 & HS15 & HJm & Hsm & HAR1 & Hfrs1 & Eab1 & Hnin1 & Hfs1 & VFL120 & WR120
   & HGm & HKm & HFRS & HK0 & HA0).
set (POST := MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
pose proof HENT as (HPRE & HRD & HP).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK8 : MODEL_READ_AK = 8416) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(lia) Hwhi) as (memS & HJi & HSTK & HXO & Hpresw & Hceil47).
destruct Hceil47 as (Hceil & H47).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
pose proof HAR1 as [M1 _].
destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Hc1 & Hp1 & _).
destruct (frames_bounds pa_segs B LAWS lyc S1 W m120 md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
set (F := frame_addr lyc 1 pos) in *.
change (fs_frame_bytes 1) with 128 in *.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite (proj1 HAE r Hr). apply ew_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (EARG : forall i, 0 <= i < 8 -> ew E (Z.to_nat (10 + i)) = Z_to_bv 64 (aarg regs i)).
{ intros i Hi. rewrite EREG by lia. unfold aarg, argZ. rewrite Z2Nat.id by lia.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (E11 : ew E 11 = Z_to_bv 64 (aarg regs 1)) by exact (EARG 1 ltac:(lia)).
assert (AR1 : 0 <= aarg regs 1 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR2 : 0 <= aarg regs 2 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR3 : 0 <= aarg regs 3 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR4 : 0 <= aarg regs 4 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR5 : 0 <= aarg regs 5 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNP := paj_run_plain_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (U60 : bv_unsigned (ew E 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EREG 2%nat ltac:(lia)); reflexivity).
assert (Hsk : alloc_ceiling <= spZ regs - MODEL_READ_AK) by lia.
set (KB := fun a => aarg regs 2 <> 0 /\ 1 <= aarg regs 3 /\ a = aarg regs 2) in *.
set (AB := fun a => aarg regs 4 <> 0 /\ 1 <= aarg regs 5 /\ a = aarg regs 4) in *.
set (FRS := fun a => in_zr a (frame_rng lyc (1, pos)) \/ in_zr a (shadow_addr F, 16)) in *.
assert (FRSlo : forall a, FRS a -> a < alloc_ceiling).
{ intros a [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
    change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia. }
assert (KBW : forall a, KB a -> inFP (model_read_awr regs (rdW W memc)) a).
{ intros a (h2 & h3 & ->). exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lia].
  right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity. }
assert (ABW : forall a, AB a -> inFP (model_read_awr regs (rdW W memc)) a).
{ intros a (h4 & h5 & ->). exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lia].
  right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity. }
assert (WRF : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
          (a < kLowMemEnd \/ kHighMemBeg <= a) /\ ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) /\ 0 <= a < 2 ^ 64 /\
          ~ aside_rng lyc 1 pos a).
{ intros a Ha. destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    HENT a Ha) as (Xapp & Xwin & _ & Xajw & X64).
  refine (conj Xapp (conj Xwin (conj X64 _))).
  exact (ajw_not_side SK pa_segs B LAWS pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k 1 pos _ HGok HJ Hc1 Hp1 Hnin1 Xajw Xapp). }
assert (WRG : forall a (m : word -> option byte), inFP (model_read_awr regs (rdW W memc)) a ->
          writable_at pa_segs (rdW W memc) a -> mem_grows (rdW W m120) (rdW W m) -> writable_at pa_segs (rdW W m) a).
{ intros a m Ha Hw Hg. apply (writable_kept (w_H W) m120 m a); [intros Hp; exact (apresent_grows _ _ _ _ Hg Hp)|].
  exact (WR120 a Ha Hw). }
pose (RUNPT := paj_run_to_plain_x SK B LAWS G HGok XO OUT).
assert (U44 : bv_unsigned (ew E 44) = F) by (rewrite E44; apply unsigned_lit_small; lia).
(* the frame's flag word at +0x120, and later where the frame's bytes did not change *)
assert (VFLm : forall (W2 : world pa_segs) (m2 : word -> option byte),
  (forall a, FRS a -> aview pa_segs (w_H W2) m2 a = aview pa_segs (w_H W) m120 a) ->
  val_mem pa_segs (rdW W2 m2) (F + 120) 8 (flag_addr lyc 1 pos)).
{ intros W2 m2 HFx kk Hkk. transitivity (mbyte pa_segs (rdW W m120) (F + 120 + Z.of_nat kk));
    [|exact (VFL120 kk Hkk)].
  apply (mbyte_of_aview pa_segs). apply HFx. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
  change (fs_frame_bytes 1) with 128. lia. }
(* the bytes of the write set at a later memory *)
assert (AU8 : forall (W2 : world pa_segs) (m2 : word -> option byte) p bs,
  (forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
     writable_at pa_segs (rdW W2 m2) a) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> inFP (model_read_awr regs (rdW W memc)) (p + i)) ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     aview pa_segs (w_H W2) m2 (p + i) = aview pa_segs (w_H W) memc (p + i)) ->
  au8arr pa_segs (rdW W memc) p bs -> au8arr pa_segs (rdW W2 m2) p bs).
{ intros W2 m2 p bs WRX HWi HV ((H0 & H1 & Hb) & Hw).
  split; [split; [exact H0|]; split; [exact H1|] |].
  - intros i Hi. transitivity (mbyte pa_segs (rdW W memc) (p + Z.of_nat i)); [|exact (Hb i Hi)].
    apply (mbyte_of_aview pa_segs). apply HV. lia.
  - intros i Hi. apply WRX; [apply HWi; exact Hi | exact (Hw i Hi)]. }
assert (BUFZ : forall (W2 : world pa_segs) (m2 : word -> option byte) p n,
  (forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
     writable_at pa_segs (rdW W2 m2) a) ->
  1 <= n -> (forall i, 0 <= i < n -> inFP (model_read_awr regs (rdW W memc)) (p + i)) ->
  (forall i, 1 <= i < n -> aview pa_segs (w_H W2) m2 (p + i) = aview pa_segs (w_H W) memc (p + i)) ->
  aview pa_segs (w_H W2) m2 p = Some 0 -> abuf pa_segs (rdW W memc) p n ->
  acstr_at pa_segs (rdW W2 m2) p [] /\ abuf pa_segs (rdW W2 m2) p n).
{ intros W2 m2 p n WRX Hn HWi HV H0 (junk & Hl & ((J0 & J1 & Jb) & Jw)).
  assert (MB0 : mbyte pa_segs (rdW W2 m2) p = Some (zb 0)).
  { unfold aview in H0. destruct (mbyte pa_segs (rdW W2 m2) p) as [b|] eqn:Eb; [|discriminate].
    cbn [option_map] in H0. injection H0 as H0. f_equal. apply bv_eq. rewrite H0. reflexivity. }
  destruct junk as [|j0 jt]; [cbn [length] in Hl; lia|].
  cbn [length] in Hl, J1.
  split.
  - split; [|intros []]. split; [exact J0|]. split; [cbn [length app]; lia|].
    intros i Hi. cbn [length app] in Hi. destruct i as [|i]; [|lia]. rewrite Z.add_0_r. exact MB0.
  - exists (zb 0 :: jt). split; [cbn [length]; lia|]. split.
    + split; [exact J0|]. split; [cbn [length]; lia|].
      intros i Hi. destruct i as [|i].
      * rewrite Z.add_0_r. exact MB0.
      * cbn [nth_error]. transitivity (mbyte pa_segs (rdW W memc) (p + Z.of_nat (Datatypes.S i))).
        { apply (mbyte_of_aview pa_segs). apply HV. cbn [length] in Hi. lia. }
        exact (Jb (Datatypes.S i) Hi).
    + intros i Hi. cbn [length] in Hi. apply WRX; [apply HWi; lia | exact (Jw i ltac:(cbn [length]; lia))]. }
pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & PMOD & PMWF & PNLK & PNWF & PTAB & PNM & PBK & PBA & PRAN & PRAI & PSCN
  & PSCT & PRAM & PHUM & PMR & PRAC & PHUC & PGNM & PFRM & PFRK & PFRA & PERM & PERK & PERA & PKB & PAB & PNSEP
  & PKA).
assert (QMR : forall (W2 : world pa_segs) (m2 : word -> option byte) rcv,
  (forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
     writable_at pa_segs (rdW W2 m2) a) ->
  (forall a, inFP (model_read_awr regs (rdW W memc)) a -> ~ KB a -> ~ AB a ->
     aview pa_segs (w_H W2) m2 a = aview pa_segs (w_H W) memc a) ->
  (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W2) m2 (aarg regs 2) = Some 0) ->
  (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> aview pa_segs (w_H W2) m2 (aarg regs 4) = Some 0) ->
  (forall mbs kbs tab nm, amodel_at pa_segs (rdW W memc) (aarg regs 0) mbs ->
     anlk_at pa_segs (rdW W memc) LA_G_NL kbs -> aiftab_at pa_segs (rdW W memc) LA_G_NL kbs tab ->
     astr_arg pa_segs (rdW W memc) (aarg regs 1) nm ->
     read_core tab nm (aarg regs 3) (aarg regs 5) (md_reqs mbs) (md_kstate mbs kbs)
       = Rres rcv [] [] (md_reqs mbs) (md_kstate mbs kbs)) ->
  MR_QM regs W memc (norm_rc rcv) (rdW W2 m2)).
{ intros W2 m2 rcv WRX HV HKq HAq HRC. unfold MR_QM, model_read_apost.
  intros regs' R10 mbs kbs tab nm Hm Hk Ht Hn. cbv zeta.
  unfold read_model. rewrite (HRC mbs kbs tab nm Hm Hk Ht Hn). cbn [r_rc r_kind r_alias r_reqs r_state].
  assert (Emb : mbs = mbs0).
  { destruct Hm as (((_ & _ & Hb1) & _) & Hl1). destruct PMOD as (((_ & _ & Hb2) & _) & Hl2).
    apply lw_list_ext; [lia|]. intros kk Hkk. rewrite <- (Hb1 kk Hkk), <- (Hb2 kk ltac:(lia)). reflexivity. }
  subst mbs. pose proof PMWF as (Wq1 & Wq2 & _).
  assert (BLK : forall i, 0 <= i < MD_SIZE -> inFP (model_read_awr regs (rdW W memc)) (aarg regs 0 + i)).
  { intros i Hi. exists (aarg regs 0, aarg regs 0 + MD_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (KNB : forall a, KB a -> ~ (aarg regs 0 <= a < aarg regs 0 + MD_SIZE)).
  { intros a (h2 & h3 & ->) Ha. destruct (PKB h2 h3) as (_ & KM & _). unfold apart in KM. lia. }
  assert (ANB : forall a, AB a -> ~ (aarg regs 0 <= a < aarg regs 0 + MD_SIZE)).
  { intros a (h4 & h5 & ->) Ha. destruct (PAB h4 h5) as (_ & AM & _). unfold apart in AM. lia. }
  refine (conj R10 (conj _ (conj _ (conj _ (conj _ _))))).
  - exists mbs0. split; [split; [|exact (proj2 PMOD)] |].
    + apply (AU8 W2 m2 _ _ WRX); [rewrite (proj2 PMOD); exact BLK | | exact (proj1 PMOD)].
      intros i Hi. rewrite (proj2 PMOD) in Hi. apply HV; [exact (BLK i Hi) | |].
      * intros HKb. exact (KNB _ HKb ltac:(lia)).
      * intros HAb. exact (ANB _ HAb ltac:(lia)).
    + split; [exact PMWF|]. cbn [md_kstate k_next k_sock k_send].
      split; [rewrite Z2Nat.id by lia; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold md_reqs; rewrite length_map, length_seq, Z2Nat.id by lia; reflexivity|].
      split; reflexivity.
  - intros h2 h3. refine (proj1 (BUFZ W2 m2 _ _ WRX h3 _ _ (HKq h2 h3) (PBK h2 h3))).
    + intros i Hi. exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lia].
      right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity.
    + intros i Hi. apply HV.
      * exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lia].
        right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity.
      * intros (_ & _ & Hq). lia.
      * intros (h4 & h5 & Hq). pose proof (PKA h2 h4 h3 h5) as Hs. unfold apart in Hs. lia.
  - intros h4 h5. refine (proj1 (BUFZ W2 m2 _ _ WRX h5 _ _ (HAq h4 h5) (PBA h4 h5))).
    + intros i Hi. exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lia].
      right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity.
    + intros i Hi. apply HV.
      * exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lia].
        right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity.
      * intros (h2 & h3 & Hq). pose proof (PKA h2 h4 h3 h5) as Hs. unfold apart in Hs. lia.
      * intros (_ & _ & Hq). lia.
  - intros h2 h3. refine (proj2 (BUFZ W2 m2 _ _ WRX h3 _ _ (HKq h2 h3) (PBK h2 h3))).
    + intros i Hi. exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lia].
      right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity.
    + intros i Hi. apply HV.
      * exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lia].
        right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity.
      * intros (_ & _ & Hq). lia.
      * intros (h4 & h5 & Hq). pose proof (PKA h2 h4 h3 h5) as Hs. unfold apart in Hs. lia.
  - intros h4 h5. refine (proj2 (BUFZ W2 m2 _ _ WRX h5 _ _ (HAq h4 h5) (PBA h4 h5))).
    + intros i Hi. exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lia].
      right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity.
    + intros i Hi. apply HV.
      * exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lia].
        right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity.
      * intros (h2 & h3 & Hq). pose proof (PKA h2 h4 h3 h5) as Hs. unfold apart in Hs. lia.
      * intros (_ & _ & Hq). lia. }
assert (EXIT : forall E2 ms2 md2 (W2 : world pa_segs) ly2 S2 k2 rcv,
  img_env pa_val A_LIM E2 -> env_agree 512 E E2 ->
  st_ok_pi pa_segs pa_val E2 mr_ss208d (restrict (w_H W2) ms2) ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 (ms_mem ms2) md2 k2 ->
  k2 <= k -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  akept pa_segs B lyc Sc W memc W2 (ms_mem ms2) (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => aside_rng lyc 1 pos a \/ KB a \/ AB a) ->
  (forall a, FRS a -> aview pa_segs (w_H W2) (ms_mem ms2) a = aview pa_segs (w_H W) m120 a) ->
  getr (ms_regs ms2) 10 = w64 rcv -> MR_QM regs W memc rcv (rdW W2 (ms_mem ms2)) ->
  SRr pa_segs W2 (mkCfg ms2 md2) POST).
{ intros E2 ms2 md2 W2 ly2 S2 k2 rcv HEI2 OLD2 HS2 HJ2 Hk2 Hfs2 Hperm2 Hfd2 Hfsy2 HK2 HFRS2 R10 HQ.
  assert (EQ : forall n, (n < 512)%nat -> ew E2 n = ew E n) by exact (proj1 OLD2).
  unfold POST.
  refine (mr_exit_d SK B LAWS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E2 ms2 md2
    ly2 S2 W2 k2 pos rcv HENT HEI2 _ _ _ _ _ _ HS2 (VFLm W2 (ms_mem ms2) HFRS2) HJ2 Hk2 Hfs2 Hperm2
    (ex_intro _ S1 (ex_intro _ W (ex_intro _ m120 (ex_intro _ md1 (conj HAR1 (conj Hfrs1 Eab1)))))) Hnin1 _
    Hfd2 Hfsy2 R10 HQ).
  - split; [intros n Hn; rewrite EQ by lia; exact (proj1 HAE n Hn) | rewrite (proj2 OLD2); exact (proj2 HAE)].
  - rewrite EQ by lia. exact E32.
  - rewrite EQ by lia. exact E44.
  - rewrite EQ by lia. exact E60.
  - rewrite EQ by lia. exact E61.
  - rewrite EQ by lia. exact E62.
  - exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W2 (ms_mem ms2) W2 (ms_mem ms2)
      (spZ regs - MODEL_READ_AK) (spZ regs) (fun a => aside_rng lyc 1 pos a \/ KB a \/ AB a)
      (fun a => inFP (model_read_awr regs (rdW W memc)) a \/ aside_rng lyc 1 pos a)
      (fun _ => False) HAR Hsk ltac:(lia) HK2 (fun a _ _ => eq_refl)
      (fun a _ Hp => Hp)
      ltac:(intros a Ha; cbv beta in Ha |- *; destruct Ha as [Ha | [Ha | Ha]];
            [right; exact Ha | left; exact (KBW a Ha) | left; exact (ABW a Ha)])
      (fun a H => False_ind _ H)). }
set (m15 := ms_mem ms) in *.
set (EX2 := fun a => aside_rng lyc 1 pos a \/ KB a \/ AB a) in *.
assert (WRX15 : forall (m2 : word -> option byte), mem_grows (rdW W m15) (rdW W m2) ->
          forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
          writable_at pa_segs (rdW W m2) a)
  by (intros m2 Hg a Ha Hw; exact (WRG a m2 Ha Hw (mem_grows_trans _ _ _ HGm Hg))).
assert (HVX : forall (m2 : word -> option byte),
          akept pa_segs B lyc Sc W memc W m2 (spZ regs - MODEL_READ_AK) (spZ regs) EX2 ->
          forall a, inFP (model_read_awr regs (rdW W memc)) a -> ~ KB a -> ~ AB a ->
          aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) memc a).
{ intros m2 HKx a Ha Hk Hab. destruct (WRF a Ha) as (_ & _ & _ & XNS).
  exact (mr_wr_view SK B LAWS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W m2 EX2 a
    HENT Ha HKx ltac:(intros [Hq | [Hq | Hq]]; [exact (XNS Hq) | exact (Hk Hq) | exact (Hab Hq)])). }
assert (STEP15 : forall (m2 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) ->
     aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) m15 a) ->
  mem_grows (rdW W m15) (rdW W m2) ->
  akept pa_segs B lyc Sc W memc W m2 (spZ regs - MODEL_READ_AK) (spZ regs) EX2 /\
  (forall a, FRS a -> aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) m120 a) /\
  (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W) m2 (aarg regs 2) = Some 0) /\
  (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> aview pa_segs (w_H W) m2 (aarg regs 4) = Some 0)).
{ intros m2 UNx HGx. split; [|split; [|split]].
  - exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W m15 W m2 (spZ regs - MODEL_READ_AK) (spZ regs)
      EX2 EX2 _ HAR Hsk ltac:(lia) HKm UNx (fun a _ Hp => apresent_grows _ _ _ _ HGx Hp) (fun a H => H)
      ltac:(intros a Ha; right; exact Ha)).
  - intros a Ha. pose proof (FRSlo a Ha). rewrite <- (HFRS a Ha). apply UNx; [|lia].
    unfold FRS, in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
      change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia.
  - intros h2 h3. destruct (WRF _ (KBW _ (conj h2 (conj h3 eq_refl)))) as (_ & Xwin & X64 & _).
    rewrite <- (HK0 h2 h3). exact (UNx _ X64 Xwin).
  - intros h4 h5. destruct (WRF _ (ABW _ (conj h4 (conj h5 eq_refl)))) as (_ & Xwin & X64 & _).
    rewrite <- (HA0 h4 h5). exact (UNx _ X64 Xwin). }
apply (BR W E mr_ss15c ms md POST BC_EQ (SOff 11 0) (SLit 0) HS15); clear HS15; intros Hc HS15.
- (* name = NULL: -EINVAL *)
  rewrite branch_eq_U, (U_atom E 11 (aarg regs 1) E11), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  rename Hc into Hn0.
  mr_run_plain_to RUNPT HS15 HJm (AF_model_read + 0x208).
  { apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60 in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_nil ]]. }
  pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                               rewrite ?U60, ?Usp in Hrr; cbv beta; lia |]);
          destruct Hin)) as UN.
  lazymatch type of HS15 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msX := m) in * end.
  prreg HS15 (10%bv : bv 5) R10.
  pmkst HS15.
  mr_joinS HS15 1000%nat 0x208 CLOB208 mr_ss208d HSj.
  destruct (STEP15 _ UN HG) as (HKx & HFx & HK0x & HA0x).
  refine (EXIT _ _ _ W lyc S1 k (norm_rc (- E_INVAL)) _ _ HSj HJm ltac:(lia) Hfs1 _ _ _ HKx HFx _ _).
  + apply img_env_havoc_hi; [exact HEI | cbv; lia].
  + split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; reflexivity | reflexivity].
  + rewrite Eab1. apply Permutation_refl.
  + exact (proj1 (same_but_materialized_fs _ _
      (same_but_materialized_trans _ _ _ Hsm (same_but_materialized_wvb_any _ _)))).
  + exact (proj2 (same_but_materialized_fs _ _
      (same_but_materialized_trans _ _ _ Hsm (same_but_materialized_wvb_any _ _)))).
  + cbn [ms_regs mkst]. rewrite R10. apply bv_eq. vm_compute. reflexivity.
  + apply (QMR W (ms_mem msX) (- E_INVAL) (WRX15 _ HG) (HVX _ HKx) HK0x HA0x).
    intros mbs kbs tab nm _ _ _ Hn. destruct nm as [s|]; [destruct Hn as (Hne & _); exfalso; exact (Hne Hn0)|].
    reflexivity.
- (* name <> NULL: the instrumented check of name[0] and its load *)
  rewrite branch_eq_U, (U_atom E 11 (aarg regs 1) E11), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  rename Hc into Hn1.
  destruct nm0 as [s0|]; [|exfalso; exact (Hn1 PNM)].
  destruct PNM as (_ & CS0).
  pose proof (PSCN s0 eq_refl) as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7).
  assert (HNa : forall j, 0 <= j <= Z.of_nat (length s0) ->
            akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) (aarg regs 1 + j)).
  { intros j Hj. apply HRD. left. split; [exact Hn1|]. exists s0. split; [exact CS0 | lia]. }
  assert (HNx : forall j, 0 <= j <= Z.of_nat (length s0) -> ~ EX2 (aarg regs 1 + j)).
  { intros j Hj [Hq | [Hq | Hq]].
    - revert Hq. eapply sclass_not_side;
        first [exact LAWS | exact TB | exact pa_img_range | exact HJ | lia | exact Hnin1 | idtac].
      eapply sclass_of_akb;
        first [exact LAWS | exact TB | exact pa_img_range | exact (HNa j Hj)].
    - destruct Hq as (h2 & h3 & Hq). destruct (PNSEP s0 eq_refl) as (Q1 & _). pose proof (Q1 h2 h3) as Q.
      unfold apart in Q. lia.
    - destruct Hq as (h4 & h5 & Hq). destruct (PNSEP s0 eq_refl) as (_ & Q2). pose proof (Q2 h4 h5) as Q.
      unfold apart in Q. lia. }
  assert (HNv : forall j, 0 <= j <= Z.of_nat (length s0) ->
            aview pa_segs (w_H W) m15 (aarg regs 1 + j) = aview pa_segs (w_H W) memc (aarg regs 1 + j)).
  { intros j Hj. exact (akept_akb_gx SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W m15
      (spZ regs - MODEL_READ_AK) (spZ regs) EX2 _ HJ HKm (HNa j Hj) (HNx j Hj)). }
  (* name[0] *)
  destruct CS0 as ((CB0 & CB1 & CBb) & CNI).
  destruct (nth_error (s0 ++ [zb 0]) 0) as [c0|] eqn:Ec0;
    [|apply nth_error_None in Ec0; rewrite length_app in Ec0; cbn [length] in Ec0; lia].
  assert (MB1 : mbyte pa_segs (rdW W memc) (aarg regs 1) = Some c0).
  { pose proof (CBb 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Q. rewrite Z.add_0_r in Q.
    rewrite Q. exact Ec0. }
  assert (MB15 : mbyte pa_segs (rdW W m15) (aarg regs 1) = Some c0).
  { rewrite <- MB1. apply (mbyte_of_aview pa_segs). pose proof (HNv 0 ltac:(lia)) as Q. rewrite Z.add_0_r in Q.
    exact Q. }
  set (v0 := bv_unsigned c0).
  assert (Hv0 : 0 <= v0 < 256) by (unfold v0; pose proof (bv_unsigned_in_range 8 c0) as Q; unfold bv_modulus in Q;
    cbn in Q; lia).
  (* the name's shadow at this memory *)
  pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W m15 md k HJm)
    as HAR15.
  assert (FM2 : fmiss lyc Sc EX2).
  { apply fmiss_or; [exact (fmiss_side pa_segs B lyc Sc W memc mdc 1 pos HAR Hc1 Hp1 Hnin1)|].
    apply fmiss_or.
    - apply (fmiss_app pa_segs B LAWS lyc Sc W memc mdc KB HAR). intros x Hx. exact (proj1 (WRF x (KBW x Hx))).
    - apply (fmiss_app pa_segs B LAWS lyc Sc W memc mdc AB HAR). intros x Hx. exact (proj1 (WRF x (ABW x Hx))). }
  destruct (shadow_transport pa_segs B LAWS TB pa_img_range lyc Sc W memc mdc lyc S1 W m15 md
    (spZ regs - MODEL_READ_AK) (spZ regs) EX2 (aarg regs 1) (Z.of_nat (length s0) + 1) HAR HAR15 eq_refl eq_refl
    ltac:(rewrite Eab1; intros b m Hb; exact Hb) HKm FM2 ltac:(lia)
    ltac:(intros x Hx; eapply sclass_of_akb;
          first [exact LAWS | exact TB | exact pa_img_range |
                 replace x with (aarg regs 1 + (x - aarg regs 1)) by lia; apply HNa; lia])
    SC4 SC5) as (NRA & _).
  (* name[0]'s value in a fresh atom, the name's region and the facts of atoms 11 and 700 *)
  pose proof (st_ok_pi_havoc_hi 700 E _ _ [Z_to_bv 64 v0] HS15 ltac:(vm_compute; reflexivity)) as HS3.
  clear HS15. rename HS3 into HS15.
  remember (havoc E 700 [Z_to_bv 64 v0]) as E7 eqn:HE7 in HS15.
  assert (OLD7 : forall n, (n < 700)%nat -> ew E7 n = ew E n)
    by (intros n Hn; rewrite HE7; apply YN3v.ew_havoc_old; exact Hn).
  assert (E700 : ew E7 700 = Z_to_bv 64 v0)
    by (rewrite HE7; exact (ew_havoc_new E 700 [Z_to_bv 64 v0] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
  assert (HEI7 : img_env pa_val A_LIM E7) by (rewrite HE7; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (HED7 : ed E7 = ed E) by (rewrite HE7; reflexivity).
  clear HE7.
  assert (E11_7 : ew E7 11 = Z_to_bv 64 (aarg regs 1)) by (rewrite OLD7 by lia; exact E11).
  assert (E32_7 : ew E7 32 = Z_to_bv 64 MR_SB) by (rewrite OLD7 by lia; exact E32).
  assert (U11 : bv_unsigned (ew E7 11) = aarg regs 1) by (rewrite E11_7; apply unsigned_lit_small; lia).
  assert (U60_7 : bv_unsigned (ew E7 60) = sp1) by (rewrite OLD7 by lia; exact U60).
  assert (Usp_7 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Usp).
  unfold amem_range in SC3. unfold apart_frame in SC6.
  add_fact HS15 11%nat MR_PF
    ltac:(unfold afact_ok, MR_PF; cbn [af_lo af_hi af_al2]; rewrite U11; rewrite Z.pow_0_r, Z.mod_1_r;
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; repeat split; lia).
  add_fact HS15 700%nat (mkAF 0 255 0)
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E700, unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia).
  lazymatch type of HS15 with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _
    (YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 700 0))]) HS15 eq_refl
    ltac:(unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite U11; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val pa_segs _ _ (aarg regs 1) 0 1 (SOff 700 0) v0);
          [ cbn [sv_denot]; rewrite E700, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia
          | intros kk Hkk; destruct kk as [|kk]; [|lia]; change (Z.of_nat 0) with 0; rewrite !Z.add_0_r;
            transitivity (Some c0); [exact MB15|]; f_equal;
            change (N.to_nat 1) with 1%nat; unfold YO0f.le_byte; change (8 * Z.of_nat 1) with 8;
            change (8 * Z.of_nat 0) with 0;
            rewrite Z.shiftr_0_r; rewrite !Z.mod_small by (cbn; lia); unfold v0;
            symmetry; apply Z_to_bv_bv_unsigned ])
    ltac:(mr_disj; rewrite ?U60_7, ?Usp_7, ?U11; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *;
          repeat split; lia)) as HS3 end.
  clear HS15; rename HS3 into HS15; norm_pi HS15.
  assert (SHN : sh_ok pa_segs MRBx [mkSHE 11 0 1] E7 (mrestrict (w_H W) m15)).
  { apply (mr_shent_ok E7 (w_H W) m15 11 (aarg regs 1) 1 E32_7 E11_7 AR1 ltac:(lia)).
    - intros x Hx. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
    - intros x Hx. apply NRA. lia. }
  (* +0x160 .. +0x174: the instrumented check of name[0] and its load, up to `beqz a1` *)
  paj_run_tok RUN HS15 HJm SHN MRspan.
  { apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U11 in Ha; lia
    | apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60_7 in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp_7 in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_nil ]]]. }
  pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                               rewrite ?U11, ?U60_7, ?Usp_7 in Hrr; cbv beta; lia |]);
          destruct Hin)) as UN1.
  clear HF HFr. rename HG into HG1.
  lazymatch type of HS15 with st_ok_pi _ _ ?Er _ (restrict _ ?m) =>
    set (msA := m) in *;
    assert (Er700 : ew Er 700 = Z_to_bv 64 v0) by (rewrite ?ew_ewset_other by lia; exact E700);
    assert (ErOLD : forall n, (n < 700)%nat -> ew Er n = ew E n)
      by (intros n Hn; rewrite ?ew_ewset_other by lia; apply OLD7; exact Hn);
    assert (ErED : ed Er = ed E) by (transitivity (ed E7); [reflexivity | exact HED7]);
    assert (HEIr : img_env pa_val A_LIM Er)
      by (repeat first [apply img_env_ewset_hi; [|cbv; lia]]; exact HEI7);
    set (EnvR := Er) in *
  end.
  assert (U11r : bv_unsigned (ew EnvR 11) = aarg regs 1) by (rewrite ErOLD by lia; rewrite <- OLD7 by lia; exact U11).
  assert (U60r : bv_unsigned (ew EnvR 60) = sp1) by (rewrite ErOLD by lia; exact U60).
  assert (Uspr : bv_unsigned (ew EnvR 2) = spZ regs) by (rewrite ErOLD by lia; exact Usp).
  apply (BR W _ _ _ _ POST BC_EQ (SOff 700 0) (SLit 0) HS15); clear HS15; intros Hc HS15.
  + (* name[0] = 0, the empty name: -EINVAL *)
    rewrite branch_eq_U, (U_atom _ 700 v0 Er700), U_lit in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hv00.
    mr_run_plain_to RUNPT HS15 HJm (AF_model_read + 0x208).
    { apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U11r in Ha; lia
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60r in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Uspr in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_nil ]]]. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                 rewrite ?U11r, ?U60r, ?Uspr in Hrr; cbv beta; lia |]);
            destruct Hin)) as UN2.
    lazymatch type of HS15 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msX := m) in * end.
    prreg HS15 (10%bv : bv 5) R10.
    pmkst HS15.
    mr_joinS HS15 1000%nat 0x208 CLOB208 mr_ss208d HSj.
    assert (UNc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) ->
              aview pa_segs (w_H W) (ms_mem msX) a = aview pa_segs (w_H W) m15 a)
      by (intros a Ha Hz; rewrite (UN2 a Ha Hz); exact (UN1 a Ha Hz)).
    destruct (STEP15 _ UNc (mem_grows_trans _ _ _ HG1 HG)) as (HKx & HFx & HK0x & HA0x).
    refine (EXIT _ _ _ W lyc S1 k (norm_rc (- E_INVAL)) _ _ HSj HJm ltac:(lia) Hfs1 _ _ _ HKx HFx _ _).
    * apply img_env_havoc_hi; [exact HEIr | cbv; lia].
    * split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; apply ErOLD; lia
             | transitivity (ed EnvR); [reflexivity | exact ErED]].
    * rewrite Eab1. apply Permutation_refl.
    * refine (proj1 (same_but_materialized_fs mdc _ _)).
      repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm.
    * refine (proj2 (same_but_materialized_fs mdc _ _)).
      repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm.
    * cbn [ms_regs mkst]. rewrite R10. apply bv_eq. vm_compute. reflexivity.
    * apply (QMR W (ms_mem msX) (- E_INVAL) (WRX15 _ (mem_grows_trans _ _ _ HG1 HG)) (HVX _ HKx) HK0x HA0x).
      intros mbs kbs tab nm _ _ _ Hn. destruct nm as [s|]; [|exfalso; exact (Hn1 Hn)].
      destruct Hn as (_ & (Sb0 & Sb1 & Sbb) & SNI). destruct s as [|c s']; [reflexivity|].
      exfalso. apply SNI. left.
      pose proof (Sbb 0%nat ltac:(cbn [length app]; lia)) as Q. rewrite Z.add_0_r in Q. cbn [app nth_error] in Q.
      rewrite MB1 in Q. injection Q as Q. subst c. apply bv_eq. change (bv_unsigned c0) with v0. rewrite Hv00.
      reflexivity.
  + (* name[0] <> 0: +0x178 a0 := name, +0x17c the call of index_of *)
    rewrite branch_eq_U, (U_atom _ 700 v0 Er700), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hv01.
    assert (SH0 : sh_ok pa_segs MRBx [] EnvR (mrestrict (w_H W) (ms_mem msA))) by constructor.
    paj_run_tok RUN HS15 HJm SH0 MRspan.
    { apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U11r in Ha; lia
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60r in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Uspr in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_nil ]]]. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                 rewrite ?U11r, ?U60r, ?Uspr in Hrr; cbv beta; lia |]);
            destruct Hin)) as UN3.
    clear HF HFr. rename HG into HG3.
    lazymatch type of HS15 with st_ok _ _ _ (restrict _ ?m) => set (msc := m) in * end.
    pmkst HS15.
    prreg HS15 (1%bv : bv 5) Q1. prreg HS15 (2%bv : bv 5) Q2. prreg HS15 (3%bv : bv 5) Q3.
    prreg HS15 (4%bv : bv 5) Q4. prreg HS15 (10%bv : bv 5) Q10.
    set (regs5 := ms_regs msc) in *.
    set (m5 := ms_mem msc) in *.
    lazymatch type of HJm with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => set (md5 := mdx) in * end.
    assert (Hsp5 : spZ regs5 = sp1).
    { unfold spZ. rewrite Q2. rewrite ErOLD by lia. rewrite E60. apply unsigned_lit_small. lia. }
    assert (A50 : aarg regs5 0 = aarg regs 1).
    { transitivity (bv_unsigned (getr regs5 10)).
      { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
      rewrite Q10, ErOLD by lia. rewrite E11. apply unsigned_lit_small. exact AR1. }
    assert (UNc5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) ->
              aview pa_segs (w_H W) m5 a = aview pa_segs (w_H W) m15 a)
      by (intros a Ha Hz; rewrite (UN3 a Ha Hz); exact (UN1 a Ha Hz)).
    destruct (STEP15 _ UNc5 (mem_grows_trans _ _ _ HG1 HG3)) as (HK5 & HF5 & HK05 & HA05).
    pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W m5 md5 k HJm)
      as HAR5.
    assert (HnSs : forall a, akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) a -> ~ aside_rng lyc 1 pos a).
    { intros a Ha. eapply sclass_not_side; first [exact LAWS | exact TB | exact pa_img_range | exact HJ | lia
                                                  | exact Hnin1 | idtac].
      eapply sclass_of_akb; first [exact LAWS | exact TB | exact pa_img_range | exact Ha]. }
    (* a string of the entry's read set at the call *)
    assert (STRAT : forall p sx, acstr_at pa_segs (rdW W memc) p sx ->
      astrcmp_arg pa_segs regs MODEL_READ_AK (rdW W memc) p sx ->
      (forall a, p <= a <= p + Z.of_nat (length sx) -> akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) a) ->
      (forall a, p <= a <= p + Z.of_nat (length sx) -> ~ KB a /\ ~ AB a) ->
      acstr_at pa_segs (rdW W m5) p sx /\ astrcmp_arg pa_segs regs5 INDEX_OF_AK (rdW W m5) p sx).
    { intros p sx Hcs (Hp0 & Hl32 & Hmr & Hra & Hhv & Hfr & Htl) Hakb Hsep.
      assert (HnE : forall a, p <= a <= p + Z.of_nat (length sx) -> ~ EX2 a).
      { intros a Ha [Hq | [Hq | Hq]]; [exact (HnSs a (Hakb a Ha) Hq) | exact (proj1 (Hsep a Ha) Hq)
                                     | exact (proj2 (Hsep a Ha) Hq)]. }
      assert (HV5 : forall a, p <= a <= p + Z.of_nat (length sx) ->
                aview pa_segs (w_H W) m5 a = aview pa_segs (w_H W) memc a)
        by (intros a Ha; exact (akept_akb_gx SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
              W m5 (spZ regs - MODEL_READ_AK) (spZ regs) EX2 a HJ HK5 (Hakb a Ha) (HnE a Ha))).
      split.
      { apply (mr_acstr_move pa_segs (rdW W memc) (rdW W m5) p sx Hcs). intros x Hx.
        apply (mbyte_of_aview pa_segs). exact (HV5 x Hx). }
      destruct (shadow_transport pa_segs B LAWS TB pa_img_range lyc Sc W memc mdc lyc S1 W m5 md5
        (spZ regs - MODEL_READ_AK) (spZ regs) EX2 p (Z.of_nat (length sx) + 1) HAR HAR5 eq_refl eq_refl
        ltac:(rewrite Eab1; intros b m Hb; exact Hb) HK5 FM2 ltac:(lia)
        ltac:(intros x Hx; eapply sclass_of_akb; first [exact LAWS | exact TB | exact pa_img_range | apply Hakb; lia])
        Hra Hhv) as (Hra5 & Hhv5).
      split; [exact Hp0|]. split; [exact Hl32|]. split; [exact Hmr|].
      split; [exact Hra5|]. split; [exact Hhv5|].
      split; [unfold apart_frame in *; rewrite Hsp5; rewrite HK8 in Hfr;
              replace INDEX_OF_AK with 8272 by reflexivity; lia|].
      intros a Ha.
      apply (mr_tail_vis_k SK B LAWS HSEGS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
        lyc S1 W m5 md5 (spZ regs - MODEL_READ_AK) (spZ regs) EX2 (fun y => KB y \/ AB y) S1 W m120 md1 pos
        (p + Z.of_nat (length sx)) a HJ HAR5 ltac:(rewrite Eab1; intros b m Hb; exact Hb) HK5 HAR1 Hfrs1 Hnin1).
      - intros y Hy. unfold EX2 in Hy. tauto.
      - intros y [(h2 & h3 & ->) | (h4 & h5 & ->)]; [exact (HK05 h2 h3) | exact (HA05 h4 h5)].
      - assert (Hsp16 : spZ regs = 16 * (spZ regs / 16)) by (pose proof (Z_div_mod_eq_full (spZ regs) 16); lia).
        apply Z.mod_divide; [lia|]. exists (2 * (spZ regs / 16) - 1052). unfold MODEL_READ_AK in *. lia.
      - assert (Hsp16 : spZ regs = 16 * (spZ regs / 16)) by (pose proof (Z_div_mod_eq_full (spZ regs) 16); lia).
        apply Z.mod_divide; [lia|]. exists (2 * (spZ regs / 16)). lia.
      - apply Hakb. lia.
      - lia.
      - lia.
      - exact (Htl a Ha). }
    assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
    (* g_nl's bytes at the call are the entry's: outside the side frame (not image bytes) and the two buffers *)
    assert (GNX : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> ~ EX2 x).
    { intros x Hx [Hq | [Hq | Hq]].
      - destruct (mr_gnl_img B TB HSEGS x Hx) as (Hi & _ & _).
        exact (proj1 (mr_aside_facts B LAWS lyc S1 W m120 md1 pos HAR1 Hin1 x Hq) Hi).
      - destruct Hq as (h2 & h3 & ->). destruct (PKB h2 h3) as (Hg & _). unfold apart_gnl in Hg. lia.
      - destruct Hq as (h4 & h5 & ->). destruct (PAB h4 h5) as (Hg & _). unfold apart_gnl in Hg. lia. }
    assert (Hmb : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE ->
              mbyte pa_segs (rdW W m5) x = mbyte pa_segs (rdW W memc) x).
    { intros x Hx. apply (mbyte_of_aview pa_segs).
      exact (mr_gnl_view_k B TB HSEGS lyc Sc W memc W m5 _ _ EX2 x HK5 Hx (GNX x Hx)). }
    (* a table string of the entry: a read-set byte, outside the side frame and the two buffers *)
    assert (TSX : forall i n2 ix p, nth_error tab0 i = Some (n2, ix) ->
              au64_at pa_segs (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at pa_segs (rdW W memc) p n2 ->
              forall x, p <= x <= p + Z.of_nat (length n2) ->
              akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) x /\ ~ KB x /\ ~ AB x).
    { intros i n2 ix p Hi HU HC x Hx.
      assert (Hil : (i < length tab0)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      split; [|split].
      - apply HRD. right. exists kbs0, (Z.of_nat i), p, n2.
        split; [exact PNLK|]. split; [destruct PTAB as (Hl & _); lia|].
        split; [exact HU|]. split; [exact HC | exact Hx].
      - intros (h2 & h3 & ->). destruct (PKB h2 h3) as (_ & _ & Ht & _). pose proof (Ht i n2 ix p Hi HU) as Q.
        unfold apart in Q. lia.
      - intros (h4 & h5 & ->). destruct (PAB h4 h5) as (_ & _ & Ht & _). pose proof (Ht i n2 ix p Hi HU) as Q.
        unfold apart in Q. lia. }
    (* the name at the call *)
    destruct (STRAT (aarg regs 1) s0 (conj (conj CB0 (conj CB1 CBb)) CNI) (PSCN s0 eq_refl)
      ltac:(intros a Ha; replace a with (aarg regs 1 + (a - aarg regs 1)) by lia; apply HNa; lia)
      ltac:(intros a Ha; pose proof (HNx (a - aarg regs 1) ltac:(lia)) as Q;
            replace (aarg regs 1 + (a - aarg regs 1)) with a in Q by lia; unfold EX2 in Q; tauto))
      as (Hcs5 & Harg5).
    (* index_of's Pre at the call *)
    assert (HN5 : anlk_at pa_segs (rdW W m5) LA_G_NL kbs0).
    { apply (mr_anlk_move pa_segs (rdW W memc) _ LA_G_NL kbs0 PNLK Hmb).
        assert (HWg : forall (mm : word -> option byte) a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at pa_segs mm a)
          by (intros mm a Ha; rewrite HSEGS; apply LA_G_NL_writable; unfold NK_SIZE in Ha; exact Ha).
        intros x Hx. apply HWg. exact Hx. }
    assert (HT5 : aiftab_at pa_segs (rdW W m5) LA_G_NL kbs0 tab0).
    { apply (mr_aiftab_move pa_segs (rdW W memc) _ LA_G_NL kbs0 tab0 PTAB Hmb).
        intros i n2 ix p Hi HU HC x Hx. destruct (TSX i n2 ix p Hi HU HC x Hx) as (Hk & Hkb & Hab).
        apply (mbyte_of_aview pa_segs).
        refine (akept_akb_gx SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
          W m5 (spZ regs - MODEL_READ_AK) (spZ regs) EX2 x HJ HK5 Hk _).
        intros [Hq | [Hq | Hq]]; [exact (HnSs x Hk Hq) | exact (Hkb Hq) | exact (Hab Hq)]. }
    assert (HPRE5 : index_of_apre pa_segs regs5 (rdW W m5)).
    { exists kbs0, tab0, s0.
      pose proof (zsh_gnl_ard B TB pa_segs lyc S1 W m5 md5 HAR5) as (Hgra & _).
      pose proof PTAB as (HTl & HT80 & HTe).
      split; [exact HN5|]. split; [exact HT5|].
      split; [intros x Hx; apply Hgra; unfold NK_IF_NAME, NK_SIZE in *; lia|].
      split; [intros x Hx; apply Hgra; unfold NK_IF_INDEX, NK_SIZE in *; lia|].
      split; [rewrite A50; exact Hn1|].
      split; [rewrite A50; exact Hcs5|].
      split; [rewrite A50; exact Harg5|].
      intros i n2 ix p Hi Hp5 Hp64.
      assert (Hp0 : au64_at pa_segs (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (mr_val_mem_move pa_segs (rdW W m5) _ _ 8 p Hp5). intros x Hx. symmetry. apply Hmb.
        assert (Hil : (i < length tab0)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
        change (Z.of_nat 8) with 8 in Hx. unfold NK_IF_NAME, NK_SIZE in *. lia. }
      destruct (HTe i n2 ix Hi) as (_ & p' & Hp' & _ & Hc' & _).
      pose proof (mr_acstr_range pa_segs _ _ _ Hc') as Hr'.
      assert (p' = p) as -> by (apply (mr_au64_det pa_segs (rdW W memc) _ p' p Hp' Hp0); lia).
      refine (proj2 (STRAT p n2 Hc' (PSCT i n2 ix p Hi Hp0 Hp64) _ _)).
      - intros x Hx. exact (proj1 (TSX i n2 ix p Hi Hp0 Hc' x Hx)).
      - intros x Hx. exact (proj2 (TSX i n2 ix p Hi Hp0 Hc' x Hx)). }
    (* its read set: the name, a read-set byte of the entry *)
    assert (HRD5 : forall a, index_of_ard pa_segs regs5 (rdW W m5) a ->
              akb pa_segs B lyc S1 (spZ regs5 - INDEX_OF_AK) (spZ regs5) a).
    { intros a (s' & Hs' & Ha). rewrite A50 in Hs', Ha.
      rewrite (mr_acstr_unique pa_segs _ _ s' s0 Hs' Hcs5) in Ha.
      eapply akb_sub.
      - replace a with (aarg regs 1 + (a - aarg regs 1)) by lia. apply HNa. lia.
      - rewrite Hsp5, HKi, HK8. lia.
      - rewrite Hsp5. lia.
      - reflexivity.
      - reflexivity.
      - rewrite Eab1. intros b m Hb. exact Hb.
      - rewrite Hfrs1. intros c q Hcq. right. exact Hcq.
      - reflexivity. }
    assert (Hret5 : YK0s.ret_ok (getr regs5 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
    assert (Hra5 : 4096 <= raZ regs5).
    { unfold raZ. rewrite Q1. pose proof pa_B_ok as (HB0 & HB1 & HB2). rewrite unsigned_lit_small by lia. lia. }
    assert (HAPRE5 : apre SK pa_segs 0 0 B INDEX_OF_AK 0 [] (index_of_awr regs5 (rdW W m5)) G XO OUT STK sp0 FP ly S
              W0 mem0 md0 ((1, pos) :: own) lyc S1 W m5 md5 k regs5).
    { unfold apre.
      split; [exact HJm|]. split; [exact HGok|].
      split.
      { refine (mr_arodata_k B LAWS rlo rhi lyc Sc W memc W m5 _ _ EX2 (fun a => inFP (model_read_awr regs (rdW W memc)) a)
          S1 W m120 md1 pos HROD HK5 HAR1 Hin1 _ _).
        - intros a [Hq | [Hq | Hq]]; [left; exact Hq | right; exact (KBW a Hq) | right; exact (ABW a Hq)].
        - intros a Ha. exact (Hnro a Ha). }
      split; [exact Hret5|]. split; [exact Hra5|].
      split; [rewrite Q3, ErOLD by lia; rewrite (EREG 3%nat ltac:(lia)); exact Hgp|].
      split; [rewrite Q4, ErOLD by lia; rewrite (EREG 4%nat ltac:(lia)); exact Htp|].
      split; [rewrite Hsp5; exact Hsp1al16|].
      split; [rewrite Hsp5, HKi; rewrite HK8 in Hwlo; lia|].
      split; [rewrite Hsp5; lia|].
      split; [lia|].
      split; [apply Forall_nil|].
      split; [intros a Ha; destruct (inFP_nil a Ha) | intros a Ha; destruct (inFP_nil a Ha)]. }
    assert (Hsig : pa_sigma LS_index_of = INDEX_OF_A) by (rewrite (lv_sigma LV); reflexivity).
    rewrite Hsig.
    eapply SRr_bind.
    { exact (IDX 0 0 G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W m5 md5 k regs5
        HAPRE5 HRD5 HPRE5). }
    intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & Hpres6 & Hfr6 & Hfd6 & Hfs6 & HK6 & Hsh6 & HS6f
      & Hperm6 & HIDX).
    rewrite Z.add_0_r in HJ6.
    assert (Hidx : getr regs6 10 = w64 (index_of tab0 s0))
      by (apply (HIDX kbs0 tab0 s0 HN5 HT5); rewrite A50; exact Hcs5).
    assert (Hir : 0 <= index_of tab0 s0 < 2 ^ 31).
    { apply mr_index_rng. intros i n ix Hi. pose proof PTAB as (_ & _ & HTe0). exact (proj1 (HTe0 i n ix Hi)). }
    (* across the call: every byte the callee keeps *)
    pose proof HK6 as (K61 & K62 & K63 & K64 & K65 & K66).
    assert (XC : forall a, akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) a ->
              aview pa_segs (w_H W6) mem6 a = aview pa_segs (w_H W) m5 a).
    { intros a Ha.
      refine (akept_akb_gx SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W m5 md5 k
        W6 mem6 _ _ _ a HJm HK6 _ (inFP_nil a)).
      eapply akb_sub.
      - exact Ha.
      - rewrite Hsp5, HKi, HK8. lia.
      - rewrite Hsp5. lia.
      - reflexivity.
      - reflexivity.
      - rewrite Eab1. intros b m Hb. exact Hb.
      - rewrite Hfrs1. intros c q Hcq. right. exact Hcq.
      - reflexivity. }
    assert (WAKB : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
              akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) a).
    { intros a Ha.
      destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HENT a Ha)
        as (Happ & Hwin & Herr & Hajw' & Ha64).
      exact (ajw_akb SK pa_segs B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc Sc
        (spZ regs - MODEL_READ_AK) (spZ regs) a HGok HJ Hajw' Hwin Happ Herr eq_refl eq_refl (fun b m H => H)
        (fun c q H => H) (fun c q => eq_refl)). }
    assert (HK6c : akept pa_segs B lyc Sc W memc W6 mem6 (spZ regs - MODEL_READ_AK) (spZ regs) EX2).
    { eapply (akept_trans SK pa_segs B LAWS Hsegs);
        [ exact Hsk | lia | exact HK5 | exact HK6 | rewrite Hsp5, HKi, HK8; lia | rewrite Hsp5; lia
        | rewrite Eab1; intros b m Hb; exact Hb | rewrite Hfrs1; intros f Hf; right; exact Hf
        | intros a H; exact H | intros a Ha; destruct (inFP_nil a Ha) ]. }
    assert (HF6 : forall a, FRS a -> aview pa_segs (w_H W6) mem6 a = aview pa_segs (w_H W) m120 a).
    { intros a Ha. rewrite <- (HF5 a Ha). exact (K64 1 pos a Hin1 Ha (inFP_nil a)). }
    pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own)
      ly6 S6 W6 mem6 md6 k HJ6) as Hpres6x.
    (* the state after the call: the realigned area at sp1 and the saved words; both above the call's window *)
    jafter_call_keep_hi HS15 720%nat regs6 (mrestrict (w_H W6) mem6) Hpres6 [1; 2]%nat HS6.
    match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U60r; intros a Ha.
        + apply (mbyte_of_aview pa_segs). apply K61; [lia | rewrite Hsp5, HKi; lia | apply inFP_nil].
        + intros _. apply (apresent_writable pa_segs). apply Hpres6x. rewrite HK8 in Hwlo. lia.
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uspr; intros a Ha.
        + apply (mbyte_of_aview pa_segs). apply K61; [lia | rewrite Hsp5, HKi; lia | apply inFP_nil].
        + intros _. apply (apresent_writable pa_segs). apply Hpres6x. rewrite HK8 in Hwlo. lia. }
    clear HS15. rewrite <- restrict_mkst_fx in HS6.
    remember (havoc EnvR 720 (map (getr regs6) CLOB)) as E6 eqn:HE6 in HS6.
    assert (HEI6 : img_env pa_val A_LIM E6) by (rewrite HE6; apply img_env_havoc_hi; [exact HEIr | cbv; lia]).
    assert (OLD6 : forall n, (n < 720)%nat -> ew E6 n = ew EnvR n)
      by (intros n Hn; rewrite HE6; apply YN3v.ew_havoc_old; exact Hn).
    assert (HED6 : ed E6 = ed EnvR) by (rewrite HE6; reflexivity).
    assert (E724 : ew E6 724 = Z_to_bv 64 (index_of tab0 s0)).
    { rewrite HE6. change 724%nat with (720 + 4)%nat.
      rewrite (ew_havoc_new EnvR 720 (map (getr regs6) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia)).
      change (nth 4 (map (getr regs6) CLOB) (Z_to_bv 64 0)) with (getr regs6 10%bv). exact Hidx. }
    clear HE6.
    assert (U60_6 : bv_unsigned (ew E6 60) = sp1) by (rewrite OLD6 by lia; exact U60r).
    assert (Usp_6 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Uspr).
    rewrite Q1.
    apply (BR W6 E6 _ _ md6 POST BC_EQ (SOff 724 0) (SLit 0) HS6); clear HS6; intros Hc HS6.
    * (* index 0: -ENODEV *)
      rewrite branch_eq_U, (U_atom _ 724 (index_of tab0 s0) E724), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
      rename Hc into Hi0.
      mr_run_plain_to RUNPT HS6 HJ6 (AF_model_read + 0x208).
      { apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60_6 in Ha;
          left; split; [left; lia | lia]
        | apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp_6 in Ha;
          left; split; [left; lia | lia]
        | apply awr_ok_x_nil ]]. }
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
        ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                   rewrite ?U60_6, ?Usp_6 in Hrr; cbv beta; lia |]);
              destruct Hin)) as UN7.
      lazymatch type of HS6 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (ms7 := m) in * end.
      prreg HS6 (10%bv : bv 5) R10.
      pmkst HS6.
      mr_joinS HS6 1000%nat 0x208 CLOB208 mr_ss208d HSj.
      assert (HK7 : akept pa_segs B lyc Sc W memc W6 (ms_mem ms7) (spZ regs - MODEL_READ_AK) (spZ regs) EX2).
      { exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W6 mem6 W6 (ms_mem ms7)
          (spZ regs - MODEL_READ_AK) (spZ regs) EX2 EX2 _ HAR Hsk ltac:(lia) HK6c UN7
          (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => H) ltac:(intros a Ha; right; exact Ha)). }
      refine (EXIT _ _ _ W6 ly6 S6 k (norm_rc (- E_NODEV)) _ _ HSj HJ6 ltac:(lia) _ _ _ _ HK7 _ _ _).
      -- apply img_env_havoc_hi; [exact HEI6 | cbv; lia].
      -- split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite OLD6 by lia; apply ErOLD; lia
               | transitivity (ed E6); [reflexivity | rewrite HED6; exact ErED]].
      -- exists (st_fs S6). apply (set_fs_trans S1 S6 Sc); [exact (set_fs_of_exists S1 Sc Hfs1) | exact HS6f].
      -- rewrite <- Eab1. exact Hperm6.
      -- transitivity (m_fds md6); [exact (proj1 (wvb_fds_fs _ _ md6))|]. rewrite Hfd6.
         refine (proj1 (same_but_materialized_fs mdc _ _)).
         repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm.
      -- transitivity (m_fs md6); [exact (proj2 (wvb_fds_fs _ _ md6))|]. rewrite Hfs6.
         refine (proj2 (same_but_materialized_fs mdc _ _)).
         repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm.
      -- intros a Ha. pose proof (FRSlo a Ha). rewrite <- (HF6 a Ha). apply UN7; [|lia].
         unfold FRS, in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
           change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia.
      -- cbn [ms_regs mkst]. rewrite R10. apply bv_eq. vm_compute. reflexivity.
      -- assert (XV : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
                   aview pa_segs (w_H W6) (ms_mem ms7) a = aview pa_segs (w_H W) m5 a).
         { intros a Ha. destruct (WRF a Ha) as (_ & Xwin & X64 & _). rewrite (UN7 a X64 Xwin).
           exact (XC a (WAKB a Ha)). }
         apply (QMR W6 (ms_mem ms7) (- E_NODEV)).
         ++ intros a Ha Hw.
            pose proof (WRX15 m5 (mem_grows_trans _ _ _ HG1 HG3) a Ha Hw) as Hw5.
            first [ exact (mr_wr_writable2 SK B HSEGS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
                             mdc k regs W m5 W6 (ms_mem ms7) a HENT Ha Hw5 (fun _ => XV a Ha))
                  | exact (mr_wr_writable2 SK B LAWS HSEGS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
                             memc mdc k regs W m5 W6 (ms_mem ms7) a HENT Ha Hw5 (fun _ => XV a Ha)) ].
         ++ intros a Ha Hk Hab.
            apply (mr_wr_view SK B LAWS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
              W6 (ms_mem ms7) EX2 a HENT Ha HK7).
            intros [Hq | [Hq | Hq]]; [exact (proj2 (proj2 (proj2 (WRF a Ha))) Hq) | exact (Hk Hq) | exact (Hab Hq)].
         ++ intros h2 h3. rewrite (XV _ (KBW _ (conj h2 (conj h3 eq_refl)))). exact (HK05 h2 h3).
         ++ intros h4 h5. rewrite (XV _ (ABW _ (conj h4 (conj h5 eq_refl)))). exact (HA05 h4 h5).
         ++ intros mbs kbs tab nm _ Hk Ht Hn.
            assert (Hnm : nm = Some s0).
            { apply (mr_astr_arg_unique pa_segs (rdW W memc) (aarg regs 1)); [exact Hn|].
              split; [exact Hn1 | exact (conj (conj CB0 (conj CB1 CBb)) CNI)]. }
            rewrite <- (mr_anlk_unique pa_segs _ _ kbs0 kbs PNLK Hk) in Ht.
            rewrite <- (mr_aiftab_unique pa_segs _ _ kbs0 tab0 tab PTAB Ht).
            subst nm.
            assert (Hs0 : length s0 <> 0%nat).
            { intros Hl. apply Hv01. apply length_zero_iff_nil in Hl. rewrite Hl in Ec0. cbn in Ec0.
              injection Ec0 as Ec0. unfold v0. rewrite <- Ec0. reflexivity. }
            unfold read_core. rewrite (proj2 (Nat.eqb_neq _ _) Hs0), Hi0. reflexivity.
    * (* index not 0: the read, model_readRq.v mr_rq from the cut MR_AT180 *)
      rewrite branch_eq_U, (U_atom _ 724 (index_of tab0 s0) E724), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
      rename Hc into Hi0.
      pose proof (mr_st_ok_pi_merge _ mr_ss180 _ _ HS6 ltac:(vm_compute; reflexivity)) as HS180.
      assert (XV6 : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
                aview pa_segs (w_H W6) mem6 a = aview pa_segs (w_H W) m5 a)
        by (intros a Ha; exact (XC a (WAKB a Ha))).
      refine (mr_rq SK B LAWS TL LV HSEGS TB AMSET TALK rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
        mdc k regs E6 _ md6 ly6 S6 W6 pos (index_of tab0 s0) s0 HENT _).
      unfold MR_AT180.
      split; [exact HEI6|].
      split; [split; [intros n Hn; rewrite OLD6 by lia; rewrite ErOLD by lia; exact (proj1 HAE n Hn)
                     | rewrite HED6, ErED; exact (proj2 HAE)]|].
      split; [rewrite OLD6 by lia; rewrite ErOLD by lia; exact E32|].
      split; [rewrite OLD6 by lia; rewrite ErOLD by lia; exact E44|].
      split; [rewrite OLD6 by lia; rewrite ErOLD by lia; exact E60|].
      split; [rewrite OLD6 by lia; rewrite ErOLD by lia; exact E61|].
      split; [rewrite OLD6 by lia; rewrite ErOLD by lia; exact E62|].
      split; [exact E724|]. split; [lia|].
      split; [exact HS180|]. split; [exact HJ6|].
      split; [exists (st_fs S6); apply (set_fs_trans S1 S6 Sc); [exact (set_fs_of_exists S1 Sc Hfs1) | exact HS6f]|].
      split; [rewrite <- Eab1; exact Hperm6|].
      split; [rewrite Hfr6; exact Hfrs1|].
      split; [exact (ex_intro _ S1 (ex_intro _ W (ex_intro _ m120 (ex_intro _ md1 (conj HAR1 (conj Hfrs1 Eab1))))))|].
      split; [exact Hnin1|]. split; [exact HK6c|].
      split; [exact (VFLm W6 mem6 HF6)|].
      split.
      { intros a Ha Hw. pose proof (WRX15 m5 (mem_grows_trans _ _ _ HG1 HG3) a Ha Hw) as Hw5.
        exact (mr_wr_writable2 SK B HSEGS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
                 mdc k regs W m5 W6 mem6 a HENT Ha Hw5 (fun _ => XV6 a Ha)). }
      split; [intros h2 h3; cbn [ms_mem mkst]; rewrite (XV6 _ (KBW _ (conj h2 (conj h3 eq_refl)))); exact (HK05 h2 h3)|].
      split; [intros h4 h5; cbn [ms_mem mkst]; rewrite (XV6 _ (ABW _ (conj h4 (conj h5 eq_refl)))); exact (HA05 h4 h5)|].
      split; [rewrite Hfd6; refine (proj1 (same_but_materialized_fs mdc _ _));
              repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]); exact Hsm|].
      split; [rewrite Hfs6; refine (proj2 (same_but_materialized_fs mdc _ _));
              repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]); exact Hsm|].
      split; [split; [exact Hn1 | exact (conj (conj CB0 (conj CB1 CBb)) CNI)]|].
      split.
      { intros Hl. apply Hv01. apply length_zero_iff_nil in Hl. rewrite Hl in Ec0. cbn in Ec0.
        injection Ec0 as Ec0. unfold v0. rewrite <- Ec0. reflexivity. }
      intros kbs tab Hk Ht.
      rewrite <- (mr_anlk_unique pa_segs _ _ kbs0 kbs PNLK Hk) in Ht.
      rewrite <- (mr_aiftab_unique pa_segs _ _ kbs0 tab0 tab PTAB Ht). reflexivity.
Qed.
End b.
End a.
