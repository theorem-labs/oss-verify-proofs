(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module names changed; 522 of its 582 lines of code are new or changed and 298 lines of the source are left out. *)
(* model_read on image A: the checks segment of its walk, from the branch on kind at +0x120 (model_readDefs.v
   MR_AT120) to the call of index_of at +0x17c, or to the exit +0x208 with -EINVAL when the name is NULL or empty.
   The frame's two regions are set aside here (their windows may meet the shadow span, which the instrumented checks
   need clear); the guarded NUL stores to kind[0] and alias[0] are joined at +0x13c and +0x158.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs model_readExit model_readKit PaJournalFs model_readTail.
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

Lemma mr_chk : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md1 S1 pos,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  MR_AT120 SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md1 S1 pos ->
  SRr pa_segs W (mkCfg ms md1) (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md1 S1 pos HENT
  (HEI & HAE & E32 & E44 & E60 & E61 & E62 & HS & HJ1 & Hfrs1 & Eab1 & Hnin1 & Hfs1 & HK & Hsm).
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
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W (ms_mem ms) md1 k
  HJ1) as HAR1.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
pose proof HAR1 as [M1 _].
destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Hc1 & Hp1 & _).
destruct (frames_bounds pa_segs B LAWS lyc S1 W (ms_mem ms) md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
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
assert (E12 : ew E 12 = Z_to_bv 64 (aarg regs 2)) by exact (EARG 2 ltac:(lia)).
assert (E13 : ew E 13 = Z_to_bv 64 (aarg regs 3)) by exact (EARG 3 ltac:(lia)).
assert (E14 : ew E 14 = Z_to_bv 64 (aarg regs 4)) by exact (EARG 4 ltac:(lia)).
assert (E15 : ew E 15 = Z_to_bv 64 (aarg regs 5)) by exact (EARG 5 ltac:(lia)).
assert (AR2 : 0 <= aarg regs 2 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR3 : 0 <= aarg regs 3 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR4 : 0 <= aarg regs 4 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR5 : 0 <= aarg regs 5 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (AR1 : 0 <= aarg regs 1 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNP := paj_run_plain_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
(* the frame's two regions set aside *)
assert (HSd : st_ok_pi pa_segs pa_val E mr_ss120d (restrict (w_H W) ms)).
{ exact (st_ok_pi_submem E mr_ss120 _ (ss_mem mr_ss120d) HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)). }
set (m120 := ms_mem ms) in *.
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (U60 : bv_unsigned (ew E 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (EREG 2%nat ltac:(lia)); reflexivity).
assert (Hsk : alloc_ceiling <= spZ regs - MODEL_READ_AK) by lia.
set (KB := fun a => aarg regs 2 <> 0 /\ 1 <= aarg regs 3 /\ a = aarg regs 2).
set (FRS := fun a => in_zr a (frame_rng lyc (1, pos)) \/ in_zr a (shadow_addr F, 16)).
assert (FRSlo : forall a, FRS a -> a < alloc_ceiling).
{ intros a [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
    change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia. }
set (AB := fun a => aarg regs 4 <> 0 /\ 1 <= aarg regs 5 /\ a = aarg regs 4).
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
assert (WR120 : forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
          writable_at pa_segs (rdW W m120) a).
{ intros a Ha Hw. destruct (WRF a Ha) as (_ & _ & _ & XNS).
  exact (mr_wr_writable SK B HSEGS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    W m120 a HENT Ha Hw
    (fun _ => mr_wr_view SK B LAWS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W
      m120 _ _ HENT Ha HK XNS)). }
assert (WRG : forall a (m : word -> option byte), inFP (model_read_awr regs (rdW W memc)) a ->
          writable_at pa_segs (rdW W memc) a -> mem_grows (rdW W m120) (rdW W m) -> writable_at pa_segs (rdW W m) a).
{ intros a m Ha Hw Hg. apply (writable_kept (w_H W) m120 m a); [intros Hp; exact (apresent_grows _ _ _ _ Hg Hp)|].
  exact (WR120 a Ha Hw). }
assert (U44 : bv_unsigned (ew E 44) = F) by (rewrite E44; apply unsigned_lit_small; lia).
(* the frame's flag word at +0x120, and later where the frame's bytes did not change *)
assert (VFL120 : val_mem pa_segs (rdW W m120) (F + 120) 8 (flag_addr lyc 1 pos)).
{ pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
  assert (HFL64 : 0 <= flag_addr lyc 1 pos < 2 ^ 64).
  { destruct (al_flag _ _ LAWS lyc S1 W m120 md1 1 pos HAR1 Hin1) as (_ & _ & (Hq1 & _) & HFLc).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hq1. lia. }
  exact (field_of_region (segs := pa_segs) E _ 44%nat F _ _ _ _ _ 120 8%N (SOff 61 0) _ HR1 U44
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & PMOD & PMWF & PNLK & PNWF & PTAB & PNM & PBK & PBA & PRAN & PRAI & PSCN
  & PSCT & PRAM & PHUM & PMR & PRAC & PHUC & PGNM & PFRM & PFRK & PFRA & PERM & PERK & PERA & PKB & PAB & PNSEP
  & PKA).
(* ---- the join at +0x15c ---- *)
assert (CONT15c : forall E' ms' md',
  img_env pa_val A_LIM E' -> env_agree 512 E E' ->
  st_ok_pi pa_segs pa_val E' mr_ss15c (restrict (w_H W) ms') ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W (ms_mem ms') md' k ->
  same_but_materialized mdc md' ->
  akept pa_segs B lyc Sc W memc W (ms_mem ms') (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => aside_rng lyc 1 pos a \/ KB a \/ AB a) ->
  (forall a, FRS a -> aview pa_segs (w_H W) (ms_mem ms') a = aview pa_segs (w_H W) m120 a) ->
  mem_grows (rdW W m120) (rdW W (ms_mem ms')) ->
  (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W) (ms_mem ms') (aarg regs 2) = Some 0) ->
  (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> aview pa_segs (w_H W) (ms_mem ms') (aarg regs 4) = Some 0) ->
  SRr pa_segs W (mkCfg ms' md') POST).
{ clear HSd. intros E' ms' md' HEI' OLD HS15 HJm Hsm' HKm HFRS HGm HK0 HA0.
  apply (mr_tail SK B LAWS TL LV HSEGS TB AMSET IDX TALK rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k regs E' ms' md' S1 pos m120 md1 HENT).
  refine (conj HEI' (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj HS15 (conj HJm (conj Hsm' (conj HAR1
    (conj Hfrs1 (conj Eab1 (conj Hnin1 (conj Hfs1 (conj VFL120 (conj WR120 (conj HGm (conj HKm
    (conj HFRS (conj HK0 HA0)))))))))))))))))))));
    [ split; [intros n Hn; rewrite (proj1 OLD) by lia; exact (proj1 HAE n Hn) | rewrite (proj2 OLD); exact (proj2 HAE)]
    | rewrite (proj1 OLD) by lia; exact E32 | rewrite (proj1 OLD) by lia; exact E44
    | rewrite (proj1 OLD) by lia; exact E60 | rewrite (proj1 OLD) by lia; exact E61
    | rewrite (proj1 OLD) by lia; exact E62 ]. }
(* ---- the join at +0x13c ---- *)
assert (CONT13c : forall E' ms' md',
  img_env pa_val A_LIM E' -> env_agree 512 E E' ->
  st_ok_pi pa_segs pa_val E' mr_ss13c (restrict (w_H W) ms') ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W (ms_mem ms') md' k ->
  same_but_materialized mdc md' ->
  akept pa_segs B lyc Sc W memc W (ms_mem ms') (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => aside_rng lyc 1 pos a \/ KB a) ->
  (forall a, FRS a -> aview pa_segs (w_H W) (ms_mem ms') a = aview pa_segs (w_H W) m120 a) ->
  mem_grows (rdW W m120) (rdW W (ms_mem ms')) ->
  (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W) (ms_mem ms') (aarg regs 2) = Some 0) ->
  SRr pa_segs W (mkCfg ms' md') POST).
{ clear HSd. intros E' ms' md' HEI' OLD HS13 HJm Hsm' HKm HFRS HGm HK0.
  assert (E14' : ew E' 14 = Z_to_bv 64 (aarg regs 4)) by (rewrite (proj1 OLD) by lia; exact E14).
  assert (E15' : ew E' 15 = Z_to_bv 64 (aarg regs 5)) by (rewrite (proj1 OLD) by lia; exact E15).
  assert (E32' : ew E' 32 = Z_to_bv 64 MR_SB) by (rewrite (proj1 OLD) by lia; exact E32).
  assert (U60' : bv_unsigned (ew E' 60) = sp1) by (rewrite (proj1 OLD) by lia; exact U60).
  assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (proj1 OLD) by lia; exact Usp).
  set (m13 := ms_mem ms') in *.
  set (EX1 := fun a => aside_rng lyc 1 pos a \/ KB a) in *.
  set (EX2 := fun a => aside_rng lyc 1 pos a \/ KB a \/ AB a).
  assert (EX12 : forall a, EX1 a -> EX2 a) by (intros a Ha; unfold EX1, EX2 in *; tauto).
  (* a step after +0x13c: the kept clause, the frame's bytes, kind[0] *)
  assert (STEP : forall (m m2 : word -> option byte) (Zs : Z -> Prop),
    akept pa_segs B lyc Sc W memc W m (spZ regs - MODEL_READ_AK) (spZ regs) EX1 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) m a) ->
    mem_grows (rdW W m) (rdW W m2) ->
    (forall a, Zs a -> AB a \/ spZ regs - MODEL_READ_AK <= a < spZ regs) ->
    akept pa_segs B lyc Sc W memc W m2 (spZ regs - MODEL_READ_AK) (spZ regs) EX2).
  { intros m m2 Zs HKx UNx HGx HZs.
    exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W m W m2 (spZ regs - MODEL_READ_AK) (spZ regs)
      EX1 EX2 Zs HAR Hsk ltac:(lia) HKx UNx (fun a _ Hp => apresent_grows _ _ _ _ HGx Hp) EX12
      ltac:(intros a Ha; destruct (HZs a Ha) as [Hq | Hq]; [left; unfold EX2; right; right; exact Hq | right; exact Hq])). }
  assert (FRSx : forall (m2 : word -> option byte) (Zs : Z -> Prop),
    (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) m13 a) ->
    (forall a, Zs a -> AB a \/ spZ regs - MODEL_READ_AK <= a < spZ regs) ->
    forall a, FRS a -> aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) m120 a).
  { intros m2 Zs UNx HZs a Ha. pose proof (FRSlo a Ha).
    assert (Ha64 : 0 <= a < 2 ^ 64)
      by (unfold FRS, in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
          change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia).
    rewrite <- (HFRS a Ha). apply UNx; [exact Ha64|]. intros Hz. destruct (HZs a Hz) as [(h4 & h5 & ->) | Hq]; [|lia].
    destruct (WRF _ (ABW _ (conj h4 (conj h5 eq_refl)))) as (_ & _ & _ & XNS). apply XNS. unfold aside_rng.
    destruct Ha as [Ha | Ha]; [left; exact Ha | right; left; fold F; change (fs_frame_bytes 1 / 8) with 16; exact Ha]. }
  assert (KK : forall (m2 : word -> option byte) (Zs : Z -> Prop),
    (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview pa_segs (w_H W) m2 a = aview pa_segs (w_H W) m13 a) ->
    (forall a, Zs a -> a = aarg regs 4 \/ spZ regs - MODEL_READ_AK <= a < spZ regs) ->
    (aarg regs 2 = aarg regs 4 -> aarg regs 2 <> 0 -> aview pa_segs (w_H W) m2 (aarg regs 4) = Some 0) ->
    aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W) m2 (aarg regs 2) = Some 0).
  { intros m2 Zs UNx HZs HA h2 h3.
    destruct (WRF _ (KBW _ (conj h2 (conj h3 eq_refl)))) as (_ & Xwin & X64 & _).
    destruct (Z.eq_dec (aarg regs 2) (aarg regs 4)) as [Heq | Hne].
    - rewrite Heq. apply HA; [exact Heq | exact h2].
    - rewrite <- (HK0 h2 h3). apply UNx; [exact X64|]. intros Hz. destruct (HZs _ Hz); [exact (Hne H) | exact (Xwin H)]. }
  apply (BR W E' mr_ss13c ms' md' POST BC_EQ (SOff 14 0) (SLit 0) HS13); clear HS13; intros Hc HS13.
  - (* alias = 0: on to +0x158 *)
    rewrite branch_eq_U, (U_atom E' 14 (aarg regs 4) E14'), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    rename Hc into Ha0.
    mr_run_plain RUNP HS13 HJm.
    { apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60' in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp' in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_nil ]]. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                 rewrite ?U60', ?Usp' in Hrr; cbv beta; lia |]);
            destruct Hin)) as UN.
    lazymatch type of HS13 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msZ := m) in * end.
    pmkst HS13.
    mr_joinS HS13 602%nat 0x15c [(11%bv : bv 5)] mr_ss15c HSj.
    refine (CONT15c _ _ _ _ _ HSj HJm _ _ _ _ _ _).
    + repeat first [apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]; exact HEI'.
    + split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply (proj1 OLD); lia
          | transitivity (ed E'); [reflexivity | exact (proj2 OLD)]].
    + repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm'.
    + exact (STEP m13 _ _ HKm UN HG ltac:(intros a Ha; right; exact Ha)).
    + exact (FRSx _ _ UN ltac:(intros a Ha; right; exact Ha)).
    + exact (mem_grows_trans _ _ _ HGm HG).
    + exact (KK _ _ UN ltac:(intros a Ha; right; exact Ha) ltac:(intros Heq h2; exfalso; apply h2; rewrite Heq; exact Ha0)).
    + intros h4. exfalso. exact (h4 Ha0).
  - (* alias <> 0: +0x140 the test of alias_n *)
    rewrite branch_eq_U, (U_atom E' 14 (aarg regs 4) E14'), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    rename Hc into Ha1.
    mr_run_plain RUNP HS13 HJm.
    { apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60' in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp' in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_nil ]]. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                 rewrite ?U60', ?Usp' in Hrr; cbv beta; lia |]);
            destruct Hin)) as UN0.
    rename HF into HF0, HFr into HFr0, HG into HG0.
    lazymatch type of HS13 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msC := m) in * end.
    pose proof (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W m13 W (ms_mem msC) (spZ regs - MODEL_READ_AK)
      (spZ regs) EX1 EX1 _ HAR Hsk ltac:(lia) HKm UN0 (fun a _ Hp => apresent_grows _ _ _ _ HG0 Hp) (fun a H => H)
      ltac:(intros a Ha; right; exact Ha)) as HKC.
    apply (BR W E' _ msC _ POST BC_EQ (SOff 15 0) (SLit 0) HS13); clear HS13; intros Hc HS13.
    + (* alias_n = 0: on to +0x158 *)
      rewrite branch_eq_U, (U_atom E' 15 (aarg regs 5) E15'), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
      rename Hc into Han0.
      mr_run_plain RUNP HS13 HJm.
      { apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60' in Ha;
          left; split; [left; lia | lia]
        | apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp' in Ha;
          left; split; [left; lia | lia]
        | apply awr_ok_x_nil ]]. }
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
        ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                   rewrite ?U60', ?Usp' in Hrr; cbv beta; lia |]);
              destruct Hin)) as UN.
      lazymatch type of HS13 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msZ := m) in * end.
      pmkst HS13.
      mr_joinS HS13 602%nat 0x15c [(11%bv : bv 5)] mr_ss15c HSj.
      refine (CONT15c _ _ _ _ _ HSj HJm _ _ _ _ _ _).
      * repeat first [apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]; exact HEI'.
      * split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply (proj1 OLD); lia
          | transitivity (ed E'); [reflexivity | exact (proj2 OLD)]].
      * repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm'.
      * exact (STEP (ms_mem msC) _ _ HKC UN HG ltac:(intros a Ha; right; exact Ha)).
      * exact (FRSx _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs)
          ltac:(intros a Ha Hz; rewrite (UN a Ha Hz); exact (UN0 a Ha Hz)) ltac:(intros a Ha; right; exact Ha)).
      * exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HGm HG0) HG).
      * intros h2 h3. destruct (WRF _ (KBW _ (conj h2 (conj h3 eq_refl)))) as (_ & Xwin & X64 & _).
        cbn [ms_mem mkst]. rewrite <- (HK0 h2 h3). rewrite (UN _ X64 Xwin). exact (UN0 _ X64 Xwin).
      * intros _ h5. exfalso. lia.
    + (* alias_n <> 0: the instrumented check of alias[0] and the NUL store *)
      rewrite branch_eq_U, (U_atom E' 15 (aarg regs 5) E15'), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
      assert (Hac : 1 <= aarg regs 5) by lia. clear Hc.
      destruct (PAB Ha1 Hac) as (AGNL & AMOD & ATAB & AMR & ARA & AHULL).
      pose proof (ABW (aarg regs 4) (conj Ha1 (conj Hac eq_refl))) as AW.
      destruct (WRF _ AW) as (Aapp & Awin & A64 & ANS).
      assert (AWR : writable_at pa_segs (rdW W (ms_mem msC)) (aarg regs 4)).
      { destruct (PBA Ha1 Hac) as (junk & Hjl & (_ & Hjw)).
        pose proof (Hjw 0 ltac:(lia)) as Hw0. rewrite Z.add_0_r in Hw0.
        exact (WRG _ (ms_mem msC) AW Hw0 (mem_grows_trans _ _ _ HGm HG0)). }
      assert (U14 : bv_unsigned (ew E' 14) = aarg regs 4) by (rewrite E14'; apply unsigned_lit_small; lia).
      pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W
        (ms_mem msC) _ k HJm) as HARC.
      assert (FM1 : fmiss lyc Sc EX1).
      { apply fmiss_or; [exact (fmiss_side pa_segs B lyc Sc W memc mdc 1 pos HAR Hc1 Hp1 Hnin1)|].
        apply (fmiss_app pa_segs B LAWS lyc Sc W memc mdc KB HAR). intros a Ha. exact (proj1 (WRF a (KBW a Ha))). }
      destruct (shadow_transport pa_segs B LAWS TB pa_img_range lyc Sc W memc mdc lyc S1 W (ms_mem msC) _
        (spZ regs - MODEL_READ_AK) (spZ regs) EX1 (aarg regs 4) (aarg regs 5) HAR HARC eq_refl eq_refl
        ltac:(rewrite Eab1; intros b m Hb; exact Hb) HKC FM1 ltac:(lia)
        ltac:(intros x Hx;
              assert (Xw : inFP (model_read_awr regs (rdW W memc)) x)
                by (exists (aarg regs 4, aarg regs 4 + aarg regs 5); split; [|cbn [fst snd]; lia];
                    right; right; left; unfold aivl; rewrite (proj2 (Z.eqb_neq _ _) Ha1); reflexivity);
              destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
                k regs HENT x Xw) as (Xapp & _ & _ & Xajw & _);
              exact (sclass_of_ajw SK pa_segs B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
                memc mdc k x HGok HJ Xajw Xapp))
        ARA AHULL) as (ARAB & _).
      add_fact HS13 14%nat MR_PF
        ltac:(unfold afact_ok, MR_PF; cbn [af_lo af_hi af_al2]; rewrite U14; rewrite Z.pow_0_r, Z.mod_1_r;
              unfold amem_range in AMR; repeat split; lia).
      lazymatch type of HS13 with st_ok_pi _ _ ?Ev _ _ =>
      pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 14%nat) 0 1 0 1 []) HS13 eq_refl
        ltac:(unfold region_ok;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
              rewrite U14; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
              intros o Ho; replace (aarg regs 4 + o) with (aarg regs 4) by lia; exact AWR)
        ltac:(mr_disj; rewrite ?U60', ?Usp', ?U14; repeat split; lia)) as HS3 end.
      clear HS13; rename HS3 into HS13; norm_pi HS13.
      assert (SHA : sh_ok pa_segs MRBx [mkSHE 14 0 1] E' (mrestrict (w_H W) (ms_mem msC))).
      { apply (mr_shent_ok E' (w_H W) (ms_mem msC) 14 (aarg regs 4) 1 E32' E14' AR4 ltac:(lia)).
        - intros x Hx. replace x with (aarg regs 4) by lia. exact Aapp.
        - intros x Hx. apply ARAB. lia. }
      paj_run_tok RUN HS13 HJm SHA MRspan.
      { apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U14 in Ha;
          eapply ajw_mono; [exact (Hajw a (ABW a (conj Ha1 (conj Hac (ltac:(lia) : a = aarg regs 4))))) | intros b m Hb; rewrite Eab1; exact Hb
                           | intros x Hx; right; exact Hx | intros c q; reflexivity]
        | apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60' in Ha;
          left; split; [left; lia | lia]
        | apply awr_ok_x_cons;
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp' in Ha;
          left; split; [left; lia | lia]
        | apply awr_ok_x_nil ]]]. }
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _
        (fun a => a = aarg regs 4 \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
        ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                   rewrite ?U14, ?U60', ?Usp' in Hrr; cbv beta; lia |]);
              destruct Hin)) as UN.
      lazymatch type of HS13 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msK := m) in * end.
      assert (A0 : aview pa_segs (w_H W) (ms_mem msK) (aarg regs 4) = Some 0).
      { pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS13 eq_refl) as HR0.
        destruct HR0 as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HC.
        rewrite ?ew_ewset_other in HC by lia. rewrite U14 in HC.
        inversion HC as [|c cs Hc0 _]; subst. destruct (Hc0 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
        cbn [YP09.c_off] in Hb2. rewrite !Z.add_0_r in Hb2. unfold aview. rewrite Hb2.
        cbn [YP09.c_val cbyte] in Hb1. injection Hb1 as <-. vm_compute. reflexivity. }
      lazymatch type of HS13 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msZ := m) in * end.
      pmkst HS13.
      mr_joinS HS13 602%nat 0x15c [(11%bv : bv 5)] mr_ss15c HSj.
      refine (CONT15c _ _ _ _ _ HSj HJm _ _ _ _ _ _).
      * repeat first [apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]; exact HEI'.
      * split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply (proj1 OLD); lia
          | transitivity (ed E'); [reflexivity | exact (proj2 OLD)]].
      * repeat (eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]). exact Hsm'.
      * exact (STEP (ms_mem msC) _ _ HKC UN HG
          ltac:(intros a Ha; destruct Ha as [-> | Ha]; [left; exact (conj Ha1 (conj Hac eq_refl)) | right; exact Ha])).
      * exact (FRSx _ (fun a => a = aarg regs 4 \/ spZ regs - MODEL_READ_AK <= a < spZ regs)
          ltac:(intros a Ha Hz; rewrite (UN a Ha Hz); apply UN0; [exact Ha | intros Hw; apply Hz; right; exact Hw])
          ltac:(intros a Ha; destruct Ha as [-> | Ha]; [left; exact (conj Ha1 (conj Hac eq_refl)) | right; exact Ha])).
      * exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HGm HG0) HG).
      * exact (KK _ (fun a => a = aarg regs 4 \/ spZ regs - MODEL_READ_AK <= a < spZ regs)
          ltac:(intros a Ha Hz; rewrite (UN a Ha Hz); apply UN0; [exact Ha | intros Hw; apply Hz; right; exact Hw])
          ltac:(intros a Ha; exact Ha) ltac:(intros _ _; exact A0)).
      * intros _ _. exact A0.
}

apply (BR W E mr_ss120d ms md1 POST BC_EQ (SOff 12 0) (SLit 0) HSd); clear HSd; intros Hc HSd.
- (* kind = 0: on to +0x13c *)
  rewrite branch_eq_U, (U_atom E 12 (aarg regs 2) E12), U_lit in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hk0.
  mr_run_plain RUNP HSd HJ1.
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
  lazymatch type of HSd with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msA := m) in * end.
  pmkst HSd.
  mr_joinS HSd 600%nat 0x13c [(10%bv : bv 5); (11%bv : bv 5)] mr_ss13c HSj.
  refine (CONT13c _ _ _ _ _ HSj HJ1 _ _ _ _ _).
  + apply img_env_havoc_hi; [exact HEI | cbv; lia].
  + split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity].
  + exact (same_but_materialized_trans _ _ _ Hsm (same_but_materialized_wvb_any _ _)).
  + exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W m120 W _ (spZ regs - MODEL_READ_AK) (spZ regs)
      _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HAR Hsk ltac:(lia) HK UN
      (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => or_introl H)
      ltac:(intros a Ha; right; exact Ha)).
  + intros a Ha. apply UN; [pose proof (FRSlo a Ha); unfold FRS, in_zr, frame_rng, shadow_addr in Ha;
      cbn [fst snd] in Ha; fold F in Ha; change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia|].
    cbv beta. pose proof (FRSlo a Ha). lia.
  + exact HG.
  + intros H2. exfalso. exact (H2 Hk0).
- (* kind <> 0: +0x124 the test of kind_n *)
  rewrite branch_eq_U, (U_atom E 12 (aarg regs 2) E12), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  rename Hc into Hk1.
  mr_run_plain RUNP HSd HJ1.
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
          destruct Hin)) as UN0.
  rename HF into HF0, HFr into HFr0, HG into HG0.
  lazymatch type of HSd with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msB := m) in * end.
  pose proof (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W m120 W _ (spZ regs - MODEL_READ_AK) (spZ regs)
      _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HAR Hsk ltac:(lia) HK UN0
      (fun a _ Hp => apresent_grows _ _ _ _ HG0 Hp) (fun a H => H)
      ltac:(intros a Ha; right; exact Ha)) as HKB.
  apply (BR W E _ msB _ POST BC_EQ (SOff 13 0) (SLit 0) HSd); clear HSd; intros Hc HSd.
  + (* kind_n = 0: on to +0x13c *)
    rewrite branch_eq_U, (U_atom E 13 (aarg regs 3) E13), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    rename Hc into Hkn0.
    mr_run_plain RUNP HSd HJ1.
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
    lazymatch type of HSd with st_ok_pi _ _ _ _ (restrict _ ?m) => set (msA := m) in * end.
    pmkst HSd.
    mr_joinS HSd 600%nat 0x13c [(10%bv : bv 5); (11%bv : bv 5)] mr_ss13c HSj.
    refine (CONT13c _ _ _ _ _ HSj HJ1 _ _ _ _ _).
    * repeat first [apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]; exact HEI.
    * split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity].
    * eapply same_but_materialized_trans; [exact Hsm|].
      eapply same_but_materialized_trans; apply same_but_materialized_wvb_any.
    * exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W (ms_mem msB) W _ (spZ regs - MODEL_READ_AK) (spZ regs)
        _ _ (fun a => spZ regs - MODEL_READ_AK <= a < spZ regs) HAR Hsk ltac:(lia) HKB UN
        (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => or_introl H)
        ltac:(intros a Ha; right; exact Ha)).
    * intros a Ha. pose proof (FRSlo a Ha).
      transitivity (aview pa_segs (w_H W) (ms_mem msB) a).
      { apply UN; [unfold FRS, in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
                   change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia | cbv beta; lia]. }
      apply UN0; [unfold FRS, in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
                  change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia | cbv beta; lia].
    * exact (mem_grows_trans _ _ _ HG0 HG).
    * intros _ H3. exfalso. lia.
  + (* kind_n <> 0: the instrumented check of kind[0] and the NUL store (tok engine, kind's shadow entry) *)
    rewrite branch_eq_U, (U_atom E 13 (aarg regs 3) E13), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert (Hkc : 1 <= aarg regs 3) by lia. clear Hc.
    destruct (PKB Hk1 Hkc) as (KGNL & KMOD & KTAB & KMR & KRA & KHULL).
    assert (KWi : forall x, aarg regs 2 <= x < aarg regs 2 + aarg regs 3 ->
              inFP (model_read_awr regs (rdW W memc)) x).
    { intros x Hx. exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lia].
      right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) Hk1). reflexivity. }
    pose proof (KWi (aarg regs 2) ltac:(lia)) as KW.
    destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HENT _ KW)
      as (Kapp & Kwin & Kerr & Kajw & K64).
    assert (KNS : ~ aside_rng lyc 1 pos (aarg regs 2))
      by exact (ajw_not_side SK pa_segs B LAWS pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
        mdc k 1 pos _ HGok HJ Hc1 Hp1 Hnin1 Kajw Kapp).
    assert (KWR : writable_at pa_segs (rdW W (ms_mem msB)) (aarg regs 2)).
    { destruct (PBK Hk1 Hkc) as (junk & Hjl & (_ & Hjw)).
      pose proof (Hjw 0 ltac:(lia)) as Hw0. rewrite Z.add_0_r in Hw0.
      exact (WRG _ (ms_mem msB) KW Hw0 HG0). }
    assert (U12 : bv_unsigned (ew E 12) = aarg regs 2) by (rewrite E12; apply unsigned_lit_small; lia).
    (* the shadow of kind's bytes at this memory (LinkWalkShadow.v shadow_transport from the call) *)
    pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W
      (ms_mem msB) _ k HJ1) as HARB.
    destruct (shadow_transport pa_segs B LAWS TB pa_img_range lyc Sc W memc mdc lyc S1 W (ms_mem msB) _
      (spZ regs - MODEL_READ_AK) (spZ regs) (aside_rng lyc 1 pos) (aarg regs 2) (aarg regs 3) HAR HARB eq_refl eq_refl
      ltac:(rewrite Eab1; intros b m Hb; exact Hb) HKB
      (fmiss_side pa_segs B lyc Sc W memc mdc 1 pos HAR Hc1 Hp1 Hnin1) ltac:(lia)
      ltac:(intros x Hx; destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
              k regs HENT x (KWi x Hx)) as (Xapp & _ & _ & Xajw & _);
            exact (sclass_of_ajw SK pa_segs B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
              memc mdc k x HGok HJ Xajw Xapp))
      KRA KHULL) as (KRAB & _).
    add_fact HSd 12%nat MR_PF
      ltac:(unfold afact_ok, MR_PF; cbn [af_lo af_hi af_al2]; rewrite U12; rewrite Z.pow_0_r, Z.mod_1_r;
            unfold amem_range in KMR; repeat split; lia).
    lazymatch type of HSd with st_ok_pi _ _ ?Ev _ _ =>
    pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 12%nat) 0 1 0 1 []) HSd eq_refl
      ltac:(unfold region_ok;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
            rewrite U12; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
            intros o Ho; replace (aarg regs 2 + o) with (aarg regs 2) by lia; exact KWR)
      ltac:(mr_disj; rewrite ?U60, ?Usp, ?U12; repeat split; lia)) as HS3 end.
    clear HSd; rename HS3 into HSd; norm_pi HSd.
    assert (SHK : sh_ok pa_segs MRBx [mkSHE 12 0 1] E (mrestrict (w_H W) (ms_mem msB))).
    { apply (mr_shent_ok E (w_H W) (ms_mem msB) 12 (aarg regs 2) 1 E32 E12 AR2 ltac:(lia)).
      - intros x Hx. replace x with (aarg regs 2) by lia. exact Kapp.
      - intros x Hx. apply KRAB. lia. }
    paj_run_tok RUN HSd HJ1 SHK MRspan.
    { apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U12 in Ha;
        eapply ajw_mono; [exact (Hajw a (KWi a ltac:(lia))) | intros b m Hb; rewrite Eab1; exact Hb
                         | intros x Hx; right; exact Hx | intros c q; reflexivity]
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60 in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp in Ha;
        left; split; [left; lia | lia]
      | apply awr_ok_x_nil ]]]. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _
      (fun a => a = aarg regs 2 \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
      ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                                 rewrite ?U12, ?U60, ?Usp in Hrr; cbv beta; lia |]);
            destruct Hin)) as UN.
    lazymatch type of HSd with st_ok_pi _ _ ?Ef _ (restrict _ ?m) => set (msK := m) in * end.
    assert (K0 : aview pa_segs (w_H W) (ms_mem msK) (aarg regs 2) = Some 0).
    { pose proof (st_ok_pi_region_nth _ _ _ 0 _ HSd eq_refl) as HR0.
      destruct HR0 as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HC.
      rewrite ?ew_ewset_other in HC by lia. rewrite U12 in HC.
      inversion HC as [|c cs Hc0 _]; subst. destruct (Hc0 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
      cbn [YP09.c_off] in Hb2. rewrite !Z.add_0_r in Hb2. unfold aview. rewrite Hb2.
      cbn [YP09.c_val cbyte] in Hb1. injection Hb1 as <-. vm_compute. reflexivity. }
    pmkst HSd.
    mr_joinS HSd 600%nat 0x13c [(10%bv : bv 5); (11%bv : bv 5)] mr_ss13c HSj.
    refine (CONT13c _ _ _ _ _ HSj HJ1 _ _ _ _ _).
    * repeat first [apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]; exact HEI.
    * split; [intros n Hn; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity].
    * eapply same_but_materialized_trans; [exact Hsm|].
      eapply same_but_materialized_trans; apply same_but_materialized_wvb_any.
    * exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W (ms_mem msB) W _ (spZ regs - MODEL_READ_AK)
        (spZ regs) _ _ (fun a => a = aarg regs 2 \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HAR Hsk ltac:(lia) HKB UN
        (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => or_introl H)
        ltac:(intros a Ha; cbv beta in Ha |- *; destruct Ha as [Ha | Ha];
              [left; right; exact (conj Hk1 (conj Hkc Ha)) | right; exact Ha])).
    * intros a Ha. pose proof (FRSlo a Ha).
      assert (Ha64 : 0 <= a < 2 ^ 64)
        by (unfold FRS, in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold F in Ha;
            change (fs_frame_bytes 1) with 128 in Ha; unfold SHADOW_OFF in Ha; lia).
      assert (Hne : a <> aarg regs 2).
      { intros ->. apply KNS. unfold aside_rng. destruct Ha as [Ha | Ha]; [left; exact Ha|].
        right; left. fold F. change (fs_frame_bytes 1 / 8) with 16. exact Ha. }
      transitivity (aview pa_segs (w_H W) (ms_mem msB) a).
      { apply UN; [exact Ha64 | cbv beta; intros [Hq | Hq]; [exact (Hne Hq) | lia]]. }
      apply UN0; [exact Ha64 | cbv beta; lia].
    * exact (mem_grows_trans _ _ _ HG0 HG).
    * intros _ _. exact K0.
Qed.
End b.
End a.
