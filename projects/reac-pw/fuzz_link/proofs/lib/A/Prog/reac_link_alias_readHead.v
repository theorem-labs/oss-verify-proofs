(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 595 of its 658 lines of code are new or changed and 1244 lines of the source are left out. *)
(* reac_link_alias_read (fuzz_link.asan 0x8867c, AF_reac_link_alias_read = 0x64b0, 760 bytes) on image A:
   the HEAD of its walk, from the contract's entry to the MID cut (+0x118 `beqz s5`) of
   lib/A/Prog/reac_link_alias_readDefs.v, and the composition of the three obligations into the contract.

   The code walked (listing (internal path) (internal record, sha256 7c23ed8f465f)):
     +0x00..+0x78  the 128-byte machine frame, the probe `sd zero,0(sp)`, ra and s0..s10 saved, s0 := the
                   entry sp, `andi sp,sp,-0x20`, s1 := sp, the four argument moves, the two .got words,
                   `beqz a2` (not taken: the switch cell holds 1, AR's const law), frame_alloc_1(0x60)
                   (the token run, LinkWalk.v paj_run_x)
     +0x78         frame_alloc_1 (0x3da88) through LinkWalkSide.v aj_gx_stack_malloc_at
     +0x7c..+0x114 s2 := s10 := F, `bnez s2` (taken: 4096 <= F), the word at s1 + 0x18, F's header
                   (magic, descriptor, pc) and its sixteen shadow bytes (the plain run,
                   LinkWalkSide.v paj_run_plain_x, which stops at +0x118 `beqz s5`)

   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_read_c nl_talk_c fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_readDefs reac_link_alias_readPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkMkVis.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB13.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


(* the all_disjoint obligation of st_ok_pi_add_region, with the region list computed and the extents opened *)
Ltac ar_disj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  try change (fs_frame_bytes 1) with 128; try change (fs_frame_bytes 1 / 8) with 16.

(* a segment of the PLAIN engine over ajournal_gx (LinkWalkSide.v SRr_run_pi_AJX), as pcap's paj_run_shc *)
Ltac ar_run_plain RUNP HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi link_tpi FUEL ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi link_tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNP W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      [ clear Hrun
      | clear Hrun HS HJ;
        let ms' := fresh "ms" in let mat := fresh "mat" in
        let hj := fresh "HJp" in
        let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
        intros ms' mat HS hj HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, hj ]
    end
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
(* frame_alloc_1 (0x3da88): lib/A/AF0s.v stack_malloc1_contract, at tfibsegs *)
Hypothesis ASM1 : astack_malloc_realizes pa_segs B 1.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = pa_sigma LS___asan_stack_malloc_1.
(* the one segment computation the walk needs (g_nl writable, the relro window): the link PAImg instance
   discharges this by reflexivity (the library walks' convention) *)
Hypothesis HSEGS : pa_segs = tfibsegs.
(* link's image certificate (lib/A/AF0m.v PcapSyms), discharged at link's B by AD2l.PcapB_syms *)
Hypothesis TB : AF0m.PcapSyms B.
(* the read-only window is image bytes; discharged in the composing file *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.



(* g_nl lies inside one loaded segment of image A, and meets no runtime static of its certificate tables.
   reac_link_alias_writeHead.v has the same two computations for the same bytes; when
   they are lifted into a shared LinkWalk<Topic>.v I drop these. *)
Lemma ar_gnl_in_image_b :
  existsb (relro_in_seg LA_G_NL (LA_G_NL + NK_SIZE)) Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ar_gnl_static_b :
  forallb (fun r => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r)) AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ar_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img pa_segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. split; [|split].
  - rewrite HSEGS. destruct (proj1 (existsb_exists _ _) ar_gnl_in_image_b) as (s & Hin & H).
    unfold relro_in_seg in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H3.
    exists s. split; [exact Hin | lia].
  - rewrite (AF0m.ts_owned B TB). intros HE. apply Exists_exists in HE as (r & Hr & Hz).
    pose proof (proj1 (forallb_forall _ _) ar_gnl_static_b r Hr) as Hb. cbv beta in Hb.
    apply orb_true_iff in Hb. unfold in_zr in Hz.
    destruct Hb as [Hb | Hb]; apply Z.leb_le in Hb; unfold LA_G_NL, NK_SIZE in *; lia.
  - rewrite (AF0m.ts_errno B TB). unfold AF0m.TFIB_ERRNO, LA_G_NL, NK_SIZE in *. lia.
Qed.

(* an 8-byte chunk of a region based at an atom, read back as a word of the view *)
Lemma ar_region_word : forall Ex H m (r : YP09.region) (b : nat) bv off (n : nat),
  region_ok pa_segs Ex (mrestrict H m) r -> YP09.r_base r = Some b -> bv_unsigned (ew Ex b) = bv ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks r) ->
  rdword (aview pa_segs H m) (bv + off) = Some (bv_unsigned (ew Ex n)).
Proof.
  intros Ex H m [rb lo hi wlo whi cs] b bv off n HR Hb Hbv Hin. cbn [YP09.r_base YP09.r_chunks] in Hb, Hin.
  subst rb.
  pose proof (bv_unsigned_in_range 64 (ew Ex n)) as Hr.
  apply (rdword_of_val_mem pa_segs); [| change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr].
  exact (field_of_region Ex (mrestrict H m) b bv cs lo hi wlo whi off 8%N (SOff n 0) (bv_unsigned (ew Ex n)) HR
    Hbv Hin ltac:(cbn [sv_denot]; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (bv_modulus 64); exact Hr) ltac:(cbn; lia)).
Qed.
(* a byte of the caller's write set (apre's ajw) is a byte an akept keeps, outside its window and exception set
   (the case split of LinkWalkShadow.v sclass_of_ajw, landing on akept's four value clauses) *)
Lemma ar_ajw_kept : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 mem2 slo shi
    (E : Z -> Prop) a,
  gx_ok pa_segs B G ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  akept pa_segs B lyc Sc W memc W2 mem2 slo shi E ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (a < kLowMemEnd \/ kHighMemBeg <= a) ->
  ~ (slo <= a < shi) -> ~ E a -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview pa_segs (w_H W2) mem2 a = aview pa_segs (w_H W) memc a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 mem2 slo shi E a HG HJ HKp Hw Happ
    Hwin HE Herr.
  pose proof HKp as (K1 & K2 & K3 & K4 & _).
  destruct (ajournal_gx_row SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
    as (R1 & R2 & R3 & R4).
  assert (H47 : 2 ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _).
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + apply K1; [lia | exact Hwin | exact HE].
    + replace a with (b + (a - b)) by lia.
      eapply K2; [exact Hin | lia | replace (b + (a - b)) with a by lia; exact HE].
    + replace a with (b + (a - b)) by lia.
      eapply K2; [exact Hin | lia | replace (b + (a - b)) with a by lia; exact HE].
    + assert (Hcq : In (c, q) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
      destruct Hr as [Hr | Hr].
      * apply (K4 c q a Hcq); [left; unfold frame_rng; exact Hr | exact HE].
      * exfalso. destruct (frames_bounds pa_segs B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hf4096 & Hfceil & _).
        pose proof (fs_frame_bytes_nonneg c) as Hnn. pose proof asan_consts as ((C1a & C1b) & _).
        unfold in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
        unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. lia.
  - destruct (HG a HGa) as (Hi & Ho). exact (K3 a Hi Ho Herr HE).
  - apply K1; [lia | exact Hwin | exact HE].
Qed.

(* One saved word of the prologue at a cut, read off a region of the cut's state. *)
Ltac ar_save HRst U3_2 OLDA EREG :=
  lazymatch goal with |- rdword _ (?sp - 16 - 8 * ?j) = Some (bv_unsigned (getr ?rg (Z_to_bv 5 ?e))) =>
    let n := eval vm_compute in (Z.to_nat e) in
    let off := eval vm_compute in (-16 - 8 * j) in
    replace (sp - 16 - 8 * j) with (sp + off) by lia;
    replace (Z_to_bv 5 e) with (Z_to_bv 5 (Z.of_nat n)) by reflexivity;
    rewrite <- (EREG n ltac:(lia)), <- (OLDA n ltac:(lia));
    rewrite (ar_region_word _ _ _ _ 2%nat sp off n HRst eq_refl U3_2
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])));
    reflexivity
  end.

(* every image address is backed by the image file (AB13.v tfib_rom_all, at link's segments) *)
Lemma ar_rom : forall a, 0x10000 <= a < pcap_img_end -> seg_rom pa_segs (Z_to_bv 64 a) <> None.
Proof. intros a Ha. rewrite HSEGS. exact (AB13.tfib_rom_all a Ha). Qed.

Let errno_low := pal_env B TL.

Theorem ar_head : ar_mid_obl SK B -> ar_send_obl SK B -> ar_exit_obl SK B ->
  reac_link_alias_read_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
intros MID SEND EXIT.
unfold reac_link_alias_read_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
set (cx := mkARCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
assert (HPX : ar_pre SK B cx) by exact (conj HPRE (conj HRD HP)).
change (SRr pa_segs W (cfg_at pa_segs REAC_LINK_ALIAS_READ_A regs memc mdc) (ar_post SK B cx)).
pose proof HPRE as HPRE0.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HJ as HJ0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : REAC_LINK_ALIAS_READ_AK = 8592) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(lia) Hwhi) as (memS & HJi & HSTK & HXO & Hpresw & Hceil47).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  HJ) as Hpres0.
destruct Hceil47 as (Hceil & H47).
assert (Hspc : alloc_ceiling + REAC_LINK_ALIAS_READ_AK <= spZ regs) by lia.
(* the entry *)
pose proof (ar_entry SK B LAWS HV TL G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  HJ Hal16 Hwlo Hwhi) as HS.
remember (Eimg (Ereg regs AR_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs AR_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 AR_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs AR_extra 0)).
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (HAE : env_agree 32 (Ereg regs AR_extra) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
assert (SHOK : sh_ok pa_segs ARBx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : cfg_at pa_segs REAC_LINK_ALIAS_READ_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_reac_link_alias_read)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text HV). reflexivity. }
rewrite HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNP := paj_run_plain_x SK B LAWS G HGok XO OUT).
pose (RUNC := paj_run_call_plain_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
(* ---- the prologue, the two GOT loads and the switch test, up to frame_alloc_1 (+0x78) ---- *)
paj_run_tok RUN HS HJ SHOK ARspan;
  [ unfold ar_ss, ar_regions, ar_stack, ar_got, ar_cell, ar_ugot, ar_ucell;
    apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp in Ha;
      left; split; [left; lia | lia]
    | repeat (apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|]);
      apply awr_ok_x_nil ] |].
(* ---- the state at the frame_alloc_1 call: the realigned sp is the atom 60 of the next phase ---- *)
pmkst HS.
sreg HS (1%bv : bv 5) R1. sreg HS (2%bv : bv 5) R2.
sreg HS (3%bv : bv 5) R3. sreg HS (4%bv : bv 5) R4.
cbn [ms_regs restrict mkst] in R1, R2, R3, R4.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
assert (Hsp1e : 32 * ((spZ regs + -128) / 32) = sp1) by (unfold sp1; f_equal; f_equal; lia).
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
rewrite (denot_and_m32 E 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in R2.
change (SOff 240 25900) with (SOff A_TEXT 25900) in R1.
rewrite (codeptr_val E 25900 HEI) in R1.
assert (R3' : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite R3; cbn [sv_denot]; rewrite E3, Hgp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (R4' : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite R4; cbn [sv_denot]; rewrite E4, Htp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (Rsp : spZ (ms_regs ms) = sp1)
  by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hcnt : count_cid 1 (frames Sc) < fs_frames 1).
{ apply (aside_room_take Sc REAC_LINK_ALIAS_READ_ASIDE 1 1 Hside);
  [ unfold REAC_LINK_ALIAS_READ_ASIDE; cbn [In]; left; reflexivity | lia ]. }
eapply SRr_bind.
{ eapply (aj_gx_stack_malloc_at SK pa_segs B LAWS Hsegs errno_low 1 ASM1 ltac:(lia)
    (pa_sigma LS___asan_stack_malloc_1) G XO OUT W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc _ k _ HSM1 HJ).
  - rewrite Rsp. exact Hsp1al16.
  - rewrite Rsp. lia.
  - rewrite Rsp. lia.
  - exact R3'.
  - exact R4'.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hcnt. }
cbv beta. intros W2 c2 _ (-> & S1 & regs1 & mem1 & md1 & pos & -> & HJ1 & HP1 & Ha01 & Eab1 & Hfrs1 & Hnin1
  & Hnev1 & Hbb1 & Hfs1 & HF4096 & HFceil & Hz & Hflagw & HKEPT & Hsame1 & Hown1).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W mem1 md1 k
  HJ1) as HAR1.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (Hposr : 0 <= pos < fs_frames 1).
{ assert (HLw : Forall (fun cp => 0 <= fst cp <= 10 /\ 0 <= snd cp < fs_frames (fst cp)) (frames S1)).
  { destruct HAR1 as (HM & _). destruct HM. destruct am_wf. destruct wf_fakestack. exact wfs_live. }
  rewrite Forall_forall in HLw. destruct (HLw (1, pos) Hin1) as (Hcq & Hpq).
  cbn [fst snd] in Hcq, Hpq. lia. }
destruct (frame_al64 pa_segs B lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HFa64 & HFb64 & HFb).
destruct (al_frames _ _ LAWS lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HFal32 & HFapp & HFpres & HFSpres).
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own)
  lyc S1 W mem1 md1 k HJ1) as Hpres1.
destruct (frames_bounds pa_segs B LAWS lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
pose proof (frm_off_imgP B lyc S1 W mem1 md1 1 pos HAR1 Hin1) as HFimg.
destruct (al_flag _ _ LAWS lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HFLpres & HFLown & HFLapp & HFLc).
set (F := frame_addr lyc 1 pos) in *.
set (FL := flag_addr lyc 1 pos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp2.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (HFL64 : 0 <= FL < 2 ^ 64)
  by (destruct HFLapp as (Hq1 & _); revert Hq1 HFLc C1a C1b; clear; intros; lia).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (HF8u : F < 8 * (F / 8) + 8)
  by (pose proof (Z.mod_pos_bound F 8 ltac:(lia)); pose proof (Z_div_mod_eq_full F 8); lia).
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8al : (AR_SB + F / 8) mod 8 = 0).
{ unfold AR_SB. destruct (div8_of_mul64 F HFa64) as [E8 _]. rewrite E8.
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
rewrite Rsp, HES in HKEPT.
(* the state after the call: keep only the machine frame; its bytes are above the call's window *)
jafter_call_keep_hi HS 40%nat regs1 (mrestrict (w_H W) mem1) HP1 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview pa_segs). pose proof HKEPT as (K1 & _).
    first [ apply K1; [lia | lia] | apply K1; [lia | lia | intros []] ].
  - intros _. apply (apresent_writable pa_segs). apply Hpres1. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs1) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env pa_val A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE1 : env_agree 32 (Ereg regs AR_extra) Ev1)
  by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE1.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10; cbn [ms_regs mkst]; exact Ha01).
clear R10.
assert (E1_2 : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; exact E2').
assert (E1_32 : ew Ev1 32 = Z_to_bv 64 AR_SB) by (rewrite OLD1 by lia; exact E32).
assert (E1_1 : ew Ev1 1 = getr regs 1) by (rewrite OLD1 by lia; exact E1).
(* atom 60 = the realigned sp, 61 = the frame's flag, 62 = SB + F / 8 *)
prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ regs) (-128) E1_2 ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in Rsp2.
rewrite (denot_and_m32_add0 Ev1 2 (spZ regs) (-128) E1_2 ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in Rs12.
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1]) as E2v eqn:HE2 in HS.
assert (OLD2 : forall nn, (nn < 60)%nat -> ew E2v nn = ew Ev1 nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E2v 60 = Z_to_bv 64 sp1)
  by (rewrite HE2; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env pa_val A_LIM E2v) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
clear HE2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned;
          symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned;
          symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_havoc_hi 61 E2v _ _ [Z_to_bv 64 FL; Z_to_bv 64 (AR_SB + F / 8)] HS
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (AR_SB + F / 8)]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 61)%nat -> ew E3v nn = ew E2v nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E61 : ew E3v 61 = Z_to_bv 64 FL)
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (AR_SB + F / 8)] 0 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 (AR_SB + F / 8))
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (AR_SB + F / 8)] 1 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (HEI3 : img_env pa_val A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
clear HE3.
assert (OLDA : forall nn, (nn < 40)%nat -> ew E3v nn = ew E nn)
  by (intros nn Hnn; rewrite OLD3, OLD2, OLD1 by lia; reflexivity).
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD3, OLD2 by lia; exact E1_2).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 AR_SB) by (rewrite OLD3, OLD2 by lia; exact E1_32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3, OLD2 by lia; exact E44).
assert (E3_60 : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite OLD3 by lia; exact E60).
assert (E3_1 : ew E3v 1 = getr regs 1) by (rewrite OLD3, OLD2 by lia; exact E1_1).
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E3_60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = AR_SB + F / 8)
  by (rewrite E62; apply unsigned_lit_small; unfold AR_SB; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ regs) by (rewrite E3_2; apply unsigned_lit_small; lia).
(* the facts of the three new atoms and the shadow alias: the engine reads (F >> 3) + SB as atom 62 *)
add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_60, unsigned_lit_small by lia;
        change (2 ^ 5) with 32; repeat split; lia).
add_fact HS 44%nat (mkAF 4096 (2 ^ 47) 6)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_44, unsigned_lit_small by lia;
        change (2 ^ 6) with 64; repeat split; lia).
add_fact HS 62%nat (mkAF AR_SB (AR_SB + 2 ^ 44) 3)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E62, unsigned_lit_small by (unfold AR_SB; lia);
        change (2 ^ 3) with 8; repeat split; [unfold AR_SB; lia | unfold AR_SB; lia | exact HF8al | lia | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS
    (shadow_decl_ok Ev 44 32 62 F AR_SB E3_44 ltac:(lia) E3_32 E62)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* the machine frame trimmed to the twelve saved words; the store through s1 (+0xac) lands below them *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  let rs := eval vm_compute in (trim_stack (ss_mem ssx) (-96) 0) in
  pose proof (st_ok_pi_submem Ev ssx msx rs HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
assert (HdFS : F + 128 <= AR_SB + F / 8 \/ AR_SB + F / 8 + 16 <= F).
{ assert (HSBv : AR_SB = 2147450880) by reflexivity.
  destruct HFapp2 as (Hf4x & [Hlowx | (Hhighx & Hhcx)]).
  - left. clear - Hf4x Hlowx HSBv HF8m HF8u. lia.
  - right. clear - Hf4x Hhighx HSBv HF8m HF8u. lia. }
(* the slot of s1, the frame (its flag word at 120) and the frame's shadow (zero, frame_alloc_1's zero_shadow) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 32 0 32 []) HS eq_refl
  ltac:(unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply Hpres1; lia)
  ltac:(ar_disj; rewrite ?U60, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val pa_segs _ _ F 120 8 _ FL);
          [ cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
          | replace (F + 120) with (F + 128 - 8) by lia;
            exact (val_mem_of_rdword pa_segs _ _ _ _ Hflagw) ] ])
  ltac:(ar_disj; rewrite ?U60, ?U44, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 1 0 16 [YP09.mkChunk 0 (CZero 16)]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold AR_SB; lia|];
        split; [unfold AR_SB; lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs);
          replace (AR_SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, AR_SB, SHADOW_OFF; lia);
          apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply chunk_ok_zero; intros i Hi;
          pose proof (Hz i ltac:(change (128 / 8) with 16; lia)) as Hzi;
          unfold shadow_of_addr in Hzi; destruct (aview_byte pa_segs _ _ _ _ Hzi) as (bb & Hbb & Hv & _);
          replace (AR_SB + F / 8 + 0 + i) with (SHADOW_OFF + F / 8 + i) by (unfold AR_SB, SHADOW_OFF; lia);
          rewrite Hbb; f_equal; apply bv_eq; rewrite <- Hv; reflexivity ])
  ltac:(ar_disj; rewrite ?U60, ?U44, ?U62, ?U3_2; unfold AR_SB in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
rewrite R1.
(* ---- +0x7c .. +0x114 (plain): the frame's magic, descriptor and pc, and its sixteen shadow bytes,
   up to the branch `beqz s5` at +0x118 ---- *)
ar_run_plain RUNP HS HJ1.
{ apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fshadow_region]; intros a Ha;
    change (fs_frame_bytes 1 / 8) with 16 in Ha; rewrite U62 in Ha;
    left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) lyc S1 W mem1 md1 k 1 pos a HJ1 ltac:(left; reflexivity));
    right; unfold in_zr, shadow_addr; cbn [fst snd];
    change (fs_frame_bytes 1 / 8) with 16; unfold AR_SB, SHADOW_OFF in *; lia
  | apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fframe_region]; intros a Ha;
    change (fs_frame_bytes 1) with 128 in Ha; rewrite U44 in Ha;
    left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) lyc S1 W mem1 md1 k 1 pos a HJ1 ltac:(left; reflexivity));
    left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
  | apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60 in Ha;
    left; split; [left; lia | lia]
  | apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U3_2 in Ha;
    left; split; [left; lia | lia]
  | apply awr_ok_x_nil ]]]]. }
(* ---- the MID cut at +0x118 ---- *)
cbv beta in HS, HJp.
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms3.
destruct (ms_shape_mkst pa_segs ms0 _ _ _ Hms3) as (Hr3 & Hsv3 & Hrom3 & Hfr3 & Hfc3 & Hpc3).
cbn [ss_pc] in Hpc3.
prreg HS (2%bv : bv 5) F2. prreg HS (9%bv : bv 5) F9. prreg HS (8%bv : bv 5) F8.
prreg HS (18%bv : bv 5) F18. prreg HS (26%bv : bv 5) F26.
prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (27%bv : bv 5) F27.
prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
prreg_raw HS (25%bv : bv 5) F25.
spregion HS 3%nat HRst. spregion HS 1%nat HRF.
(* the kept clause of the head: the window, frame_alloc_1's acall_kept, the two runs' frames *)
set (Ea := aside_rng lyc 1 pos).
set (slo := spZ regs - REAC_LINK_ALIAS_READ_AK).
assert (Hslo_c : alloc_ceiling <= slo) by (unfold slo; rewrite HK; lia).
assert (K0 : akept pa_segs B lyc Sc W memc W memc slo (spZ regs) Ea).
{ apply (akept_refl SK pa_segs B LAWS Hsegs). intros a Ha. apply Hpres0. unfold slo in Ha. rewrite HK in Ha. lia. }
pose proof (kept_of_frame (segs := pa_segs) E (ss_mem ar_ss) (w_H W) memc (ms_mem ms)
  (fun a => spZ regs - 128 <= a < spZ regs) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?Usp in HrrW; cbv beta; lia|]); destruct HinW)) as UN1.
assert (K1 : akept pa_segs B lyc Sc W memc W (ms_mem ms) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W memc W (ms_mem ms) slo (spZ regs) Ea Ea
    (fun a => spZ regs - 128 <= a < spZ regs) HAR Hslo_c ltac:(lia) K0 UN1).
  - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
  - intros a H; exact H.
  - intros a Ha. right. unfold slo; rewrite HK. cbv beta in Ha. lia. }
assert (K2 : akept pa_segs B lyc Sc W memc W mem1 slo (spZ regs) Ea).
{ eapply (akept_trans SK pa_segs B LAWS Hsegs lyc Sc W memc Sc W (ms_mem ms) W mem1 slo (spZ regs)
    (sp1 - 4096) sp1 Ea Ea Ea Hslo_c ltac:(lia) K1
    (akept_of_acall_kept SK pa_segs B LAWS Hsegs lyc Sc W (ms_mem ms) W mem1 (sp1 - 4096) sp1
       (fun _ => False) Ea HKEPT (fun a H => match H with end))).
  - unfold slo; rewrite HK; lia.
  - lia.
  - intros bb mm H; exact H.
  - intros f H; exact H.
  - intros a H; exact H.
  - intros a H; exact H. }
set (X3 := fun a : Z => (AR_SB + F / 8 <= a < AR_SB + F / 8 + 16) \/ (F <= a < F + 128) \/
  (sp1 <= a < sp1 + 32) \/ (spZ regs - 96 <= a < spZ regs)).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ X3 HFr0
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U62, ?U44, ?U60, ?U3_2 in HrrW; unfold X3; lia|]); destruct HinW)) as UN3.
assert (K3 : akept pa_segs B lyc Sc W memc W (ms_mem ms0) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W mem1 W (ms_mem ms0) slo (spZ regs) Ea Ea X3
    HAR Hslo_c ltac:(lia) K2 UN3).
  - intros a _ Hp. eapply apresent_grows; [exact HG0 | exact Hp].
  - intros a H; exact H.
  - intros a Ha. unfold X3 in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    + left. unfold Ea, aside_rng. right; left. unfold in_zr, shadow_addr. cbn [fst snd].
      change (fs_frame_bytes 1 / 8) with 16. unfold AR_SB, SHADOW_OFF in *. lia.
    + left. unfold Ea, aside_rng. left. unfold in_zr, frame_rng. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. lia.
    + right. unfold slo; rewrite HK. lia.
    + right. unfold slo; rewrite HK. lia. }
pose proof K3 as (_ & _ & K3img & _).
assert (NSIDE : forall a, in_img pa_segs a -> ~ Ea a).
{ intros a Hi HE.
  destruct (aside_rng_low SK pa_segs B LAWS Hsegs lyc S1 W mem1 md1 1 pos a HAR1 Hin1 HE) as (_ & Hn).
  exact (Hn Hi). }
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W
  (ms_mem ms0) _ k HJp) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR3 Hin1) as (_ & _ & HFpres3 & HFSpres3).
change (fs_frame_bytes 1) with 128 in HFpres3, HFSpres3. change (128 / 8) with 16 in HFSpres3.
assert (Hfd : m_fds (with_vm_backing (m_vm_lazy md1) mat0 md1) = m_fds mdc /\
              m_fs (with_vm_backing (m_vm_lazy md1) mat0 md1) = m_fs mdc).
{ pose proof (same_but_materialized_wvb _ _ Hsame1) as Emd.
  assert (Ef1 : m_fds md1 = m_fds mdc).
  { rewrite Emd at 1. rewrite (proj1 (wvb_fds_fs _ _ _)). exact (proj1 (wvb_fds_fs _ _ _)). }
  assert (Ef2 : m_fs md1 = m_fs mdc).
  { rewrite Emd at 1. rewrite (proj2 (wvb_fds_fs _ _ _)). exact (proj2 (wvb_fds_fs _ _ _)). }
  split; [rewrite (proj1 (wvb_fds_fs _ _ _)); exact Ef1
         | rewrite (proj2 (wvb_fds_fs _ _ _)); exact Ef2]. }
refine (MID cx pos lyc S1 W ms0 _ HPX _).
unfold ar_gi_mid, ar_base, ar_gnl_kept. cbv zeta.
unfold ar_FL, ar_SH, ar_sp1, ar_name, ar_kind, ar_kn, ar_alias, ar_an, ar_E, ar_wr, ar_m0, ar_F, ar_sp.
unfold cx. cbn [ar_G ar_XO ar_OUT ar_STK ar_sp0 ar_FP ar_ly ar_S ar_W0 ar_mem0 ar_md0 ar_own ar_lyc ar_Sc ar_W
  ar_memc ar_mdc ar_k ar_regs].
unfold AR_CID, AR_FB, AR_SHN, AR_FLAGPTR, AR_FRAME. rewrite HK. fold F. fold FL.
split; [rewrite Hpc3; apply (f_equal (Z_to_bv 64)); unfold AR_CUT_MID, AF_reac_link_alias_read; lia|].
split; [rewrite F19, OLD3, OLD2, OLD1 by lia; rewrite (EREG 13%nat ltac:(lia));
        unfold w64, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F20, OLD3, OLD2, OLD1 by lia; rewrite (EREG 14%nat ltac:(lia));
        unfold w64, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F21, OLD3, OLD2, OLD1 by lia; rewrite (EREG 11%nat ltac:(lia));
        unfold w64, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F22, OLD3, OLD2, OLD1 by lia; rewrite (EREG 12%nat ltac:(lia));
        unfold w64, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F23, OLD3, OLD2, OLD1 by lia; rewrite (EREG 10%nat ltac:(lia));
        unfold w64, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F24, E3_32; reflexivity|].
split.
{ intros a Ha. destruct (ar_gnl_img a Ha) as (Hi & Ho & He). exact (K3img a Hi Ho He (NSIDE a Hi)). }
split.
{ intros a Ha.
  assert (Hb : akb pa_segs B lyc Sc (spZ regs - REAC_LINK_ALIAS_READ_AK) (spZ regs) a) by exact (HRD a Ha).
  apply (akept_akb_gx SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W (ms_mem ms0)
    slo (spZ regs) Ea a HJ0 K3 ltac:(unfold slo; rewrite HK; exact Hb)).
  exact (akb_not_side SK pa_segs B pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (spZ regs - REAC_LINK_ALIAS_READ_AK) (spZ regs) 1 pos a HJ0 ltac:(lia) Hposr Hnin1 Hb). }
split.
{ intros p str Hstr a Ha.
  destruct HP as (kbs1 & tab1 & nm1 & Hnk1 & _ & _ & _ & _ & Hit1 & _ & _ & _ & Hsa1 & _ & _ & Htab1
    & _ & _ & _ & _ & Hnmf1 & _ & _ & _ & _).
  (* the contract's tail clause at the entry, and the string's NUL in the read set *)
  assert (Hent : ard pa_segs (mrestrict (w_H W) memc) a <> None /\
                 reac_link_alias_read_ard pa_segs regs (mrestrict (w_H W) memc) (p + Z.of_nat (length str))).
  { destruct Hstr as [(Hpn & Hnm) | (bs & tab & i & ix & Hnk & Hit & Hi & Hu & Hp64 & Hcs)].
    - assert (nm1 = Some str) by exact (ar_astr_arg_unique pa_segs _ _ _ _ Hsa1 Hnm).
      destruct (Hnmf1 str ltac:(assumption)) as (_ & _ & _ & _ & Htl). subst p.
      destruct Hnm as (Hn0 & Hcs).
      split; [exact (Htl a Ha)|].
      left. split; [exact Hn0|]. exists str. split; [exact Hcs | unfold ar_name, cx; cbn [ar_regs]; lia].
    - assert (kbs1 = bs) by exact (ar_anlk_unique pa_segs _ _ _ _ Hnk1 Hnk). subst bs.
      assert (tab1 = tab) by exact (ar_aiftab_unique pa_segs _ _ _ _ Hit1 Hit). subst tab.
      destruct (Htab1 i str ix p Hi Hu) as (_ & _ & _ & _ & _ & POS).
      destruct (POS Hp64) as (_ & _ & _ & Htl).
      split; [exact (Htl a Ha)|].
      right. exists kbs1, tab1, i, str, ix, p. split; [exact Hnk|]. split; [exact Hit|]. split; [exact Hi|].
      split; [exact Hu|]. split; [exact Hcs | lia]. }
  destruct Hent as (Hvis & Hrd).
  pose proof (HRD _ Hrd) as Hb.
  destruct (ajournal_gx_row SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ0)
    as (Rw1 & Rw2 & _ & _).
  rewrite ard_aview in Hvis |- *.
  apply (tail_vis_transport pa_segs B LAWS pa_img_range ar_rom lyc Sc W memc lyc S1 W (ms_mem ms0) _
    slo (spZ regs) Ea (p + Z.of_nat (length str)) a HAR3 Rw1 Rw2).
  - unfold slo. rewrite HK. clear -Hal16. lia.
  - clear -Hal16. lia.
  - intros q m Hq. rewrite Eab1. exact Hq.
  - intros c q Hq. rewrite Hfrs1. right. exact Hq.
  - intros c q. reflexivity.
  - exact K3.
  - unfold slo. rewrite HK in Hb. exact Hb.
  - unfold ar_tail_rng in Ha. exact Ha.
  - exact Hvis. }
split.
{ destruct HP as (kbs0 & tab0 & nm0 & Hanlk & Hwf & Hopen & Hop1 & Hcl1 & Hift & Hra & Hhv & Herrno & Hnm
    & Hbk & Hba & Htab & Hnmb & Hka & Hke & Hae & Hnmf & Hkf & Haf & Hkc & Hac).
  unfold ar_bufs_kept, ar_kind, ar_kn, ar_alias, ar_an, cx. cbn [ar_regs ar_W ar_memc].
  split; intros Hnz a Ha.
  - assert (Hkn : 1 <= aarg regs 2) by lia.
    destruct (Hkc Hnz Hkn) as (Hmr & _ & _). destruct (Hkf Hnz) as (Hfr & _).
    assert (Happ : a < kLowMemEnd \/ kHighMemBeg <= a) by (unfold amem_range in Hmr; lia).
    assert (Hw : ajw B G XO OUT STK sp0 FP ly S lyc Sc own a).
    { apply Hajw. exists (aivl (aarg regs 1) (aarg regs 2)). split; [right; left; reflexivity|].
      unfold aivl. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) Hnz). lia. }
    apply (ar_ajw_kept G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W (ms_mem ms0) slo (spZ regs)
      Ea a HGok HJ0 K3 Hw Happ).
    + unfold slo. unfold apart_frame in Hfr. rewrite HK in Hfr |- *. lia.
    + exact (ajw_not_side SK pa_segs B LAWS pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k 1 pos a
        HGok HJ0 ltac:(lia) Hposr Hnin1 Hw Happ).
    + pose proof (Hke Hnz) as Hap. unfold apart in Hap. lia.
  - assert (Han : 1 <= aarg regs 4) by lia.
    destruct (Hac Hnz Han) as (Hmr & _ & _). destruct (Haf Hnz) as (Hfr & _).
    assert (Happ : a < kLowMemEnd \/ kHighMemBeg <= a) by (unfold amem_range in Hmr; lia).
    assert (Hw : ajw B G XO OUT STK sp0 FP ly S lyc Sc own a).
    { apply Hajw. exists (aivl (aarg regs 3) (aarg regs 4)). split; [right; right; left; reflexivity|].
      unfold aivl. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) Hnz). lia. }
    apply (ar_ajw_kept G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W (ms_mem ms0) slo (spZ regs)
      Ea a HGok HJ0 K3 Hw Happ).
    + unfold slo. unfold apart_frame in Hfr. rewrite HK in Hfr |- *. lia.
    + exact (ajw_not_side SK pa_segs B LAWS pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k 1 pos a
        HGok HJ0 ltac:(lia) Hposr Hnin1 Hw Happ).
    + pose proof (Hae Hnz) as Hap. unfold apart in Hap. lia. }
split; [exact Hr3|]. split; [exact Hsv3|]. split; [exact Hrom3|]. split; [exact Hfr3|]. split; [exact Hfc3|].
split; [exact HJp|].
split; [exact Hfrs1|]. split; [exact Hnin1|]. split; [exact Hfs1|].
split; [rewrite Eab1; apply Permutation_refl|].
split; [exists S1, W, mem1, md1; split; [exact HAR1 | split; [exact Hfrs1 | exact Eab1]]|].
split; [intros c q; reflexivity|].
split; [rewrite F2, E3_60; reflexivity|].
split; [rewrite F9, E3_60; reflexivity|].
split; [rewrite F8, OLD3, OLD2, OLD1, E2 by lia; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
split; [rewrite F18, E3_44; reflexivity|].
split; [rewrite F26, E3_44; reflexivity|].
split; [rewrite F25;
        try rewrite (shadow_decl_ok E3v 44 32 62 F AR_SB E3_44 ltac:(lia) E3_32 E62);
        cbn [sv_denot]; rewrite E62, Z.add_0_r, Z_to_bv_bv_unsigned;
        unfold AR_SB, SHADOW_OFF; reflexivity|].
split; [rewrite F3, OLD3, OLD2, OLD1 by lia; exact E3|].
split; [rewrite F4, OLD3, OLD2, OLD1 by lia; exact E4|].
split; [rewrite F27, OLD3, OLD2, OLD1 by lia; exact E27|].
split.
{ replace (spZ regs - 8) with (spZ regs + -8) by lia.
  rewrite (ar_region_word _ _ _ _ 2%nat (spZ regs) (-8) 1%nat HRst eq_refl U3_2
    ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))).
  rewrite OLD3, OLD2, OLD1, E1 by lia. reflexivity. }
split.
{ intros j Hj.
  assert (Hj11 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9
                 \/ j = 10) by lia.
  destruct Hj11 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
  ar_save HRst U3_2 OLDA EREG. }
split.
{ rewrite (ar_region_word _ _ _ _ 44%nat F 120 61%nat HRF eq_refl U44
    ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))).
  rewrite E61, unsigned_lit_small by lia. reflexivity. }
split; [intros a Ha; exact (proj1 (HFpres3 a Ha))|].
split.
{ intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia).
  apply (proj1 (HFSpres3 (a - shadow_addr F) ltac:(unfold shadow_addr, AR_SB, SHADOW_OFF in *; lia))). }
split.
{ exact (akept_mono SK pa_segs B LAWS Hsegs lyc Sc W memc W (ms_mem ms0) slo (spZ regs) Ea _ K3
    (fun a H => or_intror H)). }
split; [exact (proj1 Hfd)|]. split; [exact (proj2 Hfd)|].
intros a Hro Ho He.
assert (Hia : in_img pa_segs a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | lia] | exact (RELRO_IMG a Hr)]).
rewrite (K3img a Hia Ho He (NSIDE a Hia)). exact (HROD a Hro Ho He).
Qed.

About ar_head.
Print Assumptions ar_head.
End b.
End a.
