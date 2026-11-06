(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v; 280 of its 357 lines of code are new or changed and 281 lines of the source are left out. *)
(* model_read on image A: the end of its walk, from the state at +0x208 (model_readDefs.v MR_AT208, where the four
   ways out join) to the Post: the frame retired (+0x208 magic, sixteen 0xf5 shadow bytes, the flag byte released at
   +0x260, LinkWalkSide.v aj_gx_flag_store_pi), the saved registers restored, `ret` (+0x2d4), then LinkWalkSide.v
   apost_side_gen.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs.
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

Lemma mr_text_of_attr_len : forall o cap, 1 <= cap -> Z.of_nat (length (text_of_attr o cap)) <= cap - 1.
Proof.
  intros o cap Hc. destruct o as [pay|]; cbn [text_of_attr]; [apply cut_text_len; exact Hc | cbn [length]; lia].
Qed.

(* the Post's body survives a step that keeps the bytes of the write set and their writability *)
Lemma mr_apost_move : forall (regs : bvmap 5 word) (m0 m1 m2 : word -> option byte) (regs' : bvmap 5 word),
  (forall a, inFP (model_read_awr regs m0) a ->
     mbyte pa_segs m2 a = mbyte pa_segs m1 a /\ (writable_at pa_segs m1 a -> writable_at pa_segs m2 a)) ->
  model_read_apost pa_segs regs m0 regs' m1 -> model_read_apost pa_segs regs m0 regs' m2.
Proof.
intros regs m0 m1 m2 regs' HW HP. unfold model_read_apost in *.
intros mbs kbs tab nm Hm Hk Ht Hn. specialize (HP mbs kbs tab nm Hm Hk Ht Hn).
set (RR := read_model tab nm (aarg regs 3) (aarg regs 5) (md_reqs mbs) (md_kstate mbs kbs)) in *.
destruct HP as (P1 & (mbs' & (Hab & Hlen) & P2) & P3 & P4 & P5 & P6).
assert (WIN : forall p n, In (p, p + n) (model_read_awr regs m0) -> forall a, p <= a < p + n ->
          mbyte pa_segs m2 a = mbyte pa_segs m1 a /\ (writable_at pa_segs m1 a -> writable_at pa_segs m2 a)).
{ intros p n Hin a Ha. apply HW. exists (p, p + n). split; [exact Hin | cbn [fst snd]; exact Ha]. }
assert (AB : forall p n bs, In (p, p + n) (model_read_awr regs m0) -> Z.of_nat (length bs) <= n ->
          abytes pa_segs m1 p bs -> abytes pa_segs m2 p bs).
{ intros p n bs Hin Hl (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
  intros i Hi. rewrite (proj1 (WIN p n Hin (p + Z.of_nat i) ltac:(lia))). exact (Q3 i Hi). }
assert (AU : forall p n bs, In (p, p + n) (model_read_awr regs m0) -> Z.of_nat (length bs) <= n ->
          au8arr pa_segs m1 p bs -> au8arr pa_segs m2 p bs).
{ intros p n bs Hin Hl (Q1 & Q2). split; [exact (AB p n bs Hin Hl Q1)|].
  intros i Hi. apply (proj2 (WIN p n Hin (p + i) ltac:(lia))). exact (Q2 i Hi). }
assert (IN0 : In (aarg regs 0, aarg regs 0 + MD_SIZE) (model_read_awr regs m0)) by (left; reflexivity).
assert (IN2 : aarg regs 2 <> 0 -> In (aarg regs 2, aarg regs 2 + aarg regs 3) (model_read_awr regs m0)).
{ intros H. right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. }
assert (IN4 : aarg regs 4 <> 0 -> In (aarg regs 4, aarg regs 4 + aarg regs 5) (model_read_awr regs m0)).
{ intros H. right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. }
refine (conj P1 (conj _ (conj _ (conj _ (conj _ _))))).
- exists mbs'. refine (conj (conj _ Hlen) P2). exact (AU _ _ mbs' IN0 ltac:(lia) Hab).
- intros H2 H3. destruct (P3 H2 H3) as (Q1 & Q2). split; [|exact Q2].
  apply (AB _ _ _ (IN2 H2)); [|exact Q1].
  assert (L : Z.of_nat (length (r_kind RR)) <= aarg regs 3 - 1).
  { unfold RR, read_model, read_core. cbv beta zeta. cbn [r_kind].
    destruct nm as [s|]; cbn [r_kind]; [|cbn [length]; lia].
    destruct (Nat.eqb (length s) 0); cbn [r_kind]; [cbn [length]; lia|].
    destruct (index_of tab s =? 0); cbn [r_kind]; [cbn [length]; lia|].
    destruct (aarg regs 3 <? 1) eqn:Ec; [cbn [length]; lia|].
    apply mr_text_of_attr_len. lia. }
  rewrite length_app. cbn [length]. lia.
- intros H2 H3. destruct (P4 H2 H3) as (Q1 & Q2). split; [|exact Q2].
  apply (AB _ _ _ (IN4 H2)); [|exact Q1].
  assert (L : Z.of_nat (length (r_alias RR)) <= aarg regs 5 - 1).
  { unfold RR, read_model, read_core. cbv beta zeta. cbn [r_alias].
    destruct nm as [s|]; cbn [r_alias]; [|cbn [length]; lia].
    destruct (Nat.eqb (length s) 0); cbn [r_alias]; [cbn [length]; lia|].
    destruct (index_of tab s =? 0); cbn [r_alias]; [cbn [length]; lia|].
    destruct (aarg regs 5 <? 1) eqn:Ec; [cbn [length]; lia|].
    apply mr_text_of_attr_len. lia. }
  rewrite length_app. cbn [length]. lia.
- intros H2 H3. destruct (P5 H2 H3) as (junk & Hl & Hj). exists junk. split; [exact Hl|].
  exact (AU _ _ junk (IN2 H2) ltac:(lia) Hj).
- intros H2 H3. destruct (P6 H2 H3) as (junk & Hl & Hj). exists junk. split; [exact Hl|].
  exact (AU _ _ junk (IN4 H2) ltac:(lia) Hj).
Qed.

Lemma mr_exit : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    E ms md2 ly2 S2 W2 k2 pos rcv,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  MR_AT208 SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2 W2 k2 pos rcv ->
  SRr pa_segs W2 (mkCfg ms md2) (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2 W2 k2 pos rcv
  (HPRE & HRD & HP)
  (HEI & HAE & E32 & E44 & E60 & E61 & E62 & HS & HJ2 & Hk2 & Hfs2 & Hperm2 & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1)
   & Hnin & HK & Hfd & Hfs & R10 & HQ).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK8 : MODEL_READ_AK = 8416) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(lia) Hwhi) as (memS & HJi & HSTK & HXO & Hpresw & Hceil47).
destruct Hceil47 as (Hceil & H47).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ2) as (FA2 & FL2).
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ) as (FA1 & FL1).
assert (FA : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by congruence.
assert (FLA : flag_addr ly2 1 pos = flag_addr lyc 1 pos) by congruence.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frame_al64 pa_segs B lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HFa64 & HFb64 & HFb).
destruct (frames_bounds pa_segs B LAWS lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
destruct (al_flag _ _ LAWS lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HFLpres & HFLown & HFLapp & HFLc).
set (F := frame_addr lyc 1 pos) in *.
set (FL := flag_addr lyc 1 pos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp2, HFLapp.
assert (HFL64 : 0 <= FL < 2 ^ 64)
  by (destruct HFLapp as (Hq1 & _); revert Hq1 HFLc C1a C1b; clear; intros; lia).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U44 : bv_unsigned (ew E 44) = F) by (rewrite E44; apply unsigned_lit_small; lia).
assert (U61 : bv_unsigned (ew E 61) = FL) by (rewrite E61; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E 62) = MR_SB + F / 8) by (rewrite E62; apply unsigned_lit_small; unfold MR_SB; lia).
set (EWr := fun a => inFP (model_read_awr regs (rdW W memc)) a).
(* ---- +0x208 .. +0x2d4: the frame retired, the flag byte released, the saved registers restored ---- *)
pose (RUNF := paj_flag_plain_x SK B LAWS G HGok XO OUT).
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let r := eval vm_compute in (sym_runN_pi link_tpi FUEL ss) in
  lazymatch r with (?ss', ?st) =>
    assert (Hrun : sym_runN_pi link_tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
    eapply (RUNF W2 FUEL E ss ss' st ms STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 k2 1 pos _ HEI HS Hrun I HJ2
      ltac:(lia)); clear Hrun
  end
end.
- (* the run's stores: the flag byte, the frame and its shadow (own frame), the machine frame (the window) *)
  intros a (r & Hin & Hr). cbn [mr_ss208 ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [mr_flag fshadow_region fframe_region mr_stk104 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  + right; right; right. rewrite FLA. rewrite U61 in Hr. fold FL. lia.
  + left. apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) ly2 S2 W2 (ms_mem ms) md2 k2 1 pos a HJ2 ltac:(left; reflexivity)).
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite FA. fold F. change (fs_frame_bytes 1 / 8) with 16.
    change (fs_frame_bytes 1 / 8) with 16 in Hr. rewrite U62 in Hr. unfold MR_SB, SHADOW_OFF in *. lia.
  + left. apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) ly2 S2 W2 (ms_mem ms) md2 k2 1 pos a HJ2 ltac:(left; reflexivity)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA. fold F. change (fs_frame_bytes 1) with 128.
    change (fs_frame_bytes 1) with 128 in Hr. rewrite U44 in Hr. lia.
  + left. rewrite Usp in Hr. split; [left; lia | lia].
- (* the flag byte the run leaves *)
  intros msr HSr. rewrite FLA. fold FL.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HSr eq_refl) as HR0.
  destruct HR0 as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC. rewrite U61 in HC.
  inversion HC as [|c cs Hc0 _]; subst. destruct (Hc0 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off] in Hb2. rewrite !Z.add_0_r in Hb2. rewrite Hb2. f_equal.
  cbn [YP09.c_val cbyte] in Hb1. injection Hb1 as <-. vm_compute. reflexivity.
- (* the ret, and the Post *)
  intros ms' mat' HS' HJ' HF HFr HG. cbn [ms_mem mkst] in HF, HFr, HG, HJ'.
  prreg HS' (1%bv : bv 5) R1'. prreg HS' (10%bv : bv 5) R10'. prreg HS (10%bv : bv 5) R10s.
  assert (A10 : getr (ms_regs ms') 10 = w64 rcv) by (rewrite R10', <- R10s; exact R10).
  pose proof (aregs_preserved_of_st_ok pa_segs (w_H W2) E _ _ regs MR_extra HS' HAE ltac:(vm_compute; reflexivity))
    as HPr.
  assert (Hsk : alloc_ceiling <= spZ regs - MODEL_READ_AK) by lia.
  pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _
    (fun a => aside_rng lyc 1 pos a \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U61, ?U44, ?U62, ?Usp in Hrr;
                   cbv beta; unfold aside_rng, in_zr, frame_rng, shadow_addr; cbn [fst snd]; fold F FL;
                   change (fs_frame_bytes 1) with 128; change (128 / 8) with 16;
                   unfold MR_SB, SHADOW_OFF in *; lia |]);
          destruct Hin)) as UN.
  pose proof (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W2 (ms_mem ms) W2 (ms_mem ms')
    (spZ regs - MODEL_READ_AK) (spZ regs) _ _
    (fun a => aside_rng lyc 1 pos a \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HAR Hsk ltac:(lia) HK UN
    (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => H)
    ltac:(intros a Ha; cbv beta in Ha |- *; destruct Ha as [Ha | Ha]; [left; right; exact Ha | right; exact Ha]))
    as HK'.
  destruct HAR1 as [M1 HAR1r]. pose proof (conj M1 HAR1r) as HAR1.
  destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Hc1 & Hp1 & _).
  assert (HWR : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
    mbyte pa_segs (rdW W2 (ms_mem ms')) a = mbyte pa_segs (rdW W2 (ms_mem ms)) a /\
    (writable_at pa_segs (rdW W2 (ms_mem ms)) a -> writable_at pa_segs (rdW W2 (ms_mem ms')) a)).
  { intros a Ha.
    destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
      (conj (conj HJ (conj HGok (conj HROD (conj Hraw (conj Hra4 (conj Hgp (conj Htp (conj Hal16 (conj Hwlo
        (conj Hwhi (conj Hev (conj Hside (conj Hajw Hnro))))))))))))) (conj HRD HP)) a Ha)
      as (Happ & Hwin & _ & Hajwa & Ha64).
    assert (NS : ~ aside_rng lyc 1 pos a)
      by exact (ajw_not_side SK pa_segs B LAWS pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
        1 pos a HGok HJ ltac:(lia) Hp1 Hnin Hajwa Happ).
    split.
    - apply (mbyte_of_aview pa_segs). apply UN; [exact Ha64|]. cbv beta. intros [H | H]; [exact (NS H) | exact (Hwin H)].
    - intros Hw. apply (writable_kept (segs := pa_segs) (w_H W2) (ms_mem ms) (ms_mem ms') a);
        [intros Hp; exact (apresent_grows _ _ _ _ HG Hp) | exact Hw]. }
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W2 _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat2.
  unfold YK0s.ret_ok in Hraw.
  rewrite R1'. rewrite ?E1. rewrite ?Hraw.
  unfold MR_POST.
  eapply (apost_side_gen SK pa_segs B LAWS Hsegs MODEL_READ_AK 0 EWr G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc
    W memc mdc k regs (ms_regs ms') ly2 (stack_free_state 1 pos S2) W2 (ms_mem ms') _ k2 1 pos S1 W1 mem1 md1 _ HJ).
  + apply (ajournal_gx_materialize pa_segs B LAWS Hsegs). exact HJ'.
  + lia.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
  + exact HPr.
  + exact HAR1.
  + exact Hfrs1.
  + exact Eab1.
  + exact HK'.
  + cbv beta. split; [|split].
    * exact (set_fs_trans S2 (stack_free_state 1 pos S2) Sc (set_fs_of_exists S2 Sc Hfs2)
        (stack_free_state_set_fs 1 pos S2)).
    * assert (EB : ablocks B ly2 (stack_free_state 1 pos S2) = ablocks B ly2 S2)
        by (rewrite (stack_free_state_set_fs 1 pos S2) at 1; apply ablocks_set_fs).
      rewrite EB. exact Hperm2.
    * exact (mr_apost_move regs (rdW W memc) (rdW W2 (ms_mem ms)) (rdW W2 (ms_mem ms')) (ms_regs ms') HWR
        (HQ (ms_regs ms') A10)).
Qed.

(* the exit from the state with the frame's regions set aside (model_readDefs.v mr_ss208d): the journal still holds
   the frame (its bytes, shadow and flag present), the frame's flag word is still at F + 120 *)
Lemma mr_exit_d : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    E ms md2 ly2 S2 W2 k2 pos rcv,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  img_env pa_val A_LIM E -> env_agree 32 (Ereg regs MR_extra) E ->
  ew E 32 = Z_to_bv 64 MR_SB -> ew E 44 = Z_to_bv 64 (frame_addr lyc 1 pos) ->
  ew E 60 = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) -> ew E 61 = Z_to_bv 64 (flag_addr lyc 1 pos) ->
  ew E 62 = Z_to_bv 64 (MR_SB + frame_addr lyc 1 pos / 8) ->
  st_ok_pi pa_segs pa_val E mr_ss208d (restrict (w_H W2) ms) ->
  val_mem pa_segs (rdW W2 (ms_mem ms)) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos) ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 (ms_mem ms) md2 k2 ->
  k2 <= k -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (exists S1 W1 mem1 md1, AR pa_segs B lyc S1 W1 mem1 md1 /\ frames S1 = (1, pos) :: frames Sc /\
     ablocks B lyc S1 = ablocks B lyc Sc) -> ~ In (1, pos) (frames Sc) ->
  akept pa_segs B lyc Sc W memc W2 (ms_mem ms) (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => inFP (model_read_awr regs (rdW W memc)) a \/ aside_rng lyc 1 pos a) ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  getr (ms_regs ms) 10 = w64 rcv -> MR_QM regs W memc rcv (rdW W2 (ms_mem ms)) ->
  SRr pa_segs W2 (mkCfg ms md2) (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2 W2 k2 pos rcv
  HENT HEI HAE E32 E44 E60 E61 E62 HS VFL HJ2 Hk2 Hfs2 Hperm2 HS1 Hnin HK Hfd Hfs R10 HQ.
pose proof HENT as (HPRE & _ & _).
destruct HPRE as (HJ & HGok & _).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct HS1 as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ2) as (FA2 & FL2).
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ) as (FA1 & FL1).
assert (FA : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by congruence.
assert (FLA : flag_addr ly2 1 pos = flag_addr lyc 1 pos) by congruence.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frame_al64 pa_segs B lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HFa64 & HFb64 & HFb).
destruct (frames_bounds pa_segs B LAWS lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
destruct (al_flag _ _ LAWS lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HFLpres & HFLown & HFLapp & HFLc).
(* the frame at the current state: the journal's frames are own ++ the caller's *)
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 (ms_mem ms)
  md2 k2 HJ2) as HAR2.
assert (Hin2 : In (1, pos) (frames S2)).
{ pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
  pose proof HJ2i as (_ & _ & _ & _ & _ & HFR & _). rewrite HFR. left. reflexivity. }
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md2 1 pos HAR2 Hin2) as (_ & _ & HFpres2 & HFSpres2).
destruct (al_flag _ _ LAWS ly2 S2 W2 (ms_mem ms) md2 1 pos HAR2 Hin2) as (HFLpres2 & _ & _ & _).
rewrite FA in HFpres2, HFSpres2. rewrite FLA in HFLpres2.
assert (HFLF : flag_addr lyc 1 pos + 1 <= frame_addr lyc 1 pos).
{ pose proof HAR1 as [M1 _].
  destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Cc & Cp & _ & _ & _ & P1 & P2 & _ & _ & _ & P3).
  unfold flag_addr, frame_addr. lia. }
set (F := frame_addr lyc 1 pos) in *.
set (FL := flag_addr lyc 1 pos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp2, HFLapp.
assert (HFL64 : 0 <= FL < 2 ^ 64)
  by (destruct HFLapp as (Hq1 & _); revert Hq1 HFLc C1a C1b; clear; intros; lia).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8al : (MR_SB + F / 8) mod 8 = 0).
{ unfold MR_SB. destruct (div8_of_mul64 F HFa64) as [E8 _]. rewrite E8.
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
assert (U44 : bv_unsigned (ew E 44) = F) by (rewrite E44; apply unsigned_lit_small; lia).
assert (U61 : bv_unsigned (ew E 61) = FL) by (rewrite E61; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E 62) = MR_SB + F / 8) by (rewrite E62; apply unsigned_lit_small; unfold MR_SB; lia).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof HENT as (HPRE & _).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _).
assert (HK8 : MODEL_READ_AK = 8416) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(lia) Hwhi) as (memS & HJi & HSTK & HXO & Hpresw & Hceil47).
destruct Hceil47 as (Hceil & H47).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (U60 : bv_unsigned (ew E 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lia).
assert (HdFS : F + 128 <= MR_SB + F / 8 \/ MR_SB + F / 8 + 16 <= F).
{ assert (HSBv : MR_SB = 2147450880) by reflexivity.
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)). pose proof (Z_div_mod_eq_full F 8).
  destruct HFapp2 as (Hf4x & [Hlowx | (Hhighx & Hhcx)]).
  - left. clear - Hf4x Hlowx HSBv HF8m H H0. lia.
  - right. clear - Hf4x Hhighx HSBv HF8m H H0. lia. }
(* the flag's fact and the three regions *)
add_fact HS 61%nat (mkAF 4096 (2 ^ 47) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U61; rewrite Z.pow_0_r, Z.mod_1_r;
        destruct HFLapp as (Hq1 & Hq2); repeat split; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply (HFpres2 (F + o)); unfold in_zr, frame_rng; cbn [fst snd];
          fold F; change (fs_frame_bytes 1) with 128; lia
        | apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val pa_segs _ _ F 120 8 _ FL);
          [ cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VFL ] ])
  ltac:(mr_disj; rewrite ?U60, ?U44, ?Usp; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 1 0 16 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold MR_SB; lia|];
        split; [unfold MR_SB; lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs);
        replace (MR_SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, MR_SB, SHADOW_OFF; lia);
        apply (HFSpres2 o ltac:(change (128 / 8) with 16; lia)))
  ltac:(mr_disj; rewrite ?U60, ?U44, ?U62, ?Usp; unfold MR_SB in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ mr_flag HS eq_refl
  ltac:(unfold region_ok, mr_flag;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U61; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; replace (FL + o) with FL by lia; apply (apresent_writable pa_segs); exact HFLpres2)
  ltac:(mr_disj; unfold mr_flag; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U60, ?U44, ?U62, ?U61, ?Usp; unfold MR_SB in *; destruct HFLapp as (Hq1 & Hq2);
        pose proof (proj1 alloc_ceiling_val) as HCE; unfold kLowMemEnd in *;
        repeat split; first [lia | match goal with |- ?g => idtac "DISJGOAL" g; fail end])) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
pose proof (mr_st_ok_pi_merge _ mr_ss208 _ _ HS ltac:(vm_compute; reflexivity)) as HS208.
exact (mr_exit rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2 W2 k2 pos rcv
  HENT (conj HEI (conj HAE (conj E32 (conj E44 (conj E60 (conj E61 (conj E62 (conj HS208 (conj HJ2 (conj Hk2
    (conj Hfs2 (conj Hperm2 (conj (ex_intro _ S1 (ex_intro _ W1 (ex_intro _ mem1 (ex_intro _ md1
      (conj HAR1 (conj Hfrs1 Eab1)))))) (conj Hnin (conj HK (conj Hfd (conj Hfs (conj R10 HQ))))))))))))))))))).
Qed.

End b.
End a.
