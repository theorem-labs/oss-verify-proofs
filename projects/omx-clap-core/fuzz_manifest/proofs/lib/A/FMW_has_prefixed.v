(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v; 369 of its 428 lines of code are new or changed and 872 lines of the source are left out. *)
(* has_prefixed 0x82130..0x822c4 (lv2_locate.c:55-76) in fm.asan: FMH_Fn.has_prefixed_spec under the runtime
   contracts of strlen, strstr, strncmp and isalnum (FMH_Rt), with name_char_holds (FMW_name_char.v). The loop
   (hp_loop) is an induction over the five loop segments of FMW_hp_kit.v (proved in FMW_hp_seg{H,N,P,Q,T}.v); its
   invariant is fm's plain proof's (lib/Prog/has_prefixed.v hp_loop :146), INV in FMW_hp_model.v.
   The three `jal __asan_report_load1` sites (0x82278, 0x822bc, 0x822c0; 0x822c0 is the function's last insn and
   falls through into name_char only if the report returned) are all REFUTED on this agreement side: each checked
   byte is a byte of the text or its NUL, addressable by cstr_ok, so the token engine takes the check's fall-through
   (segment files). has_prefixed holds no halt case. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt FMW_name_char FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
FMW_hp_segH FMW_hp_segN FMW_hp_segP FMW_hp_segQ FMW_hp_segT.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma hp_pre_len : forall cx, hp_entry_ok B cx -> length (cx_pre cx) = Z.to_nat (cx_plen cx).
Proof.
intros cx (_ & _ & _ & _ & _ & _ & _ & _ & Hq & Hp & Hqp & _). unfold cx_pre.
rewrite length_firstn, length_skipn. lia.
Qed.

(* the loop: from the loop head at an occurrence a with INV a, the walk reaches has_prefixed's post *)
Lemma hp_loop : seg_head_ok B -> seg_ncmp_ok B -> seg_pre_ok B -> seg_post_ok B -> seg_tail_ok B ->
  forall n cx a, (length (cx_tb cx) - a < n)%nat -> INV (cx_tb cx) (cx_pre cx) (cx_lb cx) a ->
  hp_cont B cx HP_HEAD a (fun _ => True).
Proof.
intros SH SN SP SO ST n. induction n as [|n IH]; intros cx a Hn INV0; [lia|].
set (P := Z.to_nat (cx_plen cx)).
(* every way into the tail at a carries INV (S a) *)
assert (TAIL : INV (cx_tb cx) (cx_pre cx) (cx_lb cx) (S a) -> hp_cont B cx HP_TAIL a (fun _ => True)).
{ intros INV1. apply (ST cx a).
  - intros Hno. unfold hp_res.
    rewrite (tok_none (cx_tb cx) (cx_pre cx) (cx_lb cx) (S a) INV1 (noocc_mt (cx_tb cx) (cx_lb cx) (S a) Hno)).
    reflexivity.
  - intros j Hfo lyc Sc W regs m mdc Hst _.
    pose proof Hst as (HE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
    pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & _).
    pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
    assert (Hlb1 : (1 <= length (cx_lb cx))%nat) by (destruct (cx_lb cx); [contradiction | cbn; lia]).
    exact (IH cx (S a + j)%nat ltac:(lia) (first_occ_inv _ _ _ (S a) j INV1 Hfo) lyc Sc W regs m mdc Hst I). }
(* the facts every continuation below re-derives from its state *)
assert (ENT : forall a' lyc Sc W regs m mdc, hp_st B cx a' lyc Sc W regs m mdc ->
  length (cx_pre cx) = P /\ (Z.to_nat (cx_q cx) + P <= length (cx_tb cx))%nat /\
  cx_pre cx = firstn P (skipn (Z.to_nat (cx_q cx)) (cx_tb cx))).
{ intros a' lyc Sc W regs m mdc (HE & _). split; [exact (hp_pre_len cx HE)|].
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & Hp & Hqp & _). split; [unfold P; lia | reflexivity]. }
apply (SH cx a).
- (* a < plen + 1, or at[-1] <> ':' *)
  intros lyc Sc W regs m mdc Hst Hr. refine (TAIL _ _ _ _ _ _ _ Hst I).
  destruct (ENT _ _ _ _ _ _ _ Hst) as (HL & _).
  apply (inv_step1 _ _ _ _ HL a INV0). intros Ha.
  destruct Hr as [Hr | Hr]; [unfold P in Ha; lia | exact (tok_colon _ _ _ _ HL a Ha Hr)].
- intros lyc Sc W regs m mdc Hst (H69 & H58).
  pose proof Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
  pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
  pose proof H69 as (HPa & _).
  refine (SN cx a _ _ lyc Sc W regs m mdc Hst H69).
  + (* the prefix differs *)
    intros lyc2 Sc2 W2 regs2 m2 mdc2 Hst2 Hne. refine (TAIL _ _ _ _ _ _ _ Hst2 I).
    destruct (ENT _ _ _ _ _ _ _ Hst2) as (HL & Hq & Hpre).
    apply (inv_step1 _ _ _ _ HL a INV0). intros Ha.
    apply (tok_prefix _ _ _ _ HL a (Z.to_nat (cx_q cx)) Hpre Hq); [lia | exact Ha | exact Hne].
  + intros lyc2 Sc2 W2 regs2 m2 mdc2 Hst2 (H69' & Heq).
    refine (SP cx a _ _ lyc2 Sc2 W2 regs2 m2 mdc2 Hst2 H69').
    * (* the byte before start is '.' or a name character *)
      intros lyc3 Sc3 W3 regs3 m3 mdc3 Hst3 (Hpos & Hb). refine (TAIL _ _ _ _ _ _ _ Hst3 I).
      destruct (ENT _ _ _ _ _ _ _ Hst3) as (HL & _).
      apply (inv_step1 _ _ _ _ HL a INV0). intros Ha.
      exact (tok_before _ _ _ _ a Hpos Hb).
    * intros lyc3 Sc3 W3 regs3 m3 mdc3 Hst3 Hbefore.
      destruct (ENT _ _ _ _ _ _ _ Hst3) as (HL & Hq & Hpre).
      refine (SO cx a _ _ lyc3 Sc3 W3 regs3 m3 mdc3 Hst3 I).
      -- (* every check passed: the answer is 1 *)
         intros Hnc. unfold hp_res.
         rewrite (tok_hit _ _ _ _ HL a (Z.to_nat (cx_q cx)) Hpre Hq HPa Hmt H58 Heq Hbefore Hnc). reflexivity.
      -- (* the byte after the location is a name character *)
         intros lyc4 Sc4 W4 regs4 m4 mdc4 Hst4 Hnc. refine (TAIL _ _ _ _ _ _ _ Hst4 I).
         apply (inv_step1 _ _ _ _ HL a INV0). intros Ha.
         exact (tok_after _ _ _ _ HL a Ha Hnc).
Qed.
End h.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis AISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis ASTRSTR : astrstr_realizes tfibsegs B PC_strstr.

(* the entry state: sp, the shadow base cell and its GOT slot *)
Lemma hp_entry : forall ly S W regs mem md ch,
  afn_pre tfibsegs B STK_has_prefixed ly S W regs mem md ch ->
  st_ok tfibsegs (Ereg regs [w64 SBz]) ss_hp
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_has_prefixed) mem (seg_rom tfibsegs))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
ceil2.
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
assert (E2 : ew (Ereg regs [w64 SBz]) 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E32 : ew (Ereg regs [w64 SBz]) 32 = w64 SBz) by exact (ew_Ereg_extra regs _ 0).
assert (Usp : bv_unsigned (ew (Ereg regs [w64 SBz]) 2) = spZ regs) by (rewrite E2; reflexivity).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (tl_got_shadow B TL), (tl_shadow_cell B TL) in Kgot. rewrite (tl_shadow_cell B TL) in Kcell.
rewrite restrict_mkst_fx. unfold ss_hp. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold hp_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (region_ok_stack tfibsegs (Ereg regs [w64 SBz]) _ 2 (spZ regs) (-112)); [exact Usp | lia | lia |].
    intros a Ha. apply (apresent_writable tfibsegs). apply Hpres. rewrite FFS. lia.
  + unfold hp_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold A_GOT_shadow; lia|]. split; [unfold A_GOT_shadow; lia|].
    split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ 0 A_GOT_shadow 8 (SLit A_shadow_glob) A_shadow_glob);
      [reflexivity | unfold A_shadow_glob; cbn; lia | cbn; lia |].
    cbn [Z.add]. exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot).
  + unfold hp_cell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold A_shadow_glob; lia|]. split; [unfold A_shadow_glob; lia|].
    split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ 0 A_shadow_glob 8 (SOff 32 0) SBz);
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SBz; cbn; lia | cbn; lia |].
    cbn [Z.add]. unfold SBz. exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold hp_regions, hp_got_region, hp_cell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_GOT_shadow, A_shadow_glob. repeat split; lia.
- split; [|split; exact I]. cbn [hp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E32. change (2 ^ 4) with 16. unfold w64, SBz. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. unfold spZ in *. repeat split; lia.
Qed.

(* a 64-bit word of the entry state's frame region (region 0, based at the entry sp = atom 2) *)
Lemma hp_frame_word : forall E ss ms (H : word -> bool) r off (n : nat) regs0 (rr : bv 5),
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some r -> YP09.r_base r = Some 2%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks r) ->
  bv_unsigned (ew E 2) = spZ regs0 -> ew E n = getr regs0 rr ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (spZ regs0 + off) 8 (bv_unsigned (getr regs0 rr)).
Proof.
intros E ss ms H r off n regs0 rr HS Hi Hb Hin Hsp Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hok & _).
pose proof (proj1 (Forall_forall _ _) Hok r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hc).
pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as Hck.
assert (Hd : sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs0 rr))).
{ cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
pose proof (bv_unsigned_in_range 64 (getr regs0 rr)) as R. unfold bv_modulus in R.
pose proof (val_of_chunk_ok tfibsegs E _ _ off 8 (SOff n 0) (bv_unsigned (getr regs0 rr)) Hck Hd
  ltac:(cbn; lia) ltac:(cbn; lia)) as V.
rewrite Hb in V. cbn [base_val] in V. rewrite Hsp in V. exact V.
Qed.
Ltac hp_in_chunks := cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]).

(* has_prefixed from the five loop segments *)
Lemma has_prefixed_of_segs : seg_head_ok B -> seg_ncmp_ok B -> seg_pre_ok B -> seg_post_ok B -> seg_tail_ok B ->
  has_prefixed_spec tfibsegs B.
Proof.
intros SH SN SP SO ST.
unfold has_prefixed_spec, fpre, fpost.
intros ly S W regs mem md ch t q plen lp tb lb live peak cnt fail (HPRE & HRO) Hglob
  H10 H11 H12 H13 Ht Hl Hkt Hkl Hlb Hq Hplen Hqp Htmax.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (ajournal_init tfibsegs B STK_has_prefixed [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
ceil2.
pose proof (hp_entry ly S W regs mem md ch HPRE) as HS.
assert (E1 : ew (Ereg regs [w64 SBz]) 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
assert (E2 : ew (Ereg regs [w64 SBz]) 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E3 : ew (Ereg regs [w64 SBz]) 3 = getr regs 3) by exact (ew_Ereg_nat regs _ 3 3%bv eq_refl).
assert (E4 : ew (Ereg regs [w64 SBz]) 4 = getr regs 4) by exact (ew_Ereg_nat regs _ 4 4%bv eq_refl).
assert (E10 : ew (Ereg regs [w64 SBz]) 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
assert (E13 : ew (Ereg regs [w64 SBz]) 13 = getr regs 13) by exact (ew_Ereg_nat regs _ 13 13%bv eq_refl).
assert (E32 : ew (Ereg regs [w64 SBz]) 32 = w64 SBz) by exact (ew_Ereg_extra regs _ 0).
assert (Usp : bv_unsigned (ew (Ereg regs [w64 SBz]) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HCL : alloc_ceiling <= spZ regs - STK_has_prefixed) by (rewrite FFS; lia).
assert (SHOK : sh_ok tfibsegs hp_Bx [] (Ereg regs [w64 SBz]) (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at. change (w64 A_has_prefixed) with (Z_to_bv 64 A_has_prefixed).
(* 0x82130..0x82188: frame, shadow base from the GOT, arguments, call strlen(local) *)
aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
{ awr_ok_tac. exact Usp. }
pose proof (gframe_of_frame tfibsegs W (Ereg regs [w64 SBz]) _ 2 (-112) 0 (spZ regs)
  (spZ regs - STK_has_prefixed) (spZ regs) mem (ms_mem ms) HFr ltac:(vm_compute; reflexivity) Usp
  ltac:(rewrite FFS; lia) ltac:(lia)) as G1.
clear HF HFr HG.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -112).
{ unfold spZ at 1. rewrite R2, E2. fold (spZ regs). apply unsigned_lit_small. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs [w64 SBz]) _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (aj_rt_ro tfibsegs B LAWS Hsegs STK_RT_STR PC_strlen (fun v => v = Z.of_nat (length lb))
    W (ms_regs ms) (ms_mem ms) STK_has_prefixed (spZ regs) [] ly S W mem md [] ly S _ 0 (-112)
    (Z_to_bv 64 0x8218c) HJ).
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold STK_RT_STR, ESTACK; lia.
  - rewrite FFS; unfold STK_RT_STR, ESTACK; lia.
  - rewrite R3, E3; exact Hgp.
  - rewrite R4, E4; exact Htp.
  - exact R1.
  - apply g2_ret_ok_lit; [lia | reflexivity].
  - intros HPK.
    assert (HRO1 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms))).
    { apply (arodata_journal tfibsegs B FM_RLO FM_RHI STK_has_prefixed (spZ regs) [] ly S W mem md []
        ly S W (ms_mem ms) _ 0 HJ (fun a => fp_spares_closed [] a sink_closed_nil) inFP_nil g2_relro_img HRO). }
    destruct (IMGF ly S W (ms_mem ms) _ (proj1 HJ) HRO1) as (HROM & _).
    apply (ASTRLEN ly S W (ms_regs ms) (ms_mem ms) _ lp lb HPK HROM).
    + rewrite R10, E13. exact H13.
    + apply (cstr_ok_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [exact G1 | exact HCL | exact Hl]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v4 & -> & HJ2 & HP2 & Ha0 & Hv4 & HRv4 & G2 & Hpres2).
jafter_call_keep HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G2; unfold STK_RT_STR, ESTACK in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite Usp. intros a Ha _.
      apply (apresent_writable tfibsegs). apply Hpr2. rewrite FFS. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G2; unfold STK_RT_STR, ESTACK, A_GOT_shadow in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G2; unfold STK_RT_STR, ESTACK, A_shadow_glob in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia. }
clear HS. rename HS2 into HS. rewrite <- restrict_mkst_fx in HS.
set (Eh := havoc (Ereg regs [w64 SBz]) 33 (map (getr regs2) CLOB)) in HS.
assert (F2 : bv_unsigned (ew Eh 2) = spZ regs) by (unfold Eh; rewrite YN3v.ew_havoc_old by lia; exact Usp).
clear SHOK.
assert (SHOK : sh_ok tfibsegs hp_Bx [] Eh (mrestrict (w_H W) mem2)) by apply Forall_nil.
(* 0x8218c..0x82198: s4 = strlen(local), call strstr(text, local) *)
aj_run_tok tbl_hp_ok HS HJ2 SHOK hp_Bspan.
{ awr_ok_tac. exact F2. }
pose proof (gframe_of_frame tfibsegs W Eh _ 2 (-112) 0 (spZ regs)
  (spZ regs - STK_has_prefixed) (spZ regs) mem2 (ms_mem ms0) HFr ltac:(vm_compute; reflexivity) F2
  ltac:(rewrite FFS; lia) ltac:(lia)) as G3.
clear HF HFr HG.
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11.
assert (Hsp2 : spZ (ms_regs ms0) = spZ regs + -112).
{ unfold spZ at 1. rewrite Q2. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E2.
  fold (spZ regs). apply unsigned_lit_small. lia. }
assert (GT : gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem (ms_mem ms0)).
{ apply (gframe_seq tfibsegs W _ _ mem mem2); [|exact G3].
  apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms)); [exact G1|].
  apply (gframe_widen tfibsegs W _ _ (spZ regs + -112 - STK_RT_STR) (spZ regs + -112));
    [exact G2 | |]; unfold STK_has_prefixed, STK_RT_STR, STK_RT_STRSTR, STK_name_char, STK_RT_ISALNUM, ESTACK; lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Eh _ ms0 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (aj_rt_ro tfibsegs B LAWS Hsegs STK_RT_STRSTR PC_strstr
    (fun v => (v = 0 /\ no_occ tb lb) \/ (exists j, first_occ tb lb j /\ v = t + Z.of_nat j))
    W (ms_regs ms0) (ms_mem ms0) STK_has_prefixed (spZ regs) [] ly S W mem md [] ly S _ 0 (-112)
    (Z_to_bv 64 0x8219c) HJ2).
  - exact Hsp2.
  - reflexivity.
  - lia.
  - unfold STK_RT_STRSTR, ESTACK; lia.
  - rewrite FFS; unfold STK_RT_STRSTR, ESTACK; lia.
  - rewrite Q3. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E3. exact Hgp.
  - rewrite Q4. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E4. exact Htp.
  - exact Q1.
  - apply g2_ret_ok_lit; [lia | reflexivity].
  - intros HPK.
    assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms0))).
    { apply (arodata_journal tfibsegs B FM_RLO FM_RHI STK_has_prefixed (spZ regs) [] ly S W mem md []
        ly S W (ms_mem ms0) _ 0 HJ2 (fun a => fp_spares_closed [] a sink_closed_nil) inFP_nil g2_relro_img HRO). }
    destruct (IMGF ly S W (ms_mem ms0) _ (proj1 HJ2) HRO2) as (HROM & HROO & _).
    apply (hp_strstr_ro B ASTRSTR ly S W (ms_regs ms0) (ms_mem ms0) _ t lp tb lb HPK HROM HROO).
    + rewrite Q10. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E10. exact H10.
    + rewrite Q11. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E13. exact H13.
    + apply (cstr_ok_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [exact GT | exact HCL | exact Ht].
    + apply (cstr_ok_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [exact GT | exact HCL | exact Hl]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v5 & -> & HJ3 & HP3 & Hb0 & Hv5 & HRv5 & G4 & Hpres3).
jafter_call_keep HS 49%nat regs3 (mrestrict (w_H W) mem3) HP3 [0;1;2]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr3 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F2. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G4; unfold STK_RT_STRSTR, ESTACK in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite F2. intros a Ha _.
      apply (apresent_writable tfibsegs). apply Hpr3. rewrite FFS. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G4; unfold STK_RT_STRSTR, ESTACK, A_GOT_shadow in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G4; unfold STK_RT_STRSTR, ESTACK, A_shadow_glob in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia. }
clear HS. rename HS3 into HS. rewrite <- restrict_mkst_fx in HS.
set (Eg := havoc Eh 49 (map (getr regs3) CLOB)) in HS.
assert (F2b : bv_unsigned (ew Eg 2) = spZ regs) by (unfold Eg; rewrite YN3v.ew_havoc_old by lia; exact F2).
clear SHOK. assert (SHOK : sh_ok tfibsegs hp_Bx [] Eg (mrestrict (w_H W) mem3)) by apply Forall_nil.
(* 0x8219c: `beqz a0` on the first strstr answer *)
aj_run_tok tbl_hp_ok HS HJ3 SHOK hp_Bspan.
{ awr_ok_tac. exact F2b. }
pose proof (gframe_of_frame tfibsegs W Eg _ 2 (-112) 0 (spZ regs) (spZ regs - STK_has_prefixed) (spZ regs) _ _
  HFr ltac:(vm_compute; reflexivity) F2b ltac:(rewrite FFS; lia) ltac:(lia)) as G4b.
clear HF HFr HG.
(* the first strstr answer: atom 53 of Eg *)
assert (U53 : U Eg (SOff 53 0) = v5).
{ apply (U_atom Eg 53 v5); [|exact Hv5].
  unfold Eg. cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB]. exact Hb0. }
assert (G14 : gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem mem3).
{ apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms0)); [exact GT|].
  apply (gframe_widen tfibsegs W _ _ (spZ regs + -112 - STK_RT_STRSTR) (spZ regs + -112));
    [exact G4 | |]; unfold STK_has_prefixed, STK_RT_STR, STK_RT_STRSTR, STK_name_char, STK_RT_ISALNUM, ESTACK; lia. }
pose proof (gframe_seq tfibsegs W _ _ _ _ _ G14 G4b) as G14b.
pose proof Ht as (_ & Ht4096 & Htcl & _).
assert (HPLEN : plen <= Z.of_nat (length tb)) by lia.
unfold MANIFEST_MAX in Htmax.
srr_branch_with tbl_hp_ok HS.
- (* strstr (text, location) = NULL: no occurrence, return 0 (0x82280) *)
  rewrite branch_eq_U, U53, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  assert (Hno : no_occ tb lb).
  { destruct HRv5 as [(_ & Hno) | (j & _ & Hj)]; [exact Hno | lia]. }
  assert (Htok : ManifestModel.token tb (firstn (Z.to_nat plen) (skipn (Z.to_nat q) tb)) lb = false).
  { apply (tok_none _ _ _ 0 (INV_0 _ _ _) (noocc_mt tb lb 0 Hno)). }
  aj_run_tok tbl_hp_ok HS HJ3 SHOK hp_Bspan.
  { awr_ok_tac. exact F2b. }
  pose proof (gframe_of_frame tfibsegs W Eg _ 2 (-112) 0 (spZ regs) (spZ regs - STK_has_prefixed) (spZ regs) _ _
    HFr ltac:(vm_compute; reflexivity) F2b ltac:(rewrite FFS; lia) ltac:(lia)) as G5.
  clear HF HFr HG.
  rreg HS (1%bv : bv 5) P1. rreg HS (10%bv : bv 5) P10.
  eapply (SRr_ret_at tfibsegs tbl_hp tbl_hp_ok Hwx W Eg _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matR.
  lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) =>
    exists ly, S, r, m, d end.
  split.
  { cbn [ms_regs]. rewrite P1. unfold Eg, Eh. rewrite !YN3v.ew_havoc_old by lia. rewrite E1, Hra. reflexivity. }
  split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs B LAWS Hsegs); exact HJ3|].
  split.
  { eapply (aregs_preserved_of_st_ok tfibsegs (w_H W) Eg _ _ regs [w64 SBz] HS); [|vm_compute; reflexivity].
    unfold Eg, Eh. apply env_agree_havoc_ge; [lia|]. apply env_agree_havoc_ge; [lia|]. apply env_agree_refl. }
  split.
  { cbn [ms_regs]. rewrite P10, Htok.
    unfold Eg. cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB]. rewrite Hb0, Hc. reflexivity. }
  split; [reflexivity|].
  apply (fm_glob_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [| rewrite FFS; lia | exact Hglob].
  cbn [ms_mem]. exact (gframe_seq tfibsegs W _ _ _ _ _ G14b G5).
- (* a first occurrence at j0: on to the loop head 0x821b0 with a = j0 *)
  rewrite branch_eq_U, U53, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  destruct HRv5 as [(Hv0 & _) | (j0 & Hfo & Hv5j)]; [contradiction|].
  aj_run_to_tok tbl_hp_ok HS HJ3 SHOK hp_Bspan HP_HEAD.
  { awr_ok_tac. exact F2b. }
  pose proof (gframe_of_frame tfibsegs W Eg _ 2 (-112) 0 (spZ regs) (spZ regs - STK_has_prefixed) (spZ regs) _ _
    HFr ltac:(vm_compute; reflexivity) F2b ltac:(rewrite FFS; lia) ltac:(lia)) as G5.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Eg _ msx HS eq_refl); cbn [ss_pc];
    set (MS := msx) in *; set (MD := mdx) in * end.
  set (cx := mkHC regs ly S W mem md t q plen lp tb lb live peak cnt fail).
  assert (EW : forall (n : nat) (rr : bv 5), (n < 33)%nat -> Z.of_nat n = bv_unsigned rr -> ew Eg n = getr regs rr).
  { intros n rr Hn Hr. unfold Eg, Eh. rewrite !YN3v.ew_havoc_old by lia. apply ew_Ereg_nat. exact Hr. }
  rreg HS (2%bv : bv 5) P2. rreg HS (3%bv : bv 5) P3. rreg HS (4%bv : bv 5) P4.
  rreg HS (8%bv : bv 5) P8. rreg HS (9%bv : bv 5) P9. rreg HS (18%bv : bv 5) P18. rreg HS (19%bv : bv 5) P19.
  rreg HS (20%bv : bv 5) P20. rreg HS (21%bv : bv 5) P21. rreg HS (23%bv : bv 5) P23. rreg HS (24%bv : bv 5) P24.
  rreg HS (26%bv : bv 5) P26. rreg HS (27%bv : bv 5) P27.
  assert (Hst : hp_st B cx j0 ly S W (ms_regs MS) (ms_mem MS) MD).
  { unfold hp_st, hp_entry_ok, cx. cbn [cx_regs0 cx_ly cx_S cx_W0 cx_mem cx_md cx_t cx_q cx_plen cx_lp cx_tb cx_lb
      cx_live cx_peak cx_cnt cx_fail].
    split.
    { split; [exact Hra|]. split; [exact Hgp|]. split; [exact Htp|]. split; [exact Ht|]. split; [exact Hl|].
      split; [exact Hkt|]. split; [exact Hkl|]. split; [exact Hlb|]. split; [exact Hq|]. split; [exact Hplen|].
      split; [exact Hqp|]. split; [unfold MANIFEST_MAX; lia | exact HRO]. }
    split; [exact HJ3|]. split; [reflexivity|].
    split; [rewrite P3, (EW 3%nat 3%bv) by (lia || reflexivity); exact Hgp|].
    split; [rewrite P4, (EW 4%nat 4%bv) by (lia || reflexivity); exact Htp|].
    split; [unfold spZ at 1; rewrite P2, (EW 2%nat 2%bv) by (lia || reflexivity);
            fold (spZ regs); rewrite unsigned_lit_small by lia; lia|].
    split.
    { unfold hp_frame.
      replace (spZ regs - 8) with (spZ regs + -8) by lia. replace (spZ regs - 16) with (spZ regs + -16) by lia.
      replace (spZ regs - 24) with (spZ regs + -24) by lia. replace (spZ regs - 32) with (spZ regs + -32) by lia.
      replace (spZ regs - 40) with (spZ regs + -40) by lia. replace (spZ regs - 48) with (spZ regs + -48) by lia.
      replace (spZ regs - 56) with (spZ regs + -56) by lia. replace (spZ regs - 64) with (spZ regs + -64) by lia.
      replace (spZ regs - 72) with (spZ regs + -72) by lia. replace (spZ regs - 80) with (spZ regs + -80) by lia.
      replace (spZ regs - 88) with (spZ regs + -88) by lia. replace (spZ regs - 96) with (spZ regs + -96) by lia.
      replace (spZ regs - 104) with (spZ regs + -104) by lia.
      repeat split;
        (eapply (hp_frame_word Eg _ MS (w_H W) _ _ _ regs _ HS eq_refl eq_refl);
         [hp_in_chunks | exact F2b | apply EW; [lia | reflexivity]]). }
    split; [rewrite P8, (EW 13%nat 13%bv) by (lia || reflexivity); exact H13|].
    split; [rewrite P9, (EW 12%nat 12%bv) by (lia || reflexivity); exact H12|].
    split; [rewrite P18, (EW 11%nat 11%bv) by (lia || reflexivity); exact H11|].
    split; [rewrite P19, (EW 10%nat 10%bv) by (lia || reflexivity); exact H10|].
    split.
    { rewrite P20. unfold Eg. rewrite YN3v.ew_havoc_old by lia.
      unfold Eh. cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB]. rewrite Ha0, HRv4. reflexivity. }
    split.
    { rewrite P21. unfold Eg. cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB].
      rewrite Hb0, Hv5j. reflexivity. }
    split.
    { rewrite P23. unfold Eg, Eh. rewrite !YN3v.ew_havoc_old by lia. exact E32. }
    split.
    { rewrite P24, (EW 12%nat 12%bv) by (lia || reflexivity). rewrite H12.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    split.
    { rewrite P26. reflexivity. }
    split.
    { rewrite P27, (EW 12%nat 12%bv) by (lia || reflexivity). rewrite H12. unfold w64.
      rewrite zalu64_sound. apply bv_eq. rewrite !Z_to_bv_unsigned.
      unfold zalu64, zalu_raw, zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_mod by lia. rewrite <- Zminus_mod. reflexivity. }
    split; [exact (first_occ_mt tb lb 0 j0 ltac:(lia) Hfo)|].
    apply (fm_glob_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [| rewrite FFS; lia | exact Hglob].
    exact (gframe_seq tfibsegs W _ _ _ _ _ G14b G5). }
  exact (hp_loop B SH SN SP SO ST (Datatypes.S (length tb)) cx j0 ltac:(unfold cx; cbn [cx_tb]; lia)
    (first_occ_inv _ _ _ 0 j0 (INV_0 _ _ _) Hfo) ly S W (ms_regs MS) (ms_mem MS) MD Hst I).
Qed.

(* has_prefixed_spec under the runtime contracts (Section hypotheses) and TfibLib / fm_img_facts *)
Theorem has_prefixed_holds : has_prefixed_spec tfibsegs B.
Proof.
apply has_prefixed_of_segs.
- apply (hp_seg_head B); assumption.
- apply (hp_seg_ncmp B); assumption.
- apply (hp_seg_pre B); assumption.
- apply (hp_seg_post B); assumption.
- apply (hp_seg_tail B); assumption.
Qed.
End t.
