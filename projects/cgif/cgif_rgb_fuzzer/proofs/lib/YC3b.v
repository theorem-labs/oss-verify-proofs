(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y YC2w YC37 YC3a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL.
Definition tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c : Prop :=
acx_ok cx /\ acx_ranges cx /\ acx_seps cx /\ acx_blk (ablocks B ly7 S7) cx /\ acx_tok cx (ablocks B lyc Sc) /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 /\
alzw_regs_core regs cx /\ agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) /\
alzw_slots (mrestrict (w_H W7) memT) cx /\ alzw_sslots (mrestrict (w_H W7) memT) cx /\ tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 /\
atables_at (mrestrict (w_H W7) memT) cx X /\ lzw_inv (z_idl cx) (z_nP cx) X /\
tmiss_pre cx X regs s1 q c /\ la_s X < s1 <= z_nP cx - 1 /\ 0 <= q < 4096 /\ 0 <= c < z_idl cx /\
val_mem trasegs (mrestrict (w_H W7) memT) (z_img cx + s1) 1 c /\ val_mem trasegs (mrestrict (w_H W7) memT) (z_sp cx - 320 + 48) 8 (z_ti cx).
Definition tmiss_tail_post cx lyc Sc W memc mdc ly7 S7 W7 memT X s1 : world trasegs -> config -> Prop :=
fun W' c' => W' = W7 /\ exists regs' mem' md' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 (atail_pc cx X')) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
atail_post cx X regs' (mrestrict (w_H W7) mem') X' /\ la_s X' = s1.
Lemma tmiss_full : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X = 4096 ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 PC_RST2) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
arst_pre false cx X s1 regs' (mrestrict (w_H W7) mem')).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFC & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HCpix & HS48) Hdp.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFC HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HCpix HS48)
as (E & more & HE0 & HS & HENV & _ & _ & _ & _).
assert (Hmc : mc_of dp (nth (Z.to_nat q) LM 0) (nth (Z.to_nat q) LI 0) = MC_full) by (unfold mc_of; rewrite (proj2 (Z.eqb_eq _ _) Hdp); reflexivity).
rewrite Hmc in HS, HENV. cbn [tmiss_J] in HENV.
destruct HENV as (HE2 & HE8 & HE27 & HE25 & HE53 & HE54 & HE56 & HE55 & HE57 & HE59 & HE58 & HE32 & HE33 & HE34 & HE35 & HE37 & HE23 & HE15 & HE71 & HE72 & HE73 &
HE60 & HE64 & HE65 & HE66 & HE68 & HE69 & HE3 & HE4 & HE70 & HE5 & HE24).
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct HT as (ATI & ALM & ALI & ATM).
set (m := mrestrict (w_H W7) memT) in *.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_RST2; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
split; [reflexivity|]. split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (0, 0); (0, 0); (0, 0)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
unfold arst_pre. cbv beta iota. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_afterI E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] end. }
split; [aregv HS (30%bv : bv 5)|]. split; [aregv HS (16%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|].
split; [genM 0%nat HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | cbn; septac HSEP 0%nat 6%nat; repeat split; lia]) (z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 25 2) (z_idl cx + 2) HE25 (SLit 1) 1 HE25|].
split.
{ eapply (atables_at_frame m _ cx (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => ~ outsideA [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (0, 0); (0, 0); (0, 0)] a));
[exact (conj ATI (conj ALM (conj ALI ATM))) | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | tauto] | | | |];
cbn beta; intros a Ha Hn; apply Hn; cbn; unfold z_tisz, z_tmsz in Ha.
- septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. repeat split; lia.
- septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. repeat split; lia.
- septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. repeat split; lia.
- septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. repeat split; lia. }
split; [exact HI|]. split; [exact Hdp|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
Lemma tmiss_map : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 <> 0 ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)) mdT)
(tmiss_tail_post cx lyc Sc W memc mdc ly7 S7 W7 memT X s1).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFC & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HCpix & HS48) Hdp HLM.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFC HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HCpix HS48)
as (E & more & HE0 & HS & HENV & Hmap & Hsw & Hfirst & _).
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
assert (Hmc : mc_of dp vLM vLI = MC_map).
{{ unfold mc_of. replace (dp =? 4096) with false by (symmetry; apply Z.eqb_neq; lia).
fold vLM in HLM. replace (vLM =? 0) with false by (symmetry; apply Z.eqb_neq; exact HLM). reflexivity. }}
rewrite Hmc in HS, HENV, Hmap, Hsw, Hfirst. cbn [tmiss_J is_map is_sw is_first] in HENV, Hmap, Hsw, Hfirst.
destruct HENV as (HE2 & HE8 & HE27 & HE25 & HE53 & HE54 & HE56 & HE55 & HE57 & HE59 & HE58 & HE32 & HE33 & HE34 & HE35 & HE37 & HE23 & HE15 & HE71 & HE72 & HE73 &
HE60 & HE64 & HE65 & HE66 & HE68 & HE69 & HE3 & HE4 & HE70 & HE5 & HE24).
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }}
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI. fold vLI in HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM. fold vLM in HvLM.
destruct HT as (ATI & ALM & ALI & ATM).
set (m := mrestrict (w_H W7) memT) in *.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
specialize (Hmap eq_refl). destruct Hmap as (HJ0 & HJlen & HJsz & HvLMr & _). clear Hsw Hfirst.
remember ((vLM - 1) * z_idl cx + c) as J eqn:HJdef.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_HEAD; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx));
try (oblk HJ HBtm HE68 HE27 (z_tm cx + 2 * J)); try (oblk HJ HBi HE70 HE27 (z_img cx + s1)); try (oblk HJ HBlm HE65 HE27 (z_lm cx + 2 * q)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. repeat (apply awr_ok_cons_ro; [cbn; lia|]).
awr_tmp 68%nat (z_tm cx + 2 * J) HE68 Atm HBtm. apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI LM LI (updn TM (Z.to_nat J) dp) s1 (lp + 1) (dp + 1) mp (Cn + 1) R) end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (0, 0); (0, 0); (0, 0); (z_tm cx + 2 * J, z_tm cx + 2 * J + 2)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
cellv HS 7%nat 68%nat (z_tm cx + 2 * J) HE68 (SOff 34 0) dp HE34 Vnew.
pose proof (inv_map (z_idl cx) (z_nP cx) Hidl _ vLM c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) ltac:(cbn [la_mp]; lia) Hc) as HI'.
cbn [st_map] in HI'. rewrite <- HJdef in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_afterI E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] end. }
split; [genM 0%nat HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | cbn; septac HSEP 0%nat 6%nat; septac HSEP 5%nat 6%nat; repeat split; lia])
(z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 34 1) (dp + 1) HE34 (SOff 35 0) mp HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia. unfold z_tisz in *.
apply Hout; [lia | cbn]. septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. septac HSEP 1%nat 5%nat. repeat split; lia.
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia | cbn]. septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. septac HSEP 2%nat 5%nat. repeat split; lia.
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia | cbn]. septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. septac HSEP 4%nat 5%nat. repeat split; lia.
- eapply arr16_upd; [exact ATM | lia | exact HJlen | lia | exact Vnew |].
intros a Ha Hna. rewrite LenTM, Z2Nat.id in Ha by lia.
apply Hout; [lia | cbn]. septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. repeat split; first [exact Hna | lia]. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
Lemma tmiss_first : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
nth (Z.to_nat q) (la_LI X) 0 = 0 ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)) mdT)
(tmiss_tail_post cx lyc Sc W memc mdc ly7 S7 W7 memT X s1).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFC & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HCpix & HS48) Hdp HLM HLI.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFC HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HCpix HS48)
as (E & more & HE0 & HS & HENV & Hmap & Hsw & Hfirst & _).
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
assert (Hmc : mc_of dp vLM vLI = MC_first).
{{ unfold mc_of. replace (dp =? 4096) with false by (symmetry; apply Z.eqb_neq; lia).
fold vLM in HLM. fold vLI in HLI. rewrite (proj2 (Z.eqb_eq _ _) HLM), (proj2 (Z.eqb_eq _ _) HLI). reflexivity. }}
rewrite Hmc in HS, HENV, Hmap, Hsw, Hfirst. cbn [tmiss_J is_map is_sw is_first] in HENV, Hmap, Hsw, Hfirst.
destruct HENV as (HE2 & HE8 & HE27 & HE25 & HE53 & HE54 & HE56 & HE55 & HE57 & HE59 & HE58 & HE32 & HE33 & HE34 & HE35 & HE37 & HE23 & HE15 & HE71 & HE72 & HE73 &
HE60 & HE64 & HE65 & HE66 & HE68 & HE69 & HE3 & HE4 & HE70 & HE5 & HE24).
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }}
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI. fold vLI in HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM. fold vLM in HvLM.
destruct HT as (ATI & ALM & ALI & ATM).
set (m := mrestrict (w_H W7) memT) in *.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
clear Hmap Hsw Hfirst.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_HEAD; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx));
try (oblk HJ HBli HE64 HE27 (z_li cx + 2 * q)); try (oblk HJ HBlc HE66 HE27 (z_lc cx + q)); try (oblk HJ HBi HE70 HE27 (z_img cx + s1));
try (oblk HJ HBlm HE65 HE27 (z_lm cx + 2 * q)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. awr_tmp 64%nat (z_li cx + 2 * q) HE64 Ali HBli. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 66%nat (z_lc cx + q) HE66 Alc HBlc. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI LM (updn LI (Z.to_nat q) dp) TM s1 (lp + 1) (dp + 1) mp (Cn + 1) R) end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (z_li cx + 2 * q, z_li cx + 2 * q + 2); (0, 0); (z_lc cx + q, z_lc cx + q + 1); (0, 0)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
cellv HS 3%nat 64%nat (z_li cx + 2 * q) HE64 (SOff 34 0) dp HE34 Vnew.
pose proof (inv_first (z_idl cx) (z_nP cx) Hidl _ q (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq) as HI'.
cbn [la_LI la_LM] in HI'. specialize (HI' HLI HLM).
cbn [st_first] in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_afterI E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] end. }
split; [genM 0%nat HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | cbn; septac HSEP 0%nat 6%nat; septac HSEP 4%nat 6%nat; septac HSEP 3%nat 6%nat; repeat split; lia])
(z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 34 1) (dp + 1) HE34 (SOff 35 0) mp HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia. unfold z_tisz in *.
apply Hout; [lia | cbn]. septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. septac HSEP 1%nat 4%nat. septac HSEP 1%nat 3%nat. repeat split; lia.
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia | cbn]. septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. septac HSEP 2%nat 4%nat. septac HSEP 2%nat 3%nat. repeat split; lia.
- eapply arr16_upd; [exact ALI | lia | exact HqLI | lia | exact Vnew |].
intros a Ha Hna. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia | cbn]. septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. septac HSEP 3%nat 4%nat. repeat split; first [exact Hna | lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia. unfold z_tmsz in *.
apply Hout; [lia | cbn]. septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. septac HSEP 4%nat 5%nat. septac HSEP 3%nat 5%nat. repeat split; lia. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
End S.
End b.
