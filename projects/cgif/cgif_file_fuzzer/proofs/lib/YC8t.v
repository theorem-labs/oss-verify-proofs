(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC81 YC4b YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC9d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8a YC93 YC9g YC95 YC91 YC99 YC92 YC9b YC9i YC9c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI0u.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC90 YC8y.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Ltac cellw HS idx n b HEn off w e v HEv Vname :=
let HR := fresh "HRc" in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx idx _ HS eq_refl) as HR end;
cbn [ms_mem restrict] in HR;
lazymatch type of HR with region_ok _ ?Ex ?mx _ =>
assert (Vname : val_mem _ mx (b + off) (N.to_nat w) v)
by (eapply (field_of_region _ _ n b _ _ _ _ _ off w e v HR);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HEn; apply unsigned_lit_small; lia | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
first [ rewrite HEv
| lazymatch e with SOff ?k _ => match goal with AGx : forall n : nat, (n < _)%nat -> ew _ n = ew _ n |- _ => rewrite (AGx k) by lia end end; rewrite HEv ];
rewrite ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| first [change (2 ^ (8 * Z.of_N 2)) with 65536 | change (2 ^ (8 * Z.of_N 1)) with 256]; lia | cbn; lia ]) end;
clear HR.
Ltac xvoff tlc timg tld :=
cbn [la_lp]; split; [|split]; intros a Ha; (split; [lia|]); intros Hn; apply Hn; cbn; [tlc | timg | tld]; repeat split; lia.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_1 PI.
Definition tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c : Prop :=
acx_ok cx /\ acx_ranges cx /\ acx_seps cx /\ acx_blk (ablocks B ly7 S7) cx /\ acx_tok cx (ablocks B lyc Sc) /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 /\
alzw_regs_fix regs cx /\ agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) /\
alzw_slots (mrestrict (w_H W7) memT) cx /\ alzw_sslots (mrestrict (w_H W7) memT) cx /\ tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 /\
atables_at (mrestrict (w_H W7) memT) cx X /\ lzw_inv (z_idl cx) (z_nP cx) X /\
tmiss_pre cx X regs s1 q c /\ la_s X < s1 <= z_nP cx - 1 /\ 0 <= q < 4096 /\ 0 <= c < z_idl cx /\
val_mem SEGS (mrestrict (w_H W7) memT) (z_img cx + s1) 1 c.
Lemma tmiss_fullX : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c (PIX : list Z) (V : lzw_v),
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X = 4096 ->
vtabs_at SEGS (mrestrict (w_H W7) memT) cx PIX V -> vinv cx PIX X V ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC_RST)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
arst_pre cx X s1 regs' (mrestrict (w_H W7) mem') /\
vtabs_at SEGS (mrestrict (w_H W7) mem') cx PIX (mkLV (v_LC V) (v_LD V ++ [q]))).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
PIX V (HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFX & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HC) Hdp HVT HVI.
pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFX HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HC)
as (E & more & HE0 & HS & HENV & _ & _ & _ & _). assert (HEI : img_env VAL A_LIM E) by (rewrite HE0; apply Eimg_env).
assert (Hmc : mc_of dp (nth (Z.to_nat q) LM 0) (nth (Z.to_nat q) LI 0) = MC_full) by (unfold mc_of; rewrite (proj2 (Z.eqb_eq _ _) Hdp); reflexivity).
rewrite Hmc in HS, HENV. cbn [tmiss_J] in HENV.
destruct HENV as (HE2 & HE8 & HE21 & HE25 & HE3 & HE4 & HE32 & HE33 & HE34 & HE35 & HE36 & HE37 & HE38 & HE39 & HE41 & HE42 & HE43 & HE45 &
HE14 & HE24 & HE26 & HE16 & HE11 & HE12 & HE60 & HE61 & HE62 & HE63 & HE64 & HE65 & HE66 & HE67).
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. unfold lzw_MR in Rld1, Rld2, Rld4, Hrqld, HBld, Ald. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct HT as (ATI & ALM & ALI & ATM).
set (m := mrestrict (w_H W7) memT) in *.
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_RST; try (oblm HJ HBld HE60 HE21 (z_ld cx + 2 * lp)); try (oblm HJ HBg HE8 HE21 (z_ctx cx)).
{ awrc 8%nat (z_ctx cx) HE8 Actx HBg. apply awr_ok_cons_ro; [cbn; lia|].
awrc 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_nil. }
idtac "FULL RUN OK".
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
split; [reflexivity|]. split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
split; [| subst m; cellw HS 2%nat 60%nat (z_ld cx + 2 * lp) HE60 0 2%N (SOff 14 0) q HE14 Vq0;
eapply (vtabs_emit SEGS _ _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => ~ outsideA [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2)] a) q HVT HVI);
[ lia | intros a Ha Hna; apply Hout; [exact Ha | tauto]
| xvoff ltac:(septac HSEP 0%nat 3%nat; septac HSEP 3%nat 6%nat) ltac:(septac HSEP 0%nat 7%nat; septac HSEP 6%nat 7%nat) ltac:(septac HSEP 0%nat 6%nat)
| cbn [la_lp]; rewrite Z.add_0_r in Vq0; exact Vq0 | lia ] ].
unfold arst_pre. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split.
{ lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]  end. }
split; [genM 0%nat HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | cbn; septac HSEP 0%nat 6%nat; repeat split; lia]) (z_ctx cx) (SOff 41 1) (lp + 1) HE41 (SOff 42 0) dp HE42 (SOff 43 0) mp HE43|].
split.
{ eapply (atables_at_frame m _ cx (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => ~ outsideA [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2)] a));
[exact (conj ATI (conj ALM (conj ALI ATM))) | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | tauto] | | | |];
cbn beta; intros a Ha Hn; apply Hn; cbn; unfold z_tisz, z_tmsz in Ha.
- septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. repeat split; lia.
- septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. repeat split; lia.
- septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. repeat split; lia.
- septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. repeat split; lia. }
split; [exact HI|]. split; [exact Hdp|]. split; [aregv HS (24%bv : bv 5) | lia].
Qed.
Lemma tmiss_mapX : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c (PIX : list Z) (V : lzw_v),
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 <> 0 ->
vtabs_at SEGS (mrestrict (w_H W7) memT) cx PIX V -> vinv cx PIX X V ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(tmiss_tail_postX B cx lyc Sc W memc mdc ly7 S7 W7 memT X s1
(vx_map (z_idl cx) X (nth (Z.to_nat q) (la_LM X) 0) c s1) PIX (mkLV (v_LC V) (v_LD V ++ [q]))).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
PIX V (HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFX & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HC) Hdp HLM HVT HVI.
pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFX HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HC)
as (E & more & HE0 & HS & HENV & Hmap & Hsw & Hfirst & _). assert (HEI : img_env VAL A_LIM E) by (rewrite HE0; apply Eimg_env).
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
assert (Hmc : mc_of dp vLM vLI = MC_map).
{ unfold mc_of. replace (dp =? 4096) with false by (symmetry; apply Z.eqb_neq; lia).
replace (vLM =? 0) with false by (symmetry; apply Z.eqb_neq; exact HLM). reflexivity. }
rewrite Hmc in HS, HENV, Hmap, Hsw, Hfirst. cbn [tmiss_J is_map is_sw is_first] in HENV, Hmap, Hsw, Hfirst.
destruct HENV as (HE2 & HE8 & HE21 & HE25 & HE3 & HE4 & HE32 & HE33 & HE34 & HE35 & HE36 & HE37 & HE38 & HE39 & HE41 & HE42 & HE43 & HE45 &
HE14 & HE24 & HE26 & HE16 & HE11 & HE12 & HE60 & HE61 & HE62 & HE63 & HE64 & HE65 & HE66 & HE67).
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. unfold lzw_MR in Rld1, Rld2, Rld4, Hrqld, HBld, Ald. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM. fold vLM in HvLM.
destruct HT as (ATI & ALM & ALI & ATM).
set (m := mrestrict (w_H W7) memT) in *.
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
specialize (Hmap eq_refl). destruct Hmap as (HJ0 & HJlen & HJsz & HvLMr & _). clear Hsw Hfirst.
remember ((vLM - 1) * z_idl cx + c) as J eqn:HJdef.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_HEAD; try (oblm HJ HBld HE60 HE21 (z_ld cx + 2 * lp)); try (oblm HJ HBg HE8 HE21 (z_ctx cx));
try (oblm HJ HBi HE16 HE21 (z_img cx + s1)); try (oblm HJ HBlm HE12 HE21 (z_lm cx + 2 * q)); try (oblm HJ HBtm HE65 HE21 (z_tm cx + 2 * J)).
{ awrc 8%nat (z_ctx cx) HE8 Actx HBg. apply awr_ok_cons_ro; [cbn; lia|].
awrc 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. repeat (apply awr_ok_cons_ro; [cbn; lia|]).
awrc 65%nat (z_tm cx + 2 * J) HE65 Atm HBtm. apply awr_ok_nil. }
idtac "MAP RUN OK".
pmkst HS.
apply SRr_ret. split; [reflexivity|].
unfold vx_map. rewrite <- HJdef.
lazymatch goal with |- exists regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2); (0, 0); (0, 0); (z_tm cx + 2 * J, z_tm cx + 2 * J + 2)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
cellv HS 5%nat 65%nat (z_tm cx + 2 * J) HE65 (SOff 42 0) dp HE42 Vnew.
pose proof (inv_map (z_idl cx) (z_nP cx) Hidl _ vLM c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) ltac:(cbn [la_mp]; lia) Hc) as HI'.
cbn [st_map] in HI'. rewrite <- HJdef in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [| split; [reflexivity|]; subst m; cellw HS 2%nat 60%nat (z_ld cx + 2 * lp) HE60 0 2%N (SOff 14 0) q HE14 Vq0;
eapply (vtabs_emit SEGS _ _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => ~ outsideA [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2); (0, 0); (0, 0); (z_tm cx + 2 * J, z_tm cx + 2 * J + 2)] a) q HVT HVI);
[ lia | intros a Ha Hna; apply Hout; [exact Ha | tauto]
| xvoff ltac:(septac HSEP 0%nat 3%nat; septac HSEP 3%nat 6%nat; septac HSEP 3%nat 5%nat) ltac:(septac HSEP 0%nat 7%nat; septac HSEP 6%nat 7%nat; septac HSEP 5%nat 7%nat) ltac:(septac HSEP 0%nat 6%nat; septac HSEP 0%nat 5%nat)
| cbn [la_lp]; rewrite Z.add_0_r in Vq0; exact Vq0 | lia ] ].
split.
{ split; [|aregv HS (15%bv : bv 5)].
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]  end. }
split; [genM 0%nat HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | cbn; septac HSEP 0%nat 6%nat; septac HSEP 5%nat 6%nat; repeat split; lia])
(z_ctx cx) (SOff 41 1) (lp + 1) HE41 (SOff 42 1) (dp + 1) HE42 (SOff 43 0) mp HE43|].
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
split; [exact HI'|]. split; [aregv HS (24%bv : bv 5) | lia].
Qed.
Lemma tmiss_firstX : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c (PIX : list Z) (V : lzw_v),
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
nth (Z.to_nat q) (la_LI X) 0 = 0 ->
vtabs_at SEGS (mrestrict (w_H W7) memT) cx PIX V -> vinv cx PIX X V ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(tmiss_tail_postX B cx lyc Sc W memc mdc ly7 S7 W7 memT X s1
(vx_first X q s1) PIX (mkLV (updn (v_LC V) (Z.to_nat q) c) (v_LD V ++ [q]))).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
PIX V (HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFX & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HC) Hdp HLM HLI HVT HVI.
pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFX HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HC)
as (E & more & HE0 & HS & HENV & Hmap & Hsw & Hfirst & _). assert (HEI : img_env VAL A_LIM E) by (rewrite HE0; apply Eimg_env).
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
assert (Hmc : mc_of dp vLM vLI = MC_first).
{ unfold mc_of. replace (dp =? 4096) with false by (symmetry; apply Z.eqb_neq; lia).
fold vLM in HLM. fold vLI in HLI. rewrite (proj2 (Z.eqb_eq _ _) HLM), (proj2 (Z.eqb_eq _ _) HLI). reflexivity. }
rewrite Hmc in HS, HENV, Hmap, Hsw, Hfirst. cbn [tmiss_J is_map is_sw is_first] in HENV, Hmap, Hsw, Hfirst.
destruct HENV as (HE2 & HE8 & HE21 & HE25 & HE3 & HE4 & HE32 & HE33 & HE34 & HE35 & HE36 & HE37 & HE38 & HE39 & HE41 & HE42 & HE43 & HE45 &
HE14 & HE24 & HE26 & HE16 & HE11 & HE12 & HE60 & HE61 & HE62 & HE63 & HE64 & HE65 & HE66 & HE67).
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. unfold lzw_MR in Rld1, Rld2, Rld4, Hrqld, HBld, Ald. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI. fold vLI in HvLI.
destruct HT as (ATI & ALM & ALI & ATM).
set (m := mrestrict (w_H W7) memT) in *.
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
clear Hmap Hsw Hfirst.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_HEAD; try (oblm HJ HBld HE60 HE21 (z_ld cx + 2 * lp)); try (oblm HJ HBg HE8 HE21 (z_ctx cx));
try (oblm HJ HBi HE16 HE21 (z_img cx + s1)); try (oblm HJ HBlm HE12 HE21 (z_lm cx + 2 * q));
try (oblm HJ HBli HE11 HE21 (z_li cx + 2 * q)); try (oblm HJ HBlc HE64 HE21 (z_lc cx + q)).
{ awrc 8%nat (z_ctx cx) HE8 Actx HBg. apply awr_ok_cons_ro; [cbn; lia|].
awrc 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. repeat (apply awr_ok_cons_ro; [cbn; lia|]).
awrc 11%nat (z_li cx + 2 * q) HE11 Ali HBli. awrc 64%nat (z_lc cx + q) HE64 Alc HBlc. apply awr_ok_nil. }
idtac "FIRST RUN OK".
pmkst HS.
apply SRr_ret. split; [reflexivity|].
unfold vx_first.
lazymatch goal with |- exists regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2); (0, 0); (0, 0); (z_li cx + 2 * q, z_li cx + 2 * q + 2); (z_lc cx + q, z_lc cx + q + 1)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
cellv HS 5%nat 11%nat (z_li cx + 2 * q) HE11 (SOff 42 0) dp HE42 Vnew.
pose proof (inv_first (z_idl cx) (z_nP cx) Hidl _ q (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq) as HI'.
cbn [la_LI la_LM] in HI'. specialize (HI' HLI HLM).
cbn [st_first] in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [| split; [reflexivity|]; subst m; cellw HS 2%nat 60%nat (z_ld cx + 2 * lp) HE60 0 2%N (SOff 14 0) q HE14 Vq0;
cellw HS 6%nat 64%nat (z_lc cx + q) HE64 0 1%N (SOff 61 0) c HE61 Vc0; rewrite Z.add_0_r in Vc0;
pose proof HVI as (LenLC & LenPIX & LenLD);
eapply (vtabs_emit_lc SEGS _ _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => ~ outsideA [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2); (0, 0); (0, 0); (z_li cx + 2 * q, z_li cx + 2 * q + 2); (0, 0)] a) q c HVT HVI);
[ lia | lia
| intros a Ha Hna Hne; apply Hout; [exact Ha | cbn; cbn in Hna; repeat split; first [tauto | lia]]
| xvoff ltac:(septac HSEP 0%nat 3%nat; septac HSEP 3%nat 6%nat; septac HSEP 3%nat 4%nat) ltac:(septac HSEP 0%nat 7%nat; septac HSEP 6%nat 7%nat; septac HSEP 4%nat 7%nat) ltac:(septac HSEP 0%nat 6%nat; septac HSEP 0%nat 4%nat)
| cbn [la_lp]; rewrite Z.add_0_r in Vq0; exact Vq0 | exact Vc0 | lia
| intros a Ha; septac HSEP 3%nat 7%nat; lia
| cbn [la_lp]; intros a Ha; septac HSEP 0%nat 3%nat; lia ] ].
split.
{ split; [|aregv HS (15%bv : bv 5)].
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]  end. }
split; [genM 0%nat HS HE8 HG ltac:(fun a Ha => apply Hout; [lia | cbn; septac HSEP 0%nat 6%nat; septac HSEP 4%nat 6%nat; septac HSEP 3%nat 6%nat; repeat split; lia])
(z_ctx cx) (SOff 41 1) (lp + 1) HE41 (SOff 42 1) (dp + 1) HE42 (SOff 43 0) mp HE43|].
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
split; [exact HI'|]. split; [aregv HS (24%bv : bv 5) | lia].
Qed.
End S.
End f.
End d.
