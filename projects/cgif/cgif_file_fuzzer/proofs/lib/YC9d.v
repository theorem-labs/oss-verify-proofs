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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8a YC93 YC9g YC95 YC91 YC99 YC92 YC9b YC9i YC9c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac miss_prep B cx HCX HRG HBt HTOK HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof HJ as (HAR & _);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity; assert (ASTACK = 16384) as Has by reflexivity;
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR);
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B _ _)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity);
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B _ _)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity);
assert (HBlm : In (z_lm cx, 8192) (ablocks B _ _)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity);
assert (HBlc : In (z_lc cx, 4096) (ablocks B _ _)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity);
assert (HBli : In (z_li cx, 8192) (ablocks B _ _)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity);
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B _ _)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity);
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3); cbn [ranges acx_tabs lzw_tabs app] in HR;
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _);
pose proof (proj1 Hbi0) as Hb4096;
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld;
pose proof (req_size_pos 8192 ltac:(lia)) as Hrq8; pose proof (req_size_pos 4096 ltac:(lia)) as Hrq4; pose proof (req_size_pos (4098 * z_idl cx) ltac:(lia)) as Hrqtm;
pose proof (req_size_pos (2 * z_idl cx * z_idl cx) ltac:(lia)) as Hrqti;
assert (Actx : forall blc lyq i, In (z_ctx cx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B _ _) blc lyq [] (z_ctx cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_ctx cx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]);
assert (Ald : forall blc lyq i, In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) blc -> 0 <= i < req_size (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ->
awr_byte LZW_TSTK (z_sp cx) [] (ablocks B _ _) blc lyq [] (z_ld cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_ld cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; left; reflexivity)); [exact Hb | exact Hi]);
assert (Alm : forall blc lyq i, In (z_lm cx, 8192) blc -> 0 <= i < req_size 8192 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B _ _) blc lyq [] (z_lm cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_lm cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity)); [exact Hb | exact Hi]);
assert (Alc : forall blc lyq i, In (z_lc cx, 4096) blc -> 0 <= i < req_size 4096 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B _ _) blc lyq [] (z_lc cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_lc cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity)); [exact Hb | exact Hi]);
assert (Ali : forall blc lyq i, In (z_li cx, 8192) blc -> 0 <= i < req_size 8192 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B _ _) blc lyq [] (z_li cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_li cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity)); [exact Hb | exact Hi]);
assert (Atm : forall blc lyq i, In (z_tm cx, 4098 * z_idl cx) blc -> 0 <= i < req_size (4098 * z_idl cx) -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B _ _) blc lyq [] (z_tm cx + i))
by (intros blc lyq i Hb Hi; apply (HTOK (z_tm cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity)); [exact Hb | exact Hi]);
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *; clear C2 C3 C4 HTS Has.
Ltac hout HFr E m ws :=
lazymatch type of HFr with frame_of _ _ _ ?m' =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> outsideA ws a -> mbyte _ m' a = mbyte _ m a)
by (intros a Ha Hws; eapply (aframe_mbyte_list E _ _ _ ws a HFr Ha); [|exact Hws];
repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd YP09.r_base YP09.r_wlo YP09.r_whi reg8 reg16 regw ld4 tms_img1 negb actx_region astk_region base_val is_first is_sw is_map];
rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end; rewrite ?unsigned_lit_small by lia; lia]|]);
apply Forall2_nil);
clear HFr
end.
Ltac genM idx HS HE8 HG houttac vctx e60 v60 HE60 e64 v64 HE64 e66 v66 HE66 :=
let HRg := fresh "HRg" in let G8 := fresh "G8" in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx idx _ HS eq_refl) as HRg | st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx idx _ HS eq_refl) as HRg  end;
cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ ?Ex _ _ =>
assert (G8 : bv_unsigned (ew Ex 8) = vctx) by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE8; apply unsigned_lit_small; lia) end;
eapply (agen_at_upd _ _ _ _ _ _ v60 v64 v66); [exact HG | intros a Ha; houttac a Ha | | |];
[ change 4%nat with (N.to_nat 4); eapply (field_of_region _ _ 8%nat vctx _ _ _ _ _ 60 4%N e60 v60 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE60, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia ]
| change 2%nat with (N.to_nat 2); eapply (field_of_region _ _ 8%nat vctx _ _ _ _ _ 64 2%N e64 v64 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE64, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ]
| change 2%nat with (N.to_nat 2); eapply (field_of_region _ _ 8%nat vctx _ _ _ _ _ 66 2%N e66 v66 HRg);
[ exact G8 | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?HE66, ?Z.add_0_r, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia]
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ] ].
Ltac cellv HS idx n b HEn e v HEv Vname :=
let HR := fresh "HRc" in
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx => pose proof (st_ok_pi_region_nth Ex ssx msx idx _ HS eq_refl) as HR | st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx idx _ HS eq_refl) as HR  end;
cbn [ms_mem restrict] in HR;
lazymatch type of HR with region_ok _ ?Ex ?mx _ =>
assert (Vname : val_mem _ mx b 2 v)
by (rewrite <- (Z.add_0_r b); change 2%nat with (N.to_nat 2);
eapply (field_of_region _ _ n b _ _ _ _ _ 0 2%N e v HR);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HEn; apply unsigned_lit_small; lia | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HEv, ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ]) end;
clear HR.
Ltac awrc n b HEn Atmp HB :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n b);
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HEn; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi actx_region astk_region reg16 reg8 regw ld4 tms_img1 negb]; intros a Ha;
lazymatch type of Atmp with forall blc lyq i, In (?b0, _) blc -> _ -> _ =>
replace a with (b0 + (a - b0)) by lia; apply Atmp; [exact HB | lia] end
| ].
Ltac oblm HJ HB HEn HE21 v :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?n ?c)) ?len =>
first [ rewrite (U_atom_off Ex n v c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n v); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff 23 0) _ len _ _ (proj1 HJ) HB);
[ rewrite (U_atom Ex 23 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE21 | unfold SB; lia]
| lia
| try change (req_size 72) with 72; first [ lia | match goal with |- _ <= _ + req_size ?nn => pose proof (req_size_pos nn ltac:(lia)); lia end ] ]
end.
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
Lemma tmiss_full : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X = 4096 ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC_RST)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
arst_pre cx X s1 regs' (mrestrict (w_H W7) mem')).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFX & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HC) Hdp.
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
Lemma tmiss_map : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 <> 0 ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(tmiss_tail_post B cx lyc Sc W memc mdc ly7 S7 W7 memT X s1).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFX & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HC) Hdp HLM.
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
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI LM LI (updn TM (Z.to_nat J) dp) s1 (lp + 1) (dp + 1) mp (Cn + 1) R) end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2); (0, 0); (0, 0); (z_tm cx + 2 * J, z_tm cx + 2 * J + 2)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
cellv HS 5%nat 65%nat (z_tm cx + 2 * J) HE65 (SOff 42 0) dp HE42 Vnew.
pose proof (inv_map (z_idl cx) (z_nP cx) Hidl _ vLM c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) ltac:(cbn [la_mp]; lia) Hc) as HI'.
cbn [st_map] in HI'. rewrite <- HJdef in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
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
Lemma tmiss_first : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
nth (Z.to_nat q) (la_LI X) 0 = 0 ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(tmiss_tail_post B cx lyc Sc W memc mdc ly7 S7 W7 memT X s1).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFX & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HC) Hdp HLM HLI.
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
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI LM (updn LI (Z.to_nat q) dp) TM s1 (lp + 1) (dp + 1) mp (Cn + 1) R) end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ|].
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2); (0, 0); (0, 0); (z_li cx + 2 * q, z_li cx + 2 * q + 2); (z_lc cx + q, z_lc cx + q + 1)].
split; [intros a Ha; apply Hout; [lia | cbn; repeat split; lia]|].
cellv HS 5%nat 11%nat (z_li cx + 2 * q) HE11 (SOff 42 0) dp HE42 Vnew.
pose proof (inv_first (z_idl cx) (z_nP cx) Hidl _ q (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq) as HI'.
cbn [la_LI la_LM] in HI'. specialize (HI' HLI HLM).
cbn [st_first] in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
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
