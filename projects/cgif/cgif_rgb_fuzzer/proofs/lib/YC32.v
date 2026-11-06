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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_temitc : sstate :=
alzw_ss PC_EMITC (sr_set (sr_set asr_t5 23%bv (SOff 59 (-1))) 15%bv (SOff 62 0)) true false
[reg16 60 61 true] [ (60%nat, APTR 1); (61%nat, mkAF 0 65535 0); (62%nat, mkAF 0 4095 0) ] []
[ (SAlu ALU_ADD (SOff 58 0) (SAlu ALU_SLL (SOff 33 0) (SLit 1)), SOff 60 0) ].
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL.
Lemma temitc_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X q,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx -> acx_tok cx (ablocks B lyc Sc) ->
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_fix regs cx -> getr regs 30 = w64 (z_ctx cx + 60) -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx X -> lzw_inv (z_idl cx) (z_nP cx) X -> la_s X < z_nP cx ->
getr regs 23 = w64 (z_nP cx - 1) -> getr regs 15 = w64 q -> 0 <= q < 4096 ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_EMITC) memT (seg_rom trasegs)) mdT)
(fun W' c' => W' = W7 /\ exists regs' mem' md' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 (atail_pc cx X')) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 /\
aabove_eq cx (mrestrict (w_H W7) memT) (mrestrict (w_H W7) mem') /\
atail_post cx X regs' (mrestrict (w_H W7) mem') X').
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X q HCX HRG HSEP (HBg & HBi & HBt) HTOK HJ HFX H30 HG HSL HSS HFR HT HI Hs H24 H13 Hq.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & Hldceil & _ & Hldpres & _).
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld.
assert (Actx : forall blc lyq i, In (z_ctx cx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ctx cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ctx cx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (Ald : forall blc lyq i, In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) blc -> 0 <= i < req_size (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ->
awr_byte LZW_TSTK (z_sp cx) [] (ablocks B lyc Sc) blc lyq [] (z_ld cx + i)).
{ intros blc lyq i Hb Hi. apply (HTOK (z_ld cx, _) ltac:(right; cbv [acx_tabs lzw_tabs]; left; reflexivity)); [exact Hb | exact Hi]. }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
set (m := mrestrict (w_H W7) memT) in *.
assert (Pld : forall i, 0 <= i < 2 * (z_nP cx + 2 + z_MR cx) -> YP0c.present m (z_ld cx + i)).
{ intros i Hi. destruct (Hldpres (z_ld cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem2 trasegs m (z_ld cx + 2 * lp)) as (vLD & HvLDr & HvLD); [apply Pld; lia | replace (z_ld cx + 2 * lp + 1) with (z_ld cx + (2 * lp + 1)) by lia; apply Pld; lia |].
change (2 ^ 16) with 65536 in HvLDr.
remember [Z_to_bv 64 (z_ld cx + 2 * lp); Z_to_bv 64 vLD; Z_to_bv 64 q] as more eqn:Hmore.
remember (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) as E eqn:HE0.
assert (HE60 : ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0), Hmore; reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 vLD) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1), Hmore; reflexivity).
assert (HE62 : ew E 62 = Z_to_bv 64 q) by (rewrite HE0; change 62%nat with (60 + 2)%nat; rewrite (AE_more regs _ _ _ _ _ more 2), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE27. pose proof (AE_ld regs cx lp dp mp regs0 more) as HE58.
pose proof (AE_nP regs cx lp dp mp regs0 more) as HE59. pose proof (AE_lp regs cx lp dp mp regs0 more) as HE33.
rewrite <- HE0 in HE2, HE8, HE27, HE58, HE59, HE33.
assert (HS1 : st_ok trasegs E (alzw_ss PC_EMITC asr_t5 true false [reg16 60 61 true] [ (60%nat, APTR 1); (61%nat, mkAF 0 65535 0); (62%nat, mkAF 0 4095 0) ] []
[ (SAlu ALU_ADD (SOff 58 0) (SAlu ALU_SLL (SOff 33 0) (SLit 1)), SOff 60 0) ])
(mkst regs (Z_to_bv 64 PC_EMITC) m (seg_rom trasegs))).
{ rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_EMITC asr_t5 true false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros _ a Ha. apply (apresent_writable trasegs). apply (proj1 (Hcpres a ltac:(lia))).
- intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_t5 regs cx); [exact HFX | exact H30 | lia | lia].
- vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E m 60 61 true (z_ld cx + 2 * lp) vLD HE60 HE61); [lia | lia | lia | exact HvLD |].
intros _ o Ho. apply (apresent_writable trasegs). apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))).
- cbn [all_disjoint app]; unfold extent_disjoint, reg16, actx_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE8, HE60, !unsigned_lit_small by lia.
pose proof (acx_sep _ HSEP 0 6 ltac:(lia) ltac:(lia)) as Hs06; cbv [nth app acx_objs fst snd zz_disj z_tisz z_tmsz z_cap cap] in Hs06. split; [lia | exact I].
- cbn [all_disjoint app]; unfold extent_disjoint, reg16, astk_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE2, HE60, !unsigned_lit_small by lia. split; [lia | exact I].
- cbn [pairwise_disjoint all_disjoint app]. repeat split.
- cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE60, HE61, HE62, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- exact I.
- cbn [alias_ok]. split; [| exact I]. apply (alias_b2i' E 58 33 60 (z_ld cx) lp HE58 HE33 HE60); lia. }
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_EMITC) m (seg_rom trasegs)) 23%bv (SOff 59 (-1)) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE59, unsigned_lit_small by lia; rewrite H24; unfold w64; f_equal; lia)) as HS2.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_EMITC) m (seg_rom trasegs)) 15%bv (SOff 62 0) HS2 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE62, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H13)) as HS.
clear HS1 HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts alzw_ss] in HS.
change (mkst regs (Z_to_bv 64 PC_EMITC) m (seg_rom trasegs)) with (restrict (w_H W7) (mkst regs (Z_to_bv 64 PC_EMITC) memT (seg_rom trasegs))) in HS.
pose proof (AE_dp regs cx lp dp mp regs0 more) as HE34. pose proof (AE_mp regs cx lp dp mp regs0 more) as HE35.
rewrite <- HE0 in HE34, HE35.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_EMITC) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_EMITC) memT (seg_rom trasegs))) in HJ.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_EPI; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx)).
{
awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (st_typec (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R)) end.
split; [unfold atail_pc; cbn [la_s st_typec]; rewrite Z.ltb_irrefl; reflexivity|].
split; [exact HJ|].
lazymatch type of HFr with frame_of _ _ _ ?m' =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (z_ctx cx + 60 <= a < z_ctx cx + 68) -> ~ (z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 2) ->
mbyte trasegs m' a = mbyte trasegs m a)
by (intros a Ha Hn1 Hn2; eapply (aframe_mbyte_list E _ _ _ [(z_ctx cx + 60, z_ctx cx + 68); (0, 0); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 2)] a HFr Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi reg16 actx_region base_val]; rewrite ?HE8, ?HE60, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ])
end.
split; [intros a Ha; apply Hout; [lia | lia | lia]|].
pose proof (inv_typec (z_idl cx) (z_nP cx) Hidl _ HI ltac:(cbn [la_s]; lia)) as HI'.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM st_typec].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
eapply (alzw_regs_fix_after _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia]. }
split.
{
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HRg end.
cbn [ms_mem restrict] in HRg.
assert (G8 : forall Ex, (forall n, (n < 63)%nat -> ew Ex n = ew E n) -> bv_unsigned (ew Ex 8) = z_ctx cx)
by (intros Ex HEx; rewrite (HEx 8%nat) by lia; rewrite HE8; apply unsigned_lit_small; lia).
eapply (agen_at_upd m _ cx lp dp mp); [exact HG | intros a Ha; apply Hout; [lia | lia | septac HSEP 0%nat 6%nat; lia] | | |].
- change 4%nat with (N.to_nat 4). eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 60 4%N _ (lp + 1) HRg);
[ apply G8; intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE33, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia ].
- change 2%nat with (N.to_nat 2). eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 64 2%N _ dp HRg);
[ apply G8; intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE34, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ].
- change 2%nat with (N.to_nat 2). eapply (field_of_region _ _ 8%nat (z_ctx cx) _ _ _ _ _ 66 2%N _ mp HRg);
[ apply G8; intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | cbn; tauto
| cbn [sv_denot ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HE35, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia ]. }
split.
{ eapply (atables_at_frame m _ cx (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => (z_ctx cx + 60 <= a < z_ctx cx + 68) \/ (z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 2)));
[exact HT | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | tauto | tauto] | | | |];
cbn beta; intros a Ha; unfold z_tisz, z_tmsz in Ha.
- septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. lia.
- septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. lia.
- septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. lia.
- septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. lia. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
End S.
End b.
