(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI04
YI1e YI39 YI1i YI57 YI1h YI0x YI26 YO3n YO0e
YI07 YP14 YI08 YI0c YI0g YI3h YI3d YI4v YI4r YI3x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Definition E1_RETM : Z := 0x1346c.
Definition E1_DRET : Z := 0x142b4.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_E1 : sstate :=
mkSS PC_E1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [] ;
YQ0b.mkRegion (Some 2%nat) (-5136) (-4978) (-5136) (-4978) [] ;
YQ0b.mkRegion (Some 10%nat) 0 RGB_SIZE 0 0 (obj_chunks_from LAY_Rgb 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RGBA_STK) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4);
(39%nat, mkAF 0 65535 0); (40%nat, mkAF 0 65535 0); (43%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition SAVE_CHUNKS : list YQ0b.chunk :=
[ mkChunk (-104) (CVal 8 (SOff 27 0)); mkChunk (-96) (CVal 8 (SOff 26 0)); mkChunk (-88) (CVal 8 (SOff 25 0));
mkChunk (-80) (CVal 8 (SOff 24 0)); mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-64) (CVal 8 (SOff 22 0));
mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0));
mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Lemma ra_saved_of_chunks : forall E (m : word -> option byte),
Forall (chunk_ok src2segs E m (spZ regs0)) SAVE_CHUNKS ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs0 rr) ->
ra_saved_ok regs0 m.
Proof.
intros E m HC HE.
assert (X : forall off n (rr : reg), In (mkChunk off (CVal 8 (SOff n 0))) SAVE_CHUNKS -> Z.of_nat n = bv_unsigned rr ->
word_mem src2segs m (spZ regs0 + off) (bv_unsigned (getr regs0 rr))).
{ intros off n rr Hin Hn. apply val_mem_word_mem.
apply (val_of_chunk_ok src2segs E m (spZ regs0) off 8%N (SOff n 0) (bv_unsigned (getr regs0 rr)));
[exact (proj1 (Forall_forall _ _) HC _ Hin) | cbn [sv_denot]; rewrite Z.add_0_r, (HE n rr Hn), Z_to_bv_bv_unsigned; reflexivity | apply u64_range8 | cbn; lia]. }
intros j rr Hj. unfold YI4v.sp0.
destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]];
[ cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 0 + 1)) with (spZ regs0 + -8) by lia; apply (X (-8) 1%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 1 + 1)) with (spZ regs0 + -16) by lia; apply (X (-16) 8%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 2 + 1)) with (spZ regs0 + -24) by lia; apply (X (-24) 9%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 3 + 1)) with (spZ regs0 + -32) by lia; apply (X (-32) 18%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 4 + 1)) with (spZ regs0 + -40) by lia; apply (X (-40) 19%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 5 + 1)) with (spZ regs0 + -48) by lia; apply (X (-48) 20%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 6 + 1)) with (spZ regs0 + -56) by lia; apply (X (-56) 21%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 7 + 1)) with (spZ regs0 + -64) by lia; apply (X (-64) 22%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 8 + 1)) with (spZ regs0 + -72) by lia; apply (X (-72) 23%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 9 + 1)) with (spZ regs0 + -80) by lia; apply (X (-80) 24%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 10 + 1)) with (spZ regs0 + -88) by lia; apply (X (-88) 25%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 11 + 1)) with (spZ regs0 + -96) by lia; apply (X (-96) 26%nat); [cbv; tauto | reflexivity]
| cbn in Hj; injection Hj as <-; replace (spZ regs0 - 8 * (Z.of_nat 12 + 1)) with (spZ regs0 + -104) by lia; apply (X (-104) 27%nat); [cbv; tauto | reflexivity]
| destruct j; discriminate Hj ].
Qed.
Lemma src2_rgbadd_E1a :
K_M1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
rgba_pre API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
SR src2segs (cfg_at regs0 PC_E1 mem0 md0) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros KM1 PRE. unfold K_M1, cfg_at in KM1.
destruct PRE as (HPRE & Hinit & Hfrm & G10 & G11 & Hc8 & Hclo & Hchi & Hcfp & Hobj & Hcg & Hwf & HW & HHt & HNmax & Hbef & Hro & HBent).
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HAPv : OFF_apal = 158) by reflexivity.
assert (HN1 : 1 <= N).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite HNdef. clear - HW1 HH1. nia. }
assert (Hrin : In (r, RGB_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HBent | left; reflexivity]).
destruct (heap_blocks_range src2_msyms MR LAWS L A mem0 md0 r RGB_SIZE HH Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rrgb.
pose proof (Rrgb 7%nat W eq_refl) as RW. pose proof (Rrgb 8%nat H eq_refl) as RH. pose proof (Rrgb 11%nat cur eq_refl) as Rcur.
cbn in RW, RH, Rcur.
set (rgbv := [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur]) in *.
set (E := Ereg regs0 (map (Z_to_bv 64) rgbv ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs0 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error rgbv j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE39 : ew E 39 = Z_to_bv 64 W) by (apply (HV 7%nat); reflexivity).
assert (HE40 : ew E 40 = Z_to_bv 64 H) by (apply (HV 8%nat); reflexivity).
assert (HE43 : ew E 43 = Z_to_bv 64 cur) by (apply (HV 11%nat); reflexivity).
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (HRFCv : RGBFC_SIZE = 24) by reflexivity.
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = r) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : st_ok src2segs E ss_E1 (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom src2segs))).
{ unfold ss_E1. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack src2segs _ mem0 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | constructor].
+ eapply (region_ok_obj src2segs _ mem0 10 r); [exact HU10 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. unfold RGBA_FRAME, OFF_apal, RGB_SIZE in *. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HE39, HE40, HE43, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold RGB_SIZE in *. repeat split; lia. }
pose proof (journal_init src2_msyms MR RGBA_STK (FPfoot r g bef beffmt s N) L A regs0 mem0 md0 HPRE) as HJ.
change mem0 with (ms_mem (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom src2segs))) in HJ. fold sp0 in HJ.
unfold cfg_at. change (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom src2segs)) with (mkst regs0 (Z_to_bv 64 PC_E1) mem0 (seg_rom src2segs)).
jrun_to LAWS src2tbl_ok HS HJ src2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
cbn [ms_mem mkst] in HF, HG, HJ.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5136 <= a < sp0) -> mbyte src2segs (ms_mem ms) a = mbyte src2segs mem0 a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]. }
eapply SR_bind.
{ eapply (jmemset src2_msyms MR LAWS IMG src2_A_memset src2_memset_spec E _ _ RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 L A _ (sp0 - 4978) 0 768);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 4978) with (sp0 + -4978) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. eapply (present_grows _ _ _ HG).
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 44%nat regs2 mem2 MEMSET_CLOB E1_RETM [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 4978 <= a < sp0 - 4210) -> mbyte src2segs mem2 a = mbyte src2segs (ms_mem ms) a).
{ intros a Ha Hna. unfold mbyte. rewrite (Hout2 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
clear HF HG.
jrun LAWS src2tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5136 <= a < sp0) -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs mem0 a).
{ intros a Ha Hna. rewrite <- (K1 a Ha Hna), <- (K2 a Ha ltac:(lia)). mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]. }
clear HF HG K1 K2.
assert (HE' : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (havoc E 44 (map (getr regs2) MEMSET_CLOB)) n = getr regs0 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite ew_havoc_old by lia. apply HE. exact Hn. }
jbranch src2tbl HS.
{
jrun_to LAWS src2tbl_ok HS HJ2 PC_M1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG |- *.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 78988) with (Z_to_bv 64 PC_M1).
lazymatch goal with |- SR _ (mkCfg (mkst _ _ (ms_mem ?msx) _) _) _ =>
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5136 <= a < sp0) -> mbyte src2segs (ms_mem msx) a = mbyte src2segs mem0 a)
by (intros a Ha Hna; rewrite <- (K3 a Ha Hna); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]);
pose proof (st_region_chunks src2segs _ _ _ 0%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC0;
pose proof (st_region_chunks src2segs _ _ _ 1%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC1
end.
cbn [r_chunks] in HC0, HC1.
apply (KM1 _ L A). split.
{
split; [exact HJ2|]. split; [exact Hinit|]. split; [exact Hfrm|]. split; [exact Hra|]. split; [exact Hal16|]. split; [exact Htp|].
split; [exact (ra_saved_of_chunks _ _ HC0 HE')|].
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in Hi. unfold YI4v.sp0 in Hclo. apply K4; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, HU2; unfold sp, YI4v.sp0, RGBA_FRAME; f_equal; unfold sp0; lia |].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq; exact (HE 3%nat 3%bv eq_refl) |].
jreg HS (4%bv:reg) as Hq; rewrite Hq; exact (HE 4%nat 4%bv eq_refl). }
split; [jreg HS (19%bv:reg) as Hq; rewrite Hq, (HE 11%nat 11%bv eq_refl); exact G11|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [jreg HS (10%bv:reg) as Hq; rewrite Hq; exact HE39|].
split; [jreg HS (11%bv:reg) as Hq; rewrite Hq; exact HE40|].
split. { unfold slot. apply (proj1 (val_mem_word_mem src2segs _ _ _)). replace (sp regs0 + 136) with (sp0 + -5000) by (unfold sp, YI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok src2segs _ m sp0 (-5000) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-5000) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { unfold slot. apply (proj1 (val_mem_word_mem src2segs _ _ _)). replace (sp regs0 + 144) with (sp0 + -4992) by (unfold sp, YI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok src2segs _ m sp0 (-4992) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-4992) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply K4; lia. }
split. { eapply (cgif_at_kept _ _ g s N (blocks L A)); [| exact Hcg |].
- eapply Permutation_trans; [exact HBent|]. unfold BASE. apply Permutation_middle.
- intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem0 md0 b n HH Hbn) as [Hb0 Hb1]. apply K4; lia. }
exact HBent. }
jrun LAWS src2tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch src2tbl HS.
{
jrun LAWS src2tbl_ok HS HJ2.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG, HF0, HG0 |- *.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5136 <= a < sp0) -> mbyte src2segs (ms_mem msx) a = mbyte src2segs mem0 a)
by (intros a Ha Hna; rewrite <- (K3 a Ha Hna); mb_frame_g HF0; [mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia] | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia])
end.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh & Hl & _).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
unfold rgba_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists fx, L, A, (ms_regs msf), (ms_mem msf), md0, s, bef, beffmt, cur end.
split. { jreg HS (1%bv:reg) as Hq. rewrite Hq, (HE 1%nat 1%bv eq_refl), Hra. reflexivity. }
split; [exact Hfrm|]. split; [exact HJ2|].
split. { apply regs_preserved_intro_g.
- jreg HS (2%bv:reg) as Hq. rewrite Hq. exact (HE 2%nat 2%bv eq_refl).
- jreg HS (3%bv:reg) as Hq. rewrite Hq. exact (HE 3%nat 3%bv eq_refl).
- jreg HS (4%bv:reg) as Hq. rewrite Hq. exact (HE 4%nat 4%bv eq_refl).
- jreg HS (8%bv:reg) as Hq. rewrite Hq. exact (HE 8%nat 8%bv eq_refl).
- jreg HS (9%bv:reg) as Hq. rewrite Hq. exact (HE 9%nat 9%bv eq_refl).
- jreg HS (18%bv:reg) as Hq. rewrite Hq. exact (HE 18%nat 18%bv eq_refl).
- jreg HS (19%bv:reg) as Hq. rewrite Hq. exact (HE 19%nat 19%bv eq_refl).
- jreg HS (20%bv:reg) as Hq. rewrite Hq. exact (HE 20%nat 20%bv eq_refl).
- jreg HS (21%bv:reg) as Hq. rewrite Hq. exact (HE 21%nat 21%bv eq_refl).
- jreg HS (22%bv:reg) as Hq. rewrite Hq. exact (HE 22%nat 22%bv eq_refl).
- jreg HS (23%bv:reg) as Hq. rewrite Hq. exact (HE 23%nat 23%bv eq_refl).
- jreg HS (24%bv:reg) as Hq. rewrite Hq. exact (HE 24%nat 24%bv eq_refl).
- jreg HS (25%bv:reg) as Hq. rewrite Hq. exact (HE 25%nat 25%bv eq_refl).
- jreg HS (26%bv:reg) as Hq. rewrite Hq. exact (HE 26%nat 26%bv eq_refl).
- jreg HS (27%bv:reg) as Hq. rewrite Hq. exact (HE 27%nat 27%bv eq_refl). }
split; [exact Hinit|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply K4; lia. }
split. { eapply (cgif_at_kept _ _ g s N (blocks L A)); [| exact Hcg |].
- eapply Permutation_trans; [exact HBent|]. unfold BASE. apply Permutation_middle.
- intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem0 md0 b n HH Hbn) as [Hb0 Hb1]. apply K4; lia. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|]. exact HBent. }
jrun_to LAWS src2tbl_ok HS HJ2 PC_M1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG, HF0, HG0 |- *.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 78988) with (Z_to_bv 64 PC_M1).
lazymatch goal with |- SR _ (mkCfg (mkst _ _ (ms_mem ?msx) _) _) _ =>
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 5136 <= a < sp0) -> mbyte src2segs (ms_mem msx) a = mbyte src2segs mem0 a)
by (intros a Ha Hna; rewrite <- (K3 a Ha Hna); mb_frame_g HF0; [mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia] | rewrite HU2; lia | rewrite HU2; lia | rewrite HU10; lia]);
pose proof (st_region_chunks src2segs _ _ _ 0%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC0;
pose proof (st_region_chunks src2segs _ _ _ 1%nat _ 2%nat sp0 HS eq_refl eq_refl ltac:(ew_havoc; exact HU2)) as HC1
end.
cbn [r_chunks] in HC0, HC1.
apply (KM1 _ L A). split.
{
split; [exact HJ2|]. split; [exact Hinit|]. split; [exact Hfrm|]. split; [exact Hra|]. split; [exact Hal16|]. split; [exact Htp|].
split; [exact (ra_saved_of_chunks _ _ HC0 HE')|].
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in Hi. unfold YI4v.sp0 in Hclo. apply K4; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, HU2; unfold sp, YI4v.sp0, RGBA_FRAME; f_equal; unfold sp0; lia |].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq; exact (HE 3%nat 3%bv eq_refl) |].
jreg HS (4%bv:reg) as Hq; rewrite Hq; exact (HE 4%nat 4%bv eq_refl). }
split; [jreg HS (19%bv:reg) as Hq; rewrite Hq, (HE 11%nat 11%bv eq_refl); exact G11|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact G10|].
split; [jreg HS (10%bv:reg) as Hq; rewrite Hq; exact HE39|].
split; [jreg HS (11%bv:reg) as Hq; rewrite Hq; exact HE40|].
split. { unfold slot. apply (proj1 (val_mem_word_mem src2segs _ _ _)). replace (sp regs0 + 136) with (sp0 + -5000) by (unfold sp, YI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok src2segs _ m sp0 (-5000) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-5000) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { unfold slot. apply (proj1 (val_mem_word_mem src2segs _ _ _)). replace (sp regs0 + 144) with (sp0 + -4992) by (unfold sp, YI4v.sp0, RGBA_FRAME; unfold sp0; lia).
lazymatch goal with |- val_mem _ ?m _ _ _ =>
eapply (val_of_chunk_ok src2segs _ m sp0 (-4992) 8%N (SLit 0) 0); [exact (proj1 (Forall_forall _ _) HC1 (mkChunk (-4992) (CVal 8 (SLit 0))) ltac:(cbv; tauto)) | reflexivity | cbn; lia | cbn; lia] end. }
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply K4; lia. }
split. { eapply (cgif_at_kept _ _ g s N (blocks L A)); [| exact Hcg |].
- eapply Permutation_trans; [exact HBent|]. unfold BASE. apply Permutation_middle.
- intros b n i Hbn Hi. destruct (blocks_range _ _ LAWS L A mem0 md0 b n HH Hbn) as [Hb0 Hb1]. apply K4; lia. }
exact HBent.
Qed.
End d.
End c.
