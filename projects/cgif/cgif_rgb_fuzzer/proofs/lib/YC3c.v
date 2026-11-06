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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y YC2w YC37 YC3a YC3b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma val_mem_zero2 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 2 -> aview trasegs H m (a + i) = Some 0) -> val_mem trasegs (mrestrict H m) a 2 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte trasegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia.
Qed.
Lemma mbyte_zero_of_aview : forall H (m : word -> option byte) a,
aview trasegs H m a = Some 0 -> mbyte trasegs (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Hz. destruct (aview_byte trasegs H m a 0 Hz) as (b & Hb & Hv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_0_l by (vm_compute; discriminate). lia.
Qed.
Lemma U_sw_dest : forall E tm mp idl,
ew E 57 = Z_to_bv 64 tm -> ew E 35 = Z_to_bv 64 mp -> ew E 25 = Z_to_bv 64 idl ->
1 <= mp <= 2048 -> 0 <= idl <= 256 -> 0 <= tm -> tm + 2 * ((mp - 1) * idl) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SLL (SMdw M_MUL (SOff 35 (-1)) (SOff 25 0)) (SLit 1))) = tm + 2 * ((mp - 1) * idl).
Proof.
intros E tm mp idl H1 H35 H25 Hmp Hidl Htm Hhi.
assert (Hp : 0 <= (mp - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
apply (U_add_small E); [apply (U_atom E 57 tm H1); lia | | lia | lia | lia].
apply (U_sll1_small E); [apply (U_mulw_row E 35 25 mp idl H35 H25); lia | lia | lia].
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Let HBcode := tl_code B TL.
Lemma tmiss_sw : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps B cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
nth (Z.to_nat q) (la_LI X) 0 <> 0 -> z_gp cx = as_gp B -> z_tp cx = as_tp B ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)) mdT)
(tmiss_tail_post B cx lyc Sc W memc mdc ly7 S7 W7 memT X s1).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFC & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HCpix & HS48) Hdp HLM HLI Hzgp Hztp.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFC HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HCpix HS48)
as (E & more & HE0 & HS & HENV & Hmap & Hsw & Hfirst & _).
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
assert (Hmc : mc_of dp vLM vLI = MC_sw).
{ unfold mc_of. replace (dp =? 4096) with false by (symmetry; apply Z.eqb_neq; lia).
fold vLM in HLM. fold vLI in HLI. rewrite (proj2 (Z.eqb_eq _ _) HLM). replace (vLI =? 0) with false by (symmetry; apply Z.eqb_neq; exact HLI). reflexivity. }
rewrite Hmc in HS, HENV, Hmap, Hsw, Hfirst. cbn [tmiss_J is_map is_sw is_first] in HENV, Hmap, Hsw, Hfirst.
destruct HENV as (HE2 & HE8 & HE27 & HE25 & HE53 & HE54 & HE56 & HE55 & HE57 & HE59 & HE58 & HE32 & HE33 & HE34 & HE35 & HE37 & HE23 & HE15 & HE71 & HE72 & HE73 &
HE60 & HE64 & HE65 & HE66 & HE68 & HE69 & HE3 & HE4 & HE70 & HE5 & HE24).
specialize (Hsw eq_refl). destruct Hsw as (Hrow0 & _ & HJsz & Hrow1 & _ & _ & _). clear Hmap Hfirst.
remember ((mp - 1) * z_idl cx + c) as J eqn:HJdef.
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI. fold vLI in HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM. fold vLM in HvLM.
destruct HT as (ATI & ALM & ALI & ATM).
unfold z_tisz, z_tmsz in *.
Local Ltac tm_sep HSEP :=
match goal with
| |- context [z_ctx _] => septac HSEP 5%nat 6%nat
| |- context [z_ld _] => septac HSEP 0%nat 5%nat
| |- context [z_li _] => septac HSEP 4%nat 5%nat
| |- context [z_lm _] => septac HSEP 2%nat 5%nat
| |- context [z_lc _] => septac HSEP 3%nat 5%nat
| |- context [z_ti _] => septac HSEP 1%nat 5%nat
| |- context [z_img _] => septac HSEP 5%nat 7%nat
| _ => idtac
end; lia.
assert (Hrow2 : 2 * ((mp - 1) * z_idl cx) + 2 * z_idl cx <= 4098 * z_idl cx) by lia.
set (m := mrestrict (w_H W7) memT) in *.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trasegs))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx));
try (oblk HJ HBi HE70 HE27 (z_img cx + s1)); try (oblk HJ HBlm HE65 HE27 (z_lm cx + 2 * q)); try (oblk HJ HBli HE64 HE27 (z_li cx + 2 * q)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 65%nat (z_lm cx + 2 * q) HE65 Alm HBlm. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (z_lm cx + 2 * q, z_lm cx + 2 * q + 2); (0, 0); (0, 0)].
rename Hout into Hout1. clear HF.
remember ((mp - 1) * z_idl cx) as P eqn:HPdef.
rregU HS (10%bv : bv 5) (z_tm cx + 2 * P)
ltac:(rewrite HPdef; apply (U_sw_dest _ (z_tm cx) mp (z_idl cx)); [eatom AG HE57 | eatom AG HE35 | eatom AG HE25 | lia | lia | lia | lia]) Ra0.
rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset).
try match goal with H : mem_grows _ _ |- _ => clear H end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) _ _ _ lyc Sc W memc mdc _
ly7 S7 _ 7 (z_tm cx + 2 * P) 0 (2 * z_idl cx) (-320) (Z_to_bv 64 0x8a0b8) HJ) end.
- exact Ra0.
- rewrite Ra1. reflexivity.
- rewrite Ra2, HE37. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ. rewrite Rsp, HE2, unsigned_lit_small by lia. lia.
- reflexivity.
- lia.
- unfold ESTACK. lia.
- rewrite Rgp, HE3, Hzgp. reflexivity.
- rewrite Rtp, HE4, Hztp. reflexivity.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (z_tm cx + (a - z_tm cx)) by lia; apply Atm; [exact HBtm | lia] | unfold ESTACK; lia].
- eapply (amem_range_of_block trasegs B LAWS ly7 S7 _ _ _ (z_tm cx) (4098 * z_idl cx) _ _ (proj1 HJ) HBtm); lia.
- eapply (range_addressable_of_block trasegs B LAWS ly7 S7 _ _ _ (z_tm cx) (4098 * z_idl cx) _ _ (proj1 HJ) HBtm); lia.
- intros _. eapply (shadow_hull_vis_of_block trasegs B LAWS ly7 S7 _ _ _ (z_tm cx) (4098 * z_idl cx) _ _ (proj1 HJ) HBtm); lia.
- exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr; [lia | revert Ha; tm_sep HSEP | unfold ESTACK; lia]
| exact Hpres2 ]).
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 320)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv20 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27);
assert (HEv25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (HEv24 : ew Ev 23 = Z_to_bv 64 s1) by (rewrite (AG 23%nat) by lia; exact HE23)
end.
clear HE2 HE8 HE27 HE25 HE23.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_tm cx) _ (proj1 HJ2) HBtm) as (_ & _ & _ & _ & Htmpres2 & _).
assert (Vz : val_mem trasegs (mrestrict (w_H W7) mem2) (z_tm cx + 2 * J) 2 0).
{ apply val_mem_zero2. intros i Hi. replace (z_tm cx + 2 * J + i) with (z_tm cx + 2 * P + (2 * c + i)) by lia.
rewrite (Heff (2 * c + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 68%nat) 0 2 0 2 [YQ0b.mkChunk 0 (CVal 2 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite HE68, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Htmpres2 (z_tm cx + 2 * J + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs Ex _ (z_tm cx + 2 * J) 0 2 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vz])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite HE68, HEv8, HEv2, HE60, HE64, HE65, HE66, HE70, !unsigned_lit_small by lia; repeat split; tm_sep HSEP)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 27%nat.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 565432) mem2 (seg_rom trasegs))) in HJ2.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK Bspan PC_HEAD; try (oblk HJ2 HBtm HE68 HEv20 (z_tm cx + 2 * J)); try (oblk HJ2 HBlm HE65 HEv20 (z_lm cx + 2 * q));
try (oblk HJ2 HBg HEv8 HEv20 (z_ctx cx)).
{ awr_tmp 68%nat (z_tm cx + 2 * J) HE68 Atm HBtm.
awr_tmp 8%nat (z_ctx cx) HEv8 Actx HBg.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HEv2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 65%nat (z_lm cx + 2 * q) HE65 Alm HBlm. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI (updn LM (Z.to_nat q) mp) LI (updn (zero_range TM (Z.to_nat P) (Z.to_nat (z_idl cx))) (Z.to_nat J) dp)
s1 (lp + 1) (dp + 1) (mp + 1) (Cn + 1) R) end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ2|].
lazymatch type of HFr with frame_of ?Ef _ ?m2r _ =>
hout HFr Ef m2r [(z_tm cx + 2 * J, z_tm cx + 2 * J + 2); (z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56);
(z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (z_lm cx + 2 * q, z_lm cx + 2 * q + 2); (0, 0); (0, 0)] end.
rename Hout into Hout2.
lazymatch type of Hout1 with forall a, _ -> _ -> mbyte _ ?m1r a = mbyte _ _ a =>
lazymatch type of Hout2 with forall a, _ -> _ -> mbyte _ _ a = mbyte _ ?m2r a =>
assert (Hms : forall a, 0 <= a < 2 ^ 64 -> ~ (z_tm cx + 2 * P <= a < z_tm cx + 2 * P + 2 * z_idl cx) ->
~ (z_sp cx - 320 - ESTACK <= a < z_sp cx - 320) -> mbyte trasegs m2r a = mbyte trasegs m1r a)
by (intros a Ha Hn1 Hn2; apply (mbyte_of_aview trasegs); apply Hfr; [exact Ha | exact Hn1 | replace (z_sp cx + -320) with (z_sp cx - 320) by lia; exact Hn2]);
assert (Hz2 : forall a, z_tm cx + 2 * P <= a < z_tm cx + 2 * P + 2 * z_idl cx -> mbyte trasegs m2r a = Some (Z_to_bv 8 0))
by (intros a Ha; replace a with (z_tm cx + 2 * P + (a - (z_tm cx + 2 * P))) by lia; apply mbyte_zero_of_aview;
rewrite (Heff (a - (z_tm cx + 2 * P))) by lia; reflexivity)
end end.
unfold ESTACK in Hms. clear Hfr Heff.
assert (Hall : forall a, 0 <= a < 2 ^ 64 ->
outsideA [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (z_lm cx + 2 * q, z_lm cx + 2 * q + 2); (0, 0); (0, 0)] a ->
~ (z_tm cx + 2 * P <= a < z_tm cx + 2 * P + 2 * z_idl cx) -> ~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320) ->
~ (z_tm cx + 2 * J <= a < z_tm cx + 2 * J + 2) ->
mbyte trasegs ltac:(lazymatch type of Hout2 with forall a, _ -> _ -> mbyte _ ?m3r a = _ => exact m3r end) a = mbyte trasegs m a).
{ intros a Ha Hw1 Hr Hsc Hcl. rewrite Hout2; [| exact Ha | cbn; cbn in Hw1; tauto]. rewrite Hms by assumption. apply Hout1; [exact Ha | exact Hw1]. }
split; [intros a Ha; apply Hall; [lia | cbn; repeat split; lia | lia | lia | lia]|].
cellv HS 0%nat 68%nat (z_tm cx + 2 * J) HE68 (SOff 34 0) dp HE34 Vtm.
cellv HS 5%nat 65%nat (z_lm cx + 2 * q) HE65 (SOff 35 0) mp HE35 Vlm.
destruct (inv_switch (z_idl cx) (z_nP cx) Hidl _ q c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq Hc
ltac:(cbn [la_LI]; exact HLI) ltac:(cbn [la_LM]; exact HLM)) as (HI' & _ & _).
cbn [st_switch la_mp] in HI'. rewrite <- HPdef in HI'. rewrite <- HJdef in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_afterI E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] end. }
split; [genM 1%nat HS HEv8 HG ltac:(fun a Ha => apply Hall; [lia | cbn; septac HSEP 0%nat 6%nat; septac HSEP 2%nat 6%nat; repeat split; lia | septac HSEP 5%nat 6%nat; lia | lia | septac HSEP 5%nat 6%nat; lia])
(z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 34 1) (dp + 1) HE34 (SOff 35 1) (mp + 1) HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hall; [lia | cbn | septac HSEP 1%nat 5%nat; lia | lia | septac HSEP 1%nat 5%nat; lia]. septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. septac HSEP 1%nat 2%nat. repeat split; lia.
- eapply arr16_upd; [exact ALM | lia | exact HqLM | lia | exact Vlm |].
intros a Ha Hna. rewrite LenLM in Ha. cbn in Ha.
apply Hall; [lia | cbn | septac HSEP 2%nat 5%nat; lia | lia | septac HSEP 2%nat 5%nat; lia]. septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. repeat split; first [exact Hna | lia].
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hall; [lia | cbn | septac HSEP 4%nat 5%nat; lia | lia | septac HSEP 4%nat 5%nat; lia]. septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. septac HSEP 2%nat 4%nat. repeat split; lia.
- assert (ATM2 : arr16 trasegs ltac:(lazymatch type of Hms with forall a, _ -> _ -> _ -> mbyte _ ?m2r a = _ => exact m2r end) (z_tm cx)
(zero_range TM (Z.to_nat P) (Z.to_nat (z_idl cx)))).
{ eapply arr16_zero_range; [exact ATM | lia | lia | rewrite LenTM, <- Z2Nat.inj_add by lia; apply (proj1 (Z2Nat.inj_le (P + z_idl cx) (2049 * z_idl cx) ltac:(lia) ltac:(lia))); lia | |].
- intros a Ha. apply Hz2. lia.
- intros a Ha Hna. rewrite LenTM, Z2Nat.id in Ha by lia.
rewrite Hms; [| lia | first [exact Hna | lia] | lia]. apply Hout1; [lia | cbn]. septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. septac HSEP 2%nat 5%nat. repeat split; lia. }
eapply arr16_upd; [exact ATM2 | lia | rewrite zero_range_length, LenTM; apply (proj1 (Z2Nat.inj_lt J (2049 * z_idl cx) ltac:(lia) ltac:(lia))); lia | lia | exact Vtm |].
intros a Ha Hna. rewrite zero_range_length, LenTM, Z2Nat.id in Ha by lia.
apply Hout2; [lia | cbn]. septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. septac HSEP 2%nat 5%nat. repeat split; first [exact Hna | lia]. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
End S.
End d.
