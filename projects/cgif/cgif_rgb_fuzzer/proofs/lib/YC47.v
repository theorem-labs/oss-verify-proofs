(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p YC46 YC4c YC4g YC4h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma denot_add_atoms : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (a + b).
Proof.
intros E n1 n2 a b H1 H2 Ha Hb Hab. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 a H1), (U_atom E n2 b H2) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma aview_kept_ro : forall E rs H (m m' : word -> option byte),
(forall r, In r rs -> YQ0b.r_whi r <= YQ0b.r_wlo r) ->
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> aview trasegs H m' a = aview trasegs H m a.
Proof.
intros E rs H m m' Hro HF a Ha. apply (aview_kept_out E rs H m m' HF a Ha).
intros (r & Hin & Hr). pose proof (Hro r Hin). lia.
Qed.
Lemma regions_kept_out2 : forall E H (m m2 : word -> option byte) lo hi lo2 hi2 rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (lo2 <= a < hi2) -> aview trasegs H m2 a = aview trasegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= lo \/ hi <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r) /\
(base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= lo2 \/ hi2 <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r)) rs ->
Forall (region_kept trasegs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi lo2 hi2 rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3 & H4). split; intros a Ha.
- apply (mbyte_of_aview trasegs). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma denot_mul_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (h * w).
Proof.
intros E nh nw h w Hh Hw Rh Rw. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 32 - 1) * (2 ^ 32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh h Hh) by lia. rewrite (U_atom E nw w Hw) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma il_denot_shadow : forall E n b p k,
ew E n = Z_to_bv 64 p -> ew E b = Z_to_bv 64 SB -> 0 <= p -> p + k < 2 ^ 47 -> 0 <= k ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (SB + (p + k) / 8).
Proof.
intros E n b p k Hn Hb Hp Hk Hk0. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom_off E n p k Hn) by lia. rewrite (U_atom E b SB Hb) by (unfold SB; lia).
rewrite (zcanon_id 3) by (rewrite M64_val; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + k) / 8)) by (rewrite M64_val; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (0 <= (p + k) / 8) by (apply Z.div_pos; lia). assert ((p + k) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite (Z.add_comm SB). apply zcanon_id. rewrite M64_val. unfold SB. lia.
Qed.
Lemma il_src_val : forall img i w, 0 <= img -> 0 <= i < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> img + i * w < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 img) (mul_div M_MUL (Z_to_bv 64 i) (Z_to_bv 64 w)) = Z_to_bv 64 (img + i * w).
Proof.
intros img i w Himg Hi Hw Hs. rewrite zmd64_sound. unfold zmd64. cbn [zmd_raw].
rewrite (zcanon_id i), (zcanon_id w) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; nia). apply alu64_add_lit.
Qed.
Section IL.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Definition ILN_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 27; 28; 29; 30; 31]%bv.
Definition ILN_KEPT' : list (bv 5) := [2; 3; 4; 8; 9; 20; 23; 25]%bv.
Lemma iln_clob_cases : forall r : bv 5, reg_in r ILN_CLOB = false ->
r = 0%bv \/ r = 19%bv \/ r = 21%bv \/ r = 22%bv \/ r = 24%bv \/ r = 26%bv \/ In r ILN_KEPT'.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity
| right; right; right; right; left; reflexivity | right; right; right; right; right; left; reflexivity
| vm_compute in Hr; discriminate | right; right; right; right; right; right; cbv; tauto] |]). destruct Hin.
Qed.
Definition sh_of (n : nat) (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff 32 0).
Definition iln_regions : smem :=
[ YQ0b.mkRegion (Some 25%nat) 0 16 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 12 (CVal 2 (SOff 34 0)); YQ0b.mkChunk 14 (CVal 2 (SOff 35 0))] ].
Lemma iln_regions_ro : forall r, In r iln_regions -> YQ0b.r_whi r <= YQ0b.r_wlo r.
Proof. intros r [<- | []]. cbn. lia. Qed.
Definition iln_regs :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 21%bv (SOff 25 12)) 22%bv (SOff 25 14)) 26%bv (sh_of 25 0)) 19%bv (sh_of 25 12)) 24%bv (sh_of 25 14).
Definition iln_facts : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (27%nat, HPTR 0); (25%nat, HPTR 3); (33%nat, HPTR 0);
(34%nat, mkAF 1 65535 0); (35%nat, mkAF 1 65535 0); (18%nat, mkAF 0 65535 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_iln (pc : Z) : sstate := mkSS pc iln_regs iln_regions None iln_facts.
Ltac iln_obl HJx Hx25 Hx32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 25 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 25 (cfp + 8) c Hx25) by lia | rewrite (U_atom Ex 25 (cfp + 8) Hx25) by lia ];
eapply (obl_of_range trasegs _ _ Ex (SOff 32 0) _ len cfp 40);
[ eapply (range_addressable_entry_frame trasegs _ LAWS); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & Hrg & Hxr); cbn [In] in Hrg; destruct Hrg as [<- | []]; cbn [fst snd] in Hxr; clear - Hxr Hrh C2 C3; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; change (req_size RAW_SIZE) with 48 in *; lia
| exact HAR0 | exact HRA ]
| rewrite (U_atom Ex 32 SB Hx32); [reflexivity | unfold SB; lia] | lia | lia ] end.
Lemma ra_iln1 : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 8 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 8 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR trasegs B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview trasegs (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x88ed8) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 0x88f44) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 8 * (mm - 1) < h /\ h <= i + 8 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 11 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds trasegs B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok trasegs E (ss_iln 0x88ed8) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x88ed8) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_iln.
apply (rn_st_ok_any E 0x88ed8 _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
aj_run_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent trasegs). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS.
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mm a = aview trasegs (w_H W) memc a) ->
val_mem trasegs (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x88ed8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 8) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha Hna Hnb).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x88f44; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (11%bv : bv 5) NXH. rewrite G35 in NXH.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ra_iln2 : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 8 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 8 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR trasegs B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview trasegs (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x88f50) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 0x88fdc) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 8 * (mm - 1) < h /\ h <= i + 8 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds trasegs B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok trasegs E (ss_iln 0x88f50) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x88f50) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_iln.
apply (rn_st_ok_any E 0x88f50 _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
aj_run_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent trasegs). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS.
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mm a = aview trasegs (w_H W) memc a) ->
val_mem trasegs (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x88f50; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 8) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha Hna Hnb).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x88fdc; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (10%bv : bv 5) NXH. rewrite G35 in NXH.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ra_iln3 : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 4 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 4 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR trasegs B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview trasegs (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x88fe8) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 0x89060) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 4 * (mm - 1) < h /\ h <= i + 4 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds trasegs B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok trasegs E (ss_iln 0x88fe8) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x88fe8) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_iln.
apply (rn_st_ok_any E 0x88fe8 _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
aj_run_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent trasegs). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS.
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mm a = aview trasegs (w_H W) memc a) ->
val_mem trasegs (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 4))) with (U Ec (SOff 18 4)) in Hc.
rewrite (U_atom_off Ec 18 i 4 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x88fe8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 4) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha Hna Hnb).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 4))) with (U Ec (SOff 18 4)) in Hc.
rewrite (U_atom_off Ec 18 i 4 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x89060; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (10%bv : bv 5) NXH. rewrite G35 in NXH.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ra_iln4 : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 2 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 2 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR trasegs B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview trasegs (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem trasegs (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 0x8906c) memc (seg_rom trasegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 0x890d8) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 2 * (mm - 1) < h /\ h <= i + 2 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds trasegs B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok trasegs E (ss_iln 0x8906c) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8906c) memc (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_iln.
apply (rn_st_ok_any E 0x8906c _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val trasegs E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
aj_run_tok tratbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent trasegs). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS.
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) mm a = aview trasegs (w_H W) memc a) ->
val_mem trasegs (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem trasegs (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
srr_branch_with tratbl_lib_ok HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 2))) with (U Ec (SOff 18 2)) in Hc.
rewrite (U_atom_off Ec 18 i 2 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x8906c; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 2) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha Hna Hnb).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 2))) with (U Ec (SOff 18 2)) in Hc.
rewrite (U_atom_off Ec 18 i 2 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
aj_run_to tratbl_lib_ok HS HJ2 0x890d8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
rreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
rreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
rreg HS (10%bv : bv 5) NXH. rewrite G35 in NXH.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg trasegs _ _ _ 0%bv HS), (st_ok_reg trasegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2). apply Hpres2. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
End IL.
End d.
