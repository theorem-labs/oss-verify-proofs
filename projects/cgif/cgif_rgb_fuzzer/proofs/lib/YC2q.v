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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_freeFrame : Z := 0x88060.
Definition FF_STK : Z := 32 + ASTACK.
Definition FRAME_OBJ : Z := 40.
Definition ff_blocks (fp img lpal attr N nlp : Z) : list (Z * Z) :=
(fp, FRAME_OBJ) :: (img, N) :: (if Z.land attr 1 =? 0 then [] else [(lpal, 3 * nlp)]).
Section FF.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition ff_regions : smem :=
[ stack_region 32; got_region; bcell_region 35;
YQ0b.mkRegion (Some 10%nat) 0 FRAME_OBJ 0 0
[YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 16 (CVal 1 (SOff 34 0))] ].
Definition ff_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 4096 140737479966720 4);
(34%nat, mkAF 0 255 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_ff : sstate := mkSS A_freeFrame sr_atoms ff_regions None ff_facts.
Definition ff_SH : list shent := [ mkSHE 10 0 FRAME_OBJ ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ff_extra (lpal img attr : Z) : list word := map (Z_to_bv 64) [lpal; img; attr mod 256; SB].
Lemma ff_entry : forall W ly S regs mem md ch fp lpal img attr N nlp rest,
afn_pre trasegs B FF_STK ly S W regs mem md ch ->
getr regs 10 = w64 fp ->
val_mem trasegs (mrestrict (w_H W) mem) fp 8 lpal ->
val_mem trasegs (mrestrict (w_H W) mem) (fp + 8) 8 img ->
val_mem trasegs (mrestrict (w_H W) mem) (fp + 16) 4 attr ->
0 <= lpal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 -> 0 <= N ->
Permutation (ablocks B ly S) (ff_blocks fp img lpal attr N nlp ++ rest) ->
st_ok trasegs (Ereg regs (ff_extra lpal img attr)) ss_ff
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_freeFrame) mem (seg_rom trasegs)))
/\ sh_ok trasegs Bx ff_SH (Ereg regs (ff_extra lpal img attr)) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch fp lpal img attr N nlp rest HPRE H10 Mlpal Mimg Mattr Rlpal Rattr RN HPerm.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : FF_STK = 16416) by reflexivity.
assert (Hinf : In (fp, FRAME_OBJ) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
assert (Hini : In (img, N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md fp FRAME_OBJ HAR Hinf) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfb & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_img _ _ _ _ _ _ fp FRAME_OBJ HAR Hinf) as Hfh_img.
destruct (al_blocks _ _ LAWS ly S W mem md img N HAR Hini) as (Hi16 & Hi4096 & Hiceil & Hih_ia & _ & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img N HAR Hini) as Hih_img.
change (req_size FRAME_OBJ) with 40 in *. pose proof (req_size_pos N RN) as HrN.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs (ff_extra lpal img attr)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 fp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (ff_extra lpal img attr) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
cbn [Nat.add nth ff_extra map] in E32, E33, E34, E35. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
split.
- unfold ss_ff. apply (entry_st_ok_full trasegs); change (Ereg regs (ff_extra lpal img attr)) with E.
+   apply regs_ok_Ereg.
+   vm_compute. reflexivity.
+
unfold ff_regions, stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
*   cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
*   cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs E _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kgot).
*   cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs E _ 0 696760 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kcell).
*   rewrite (VB 10%nat fp E10) by lia. unfold FRAME_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val trasegs E _ fp 0 8 _ lpal); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mlpal.
-- apply (chunk_ok_val trasegs E _ fp 8 8 _ img); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mimg].
-- apply (chunk_ok_val trasegs E _ fp 16 1 _ (attr mod 256)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_byte0 trasegs _ _ _ _ Mattr).
+
apply pairwise_disjoint_of_extents. unfold ff_regions, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat fp E10) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, FRAME_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hfceil Hfh Hfh_img Hf4096 C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+
split; [|split; [exact I | exact I]].
cbn [ff_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hfceil Hfh Hfh_img Hf4096 Hf16 Hi16 Hi4096 Hiceil Hih Hih_img HrN Hal16 Hab C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
-
unfold sh_ok, ff_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS ly S W mem md E Bx 10 fp FRAME_OBJ 0 FRAME_OBJ HAR Hinf).
+ unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size FRAME_OBJ) with 40. unfold FRAME_OBJ. lia.
Qed.
Definition ff_post (regs : bvmap 5 word) ly S W mem md (FP rest : list (Z * Z)) : world trasegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B FF_STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' 3 /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest.
Lemma ff_tail : forall W ly S regs mem md ch fp img lpal attr N nlp rest Wt regsT memT lyt St mdt kt,
afn_pre trasegs B FF_STK ly S W regs mem md ch ->
In (call_trace0 (pc_free_ra0 Tra_code) regs ch) (as_universe B) ->
vev S + 3 <= VEV_MAX ->
ajournal trasegs B FF_STK (spZ regs) (ablocks_fp (ff_blocks fp img lpal attr N nlp)) ly S W mem md [] lyt St Wt memT mdt kt ->
kt <= 2 ->
Permutation (ablocks B lyt St) ((fp, FRAME_OBJ) :: rest) ->
aregs_preserved regs regsT -> getr regsT 10 = w64 fp -> getr regsT 1 = getr regs 1 ->
SRr trasegs Wt (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom trasegs)) mdt)
(ff_post regs ly S W mem md (ablocks_fp (ff_blocks fp img lpal attr N nlp)) rest).
Proof.
intros W ly S regs mem md ch fp img lpal attr N nlp rest Wt regsT memT lyt St mdt kt
HPRE HU3 Hev HJ Hkt HPermR HP Ha0 Hra1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARt & Hly & _ & _ & _ & _ & Hnev & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (FFS : FF_STK = 16416) by reflexivity.
assert (HinfT : In (fp, FRAME_OBJ) (ablocks B lyt St)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermR|]. left. reflexivity. }
assert (P2 : getr regsT 2 = getr regs 2) by (apply (HP 2); left; reflexivity).
assert (P3 : getr regsT 3 = getr regs 3) by (apply (HP 3); right; left; reflexivity).
assert (P4 : getr regsT 4 = getr regs 4) by (apply (HP 4); right; right; left; reflexivity).
assert (P8 : getr regsT 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
eapply SRr_mono.
{ eapply (aj_free_at trasegs B LAWS tra_segs_low errno_low ML AFREE Wt regsT memT FF_STK (spZ regs) _ ly S W mem md [] lyt St mdt kt
fp FRAME_OBJ 0 (getr regs 1) ch HJ HinfT Ha0).
- unfold spZ. rewrite P2. lia.
- reflexivity. - lia. - unfold FF_STK; lia.
- rewrite P3; exact Hgp. - rewrite P4; exact Htp.
- exact Hra1. - exact Hra. - lia.
- eapply (achain_chain_pre lyt _ (spZ regs) (s0Z regs) ch).
+ apply (achain_ly_top ly lyt). { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET. }
eapply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
intros a Ha. apply G1; lia.
+ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite P2. change (bv_unsigned (getr regs 2)) with (spZ regs). lia.
+ unfold s0Z. rewrite P8. reflexivity.
+ unfold raZ. rewrite Hra1. exact Hra4.
- unfold call_trace0, raZ in *. rewrite Hra1, HBcode. exact HU3.
- intros _ i Hi. apply (inFP_ablocks_fp _ fp FRAME_OBJ i); [left; reflexivity | exact Hi]. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1' & l2' & Ebl' & Ebl2') & _ & _).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|].
split; [eapply (ajournal_mono_k trasegs B); [exact HJ3 | lia]|].
split; [eapply aregs_preserved_trans; [exact HP | exact HP3]|].
rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (fp, FRAME_OBJ)). rewrite <- Ebl'.
apply Permutation_sym. exact HPermR.
Qed.
Theorem tra_freeFrame : forall W ly S regs mem md ch fp lpal img attr N nlp rest,
afn_pre trasegs B FF_STK ly S W regs mem md ch ->
vev S + 3 <= VEV_MAX ->
getr regs 10 = w64 fp ->
val_mem trasegs (mrestrict (w_H W) mem) fp 8 lpal ->
val_mem trasegs (mrestrict (w_H W) mem) (fp + 8) 8 img ->
val_mem trasegs (mrestrict (w_H W) mem) (fp + 16) 4 attr ->
0 <= lpal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 -> 0 <= N -> 0 <= nlp ->
Permutation (ablocks B ly S) (ff_blocks fp img lpal attr N nlp ++ rest) ->
In [pc_free_ra0 Tra_code; 0x880a0] (as_universe B) ->
In [pc_free_ra0 Tra_code; 0x880d8] (as_universe B) ->
In (call_trace0 (pc_free_ra0 Tra_code) regs ch) (as_universe B) ->
SRr trasegs W (cfg_at trasegs A_freeFrame regs mem md)
(ff_post regs ly S W mem md (ablocks_fp (ff_blocks fp img lpal attr N nlp)) rest).
Proof.
intros W ly S regs mem md ch fp lpal img attr N nlp rest HPRE Hev H10 Mlpal Mimg Mattr Rlpal Rattr RN Rnlp HPerm HU1 HU2 HU3.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct (ff_entry W ly S regs mem md ch fp lpal img attr N nlp rest HPRE H10 Mlpal Mimg Mattr Rlpal Rattr RN HPerm) as [HS SHOK].
pose proof (ajournal_init trasegs B FF_STK (ablocks_fp (ff_blocks fp img lpal attr N nlp)) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : FF_STK = 16416) by reflexivity.
remember (Ereg regs (ff_extra lpal img attr)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 fp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 lpal) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (attr mod 256)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ff_extra lpal img attr)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_freeFrame) with (Z_to_bv 64 A_freeFrame).
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan.
{ awr_ok_tac. exact Usp. }
assert (Hini : In (img, N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
assert (Hinf : In (fp, FRAME_OBJ) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md fp FRAME_OBJ HAR Hinf) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & _ & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_img _ _ _ _ _ _ fp FRAME_OBJ HAR Hinf) as Hfh_img.
change (req_size FRAME_OBJ) with 40 in Hfceil, Hfh, Hfh_img.
pose proof (sep_blocks_perm trasegs B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size FRAME_OBJ) with 40 in Hd1.
pose proof (proj1 HJ) as HARc.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free trasegs B LAWS Hsegs errno_low ML AFREE W E _ ms FF_STK (spZ regs) _ ly S W mem md [] ly S _ 0
img N (-32) (ew E 2) (Z_to_bv 64 0x880a0) []);
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ | exact Hini
| rewrite R10, E33; reflexivity
| exact (st_ok_restrict_reg trasegs (w_H W) E _ _ 2%bv HS)
| reflexivity | exact Usp | reflexivity | lia | unfold FF_STK; lia
| rewrite R3, E3; exact Hgp | rewrite R4, E4; exact Htp
| exact R1 | vm_compute; reflexivity | lia
|   eapply (achain_chain_pre ly _ (spZ regs - 32) fp []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, E10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
|   rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU1
| intros _ i Hi; apply (inFP_ablocks_fp _ img N i); [right; left; reflexivity | exact Hi] ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) ((fp, FRAME_OBJ) :: (if Z.land attr 1 =? 0 then [] else [(lpal, 3 * nlp)]) ++ rest)).
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (img, N)). rewrite <- Ebl.
apply Permutation_sym. eapply Permutation_trans; [exact HPerm|]. apply perm_swap. }
assert (Hinf2 : In (fp, FRAME_OBJ) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. left. reflexivity. }
jafter_call HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJ | exact Usp | lia | unfold FF_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val trasegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgot) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | lia].
- apply (region_kept_val trasegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcell) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_aj trasegs B); [exact HK | rewrite E10; apply unsigned_lit_small; lia | exact Hinf | lia
| change (req_size FRAME_OBJ) with 40; unfold FRAME_OBJ; lia | lia | unfold FRAME_OBJ; intros a Ha HE; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS.
assert (OLD2 : forall n, (n < 36)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (ff_extra lpal img attr)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2'.
assert (F10 : ew E2' 10 = Z_to_bv 64 fp) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F35 : ew E2' 35 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact E35).
assert (F32 : ew E2' 32 = Z_to_bv 64 lpal) by (rewrite OLD2 by (cbv; lia); exact E32).
assert (F34 : ew E2' 34 = Z_to_bv 64 (attr mod 256)) by (rewrite OLD2 by (cbv; lia); exact E34).
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (F3 : ew E2' 3 = getr regs 3) by (rewrite OLD2 by (cbv; lia); exact E3).
assert (F4 : ew E2' 4 = getr regs 4) by (rewrite OLD2 by (cbv; lia); exact E4).
assert (F8 : ew E2' 8 = getr regs 8) by (rewrite OLD2 by (cbv; lia); exact E8).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
assert (SHOK : sh_ok trasegs Bx ff_SH E2' (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, ff_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 fp FRAME_OBJ 0 FRAME_OBJ HAR2 Hinf2).
+ unfold U, Bx. cbn [sv_denot]. rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size FRAME_OBJ) with 40. unfold FRAME_OBJ. lia. }
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan.
{ awr_ok_tac. exact Usp2. }
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
srr_branch_tok tratbl_lib_ok HS SHOK Bspan.
-
rewrite branch_eq_U, U_and_lit, (U_atom E2' 34 (attr mod 256) F34), U_lit, land_mod256_1 in Hc by lia.
rewrite Hc in HPerm2. cbn [app] in HPerm2.
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340224 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
eapply (ff_tail W ly S regs mem md ch fp img lpal attr N nlp rest); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm2 | | |].
+ eapply (aregs_preserved_of_st_ok trasegs _ E2' _ _ regs (ff_extra lpal img attr) HS); [exact HAE2 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, F10. reflexivity.
+ cbn [ms_regs]. rewrite R1, F1. reflexivity.
-
rewrite branch_eq_U, U_and_lit, (U_atom E2' 34 (attr mod 256) F34), U_lit, land_mod256_1 in Hc by lia.
rewrite Hc in HPerm2. cbn [app] in HPerm2.
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
assert (Hinl : In (lpal, 3 * nlp) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. right. left. reflexivity. }
pose proof (sep_blocks_perm trasegs B LAWS ly2 S2 W2 mem2 md2 _ _ _ HAR2 HPerm2) as Hd2. unfold zdisjoint, block_rng in Hd2. cbn [fst snd] in Hd2.
change (req_size FRAME_OBJ) with 40 in Hd2.
pose proof (proj1 HJ) as HARc2.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
rreg HS (1%bv : bv 5) R1; rreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free trasegs B LAWS Hsegs errno_low ML AFREE W2 E2' _ ms FF_STK (spZ regs) _ ly S W mem md [] ly2 S2 _ (0 + 1)
lpal (3 * nlp) (-32) (ew E2' 2) (Z_to_bv 64 0x880d8) []);
[ exact HS | rewrite HBcode; reflexivity | reflexivity | exact HJ | exact Hinl
| rewrite R10, F32; reflexivity
| exact (st_ok_restrict_reg trasegs (w_H W2) E2' _ _ 2%bv HS)
| reflexivity | exact Usp2 | reflexivity | lia | unfold FF_STK; lia
| rewrite R3, F3; exact Hgp | rewrite R4, F4; exact Htp
| exact R1 | vm_compute; reflexivity | destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia
| eapply (achain_chain_pre ly2 _ (spZ regs - 32) fp []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, F10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite HBcode; cbn; exact HU2
| intros _ i Hi; apply (inFP_ablocks_fp _ lpal (3 * nlp) i); [| exact Hi];
unfold ff_blocks; rewrite Hc; right; right; left; reflexivity ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8.
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ & HP3 & (l1' & l2' & Ebl' & Ebl2') & Hfrs3 & HK3).
pose proof (proj1 HJ) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc2) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((fp, FRAME_OBJ) :: rest)).
{ rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (lpal, 3 * nlp)). rewrite <- Ebl'.
apply Permutation_sym. eapply Permutation_trans; [exact HPerm2|]. apply perm_swap. }
assert (Hinf3 : In (fp, FRAME_OBJ) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]. left. reflexivity. }
jafter_call HS 52%nat regs3 (mrestrict (w_H W3) mem3) HP3 HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj trasegs B); [exact HK3 | exact HJ | exact Usp2 | lia | unfold FF_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val trasegs E2' _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgotb) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot3) | lia].
- apply (region_kept_val trasegs E2' _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcellb) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell3) | lia].
- eapply (region_kept_block_aj trasegs B); [exact HK3 | rewrite F10; apply unsigned_lit_small; lia | exact Hinf2 | lia
| change (req_size FRAME_OBJ) with 40; unfold FRAME_OBJ; lia | lia | unfold FRAME_OBJ; intros a Ha HE3; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2' 52 (map (getr regs3) CLOB)) as E3' eqn:HE3' in HS.
assert (OLD3 : forall n, (n < 52)%nat -> ew E3' n = ew E2' n) by (intros n Hn; rewrite HE3'; apply YO3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (ff_extra lpal img attr)) E3') by (rewrite HE3'; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3'.
assert (G10 : ew E3' 10 = Z_to_bv 64 fp) by (rewrite OLD3 by (cbv; lia); exact F10).
assert (G35 : ew E3' 35 = Z_to_bv 64 SB) by (rewrite OLD3 by (cbv; lia); exact F35).
assert (G1 : ew E3' 1 = getr regs 1) by (rewrite OLD3 by (cbv; lia); exact F1).
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (SHOK : sh_ok trasegs Bx ff_SH E3' (mrestrict (w_H W3) mem3)).
{ unfold sh_ok, ff_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS ly3 S3 W3 mem3 md3 E3' Bx 10 fp FRAME_OBJ 0 FRAME_OBJ HAR3 Hinf3).
+ unfold U, Bx. cbn [sv_denot]. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite G10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size FRAME_OBJ) with 40. unfold FRAME_OBJ. lia. }
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp3. }
rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340224 with (pc_wrap_free code) by (rewrite HBcode; reflexivity).
eapply (ff_tail W ly S regs mem md ch fp img lpal attr N nlp rest); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm3 | | |].
+ eapply (aregs_preserved_of_st_ok trasegs _ E3' _ _ regs (ff_extra lpal img attr) HS); [exact HAE3 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, G10. reflexivity.
+ cbn [ms_regs]. rewrite R1, G1. reflexivity.
Qed.
End FF.
End b.
Print Assumptions tra_freeFrame.
