(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Definition A_freeFrame : Z := AF_asan3_freeFrame.
Definition A_freeFrameP : Z := BASE + A_freeFrame.
Definition FF_STK : Z := 32 + ASTACK.
Definition FRAME_OBJ : Z := 40.
Definition ff_blocks (fp img lpal attr N nlp : Z) : list (Z * Z) :=
(fp, FRAME_OBJ) :: (img, N) :: (if Z.land attr 1 =? 0 then [] else [(lpal, 3 * nlp)]).
Section FF.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Local Notation code := (as_code B).
Definition Bx : sv := SOff 35 0.
Definition ff_regions : smem :=
[ stack_region 32; got_regionP; bcell_regionP 35;
YP09.mkRegion (Some 10%nat) 0 FRAME_OBJ 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 1 (SOff 34 0))] ].
Definition ff_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 4096 140737479966720 4);
(34%nat, mkAF 0 255 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_ff : sstate := mkSS A_freeFrame sr_atoms ff_regions None ff_facts.
Definition ff_SH : list shent := [ mkSHE 10 0 FRAME_OBJ ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ff_extra (lpal img attr : Z) : list word := map (Z_to_bv 64) [lpal; img; attr mod 256; SB].
Lemma ff_entry : forall W ly S regs mem md ch fp lpal img attr N nlp rest,
afn_pre SEGS B FF_STK ly S W regs mem md ch ->
getr regs 10 = w64 fp ->
val_mem SEGS (mrestrict (w_H W) mem) fp 8 lpal ->
val_mem SEGS (mrestrict (w_H W) mem) (fp + 8) 8 img ->
val_mem SEGS (mrestrict (w_H W) mem) (fp + 16) 4 attr ->
0 <= lpal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 -> 0 <= N ->
Permutation (ablocks B ly S) (ff_blocks fp img lpal attr N nlp ++ rest) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ff_extra lpal img attr))) ss_ff
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_freeFrameP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx ff_SH (Eimg (Ereg regs (ff_extra lpal img attr))) (mrestrict (w_H W) mem).
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
pose proof (blk_off_imgP _ _ _ _ _ _ fp FRAME_OBJ HAR Hinf) as Hfh_img.
destruct (al_blocks _ _ LAWS ly S W mem md img N HAR Hini) as (Hi16 & Hi4096 & Hiceil & Hih_ia & _ & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img N HAR Hini) as Hih_img.
change (req_size FRAME_OBJ) with 40 in *. pose proof (req_size_pos N RN) as HrN.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ff_extra lpal img attr))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 fp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 lpal) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (attr mod 256)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
split.
- unfold ss_ff, A_freeFrameP. apply pa_entry_st_ok_full.
+   apply regs_ok_Eimg_Ereg.
+   vm_compute. reflexivity.
+
unfold ff_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
*   cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
*
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
*
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
*   rewrite (VB 10%nat fp E10) by lia. unfold FRAME_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ fp 0 8 _ lpal); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mlpal.
-- apply (chunk_ok_val SEGS E _ fp 8 8 _ img); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mimg].
-- apply (chunk_ok_val SEGS E _ fp 16 1 _ (attr mod 256)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_byte0 SEGS _ _ _ _ Mattr).
+
apply pairwise_disjoint_of_extents. unfold ff_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat fp E10) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
unfold FRAME_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hfceil Hfh Hfh_img Hf4096 C1 C3 FFS Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+
split; [|split; [exact I | exact I]].
cbn [ff_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hfceil Hfh Hfh_img Hf4096 Hf16 Hi16 Hi4096 Hiceil Hih Hih_img HrN Hal16 Hab C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
-
unfold sh_ok, ff_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly S W mem md E Bx 10 fp FRAME_OBJ 0 FRAME_OBJ HAR Hinf).
+ unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size FRAME_OBJ) with 40. unfold FRAME_OBJ. lia.
Qed.
Definition ff_post (regs : bvmap 5 word) ly S W mem md (FP rest : list (Z * Z)) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B FF_STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' 3 /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest.
Lemma ff_tail : forall W ly S regs mem md ch fp img lpal attr N nlp rest Wt regsT memT lyt St mdt kt,
afn_pre SEGS B FF_STK ly S W regs mem md ch ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs ch) (as_universe B) ->
st_nev S + 3 <= EV_MAX ->
ajournal SEGS B FF_STK (spZ regs) (ablocks_fp (ff_blocks fp img lpal attr N nlp)) ly S W mem md [] lyt St Wt memT mdt kt ->
kt <= 2 ->
Permutation (ablocks B lyt St) ((fp, FRAME_OBJ) :: rest) ->
aregs_preserved regs regsT -> getr regsT 10 = w64 fp -> getr regsT 1 = getr regs 1 ->
SRr SEGS Wt (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom SEGS)) mdt)
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
{ eapply (aj_free_at SEGS B LAWS pa_segs_low errno_low ML AFREE Wt regsT memT FF_STK (spZ regs) _ ly S W mem md [] lyt St mdt kt
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
- unfold call_trace0, raZ in *. rewrite Hra1. exact HU3.
- intros _ i Hi. apply (inFP_ablocks_fp _ fp FRAME_OBJ i); [left; reflexivity | exact Hi]. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1' & l2' & Ebl' & Ebl2') & _ & _).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [exact HJ3 | lia]|].
split; [eapply aregs_preserved_trans; [exact HP | exact HP3]|].
rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (fp, FRAME_OBJ)). rewrite <- Ebl'.
apply Permutation_sym. exact HPermR.
Qed.
Theorem pb_freeFrame : forall W ly S regs mem md ch fp lpal img attr N nlp rest,
afn_pre SEGS B FF_STK ly S W regs mem md ch ->
st_nev S + 3 <= EV_MAX ->
getr regs 10 = w64 fp ->
val_mem SEGS (mrestrict (w_H W) mem) fp 8 lpal ->
val_mem SEGS (mrestrict (w_H W) mem) (fp + 8) 8 img ->
val_mem SEGS (mrestrict (w_H W) mem) (fp + 16) 4 attr ->
0 <= lpal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 -> 0 <= N -> 0 <= nlp ->
Permutation (ablocks B ly S) (ff_blocks fp img lpal attr N nlp ++ rest) ->
In [pc_free_ra0 (as_code B); BASE + 0x2ad0] (as_universe B) ->
In [pc_free_ra0 (as_code B); BASE + 0x2b08] (as_universe B) ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs ch) (as_universe B) ->
SRr SEGS W (cfg_at SEGS A_freeFrameP regs mem md)
(ff_post regs ly S W mem md (ablocks_fp (ff_blocks fp img lpal attr N nlp)) rest).
Proof.
intros W ly S regs mem md ch fp lpal img attr N nlp rest HPRE Hev H10 Mlpal Mimg Mattr Rlpal Rattr RN Rnlp HPerm HU1 HU2 HU3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct (ff_entry W ly S regs mem md ch fp lpal img attr N nlp rest HPRE H10 Mlpal Mimg Mattr Rlpal Rattr RN HPerm) as [HS SHOK].
pose proof (ajournal_init SEGS B FF_STK (ablocks_fp (ff_blocks fp img lpal attr N nlp)) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : FF_STK = 16416) by reflexivity.
remember (Eimg (Ereg regs (ff_extra lpal img attr))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 fp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 lpal) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (attr mod 256)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ff_extra lpal img attr)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_freeFrameP) with (Z_to_bv 64 A_freeFrameP).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. exact Usp. }
assert (Hini : In (img, N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
assert (Hinf : In (fp, FRAME_OBJ) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md fp FRAME_OBJ HAR Hinf) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & _ & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_imgP _ _ _ _ _ _ fp FRAME_OBJ HAR Hinf) as Hfh_img.
change (req_size FRAME_OBJ) with 40 in Hfceil, Hfh, Hfh_img.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size FRAME_OBJ) with 40 in Hd1.
pose proof (proj1 HJ) as HARc.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
prreg HS (2%bv : bv 5) R2; prreg HS (10%bv : bv 5) R10; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
prreg HS (1%bv : bv 5) R1; prreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free SEGS B LAWS Hsegs errno_low ML AFREE W E _ ms FF_STK (spZ regs) _ ly S W mem md [] ly S _ 0
img N (-32) (ew E 2) (Z_to_bv 64 (BASE + 0x2ad0)) []);
[ exact HS | exact HBfree | reflexivity | exact HJ | exact Hini
| rewrite R10, E33; reflexivity
| exact (st_ok_restrict_reg SEGS (w_H W) E _ _ 2%bv HS)
| reflexivity | exact Usp | reflexivity | lia | unfold FF_STK; lia
| rewrite R3, E3; exact Hgp | rewrite R4, E4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity] | lia
|   eapply (achain_chain_pre ly _ (spZ regs - 32) fp []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, E10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
|   rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); exact HU1
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
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ | exact Usp | lia | unfold FF_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_aj SEGS B); [exact HK | rewrite E10; apply unsigned_lit_small; lia | exact Hinf | lia
| change (req_size FRAME_OBJ) with 40; unfold FRAME_OBJ; lia | lia | unfold FRAME_OBJ; intros a Ha HE; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS. assert (HEIb : img_env VAL A_LIM E2') by (rewrite HE2'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 36)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YN3v.ew_havoc_old; exact Hn).
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
assert (SHOK : sh_ok SEGS Bx ff_SH E2' (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, ff_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 fp FRAME_OBJ 0 FRAME_OBJ HAR2 Hinf2).
+ unfold U, Bx. cbn [sv_denot]. rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size FRAME_OBJ) with 40. unfold FRAME_OBJ. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. exact Usp2. }
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
psrr_branch_tok RUN BR HS SHOK Bspan.
-
rewrite branch_eq_U, U_and_lit, (U_atom E2' 34 (attr mod 256) F34), U_lit, land_mod256_1 in Hc by lia.
rewrite Hc in HPerm2. cbn [app] in HPerm2.
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite HBfree.
eapply (ff_tail W ly S regs mem md ch fp img lpal attr N nlp rest); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm2 | | |].
+ eapply (aregs_preserved_of_st_ok SEGS _ E2' _ _ regs (ff_extra lpal img attr) HS); [exact HAE2 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, F10. reflexivity.
+ cbn [ms_regs]. rewrite R1, F1. reflexivity.
-
rewrite branch_eq_U, U_and_lit, (U_atom E2' 34 (attr mod 256) F34), U_lit, land_mod256_1 in Hc by lia.
rewrite Hc in HPerm2. cbn [app] in HPerm2.
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
assert (Hinl : In (lpal, 3 * nlp) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. right. left. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ _ HAR2 HPerm2) as Hd2. unfold zdisjoint, block_rng in Hd2. cbn [fst snd] in Hd2.
change (req_size FRAME_OBJ) with 40 in Hd2.
pose proof (proj1 HJ) as HARc2.
lazymatch goal with |- SRr _ _ (mkCfg ?ms ?mdc) _ =>
prreg HS (2%bv : bv 5) R2; prreg HS (10%bv : bv 5) R10; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
prreg HS (1%bv : bv 5) R1; prreg HS (8%bv : bv 5) R8;
eapply SRr_bind;
[ eapply (aj_free SEGS B LAWS Hsegs errno_low ML AFREE W2 E2' _ ms FF_STK (spZ regs) _ ly S W mem md [] ly2 S2 _ (0 + 1)
lpal (3 * nlp) (-32) (ew E2' 2) (Z_to_bv 64 (BASE + 0x2b08)) []);
[ exact HS | exact HBfree | reflexivity | exact HJ | exact Hinl
| rewrite R10, F32; reflexivity
| exact (st_ok_restrict_reg SEGS (w_H W2) E2' _ _ 2%bv HS)
| reflexivity | exact Usp2 | reflexivity | lia | unfold FF_STK; lia
| rewrite R3, F3; exact Hgp | rewrite R4, F4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity] | destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia
| eapply (achain_chain_pre ly2 _ (spZ regs - 32) fp []);
[ apply achain_low; lia
| change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)); rewrite R2, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite R8, F10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); exact HU2
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
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ | exact Usp2 | lia | unfold FF_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val_at E2' _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
- apply (region_kept_val_at E2' _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEIb (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia].
- eapply (region_kept_block_aj SEGS B); [exact HK3 | rewrite F10; apply unsigned_lit_small; lia | exact Hinf2 | lia
| change (req_size FRAME_OBJ) with 40; unfold FRAME_OBJ; lia | lia | unfold FRAME_OBJ; intros a Ha HE3; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2' 52 (map (getr regs3) CLOB)) as E3' eqn:HE3' in HS. assert (HEIc : img_env VAL A_LIM E3') by (rewrite HE3'; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLD3 : forall n, (n < 52)%nat -> ew E3' n = ew E2' n) by (intros n Hn; rewrite HE3'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (ff_extra lpal img attr)) E3') by (rewrite HE3'; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3'.
assert (G10 : ew E3' 10 = Z_to_bv 64 fp) by (rewrite OLD3 by (cbv; lia); exact F10).
assert (G35 : ew E3' 35 = Z_to_bv 64 SB) by (rewrite OLD3 by (cbv; lia); exact F35).
assert (G1 : ew E3' 1 = getr regs 1) by (rewrite OLD3 by (cbv; lia); exact F1).
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (SHOK : sh_ok SEGS Bx ff_SH E3' (mrestrict (w_H W3) mem3)).
{ unfold sh_ok, ff_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 E3' Bx 10 fp FRAME_OBJ 0 FRAME_OBJ HAR3 Hinf3).
+ unfold U, Bx. cbn [sv_denot]. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite G10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size FRAME_OBJ) with 40. unfold FRAME_OBJ. lia. }
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp3. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite HBfree.
eapply (ff_tail W ly S regs mem md ch fp img lpal attr N nlp rest); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm3 | | |].
+ eapply (aregs_preserved_of_st_ok SEGS _ E3' _ _ regs (ff_extra lpal img attr) HS); [exact HAE3 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, G10. reflexivity.
+ cbn [ms_regs]. rewrite R1, G1. reflexivity.
Qed.
End FF.
End c.
End b.
