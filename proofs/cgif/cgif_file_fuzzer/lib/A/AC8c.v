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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC8f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Lemma tcbl_loop : forall (k : nat) (i bp b Lc : Z) W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0,
Z.of_nat k = lzwPos - i ->
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
(bl + req_size Lby <= lz \/ lz + req_size Llz <= bl) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 9 = Z_to_bv 64 b -> getr regs 31 = Z_to_bv 64 Lc ->
getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
0 <= i < lzwPos -> 0 <= bp -> 8 * bp + b <= 12 * i -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbl_A)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' bp' b' corr,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cbl_X)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W mem' md' 0 /\
getr regs' 17 = Z_to_bv 64 bp' /\ getr regs' 20 = Z_to_bv 64 corr /\
(corr = 0 \/ (corr = -1 /\ 1 <= bp')) /\ 0 <= bp' /\ 0 <= b' /\ 8 * bp' + b' <= 12 * lzwPos /\
(forall r, In r TKEPT -> getr regs' r = getr regs r)).
Proof.
induction k as [|k IH]; intros i bp b Lc W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0
Hk HJ Hbl Hlz Hdisj Hfix Hcf H11 H12 H17 H9 H31 H29 Hi Hbp Hinv Hb HLc; [lia|].
pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
assert (Hbp29 : bp < 2 ^ 29) by lia.
assert (HbpL : bp + 3 <= Lby) by lia.
eapply SRr_bind.
{ eapply (tcbl_segA B LAWS W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc); try eassumption; lia. }
cbv beta. intros W1 c1 _ (-> & regsA & memA & mdA & L1 & -> & HJA & HfixA & H11A & H12A & H17A & H9A & H29A & H31A & HL1 & HKA).
eapply SRr_bind.
{ eapply (tcbl_segB B LAWS W regsA memA mdA sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b L1); try eassumption; lia. }
cbv beta. intros W2 c2 _ (-> & regsB & memB & mdB & s & corr & -> & HJB & HfixB & H11B & H12B & H17B & H31B & H29B & H19B & H20B & H18B & Hcorr & Hs & Hsb & HKB).
eapply SRr_bind.
{ eapply (tcbl_segC B LAWS W regsB memB mdB sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i (bp + s) (b + L1) L1 corr); try eassumption; lia. }
cbv beta. intros W3 c3 _ (-> & regsC & memC & mdC & b' & m & L2 & -> & HJC & HfixC & H11C & H12C & H17C & H20C & H29C & H9C & H31C & Htm & Hb' & HL2 & HKC).
assert (Hms : m = s) by lia.
assert (HK : forall r, In r TKEPT -> getr regsC r = getr regs r).
{ intros r Hr. rewrite HKC, HKB, HKA by exact Hr. reflexivity. }
destruct (Z.eqb_spec (i + 1) lzwPos) as [Heq | Hne].
-
apply SRr_ret. split; [reflexivity|]. exists regsC, memC, mdC, (bp + s), b', corr.
split; [reflexivity|]. split; [exact HJC|]. split; [exact H17C|]. split; [exact H20C|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact HK.
-
eapply SRr_mono.
{ eapply (IH (i + 1) (bp + s) b' L2 W regsC memC mdC sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0);
try eassumption; lia. }
cbv beta. intros W4 c' _ (-> & regs' & mem' & md' & bp' & b'' & corr' & -> & HJ' & H17' & H20' & Hcorr' & Hbp' & Hb'' & Hinv' & HK').
split; [reflexivity|]. exists regs', mem', md', bp', b'', corr'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact H17'|]. split; [exact H20'|].
split; [exact Hcorr'|]. split; [exact Hbp'|]. split; [exact Hb''|]. split; [exact Hinv'|].
intros r Hr. rewrite HK' by exact Hr. apply HK. exact Hr.
Qed.
Definition BxE : sv := SOff 32 0.
Definition ss_tcbl : sstate :=
mkSS A_cbl sr_atoms
[ stack_region 80; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 10%nat) 0 1 0 1 [] ] None
(mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, PTR 4); (11%nat, mkAF 0 (2^28) 0); (12%nat, PTR 4);
(13%nat, mkAF 0 65535 0); (14%nat, mkAF 0 12 0); (32%nat, mkAF SB SB 0) ] [] []).
Definition TCBL_CLOB : list (bv 5) := [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28; 29; 30; 31]%bv.
Lemma tcbl_clob_kept : forall r : bv 5, reg_in r TCBL_CLOB = false -> r = 0%bv \/ In r TKEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Theorem pb_cbl : forall W ly S regs mem md ch bl Lby lz Llz lzwPos D C0 rest,
afn_pre SEGS B TCBL_STK ly S W regs mem md ch ->
getr regs 10 = w64 bl -> getr regs 11 = w64 lzwPos -> getr regs 12 = w64 lz ->
getr regs 13 = w64 D -> getr regs 14 = w64 C0 ->
0 <= lzwPos < 2 ^ 28 -> 0 <= D <= 65535 -> 0 <= C0 <= 12 ->
12 * lzwPos / 8 + 3 <= Lby -> 2 * lzwPos <= Llz ->
Permutation (ablocks B ly S) ((bl, Lby) :: (lz, Llz) :: rest) ->
SRr SEGS W (cfg_at SEGS (BASE + A_cbl) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' ret,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TCBL_STK (spZ regs) (ablocks_fp [(bl, Lby)]) ly S W mem md [] ly S W mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 ret /\ 0 <= ret /\ 8 * ret <= 12 * lzwPos).
Proof.
intros W ly S regs mem md ch bl Lby lz Llz lzwPos D C0 rest HPRE H10 H11 H12 H13 H14 HlzwPos HD HC0 HLby HLlz HPerm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS80 : TCBL_STK = 80) by reflexivity.
assert (Hbl : In (bl, Lby) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
assert (Hlz : In (lz, Llz) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; left; reflexivity]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HPerm) as Hdisj. unfold zdisjoint, block_rng in Hdisj. cbn [fst snd] in Hdisj.
pose proof (Z.div_mod (12 * lzwPos) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (12 * lzwPos) 8 ltac:(lia)) as Hmb.
set (q8 := 12 * lzwPos / 8) in *. set (r8 := (12 * lzwPos) mod 8) in *. clearbody q8 r8.
assert (HLby' : 3 * lzwPos + 5 <= 2 * Lby) by lia. assert (HLby3 : 3 <= Lby) by lia. clear Hdm Hmb HLby q8 r8.
destruct (al_blocks _ _ LAWS ly S W mem md bl Lby HAR Hbl) as (Hbl16 & _ & Hblceil & Hblh_ia & Hblpres & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
destruct (al_blocks _ _ LAWS ly S W mem md lz Llz HAR Hlz) as (Hlz16 & _ & Hlzceil & Hlzh_ia & _ & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB. pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
remember (Eimg (Ereg regs [Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 bl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 lzwPos) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 lz) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 D) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 C0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (HS : st_ok_pi SEGS VAL E ss_tcbl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx, HE. unfold ss_tcbl. apply pa_entry_st_ok_full; rewrite <- ?HE.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 BxE SB);
[cbn [sv_denot BxE]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
+ rewrite (VB 10%nat bl E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hblpres. lia.
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat bl E10) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
idtac.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hblceil Hblh Hblh_img C1 C3 HS80 Hstk0 HrB HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E13, E14, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hblceil Hblh Hblh_img Hbl16 Hlzceil Hlzh Hlzh_img Hlz16 Hal16 C1 C3 HS80 Hstk0 HlzwPos HD HC0 HrB HrL. clear. unfold off_img.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
pose proof (ajournal_init SEGS B TCBL_STK (ablocks_fp [(bl, Lby)]) ly S W regs mem md ch HPRE) as HJ.
shok_auto SHOK BxE E (mrestrict (w_H W) mem).
unfold cfg_at. change (w64 A_cbl) with (Z_to_bv 64 (BASE + A_cbl)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite (U_atom E 10 bl E10) by lia.
eapply (obl_of_block SEGS B LAWS ly S W _ _ E BxE _ 1 bl Lby (proj1 HJ) Hbl); [unfold BxE; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity | lia | lia]. }
{ awr_ok_tac; [exact Usp | ].
eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10 bl Lby); [reflexivity | rewrite E10; apply unsigned_lit_small; lia | exact Hbl | cbn; lia | cbn; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (bl + (a - bl)) by lia. apply (inFP_ablocks_fp _ bl Lby); [left; reflexivity | lia]. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
-
rewrite branch_eq_U, (U_atom _ 11 lzwPos), U_lit in Hc; [| lia0 | cbn [ew ewset Nat.eqb]; exact E11 | lia].
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; [exact Usp | ].
eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10 bl Lby); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E10; apply unsigned_lit_small; lia | exact Hbl | cbn; lia | cbn; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (bl + (a - bl)) by lia. apply (inFP_ablocks_fp _ bl Lby); [left; reflexivity | lia]. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. cbn [ew ewset Nat.eqb] in Rra.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d, 0 end.
split; [cbn [ms_regs]; rewrite Rra, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SB] HS); [env_agree_chain HAE | vm_compute; reflexivity]|].
split; [cbn [ms_regs]; exact Ra0|]. lia.
-
rewrite branch_eq_U, (U_atom _ 11 lzwPos), U_lit in Hc; [| lia0 | cbn [ew ewset Nat.eqb]; exact E11 | lia].
assert (Hlp : 0 < lzwPos) by (destruct (Z.eqb_spec lzwPos 0); [discriminate | lia]).
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_A.
{ awr_ok_tac; [exact Usp | ].
eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10 bl Lby); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E10; apply unsigned_lit_small; lia | exact Hbl | cbn; lia | cbn; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (bl + (a - bl)) by lia. apply (inFP_ablocks_fp _ bl Lby); [left; reflexivity | lia]. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) L10. prreg HS (13%bv : bv 5) L13. prreg HS (14%bv : bv 5) L14. prreg HS (5%bv : bv 5) L5.
prreg HS (16%bv : bv 5) L16. prreg HS (7%bv : bv 5) L7. prreg HS (28%bv : bv 5) L28. prreg HS (30%bv : bv 5) L30.
prreg HS (11%bv : bv 5) L11. prreg HS (12%bv : bv 5) L12. prreg HS (17%bv : bv 5) L17. prreg HS (9%bv : bv 5) L9.
prreg HS (31%bv : bv 5) L31. prreg HS (29%bv : bv 5) L29.
prreg HS (2%bv : bv 5) Lsp.
cbn [ew ewset Nat.eqb] in L10, L13, L14, L5, L16, L11, L12, L31, L29, Lsp.
rewrite E10 in L10. rewrite E13 in L13. rewrite E14 in L14. rewrite E13, alu64_sll1 in L5 by lia.
rewrite E32 in L16. rewrite E12 in L11. rewrite E12 in L12. rewrite E14 in L31. rewrite E11 in L29.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
pose proof (ajournal_sub_init SEGS B _ _ _ _ _ _ _ _ _ _ _ W (ms_mem msX) mdX _ 0 (spZ regs - 80) (ablocks_fp [(bl, Lby)]) (-80)
HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(rewrite HS80; lia)) as HJL
end.
pmkst HS.
eapply SRr_bind.
{ eapply (tcbl_loop (Z.to_nat lzwPos) 0 0 0 C0 W _ _ _ (spZ regs - 80) _ _ ly S bl Lby lz Llz lzwPos D C0);
[ lia | exact HJL | exact Hbl | exact Hlz | exact Hdisj
| unfold tcbl_regs_fix; cbn [ms_regs]; repeat split; assumption
| unfold tcbl_fix; lia
| cbn [ms_regs]; rewrite L11; unfold w64; f_equal; lia | cbn [ms_regs]; rewrite L12; unfold w64; f_equal; lia
| cbn [ms_regs]; exact L17 | cbn [ms_regs]; exact L9 | cbn [ms_regs]; exact L31
| cbn [ms_regs]; rewrite L29; unfold w64; f_equal; lia | lia | lia | lia | lia | lia ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regsL & memL & mdL & bp' & b' & corr & -> & HJL3 & H17L & H20L & Hcorr & Hbp' & Hb' & Hinv & HKL).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msX) _ 0 0 (spZ regs - 80) (ablocks_fp [(bl, Lby)]) [] ly S W memL mdL 0
HJ HJL3 ltac:(rewrite HS80; lia) ltac:(lia)) as HJ3
end.
match type of HJ3 with ?P -> _ => assert (HFP : P); [|specialize (HJ3 HFP); clear HFP] end.
{ intros a Ha. left. split; [exact Ha|]. destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & n & Hpin & Hpn).
destruct Hpin as [Hpin | []]. injection Hpin as <- <-. exists bl, Lby. split; [exact Hbl | exact Hpn]. }
cbn [app] in HJ3.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) [0%nat]) in
pose proof (st_ok_pi_after_stretch 35 Ex (abs_ss VAL ss) ms regsL (mrestrict (w_H W) memL) rs A_cbl_X TCBL_CLOB HS eq_refl
ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs 35 TCBL_CLOB A_cbl_X) in
change (ss_after_stretch (abs_ss VAL ss) rs 35 TCBL_CLOB A_cbl_X) with ss2 in HS2
end.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [| assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r Hr. cbn [ms_regs restrict]. destruct (tcbl_clob_kept r Hr) as [-> | Hin]; [rewrite !getr_zero; reflexivity | apply HKL; exact Hin]. }
{ cbn [ms_mem restrict]. constructor; [|constructor].
eapply (region_kept_stack_sub SEGS B E); [exact HJL3 | exact HJ3 | exact Usp | lia | rewrite HS80; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 35 _) as Et eqn:HEt in HS. assert (HEIt : img_env VAL A_LIM Et) by (rewrite HEt; apply img_env_havoc; [first [exact HEI | assumption] | cbv; lia]).
assert (HAEt : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Et) by (rewrite HEt; env_agree_chain HAE).
assert (F47 : ew Et 47 = Z_to_bv 64 bp').
{ rewrite HEt, <- H17L. etransitivity; [apply (ew_havoc_new _ 35 (map (getr regsL) TCBL_CLOB) 12 (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (F1 : ew Et 1 = getr regs 1) by (rewrite HEt, ew_havoc_old by lia; cbn [ew ewset Nat.eqb]; exact E1).
assert (Uspt : bv_unsigned (ew Et 2) = spZ regs) by (rewrite HEt, ew_havoc_old by lia; cbn [ew ewset Nat.eqb]; exact Usp).
clear HEt.
Local Ltac tcbl_tail Hwx Hsegs HS HJ HAEt F1 F47 Uspt Hra ret :=
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end;
let SHOKt := fresh "SHOK" in
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msX) =>
shok_auto SHOKt BxE Ex (mrestrict (w_H Wx) (ms_mem msX)) end;
paj_run_tok RUN HS HJ SHOKt Bspan; [ awr_ok_tac; exact Uspt |];
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
prreg HS (10%bv : bv 5) Hr10; prreg HS (1%bv : bv 5) Hr1; cbn [ew ewset Nat.eqb] in Hr10, Hr1;
eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat'; split; [reflexivity|];
lazymatch goal with |- exists _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d, ret end;
split; [cbn [ms_regs]; rewrite Hr1, F1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ [Z_to_bv 64 SB] HS); [env_agree_chain HAEt | vm_compute; reflexivity]|];
cbn [ms_regs]; rewrite Hr10, F47, ?unsigned_lit_small by lia; split; [unfold w64; f_equal; lia | lia].
destruct Hcorr as [Hcz | [Hcz Hbp1]]; rewrite Hcz in H20L.
+ pose proof (st_ok_pi_set_reg _ _ _ (20%bv : bv 5) (SLit 0) HS ltac:(intros X; discriminate X) H20L) as HS1.
pose proof (st_ok_pi_add_fact _ _ _ 47 (mkAF 0 (2 ^ 29) 0) HS1) as HS2.
match type of HS2 with ?P -> _ => assert (HFa : P); [| specialize (HS2 HFa); clear HFa] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite F47, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
clear HS HS1. rename HS2 into HS.
tcbl_tail Hwx Hsegs HS HJ3 HAEt F1 F47 Uspt Hra bp'.
+ rewrite <- lit_m1 in H20L.
pose proof (st_ok_pi_set_reg _ _ _ (20%bv : bv 5) (SLit 18446744073709551615) HS ltac:(intros X; discriminate X) H20L) as HS1.
pose proof (st_ok_pi_add_fact _ _ _ 47 (mkAF 1 (2 ^ 29) 0) HS1) as HS2.
match type of HS2 with ?P -> _ => assert (HFa : P); [| specialize (HS2 HFa); clear HFa] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite F47, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
clear HS HS1. rename HS2 into HS.
tcbl_tail Hwx Hsegs HS HJ3 HAEt F1 F47 Uspt Hra (bp' - 1).
Qed.
End f.
End e.
End c.
