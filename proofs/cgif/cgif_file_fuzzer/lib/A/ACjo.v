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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d.
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
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Local Notation code := (as_code B).
Definition fc_postX (regs : bvmap 5 word) ly S W mem md (FP rest : list (Z * Z)) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B FC_STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' 2 /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest /\
mo_le MT S S' (2 * mo_free MT).
Lemma fc_tailX : forall W ly S regs mem md ch g pal attr ngp rest Wt regsT memT lyt St mdt kt acc,
afn_pre SEGS B FC_STK ly S W regs mem md ch ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs ch) (as_universe B) ->
st_nev S + 2 <= EV_MAX ->
ajournal SEGS B FC_STK (spZ regs) (ablocks_fp (fc_blocks g pal attr ngp)) ly S W mem md [] lyt St Wt memT mdt kt ->
kt <= 1 ->
Permutation (ablocks B lyt St) ((g, CGIF_OBJ) :: rest) ->
aregs_preserved regs regsT -> getr regsT 10 = w64 g -> getr regsT 1 = getr regs 1 ->
mo_ok MT S (2 * mo_free MT) -> mo_le MT S St acc -> acc + mo_free MT <= 2 * mo_free MT ->
SRr SEGS Wt (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom SEGS)) mdt)
(fc_postX regs ly S W mem md (ablocks_fp (fc_blocks g pal attr ngp)) rest).
Proof.
intros W ly S regs mem md ch g pal attr ngp rest Wt regsT memT lyt St mdt kt acc
HPRE HU3 Hev HJ Hkt HPermR HP Ha0 Hra1 MOK MACC Hacc.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARt & Hly & _ & _ & _ & _ & Hnev & _ & G1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (FFS : FC_STK = 16400) by reflexivity.
assert (HinfT : In (g, CGIF_OBJ) (ablocks B lyt St)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPermR|]. left. reflexivity. }
assert (P2 : getr regsT 2 = getr regs 2) by (apply (HP 2); left; reflexivity).
assert (P3 : getr regsT 3 = getr regs 3) by (apply (HP 3); right; left; reflexivity).
assert (P4 : getr regsT 4 = getr regs 4) by (apply (HP 4); right; right; left; reflexivity).
assert (P8 : getr regsT 8 = getr regs 8) by (apply (HP 8); right; right; right; left; reflexivity).
eapply SRr_mono.
{ eapply (AFREE4 Wt regsT memT FC_STK (spZ regs) _ ly S W mem md [] lyt St mdt kt
g CGIF_OBJ 0 (getr regs 1) ch HJ HinfT Ha0).
- unfold spZ. rewrite P2. lia.
- reflexivity. - lia. - unfold FC_STK; lia.
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
- intros _ i Hi. apply (inFP_ablocks_fp _ g CGIF_OBJ i); [left; reflexivity | exact Hi].
-   pose proof (mo_free_nonneg MT MLAW) as Hf0. exact (mok_station MT S St _ acc _ MLAW MOK MACC Hf0 Hacc). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1' & l2' & Ebl' & Ebl2') & _ & _ & MLE3).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [exact HJ3 | lia]|].
split; [eapply aregs_preserved_trans; [exact HP | exact HP3]|].
split; [| exact (mle_weaken MT S S3 _ _ MLAW (mle_station MT S St S3 _ _ MLAW MACC MLE3) Hacc)].
rewrite Ebl2'. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1' l2' (g, CGIF_OBJ)). rewrite <- Ebl'.
apply Permutation_sym. exact HPermR.
Qed.
Theorem pb_freeCGIFX : forall W ly S regs mem md ch g pal attr ngp rest,
afn_pre SEGS B FC_STK ly S W regs mem md ch ->
st_nev S + 2 <= EV_MAX ->
getr regs 10 = w64 g ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 24) 8 pal ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 40) 4 attr ->
0 <= pal < 2 ^ 64 -> 0 <= attr < 2 ^ 32 -> 0 <= ngp ->
Permutation (ablocks B ly S) (fc_blocks g pal attr ngp ++ rest) ->
In [pc_free_ra0 (as_code B); BASE + 0x73c] (as_universe B) ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs ch) (as_universe B) ->
mo_ok MT S (2 * mo_free MT) ->
SRr SEGS W (cfg_at SEGS A_freeCGIFP regs mem md)
(fc_postX regs ly S W mem md (ablocks_fp (fc_blocks g pal attr ngp)) rest).
Proof.
intros W ly S regs mem md ch g pal attr ngp rest HPRE Hev H10 Mpal Mattr Rpal Rattr Rngp HPerm HU1 HU3 MOK.
pose proof (mo_free_nonneg MT MLAW) as Hf0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (fc_entry B LAWS TL W ly S regs mem md ch g pal attr ngp rest HPRE H10 Mpal Mattr Rpal Rattr HPerm) as [HS SHOK].
pose proof (ajournal_init SEGS B FC_STK (ablocks_fp (fc_blocks g pal attr ngp)) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : FC_STK = 16400) by reflexivity.
remember (Eimg (Ereg regs (fc_extra pal attr))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 pal) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (attr mod 256)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fc_extra pal attr)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (Hing : In (g, CGIF_OBJ) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_OBJ HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_OBJ HAR Hing) as Hgh_img.
change (req_size CGIF_OBJ) with 96 in Hgceil, Hgh, Hgh_img.
pose proof (Z.mod_pos_bound attr 256 ltac:(lia)) as Hab.
unfold cfg_at. change (w64 A_freeCGIFP) with (Z_to_bv 64 A_freeCGIFP).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
psrr_branch_tok RUN BR HS SHOK Bspan.
-
rewrite branch_ne_U, U_and_lit, (U_atom E 33 (attr mod 256) E33), U_lit, land_mod256_4 in Hc by lia.
assert (Hc' : (Z.land attr 4 =? 0) = false) by (destruct (Z.land attr 4 =? 0); [discriminate | reflexivity]).
unfold fc_blocks in HPerm. rewrite Hc' in HPerm. cbn [app] in HPerm.
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite HBfree.
eapply (fc_tailX W ly S regs mem md ch g pal attr ngp rest _ _ _ _ _ _ _ 0); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm | | | | exact MOK | exact (mle_start MT S MLAW) | clear - Hf0; lia].
+ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (fc_extra pal attr) HS); [exact HAE | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, E10. reflexivity.
+ cbn [ms_regs]. rewrite R1, E1. reflexivity.
-
rewrite branch_ne_U, U_and_lit, (U_atom E 33 (attr mod 256) E33), U_lit, land_mod256_4 in Hc by lia.
assert (Hc' : (Z.land attr 4 =? 0) = true) by (destruct (Z.land attr 4 =? 0); [reflexivity | discriminate]).
pose proof HPerm as HPerm0. unfold fc_blocks in HPerm. rewrite Hc' in HPerm. cbn [app] in HPerm.
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
assert (Hinp : In (pal, 3 * ngp) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. right. left. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HPerm) as Hd1. unfold zdisjoint, block_rng in Hd1. cbn [fst snd] in Hd1.
change (req_size CGIF_OBJ) with 96 in Hd1.
pose proof (proj1 HJ) as HARc.
pmkst HS. rewrite HBfree.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdc) _ =>
prreg HS (2%bv : bv 5) R2; prreg HS (10%bv : bv 5) R10; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
prreg HS (1%bv : bv 5) R1; prreg HS (8%bv : bv 5) R8;
assert (QQ : spZ rg = spZ regs + -16) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia);
eapply SRr_bind;
[ eapply (AFREE4 W rg mm FC_STK (spZ regs) _ ly S W mem md [] ly S mdc 0
pal (3 * ngp) (-16) (Z_to_bv 64 (BASE + 0x73c)) []);
[ exact HJ | exact Hinp
| rewrite R10, E32; reflexivity
| exact QQ | reflexivity | lia | unfold FC_STK; lia
| rewrite R3, E3; exact Hgp | rewrite R4, E4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity] | lia
| eapply (achain_chain_pre ly _ (spZ regs - 16) g []);
[ apply achain_low; lia
| rewrite QQ; lia
| unfold s0Z; rewrite R8, E10; apply unsigned_lit_small; lia
| unfold raZ; rewrite R1; rewrite unsigned_lit_small by lia; lia ]
| rewrite call_trace_nil; unfold raZ; rewrite R1, unsigned_lit_small by lia; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); exact HU1
| intros _ i Hi; apply (inFP_ablocks_fp _ pal (3 * ngp) i); [| exact Hi];
unfold fc_blocks; rewrite Hc'; right; left; reflexivity
|   exact (mok_station MT S S _ 0 _ MLAW MOK (mle_start MT S MLAW) Hf0 ltac:(clear - Hf0; lia)) ]
| ]
end.
clear HJ SHOK R2 R10 R3 R4 R1 R8 QQ.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfrs2 & HK & MLE1).
pose proof (proj1 HJ) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) ((g, CGIF_OBJ) :: rest)).
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (pal, 3 * ngp)). rewrite <- Ebl.
apply Permutation_sym. eapply Permutation_trans; [exact HPerm|]. apply perm_swap. }
assert (Hing2 : In (g, CGIF_OBJ) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. left. reflexivity. }
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ | exact Usp | lia | unfold FC_STK, ASTACK; lia | lia | lia | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
- eapply (region_kept_block_aj SEGS B); [exact HK | rewrite E10; apply unsigned_lit_small; lia | exact Hing | lia
| change (req_size CGIF_OBJ) with 96; unfold CGIF_OBJ; lia | lia | unfold CGIF_OBJ; intros a Ha HE'; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as E2' eqn:HE2' in HS. assert (HEIb : img_env VAL A_LIM E2') by (rewrite HE2'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 35)%nat -> ew E2' n = ew E n) by (intros n Hn; rewrite HE2'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (fc_extra pal attr)) E2') by (rewrite HE2'; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2'.
assert (F10 : ew E2' 10 = Z_to_bv 64 g) by (rewrite OLD2 by (cbv; lia); exact E10).
assert (F34 : ew E2' 34 = Z_to_bv 64 SB) by (rewrite OLD2 by (cbv; lia); exact E34).
assert (F1 : ew E2' 1 = getr regs 1) by (rewrite OLD2 by (cbv; lia); exact E1).
assert (Usp2 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite OLD2 by (cbv; lia); exact Usp).
assert (SHOK : sh_ok SEGS Bx fc_SH E2' (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, fc_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2' Bx 10 g CGIF_OBJ 0 CGIF_OBJ HAR2 Hing2).
+ unfold U, Bx. cbn [sv_denot]. rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_OBJ) with 96. unfold CGIF_OBJ. lia. }
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp2. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite HBfree.
eapply (fc_tailX W ly S regs mem md ch g pal attr ngp rest _ _ _ _ _ _ _ (mo_free MT)); [exact HPRE | exact HU3 | exact Hev | exact HJ | lia | exact HPerm2 | | | | exact MOK | exact MLE1 | clear - Hf0; lia].
+ eapply (aregs_preserved_of_st_ok SEGS _ E2' _ _ regs (fc_extra pal attr) HS); [exact HAE2 | vm_compute; reflexivity].
+ cbn [ms_regs]. rewrite R10, F10. reflexivity.
+ cbn [ms_regs]. rewrite R1, F1. reflexivity.
Qed.
End d.
End c.
End b.
