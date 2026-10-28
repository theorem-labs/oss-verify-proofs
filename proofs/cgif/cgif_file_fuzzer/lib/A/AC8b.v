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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO07 YI0i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC89.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a.
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
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AIMC : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Ltac xrng_prefix xa Hxa := rewrite cbb_prefix_length in Hxa by lia; lia.
Lemma tcbb_loopX : forall (k : nat) (i : Z) W regs memc mdc sp1 mem0 md0 lyc Sc bb Lbb bl Lbl q (BL : list Z),
Z.of_nat k = q - i -> 0 <= i < q ->
ajournal SEGS B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W mem0 md0 [] lyc Sc W memc mdc 0 ->
In (bb, Lbb) (ablocks B lyc Sc) -> In (bl, Lbl) (ablocks B lyc Sc) ->
(bb + req_size Lbb <= bl \/ bl + req_size Lbl <= bb) ->
256 * q + 1 <= Lbb -> 255 * q <= Lbl -> q < 2 ^ 21 ->
spZ regs = sp1 -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 23 = w64 (256 * i) -> getr regs 18 = w64 (bl + 255 * i) -> getr regs 24 = w64 (bb + 1) ->
getr regs 25 = w64 (256 * q) -> getr regs 8 = w64 bb -> getr regs 22 = w64 255 -> getr regs 20 = w64 SB ->
garr8 SEGS (mrestrict (w_H W) mem0) bl BL -> 255 * q <= Z.of_nat (length BL) <= Lbl ->
garr8 SEGS (mrestrict (w_H W) memc) bb (cbb_prefix BL (Z.to_nat i)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbb_loop)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cbb_tail)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W mem0 md0 [] lyc Sc W mem' md' 0 /\
(forall r, In r TCBB_KEPT -> getr regs' r = getr regs r) /\
garr8 SEGS (mrestrict (w_H W) mem') bb (cbb_prefix BL (Z.to_nat q))).
Proof.
induction k as [|k IH]; intros i W regs memc mdc sp1 mem0 md0 lyc Sc bb Lbb bl Lbl q BL Hk Hi HJ Hbb Hbl Hdisj HLbb HLbl Hq
Hsp Hgp Htp H23 H18 H24 H25 H8 H22 H20 GBL LenBL GP; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HLS : CBB_LSTK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & Hblpres & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
assert (Hrb : req_size Lbb = Lbb) by (unfold req_size; destruct (Z.eqb_spec Lbb 0); lia).
assert (Hrl : req_size Lbl = Lbl) by (unfold req_size; destruct (Z.eqb_spec Lbl 0); lia).
rewrite Hrb, Hrl in *.
remember (Eimg (Ereg regs [Z_to_bv 64 (bb + 256 * i)])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 bb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (E23 : ew E 23 = Z_to_bv 64 (256 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 (bb + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E18 : ew E 18 = Z_to_bv 64 (bl + 255 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E25 : ew E 25 = Z_to_bv 64 (256 * q)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (bb + 256 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E ss_tcbb_loop
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbb_loop)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tcbb_loop. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H22].
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, reg_at. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hbbpres. lia.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite E8, E23, E32, E24, E18, E25, E20, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 8) with 256. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
ceil; unfold ASAN_CEIL, SB, kLowShadowBeg, kHighMemBeg. rewrite ?C3 in *. idtac.
repeat match goal with |- _ /\ _ => split end; try lia.
all: first [rewrite Z.mul_comm; apply Z_mod_mult | idtac].
+ cbn [f_alias alias_ok]. split; [|split; [|exact I]].
* apply (alias_srlw_sll _ i); [exact E23 | lia].
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom _ 8 bb E8), (U_atom _ 23 (256 * i) E23), (U_atom _ 32 (bb + 256 * i) E32) by lia.
apply zcanon_id. unfold M64. lia. }
clear HE.
assert (HBx : U E BxL = SHADOW_OFF) by (unfold BxL; rewrite (U_atom E 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxL [mkSHE 32 1 0] E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
apply (shent_app_of_block SEGS B LAWS lyc Sc W memc mdc E BxL 32 (bb + 256 * i) bb Lbb 0 1 _ HAR Hbb HBx);
[rewrite (U_atom E 32 (bb + 256 * i) E32) by lia; reflexivity | lia | lia | rewrite Hrb; lia]. }
paj_run_tok RUN HS HJ SHOK Bspan.
{
rewrite (U_atom E 32 (bb + 256 * i) E32) by lia.
eapply (obl_of_block SEGS B LAWS lyc Sc W memc mdc E BxL _ 1 bb Lbb HAR Hbb HBx); [lia | rewrite Hrb; lia]. }
{ eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (bb + 256 * i));
[reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
unfold reg_at. cbn [r_wlo r_whi]. intros a Ha. right. left. split.
- exists (bb, bb + 256 * q). split; [left; reflexivity | cbn; lia].
- exists bb, Lbb. split; [exact Hbb | rewrite Hrb; lia]. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
cbn [ew ewset Nat.eqb] in Ra0, Ra1, Ra2, Rra, Rsp, Rgp, Rtp.
assert (E32u : bv_unsigned (ew E 32) = bb + 256 * i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (V255 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (bb + 256 * i + 0) (N.to_nat 1) 255).
{
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex _ 32%nat (bb + 256 * i) _ 0 1 0 1 0 1%N (SLit 255)
(@st_ok_region_nth _ SEGS _ _ _ 0 _ HS eq_refl) ltac:(rewrite !ew_ewset_other by lia; exact E32u) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
cbn [sv_denot] in V; rewrite unsigned_lit_small in V by lia; exact V end. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => bb + 256 * i <= a < bb + 256 * i + 1) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?E32u in Hrr; lia|]); destruct Hin)) as KEEP1.
clear HF HFr HG SHOK.
pmkst HS.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ bl Lbl HAR1 Hbl) as (_ & _ & _ & _ & Hblpres1 & _). rewrite Hrl in Hblpres1.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AIMC W (ms_regs ms) (ms_mem ms) CBB_LSTK sp1 _ lyc Sc W mem0 md0 [] lyc Sc _ 0
(bb + 1 + 256 * i) (bl + 255 * i) 255 0 (Z_to_bv 64 (BASE + 0x29d8)) HJ).
- rewrite Ra0, E23, E24. unfold w64. rewrite alu64_add_lit. f_equal. lia.
- rewrite Ra1, E18. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp, Usp. lia.
- reflexivity. - lia. - unfold CBB_LSTK. lia.
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
+ right. left. split.
* exists (bb, bb + 256 * q). split; [left; reflexivity | cbn; lia].
* exists bb, Lbb. split; [exact Hbb | rewrite Hrb; lia].
+ unfold ESTACK. intros Hx. lia.
- apply (amem_range_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ bb Lbb _ _ HAR1 Hbb); [lia | rewrite Hrb; lia].
- apply (range_addressable_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ bb Lbb _ _ HAR1 Hbb); [lia | rewrite Hrb; lia].
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ bb Lbb _ _ HAR1 Hbb); [lia | rewrite Hrb; lia | lia].
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp, Usp; intro; lia].
apply (aview_some_of_apresent SEGS). apply (proj1 (Hblpres1 a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ bl Lbl _ _ HAR1 Hbl); [lia | rewrite Hrl; lia]|]. split.
+ apply (range_addressable_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ bl Lbl _ _ HAR1 Hbl); [lia | rewrite Hrl; lia].
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ bl Lbl _ _ HAR1 Hbl); [lia | rewrite Hrl; lia | lia]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
assert (GP2 : garr8 SEGS (mrestrict (w_H W) mem2) bb (cbb_prefix BL (Z.to_nat (i + 1)))).
{ replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. rewrite cbb_prefix_S. apply garr8_app.
pose proof (cbb_prefix_length BL (Z.to_nat i) ltac:(lia)) as LP.
assert (GBLc : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) bl BL).
{ eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl Lbl bl BL HJ Hbl Hbl); [lia | lia | | exact GBL].
intros a Ha (r & Hr & Hra). cbv [In] in Hr. destruct Hr as [<- | []]. cbn in Hra. lia. }
split.
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc mem2); [|exact GP]. rewrite LP. intros a Ha.
rewrite (Hout2 a); [apply KEEP1; lia | lia | lia | unfold ESTACK; lia].
- rewrite LP. unfold cbb_chunk. apply garr8_cons_x.
+ replace (bb + Z.of_nat (256 * Z.to_nat i)) with (bb + 256 * i + 0) by lia.
apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) (ms_mem ms) mem2); [|exact V255].
intros x Hx. apply Hout2; [lia | lia | unfold ESTACK; lia].
+ lia.
+ replace (bb + Z.of_nat (256 * Z.to_nat i) + 1) with (bb + 1 + 256 * i) by lia.
apply (garr8_aview SEGS (w_H W) (w_H W) (ms_mem ms) mem2 (bl + 255 * i)).
* rewrite length_firstn, length_skipn. intros j Hj. apply Heff. lia.
* replace (bl + 255 * i) with (bl + Z.of_nat (255 * Z.to_nat i)) by lia.
replace (255 * Z.to_nat i)%nat with (255 * Z.to_nat i)%nat by reflexivity.
apply (garr8_sub_x SEGS _ bl BL (255 * Z.to_nat i) 255 GBLc). lia. }
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 35 _) as Eb eqn:HEb in HS. assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD : forall n, (n < 33)%nat -> ew Eb n = ew E n).
{ intros n Hn. rewrite HEb, ew_havoc_old by lia. rewrite !ew_ewset_other by lia. reflexivity. }
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 (bb + 256 * i)]) Eb).
{ rewrite HEb. env_agree_chain HAE. }
clear HEb.
shok_auto SHOK BxL Eb (mrestrict (w_H W) mem2).
paj_run_tok RUN HS HJ2 SHOK Bspan. { awr_ok_tac. }
xcarry GP2 HFr xrng_prefix.
clear HF HFr HG.
assert (F25 : ew Eb 25 = Z_to_bv 64 (256 * q)) by (rewrite OLD by lia; exact E25).
assert (F23 : ew Eb 23 = Z_to_bv 64 (256 * i)) by (rewrite OLD by lia; exact E23).
psrr_branch_tok RUN BR HS SHOK Bspan.
-
rewrite branch_ne_U, (U_atom _ 25 (256 * q) F25), (U_atom_off _ 23 (256 * i) 256 F23) in Hc by lia.
assert (Hlt : i + 1 < q) by (destruct (Z.eqb_spec (256 * q) (256 * i + 256)); [discriminate | lia]).
paj_run_to_tok RUNTO HS HJ2 SHOK Bspan A_cbb_loop. { awr_ok_tac. }
xcarry GP2 HFr xrng_prefix.
clear HF HFr HG. rename HJ2 into HJ3.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TCBB_KEPT' HS HAEb ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (23%bv : bv 5) N23. prreg HS (18%bv : bv 5) N18. prreg HS (22%bv : bv 5) N22.
rewrite F23, unsigned_lit_small in N23 by lia. rewrite OLD, E18, unsigned_lit_small in N18 by lia.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i + 1) W _ _ _ sp1 mem0 md0 lyc Sc bb Lbb bl Lbl q);
[ lia | lia | exact HJ3 | exact Hbb | exact Hbl | rewrite Hrb, Hrl; exact Hdisj | exact HLbb | exact HLbl | exact Hq
| unfold spZ; cbn [ms_regs]; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp
| cbn [ms_regs]; rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp
| cbn [ms_regs]; rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| cbn [ms_regs]; rewrite N23; unfold w64; f_equal; lia
| cbn [ms_regs]; rewrite N18; unfold w64; f_equal; lia
| cbn [ms_regs]; rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24
| cbn [ms_regs]; rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25
| cbn [ms_regs]; rewrite (HK 8%bv ltac:(cbv; tauto)); exact H8
| cbn [ms_regs]; exact N22
| cbn [ms_regs]; rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20
| exact GBL | exact LenBL | cbn [ms_mem]; exact GP2 ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ4 & HK3 & GP3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ4|]. split.
{ intros r Hr. rewrite (HK3 r Hr). cbn [ms_regs]. destruct (tcbb_kept_cases r Hr) as [-> | Hr']; [rewrite N22, H22; reflexivity | exact (HK r Hr')]. }
exact GP3.
-
rewrite branch_ne_U, (U_atom _ 25 (256 * q) F25), (U_atom_off _ 23 (256 * i) 256 F23) in Hc by lia.
assert (Heq : i + 1 = q) by (destruct (Z.eqb_spec (256 * q) (256 * i + 256)); [lia | discriminate]).
paj_run_to_tok RUNTO HS HJ2 SHOK Bspan A_cbb_tail. { awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TCBB_KEPT' HS HAEb ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (22%bv : bv 5) N22.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ2|]. split.
{ intros r Hr. destruct (tcbb_kept_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite N22, H22; reflexivity | exact (HK r Hr')]. }
replace (Z.to_nat q) with (Z.to_nat (i + 1)) by lia. xcarry GP2 HFr xrng_prefix. cbn [ms_mem]. exact GP2.
Qed.
Lemma tcbb_blocksX : forall W regs memc mdc sp1 lyc Sc bb Lbb bl Lbl q n (BL : list Z),
ajournal SEGS B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
In (bb, Lbb) (ablocks B lyc Sc) -> In (bl, Lbl) (ablocks B lyc Sc) ->
(bb + req_size Lbb <= bl \/ bl + req_size Lbl <= bb) ->
256 * q + 1 <= Lbb -> 255 * q <= Lbl -> 255 * q <= n < 255 * q + 255 -> 0 <= n < 2 ^ 28 ->
spZ regs = sp1 -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 19 = w64 n -> getr regs 21 = w64 q -> getr regs 22 = w64 255 ->
getr regs 8 = w64 bb -> getr regs 9 = w64 bl -> getr regs 20 = w64 SB ->
garr8 SEGS (mrestrict (w_H W) memc) bl BL -> 255 * q <= Z.of_nat (length BL) <= Lbl ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbb_test)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cbb_tail)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B CBB_LSTK sp1 [(bb, bb + 256 * q)] lyc Sc W memc mdc [] lyc Sc W mem' md' 0 /\
(forall r, In r TCBB_TKEPT -> getr regs' r = getr regs r) /\
garr8 SEGS (mrestrict (w_H W) mem') bb (cbb_prefix BL (Z.to_nat q))).
Proof.
intros W regs memc mdc sp1 lyc Sc bb Lbb bl Lbl q n BL HJ Hbb Hbl Hdisj HLbb HLbl Hnq Hn Hsp Hgp Htp H19 H21 H22 H8 H9 H20 GBL LenBL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
assert (Hq : 0 <= q < 2 ^ 21) by lia.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & _ & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lbb ltac:(lia)) as HrB. pose proof (req_size_pos' Lbl ltac:(lia)) as HrL.
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 bb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 bl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E21 : ew E 21 = Z_to_bv 64 q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (HS : st_ok_pi SEGS VAL E ss_tcbb_test (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbb_test)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tcbb_test. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H22].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite E8, E9, E19, E21, E20, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
ceil; unfold ASAN_CEIL, SB, kLowShadowBeg, kHighMemBeg. rewrite ?C3 in *. idtac.
repeat match goal with |- _ /\ _ => split end; try lia.
all: match goal with |- ?g => idtac "TESTFACT" g end; fail. }
clear HE.
shok_auto SHOK BxL E (mrestrict (w_H W) memc).
psrr_branch_tok RUN BR HS SHOK Bspan.
-
rewrite branch_geu_U, (U_atom E 19 n E19), U_lit in Hc by lia.
assert (Hq1 : 1 <= q) by (destruct (Z.ltb_spec n 255); [discriminate|lia]).
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbb_loop. { awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TCBB_TKEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (23%bv : bv 5) L23. prreg HS (18%bv : bv 5) L18. prreg HS (24%bv : bv 5) L24. prreg HS (25%bv : bv 5) L25.
prreg HS (22%bv : bv 5) L22.
rewrite E21, alu64_sll_lit in L25 by lia. rewrite E8, unsigned_lit_small in L24 by lia. rewrite E9 in L18.
pmkst HS.
eapply SRr_mono.
{ eapply (tcbb_loopX (Z.to_nat q) 0 W _ _ _ sp1 memc mdc lyc Sc bb Lbb bl Lbl q BL);
[ lia | lia | exact HJ | exact Hbb | exact Hbl | exact Hdisj | exact HLbb | exact HLbl | lia
| unfold spZ; cbn [ms_regs]; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp
| cbn [ms_regs]; rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp
| cbn [ms_regs]; rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| cbn [ms_regs]; rewrite L23; reflexivity
| cbn [ms_regs]; rewrite L18; unfold w64; f_equal; lia
| cbn [ms_regs]; exact L24
| cbn [ms_regs]; rewrite L25; unfold w64; f_equal; lia
| cbn [ms_regs]; rewrite (HK 8%bv ltac:(cbv; tauto)); exact H8
| cbn [ms_regs]; exact L22
| cbn [ms_regs]; rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20
| exact GBL | exact LenBL | cbn [ms_mem]; change (Z.to_nat 0) with 0%nat; apply garr8_nil ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & GP3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split.
{ intros r Hr. destruct (tcbb_tkept_cases r Hr) as [-> | Hr'].
+ rewrite (HK3 22%bv ltac:(cbv; tauto)). cbn [ms_regs]. rewrite L22, H22. reflexivity.
+ rewrite (HK3 r (tcbb_tkept_kept r Hr')). cbn [ms_regs]. exact (HK r Hr'). }
exact GP3.
-
rewrite branch_geu_U, (U_atom E 19 n E19), U_lit in Hc by lia.
assert (Hq0 : q = 0) by (destruct (Z.ltb_spec n 255); [lia|discriminate]).
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbb_tail. { awr_ok_tac. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TCBB_TKEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK. prreg HS (22%bv : bv 5) L22.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|]. split.
{ intros r Hr. destruct (tcbb_tkept_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite L22, H22; reflexivity | exact (HK r Hr')]. }
rewrite Hq0. change (Z.to_nat 0) with 0%nat. apply garr8_nil.
Qed.
Local Ltac awr_at k v Eq bbv Lbbv Hin :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ k v);
[ reflexivity | rewrite Eq; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
[ replace a with (bbv + (a - bbv)) by lia; apply (inFP_ablocks_fp _ bbv Lbbv); [left; reflexivity | lia]
| exists bbv, Lbbv; split; [exact Hin | lia] ]
| ].
Theorem pb_cbbX : forall W ly S regs mem md ch bl Lbl bb Lbb n rest (BL : list Z),
afn_pre SEGS B CBB_STK ly S W regs mem md ch ->
getr regs 10 = w64 bl -> getr regs 11 = w64 bb -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 28 -> n <= Lbl -> cbb_len n <= Lbb ->
Permutation (ablocks B ly S) ((bl, Lbl) :: (bb, Lbb) :: rest) ->
garr8 SEGS (mrestrict (w_H W) mem) bl BL -> Z.of_nat (length BL) = n ->
SRr SEGS W (cfg_at SEGS A_cbbP regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B CBB_STK (spZ regs) (ablocks_fp [(bb, Lbb)]) ly S W mem md [] ly S W mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 (cbb_len n - 1) /\
garr8 SEGS (mrestrict (w_H W) mem') bb (blocks255 (Datatypes.S (length BL)) BL) /\
Z.of_nat (length (blocks255 (Datatypes.S (length BL)) BL)) = cbb_len n).
Proof.
intros W ly S regs mem md ch bl Lbl bb Lbb n rest BL HPRE H10 H11 H12 Hn HLbl HLbb HPerm GBL LenBL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS96 : CBB_STK = 4192) by reflexivity.
assert (Hbl : In (bl, Lbl) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
assert (Hbb : In (bb, Lbb) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; left; reflexivity]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HPerm) as Hdisj. unfold zdisjoint, block_rng in Hdisj. cbn [fst snd] in Hdisj.
pose proof (Z.div_mod n 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 255 ltac:(lia)) as Hmb.
assert (Hcl : cbb_len n = 256 * (n / 255) + (if n mod 255 =? 0 then 1 else n mod 255 + 2)) by reflexivity.
rewrite Hcl in HLbb |- *. clear Hcl.
destruct (blocks255_qrZ BL (n / 255) (n mod 255) ltac:(lia) ltac:(lia) ltac:(lia)) as (EB255 & EL255 & ESK).
rewrite EL255, EB255. clear EB255 EL255.
set (q := n / 255) in *. set (r := n mod 255) in *. clearbody q r.
assert (Hlen1 : 256 * q + r + 1 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
destruct (al_blocks _ _ LAWS ly S W mem md bb Lbb HAR Hbb) as (Hbb16 & Hbb4096 & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR Hbb) as Hbbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md bl Lbl HAR Hbl) as (Hbl16 & Hbl4096 & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lbl HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lbb ltac:(lia)) as HrB. pose proof (req_size_pos' Lbl ltac:(lia)) as HrL.
pose proof (tcbb_entry B LAWS TL W ly S regs mem md ch bl Lbl bb Lbb n q r HPRE H10 H11 H12 Hn ltac:(lia) ltac:(lia) Hlen1 HLbl Hbl Hbb) as HS.
pose proof (ajournal_init SEGS B CBB_STK (ablocks_fp [(bb, Lbb)]) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (tcbb_extra q r bb bl))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (tcbb_extra q r bb bl)) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 bl) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 bb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 r) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bb + 256 * q)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bl + 255 * q)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
assert (HBx0 : U E Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom E 37 SB E37) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS Bx [mkSHE 34 1 0] E (mrestrict (w_H W) mem)).
{ constructor; [|constructor].
apply (shent_app_of_block SEGS B LAWS ly S W mem md E Bx 34 (bb + 256 * q) bb Lbb 0 1 _ HAR Hbb HBx0);
[rewrite (U_atom E 34 (bb + 256 * q) E34) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
unfold cfg_at. change (w64 A_cbbP) with (Z_to_bv 64 A_cbbP).
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbb_test.
{ awr_ok_tac; [exact Usp | awr_at 34%nat (bb + 256 * q) E34 bb Lbb Hbb; apply awr_ok_nil]. }
clear HF HFr HG.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (19%bv : bv 5) T19. prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (20%bv : bv 5) T20.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
pose proof (ajournal_sub_init SEGS B _ _ _ _ _ _ _ _ _ _ _ W (ms_mem msX) mdX _ CBB_LSTK (spZ regs - 96) [(bb, bb + 256 * q)] (-96)
HJ ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(unfold CBB_LSTK, ESTACK; lia) ltac:(rewrite HS96; unfold CBB_LSTK, ESTACK; lia)) as HJL
end.
pmkst HS.
eapply SRr_bind.
{ eapply (tcbb_blocksX W _ _ _ (spZ regs - 96) ly S bb Lbb bl Lbl q n BL HJL Hbb Hbl ltac:(lia));
[ lia | lia | lia | lia
| unfold spZ at 1; rewrite Rsp, E2; change (bv_unsigned (getr regs 2)) with (spZ regs); rewrite unsigned_lit_small by lia; reflexivity
| rewrite Rgp, E3; exact Hgp | rewrite Rtp, E4; exact Htp
| rewrite T19, E12; reflexivity | rewrite T21, E32; reflexivity | exact T22
| rewrite T8, E11; reflexivity | rewrite T9, E10; reflexivity | rewrite T20, E37; reflexivity
|
cbn [ms_mem]; eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl Lbl bl BL HJ Hbl Hbl); [lia | lia | | exact GBL];
intros a Ha Hf; apply inFP_ablocks_fp_inv in Hf; destruct Hf as (p0 & n0 & [Hq0|[]] & Hr0); injection Hq0 as <- <-; lia
| lia ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJL3 & HK3 & GP3).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msX) _ 0 CBB_LSTK (spZ regs - 96) [(bb, bb + 256 * q)] [] ly S W mem3 md3 0
HJ HJL3 ltac:(rewrite HS96; unfold CBB_LSTK, ESTACK; lia) ltac:(lia)) as HJ3
end.
match type of HJ3 with ?P -> _ => assert (HFP : P); [|specialize (HJ3 HFP); clear HFP] end.
{ intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. left. split.
- replace a with (bb + (a - bb)) by lia. apply (inFP_ablocks_fp _ bb Lbb); [left; reflexivity | lia].
- exists bb, Lbb. split; [exact Hbb | lia]. }
cbn [app] in HJ3.
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ3) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
jafter_stretch_pi HS 38%nat regs3 (mrestrict (w_H W) mem3) TCBB_TCLOB A_cbb_tail HS2.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. destruct (tcbb_tclob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B E); [exact HJL3 | exact HJ3 | exact Usp | lia | rewrite HS96; lia | lia | lia | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia].
- eapply (region_kept_at1 B LAWS E); [exact HJL3 | rewrite E34; apply unsigned_lit_small; lia | exact Hbb | lia | lia |].
intros (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 _) as Et eqn:HE2 in HS. assert (HEIt : img_env VAL A_LIM Et) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 38)%nat -> ew Et k = ew E k) by (intros k Hk; rewrite HE2; apply ew_havoc_old; exact Hk).
assert (HAE2 : env_agree 32 (Ereg regs (tcbb_extra q r bb bl)) Et) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE2 HJ HJL HJL3 HK3 Rsp Rgp Rtp T19 T21 T22 T8 T9 T20 SHOK. rename HJ3 into HJ.
assert (F34 : ew Et 34 = Z_to_bv 64 (bb + 256 * q)) by (rewrite OLD by lia; exact E34).
assert (F33 : ew Et 33 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E33).
assert (F36 : ew Et 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (rewrite OLD by lia; exact E36).
assert (F35 : ew Et 35 = Z_to_bv 64 (bl + 255 * q)) by (rewrite OLD by lia; exact E35).
assert (F32 : ew Et 32 = Z_to_bv 64 q) by (rewrite OLD by lia; exact E32).
assert (F37 : ew Et 37 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E37).
assert (F1 : ew Et 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp2 : bv_unsigned (ew Et 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (HBx2 : U Et Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom Et 37 SB F37) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS Bx [mkSHE 34 1 0] Et (mrestrict (w_H W) mem3)).
{ constructor; [|constructor].
apply (shent_app_of_block SEGS B LAWS ly S W _ _ Et Bx 34 (bb + 256 * q) bb Lbb 0 1 _ (proj1 HJ) Hbb HBx2);
[rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; [exact Usp2 | awr_at 34%nat (bb + 256 * q) F34 bb Lbb Hbb; apply awr_ok_nil]. }
assert (F34u : bv_unsigned (ew Et 34) = bb + 256 * q) by (rewrite F34; apply unsigned_lit_small; lia).
pose proof (cbb_prefix_length BL (Z.to_nat q) ltac:(lia)) as LPq.
xcarryw GP3 HFr (fun a => spZ regs - 96 <= a < spZ regs \/ bb + 256 * q <= a < bb + 256 * q + 1) ltac:(fun h => rewrite ?Usp2, ?F34u in h).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
-
rewrite branch_eq_U, (U_atom Et 33 r F33), U_lit in Hc by lia.
assert (Hr0 : r = 0) by (destruct (Z.eqb_spec r 0); [lia|discriminate]).
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia.
eapply (obl_of_block SEGS B LAWS ly S W _ _ Et Bx _ 1 bb Lbb (proj1 HJ) Hbb HBx2); lia. }
{ awr_ok_tac; [exact Usp2 | awr_at 34%nat (bb + 256 * q) F34 bb Lbb Hbb; apply awr_ok_nil]. }
xcarryw GP3 HFr (fun a => spZ regs - 96 <= a < spZ regs \/ bb + 256 * q <= a < bb + 256 * q + 1) ltac:(fun h => rewrite ?Usp2, ?F34u in h).
xregbyte V0 HS 3%nat (bb + 256 * q) 0 F34u ltac:(reflexivity).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split; [cbn [ms_regs]; rewrite Rra; cbn [ew ewset Nat.eqb]; rewrite F1, Hra; reflexivity|].
split; [|split].
+ cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
+ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (tcbb_extra q r bb bl) HS); [|vm_compute; reflexivity].
env_agree_chain HAE2.
+ split.
{ cbn [ms_regs]. rewrite Ra0. cbn [ew ewset Nat.eqb]. rewrite F32, alu64_sll_lit by lia.
unfold w64. f_equal. rewrite (proj2 (Z.eqb_eq r 0) Hr0). lia. }
rewrite (proj2 (Z.eqb_eq r 0) Hr0). split; [|lia]. cbn [ms_mem].
apply garr8_app. split; [exact GP3|]. rewrite LPq. replace (bb + Z.of_nat (256 * Z.to_nat q)) with (bb + 256 * q + 0) by lia.
apply garr8_cons_x; [exact V0 | lia | apply garr8_nil].
-
rewrite branch_eq_U, (U_atom Et 33 r F33), U_lit in Hc by lia.
assert (Hr1 : r <> 0) by (destruct (Z.eqb_spec r 0); [discriminate|lia]).
assert (Hlen2 : 256 * q + r + 2 <= Lbb) by (destruct (Z.eqb_spec r 0); lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msX) =>
pose proof (st_ok_pi_add_region Et ss (restrict (w_H W) msX) (reg_at 36) HS eq_refl) as HS2
end.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ unfold region_ok, reg_at. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
rewrite F36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS).
destruct (al_blocks _ _ LAWS ly S W _ _ bb Lbb (proj1 HJ) Hbb) as (_ & _ & _ & _ & HbbpresT & _). apply HbbpresT. lia. }
{ unfold add_cond. cbn [ss_mem all_disjoint]. unfold extent_disjoint, reg_at.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F36, F34, Usp2, !unsigned_lit_small by lia.
rewrite (HEIt 241%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEIt 253%nat ltac:(unfold A_TEXT, A_LIM; lia)). pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 12 ltac:(lia)) as Ho12. unfold A_OBJ, A_TEXT in Ho0, Ho12. cbn [Nat.add] in Ho0, Ho12. repeat split; zone_lia. }
clear HS. unfold add_cond in HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS2. rename HS2 into HS.
lazymatch type of SHOK with sh_ok _ _ _ _ ?MM =>
clear SHOK; assert (SHOK : sh_ok SEGS Bx [mkSHE 36 1 0; mkSHE 34 1 0] Et MM) end.
{ constructor; [|constructor; [|constructor]].
- apply (shent_app_of_block SEGS B LAWS ly S W _ _ Et Bx 36 (bb + 256 * q + r + 1) bb Lbb 0 1 _ (proj1 HJ) Hbb HBx2);
[rewrite (U_atom Et 36 (bb + 256 * q + r + 1) F36) by lia; reflexivity | lia | lia | pose proof HrB; lia].
- apply (shent_app_of_block SEGS B LAWS ly S W _ _ Et Bx 34 (bb + 256 * q) bb Lbb 0 1 _ (proj1 HJ) Hbb HBx2);
[rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite (U_atom Et 34 (bb + 256 * q) F34) by lia.
eapply (obl_of_block SEGS B LAWS ly S W _ _ Et Bx _ 1 bb Lbb (proj1 HJ) Hbb HBx2); lia. }
{ awr_ok_tac. awr_at 36%nat (bb + 256 * q + r + 1) F36 bb Lbb Hbb.
awr_ok_tac; [ exact Usp2 | awr_at 34%nat (bb + 256 * q) F34 bb Lbb Hbb; apply awr_ok_nil ]. }
assert (F36u : bv_unsigned (ew Et 36) = bb + 256 * q + r + 1) by (rewrite F36; apply unsigned_lit_small; lia).
xcarryw GP3 HFr (fun a => spZ regs - 96 <= a < spZ regs \/ bb + 256 * q + r + 1 <= a < bb + 256 * q + r + 2 \/ bb + 256 * q <= a < bb + 256 * q + 1) ltac:(fun h => rewrite ?Usp2, ?F34u, ?F36u in h).
xregbyte Vr HS 4%nat (bb + 256 * q) r F34u ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite F33, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
cbn [ew ewset Nat.eqb] in Ra0, Ra1, Ra2, Rra, Rsp, Rgp, Rtp.
pmkst HS.
pose proof (proj1 HJ) as HAR4.
destruct (al_blocks _ _ LAWS ly S W _ _ bl Lbl HAR4 Hbl) as (_ & _ & _ & _ & Hblpres4 & _).
destruct (al_blocks _ _ LAWS ly S W _ _ bb Lbb HAR4 Hbb) as (_ & _ & _ & _ & Hbbpres4 & _).
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AIMC W _ _ CBB_STK (spZ regs) _ ly S W mem md [] ly S _ 0
(bb + 256 * q + 1) (bl + 255 * q) r (-96) (Z_to_bv 64 (BASE + 0x2968)) HJ).
- rewrite Ra0, F34. unfold w64. rewrite unsigned_lit_small by lia. first [reflexivity | f_equal; lia].
- rewrite Ra1, F35. reflexivity.
- rewrite Ra2, F33. reflexivity.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp, Usp2, unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite HS96. unfold ESTACK. lia.
- rewrite Rgp, OLD, E3 by lia. exact Hgp.
- rewrite Rtp, OLD, E4 by lia. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
+ right. left. split.
* replace a with (bb + (a - bb)) by lia. apply (inFP_ablocks_fp _ bb Lbb); [left; reflexivity | lia].
* exists bb, Lbb. split; [exact Hbb | lia].
+ unfold ESTACK. intros Hx. lia.
- apply (amem_range_of_block SEGS B LAWS ly S W _ _ bb Lbb _ _ HAR4 Hbb); lia.
- apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bb Lbb _ _ HAR4 Hbb); lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bb Lbb _ _ HAR4 Hbb); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp, Usp2, unsigned_lit_small by lia; intro; lia].
apply (aview_some_of_apresent SEGS). apply (proj1 (Hblpres4 a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS ly S W _ _ bl Lbl _ _ HAR4 Hbl); lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bl Lbl _ _ HAR4 Hbl); lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bl Lbl _ _ HAR4 Hbl); lia. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha0' & Heff & Hout5 & Hpres5).
assert (GP5 : garr8 SEGS (mrestrict (w_H W) mem5) bb (cbb_prefix BL (Z.to_nat q))).
{ lazymatch type of GP3 with garr8 _ (mrestrict _ ?mm) _ _ => apply (garr8_aview_kept SEGS (w_H W) (w_H W) mm mem5); [|exact GP3] end. rewrite LPq. intros a Ha. apply Hout5; [lia | lia | unfold ESTACK; lia]. }
assert (Vr5 : val_mem SEGS (mrestrict (w_H W) mem5) (bb + 256 * q + 0) (N.to_nat 1) r).
{ lazymatch type of Vr with val_mem _ (mrestrict _ ?mm) _ _ _ => apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mm mem5); [|exact Vr] end. intros x Hx. cbn in Hx. apply Hout5; [lia | lia | unfold ESTACK; lia]. }
assert (GR5 : garr8 SEGS (mrestrict (w_H W) mem5) (bb + 256 * q + 1) (skipn (255 * Z.to_nat q) BL)).
{ lazymatch type of Heff with (forall i, _ -> aview _ _ _ _ = aview _ _ ?mm _) =>
assert (GBL4 : garr8 SEGS (mrestrict (w_H W) mm) bl BL)
by (eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl Lbl bl BL HJ Hbl Hbl); [lia | lia | | exact GBL];
intros a Ha Hf; apply inFP_ablocks_fp_inv in Hf; destruct Hf as (p0 & n0 & [Hq0|[]] & Hr0); injection Hq0 as <- <-; lia) end.
lazymatch type of GBL4 with garr8 _ (mrestrict _ ?mm) _ _ => apply (garr8_aview SEGS (w_H W) (w_H W) mm mem5 (bl + 255 * q)) end.
- rewrite ESK. intros j Hj. apply Heff. lia.
- replace (bl + 255 * q) with (bl + Z.of_nat (255 * Z.to_nat q)) by lia.
replace (skipn (255 * Z.to_nat q) BL) with (firstn (Z.to_nat r) (skipn (255 * Z.to_nat q) BL))
by (rewrite <- ESK; apply firstn_all).
apply (garr8_sub_x SEGS _ bl BL (255 * Z.to_nat q) (Z.to_nat r) GBL4). lia. }
jafter_call_keep_pi HS 60%nat regs5 (mrestrict (w_H W) mem5) HP5 [0; 1]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5' & _).
repeat apply Forall_cons; [| | apply Forall_nil].
-
split; unfold reg_at; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
cbn [ew ewset Nat.eqb]; rewrite F36, unsigned_lit_small by lia; intros a Ha.
+ apply (mbyte_of_aview SEGS). apply Hout5; [lia | lia | unfold ESTACK; lia].
+ intros _. apply (apresent_writable SEGS). apply Hpres5. apply (proj1 (Hbbpres4 a ltac:(lia))).
-
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
cbn [ew ewset Nat.eqb]; rewrite Usp2; intros a Ha.
+ apply (mbyte_of_aview SEGS). apply Hout5; [lia | lia | unfold ESTACK; lia].
+ intros _. apply (apresent_writable SEGS). apply Hpres5'. rewrite HS96. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 60 _) as E5 eqn:HE5 in HS. assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD5 : forall k, (k < 38)%nat -> ew E5 k = ew Et k).
{ intros k Hk. rewrite HE5, ew_havoc_old by lia. rewrite !ew_ewset_other by lia. reflexivity. }
assert (HAE5 : env_agree 32 (Ereg regs (tcbb_extra q r bb bl)) E5) by (rewrite HE5; env_agree_chain HAE2).
clear HE5.
assert (G36 : ew E5 36 = Z_to_bv 64 (bb + 256 * q + r + 1)) by (rewrite OLD5 by lia; exact F36).
assert (G32 : ew E5 32 = Z_to_bv 64 q) by (rewrite OLD5 by lia; exact F32).
assert (G33 : ew E5 33 = Z_to_bv 64 r) by (rewrite OLD5 by lia; exact F33).
assert (G1 : ew E5 1 = getr regs 1) by (rewrite OLD5 by lia; exact F1).
assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Usp2).
assert (G37 : ew E5 37 = Z_to_bv 64 SB) by (rewrite OLD5 by lia; exact F37).
assert (HBx5 : U E5 Bx = SHADOW_OFF) by (unfold Bx; rewrite (U_atom E5 37 SB G37) by (unfold SB; lia); reflexivity).
assert (SHOK5 : sh_ok SEGS Bx [mkSHE 36 1 0] E5 (mrestrict (w_H W) mem5)).
{ constructor; [|constructor].
apply (shent_app_of_block SEGS B LAWS ly S W _ _ E5 Bx 36 (bb + 256 * q + r + 1) bb Lbb 0 1 _ (proj1 HJ5) Hbb HBx5);
[rewrite (U_atom E5 36 (bb + 256 * q + r + 1) G36) by lia; reflexivity | lia | lia | pose proof HrB; lia]. }
paj_run_tok RUN HS HJ5 SHOK5 Bspan.
{ rewrite (U_atom E5 36 (bb + 256 * q + r + 1) G36) by lia.
eapply (obl_of_block SEGS B LAWS ly S W _ _ E5 Bx _ 1 bb Lbb (proj1 HJ5) Hbb HBx5); lia. }
{ awr_ok_tac. awr_at 36%nat (bb + 256 * q + r + 1) G36 bb Lbb Hbb. awr_ok_tac. exact Usp5. }
assert (G36u : bv_unsigned (ew E5 36) = bb + 256 * q + r + 1) by (rewrite G36; apply unsigned_lit_small; lia).
xcarryw GP5 HFr (fun a => bb + 256 * q + r + 1 <= a < bb + 256 * q + r + 2 \/ spZ regs - 96 <= a < spZ regs) ltac:(fun h => rewrite ?Usp5, ?G36u in h).
xcarryw GR5 HFr (fun a => bb + 256 * q + r + 1 <= a < bb + 256 * q + r + 2 \/ spZ regs - 96 <= a < spZ regs) ltac:(fun h => rewrite ?Usp5, ?G36u in h).
xcarryv Vr5 HFr (fun a => bb + 256 * q + r + 1 <= a < bb + 256 * q + r + 2 \/ spZ regs - 96 <= a < spZ regs) ltac:(fun h => rewrite ?Usp5, ?G36u in h).
xregbyte V05 HS 0%nat (bb + 256 * q + r + 1) 0 G36u ltac:(reflexivity).
prreg HS (10%bv : bv 5) Rb0. prreg HS (1%bv : bv 5) Rra5.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
split; [cbn [ms_regs]; rewrite Rra5; cbn [ew ewset Nat.eqb]; rewrite G1, Hra; reflexivity|].
split; [|split].
+ cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ5.
+ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (tcbb_extra q r bb bl) HS); [env_agree_chain HAE5 | vm_compute; reflexivity].
+ split.
{ cbn [ms_regs]. rewrite Rb0. cbn [ew ewset Nat.eqb]. rewrite G32, G33, alu64_sll_lit, !alu64_add_lit by lia.
unfold w64. f_equal. destruct (Z.eqb_spec r 0); lia. }
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr1). split; [|lia]. cbn [ms_mem].
apply garr8_app. split; [exact GP5|]. rewrite LPq. replace (bb + Z.of_nat (256 * Z.to_nat q)) with (bb + 256 * q + 0) by lia.
apply garr8_cons_x; [exact Vr5 | lia |]. replace (bb + 256 * q + 0 + 1) with (bb + 256 * q + 1) by lia.
apply garr8_app. split; [exact GR5|]. rewrite ESK. replace (bb + 256 * q + 1 + Z.of_nat (Z.to_nat r)) with (bb + 256 * q + r + 1 + 0) by lia.
apply garr8_cons_x; [exact V05 | lia | apply garr8_nil].
Qed.
End f.
End e.
End c.
