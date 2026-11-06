(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LQT_HEAD : Z := 0x83e2c.
Definition LQT_BR : Z := 0x83e84.
Definition LQT_EXIT : Z := 0x83eac.
Definition LQT_CLOB : list (bv 5) := [5; 6; 7; 10; 11; 12; 17]%bv.
Definition LQT_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lqt_clob_cases : forall r : bv 5, reg_in r LQT_CLOB = false -> r = 0%bv \/ In r LQT_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Section d.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (ib nI img flt nF M : Z).
Hypothesis HinI : In (ib, nI) (ablocks B lyc Sc). Hypothesis HI0 : ib <= img. Hypothesis HI1 : img + M <= ib + nI.
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc). Hypothesis HF1 : 4 * M <= nF.
Hypothesis HIF : (ib, nI) <> (flt, nF).
Hypothesis HM : 0 < M < 2 ^ 32.
Hypothesis HFW : forall blc lyq ownq i, In (flt, nF) blc -> 0 <= i < req_size nF ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + i).
Definition lqt_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (j : Z) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\
getr regs 10 = w64 (img + j) /\ getr regs 17 = w64 (img + j) /\
getr regs 12 = w64 (4 * j) /\ getr regs 15 = w64 (4 * M) /\
getr regs 13 = w64 (2 ^ 64 - 1 - flt) /\ getr regs 14 = w64 0 /\ getr regs 16 = w64 1 /\
getr regs 29 = w64 img /\ getr regs 23 = w64 flt /\ getr regs 27 = w64 SB.
Lemma lqt_env : forall fy regs mem md j, lqt_inv fy regs mem md j ->
4096 <= ib /\ ib + req_size nI <= alloc_ceiling /\ 4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\
nI <= req_size nI /\ nF <= req_size nF /\ 140735332483072 <= alloc_ceiling <= 140737479966720 /\
(ib + req_size nI <= flt \/ flt + req_size nF <= ib).
Proof.
intros fy regs mem md j (HJ & _). pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ib nI HAR HinI) as (_ & Hi4096 & Hiceil & _ & _ & _ & Hni0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nI ltac:(lia)) as [_ HrI]. pose proof (req_size_pos nF ltac:(lia)) as [_ HrF].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ ib nI flt nF HAR HinI HinF HIF) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
repeat split; try assumption; try lia.
Qed.
Definition lq_regs := sr_set (sr_set (sr_set sr_atoms 17%bv (SOff 10 0)) 16%bv (SLit 1)) 14%bv (SLit 0).
Definition lq_mem : smem :=
[ YQ0b.mkRegion (Some 10%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 32 0))];
YQ0b.mkRegion (Some 33%nat) 0 4 0 4 [] ].
Definition lq_alias : sv := SAlu ALU_ADD (SOff 23 0) (SOff 12 0).
Definition lq_facts : facts :=
mkFacts [ (10%nat, mkAF 4096 140737479966720 0); (12%nat, mkAF 0 (2^34) 0); (13%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0);
(27%nat, mkAF SB SB 0); (29%nat, mkAF 4096 140737479966720 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 140737479966720 2) ]
[ mkAC BC_GEU (SOff 10 0) (SOff 29 0) ] [ (lq_alias, SOff 33 0) ].
Definition ss_LQx : sstate := mkSS LQT_HEAD lq_regs lq_mem None lq_facts.
Definition lq_Bx : sv := SOff 27 0.
Definition lq_SH : list shent := [ mkSHE 10 0 1; mkSHE 33 0 4 ].
Definition lq_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma LQ_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (j v : Z),
0 <= j < M -> lqt_inv fy regs mem md j ->
mbyte trbsegs (mrestrict (w_H W) mem) (img + j) = Some (Z_to_bv 8 v) -> 0 <= v < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [v; flt + 4 * j] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LQT_HEAD lq_regs (sfr_atoms 64) lq_mem None lq_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LQT_HEAD) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lq_Bx lq_SH E (mrestrict (w_H W) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
bv_unsigned (ew E 10) = img + j /\ bv_unsigned (ew E 12) = 4 * j /\ bv_unsigned (ew E 15) = 4 * M /\ bv_unsigned (ew E 33) = flt + 4 * j.
Proof.
intros fy regs mem md j v Hj HI Hbyte Hv E0 E.
pose proof (lqt_env fy regs mem md j HI) as (Qib0 & Qib1 & Qf0 & Qf1 & Qf16 & QnI & QnF & C1 & Qsep).
pose proof HI as (HJ & Hfrm & G10 & G17 & G12 & G15 & G13 & G14 & G16 & G29 & G23 & G27).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall i x, nth_error [v; flt + 4 * j] i = Some x -> ew E0 (32 + i) = Z_to_bv 64 x) by (intros i x Hi; subst E0; apply Ereg_vals; exact Hi).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (U10 : bv_unsigned (ew E0 10) = img + j) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Hj HI0 HI1 Qib0 Qib1 QnI C1; lia).
assert (U12 : bv_unsigned (ew E0 12) = 4 * j) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hj HM; lia).
assert (U15 : bv_unsigned (ew E0 15) = 4 * M) by (rewrite (HE0 15%nat 15%bv eq_refl), G15; apply unsigned_lit_small; clear - HM; lia).
assert (U13 : bv_unsigned (ew E0 13) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; clear - HM HF1 Qf0 Qf1 QnF C1; lia).
assert (U23 : bv_unsigned (ew E0 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - HM HF1 Qf0 Qf1 QnF C1; lia).
assert (U29 : bv_unsigned (ew E0 29) = img) by (rewrite (HE0 29%nat 29%bv eq_refl), G29; apply unsigned_lit_small; clear - HI0 HI1 HM Qib0 Qib1 QnI C1; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A32 : bv_unsigned (ew E0 32) = v).
{ pose proof (HV 0%nat v eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Hv. lia. }
assert (A33 : bv_unsigned (ew E0 33) = flt + 4 * j).
{ pose proof (HV 1%nat (flt + 4 * j) eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Hj HF1 Qf0 Qf1 QnF C1. lia. }
assert (DN : forall n x, bv_unsigned (ew E0 n) = x -> sv_denot E0 (SOff n 0) = Z_to_bv 64 x).
{ intros n x Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trbsegs fy E0 ss_LQx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LQT_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LQx, lq_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite G17. cbn [sv_denot]. fold E0. rewrite U10, Z.add_0_r. reflexivity.
+ rewrite G16. cbn [sv_denot]. reflexivity.
+ rewrite G14. cbn [sv_denot]. reflexivity.
- vm_compute. reflexivity.
- unfold lq_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U10.
split; [clear - Hj HI0 Qib0; lia|]. split; [clear - Hj HI0 HI1 Qib1 QnI C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (img + j) 0 1 _ v); [exact (DN _ _ A32) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; exact Hbyte | exact Hv].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite A33.
split; [clear - Hj Qf0; lia|]. split; [clear - Hj HF1 Qf1 QnF C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hfpres (flt + 4 * j + o) ltac:(clear - Ho Hj HF1 QnF; lia))).
- apply pairwise_disjoint_of_extents. unfold lq_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs ([Z_to_bv 64 v; Z_to_bv 64 (flt + 4 * j)] ++ [])) with E0. rewrite U10, A33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hj HI0 HI1 HF1 QnI QnF Qsep. repeat split; lia.
- split; [|split; [split; [|exact I] | split; [|exact I]]].
+ cbn [lq_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
rewrite U10, U12, U13, E27, U29, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hf4 : (flt + 4 * j) mod 4 = 0).
{ replace (flt + 4 * j) with (flt + j * 4) by lia. rewrite Z.mod_add by lia.
clear - Qf16. pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - Hj HM HI0 HI1 HF1 Qib0 Qib1 Qf0 Qf1 QnI QnF C1 Hv Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+
unfold acond_ok. cbn [ac_c ac_a ac_b]. fold E0. rewrite YO3v.branch_geu_U, !U_SOff, U10, U29, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Hj HI0 HI1 HM Qib0 Qib1 QnI C1; lia).
apply Bool.negb_true_iff, Z.ltb_ge. clear - Hj. lia.
+
fold E0. unfold lq_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U23, U12, A33, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id (4 * j)), (zcanon_id (flt + 4 * j)) by (unfold M64; clear - Hj HM HF1 Qf0 Qf1 QnF C1; lia).
reflexivity. }
assert (SHOK0 : sh_ok trbsegs lq_Bx lq_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lq_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lq_Bx 10 (img + j) 1 (img + j) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md ib nI _ _ HAR HinI); clear - Hj HI0 HI1 QnI; lia.
+ unfold U, lq_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
+ lia.
+ lia.
+ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ ib nI HAR HinI) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ ib nI HAR HinI) as Himg.
revert Hx Hia Himg Hj HI0 HI1 QnI Qib0 Qib1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lq_Bx 33 (flt + 4 * j) 4 (flt + 4 * j) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hj HF1 QnF; lia.
+ unfold U, lq_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Himg.
revert Hx Hia Himg Hj HF1 QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LQx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lq_Bx lq_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
rewrite !HEE by lia. repeat split; assumption.
Qed.
Lemma lq_kept_win : forall E0 rs (H : word -> bool) (m m' : word -> option byte) (n : nat) b lo hi,
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some n /\ lo <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= hi)) ->
bv_unsigned (ew E0 n) = b ->
forall x, 0 <= x < 2 ^ 64 -> ~ (b + lo <= x < b + hi) -> aview trbsegs H m' x = aview trbsegs H m x.
Proof.
intros E0 rs H m m' n b lo hi HF Hrs Hb x Hx Hnw. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). destruct (Hrs rr Hin) as [Hro | (Hbs & Hlo & Hhi)]; [lia|].
rewrite Hbs in Hr. cbn [base_val] in Hr. rewrite Hb in Hr. lia.
Qed.
Local Ltac aj_branchF tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (st_okF_branch segs E ss ms _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "aj_branchF: state is not stuck at a branch:" why
end
end
end.
Local Ltac lq_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold lq_mem in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Definition LQT_KEEPA : list (bv 5) := [1; 2; 3; 4; 8; 9; 13; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lqt_keep_cases : forall r : bv 5, In r LQT_KEEP -> r = 14%bv \/ r = 16%bv \/ In r LQT_KEEPA.
Proof.
intros r Hr. cbv [LQT_KEEP In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [left; reflexivity | right; left; reflexivity | right; right; cbv; tauto] |]). destruct Hr.
Qed.
Lemma LQT_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (j : Z),
0 <= j < M -> lqt_inv fy regs mem md j ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LQT_HEAD) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if j + 1 <? M then LQT_HEAD else LQT_EXIT)) mem' (seg_rom trbsegs)) md' /\
lqt_inv fy' regs' mem' md' (j + 1) /\
(forall r : bv 5, In r LQT_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * j <= a < flt + 4 * j + 4) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md j Hj HI.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (lqt_env fy regs mem md j HI) as (Qib0 & Qib1 & Qf0 & Qf1 & Qf16 & QnI & QnF & C1 & Qsep).
pose proof HI as (HJ & Hfrm & G10 & G17 & G12 & G15 & G13 & G14 & G16 & G29 & G23 & G27).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ib nI HAR HinI) as (_ & _ & _ & _ & Hipres & _).
destruct (proj1 (Hipres (img + j) ltac:(clear - Hj HI0 HI1 QnI; lia))) as (Hhid & bb & Hbb).
assert (Hbyte : mbyte trbsegs (mrestrict (w_H W) mem) (img + j) = Some (Z_to_bv 8 (bv_unsigned bb))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hbb, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 bb) as Hbr. change (bv_modulus 8) with 256 in Hbr.
destruct (LQ_seed fy regs mem md j (bv_unsigned bb) Hj HI Hbyte Hbr) as (HS & SHOK & HE & HU10 & HU12 & HU15 & HU33).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HU10, HU12, HU15, HU33.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lq_Bspan LQT_BR.
{ cbn [ss_mem]. unfold lq_mem. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact HU33 | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hj HF1 QnF; lia]. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * j <= a < flt + 4 * j + 4) -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) mem a).
{ intros a Ha Hnw. apply (lq_kept_win _ _ _ _ _ 33%nat (flt + 4 * j) 0 4 HFr1); [lq_rs_tac | exact HU33 | exact Ha | clear - Hnw; lia]. }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc', @st_ok trbsegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 10 = SOff 10 1 -> sr_get (ss_regs ss') 17 = SOff 10 1 ->
sr_get (ss_regs ss') 12 = SOff 12 4 -> sr_get (ss_regs ss') 14 = SLit 0 -> sr_get (ss_regs ss') 16 = SLit 1 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LQT_KEEPA = true ->
frm_zero (@fp_csr fz) ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * j <= a < flt + 4 * j + 4) -> aview trbsegs (w_H W) (ms_mem ms') a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trbsegs W (mkCfg ms' md')
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md'',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc') mem' (seg_rom trbsegs)) md'' /\
lqt_inv fy' regs' mem' md'' (j + 1) /\
(forall r : bv 5, In r LQT_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * j <= a < flt + 4 * j + 4) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros fz E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q10 Q17 Q12 Q14 Q16 QK Hfz HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [bv_unsigned bb; flt + 4 * j] ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LQT_KEEPA HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
assert (HKR' : forall r : bv 5, In r LQT_KEEP -> getr (ms_regs ms') r = getr regs r).
{ intros r Hr. destruct (lqt_keep_cases r Hr) as [-> | [-> | Hin]]; [ | | exact (HKR r Hin)].
- rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (14%bv : bv 5) HS'), Q14, G14. reflexivity.
- rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (16%bv : bv 5) HS'), Q16, G16. reflexivity. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (10%bv : bv 5) HS'), Q10; cbn [sv_denot]; rewrite EA, HU10 by lia; unfold w64; f_equal; lia|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (17%bv : bv 5) HS'), Q17; cbn [sv_denot]; rewrite EA, HU10 by lia; unfold w64; f_equal; lia|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (12%bv : bv 5) HS'), Q12; cbn [sv_denot]; rewrite EA, HU12 by lia; unfold w64; f_equal; lia|].
split; [rewrite (HKR' (15%bv : bv 5) ltac:(cbv; tauto)); exact G15|].
split; [rewrite (HKR' (13%bv : bv 5) ltac:(cbv; tauto)); exact G13|].
split; [rewrite (HKR' (14%bv : bv 5) ltac:(cbv; tauto)); exact G14|].
split; [rewrite (HKR' (16%bv : bv 5) ltac:(cbv; tauto)); exact G16|].
split; [rewrite (HKR' (29%bv : bv 5) ltac:(cbv; tauto)); exact G29|].
split; [rewrite (HKR' (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
rewrite (HKR' (27%bv : bv 5) ltac:(cbv; tauto)). exact G27. }
split; [exact HKR'|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_branchF trbtbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
rewrite branch_ne_U, !U_SOff in Hc. rewrite !(proj1 HAEx) in Hc by lia. rewrite HU15, HU12, !zcanon_id in Hc by (unfold M64; clear - Hj HM; lia).
apply Bool.negb_true_iff, Z.eqb_neq in Hc.
replace (j + 1 <? M) with true by (symmetry; apply Z.ltb_lt; clear - Hc Hj; lia).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (U33X : bv_unsigned (ew Ex 33) = flt + 4 * j) by (rewrite (proj1 HAEx) by lia; exact HU33) end.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK lq_Bspan LQT_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact U33X | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hj HF1 QnF; lia]. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ LQT_HEAD HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HJ | | ].
+ intros a Ha Hnw. rewrite (lq_kept_win _ _ _ _ _ 33%nat (flt + 4 * j) 0 4 HFr ltac:(lq_rs_tac) U33X a Ha ltac:(clear - Hnw; lia)). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
rewrite branch_ne_U, !U_SOff in Hc. rewrite !(proj1 HAEx) in Hc by lia. rewrite HU15, HU12, !zcanon_id in Hc by (unfold M64; clear - Hj HM; lia).
apply Bool.negb_false_iff, Z.eqb_eq in Hc.
replace (j + 1 <? M) with false by (symmetry; apply Z.ltb_ge; clear - Hc Hj; lia).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (U33X : bv_unsigned (ew Ex 33) = flt + 4 * j) by (rewrite (proj1 HAEx) by lia; exact HU33) end.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK lq_Bspan LQT_EXIT.
{ apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact U33X | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hj HF1 QnF; lia]. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ LQT_EXIT HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HJ | | ].
+ intros a Ha Hnw. rewrite (lq_kept_win _ _ _ _ _ 33%nat (flt + 4 * j) 0 4 HFr ltac:(lq_rs_tac) U33X a Ha ltac:(clear - Hnw; lia)). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma LQT_loop : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (j : Z),
0 <= j < M -> Z.of_nat n = M - 1 - j -> lqt_inv fy regs mem md j ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LQT_HEAD) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LQT_EXIT) mem' (seg_rom trbsegs)) md' /\
lqt_inv fy' regs' mem' md' M /\
(forall r : bv 5, In r LQT_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * j <= a < flt + 4 * M) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
induction n as [|n IH]; intros fy regs mem md j Hj Hn HI.
- assert (Hlast : j + 1 = M) by lia.
eapply SRr_mono; [exact (LQT_step fy regs mem md j Hj HI)|].
cbv beta. intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & HI' & Hk' & Hm' & Hp').
replace (j + 1 <? M) with false in Hc by (symmetry; apply Z.ltb_ge; lia). rewrite Hlast in HI'.
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HI'|]. split; [exact Hk'|].
split; [|exact Hp']. intros a Ha Hna. apply Hm'; [exact Ha | lia].
- eapply SRr_bind; [exact (LQT_step fy regs mem md j Hj HI)|].
cbv beta. intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hm' & Hp').
replace (j + 1 <? M) with true by (symmetry; apply Z.ltb_lt; lia).
eapply SRr_mono; [exact (IH fy' regs' mem' md' (j + 1) ltac:(lia) ltac:(lia) HI')|].
cbv beta. intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc & HI'' & Hk'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc|]. split; [exact HI''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros a Ha Hna; rewrite (Hm'' a Ha ltac:(lia)); apply Hm'; [exact Ha | lia]|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
End d.
Lemma rga_lqt {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W ib nI img flt nF M (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (ib, nI) (ablocks B lyc Sc) -> ib <= img -> img + M <= ib + nI ->
In (flt, nF) (ablocks B lyc Sc) -> 4 * M <= nF -> (ib, nI) <> (flt, nF) -> 0 < M < 2 ^ 32 ->
(forall blc lyq ownq i, In (flt, nF) blc -> 0 <= i < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + i)) ->
getr regs 10 = w64 img -> getr regs 17 = w64 img -> getr regs 12 = w64 0 -> getr regs 15 = w64 (4 * M) ->
getr regs 13 = w64 (2 ^ 64 - 1 - flt) -> getr regs 14 = w64 0 -> getr regs 16 = w64 1 ->
getr regs 29 = w64 img -> getr regs 23 = w64 flt -> getr regs 27 = w64 SB ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LQT_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LQT_EXIT) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LQT_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 10 = w64 (img + M) /\ getr regs2 17 = w64 (img + M) /\ getr regs2 12 = w64 (4 * M) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W ib nI img flt nF M fy regs memc mdc
HJ Hfrm HinI HI0 HI1 HinF HF1 HIF HM HFW G10 G17 G12 G15 G13 G14 G16 G29 G23 G27.
assert (HI : lqt_inv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W img flt M fy regs memc mdc 0).
{ split; [exact HJ|]. split; [exact Hfrm|]. replace (img + 0) with img by lia. replace (4 * 0) with 0 by lia. repeat split; assumption. }
eapply SRr_mono; [exact (LQT_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W ib nI img flt nF M HinI HI0 HI1 HinF HF1 HIF HM HFW
(Z.to_nat (M - 1)) fy regs memc mdc 0 ltac:(lia) ltac:(lia) HI)|].
cbv beta. intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc & (HJ2 & Hfrm2 & R10 & R17 & R12 & _) & Hk & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lqt_clob_cases r Hr) as [-> | Hin]; [|exact (Hk r Hin)].
rewrite !getr_zero. reflexivity. }
split; [exact R10|]. split; [exact R17|]. split; [exact R12|].
split; [|exact Hp]. intros a Ha Hna. apply Hm; [exact Ha | lia].
Qed.
