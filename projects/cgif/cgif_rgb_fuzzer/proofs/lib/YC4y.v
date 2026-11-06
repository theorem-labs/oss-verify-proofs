(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition GP_TEST : Z := 0x853f4.
Definition GP_RET1 : Z := 0x85418.
Definition LAY_GPF : layout_t := [(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N)].
Definition gpf_vals (regs0 : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1)].
Section GP.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Definition gp_post (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem0 md0 own lyc Sc (W : world trasegs)
(mem : word -> option byte) (k lo hi pal : Z) : world trasegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists (fx' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs0 1) mem2 (seg_rom trasegs)) md2 /\ frm_zero (@fp_csr fx') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs0 regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (pal <= a < pal + 768) ->
aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a).
Definition gp_R_stmt (u : tree) : Prop :=
forall (fy : FPState) (regs0 regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (pal cid pos : Z) (d : nat),
let sp := spZ regs0 in
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(tree_height u <= d)%nat -> tree_full u ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - GP_STK (Z.of_nat d) -> sp <= sp0 ->
frm_zero (@fp_csr fy) ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF pal 768 ->
getr regs 2 = w64 (sp - 32) -> getr regs 8 = w64 pal -> getr regs 9 = w64 (troot u) -> getr regs 10 = w64 (troot u + 50) ->
getr regs 18 = w64 SB ->
(forall r : bv 5, In r CALLEE_SAVED -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> getr regs r = getr regs0 r) ->
obj_at trasegs (mrestrict (w_H W) mem) (sp - 32) LAY_GPF (gpf_vals regs0) ->
(forall b, In b (tree_blocks u) -> In b (ablocks B lyc Sc)) ->
tree_at trasegs (mrestrict (w_H W) mem) u ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 GP_TEST) mem (seg_rom trasegs)) md)
(gp_post regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k (sp - GP_STK (Z.of_nat d)) (sp - 32) pal).
Definition gp_P_stmt (t : tree) : Prop :=
forall (fy : FPState) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (pal cid pos : Z) (d : nat),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(tree_height t <= d)%nat -> tree_full t ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 (troot t) -> getr regs 11 = w64 pal ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - GP_STK (Z.of_nat d) -> spZ regs <= sp0 ->
frm_zero (@fp_csr fy) ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trasegs (w_H W) memc) SHADOW_OFF pal 768 ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
tree_at trasegs (mrestrict (w_H W) memc) t ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 A_get_palette) memc (seg_rom trasegs)) mdc)
(gp_post regs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (spZ regs - GP_STK (Z.of_nat d)) (spZ regs) pal).
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Definition gp_lits (leafv : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some leafv].
Definition gp_alias : list (sv * sv) := [(SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 44 0) (SLit 3)), SOff 46 0)].
Definition gp_mem (leafv : Z) : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 32 0 0 (obj_chunks_from LAY_GPF 32);
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 36 (gp_lits leafv));
YQ0b.mkRegion (Some 46%nat) 0 3 0 3 [] ].
Definition gp_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 4096 140737479966720 4); (18%nat, mkAF SB SB 0);
(44%nat, mkAF 0 255 0); (46%nat, mkAF 4096 140737479966720 0) ] [] gp_alias.
Definition ss_gp (pin : bool) (pc leafv : Z) : sstate :=
mkSS pc (if pin then sr_set sr_atoms 10%bv (SOff 9 50) else sr_atoms) (gp_mem leafv) None gp_facts.
Definition gp_Bx : sv := SOff 18 0.
Definition gp_SH : list shent := [ mkSHE 9 0 NODE_SIZE; mkSHE 46 0 3 ].
Definition gp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gp_extra (regs0 : bvmap 5 word) (c0 c1 : Z) (n : tnode) (leafv pal : Z) : list word :=
map (Z_to_bv 64) (gpf_vals regs0 ++ node_vals c0 c1 n leafv) ++ [Z_to_bv 64 (pal + 3 * tn_cidx n)].
Lemma u64_range8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma gp_E46 : forall regs regs0 c0 c1 n leafv pal, length (tn_mean n) = 3%nat ->
ew (Ereg regs (gp_extra regs0 c0 c1 n leafv pal)) 46 = Z_to_bv 64 (pal + 3 * tn_cidx n).
Proof.
intros regs regs0 c0 c1 n leafv pal Hlen. unfold gp_extra. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
assert (HL : length (map (Z_to_bv 64) (gpf_vals regs0 ++ node_vals c0 c1 n leafv)) = 14%nat).
{ rewrite length_map, length_app. unfold node_vals. rewrite !length_app, Hlen. reflexivity. }
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. reflexivity.
Qed.
Lemma gp_EF : forall regs regs0 c0 c1 n leafv pal j v, nth_error (gpf_vals regs0) j = Some v ->
ew (Ereg regs (gp_extra regs0 c0 c1 n leafv pal)) (32 + j) = Z_to_bv 64 v.
Proof. intros regs regs0 c0 c1 n leafv pal j v Hj. unfold gp_extra. rewrite map_app, <- app_assoc. apply Ereg_vals. exact Hj. Qed.
Lemma gp_EN : forall regs regs0 c0 c1 n leafv pal j v, nth_error (node_vals c0 c1 n leafv) j = Some v ->
ew (Ereg regs (gp_extra regs0 c0 c1 n leafv pal)) (36 + j) = Z_to_bv 64 v.
Proof.
intros regs regs0 c0 c1 n leafv pal j v Hj. unfold gp_extra. change (36 + j)%nat with (32 + (4 + j))%nat. rewrite ew_Ereg_extra.
assert (Hl : (j < length (node_vals c0 c1 n leafv))%nat) by (apply nth_error_Some; congruence).
rewrite app_nth1 by (rewrite length_map, length_app; cbn [gpf_vals length]; lia).
rewrite map_app, app_nth2 by (rewrite length_map; cbn [gpf_vals length]; lia).
rewrite length_map. cbn [gpf_vals length]. replace (4 + j - 4)%nat with j by lia.
apply nth_error_nth. apply map_nth_error. exact Hj.
Qed.
Lemma gp_cidx_range : forall m a c0 c1 n leafv, length (tn_mean n) = 3%nat ->
obj_at trasegs m a LAY_Node (node_vals c0 c1 n leafv) -> 0 <= tn_cidx n < 256.
Proof.
intros m a c0 c1 n leafv Hlen Ond.
assert (Hnv8 : nth_error (node_vals c0 c1 n leafv) 8 = Some (tn_cidx n)).
{ unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity. }
destruct (obj_at_nth trasegs _ _ _ _ 8%nat (49, 1%N) (tn_cidx n) Ond eq_refl Hnv8) as [_ R]. cbn [snd Z.of_N] in R. change (2 ^ (8 * 1)) with 256 in R. exact R.
Qed.
Lemma gp_pal_range : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k pal cid pos,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
In (cid, pos) own -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
4096 <= pal /\ pal + 768 <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k pal cid pos HJ Hown Hpal1 Hpal2.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (fs_frame_bytes_nonneg cid) as HFB.
ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. clear - Hpal1 Hpal2 HFhi1 HFhi2 HFB C1 CR CR0. lia.
Qed.
Lemma gp_seed : forall (fy : FPState) (pin : bool) pc (regs0 regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k
(pal cid pos : Z) (d : nat) (n : tnode) (c0 c1 leafv : Z),
let sp := spZ regs0 in
let E := Ereg regs (gp_extra regs0 c0 c1 n leafv pal) in
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
sp mod 16 = 0 -> sp0 - STK <= sp - GP_STK (Z.of_nat d) -> sp <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF pal 768 ->
getr regs 2 = w64 (sp - 32) -> getr regs 8 = w64 pal -> getr regs 9 = w64 (tn_addr n) ->
(pin = true -> getr regs 10 = w64 (tn_addr n + 50)) ->
getr regs 18 = w64 SB ->
obj_at trasegs (mrestrict (w_H W) mem) (sp - 32) LAY_GPF (gpf_vals regs0) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trasegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
@st_ok trasegs fy E (ss_gp pin pc leafv) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 pc) mem (seg_rom trasegs)))
/\ sh_ok trasegs gp_Bx gp_SH E (mrestrict (w_H W) mem).
Proof.
intros fy pin pc regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 leafv sp E
HJ Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G10 G18 Ofr Hinn Ond Hlen.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 32 <= GP_STK (Z.of_nat d)) by (unfold GP_STK; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & _ & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as Hnh_img.
change (req_size NODE_SIZE) with 56 in *.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (sep_block_frame trasegs _ LAWS lyc Sc _ _ _ (tn_addr n) NODE_SIZE cid pos HAR Hinn Hfin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (req_size NODE_SIZE) with 56 in HdBF.
pose proof (obj_at_nth trasegs _ _ _ _ 8%nat (49, 1%N) (tn_cidx n) Ond eq_refl) as Fcidx.
assert (Hnv8 : nth_error (node_vals c0 c1 n leafv) 8 = Some (tn_cidx n)).
{ unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity. }
specialize (Fcidx Hnv8). destruct Fcidx as [_ Rcidx]. cbn [snd Z.of_N] in Rcidx. change (2 ^ (8 * 1)) with 256 in Rcidx.
rewrite restrict_mkst_fx.
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVF : forall j v, nth_error (gpf_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. unfold gp_extra. rewrite map_app, <- app_assoc. apply Ereg_vals. exact Hj. }
assert (HVN : forall j v, nth_error (node_vals c0 c1 n leafv) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. unfold gp_extra. change (36 + j)%nat with (32 + (4 + j))%nat. rewrite ew_Ereg_extra.
assert (Hl : (j < length (node_vals c0 c1 n leafv))%nat) by (apply nth_error_Some; congruence).
rewrite app_nth1 by (rewrite length_map, length_app; cbn [gpf_vals length]; lia).
rewrite map_app, app_nth2 by (rewrite length_map; cbn [gpf_vals length]; lia).
rewrite length_map. cbn [gpf_vals length]. replace (4 + j - 4)%nat with j by lia.
apply nth_error_nth. apply map_nth_error. exact Hj. }
assert (E46 : ew E 46 = Z_to_bv 64 (pal + 3 * tn_cidx n)).
{ subst E. unfold gp_extra. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra.
assert (HL : length (map (Z_to_bv 64) (gpf_vals regs0 ++ node_vals c0 c1 n leafv)) = 14%nat).
{ rewrite length_map, length_app. unfold node_vals. rewrite !length_app, Hlen. reflexivity. }
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. reflexivity. }
assert (E44 : ew E 44 = Z_to_bv 64 (tn_cidx n)) by (apply (HVN 8%nat); exact Hnv8).
assert (E2 : ew E 2 = getr regs 2) by (apply (HE 2%nat 2%bv); reflexivity).
assert (E8 : ew E 8 = w64 pal) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (E9 : ew E 9 = w64 (tn_addr n)) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (E18 : ew E 18 = w64 SB) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (Hspr : 0 <= sp - 32 < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 HGS Hstk0; lia).
assert (U2 : bv_unsigned (ew E 2) = sp - 32) by (rewrite E2, G2; apply unsigned_lit_small; exact Hspr).
assert (U9 : bv_unsigned (ew E 9) = tn_addr n) by (rewrite E9; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (U46 : bv_unsigned (ew E 46) = pal + 3 * tn_cidx n).
{ rewrite E46. apply unsigned_lit_small. clear - Hpal1 Hpal2 HFhi1 HFhi2 Rcidx HFB C1 CR CR0. lia. }
split.
- unfold ss_gp. apply (entry_st_ok_full trasegs).
+ destruct pin; [|apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |].
rewrite (G10 eq_refl). cbn [sv_denot]. fold E. rewrite U9. reflexivity.
+ destruct pin; vm_compute; reflexivity.
+ unfold gp_mem. repeat apply Forall_cons; try apply Forall_nil.
* eapply (region_ok_obj_gen trasegs _ _ 2 (sp - 32)); [exact U2 | lia | lia | exact Ofr | reflexivity | exact HVF | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
* eapply (region_ok_obj_gen trasegs _ _ 9 (tn_addr n)); [exact U9 | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U46.
split; [clear - Hpal1 HFhi1 Rcidx; lia|]. split; [clear - Hpal2 HFhi2 Rcidx HFB C1 CR CR0; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (HFpres (pal + 3 * tn_cidx n + o) ltac:(clear - Ho Hpal1 Hpal2 Rcidx; lia))).
+ apply pairwise_disjoint_of_extents. unfold gp_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U2, U9, U46. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
subst sp. revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 Hstk0 HGS Hpal1 Hpal2 HFhi1 HFhi2 HFhi2_img Hnceil Hn4096 HdBF Rcidx HFB. clear. ceil; unfold off_img, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [gp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U2, U9, U46, E18, E44, !unsigned_lit_small by (unfold SB; clear - Rcidx; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
subst sp. revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 C1 C3 Hstk0 HGS Hpal1 Hpal2 HFhi1 HFhi2 HFhi2_img Hnceil Hn4096 Hn16 Hnh Hnh_img Rcidx HFB. clear. unfold off_img.
ceil; unfold SB, zone2, in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat match goal with |- _ /\ _ => split end; try lia.
rewrite Zminus_mod, Hal16. reflexivity.
* cbn [gp_facts f_alias alias_ok gp_alias]. split; [|exact I].
fold E. apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
assert (Rpal : 0 <= pal /\ pal + 768 < 2 ^ 63) by (clear - Hpal1 Hpal2 HFhi1 HFhi2 HFB C1 CR CR0; lia).
rewrite (U_atom E 8 pal E8) by lia. rewrite (U_atom E 44 (tn_cidx n) E44) by lia. rewrite (U_lit E 3) by lia.
rewrite (U_atom E 46 (pal + 3 * tn_cidx n) E46) by lia.
rewrite (zcanon_id (tn_cidx n * 3)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
- unfold sh_ok, gp_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E gp_Bx 9 (tn_addr n) NODE_SIZE 0 NODE_SIZE HAR Hinn).
* unfold U, gp_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
* lia.
* change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
+ apply (shent_ok_of_range trasegs (w_H W) mem E gp_Bx 46 pal 768 (pal + 3 * tn_cidx n) 0 3 HRA).
* unfold U, gp_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U46.
* clear - Rcidx; lia.
* clear - Rcidx; lia.
* intros x Hx. clear - Hx Hpal1 Hpal2 HFhi1 HFhi2 HFhi2_img Rcidx HFB C1 CR CR0. unfold off_img, SHADOW_OFF in *. lia.
Qed.
Lemma gp_leaf : forall n, gp_R_stmt (TLeaf n).
Proof.
intros n fy regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d sp
HJ Hh Hfull Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G10 G18 Gkeep Ofr Hblk Hat.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
cbn [troot] in G9, G10. cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & c0 & c1 & Ond).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
destruct (gp_seed fy true GP_TEST regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 1
HJ Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 (fun _ => G10) G18 Ofr Hinn Ond Hlen) as [HS SHOK].
set (E := Ereg regs (gp_extra regs0 c0 c1 n 1 pal)) in *.
pose proof (st_ok_enterF trasegs fy 47 E _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF.
pose proof (sh_ok_agree trasegs gp_Bx gp_SH 47 E (ew_fregs E 47 (@fp_regs fy)) _ (env_agree_ew_fregs E 47 _) ltac:(vm_compute; reflexivity) SHOK) as SHOKF.
clear HS SHOK.
pose proof (gp_cidx_range _ _ c0 c1 n 1 Hlen Ond) as Rcidx.
pose proof (gp_E46 regs regs0 c0 c1 n 1 pal Hlen) as E46. fold E in E46.
aj_run_tokF tratbl_lib_ok HSF HJ SHOKF gp_Bspan.
{
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyx ?ownx =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fp b0 bc lyx ownx) end.
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | rewrite ew_fregs_low by lia; rewrite E46; apply unsigned_lit_small | | apply awr_ok_nil].
- destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2]. clear - Rp1 Rp2 Rcidx. lia.
- cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. right. right. right. exists cid, pos. split; [exact Hown|]. left.
unfold in_zr. cbn [fst snd]. clear - Ha Hpal1 Hpal2 Rcidx. lia. }
pose proof (st_okF_frm trasegs _ _ _ HSF) as Hfrm'.
pose proof (st_okF_to_legacy trasegs _ _ _ HSF) as HSL.
rreg HSL (1%bv : bv 5) R1.
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx W _ _ _ _ _ HSL eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gp_post. split; [reflexivity|].
assert (EF : forall j v, nth_error (gpf_vals regs0) j = Some v -> ew (ew_fregs E 47 (@fp_regs fy)) (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. assert (Hj4 : (j < 4)%nat) by (apply (proj1 (nth_error_Some (gpf_vals regs0) j)); congruence).
rewrite ew_fregs_low by lia. exact (gp_EF regs regs0 c0 c1 n 1 pal j v Hj). }
assert (ER : forall j (rr : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned rr -> ew (ew_fregs E 47 (@fp_regs fy)) j = getr regs rr).
{ intros j rr Hj Hrr. rewrite ew_fregs_low by lia. subst E. apply ew_Ereg_nat. exact Hrr. }
pose proof (EF 0%nat _ eq_refl) as E32. pose proof (EF 1%nat _ eq_refl) as E33. pose proof (EF 2%nat _ eq_refl) as E34. pose proof (EF 3%nat _ eq_refl) as E35.
cbn [Nat.add] in E32, E33, E34, E35.
rewrite R1, E35, Z_to_bv_bv_unsigned, Hra.
exists (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [exact Hfrm'|].
split; [cbn [ms_mem]; apply (ajournal_materialize trasegs B LAWS Hsegs); exact HJ|].
split; [|split].
-
assert (Hspr : 0 <= sp - 32 /\ sp < 2 ^ 64).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _). assert (32 <= GP_STK (Z.of_nat d)) by (unfold GP_STK; lia). subst sp. clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 H Hstk0. lia. }
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
repeat (destruct Hc as [-> | Hc]); [ | | | | | | | | | | | | | | subst r].
+ assert (X : getr (ms_regs ms) (2%bv : bv 5) = getr regs0 (2%bv : bv 5)); [|exact X]. rreg HSL (2%bv : bv 5) Rk. rewrite Rk, (ER 2%nat 2%bv ltac:(lia) eq_refl), G2.
unfold w64. rewrite unsigned_lit_small by lia. replace (sp - 32 + 32) with sp by lia. subst sp. unfold spZ. apply Z_to_bv_bv_unsigned.
+ assert (X : getr (ms_regs ms) (3%bv : bv 5) = getr regs0 (3%bv : bv 5)); [|exact X]. rreg HSL (3%bv : bv 5) Rk. rewrite Rk, (ER 3%nat 3%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (4%bv : bv 5) = getr regs0 (4%bv : bv 5)); [|exact X]. rreg HSL (4%bv : bv 5) Rk. rewrite Rk, (ER 4%nat 4%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (8%bv : bv 5) = getr regs0 (8%bv : bv 5)); [|exact X]. rreg HSL (8%bv : bv 5) Rk. rewrite Rk, E34. apply Z_to_bv_bv_unsigned.
+ assert (X : getr (ms_regs ms) (9%bv : bv 5) = getr regs0 (9%bv : bv 5)); [|exact X]. rreg HSL (9%bv : bv 5) Rk. rewrite Rk, E33. apply Z_to_bv_bv_unsigned.
+ assert (X : getr (ms_regs ms) (18%bv : bv 5) = getr regs0 (18%bv : bv 5)); [|exact X]. rreg HSL (18%bv : bv 5) Rk. rewrite Rk, E32. apply Z_to_bv_bv_unsigned.
+ assert (X : getr (ms_regs ms) (19%bv : bv 5) = getr regs0 (19%bv : bv 5)); [|exact X]. rreg HSL (19%bv : bv 5) Rk. rewrite Rk, (ER 19%nat 19%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (20%bv : bv 5) = getr regs0 (20%bv : bv 5)); [|exact X]. rreg HSL (20%bv : bv 5) Rk. rewrite Rk, (ER 20%nat 20%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (21%bv : bv 5) = getr regs0 (21%bv : bv 5)); [|exact X]. rreg HSL (21%bv : bv 5) Rk. rewrite Rk, (ER 21%nat 21%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (22%bv : bv 5) = getr regs0 (22%bv : bv 5)); [|exact X]. rreg HSL (22%bv : bv 5) Rk. rewrite Rk, (ER 22%nat 22%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (23%bv : bv 5) = getr regs0 (23%bv : bv 5)); [|exact X]. rreg HSL (23%bv : bv 5) Rk. rewrite Rk, (ER 23%nat 23%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (24%bv : bv 5) = getr regs0 (24%bv : bv 5)); [|exact X]. rreg HSL (24%bv : bv 5) Rk. rewrite Rk, (ER 24%nat 24%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (25%bv : bv 5) = getr regs0 (25%bv : bv 5)); [|exact X]. rreg HSL (25%bv : bv 5) Rk. rewrite Rk, (ER 25%nat 25%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (26%bv : bv 5) = getr regs0 (26%bv : bv 5)); [|exact X]. rreg HSL (26%bv : bv 5) Rk. rewrite Rk, (ER 26%nat 26%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
+ assert (X : getr (ms_regs ms) (27%bv : bv 5) = getr regs0 (27%bv : bv 5)); [|exact X]. rreg HSL (27%bv : bv 5) Rk. rewrite Rk, (ER 27%nat 27%bv ltac:(lia) eq_refl). apply Gkeep; [vm_compute; tauto | discriminate | discriminate | discriminate | discriminate].
-
intros a Ha Hnlo Hnpal. cbn [ms_mem]. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_gp gp_mem] in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; try (clear - Hr; lia).
rewrite ew_fregs_low in Hr by lia. rewrite E46 in Hr.
destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
rewrite unsigned_lit_small in Hr by (clear - Rp1 Rp2 Rcidx; lia). clear - Hr Hnpal Rcidx. lia.
- intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
Definition gpe_mem (leafv : Z) : smem :=
[ stack_region 32; got_region; bcell_region 35;
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 36 (gp_lits leafv)) ].
Definition gpe_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_gpe (leafv : Z) : sstate := mkSS A_get_palette sr_atoms (gpe_mem leafv) None gpe_facts.
Definition gpe_Bx : sv := SOff 35 0.
Definition gpe_SH : list shent := [ mkSHE 10 0 NODE_SIZE ].
Definition gpe_extra (c0 c1 : Z) (n : tnode) (leafv : Z) : list word := map (Z_to_bv 64) ([0; 0; 0; SB] ++ node_vals c0 c1 n leafv).
Lemma gp_seed_entry : forall (fy : FPState) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k
(d : nat) (n : tnode) (c0 c1 leafv : Z),
let E := Ereg regs (gpe_extra c0 c1 n leafv) in
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - GP_STK (Z.of_nat d) -> spZ regs <= sp0 ->
getr regs 10 = w64 (tn_addr n) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trasegs (mrestrict (w_H W) memc) (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
@st_ok trasegs fy E (ss_gpe leafv) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 A_get_palette) memc (seg_rom trasegs)))
/\ sh_ok trasegs gpe_Bx gpe_SH E (mrestrict (w_H W) memc).
Proof.
intros fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k d n c0 c1 leafv E HJ Hal16 Hwlo Hwhi G10 Hinn Ond Hlen.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 32 <= GP_STK (Z.of_nat d)) by (unfold GP_STK; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & _ & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as Hnh_img.
change (req_size NODE_SIZE) with 56 in *.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
assert (HVN : forall j v, nth_error (node_vals c0 c1 n leafv) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. unfold gpe_extra. change (36 + j)%nat with (32 + (4 + j))%nat. rewrite ew_Ereg_extra.
rewrite map_app, app_nth2 by (cbn [map length]; lia). cbn [map length]. replace (4 + j - 4)%nat with j by lia.
apply nth_error_nth. apply map_nth_error. exact Hj. }
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 (tn_addr n)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = tn_addr n) by (rewrite E10; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
split.
- unfold ss_gpe. apply (entry_st_ok_full trasegs).
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold gpe_mem, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite Usp.
split; [clear - Hwlo Hwhi Hslo Hceil C1 HGS Hstk0; lia|]. split; [clear - Hwhi Hshi H47; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. clear - Ho Hwlo Hwhi HGS. lia.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs _ _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) memc _ _ Kgot).
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs _ _ 0 696760 8 gpe_Bx SB);
[cbn [sv_denot gpe_Bx]; fold E; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) memc _ _ Kcell).
* eapply (region_ok_obj_gen trasegs _ _ 10 (tn_addr n)); [exact U10 | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
+ apply pairwise_disjoint_of_extents. unfold gpe_mem, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite Usp, U10. unfold A_GOT_shadow, A_shadow_glob, NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 Hstk0 HGS Hnceil Hn4096 Hnh Hnh_img. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gpe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite Usp, U10, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 C1 C3 Hstk0 HGS Hnceil Hn4096 Hn16 Hnh Hnh_img. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gpe_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W memc mdc E gpe_Bx 10 (tn_addr n) NODE_SIZE 0 NODE_SIZE HAR Hinn).
* unfold U, gpe_Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
* lia.
* change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
Qed.
Lemma gp_root : forall m t, tree_full t -> tree_at trasegs m t ->
exists n c0 c1 leafv, troot t = tn_addr n /\ In (tn_addr n, NODE_SIZE) (tree_blocks t) /\ length (tn_mean n) = 3%nat /\
obj_at trasegs m (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) /\ (leafv = 0 \/ leafv = 1).
Proof.
intros m t Hf Hat. destruct t as [|n|n l r]; [destruct Hf | |]; cbn [tree_at troot tree_blocks] in *.
- destruct Hat as (_ & Hlen & c0 & c1 & Ho). exists n, c0, c1, 1. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. right. reflexivity.
- destruct Hat as (_ & Hlen & Ho & _ & _). exists n, (troot l), (troot r), 0. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. left. reflexivity.
Qed.
Local Ltac gp_keep1 HS ER msA regs r j :=
let X := fresh "X" in let Rk := fresh "Rk" in
assert (X : getr (ms_regs msA) (r : bv 5) = getr regs (r : bv 5));
[ rreg HS (r : bv 5) Rk; rewrite Rk; exact (ER j r eq_refl) | exact X ].
Local Ltac gp_keep_auto HS ER msA regs :=
lazymatch goal with |- getr (ms_regs msA) ?r = getr regs ?r =>
let j := eval vm_compute in (Z.to_nat (bv_unsigned r)) in gp_keep1 HS ER msA regs r j end.
Lemma gp_P_of_R : forall t, gp_R_stmt t -> gp_P_stmt t.
Proof.
intros t HR fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d
HJ Hh Hfull Hra Hra4 G10 G11 Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA Hblk Hat.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct (gp_root _ t Hfull Hat) as (n & c0 & c1 & leafv & Hroot & Hinb & Hlen & Ond & Hlv).
rewrite Hroot in G10.
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; exact Hinb).
destruct (gp_seed_entry fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k d n c0 c1 leafv HJ Hal16 Hwlo Hwhi G10 Hinn Ond Hlen) as [HS SHOK].
set (E := Ereg regs (gpe_extra c0 c1 n leafv)) in *.
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%nat 2%bv eq_refl); reflexivity).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 32 <= GP_STK (Z.of_nat d)) by (unfold GP_STK; lia).
destruct Hlv as [-> | ->].
all: aj_run_to_tok tratbl_lib_ok HS HJ SHOK gp_Bspan GP_TEST.
1, 3: (cbn [ss_mem ss_gpe gpe_mem]; eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite Usp; clear; lia | cbn; clear - Hwlo HGS; lia | cbn; clear - Hwhi; lia | awr_ok_tac]).
all: lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
all: rename HFr into HFr1; clear HF.
all: rreg HS (2%bv : bv 5) R2; rreg HS (8%bv : bv 5) R8; rreg HS (9%bv : bv 5) R9; rreg HS (10%bv : bv 5) R10; rreg HS (18%bv : bv 5) R18.
all: destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
all: destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & _); change (req_size NODE_SIZE) with 56 in Hnceil.
all: assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) memc a);
[ intros a Ha Hnw; apply aview_eq_of; apply HFr1; rewrite unsigned_lit_small by lia;
intros (rr & Hin & Hr); cbn [ss_mem ss_gpe gpe_mem] in Hin; unfold stack_region, got_region, bcell_region in Hin; cbn [In] in Hin;
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; unfold stack_region, got_region, bcell_region in Hr;
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; try rewrite Usp in Hr; clear - Hr Hnw; lia | ].
all: assert (Ofr : obj_at trasegs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 32) LAY_GPF (gpf_vals regs));
[ lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let rs := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx _ 0%nat rs HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ?ew_ewset_other by (cbv; lia); exact Usp);
assert (SL : forall od (rr : bv 5) j, Z.of_nat j = bv_unsigned rr -> (j < 32)%nat ->
In (YQ0b.mkChunk od (CVal 8 (SOff j 0))) (YQ0b.r_chunks rs) ->
val_mem trasegs (mrestrict (w_H W) (ms_mem msA)) (spZ regs + od) 8 (bv_unsigned (getr regs rr)));
[ intros od rr j Hj Hj32 Hin;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (slot_of_region Ex _ (spZ regs) cs lo hi wlo whi od (SOff j 0) _ HRstk UspX Hin);
[ cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite (ER j rr Hj), Z.add_0_r; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs rr)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq ] end
| ] end;
cbn [obj_at LAY_GPF gpf_vals]; unfold field_ok; cbn [fst snd N.to_nat Z.of_N Pos.to_nat];
repeat split; try apply u64_range8;
[ replace (spZ regs - 32 + 0) with (spZ regs + -32) by lia; apply (SL (-32) 18%bv 18%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 32 + 8) with (spZ regs + -24) by lia; apply (SL (-24) 9%bv 9%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 32 + 16) with (spZ regs + -16) by lia; apply (SL (-16) 8%bv 8%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 32 + 24) with (spZ regs + -8) by lia; apply (SL (-8) 1%bv 1%nat eq_refl ltac:(lia)); cbn; tauto ]
| ].
all: assert (Hat1 : tree_at trasegs (mrestrict (w_H W) (ms_mem msA)) t);
[ apply (rg_tree_at_kept (w_H W) (w_H W) memc (ms_mem msA) t Hat); intros b sz Hb i Hi;
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Hblk _ Hb)) as (_ & Hb4096 & Hbceil & _);
apply KEEP; [clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Hwlo Hwhi Hslo Hceil HGS Hstk0; lia] | ].
all: assert (HRA1 : range_addressable (aview trasegs (w_H W) (ms_mem msA)) SHADOW_OFF pal 768);
[ eapply range_addressable_agree; [|exact HRA]; intros x Hx;
assert (Hx8 : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]);
apply KEEP; unfold shadow_of_addr, SHADOW_OFF;
[ clear - Hx8; lia | clear - Hx8 Hwlo Hwhi Hslo Hceil HGS Hstk0 C1; lia ] | ].
all: rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ msA HS eq_refl); cbn [ss_pc].
all: eapply SRr_mono;
[ eapply (HR fy regs (ms_regs msA) (ms_mem msA) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d
HJ Hh Hfull Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA1);
[ rewrite R2, Usp; unfold w64; f_equal; lia
| rewrite R8, (ER 11%nat 11%bv eq_refl); exact G11
| rewrite R9, (ER 10%nat 10%bv eq_refl), Hroot; exact G10
| rewrite R10, (ER 10%nat 10%bv eq_refl), G10, Hroot; unfold w64; rewrite unsigned_lit_small by (clear - Hn4096 Hnceil C1; lia); reflexivity
| rewrite R18; exact E35
| intros r Hin N2 N8 N9 N18; unfold CALLEE_SAVED in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; try congruence;
[ gp_keep1 HS ER msA regs (3%bv : bv 5) 3%nat | gp_keep1 HS ER msA regs (4%bv : bv 5) 4%nat
| gp_keep1 HS ER msA regs (19%bv : bv 5) 19%nat | gp_keep1 HS ER msA regs (20%bv : bv 5) 20%nat | gp_keep1 HS ER msA regs (21%bv : bv 5) 21%nat
| gp_keep1 HS ER msA regs (22%bv : bv 5) 22%nat | gp_keep1 HS ER msA regs (23%bv : bv 5) 23%nat | gp_keep1 HS ER msA regs (24%bv : bv 5) 24%nat
| gp_keep1 HS ER msA regs (25%bv : bv 5) 25%nat | gp_keep1 HS ER msA regs (26%bv : bv 5) 26%nat | gp_keep1 HS ER msA regs (27%bv : bv 5) 27%nat ]
| exact Ofr | exact Hblk | exact Hat1 ]
| intros W' c' _ (HW & fx' & regs2 & mem2 & md2 & Hc & Hfz & HJ2 & Hpr & Hkeep2 & Hpres2);
split; [exact HW|]; exists fx', regs2, mem2, md2;
split; [exact Hc|]; split; [exact Hfz|]; split; [exact HJ2|]; split; [exact Hpr|]; split;
[ intros a Ha Hnw Hnpal; rewrite (Hkeep2 a Ha ltac:(clear - Hnw; lia) Hnpal); apply KEEP; [exact Ha | clear - Hnw HGS; lia]
| intros a Ha; apply Hpres2; exact (apresent_grows _ _ _ _ HG Ha) ] ].
Qed.
Lemma gp_kept : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memJ mdJ k (pal cid pos sp lo hi : Z) (mem m' : word -> option byte),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memJ mdJ k ->
In (cid, pos) own -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
sp0 - STK <= lo -> lo <= hi -> hi <= sp - 32 -> sp <= sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (pal <= a < pal + 768) ->
aview trasegs (w_H W) m' a = aview trasegs (w_H W) mem a) ->
(forall b sz, In (b, sz) (ablocks B lyc Sc) -> rg_blk_kept (w_H W) (w_H W) mem m' b (req_size sz)) /\
rg_blk_kept (w_H W) (w_H W) mem m' (sp - 32) 32 /\
(range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF pal 768 ->
range_addressable (aview trasegs (w_H W) m') SHADOW_OFF pal 768).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memJ mdJ k pal cid pos sp lo hi mem m' HJ Hown Hpal1 Hpal2 Hlo Hlh Hhi Hsp KEEP.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2.
pose proof (fs_frame_bytes_nonneg cid) as HFB.
split; [|split].
- intros b sz Hb i Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR Hb) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_block_frame trasegs _ LAWS lyc Sc _ _ _ b sz cid pos HAR Hb Hfin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
apply KEEP; [clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Hceil Hslo Hlo; lia | clear - Hi Hd Hpal1 Hpal2; lia].
- intros i Hi. apply KEEP; [clear - Hi Hlo Hlh Hhi Hsp Hslo Hshi H47 Hceil C1 Hstk0; lia | clear - Hi Hhi; lia |].
clear - Hi Hlo Hlh Hhi Hsp Hslo Hshi H47 Hceil C1 Hstk0 Hpal1 Hpal2 HFhi1 HFhi2 HFB CR CR0. lia.
- intros HRA. eapply range_addressable_agree; [|exact HRA]. intros x Hx.
assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply KEEP; unfold shadow_of_addr, SHADOW_OFF.
+ clear - Hx8; lia.
+ clear - Hx8 Hlo Hslo Hceil Hstk0 C1; lia.
+ clear - Hx Hx8 Hpal1 Hpal2 HFhi1 HFhi2 HFB C1 CR CR0. lia.
Qed.
Lemma gp_pres_in : forall regs regs' : bvmap 5 word, aregs_preserved regs regs' ->
forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs r.
Proof.
intros regs regs' Hp r Hin. unfold CALLEE_SAVED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); [ | | | | | | | | | | | | | | | destruct Hin].
- exact (Hp 2 ltac:(unfold acallee_saved; lia)).
- exact (Hp 3 ltac:(unfold acallee_saved; lia)).
- exact (Hp 4 ltac:(unfold acallee_saved; lia)).
- exact (Hp 8 ltac:(unfold acallee_saved; lia)).
- exact (Hp 9 ltac:(unfold acallee_saved; lia)).
- exact (Hp 18 ltac:(unfold acallee_saved; lia)).
- exact (Hp 19 ltac:(unfold acallee_saved; lia)).
- exact (Hp 20 ltac:(unfold acallee_saved; lia)).
- exact (Hp 21 ltac:(unfold acallee_saved; lia)).
- exact (Hp 22 ltac:(unfold acallee_saved; lia)).
- exact (Hp 23 ltac:(unfold acallee_saved; lia)).
- exact (Hp 24 ltac:(unfold acallee_saved; lia)).
- exact (Hp 25 ltac:(unfold acallee_saved; lia)).
- exact (Hp 26 ltac:(unfold acallee_saved; lia)).
- exact (Hp 27 ltac:(unfold acallee_saved; lia)).
Qed.
Definition gpn_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 36 (gp_lits 0)) ].
Lemma gpn_submem : submem gpn_mem (gp_mem 0).
Proof.
unfold gpn_mem, gp_mem. apply submem_drop. apply submem_keep; [|apply submem_nil].
split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [left; cbn; lia|]. intros c Hc; exact Hc.
Qed.
Lemma gp_node : forall n l r, gp_P_stmt l -> gp_R_stmt r -> gp_R_stmt (TNode n l r).
Proof.
intros n l r HPl HRr fy regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d sp
HJ Hh Hfull Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G10 G18 Gkeep Ofr Hblk Hat.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
cbn [troot] in G9, G10. cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & Ond & Hatl & Hatr).
cbn [tree_full] in Hfull. destruct Hfull as [Hfl Hfr].
destruct d as [|d']; [cbn [tree_height] in Hh; lia|]. cbn [tree_height] in Hh.
assert (Hhl : (tree_height l <= d')%nat) by lia. assert (Hhr : (tree_height r <= Datatypes.S d')%nat) by lia.
assert (HGS : GP_STK (Z.of_nat (Datatypes.S d')) = GP_STK (Z.of_nat d') + 32) by (unfold GP_STK; lia).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
assert (Hblkl : forall b, In b (tree_blocks l) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; left; exact Hb).
assert (Hblkr : forall b, In b (tree_blocks r) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; right; exact Hb).
destruct (gp_seed fy true GP_TEST regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos (Datatypes.S d') n (troot l) (troot r) 0
HJ Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 (fun _ => G10) G18 Ofr Hinn Ond Hlen) as [HS0 SHOK].
set (E := Ereg regs (gp_extra regs0 (troot l) (troot r) n 0 pal)) in *.
pose proof (st_ok_submem trasegs _ _ _ gpn_mem HS0 gpn_submem ltac:(vm_compute; reflexivity)) as HS.
cbn [ss_pc ss_regs ss_resv ss_facts ss_gp] in HS. clear HS0.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK gp_Bspan A_get_palette.
{ cbn [ss_mem]. unfold gpn_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msB := msx) in * end.
rename HFr into HFr1; rename HG into HG1; clear HF.
rreg HS (1%bv : bv 5) R1; rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (11%bv : bv 5) R11.
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (gp_EN regs regs0 (troot l) (troot r) n 0 pal 0%nat (troot l) eq_refl) as E36.
pose proof (gp_EN regs regs0 (troot l) (troot r) n 0 pal 1%nat (troot r) eq_refl) as E37.
cbn [Nat.add] in E36, E37. fold E in E36, E37.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS0 : 32 <= GP_STK (Z.of_nat d')) by (unfold GP_STK; lia).
assert (Hspr : 0 <= sp - 32 /\ sp < 2 ^ 64) by (clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 HGS HGS0 Hstk0; lia).
assert (UspB : spZ (ms_regs msB) = sp - 32).
{ unfold spZ. rewrite R2, (ER 2%nat 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. clear - Hspr. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msB) a = aview trasegs (w_H W) mem a).
{ intros a Ha. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem gpn_mem In] in Hin. destruct Hin as [<- | []].
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - 32) (sp - 32) mem (ms_mem msB)
HJ Hown Hpal1 Hpal2 ltac:(clear - Hwlo HGS HGS0; lia) ltac:(clear; lia) ltac:(clear; lia) Hwhi
ltac:(intros a Ha _ _; exact (KEEP1 a Ha))) as (KB1 & KB2 & KB3).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ msB HS eq_refl); cbn [ss_pc].
eapply SRr_bind.
{ eapply (HPl fy (ms_regs msB) (ms_mem msB) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d' HJ Hhl Hfl).
- rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
- unfold raZ. rewrite R1. rewrite unsigned_lit_small by (clear; lia). clear; lia.
- rewrite R10, E36. reflexivity.
- rewrite R11, (ER 8%nat 8%bv eq_refl). exact G8.
- rewrite UspB. clear - Hal16. rewrite Zminus_mod, Hal16. reflexivity.
- rewrite UspB. clear - Hwlo HGS. lia.
- rewrite UspB. clear - Hwhi. lia.
- exact Hfrm.
- exact Hown.
- exact Hcid.
- exact Hpal1.
- exact Hpal2.
- exact (KB3 HRA).
- exact Hblkl.
- apply (rg_tree_at_kept (w_H W) (w_H W) mem (ms_mem msB) l Hatl). intros b sz Hb. apply KB1. exact (Hblkl _ Hb). }
cbv beta. intros W' c' _ (HW & fx' & regs2 & mem2 & md2 & Hc & Hfz & HJ2 & Hpr & Hkeep2 & Hpres2). subst W' c'.
rewrite R1. rewrite UspB in Hkeep2.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GP_STK (Z.of_nat (Datatypes.S d')) <= a < sp - 32) -> ~ (pal <= a < pal + 768) ->
aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha Hnw Hnp. rewrite (Hkeep2 a Ha ltac:(clear - Hnw HGS; lia) Hnp). exact (KEEP1 a Ha). }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GP_STK (Z.of_nat (Datatypes.S d'))) (sp - 32) mem mem2
HJ2 Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS HGS0; lia) ltac:(clear; lia) Hwhi KEEP2) as (KC1 & KC2 & KC3).
pose proof (gp_pres_in _ _ Hpr) as PR.
rreg HS (8%bv : bv 5) R8; rreg HS (9%bv : bv 5) R9; rreg HS (18%bv : bv 5) R18.
assert (G2c : getr regs2 2 = w64 (sp - 32)).
{ rewrite (PR (2%bv : bv 5) (or_introl eq_refl)), R2, (ER 2%nat 2%bv eq_refl). exact G2. }
assert (G8c : getr regs2 8 = w64 pal) by (rewrite (PR (8%bv : bv 5) (or_intror (or_intror (or_intror (or_introl eq_refl))))), R8, (ER 8%nat 8%bv eq_refl); exact G8).
assert (G9c : getr regs2 9 = w64 (tn_addr n)) by (rewrite (PR (9%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))), R9, (ER 9%nat 9%bv eq_refl); exact G9).
assert (G18c : getr regs2 18 = w64 SB) by (rewrite (PR (18%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))), R18, (ER 18%nat 18%bv eq_refl); exact G18).
assert (Ofr2 : obj_at trasegs (mrestrict (w_H W) mem2) (sp - 32) LAY_GPF (gpf_vals regs0))
by (apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 (sp - 32) LAY_GPF _ 32 Ofr ltac:(vm_compute; reflexivity) KC2)).
assert (Ond2 : obj_at trasegs (mrestrict (w_H W) mem2) (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0))
by (apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)); exact (KC1 _ _ Hinn)).
assert (Hatr2 : tree_at trasegs (mrestrict (w_H W) mem2) r)
by (apply (rg_tree_at_kept (w_H W) (w_H W) mem mem2 r Hatr); intros b sz Hb; apply KC1; exact (Hblkr _ Hb)).
destruct (gp_seed fx' false GP_RET1 regs0 regs2 mem2 md2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos (Datatypes.S d') n (troot l) (troot r) 0
HJ2 Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 (KC3 HRA) G2c G8c G9c ltac:(intros HH0; discriminate HH0) G18c Ofr2 Hinn Ond2 Hlen) as [HSc0 SHOKc].
set (Ec := Ereg regs2 (gp_extra regs0 (troot l) (troot r) n 0 pal)) in *.
pose proof (st_ok_submem trasegs _ _ _ gpn_mem HSc0 gpn_submem ltac:(vm_compute; reflexivity)) as HSc1.
cbn [ss_pc ss_regs ss_resv ss_facts ss_gp] in HSc1. clear HSc0.
destruct (gp_root _ r Hfr Hatr2) as (nr & cr0 & cr1 & lvr & Hrootr & Hinbr & Hlenr & Ondr & Hlvr).
assert (Hinnr : In (tn_addr nr, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblkr; exact Hinbr).
pose proof (proj1 HJ2) as HAR2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr nr) NODE_SIZE HAR2 Hinnr) as (Hr16 & Hr4096 & Hrceil & _). change (req_size NODE_SIZE) with 56 in Hrceil.
pose proof (gp_EN regs2 regs0 (troot l) (troot r) n 0 pal 1%nat (troot r) eq_refl) as E37c. cbn [Nat.add] in E37c. fold Ec in E37c. rewrite Hrootr in E37c.
assert (U37 : bv_unsigned (ew Ec 37) = tn_addr nr) by (rewrite E37c; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia).
assert (E18c : ew Ec 18 = w64 SB) by (subst Ec; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact G18c).
pose proof (st_ok_add_fact trasegs Ec _ _ 37%nat (mkAF 4096 140737479966720 4) HSc1
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U37; change (2 ^ 4) with 16; clear - Hr16 Hr4096 Hrceil C1; lia)) as HSc.
clear HSc1.
assert (SHOKc' : sh_ok trasegs gp_Bx (mkSHE 37 0 NODE_SIZE :: gp_SH) Ec (mrestrict (w_H W) mem2)).
{ constructor; [|exact SHOKc].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem2 md2 Ec gp_Bx 37 (tn_addr nr) NODE_SIZE 0 NODE_SIZE HAR2 Hinnr).
- unfold U, gp_Bx. cbn [sv_denot]. rewrite E18c, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U37.
- lia.
- change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia. }
assert (KBreg : forall rr : bv 5, In rr CALLEE_SAVED -> getr (ms_regs msB) rr = getr regs rr).
{ intros rr Hin. unfold CALLEE_SAVED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); try contradiction; gp_keep_auto HS ER msB regs. }
clear SHOKc HS HFr1.
aj_run_to_tok tratbl_lib_ok HSc HJ2 SHOKc' gp_Bspan GP_TEST.
{ cbn [ss_mem add_atom]. unfold gpn_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msD := msx) in * end.
rename HFr into HFr3; clear HF.
rreg HSc (2%bv : bv 5) Q2; rreg HSc (8%bv : bv 5) Q8; rreg HSc (9%bv : bv 5) Q9; rreg HSc (10%bv : bv 5) Q10; rreg HSc (18%bv : bv 5) Q18.
assert (ERc : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew Ec j = getr regs2 rr) by (intros; subst Ec; apply ew_Ereg_nat; assumption).
assert (KDreg : forall rr : bv 5, In rr CALLEE_SAVED -> rr <> 9%bv -> getr (ms_regs msD) rr = getr regs2 rr).
{ intros rr Hin N9. unfold CALLEE_SAVED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); try contradiction; try (exfalso; apply N9; reflexivity);
gp_keep_auto HSc ERc msD regs2. }
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msD) a = aview trasegs (w_H W) mem2 a).
{ intros a Ha. apply aview_eq_of. apply HFr3. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem add_atom gpn_mem In] in Hin. destruct Hin as [<- | []].
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
assert (KEEPd : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GP_STK (Z.of_nat (Datatypes.S d')) <= a < sp - 32) -> ~ (pal <= a < pal + 768) ->
aview trasegs (w_H W) (ms_mem msD) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hnw Hnp. rewrite (KEEP3 a Ha). exact (KEEP2 a Ha Hnw Hnp). }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GP_STK (Z.of_nat (Datatypes.S d'))) (sp - 32) mem (ms_mem msD)
HJ2 Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS HGS0; lia) ltac:(clear; lia) Hwhi KEEPd) as (KD1 & KD2 & KD3).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ msD HSc eq_refl); cbn [ss_pc].
eapply SRr_mono.
{ eapply (HRr fx' regs0 (ms_regs msD) (ms_mem msD) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos (Datatypes.S d')
HJ2 Hhr Hfr Hra Hal16 Hwlo Hwhi Hfz Hown Hcid Hpal1 Hpal2 (KD3 HRA)).
- rewrite Q2, (ERc 2%nat 2%bv eq_refl). exact G2c.
- rewrite Q8, (ERc 8%nat 8%bv eq_refl). exact G8c.
- rewrite Q9, E37c, Hrootr. reflexivity.
- rewrite Q10, U37, Hrootr. reflexivity.
- rewrite Q18. exact E18c.
- intros rr Hin N2 N8 N9 N18. rewrite (KDreg rr Hin N9), (PR rr Hin), (KBreg rr Hin). exact (Gkeep rr Hin N2 N8 N9 N18).
- exact (rg_obj_at_blk_kept (w_H W) (w_H W) mem (ms_mem msD) (sp - 32) LAY_GPF _ 32 Ofr ltac:(vm_compute; reflexivity) KD2).
- exact Hblkr.
- apply (rg_tree_at_kept (w_H W) (w_H W) mem (ms_mem msD) r Hatr). intros b sz Hb. apply KD1. exact (Hblkr _ Hb). }
intros W' c' _ (HW & fx2 & regs3 & mem3 & md3 & Hc & Hfz3 & HJ3 & Hpr3 & Hkeep3 & Hpres3).
split; [exact HW|]. exists fx2, regs3, mem3, md3.
split; [exact Hc|]. split; [exact Hfz3|]. split; [exact HJ3|]. split; [exact Hpr3|]. split.
- intros a Ha Hnw Hnp. rewrite (Hkeep3 a Ha Hnw Hnp). exact (KEEPd a Ha Hnw Hnp).
- intros a Ha. apply Hpres3. apply (apresent_grows _ _ _ _ HG). apply Hpres2. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma gp_R_all : forall u, gp_R_stmt u.
Proof.
induction u as [|n|n l IHl r IHr].
- intros fy regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d sp HJ Hh Hfull. destruct Hfull.
- apply gp_leaf.
- apply gp_node; [apply gp_P_of_R; exact IHl | exact IHr].
Qed.
Theorem tra_get_palette : forall {fx : FPState}, tgetpal_spec B.
Proof.
intros fx d STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t pal cid pos
HJ Hh Hfull Hra Hra4 G10 G11 Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA Hblk Hat.
exact (gp_P_of_R t (gp_R_all t) fx regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d
HJ Hh Hfull Hra Hra4 G10 G11 Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA Hblk Hat).
Qed.
End GP.
