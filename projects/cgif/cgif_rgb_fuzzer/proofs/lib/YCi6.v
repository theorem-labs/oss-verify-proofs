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
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0a YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCi1 YCib
YCia YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCip YCi7 YCio.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition GP_TEST : Z := 0x858d0.
Definition GP_RET1 : Z := 0x858f8.
Definition GP_L1 : Z := 0x85948.
Definition GP_L2 : Z := 0x859d0.
Definition GP_L3 : Z := 0x85a3c.
Definition LAY_GPF : layout_t := [(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 8%N); (48, 8%N); (56, 8%N); (64, 8%N); (72, 8%N)].
Definition gpf_vals (regs0 f0 : bvmap 5 word) : list Z :=
[bv_unsigned (reg_get f0 9); bv_unsigned (reg_get f0 8); bv_unsigned (getr regs0 22); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 20);
bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1)].
Definition GP_UNTOUCHED : list (bv 5) := [3; 4; 23; 24; 25; 26; 27]%bv.
Definition GPR_LO : Z := 0x10300.
Definition GPR_HI : Z := 0x10348.
Section GP.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis FPC : trb_fp_consts B.
Hypothesis TROUND : forall fx : FPState, @tround_spec fx rc B.
Definition gp_post (regs0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem0 md0 own lyc Sc (W : world trbsegs)
(mem : word -> option byte) (k lo hi pal : Z) : world trbsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists (fx' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs0 1) mem2 (seg_rom trbsegs)) md2 /\ frm_zero (@fp_csr fx') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs0 regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a).
Definition gp_R_stmt (u : tree) : Prop :=
forall (fy : FPState) (regs0 f0 regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (pal cid pos : Z) (d : nat),
let sp := spZ regs0 in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(tree_height u <= d)%nat -> tree_full u -> tree_forall tnode_wf u -> tree_forall tnode_means_ok u ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - GPB_STK (Z.of_nat d) -> sp <= sp0 ->
frm_zero (@fp_csr fy) ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF pal 768 ->
getr regs 2 = w64 (sp - 80) -> getr regs 8 = w64 pal -> getr regs 9 = w64 (troot u) -> getr regs 10 = w64 (troot u + 50) ->
getr regs 18 = w64 2 -> getr regs 20 = w64 SB ->
(forall r : bv 5, In r GP_UNTOUCHED -> getr regs r = getr regs0 r) ->
obj_at trbsegs (mrestrict (w_H W) mem) (sp - 80) LAY_GPF (gpf_vals regs0 f0) ->
(forall b, In b (tree_blocks u) -> In b (ablocks B lyc Sc)) ->
tree_at trbsegs (mrestrict (w_H W) mem) u ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 GP_TEST) mem (seg_rom trbsegs)) md)
(gp_post regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k (sp - GPB_STK (Z.of_nat d)) (sp - 80) pal).
Definition gp_P_stmt (t : tree) : Prop :=
forall (fy : FPState) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (pal cid pos : Z) (d : nat),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(tree_height t <= d)%nat -> tree_full t -> tree_forall tnode_wf t -> tree_forall tnode_means_ok t ->
arodata_ok B (aview trbsegs (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 (troot t) -> getr regs 11 = w64 pal ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - GPB_STK (Z.of_nat d) -> spZ regs <= sp0 ->
frm_zero (@fp_csr fy) ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trbsegs (w_H W) memc) SHADOW_OFF pal 768 ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
tree_at trbsegs (mrestrict (w_H W) memc) t ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 A_get_palette) memc (seg_rom trbsegs)) mdc)
(gp_post regs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k (spZ regs - GPB_STK (Z.of_nat d)) (spZ regs) pal).
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Definition gp_lits (leafv : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some leafv].
Definition gp_3cidx : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 50 0) (SLit 1)) (SOff 50 0).
Definition gp_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 8 0) gp_3cidx, SOff 52 0); (SAlu ALU_XOR (SOff 8 0) (SLit (-1)), SOff 53 0) ].
Definition gp_rodata : YQ0b.region := YQ0b.mkRegion None GPR_LO GPR_HI 0 0 [YQ0b.mkChunk 0x10300 (CImg 8); YQ0b.mkChunk 0x10340 (CImg 8)].
Definition gp_mem (leafv : Z) : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 80 0 0 (obj_chunks_from LAY_GPF 32);
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 42 (gp_lits leafv));
YQ0b.mkRegion (Some 52%nat) 0 3 0 3 [];
gp_rodata ].
Definition gp_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 4096 140737479966720 4); (20%nat, mkAF SB SB 0);
(50%nat, mkAF 0 255 0); (52%nat, mkAF 4096 140737479966720 0); (53%nat, mkAF 18446603336221196287 18446744073709547519 0) ] [] gp_alias.
Definition gp_sh6 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 49) (SLit 3)) (SOff 20 0).
Definition gp_regs (g : nat) : list sv :=
match g with
| 0%nat => sr_set (sr_set sr_atoms 10%bv (SOff 9 50)) 18%bv (SLit 2)
| 1%nat => sr_set sr_atoms 19%bv (SOff 9 16)
| 2%nat | 3%nat => sr_set (sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 9 16)) 18%bv (SOff 9 49)) 21%bv (SOff 53 0)) 22%bv gp_sh6
| _ => sr_set sr_atoms 18%bv (SLit 2)
end.
Definition gp_pc (g : nat) : Z := match g with 0%nat => GP_TEST | 1%nat => GP_L1 | 2%nat => GP_L2 | 3%nat => GP_L3 | _ => GP_RET1 end.
Definition gp_pin_facts (g : nat) (regs : bvmap 5 word) (node pal : Z) : Prop :=
match g with
| 0%nat => getr regs 10 = w64 (node + 50) /\ getr regs 18 = w64 2
| 1%nat => getr regs 19 = w64 (node + 16)
| 2%nat | 3%nat => getr regs 19 = w64 (node + 16) /\ getr regs 18 = w64 (node + 49) /\ getr regs 21 = w64 (2 ^ 64 - 1 - pal) /\
getr regs 22 = w64 (SB + (node + 49) / 8)
| _ => getr regs 18 = w64 2
end.
Definition ss_gp (g : nat) (leafv : Z) : sstate := mkSS (gp_pc g) (gp_regs g) (gp_mem leafv) None gp_facts.
Definition gp_Bx : sv := SOff 20 0.
Definition gp_SH : list shent := [ mkSHE 9 0 NODE_SIZE; mkSHE 52 0 3 ].
Definition gp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gp_extra (regs0 f0 : bvmap 5 word) (c0 c1 : Z) (n : tnode) (leafv pal : Z) : list word :=
map (Z_to_bv 64) (gpf_vals regs0 f0 ++ node_vals c0 c1 n leafv) ++ [Z_to_bv 64 (pal + 3 * tn_cidx n); Z_to_bv 64 (2 ^ 64 - 1 - pal)].
Lemma u64_range8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma gp_len20 : forall regs0 f0 c0 c1 n leafv, length (tn_mean n) = 3%nat ->
length (map (Z_to_bv 64) (gpf_vals regs0 f0 ++ node_vals c0 c1 n leafv)) = 20%nat.
Proof. intros regs0 f0 c0 c1 n leafv Hlen. rewrite length_map, length_app. unfold node_vals. rewrite !length_app, Hlen. reflexivity. Qed.
Lemma gp_E52 : forall regs regs0 f0 c0 c1 n leafv pal, length (tn_mean n) = 3%nat ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) 52 = Z_to_bv 64 (pal + 3 * tn_cidx n).
Proof.
intros regs regs0 f0 c0 c1 n leafv pal Hlen. unfold gp_extra. change 52%nat with (32 + 20)%nat. rewrite ew_Ereg_extra.
pose proof (gp_len20 regs0 f0 c0 c1 n leafv Hlen) as HL.
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. reflexivity.
Qed.
Lemma gp_E53 : forall regs regs0 f0 c0 c1 n leafv pal, length (tn_mean n) = 3%nat ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) 53 = Z_to_bv 64 (2 ^ 64 - 1 - pal).
Proof.
intros regs regs0 f0 c0 c1 n leafv pal Hlen. unfold gp_extra. change 53%nat with (32 + 21)%nat. rewrite ew_Ereg_extra.
pose proof (gp_len20 regs0 f0 c0 c1 n leafv Hlen) as HL.
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. reflexivity.
Qed.
Lemma gp_EF : forall regs regs0 f0 c0 c1 n leafv pal j v, nth_error (gpf_vals regs0 f0) j = Some v ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) (32 + j) = Z_to_bv 64 v.
Proof. intros regs regs0 f0 c0 c1 n leafv pal j v Hj. unfold gp_extra. rewrite map_app, <- app_assoc. apply Ereg_vals. exact Hj. Qed.
Lemma gp_EN : forall regs regs0 f0 c0 c1 n leafv pal j v, nth_error (node_vals c0 c1 n leafv) j = Some v ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) (42 + j) = Z_to_bv 64 v.
Proof.
intros regs regs0 f0 c0 c1 n leafv pal j v Hj. unfold gp_extra. change (42 + j)%nat with (32 + (10 + j))%nat. rewrite ew_Ereg_extra.
assert (Hl : (j < length (node_vals c0 c1 n leafv))%nat) by (apply nth_error_Some; congruence).
rewrite app_nth1 by (rewrite length_map, length_app; cbn [gpf_vals length]; lia).
rewrite map_app, app_nth2 by (rewrite length_map; cbn [gpf_vals length]; lia).
rewrite length_map. cbn [gpf_vals length]. replace (10 + j - 10)%nat with j by lia.
apply nth_error_nth. apply map_nth_error. exact Hj.
Qed.
Lemma gp_cidx_range : forall m a c0 c1 n leafv, length (tn_mean n) = 3%nat ->
obj_at trbsegs m a LAY_Node (node_vals c0 c1 n leafv) -> 0 <= tn_cidx n < 256.
Proof.
intros m a c0 c1 n leafv Hlen Ond.
assert (Hnv8 : nth_error (node_vals c0 c1 n leafv) 8 = Some (tn_cidx n)).
{ unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity. }
destruct (obj_at_nth trbsegs _ _ _ _ 8%nat (49, 1%N) (tn_cidx n) Ond eq_refl Hnv8) as [_ R]. cbn [snd Z.of_N] in R. change (2 ^ (8 * 1)) with 256 in R. exact R.
Qed.
Lemma gp_pal_range : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k pal cid pos,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
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
Lemma gp_rodata_j2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own2 ly2 S2 mem2 md2 k2,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own2 ly2 S2 W mem2 md2 k2 ->
arodata_ok B (aview trbsegs (w_H W) memc) -> arodata_ok B (aview trbsegs (w_H W) mem2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own2 ly2 S2 mem2 md2 k2 HJ HJ2 HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3' & _).
assert (Himg : in_img trbsegs a).
{ destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia. }
rewrite (F3' a Himg Ho He), <- (F3 a Himg Ho He). exact (HR a Hro Ho He).
Qed.
Lemma gp_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_dec n 64).
- replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.
Lemma gp_sh6_denot : forall E node, ew E 9 = w64 node -> ew E 20 = w64 SB -> 4096 <= node <= 140737479966720 ->
sv_denot E gp_sh6 = w64 (SB + (node + 49) / 8).
Proof.
intros E node E9 E20 Rn. unfold gp_sh6, w64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 9 node 49 E9) by lia. rewrite U_SLit, (U_atom E 20 SB E20) by (unfold SB; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (node + 49) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((node + 49) / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64, SB; lia). lia.
Qed.
Lemma gp_seed : forall (fy : FPState) (g : nat) (regs0 f0 regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k
(pal cid pos : Z) (d : nat) (n : tnode) (c0 c1 leafv : Z),
let sp := spZ regs0 in
let E := Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal) in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
sp mod 16 = 0 -> sp0 - STK <= sp - GPB_STK (Z.of_nat d) -> sp <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF pal 768 ->
getr regs 2 = w64 (sp - 80) -> getr regs 8 = w64 pal -> getr regs 9 = w64 (tn_addr n) -> getr regs 20 = w64 SB ->
gp_pin_facts g regs (tn_addr n) pal ->
obj_at trbsegs (mrestrict (w_H W) mem) (sp - 80) LAY_GPF (gpf_vals regs0 f0) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trbsegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
@st_ok trbsegs fy E (ss_gp g leafv) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (gp_pc g)) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs gp_Bx gp_SH E (mrestrict (w_H W) mem).
Proof.
intros fy g regs0 f0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 leafv sp E
HJ HRO Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Ofr Hinn Ond Hlen.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & _ & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as Hnh_img.
change (req_size NODE_SIZE) with 56 in *.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (sep_block_frame trbsegs _ LAWS lyc Sc _ _ _ (tn_addr n) NODE_SIZE cid pos HAR Hinn Hfin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (req_size NODE_SIZE) with 56 in HdBF.
pose proof (obj_at_nth trbsegs _ _ _ _ 8%nat (49, 1%N) (tn_cidx n) Ond eq_refl) as Fcidx.
assert (Hnv8 : nth_error (node_vals c0 c1 n leafv) 8 = Some (tn_cidx n)).
{ unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity. }
specialize (Fcidx Hnv8). destruct Fcidx as [_ Rcidx]. cbn [snd Z.of_N] in Rcidx. change (2 ^ (8 * 1)) with 256 in Rcidx.
rewrite restrict_mkst_fx.
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVF : forall j v, nth_error (gpf_vals regs0 f0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply gp_EF; exact Hj).
assert (HVN : forall j v, nth_error (node_vals c0 c1 n leafv) j = Some v -> ew E (42 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply gp_EN; exact Hj).
assert (E52 : ew E 52 = Z_to_bv 64 (pal + 3 * tn_cidx n)) by (subst E; apply gp_E52; exact Hlen).
assert (E53 : ew E 53 = Z_to_bv 64 (2 ^ 64 - 1 - pal)) by (subst E; apply gp_E53; exact Hlen).
assert (E50 : ew E 50 = Z_to_bv 64 (tn_cidx n)) by (apply (HVN 8%nat); exact Hnv8).
assert (E2 : ew E 2 = getr regs 2) by (apply (HE 2%nat 2%bv); reflexivity).
assert (E8 : ew E 8 = w64 pal) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (E9 : ew E 9 = w64 (tn_addr n)) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (E20 : ew E 20 = w64 SB) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (Hspr : 0 <= sp - 80 < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 HGS Hstk0; lia).
assert (U2 : bv_unsigned (ew E 2) = sp - 80) by (rewrite E2, G2; apply unsigned_lit_small; exact Hspr).
assert (U9 : bv_unsigned (ew E 9) = tn_addr n) by (rewrite E9; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (Rpal : 4096 <= pal /\ pal + 768 <= 2 ^ 47) by (clear - Hpal1 Hpal2 HFhi1 HFhi2 HFB C1 CR CR0; lia).
assert (U52 : bv_unsigned (ew E 52) = pal + 3 * tn_cidx n) by (rewrite E52; apply unsigned_lit_small; clear - Rpal Rcidx; lia).
assert (U53 : bv_unsigned (ew E 53) = 2 ^ 64 - 1 - pal) by (rewrite E53; apply unsigned_lit_small; clear - Rpal; lia).
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
split.
- unfold ss_gp. apply (entry_st_ok_full trbsegs).
+ destruct g as [|[|[|[|g]]]]; cbn [gp_regs gp_pin_facts] in *.
* destruct Gpin as [G10 G18].
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
-- rewrite G10. cbn [sv_denot]. fold E. rewrite U9. reflexivity.
-- rewrite G18. reflexivity.
* apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |].
rewrite Gpin. cbn [sv_denot]. fold E. rewrite U9. reflexivity.
* destruct Gpin as (G19 & G18 & G21 & G22).
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
-- rewrite G19. cbn [sv_denot]. fold E. rewrite U9. reflexivity.
-- rewrite G18. cbn [sv_denot]. fold E. rewrite U9. reflexivity.
-- rewrite G21. cbn [sv_denot]. fold E. rewrite U53, Z.add_0_r. reflexivity.
-- rewrite G22. fold E. symmetry. apply (gp_sh6_denot E (tn_addr n) E9 E20 Rn).
* destruct Gpin as (G19 & G18 & G21 & G22).
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
-- rewrite G19. cbn [sv_denot]. fold E. rewrite U9. reflexivity.
-- rewrite G18. cbn [sv_denot]. fold E. rewrite U9. reflexivity.
-- rewrite G21. cbn [sv_denot]. fold E. rewrite U53, Z.add_0_r. reflexivity.
-- rewrite G22. fold E. symmetry. apply (gp_sh6_denot E (tn_addr n) E9 E20 Rn).
* apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |].
rewrite Gpin. reflexivity.
+ destruct g as [|[|[|[|g]]]]; vm_compute; reflexivity.
+ unfold gp_mem. repeat apply Forall_cons; try apply Forall_nil.
* eapply (region_ok_obj_gen trbsegs _ _ 2 (sp - 80)); [exact U2 | lia | lia | exact Ofr | reflexivity | exact HVF | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
* eapply (region_ok_obj_gen trbsegs _ _ 9 (tn_addr n)); [exact U9 | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U52.
split; [clear - Rpal Rcidx; lia|]. split; [clear - Rpal Rcidx; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (HFpres (pal + 3 * tn_cidx n + o) ltac:(clear - Ho Hpal1 Hpal2 Rcidx; lia))).
* unfold gp_rodata, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold GPR_LO, GPR_HI.
split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor; [|constructor]].
-- intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
destruct (trb_fpc_mbyte B (w_H W) mem (0x10300 + i) FPC HRO ltac:(unfold trb_fpc_addr; lia)) as (b & Hb & Hm).
exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb | exact Hm].
-- intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
destruct (trb_fpc_mbyte B (w_H W) mem (0x10340 + i) FPC HRO ltac:(unfold trb_fpc_addr; lia)) as (b & Hb & Hm).
exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb | exact Hm].
+ apply pairwise_disjoint_of_extents. unfold gp_mem, gp_rodata, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U2, U9, U52. unfold NODE_SIZE, GPR_LO, GPR_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
subst sp. revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 Hstk0 HGS Hpal1 Hpal2 HFhi1 HFhi2 HFhi2_img Hnceil Hn4096 Hnh Hnh_img HdBF Rcidx HFB Rpal. clear. ceil; unfold zone2, off_img, in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [gp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U2, U9, U52, U53, E20, E50, !unsigned_lit_small by (unfold SB; clear - Rcidx; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
subst sp. revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 C1 C3 Hstk0 HGS Hpal1 Hpal2 HFhi1 HFhi2 HFhi2_img Hnceil Hn4096 Hn16 Hnh Hnh_img Rcidx HFB Rpal. clear. unfold off_img.
ceil; unfold SB, zone2, in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat match goal with |- _ /\ _ => split end; try lia.
rewrite Zminus_mod, Hal16. reflexivity.
* cbn [gp_facts f_alias alias_ok gp_alias]. split; [|split; [|exact I]].
-- fold E. apply U_inj. unfold gp_3cidx. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 8 pal E8) by (clear - Rpal; lia). rewrite (U_atom E 50 (tn_cidx n) E50) by lia. rewrite U_SLit.
rewrite (U_atom E 52 (pal + 3 * tn_cidx n) E52) by (clear - Rpal Rcidx; lia).
change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (tn_cidx n * 2)) by (unfold M64; lia). rewrite (zcanon_id (tn_cidx n * 2 + tn_cidx n)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; clear - Rpal Rcidx; lia). lia.
-- fold E. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 8 pal E8) by (clear - Rpal; lia). rewrite U_SLit.
rewrite (U_atom E 53 (2 ^ 64 - 1 - pal) E53) by (clear - Rpal; lia).
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite gp_lxor_ones64 by (clear - Rpal; lia). apply zcanon_id. unfold M64. clear - Rpal. lia.
- unfold sh_ok, gp_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block trbsegs B LAWS lyc Sc W mem md E gp_Bx 9 (tn_addr n) NODE_SIZE 0 NODE_SIZE HAR Hinn).
* unfold U, gp_Bx. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
* lia.
* change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
+ apply (shent_ok_of_range trbsegs (w_H W) mem E gp_Bx 52 pal 768 (pal + 3 * tn_cidx n) 0 3 HRA).
* unfold U, gp_Bx. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U52.
* clear - Rcidx; lia.
* clear - Rcidx; lia.
* intros x Hx. clear - Hx Hpal1 Hpal2 HFhi1 HFhi2 HFhi2_img Rcidx HFB C1 CR CR0. unfold off_img, SHADOW_OFF in *. lia.
Qed.
Lemma gl_round_call : forall E ss ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc W md k (spc : Z) (Q : world trbsegs -> config -> Prop),
st_okF trbsegs E ss (restrict (w_H W) ms) -> ss_pc ss = A_round -> ss_resv ss = None ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
spZ (ms_regs ms) = spc -> spc mod 16 = 0 -> sp0 - STK <= spc - 16 -> spc <= sp0 ->
YK0s.ret_ok (getr (ms_regs ms) 1) -> 4096 <= raZ (ms_regs ms) ->
arodata_ok B (aview trbsegs (w_H W) (ms_mem ms)) ->
(forall (fx1 : FPState) (regs1 : bvmap 5 word) (mem1 : word -> option byte) md1,
frm_zero (@fp_csr fx1) ->
reg_get (@fp_regs fx1) 10 = round_bits (reg_get (ms_fregs ms) 10) ->
fregs_preserved (ms_fregs ms) (@fp_regs fx1) ->
aregs_preserved (ms_regs ms) regs1 ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc - 16 <= a < spc) -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) (ms_mem ms) a) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem1 a) ->
SRr trbsegs W (mkCfg (@mkst fx1 regs1 (getr (ms_regs ms) 1) mem1 (seg_rom trbsegs)) md1) Q) ->
SRr trbsegs W (mkCfg ms md) Q.
Proof.
intros E ss ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc W md k spc Q HS Hpc Hrv HJ Hsp Hal Hlo Hhi Hra Hra4 HRO HK.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL.
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm.
rewrite (@st_ok_restrict_mkst trbsegs (fp_of (restrict (w_H W) ms)) (w_H W) _ _ ms HSL Hrv), Hpc.
eapply SRr_bind.
{ eapply (TROUND (fp_of (restrict (w_H W) ms)) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k (ms_regs ms) HJ Hra Hra4);
[ rewrite Hsp; exact Hal | rewrite Hsp; unfold TROUND_STK; exact Hlo | rewrite Hsp; exact Hhi | exact Hfrm | exact HRO ]. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs1 & mem1 & md1 & -> & Hfrm1 & Hfa1 & Hfp1 & HJ1 & HP1 & HM1 & HX1).
apply (HK fx1 regs1 mem1 md1 Hfrm1); [exact Hfa1 | exact Hfp1 | exact HP1 | exact HJ1 | | exact HX1].
intros a Ha Hn. apply HM1; [exact Ha | rewrite Hsp; unfold TROUND_STK; exact Hn].
Qed.
Lemma gp_kept : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memJ mdJ k (pal cid pos sp lo hi : Z) (mem m' : word -> option byte),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memJ mdJ k ->
In (cid, pos) own -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
sp0 - STK <= lo -> lo <= hi -> hi <= sp - 80 -> sp <= sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) m' a = aview trbsegs (w_H W) mem a) ->
(forall b sz, In (b, sz) (ablocks B lyc Sc) -> rg_blk_kept (w_H W) (w_H W) mem m' b (req_size sz)) /\
rg_blk_kept (w_H W) (w_H W) mem m' (sp - 80) 80 /\
(range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF pal 768 ->
range_addressable (aview trbsegs (w_H W) m') SHADOW_OFF pal 768).
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
pose proof (sep_block_frame trbsegs _ LAWS lyc Sc _ _ _ b sz cid pos HAR Hb Hfin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
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
Lemma beq_w1_w0 : branch_taken BC_EQ w1 (Z_to_bv 64 0) = false.
Proof. unfold branch_taken, bv_eqb, w1. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Definition gl_fp_facts (g : nat) (fy : FPState) (n : tnode) : Prop :=
match g with
| 0%nat => True
| 1%nat => reg_get (@fp_regs fy) 10 = round_bits (w64 (nth 0 (tn_mean n) 0))
| Datatypes.S g' => reg_get (@fp_regs fy) 10 = round_bits (w64 (nth g' (tn_mean n) 0)) /\
reg_get (@fp_regs fy) 8 = Z_to_bv 64 Cm1 /\ reg_get (@fp_regs fy) 9 = Z_to_bv 64 C256
end.
Definition gl_stmt (g : nat) (n : tnode) : Prop :=
forall (fy : FPState) (regs0 f0 regs : bvmap 5 word) mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (pal cid pos : Z) (d : nat) (c0 c1 : Z),
let sp := spZ regs0 in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memg md k ->
arodata_ok B (aview trbsegs (w_H W) memg) ->
tnode_wf n -> tnode_means_ok n ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - GPB_STK (Z.of_nat d) -> sp <= sp0 ->
frm_zero (@fp_csr fy) ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trbsegs (w_H W) memg) SHADOW_OFF pal 768 ->
getr regs 2 = w64 (sp - 80) -> getr regs 8 = w64 pal -> getr regs 9 = w64 (tn_addr n) -> getr regs 20 = w64 SB ->
gp_pin_facts g regs (tn_addr n) pal -> gl_fp_facts g fy n ->
(forall r : bv 5, In r GP_UNTOUCHED -> getr regs r = getr regs0 r) ->
obj_at trbsegs (mrestrict (w_H W) memg) (sp - 80) LAY_GPF (gpf_vals regs0 f0) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trbsegs (mrestrict (w_H W) memg) (tn_addr n) LAY_Node (node_vals c0 c1 n 1) -> length (tn_mean n) = 3%nat ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) memg a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memg a) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 (gp_pc g)) memg (seg_rom trbsegs)) md)
(gp_post regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k (sp - GPB_STK (Z.of_nat d)) (sp - 80) pal).
Lemma gl_call : forall (g : nat) (n : tnode), gl_stmt (Datatypes.S g) n -> (g <= 2)%nat ->
forall E ss ms (regs0 f0 : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (pal cid pos : Z) (d : nat) (c0 c1 : Z),
let sp := spZ regs0 in
st_okF trbsegs E ss (restrict (w_H W) ms) -> ss_pc ss = A_round -> ss_resv ss = None ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
arodata_ok B (aview trbsegs (w_H W) (ms_mem ms)) ->
tnode_wf n -> tnode_means_ok n ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - GPB_STK (Z.of_nat d) -> sp <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trbsegs (w_H W) (ms_mem ms)) SHADOW_OFF pal 768 ->
sv_denot E (sr_get (ss_regs ss) 1) = w64 (gp_pc (Datatypes.S g)) ->
sv_denot E (sr_get (ss_regs ss) 2) = w64 (sp - 80) -> sv_denot E (sr_get (ss_regs ss) 8) = w64 pal ->
sv_denot E (sr_get (ss_regs ss) 9) = w64 (tn_addr n) -> sv_denot E (sr_get (ss_regs ss) 20) = w64 SB ->
sv_denot E (sr_get (ss_regs ss) 19) = w64 (tn_addr n + 16) ->
((1 <= g)%nat -> sv_denot E (sr_get (ss_regs ss) 18) = w64 (tn_addr n + 49) /\ sv_denot E (sr_get (ss_regs ss) 21) = w64 (2 ^ 64 - 1 - pal) /\
sv_denot E (sr_get (ss_regs ss) 22) = w64 (SB + (tn_addr n + 49) / 8)) ->
sv_denot E (sfr_get (ss_fregs ss) 10) = w64 (nth g (tn_mean n) 0) ->
((1 <= g)%nat -> sv_denot E (sfr_get (ss_fregs ss) 8) = Z_to_bv 64 Cm1 /\ sv_denot E (sfr_get (ss_fregs ss) 9) = Z_to_bv 64 C256) ->
(forall r : bv 5, In r GP_UNTOUCHED -> sv_denot E (sr_get (ss_regs ss) r) = getr regs0 r) ->
obj_at trbsegs (mrestrict (w_H W) (ms_mem ms)) (sp - 80) LAY_GPF (gpf_vals regs0 f0) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trbsegs (mrestrict (w_H W) (ms_mem ms)) (tn_addr n) LAY_Node (node_vals c0 c1 n 1) -> length (tn_mean n) = 3%nat ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) (ms_mem ms) a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
SRr trbsegs W (mkCfg ms md)
(gp_post regs0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k (sp - GPB_STK (Z.of_nat d)) (sp - 80) pal).
Proof.
intros g n HN Hg E ss ms regs0 f0 mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 sp
HS Hpc Hrv HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA D1 D2 D8 D9 D20 D19 Dpin Df10 Df89 Dkeep Ofr Hinn Ond Hlen KEEP PR.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
assert (Hspr : 0 <= sp - 80 < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 HGS Hstk0; lia).
assert (RG : forall r : bv 5, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)) by (intros r; exact (st_okF_reg trbsegs E ss _ r HS)).
assert (FG : forall r : bv 5, reg_get (ms_fregs ms) r = sv_denot E (sfr_get (ss_fregs ss) r)) by (intros r; exact (st_okF_freg trbsegs E ss _ r HS)).
eapply (gl_round_call E ss ms STK sp0 FP ly S W0 mem0 md0 own lyc Sc W md k (sp - 80) _ HS Hpc Hrv HJ).
- unfold spZ. rewrite RG, D2. apply unsigned_lit_small. exact Hspr.
- replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- clear - Hwlo HGS. lia.
- clear - Hwhi. lia.
- rewrite RG, D1. apply ret_ok_even. destruct g as [|[|[|g]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia].
- unfold raZ. rewrite RG, D1. unfold w64. destruct g as [|[|[|g]]]; [ | | | lia]; cbn [gp_pc]; unfold GP_L1, GP_L2, GP_L3; rewrite unsigned_lit_small by lia; lia.
- exact HRO.
- intros fx1 regs1 mem1 md1 Hfrm1 Hfa1 Hfp1 HP1 HJ1 HM1 HX1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) (ms_mem ms) a).
{ intros a Ha Hn1 _. apply HM1; [exact Ha | clear - Hn1 HGS; lia]. }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GPB_STK (Z.of_nat d)) (sp - 80) (ms_mem ms) mem1
HJ1 Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS; lia) ltac:(clear; lia) Hwhi KEEP1) as (KC1 & KC2 & KC3).
pose proof (gp_pres_in _ _ HP1) as PRr.
rewrite RG, D1.
eapply (HN fx1 regs0 f0 regs1 mem mem1 md1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1
HJ1 (gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ1 HRO) Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hfrm1 Hown Hcid Hpal1 Hpal2 (KC3 HRA)).
+ rewrite (PRr (2%bv : bv 5) ltac:(cbv; tauto)), RG. exact D2.
+ rewrite (PRr (8%bv : bv 5) ltac:(cbv; tauto)), RG. exact D8.
+ rewrite (PRr (9%bv : bv 5) ltac:(cbv; tauto)), RG. exact D9.
+ rewrite (PRr (20%bv : bv 5) ltac:(cbv; tauto)), RG. exact D20.
+ destruct g as [|[|[|g]]]; [ | | | lia]; cbn [gp_pin_facts].
* rewrite (PRr (19%bv : bv 5) ltac:(cbv; tauto)), RG. exact D19.
* destruct (Dpin ltac:(lia)) as (D18 & D21 & D22).
rewrite (PRr (19%bv : bv 5) ltac:(cbv; tauto)), (PRr (18%bv : bv 5) ltac:(cbv; tauto)), (PRr (21%bv : bv 5) ltac:(cbv; tauto)), (PRr (22%bv : bv 5) ltac:(cbv; tauto)), !RG.
split; [exact D19 | split; [exact D18 | split; [exact D21 | exact D22]]].
* destruct (Dpin ltac:(lia)) as (D18 & D21 & D22).
rewrite (PRr (19%bv : bv 5) ltac:(cbv; tauto)), (PRr (18%bv : bv 5) ltac:(cbv; tauto)), (PRr (21%bv : bv 5) ltac:(cbv; tauto)), (PRr (22%bv : bv 5) ltac:(cbv; tauto)), !RG.
split; [exact D19 | split; [exact D18 | split; [exact D21 | exact D22]]].
+ destruct g as [|g]; cbn [gl_fp_facts].
* rewrite Hfa1, FG, Df10. reflexivity.
* destruct (Df89 ltac:(lia)) as (Df8 & Df9).
split; [rewrite Hfa1, FG, Df10; reflexivity|].
split; [rewrite (Hfp1 (8%bv : bv 5) ltac:(cbv; tauto)), FG; exact Df8 | rewrite (Hfp1 (9%bv : bv 5) ltac:(cbv; tauto)), FG; exact Df9].
+ intros r Hr. rewrite (PRr r ltac:(cbv [GP_UNTOUCHED In] in Hr; cbv [CALLEE_SAVED In]; intuition)), RG. exact (Dkeep r Hr).
+ exact (rg_obj_at_blk_kept (w_H W) (w_H W) (ms_mem ms) mem1 (sp - 80) LAY_GPF _ 80 Ofr ltac:(vm_compute; reflexivity) KC2).
+ exact Hinn.
+ apply (rg_obj_at_blk_kept (w_H W) (w_H W) (ms_mem ms) mem1 (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)). exact (KC1 _ _ Hinn).
+ exact Hlen.
+ intros a Ha Hn1 Hn2. rewrite (KEEP1 a Ha Hn1 Hn2). exact (KEEP a Ha Hn1 Hn2).
+ intros a Ha. apply HX1. apply PR. exact Ha.
Qed.
Lemma gl_kept : forall E0 rs (H : word -> bool) (m m' : word -> option byte) p3,
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some 52%nat /\ 0 <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= 3)) ->
bv_unsigned (ew E0 52) = p3 ->
forall x, 0 <= x < 2 ^ 64 -> ~ (p3 <= x < p3 + 3) -> aview trbsegs H m' x = aview trbsegs H m x.
Proof.
intros E0 rs H m m' p3 HF Hrs Hp x Hx Hnw. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). destruct (Hrs rr Hin) as [Hro | (Hb & Hlo & Hhi)]; [lia|].
rewrite Hb in Hr. cbn [base_val] in Hr. rewrite Hp in Hr. lia.
Qed.
Local Ltac gl_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; vm_compute in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Local Ltac gl_step stop HSF HJ SHOKF KEEP PR U52 Rcidx Rpal Hown Hpal1 Hpal2 W mem sp d pal cid pos :=
lazymatch type of HSF with st_okF _ ?Ex _ _ =>
let U52x := fresh "U52x" in
assert (U52x : bv_unsigned (ew Ex 52) = pal + 3 * tn_cidx _) by (rewrite ?ew_ewset_other by lia; exact U52);
aj_run_to_tokF trbtbl_lib_ok HSF HJ SHOKF gp_Bspan stop;
[ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyx ?ownx =>
let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk s0 fp b0 bc lyx ownx) end;
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen; [reflexivity | exact U52x | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]];
cbn [YQ0b.r_wlo YQ0b.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; right; right; right; exists cid, pos; split; [exact Hown|]; left;
unfold in_zr; cbn [fst snd]; clear - Ha Hpal1 Hpal2 Rcidx; lia
| lazymatch goal with
| HFrx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2), HGx : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), HFx : frame_of _ _ ?m1 ?m2 |- _ =>
let KE2 := fresh "KEEP" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) m2 a = aview trbsegs (w_H W) mem a)
by (let a' := fresh "a" in let Ha' := fresh "Ha" in let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in
intros a' Ha' Hn1 Hn2; rewrite (gl_kept _ _ _ _ _ _ HFrx ltac:(gl_rs_tac) U52x a' Ha' ltac:(clear - Hn2 Rcidx; lia)); exact (KEEP a' Ha' Hn1 Hn2));
clear KEEP; rename KE2 into KEEP;
let PR2 := fresh "PR" in
assert (PR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) m2 a) by (let a' := fresh "a" in let Ha' := fresh "Ha" in intros a' Ha'; exact (apresent_grows _ _ _ _ HGx (PR a' Ha')));
clear PR; rename PR2 into PR; clear HFx HFrx HGx U52x end ]
end.
Local Ltac gl_refute Hc Ha Hb Hd Hchk :=
exfalso; cbn [sv_denot] in Hc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc; rewrite ?ew_ewset_other in Hc by lia;
rewrite fcmp_denot in Hc; cbn [fcmp_sem fp_format] in Hc; rewrite !fp_arg_D in Hc;
rewrite ?Ha, ?Hb, ?Hd in Hc; unfold Cm1, C256, w64 in Hc; rewrite ?unsigned_lit_small in Hc by lia;
try change 13830554455654793216 with Cm1 in Hc; try change 4643211215818981376 with C256 in Hc;
first [ rewrite (proj1 Hchk) in Hc | rewrite (proj2 Hchk) in Hc ]; rewrite beq_w1_w0 in Hc; discriminate Hc.
Lemma gp_mean_nth : forall c0 c1 n lf j, length (tn_mean n) = 3%nat -> (j < 3)%nat ->
nth_error (node_vals c0 c1 n lf) (2 + j) = Some (nth j (tn_mean n) 0).
Proof.
intros c0 c1 n lf j Hlen Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.
Local Ltac gl_den :=
lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia.
Lemma gl3 : forall n, gl_stmt 3 n.
Proof.
intros n fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Gfp Gkeep Ofr Hinn Ond Hlen KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
destruct (gp_seed fy 3%nat regs0 f0 regs memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 1
HJ HRO Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Ofr Hinn Ond Hlen) as [HS SHOK].
set (E0 := Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) in *.
pose proof (st_ok_enterF trbsegs fy 54 E0 _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF.
pose proof (sh_ok_agree trbsegs gp_Bx gp_SH 54 E0 (ew_fregs E0 54 (@fp_regs fy)) _ (env_agree_ew_fregs E0 54 _) ltac:(vm_compute; reflexivity) SHOK) as SHOKF.
clear HS SHOK. set (E := ew_fregs E0 54 (@fp_regs fy)) in *.
pose proof (gp_cidx_range _ _ c0 c1 n 1 Hlen Ond) as Rcidx.
destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
assert (U52 : bv_unsigned (ew E 52) = pal + 3 * tn_cidx n).
{ subst E. rewrite ew_fregs_low by lia. subst E0. rewrite (gp_E52 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. clear - Rp1 Rp2 Rcidx. lia. }
assert (HEf : forall r : bv 5, ew E (54 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
destruct Gfp as (Gf10 & Gf8 & Gf9).
assert (Ha64 : ew E 64 = round_bits (w64 (nth 2 (tn_mean n) 0))) by (rewrite <- Gf10; exact (HEf 10%bv)).
assert (Ha62 : ew E 62 = Z_to_bv 64 Cm1) by (rewrite <- Gf8; exact (HEf 8%bv)).
assert (Ha63 : ew E 63 = Z_to_bv 64 C256) by (rewrite <- Gf9; exact (HEf 9%bv)).
destruct Hwfn as (_ & _ & _ & _ & _ & Hmr). unfold tnode_means_ok in Hmokn.
assert (Hchk : fst (fp_lt fmt_double Cm1 (bv_unsigned (round_bits (Z_to_bv 64 (nth 2 (tn_mean n) 0))))) = true /\
fst (fp_lt fmt_double (bv_unsigned (round_bits (Z_to_bv 64 (nth 2 (tn_mean n) 0)))) C256) = true).
{ apply (round_checks_mean _ RTZ).
- rewrite Forall_forall in Hmokn. apply Hmokn. apply nth_In. rewrite Hlen. lia.
- rewrite Forall_forall in Hmr. apply Hmr. apply nth_In. rewrite Hlen. lia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp gp_pc] in HSF.
gl_step 0 HSF HJ SHOKF KEEP PR U52 Rcidx Rp1 Hown Hpal1 Hpal2 W mem sp d pal cid pos.
lg_branchF trbtbl_lib_ok HSF; [gl_refute Hc Ha62 Ha63 Ha64 Hchk | clear Hc].
gl_step 0 HSF HJ SHOKF KEEP PR U52 Rcidx Rp1 Hown Hpal1 Hpal2 W mem sp d pal cid pos.
lg_branchF trbtbl_lib_ok HSF; [gl_refute Hc Ha62 Ha63 Ha64 Hchk | clear Hc].
gl_step 0 HSF HJ SHOKF KEEP PR U52 Rcidx Rp1 Hown Hpal1 Hpal2 W mem sp d pal cid pos.
pose proof (st_okF_frm trbsegs _ _ _ HSF) as Hfrm'.
pose proof (st_okF_to_legacy trbsegs _ _ _ HSF) as HSL.
assert (EV : forall j, (j < 54)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; lia).
assert (EF : forall j v, nth_error (gpf_vals regs0 f0) j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply gp_EF; exact Hj).
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros j rr Hrr; subst E0; apply ew_Ereg_nat; exact Hrr).
pose proof (EF 2%nat _ eq_refl) as F34. pose proof (EF 3%nat _ eq_refl) as F35. pose proof (EF 4%nat _ eq_refl) as F36. pose proof (EF 5%nat _ eq_refl) as F37.
pose proof (EF 6%nat _ eq_refl) as F38. pose proof (EF 7%nat _ eq_refl) as F39. pose proof (EF 8%nat _ eq_refl) as F40. pose proof (EF 9%nat _ eq_refl) as F41.
cbn [Nat.add] in F34, F35, F36, F37, F38, F39, F40, F41.
rreg HSL (1%bv : bv 5) R1.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HSL eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gp_post. split; [reflexivity|].
rewrite R1. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite ?ew_ewset_other by lia. rewrite (EV 41%nat ltac:(lia)), F41, Z_to_bv_bv_unsigned, Hra.
lazymatch type of HSF with st_okF _ _ _ (restrict ?Hh ?msF) => exists (fp_of (restrict Hh msF)), (ms_regs msF), (ms_mem msF) end. eexists. split; [reflexivity|].
split; [exact Hfrm'|].
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ|].
split; [|split; [exact KEEP | exact PR]].
assert (Hspr : 0 <= sp - 80 /\ sp < 2 ^ 64).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _). assert (96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia). subst sp. clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 H Hstk0. lia. }
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
lazymatch type of HSF with st_okF _ _ _ (restrict _ ?msF) =>
repeat (destruct Hc as [-> | Hc]); [ | | | | | | | | | | | | | | subst r];
[ assert (X : getr (ms_regs msF) (2%bv : bv 5) = getr regs0 (2%bv : bv 5)); [|exact X]; rreg HSL (2%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite (EV 2%nat ltac:(lia)), (ER 2%nat 2%bv eq_refl), G2;
unfold w64; rewrite unsigned_lit_small by lia; replace (sp - 80 + 80) with sp by lia; subst sp; unfold spZ; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (3%bv : bv 5) = getr regs0 (3%bv : bv 5)); [|exact X]; rreg HSL (3%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 3%nat ltac:(lia)), (ER 3%nat 3%bv eq_refl); apply Gkeep; cbv; tauto
| assert (X : getr (ms_regs msF) (4%bv : bv 5) = getr regs0 (4%bv : bv 5)); [|exact X]; rreg HSL (4%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 4%nat ltac:(lia)), (ER 4%nat 4%bv eq_refl); apply Gkeep; cbv; tauto
| assert (X : getr (ms_regs msF) (8%bv : bv 5) = getr regs0 (8%bv : bv 5)); [|exact X]; rreg HSL (8%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 40%nat ltac:(lia)), F40; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (9%bv : bv 5) = getr regs0 (9%bv : bv 5)); [|exact X]; rreg HSL (9%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 39%nat ltac:(lia)), F39; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (18%bv : bv 5) = getr regs0 (18%bv : bv 5)); [|exact X]; rreg HSL (18%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 38%nat ltac:(lia)), F38; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (19%bv : bv 5) = getr regs0 (19%bv : bv 5)); [|exact X]; rreg HSL (19%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 37%nat ltac:(lia)), F37; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (20%bv : bv 5) = getr regs0 (20%bv : bv 5)); [|exact X]; rreg HSL (20%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 36%nat ltac:(lia)), F36; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (21%bv : bv 5) = getr regs0 (21%bv : bv 5)); [|exact X]; rreg HSL (21%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 35%nat ltac:(lia)), F35; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (22%bv : bv 5) = getr regs0 (22%bv : bv 5)); [|exact X]; rreg HSL (22%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 34%nat ltac:(lia)), F34; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs msF) (23%bv : bv 5) = getr regs0 (23%bv : bv 5)); [|exact X]; rreg HSL (23%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 23%nat ltac:(lia)), (ER 23%nat 23%bv eq_refl); apply Gkeep; cbv; tauto
| assert (X : getr (ms_regs msF) (24%bv : bv 5) = getr regs0 (24%bv : bv 5)); [|exact X]; rreg HSL (24%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 24%nat ltac:(lia)), (ER 24%nat 24%bv eq_refl); apply Gkeep; cbv; tauto
| assert (X : getr (ms_regs msF) (25%bv : bv 5) = getr regs0 (25%bv : bv 5)); [|exact X]; rreg HSL (25%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 25%nat ltac:(lia)), (ER 25%nat 25%bv eq_refl); apply Gkeep; cbv; tauto
| assert (X : getr (ms_regs msF) (26%bv : bv 5) = getr regs0 (26%bv : bv 5)); [|exact X]; rreg HSL (26%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 26%nat ltac:(lia)), (ER 26%nat 26%bv eq_refl); apply Gkeep; cbv; tauto
| assert (X : getr (ms_regs msF) (27%bv : bv 5) = getr regs0 (27%bv : bv 5)); [|exact X]; rreg HSL (27%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other by lia; rewrite (EV 27%nat ltac:(lia)), (ER 27%nat 27%bv eq_refl); apply Gkeep; cbv; tauto ]
end.
Qed.
Lemma gl2 : forall n, gl_stmt 2 n.
Proof.
intros n fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Gfp Gkeep Ofr Hinn Ond Hlen KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof HJ as HJ0.
destruct (gp_seed fy 2%nat regs0 f0 regs memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 1
HJ HRO Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Ofr Hinn Ond Hlen) as [HS SHOK].
set (E0 := Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) in *.
pose proof (st_ok_enterF trbsegs fy 54 E0 _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF.
pose proof (sh_ok_agree trbsegs gp_Bx gp_SH 54 E0 (ew_fregs E0 54 (@fp_regs fy)) _ (env_agree_ew_fregs E0 54 _) ltac:(vm_compute; reflexivity) SHOK) as SHOKF.
clear HS SHOK. set (E := ew_fregs E0 54 (@fp_regs fy)) in *.
pose proof (gp_cidx_range _ _ c0 c1 n 1 Hlen Ond) as Rcidx.
destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
assert (U52 : bv_unsigned (ew E 52) = pal + 3 * tn_cidx n).
{ subst E. rewrite ew_fregs_low by lia. subst E0. rewrite (gp_E52 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. clear - Rp1 Rp2 Rcidx. lia. }
assert (HEf : forall r : bv 5, ew E (54 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
destruct Gfp as (Gf10 & Gf8 & Gf9).
assert (Ha64 : ew E 64 = round_bits (w64 (nth 1 (tn_mean n) 0))) by (rewrite <- Gf10; exact (HEf 10%bv)).
assert (Ha62 : ew E 62 = Z_to_bv 64 Cm1) by (rewrite <- Gf8; exact (HEf 8%bv)).
assert (Ha63 : ew E 63 = Z_to_bv 64 C256) by (rewrite <- Gf9; exact (HEf 9%bv)).
pose proof Hwfn as (_ & _ & _ & _ & _ & Hmr). pose proof Hmokn as Hmokn'. unfold tnode_means_ok in Hmokn'.
assert (Hchk : fst (fp_lt fmt_double Cm1 (bv_unsigned (round_bits (Z_to_bv 64 (nth 1 (tn_mean n) 0))))) = true /\
fst (fp_lt fmt_double (bv_unsigned (round_bits (Z_to_bv 64 (nth 1 (tn_mean n) 0)))) C256) = true).
{ apply (round_checks_mean _ RTZ).
- rewrite Forall_forall in Hmokn'. apply Hmokn'. apply nth_In. rewrite Hlen. lia.
- rewrite Forall_forall in Hmr. apply Hmr. apply nth_In. rewrite Hlen. lia. }
assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) memg a = aview trbsegs (w_H W) memg a) by reflexivity.
assert (PRL : forall a, apresent (w_H W) memg a -> apresent (w_H W) memg a) by (intros a Ha; exact Ha).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp gp_pc] in HSF.
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
lg_branchF trbtbl_lib_ok HSF; [gl_refute Hc Ha62 Ha63 Ha64 Hchk | clear Hc].
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
lg_branchF trbtbl_lib_ok HSF; [gl_refute Hc Ha62 Ha63 Ha64 Hchk | clear Hc].
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
pose proof HJ0 as (HAR0 & _). destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR0 Hinn) as (_ & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof asan_consts as (C1 & _).
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
assert (EV : forall j, (j < 54)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; lia).
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros j rr Hrr; subst E0; apply ew_Ereg_nat; exact Hrr).
lazymatch type of HSF with st_okF _ _ _ (restrict _ ?msF) =>
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GPB_STK (Z.of_nat d)) (sp - 80) memg (ms_mem msF)
HJ Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS; lia) ltac:(clear; lia) Hwhi KEEPL) as (KC1 & KC2 & KC3) end.
eapply (gl_call 2%nat n (gl3 n) ltac:(lia) _ _ _ regs0 f0 mem _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 HSF eq_refl eq_refl HJ
(gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ HRO) Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 (KC3 HRA)).
- reflexivity.
- gl_den. rewrite (EV 2%nat ltac:(lia)), (ER 2%nat 2%bv eq_refl). exact G2.
- gl_den. rewrite (EV 8%nat ltac:(lia)), (ER 8%nat 8%bv eq_refl). exact G8.
- gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl). exact G9.
- gl_den. rewrite (EV 20%nat ltac:(lia)), (ER 20%nat 20%bv eq_refl). exact G20.
- gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl), G9. unfold w64. rewrite unsigned_lit_small by (clear - Rn; lia). reflexivity.
- intros _. split; [|split].
+ gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl), G9. unfold w64. rewrite unsigned_lit_small by (clear - Rn; lia). reflexivity.
+ gl_den. rewrite (EV 53%nat ltac:(lia)). subst E0. exact (gp_E53 regs regs0 f0 c0 c1 n 1 pal Hlen).
+ lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
apply (gp_sh6_denot _ (tn_addr n)); [ | | exact Rn].
* rewrite ?ew_ewset_other by lia. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl). exact G9.
* rewrite ?ew_ewset_other by lia. rewrite (EV 20%nat ltac:(lia)), (ER 20%nat 20%bv eq_refl). exact G20.
- gl_den. rewrite (EV 46%nat ltac:(lia)). subst E0. exact (gp_EN regs regs0 f0 c0 c1 n 1 pal 4%nat _ (gp_mean_nth c0 c1 n 1 2%nat Hlen ltac:(lia))).
- intros _. split; [gl_den; exact Ha62 | gl_den; exact Ha63].
- intros r Hr. cbv [GP_UNTOUCHED In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]; gl_den;
[ rewrite (EV 3%nat ltac:(lia)), (ER 3%nat 3%bv eq_refl) | rewrite (EV 4%nat ltac:(lia)), (ER 4%nat 4%bv eq_refl)
| rewrite (EV 23%nat ltac:(lia)), (ER 23%nat 23%bv eq_refl) | rewrite (EV 24%nat ltac:(lia)), (ER 24%nat 24%bv eq_refl)
| rewrite (EV 25%nat ltac:(lia)), (ER 25%nat 25%bv eq_refl) | rewrite (EV 26%nat ltac:(lia)), (ER 26%nat 26%bv eq_refl)
| rewrite (EV 27%nat ltac:(lia)), (ER 27%nat 27%bv eq_refl) ]; apply Gkeep; cbv; tauto.
- exact (rg_obj_at_blk_kept (w_H W) (w_H W) memg _ (sp - 80) LAY_GPF _ 80 Ofr ltac:(vm_compute; reflexivity) KC2).
- exact Hinn.
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) memg _ (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)). exact (KC1 _ _ Hinn).
- exact Hlen.
- intros a Ha Hn1 Hn2. rewrite (KEEPL a Ha Hn1 Hn2). exact (KEEP a Ha Hn1 Hn2).
- intros a Ha. apply PRL. apply PR. exact Ha.
Qed.
Lemma gl1 : forall n, gl_stmt 1 n.
Proof.
intros n fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Gfp Gkeep Ofr Hinn Ond Hlen KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof HJ as HJ0.
destruct (gp_seed fy 1%nat regs0 f0 regs memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 1
HJ HRO Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Ofr Hinn Ond Hlen) as [HS SHOK].
set (E0 := Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) in *.
pose proof (st_ok_enterF trbsegs fy 54 E0 _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF.
pose proof (sh_ok_agree trbsegs gp_Bx gp_SH 54 E0 (ew_fregs E0 54 (@fp_regs fy)) _ (env_agree_ew_fregs E0 54 _) ltac:(vm_compute; reflexivity) SHOK) as SHOKF.
clear HS SHOK. set (E := ew_fregs E0 54 (@fp_regs fy)) in *.
pose proof (gp_cidx_range _ _ c0 c1 n 1 Hlen Ond) as Rcidx.
destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
assert (U52 : bv_unsigned (ew E 52) = pal + 3 * tn_cidx n).
{ subst E. rewrite ew_fregs_low by lia. subst E0. rewrite (gp_E52 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. clear - Rp1 Rp2 Rcidx. lia. }
assert (HEf : forall r : bv 5, ew E (54 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
cbn [gl_fp_facts] in Gfp.
assert (Ha64 : ew E 64 = round_bits (w64 (nth 0 (tn_mean n) 0))) by (rewrite <- Gfp; exact (HEf 10%bv)).
pose proof Hwfn as (_ & _ & _ & _ & _ & Hmr). pose proof Hmokn as Hmokn'. unfold tnode_means_ok in Hmokn'.
assert (Hchk : fst (fp_lt fmt_double Cm1 (bv_unsigned (round_bits (Z_to_bv 64 (nth 0 (tn_mean n) 0))))) = true /\
fst (fp_lt fmt_double (bv_unsigned (round_bits (Z_to_bv 64 (nth 0 (tn_mean n) 0)))) C256) = true).
{ apply (round_checks_mean _ RTZ).
- rewrite Forall_forall in Hmokn'. apply Hmokn'. apply nth_In. rewrite Hlen. lia.
- rewrite Forall_forall in Hmr. apply Hmr. apply nth_In. rewrite Hlen. lia. }
assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) memg a = aview trbsegs (w_H W) memg a) by reflexivity.
assert (PRL : forall a, apresent (w_H W) memg a -> apresent (w_H W) memg a) by (intros a Ha; exact Ha).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp gp_pc] in HSF.
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
lg_branchF trbtbl_lib_ok HSF; [gl_refute Hc Ha64 Ha64 Ha64 Hchk | clear Hc].
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
lg_branchF trbtbl_lib_ok HSF; [gl_refute Hc Ha64 Ha64 Ha64 Hchk | clear Hc].
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
pose proof HJ0 as (HAR0 & _). destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR0 Hinn) as (_ & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof asan_consts as (C1 & _).
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
assert (EV : forall j, (j < 54)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; lia).
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros j rr Hrr; subst E0; apply ew_Ereg_nat; exact Hrr).
lazymatch type of HSF with st_okF _ _ _ (restrict _ ?msF) =>
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GPB_STK (Z.of_nat d)) (sp - 80) memg (ms_mem msF)
HJ Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS; lia) ltac:(clear; lia) Hwhi KEEPL) as (KC1 & KC2 & KC3) end.
eapply (gl_call 1%nat n (gl2 n) ltac:(lia) _ _ _ regs0 f0 mem _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 HSF eq_refl eq_refl HJ
(gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ HRO) Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 (KC3 HRA)).
- reflexivity.
- gl_den. rewrite (EV 2%nat ltac:(lia)), (ER 2%nat 2%bv eq_refl). exact G2.
- gl_den. rewrite (EV 8%nat ltac:(lia)), (ER 8%nat 8%bv eq_refl). exact G8.
- gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl). exact G9.
- gl_den. rewrite (EV 20%nat ltac:(lia)), (ER 20%nat 20%bv eq_refl). exact G20.
- gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl), G9. unfold w64. rewrite unsigned_lit_small by (clear - Rn; lia). reflexivity.
- intros _. split; [|split].
+ gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl), G9. unfold w64. rewrite unsigned_lit_small by (clear - Rn; lia). reflexivity.
+ gl_den. rewrite (EV 53%nat ltac:(lia)). subst E0. exact (gp_E53 regs regs0 f0 c0 c1 n 1 pal Hlen).
+ lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
apply (gp_sh6_denot _ (tn_addr n)); [ | | exact Rn].
* rewrite ?ew_ewset_other by lia. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl). exact G9.
* rewrite ?ew_ewset_other by lia. rewrite (EV 20%nat ltac:(lia)), (ER 20%nat 20%bv eq_refl). exact G20.
- gl_den. rewrite (EV 45%nat ltac:(lia)). subst E0. exact (gp_EN regs regs0 f0 c0 c1 n 1 pal 3%nat _ (gp_mean_nth c0 c1 n 1 1%nat Hlen ltac:(lia))).
- intros _. split; [gl_den; reflexivity | gl_den; reflexivity].
- intros r Hr. cbv [GP_UNTOUCHED In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]; gl_den;
[ rewrite (EV 3%nat ltac:(lia)), (ER 3%nat 3%bv eq_refl) | rewrite (EV 4%nat ltac:(lia)), (ER 4%nat 4%bv eq_refl)
| rewrite (EV 23%nat ltac:(lia)), (ER 23%nat 23%bv eq_refl) | rewrite (EV 24%nat ltac:(lia)), (ER 24%nat 24%bv eq_refl)
| rewrite (EV 25%nat ltac:(lia)), (ER 25%nat 25%bv eq_refl) | rewrite (EV 26%nat ltac:(lia)), (ER 26%nat 26%bv eq_refl)
| rewrite (EV 27%nat ltac:(lia)), (ER 27%nat 27%bv eq_refl) ]; apply Gkeep; cbv; tauto.
- exact (rg_obj_at_blk_kept (w_H W) (w_H W) memg _ (sp - 80) LAY_GPF _ 80 Ofr ltac:(vm_compute; reflexivity) KC2).
- exact Hinn.
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) memg _ (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)). exact (KC1 _ _ Hinn).
- exact Hlen.
- intros a Ha Hn1 Hn2. rewrite (KEEPL a Ha Hn1 Hn2). exact (KEEP a Ha Hn1 Hn2).
- intros a Ha. apply PRL. apply PR. exact Ha.
Qed.
Lemma gl0 : forall n, gl_stmt 0 n.
Proof.
intros n fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Gfp Gkeep Ofr Hinn Ond Hlen KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof HJ as HJ0.
destruct (gp_seed fy 0%nat regs0 f0 regs memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d n c0 c1 1
HJ HRO Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 Gpin Ofr Hinn Ond Hlen) as [HS SHOK].
set (E0 := Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) in *.
pose proof (st_ok_enterF trbsegs fy 54 E0 _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF.
pose proof (sh_ok_agree trbsegs gp_Bx gp_SH 54 E0 (ew_fregs E0 54 (@fp_regs fy)) _ (env_agree_ew_fregs E0 54 _) ltac:(vm_compute; reflexivity) SHOK) as SHOKF.
clear HS SHOK. set (E := ew_fregs E0 54 (@fp_regs fy)) in *.
pose proof (gp_cidx_range _ _ c0 c1 n 1 Hlen Ond) as Rcidx.
destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
assert (U52 : bv_unsigned (ew E 52) = pal + 3 * tn_cidx n).
{ subst E. rewrite ew_fregs_low by lia. subst E0. rewrite (gp_E52 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. clear - Rp1 Rp2 Rcidx. lia. }
assert (HEf : forall r : bv 5, ew E (54 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (KEEPL : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat d) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) memg a = aview trbsegs (w_H W) memg a) by reflexivity.
assert (PRL : forall a, apresent (w_H W) memg a -> apresent (w_H W) memg a) by (intros a Ha; exact Ha).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp gp_pc] in HSF.
gl_step A_round HSF HJ SHOKF KEEPL PRL U52 Rcidx Rp1 Hown Hpal1 Hpal2 W memg sp d pal cid pos.
pose proof HJ0 as (HAR0 & _). destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR0 Hinn) as (_ & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof asan_consts as (C1 & _).
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
assert (EV : forall j, (j < 54)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; lia).
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros j rr Hrr; subst E0; apply ew_Ereg_nat; exact Hrr).
lazymatch type of HSF with st_okF _ _ _ (restrict _ ?msF) =>
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GPB_STK (Z.of_nat d)) (sp - 80) memg (ms_mem msF)
HJ Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS; lia) ltac:(clear; lia) Hwhi KEEPL) as (KC1 & KC2 & KC3) end.
eapply (gl_call 0%nat n (gl1 n) ltac:(lia) _ _ _ regs0 f0 mem _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1 HSF eq_refl eq_refl HJ
(gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ HRO) Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 (KC3 HRA)).
- reflexivity.
- gl_den. rewrite (EV 2%nat ltac:(lia)), (ER 2%nat 2%bv eq_refl). exact G2.
- gl_den. rewrite (EV 8%nat ltac:(lia)), (ER 8%nat 8%bv eq_refl). exact G8.
- gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl). exact G9.
- gl_den. rewrite (EV 20%nat ltac:(lia)), (ER 20%nat 20%bv eq_refl). exact G20.
- gl_den. rewrite (EV 9%nat ltac:(lia)), (ER 9%nat 9%bv eq_refl), G9. unfold w64. rewrite unsigned_lit_small by (clear - Rn; lia). reflexivity.
- intros X. exfalso. clear - X. lia.
- gl_den. rewrite (EV 44%nat ltac:(lia)). subst E0. exact (gp_EN regs regs0 f0 c0 c1 n 1 pal 2%nat _ (gp_mean_nth c0 c1 n 1 0%nat Hlen ltac:(lia))).
- intros X. exfalso. clear - X. lia.
- intros r Hr. cbv [GP_UNTOUCHED In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]; gl_den;
[ rewrite (EV 3%nat ltac:(lia)), (ER 3%nat 3%bv eq_refl) | rewrite (EV 4%nat ltac:(lia)), (ER 4%nat 4%bv eq_refl)
| rewrite (EV 23%nat ltac:(lia)), (ER 23%nat 23%bv eq_refl) | rewrite (EV 24%nat ltac:(lia)), (ER 24%nat 24%bv eq_refl)
| rewrite (EV 25%nat ltac:(lia)), (ER 25%nat 25%bv eq_refl) | rewrite (EV 26%nat ltac:(lia)), (ER 26%nat 26%bv eq_refl)
| rewrite (EV 27%nat ltac:(lia)), (ER 27%nat 27%bv eq_refl) ]; apply Gkeep; cbv; tauto.
- exact (rg_obj_at_blk_kept (w_H W) (w_H W) memg _ (sp - 80) LAY_GPF _ 80 Ofr ltac:(vm_compute; reflexivity) KC2).
- exact Hinn.
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) memg _ (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)). exact (KC1 _ _ Hinn).
- exact Hlen.
- intros a Ha Hn1 Hn2. rewrite (KEEPL a Ha Hn1 Hn2). exact (KEEP a Ha Hn1 Hn2).
- intros a Ha. apply PRL. apply PR. exact Ha.
Qed.
Lemma gp_leaf : forall n, gp_R_stmt (TLeaf n).
Proof.
intros n fy regs0 f0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d sp
HJ Hh Hfull Hwf Hmok HRO Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G10 G18 G20 Gkeep Ofr Hblk Hat.
cbn [troot] in G9, G10. cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & c0 & c1 & Ond).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
assert (Hwfn : tnode_wf n) by (apply (proj1 (Forall_cons_iff _ _ _) Hwf)).
assert (Hmokn : tnode_means_ok n) by (apply (proj1 (Forall_cons_iff _ _ _) Hmok)).
exact (gl0 n fy regs0 f0 regs mem mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d c0 c1
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 (conj G10 G18) I Gkeep Ofr Hinn Ond Hlen
(fun _ _ _ _ => eq_refl) (fun _ H => H)).
Qed.
Lemma gp_root : forall m t, tree_full t -> tree_at trbsegs m t ->
exists n c0 c1 leafv, troot t = tn_addr n /\ In (tn_addr n, NODE_SIZE) (tree_blocks t) /\ length (tn_mean n) = 3%nat /\
obj_at trbsegs m (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) /\ (leafv = 0 \/ leafv = 1).
Proof.
intros m t Hf Hat. destruct t as [|n|n l r]; [destruct Hf | |]; cbn [tree_at troot tree_blocks] in *.
- destruct Hat as (_ & Hlen & c0 & c1 & Ho). exists n, c0, c1, 1. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. right. reflexivity.
- destruct Hat as (_ & Hlen & Ho & _ & _). exists n, (troot l), (troot r), 0. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. left. reflexivity.
Qed.
Definition gpn_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 42 (gp_lits 0)) ].
Lemma gpn_submem : submem gpn_mem (gp_mem 0).
Proof.
unfold gpn_mem, gp_mem. apply submem_drop. apply submem_keep; [|apply submem_nil].
split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [left; cbn; lia|]. intros c Hc; exact Hc.
Qed.
Local Ltac gp_keep1 HS ER msA regs r j :=
let X := fresh "X" in let Rk := fresh "Rk" in
assert (X : getr (ms_regs msA) (r : bv 5) = getr regs (r : bv 5));
[ rreg HS (r : bv 5) Rk; rewrite Rk; exact (ER j r eq_refl) | exact X ].
Local Ltac gp_keep_auto HS ER msA regs :=
lazymatch goal with |- getr (ms_regs msA) ?r = getr regs ?r =>
let j := eval vm_compute in (Z.to_nat (bv_unsigned r)) in gp_keep1 HS ER msA regs r j end.
Lemma gp_node : forall n l r, gp_P_stmt l -> gp_R_stmt r -> gp_R_stmt (TNode n l r).
Proof.
intros n l r HPl HRr fy regs0 f0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d sp
HJ Hh Hfull Hwf Hmok HRO Hra Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G10 G18 G20 Gkeep Ofr Hblk Hat.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof HJ as HJ0.
cbn [troot] in G9, G10. cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & Ond & Hatl & Hatr).
cbn [tree_full] in Hfull. destruct Hfull as [Hfl Hfr].
apply tree_forall_node in Hwf. destruct Hwf as (Hwfn & Hwfl & Hwfr).
apply tree_forall_node in Hmok. destruct Hmok as (Hmokn & Hmokl & Hmokr).
destruct d as [|d']; [cbn [tree_height] in Hh; lia|]. cbn [tree_height] in Hh.
assert (Hhl : (tree_height l <= d')%nat) by lia. assert (Hhr : (tree_height r <= Datatypes.S d')%nat) by lia.
assert (HGS : GPB_STK (Z.of_nat (Datatypes.S d')) = GPB_STK (Z.of_nat d') + 80) by (unfold GPB_STK, GP_STK; lia).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
assert (Hblkl : forall b, In b (tree_blocks l) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; left; exact Hb).
assert (Hblkr : forall b, In b (tree_blocks r) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; right; exact Hb).
destruct (gp_seed fy 0%nat regs0 f0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos (Datatypes.S d') n (troot l) (troot r) 0
HJ HRO Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 HRA G2 G8 G9 G20 (conj G10 G18) Ofr Hinn Ond Hlen) as [HS0 SHOK].
set (E := Ereg regs (gp_extra regs0 f0 (troot l) (troot r) n 0 pal)) in *.
pose proof (st_ok_submem trbsegs _ _ _ gpn_mem HS0 gpn_submem ltac:(vm_compute; reflexivity)) as HS.
cbn [ss_pc ss_regs ss_resv ss_facts ss_gp gp_pc gp_regs] in HS. clear HS0.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK gp_Bspan A_get_palette.
{ cbn [ss_mem]. unfold gpn_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msB := msx) in * end.
rename HFr into HFr1; rename HG into HG1; clear HF.
rreg HS (1%bv : bv 5) R1; rreg HS (2%bv : bv 5) R2; rreg HS (10%bv : bv 5) R10; rreg HS (11%bv : bv 5) R11.
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (gp_EN regs regs0 f0 (troot l) (troot r) n 0 pal 0%nat (troot l) eq_refl) as E42.
pose proof (gp_EN regs regs0 f0 (troot l) (troot r) n 0 pal 1%nat (troot r) eq_refl) as E43.
cbn [Nat.add] in E42, E43. fold E in E42, E43.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS0 : 96 <= GPB_STK (Z.of_nat d')) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
assert (Hspr : 0 <= sp - 80 /\ sp < 2 ^ 64) by (clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 HGS HGS0 Hstk0; lia).
assert (UspB : spZ (ms_regs msB) = sp - 80).
{ unfold spZ. rewrite R2, (ER 2%nat 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. clear - Hspr. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msB) a = aview trbsegs (w_H W) mem a).
{ intros a Ha. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem gpn_mem In] in Hin. destruct Hin as [<- | []].
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - 80) (sp - 80) mem (ms_mem msB)
HJ Hown Hpal1 Hpal2 ltac:(clear - Hwlo HGS HGS0; lia) ltac:(clear; lia) ltac:(clear; lia) Hwhi
ltac:(intros a Ha _ _; exact (KEEP1 a Ha))) as (KB1 & KB2 & KB3).
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msB HS eq_refl); cbn [ss_pc].
eapply SRr_bind.
{ eapply (HPl fy (ms_regs msB) (ms_mem msB) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d' HJ Hhl Hfl Hwfl Hmokl
(gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ HRO)).
- rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
- unfold raZ. rewrite R1. rewrite unsigned_lit_small by (clear; lia). clear; lia.
- rewrite R10, E42. reflexivity.
- rewrite R11, (ER 8%nat 8%bv eq_refl). exact G8.
- rewrite UspB. clear - Hal16. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
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
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat (Datatypes.S d')) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem a).
{ intros a Ha Hnw Hnp. rewrite (Hkeep2 a Ha ltac:(clear - Hnw HGS; lia) Hnp). exact (KEEP1 a Ha). }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GPB_STK (Z.of_nat (Datatypes.S d'))) (sp - 80) mem mem2
HJ2 Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS HGS0; lia) ltac:(clear; lia) Hwhi KEEP2) as (KC1 & KC2 & KC3).
pose proof (gp_pres_in _ _ Hpr) as PR.
rreg HS (8%bv : bv 5) R8; rreg HS (9%bv : bv 5) R9; rreg HS (18%bv : bv 5) R18; rreg HS (20%bv : bv 5) R20.
assert (G2c : getr regs2 2 = w64 (sp - 80)).
{ rewrite (PR (2%bv : bv 5) ltac:(cbv; tauto)), R2, (ER 2%nat 2%bv eq_refl). exact G2. }
assert (G8c : getr regs2 8 = w64 pal) by (rewrite (PR (8%bv : bv 5) ltac:(cbv; tauto)), R8, (ER 8%nat 8%bv eq_refl); exact G8).
assert (G9c : getr regs2 9 = w64 (tn_addr n)) by (rewrite (PR (9%bv : bv 5) ltac:(cbv; tauto)), R9, (ER 9%nat 9%bv eq_refl); exact G9).
assert (G18c : getr regs2 18 = w64 2) by (rewrite (PR (18%bv : bv 5) ltac:(cbv; tauto)), R18; reflexivity).
assert (G20c : getr regs2 20 = w64 SB) by (rewrite (PR (20%bv : bv 5) ltac:(cbv; tauto)), R20, (ER 20%nat 20%bv eq_refl); exact G20).
assert (Ofr2 : obj_at trbsegs (mrestrict (w_H W) mem2) (sp - 80) LAY_GPF (gpf_vals regs0 f0))
by (apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 (sp - 80) LAY_GPF _ 80 Ofr ltac:(vm_compute; reflexivity) KC2)).
assert (Ond2 : obj_at trbsegs (mrestrict (w_H W) mem2) (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0))
by (apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)); exact (KC1 _ _ Hinn)).
assert (Hatr2 : tree_at trbsegs (mrestrict (w_H W) mem2) r)
by (apply (rg_tree_at_kept (w_H W) (w_H W) mem mem2 r Hatr); intros b sz Hb; apply KC1; exact (Hblkr _ Hb)).
assert (HRO2 : arodata_ok B (aview trbsegs (w_H W) mem2)) by (exact (gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ2 HRO)).
destruct (gp_seed fx' 4%nat regs0 f0 regs2 mem2 md2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos (Datatypes.S d') n (troot l) (troot r) 0
HJ2 HRO2 Hal16 Hwlo Hwhi Hown Hcid Hpal1 Hpal2 (KC3 HRA) G2c G8c G9c G20c G18c Ofr2 Hinn Ond2 Hlen) as [HSc0 SHOKc].
set (Ec := Ereg regs2 (gp_extra regs0 f0 (troot l) (troot r) n 0 pal)) in *.
pose proof (st_ok_submem trbsegs _ _ _ gpn_mem HSc0 gpn_submem ltac:(vm_compute; reflexivity)) as HSc1.
cbn [ss_pc ss_regs ss_resv ss_facts ss_gp gp_pc gp_regs] in HSc1. clear HSc0.
destruct (gp_root _ r Hfr Hatr2) as (nr & cr0 & cr1 & lvr & Hrootr & Hinbr & Hlenr & Ondr & Hlvr).
assert (Hinnr : In (tn_addr nr, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblkr; exact Hinbr).
pose proof (proj1 HJ2) as HAR2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr nr) NODE_SIZE HAR2 Hinnr) as (Hr16 & Hr4096 & Hrceil & _). change (req_size NODE_SIZE) with 56 in Hrceil.
pose proof (gp_EN regs2 regs0 f0 (troot l) (troot r) n 0 pal 1%nat (troot r) eq_refl) as E43c. cbn [Nat.add] in E43c. fold Ec in E43c. rewrite Hrootr in E43c.
assert (U43 : bv_unsigned (ew Ec 43) = tn_addr nr) by (rewrite E43c; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia).
assert (E20c : ew Ec 20 = w64 SB) by (subst Ec; rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact G20c).
pose proof (st_ok_add_fact trbsegs Ec _ _ 43%nat (mkAF 4096 140737479966720 4) HSc1
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U43; change (2 ^ 4) with 16; clear - Hr16 Hr4096 Hrceil C1; lia)) as HSc.
clear HSc1.
assert (SHOKc' : sh_ok trbsegs gp_Bx (mkSHE 43 0 NODE_SIZE :: gp_SH) Ec (mrestrict (w_H W) mem2)).
{ constructor; [|exact SHOKc].
apply (shent_ok_of_block trbsegs B LAWS lyc Sc W mem2 md2 Ec gp_Bx 43 (tn_addr nr) NODE_SIZE 0 NODE_SIZE HAR2 Hinnr).
- unfold U, gp_Bx. cbn [sv_denot]. rewrite E20c, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U43.
- lia.
- change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia. }
assert (KBreg : forall rr : bv 5, In rr GP_UNTOUCHED -> getr (ms_regs msB) rr = getr regs rr).
{ intros rr Hin. unfold GP_UNTOUCHED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); try contradiction; gp_keep_auto HS ER msB regs. }
clear SHOKc HS HFr1.
aj_run_to_tok trbtbl_lib_ok HSc HJ2 SHOKc' gp_Bspan GP_TEST.
{ cbn [ss_mem add_atom]. unfold gpn_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msD := msx) in * end.
rename HFr into HFr3; clear HF.
rreg HSc (2%bv : bv 5) Q2; rreg HSc (8%bv : bv 5) Q8; rreg HSc (9%bv : bv 5) Q9; rreg HSc (10%bv : bv 5) Q10; rreg HSc (18%bv : bv 5) Q18; rreg HSc (20%bv : bv 5) Q20.
assert (ERc : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew Ec j = getr regs2 rr) by (intros; subst Ec; apply ew_Ereg_nat; assumption).
assert (KDreg : forall rr : bv 5, In rr GP_UNTOUCHED -> getr (ms_regs msD) rr = getr regs2 rr).
{ intros rr Hin. unfold GP_UNTOUCHED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); try contradiction; gp_keep_auto HSc ERc msD regs2. }
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msD) a = aview trbsegs (w_H W) mem2 a).
{ intros a Ha. apply aview_eq_of. apply HFr3. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem add_atom gpn_mem In] in Hin. destruct Hin as [<- | []].
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
assert (KEEPd : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB_STK (Z.of_nat (Datatypes.S d')) <= a < sp - 80) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) (ms_mem msD) a = aview trbsegs (w_H W) mem a).
{ intros a Ha Hnw Hnp. rewrite (KEEP3 a Ha). exact (KEEP2 a Ha Hnw Hnp). }
destruct (gp_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k pal cid pos sp (sp - GPB_STK (Z.of_nat (Datatypes.S d'))) (sp - 80) mem (ms_mem msD)
HJ2 Hown Hpal1 Hpal2 Hwlo ltac:(clear - HGS HGS0; lia) ltac:(clear; lia) Hwhi KEEPd) as (KD1 & KD2 & KD3).
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msD HSc eq_refl); cbn [ss_pc].
eapply SRr_mono.
{ eapply (HRr fx' regs0 f0 (ms_regs msD) (ms_mem msD) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos (Datatypes.S d')
HJ2 Hhr Hfr Hwfr Hmokr (gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ2 HRO) Hra Hal16 Hwlo Hwhi Hfz Hown Hcid Hpal1 Hpal2 (KD3 HRA)).
- rewrite Q2, (ERc 2%nat 2%bv eq_refl). exact G2c.
- rewrite Q8, (ERc 8%nat 8%bv eq_refl). exact G8c.
- rewrite Q9, E43c, Hrootr. reflexivity.
- rewrite Q10, U43, Hrootr. reflexivity.
- rewrite Q18. reflexivity.
- rewrite Q20. exact E20c.
- intros rr Hin. rewrite (KDreg rr Hin), (PR rr ltac:(cbv [GP_UNTOUCHED In] in Hin; cbv [CALLEE_SAVED In]; intuition)), (KBreg rr Hin). exact (Gkeep rr Hin).
- exact (rg_obj_at_blk_kept (w_H W) (w_H W) mem (ms_mem msD) (sp - 80) LAY_GPF _ 80 Ofr ltac:(vm_compute; reflexivity) KD2).
- exact Hblkr.
- apply (rg_tree_at_kept (w_H W) (w_H W) mem (ms_mem msD) r Hatr). intros b sz Hb. apply KD1. exact (Hblkr _ Hb). }
intros W' c' _ (HW & fx2 & regs3 & mem3 & md3 & Hc & Hfz3 & HJ3 & Hpr3 & Hkeep3 & Hpres3).
split; [exact HW|]. exists fx2, regs3, mem3, md3.
split; [exact Hc|]. split; [exact Hfz3|]. split; [exact HJ3|]. split; [exact Hpr3|]. split.
- intros a Ha Hnw Hnp. rewrite (Hkeep3 a Ha Hnw Hnp). exact (KEEPd a Ha Hnw Hnp).
- intros a Ha. apply Hpres3. apply (apresent_grows _ _ _ _ HG). apply Hpres2. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Definition gpe_mem : smem := [ stack_region 80; got_region; bcell_region 35 ].
Definition gpe_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_gpe : sstate := mkSS A_get_palette sr_atoms gpe_mem None gpe_facts.
Definition gpe_Bx : sv := SOff 35 0.
Definition gpe_SH : list shent := [ mkSHE 10 0 NODE_SIZE ].
Definition gpe_extra : list word := map (Z_to_bv 64) [0; 0; 0; SB].
Lemma gp_seed_entry : forall (fy : FPState) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (d : nat) (node : Z),
let E := Ereg regs gpe_extra in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - GPB_STK (Z.of_nat d) -> spZ regs <= sp0 ->
getr regs 10 = w64 node ->
In (node, NODE_SIZE) (ablocks B lyc Sc) ->
@st_ok trbsegs fy E ss_gpe (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 A_get_palette) memc (seg_rom trbsegs)))
/\ sh_ok trbsegs gpe_Bx gpe_SH E (mrestrict (w_H W) memc).
Proof.
intros fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k d node E HJ Hal16 Hwlo Hwhi G10 Hinn.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ node NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & _ & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ node NODE_SIZE HAR Hinn) as Hnh_img.
change (req_size NODE_SIZE) with 56 in *.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 node) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = node) by (rewrite E10; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
split.
- unfold ss_gpe. apply (entry_st_ok_full trbsegs).
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold gpe_mem, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite Usp.
split; [clear - Hwlo Hwhi Hslo Hceil C1 HGS Hstk0; lia|]. split; [clear - Hwhi Hshi H47; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. clear - Ho Hwlo Hwhi HGS. lia.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa3250) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xa3250 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kgot).
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xab278) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xab278 8 gpe_Bx SB);
[cbn [sv_denot gpe_Bx]; fold E; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold gpe_mem, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite Usp. unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 Hstk0 HGS. clear. unfold ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gpe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite Usp, U10, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 C1 C3 Hstk0 HGS Hnceil Hn4096 Hn16 Hnh Hnh_img. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gpe_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS lyc Sc W memc mdc E gpe_Bx 10 node NODE_SIZE 0 NODE_SIZE HAR Hinn).
* unfold U, gpe_Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
* lia.
* change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
Qed.
Lemma gp_P_of_R : forall t, gp_R_stmt t -> gp_P_stmt t.
Proof.
intros t HR fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d
HJ Hh Hfull Hwf Hmok HRO Hra Hra4 G10 G11 Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA Hblk Hat.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof HJ as HJ0.
destruct (gp_root _ t Hfull Hat) as (n & c0 & c1 & leafv & Hroot & Hinb & Hlen & Ond & Hlv).
rewrite Hroot in G10.
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; exact Hinb).
destruct (gp_seed_entry fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k d (tn_addr n) HJ Hal16 Hwlo Hwhi G10 Hinn) as [HS SHOK].
set (E0 := Ereg regs gpe_extra) in *.
pose proof (st_ok_enterF trbsegs fy 36 E0 _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF.
pose proof (sh_ok_agree trbsegs gpe_Bx gpe_SH 36 E0 (ew_fregs E0 36 (@fp_regs fy)) _ (env_agree_ew_fregs E0 36 _) ltac:(vm_compute; reflexivity) SHOK) as SHOKF.
clear HS SHOK. set (E := ew_fregs E0 36 (@fp_regs fy)) in *.
assert (EV : forall j, (j < 36)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; lia).
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HEf : forall r : bv 5, ew E (36 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (rewrite (EV 35%nat ltac:(lia)); subst E0; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EV 2%nat ltac:(lia)), (ER 2%nat 2%bv eq_refl); reflexivity).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGS : 96 <= GPB_STK (Z.of_nat d)) by (unfold GPB_STK, GP_STK, TROUND_STK; lia).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gpe] in HSF.
aj_run_to_tokF trbtbl_lib_ok HSF HJ SHOKF gp_Bspan GP_TEST.
{ cbn [ss_mem gpe_mem]. eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite Usp; clear; lia | cbn; clear - Hwlo HGS; lia | cbn; clear - Hwhi; lia | awr_ok_tac]. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
rename HFr into HFr1; clear HF.
pose proof (st_okF_frm trbsegs _ _ _ HSF) as HfrmA.
pose proof (st_okF_to_legacy trbsegs _ _ _ HSF) as HSL.
rreg HSL (2%bv : bv 5) R2; rreg HSL (8%bv : bv 5) R8; rreg HSL (9%bv : bv 5) R9; rreg HSL (10%bv : bv 5) R10; rreg HSL (18%bv : bv 5) R18; rreg HSL (20%bv : bv 5) R20.
destruct (gp_pal_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal cid pos HJ Hown Hpal1 Hpal2) as [Rp1 Rp2].
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & _); change (req_size NODE_SIZE) with 56 in Hnceil.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) memc a).
{ intros a Ha Hnw. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_gpe gpe_mem] in Hin. unfold stack_region, got_region, bcell_region in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; unfold stack_region, got_region, bcell_region in Hr;
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; try rewrite Usp in Hr; clear - Hr Hnw; lia. }
assert (Ofr : obj_at trbsegs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 80) LAY_GPF (gpf_vals regs (@fp_regs fy))).
{ lazymatch type of HSL with st_ok _ ?Ex ?ssx _ =>
let rs := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx _ 0%nat rs HSL ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ?ew_ewset_other by (cbv; lia); exact Usp);
assert (SL : forall od (rr : bv 5) j, Z.of_nat j = bv_unsigned rr -> (j < 32)%nat ->
In (YQ0b.mkChunk od (CVal 8 (SOff j 0))) (YQ0b.r_chunks rs) ->
val_mem trbsegs (mrestrict (w_H W) (ms_mem msA)) (spZ regs + od) 8 (bv_unsigned (getr regs rr)));
[ intros od rr j Hj Hj32 Hin;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (slot_of_region Ex _ (spZ regs) cs lo hi wlo whi od (SOff j 0) _ HRstk UspX Hin);
[ cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite (EV j ltac:(lia)), (ER j rr Hj), Z.add_0_r; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs rr)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq ] end
| ];
assert (SLF : forall od (fr : bv 5) j, j = (36 + ridx fr)%nat -> (j < 68)%nat ->
In (YQ0b.mkChunk od (CVal 8 (SOff j 0))) (YQ0b.r_chunks rs) ->
val_mem trbsegs (mrestrict (w_H W) (ms_mem msA)) (spZ regs + od) 8 (bv_unsigned (reg_get (@fp_regs fy) fr)));
[ intros od fr j Hj Hj86 Hin;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (slot_of_region Ex _ (spZ regs) cs lo hi wlo whi od (SOff j 0) _ HRstk UspX Hin);
[ cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite Hj, (HEf fr), Z.add_0_r; reflexivity
| pose proof (bv_unsigned_in_range 64 (reg_get (@fp_regs fy) fr)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq ] end
| ] end.
cbn [obj_at LAY_GPF gpf_vals]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
repeat split; try apply u64_range8;
[ replace (spZ regs - 80 + 0) with (spZ regs + -80) by lia; apply (SLF (-80) 9%bv 45%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 8) with (spZ regs + -72) by lia; apply (SLF (-72) 8%bv 44%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 16) with (spZ regs + -64) by lia; apply (SL (-64) 22%bv 22%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 24) with (spZ regs + -56) by lia; apply (SL (-56) 21%bv 21%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 32) with (spZ regs + -48) by lia; apply (SL (-48) 20%bv 20%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 40) with (spZ regs + -40) by lia; apply (SL (-40) 19%bv 19%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 48) with (spZ regs + -32) by lia; apply (SL (-32) 18%bv 18%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 56) with (spZ regs + -24) by lia; apply (SL (-24) 9%bv 9%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 64) with (spZ regs + -16) by lia; apply (SL (-16) 8%bv 8%nat eq_refl ltac:(lia)); cbn; tauto
| replace (spZ regs - 80 + 72) with (spZ regs + -8) by lia; apply (SL (-8) 1%bv 1%nat eq_refl ltac:(lia)); cbn; tauto ]. }
assert (Hat1 : tree_at trbsegs (mrestrict (w_H W) (ms_mem msA)) t).
{ apply (rg_tree_at_kept (w_H W) (w_H W) memc (ms_mem msA) t Hat). intros b sz Hb i Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Hblk _ Hb)) as (_ & Hb4096 & Hbceil & _).
apply KEEP; [clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Hwlo Hwhi Hslo Hceil HGS Hstk0; lia]. }
assert (HRA1 : range_addressable (aview trbsegs (w_H W) (ms_mem msA)) SHADOW_OFF pal 768).
{ eapply range_addressable_agree; [|exact HRA]. intros x Hx.
assert (Hx8 : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
apply KEEP; unfold shadow_of_addr, SHADOW_OFF;
[ clear - Hx8; lia | clear - Hx8 Hwlo Hwhi Hslo Hceil HGS Hstk0 C1; lia ]. }
assert (KAreg : forall rr : bv 5, In rr GP_UNTOUCHED -> getr (ms_regs msA) rr = getr regs rr).
{ intros rr Hin. unfold GP_UNTOUCHED in Hin. cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]); try contradiction;
lazymatch goal with |- getr (ms_regs msA) ?r = getr regs ?r =>
let j := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
let Rk := fresh "Rk" in rreg HSL (r : bv 5) Rk; rewrite Rk; rewrite (EV j ltac:(lia)); exact (ER j r eq_refl) end. }
rewrite (@st_ok_restrict_mkst trbsegs (fp_of (restrict (w_H W) msA)) (w_H W) _ _ msA HSL eq_refl); cbn [ss_pc].
eapply SRr_mono.
{ eapply (HR (fp_of (restrict (w_H W) msA)) regs (@fp_regs fy) (ms_regs msA) (ms_mem msA) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d
HJ Hh Hfull Hwf Hmok (gp_rodata_j2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJ HRO) Hra Hal16 Hwlo Hwhi HfrmA Hown Hcid Hpal1 Hpal2 HRA1).
- rewrite R2, Usp. unfold w64. first [reflexivity | f_equal; lia].
- rewrite R8, (EV 11%nat ltac:(lia)), (ER 11%nat 11%bv eq_refl). exact G11.
- rewrite R9, (EV 10%nat ltac:(lia)), (ER 10%nat 10%bv eq_refl), Hroot. exact G10.
- rewrite R10, (EV 10%nat ltac:(lia)), (ER 10%nat 10%bv eq_refl), G10, Hroot. unfold w64. rewrite unsigned_lit_small by (clear - Hn4096 Hnceil C1; lia). reflexivity.
- rewrite R18. reflexivity.
- rewrite R20. exact E35.
- exact KAreg.
- exact Ofr.
- exact Hblk.
- exact Hat1. }
intros W' c' _ (HW & fx' & regs2 & mem2 & md2 & Hc & Hfz & HJ2 & Hpr & Hkeep2 & Hpres2).
split; [exact HW|]. exists fx', regs2, mem2, md2.
split; [exact Hc|]. split; [exact Hfz|]. split; [exact HJ2|]. split; [exact Hpr|]. split.
- intros a Ha Hnw Hnpal. rewrite (Hkeep2 a Ha ltac:(clear - Hnw; lia) Hnpal). apply KEEP; [exact Ha | clear - Hnw HGS; lia].
- intros a Ha. apply Hpres2. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
Lemma gp_R_all : forall u, gp_R_stmt u.
Proof.
induction u as [|n|n l IHl r IHr].
- intros fy regs0 f0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d sp HJ Hh Hfull. destruct Hfull.
- apply gp_leaf.
- apply gp_node; [apply gp_P_of_R; exact IHl | exact IHr].
Qed.
Theorem trb_get_palette : forall {fx : FPState}, tgetpal_specB B.
Proof.
intros fx d STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t pal cid pos
HJ Hh Hfull Hwf Hmok HRO Hra Hra4 G10 G11 Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA Hblk Hat.
exact (gp_P_of_R t (gp_R_all t) fx regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pal cid pos d
HJ Hh Hfull Hwf Hmok HRO Hra Hra4 G10 G11 Hal16 Hwlo Hwhi Hfrm Hown Hcid Hpal1 Hpal2 HRA Hblk Hat).
Qed.
End GP.
