(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i YI0x UI1h YI08 YI0c YI0f UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YM06 YCip UIZ9.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition gp_pc (g : nat) : Z :=
match g with
| 0%nat => ubs2_A_get_palette_from_decision_tree + 56
| 1%nat => ubs2_A_get_palette_from_decision_tree + 108
| 2%nat => ubs2_A_get_palette_from_decision_tree + 192
| 3%nat => ubs2_A_get_palette_from_decision_tree + 252
| _ => ubs2_A_get_palette_from_decision_tree + 80
end.
Definition GPB (h : Z) : Z := 64 * (h + 1) + 16.
Definition LAY_GPF : layout_t := [(8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 8%N); (48, 8%N); (56, 8%N)].
Definition gpf_vals (regs0 f0 : bvmap 5 word) : list Z :=
[bv_unsigned (reg_get f0 9); bv_unsigned (reg_get f0 8); bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1)].
Definition GP_UNTOUCHED : list reg := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition fregs_kept89 (f0 f : bvmap 5 word) : Prop :=
forall r, In r FCALLEE_SAVED -> r <> 8%bv -> r <> 9%bv -> reg_get f r = reg_get f0 r.
Definition gp_pin_facts (g : nat) (regs regs0 : bvmap 5 word) (node pal : Z) : Prop :=
match g with
| 2%nat | 3%nat => getr regs 18 = Z_to_bv 64 (2 ^ 64 - 1 - pal) /\ getr regs 19 = Z_to_bv 64 (node + 16)
| _ => getr regs 18 = Z_to_bv 64 2 /\ getr regs 19 = getr regs0 19
end.
Definition gl_fp_facts (g : nat) (fy : FPState) (n : tnode) : Prop :=
match g with
| 0%nat => True
| 1%nat => reg_get (@fp_regs fy) 10 = round_bits (Z_to_bv 64 (nth 0 (tn_mean n) 0))
| Datatypes.S g' => reg_get (@fp_regs fy) 10 = round_bits (Z_to_bv 64 (nth g' (tn_mean n) 0)) /\
reg_get (@fp_regs fy) 8 = Z_to_bv 64 Cm1 /\ reg_get (@fp_regs fy) 9 = Z_to_bv 64 C256
end.
Definition gp_lits (leafv : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some leafv].
Definition gp_3cidx : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 47 0) (SLit 1)) (SOff 47 0).
Definition gp_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 8 0) gp_3cidx, SOff 49 0); (SAlu ALU_XOR (SOff 8 0) (SLit (-1)), SOff 50 0) ].
Definition gp_mem (leafv : Z) : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (obj_chunks_from LAY_GPF 32);
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 39 (gp_lits leafv));
YQ0b.mkRegion (Some 49%nat) 0 3 0 3 [];
ro_region ].
Definition gp_facts (g : nat) : facts :=
mkFacts ((match g with 4%nat => [(40%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4)] | _ => [] end) ++
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4);
(47%nat, mkAF 0 255 0); (49%nat, mkAF CEIL_MIN (2^63) 0); (50%nat, mkAF (2^63) (2^64 - 1 - CEIL_MIN) 0) ])
[] gp_alias.
Definition gp_regs (g : nat) : list sv :=
match g with
| 2%nat | 3%nat => sr_set (sr_set sr_atoms 18%bv (SOff 50 0)) 19%bv (SOff 9 16)
| _ => sr_set sr_atoms 18%bv (SLit 2)
end.
Definition ss_gp (g : nat) (leafv : Z) : sstate := mkSS (gp_pc g) (gp_regs g) (gp_mem leafv) None (gp_facts g).
Definition gp_extra (regs0 f0 : bvmap 5 word) (c0 c1 : Z) (n : tnode) (leafv pal : Z) : list word :=
map (Z_to_bv 64) (gpf_vals regs0 f0 ++ node_vals c0 c1 n leafv) ++
[Z_to_bv 64 (pal + 3 * tn_cidx n); Z_to_bv 64 (2 ^ 64 - 1 - pal)].
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Lemma gp_len17 : forall regs0 f0 c0 c1 n leafv, length (tn_mean n) = 3%nat ->
length (map (Z_to_bv 64) (gpf_vals regs0 f0 ++ node_vals c0 c1 n leafv)) = 17%nat.
Proof. intros regs0 f0 c0 c1 n leafv Hlen. rewrite length_map, length_app. unfold node_vals. rewrite !length_app, Hlen. reflexivity. Qed.
Lemma gp_E49 : forall regs regs0 f0 c0 c1 n leafv pal, length (tn_mean n) = 3%nat ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) 49 = Z_to_bv 64 (pal + 3 * tn_cidx n).
Proof.
intros regs regs0 f0 c0 c1 n leafv pal Hlen. unfold gp_extra. change 49%nat with (32 + 17)%nat. rewrite ew_Ereg_extra.
pose proof (gp_len17 regs0 f0 c0 c1 n leafv Hlen) as HL.
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. reflexivity.
Qed.
Lemma gp_E50 : forall regs regs0 f0 c0 c1 n leafv pal, length (tn_mean n) = 3%nat ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) 50 = Z_to_bv 64 (2 ^ 64 - 1 - pal).
Proof.
intros regs regs0 f0 c0 c1 n leafv pal Hlen. unfold gp_extra. change 50%nat with (32 + 18)%nat. rewrite ew_Ereg_extra.
pose proof (gp_len17 regs0 f0 c0 c1 n leafv Hlen) as HL.
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. reflexivity.
Qed.
Lemma gp_EF : forall regs regs0 f0 c0 c1 n leafv pal j v, nth_error (gpf_vals regs0 f0) j = Some v ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) (32 + j) = Z_to_bv 64 v.
Proof. intros regs regs0 f0 c0 c1 n leafv pal j v Hj. unfold gp_extra. rewrite map_app, <- app_assoc. apply Ereg_vals. exact Hj. Qed.
Lemma gp_EN : forall regs regs0 f0 c0 c1 n leafv pal j v, nth_error (node_vals c0 c1 n leafv) j = Some v ->
ew (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) (39 + j) = Z_to_bv 64 v.
Proof.
intros regs regs0 f0 c0 c1 n leafv pal j v Hj. unfold gp_extra. change (39 + j)%nat with (32 + (7 + j))%nat. rewrite ew_Ereg_extra.
assert (Hl : (j < length (node_vals c0 c1 n leafv))%nat) by (apply nth_error_Some; congruence).
rewrite app_nth1 by (rewrite length_map, length_app; cbn [gpf_vals length]; lia).
rewrite map_app, app_nth2 by (rewrite length_map; cbn [gpf_vals length]; lia).
rewrite length_map. cbn [gpf_vals length]. replace (7 + j - 7)%nat with j by lia.
apply nth_error_nth. apply map_nth_error. exact Hj.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Definition gp_postR (regs0 f0 : bvmap 5 word) STK sp0 FP L A mem0 md0 Lc Ac md (mem : word -> option byte)
(lo hi pal : Z) : config -> Prop :=
fun c' => exists (fx' : FPState) regs2 mem2,
c' = mkCfg (@mkst fx' regs2 (getr regs0 1) mem2 rom) md /\ frm_zero (@fp_csr fx') /\
fregs_preserved f0 (@fp_regs fx') /\
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem2 md /\
regs_preserved regs0 regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (pal <= a < pal + 768) -> mbyte segs mem2 a = mbyte segs mem a).
Definition gp_R_stmt (u : tree) : Prop :=
forall (fy : FPState) (regs0 f0 regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (pal : Z),
let sp := spZ regs0 in
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md -> ubs2_rgb_rodata_ok mem ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 ->
sp0 - STK <= sp - GPB (theight u) -> sp <= pal -> pal + 768 <= sp0 ->
frm_zero (@fp_csr fy) -> fregs_kept89 f0 (@fp_regs fy) ->
getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 8 = Z_to_bv 64 pal -> getr regs 9 = Z_to_bv 64 (troot u) ->
getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = getr regs0 19 ->
(forall r : reg, In r GP_UNTOUCHED -> getr regs r = getr regs0 r) ->
obj_at segs mem (sp - 64) LAY_GPF (gpf_vals regs0 f0) ->
tree_at segs mem u -> tree_full u -> tree_forall tnode_wf u -> tree_forall tnode_means_ok u ->
(forall b, In b (tree_blocks u) -> In b (blocks Lc Ac)) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 (gp_pc 0)) mem rom) md)
(gp_postR regs0 f0 STK sp0 FP L A mem0 md0 Lc Ac md mem (sp - GPB (theight u)) (sp - 64) pal).
Definition gp_P_stmt (t : tree) : Prop :=
forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (pal : Z),
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md -> ubs2_rgb_rodata_ok mem ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - GPB (theight t) -> spZ regs <= pal -> pal + 768 <= sp0 ->
frm_zero (@fp_csr fy) ->
getr regs 10 = Z_to_bv 64 (troot t) -> getr regs 11 = Z_to_bv 64 pal ->
tree_at segs mem t -> tree_full t -> tree_forall tnode_wf t -> tree_forall tnode_means_ok t ->
(forall b, In b (tree_blocks t) -> In b (blocks Lc Ac)) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 ubs2_A_get_palette_from_decision_tree) mem rom) md)
(gp_postR regs (@fp_regs fy) STK sp0 FP L A mem0 md0 Lc Ac md mem (spZ regs - GPB (theight t)) (spZ regs) pal).
Definition gl_stmt (g : nat) (n : tnode) : Prop :=
forall (fy : FPState) (regs0 f0 regs : bvmap 5 word) mem memg STK sp0 FP L A mem0 md0 Lc Ac md (pal c0 c1 : Z),
let sp := spZ regs0 in
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac memg md -> ubs2_rgb_rodata_ok memg ->
tnode_wf n -> tnode_means_ok n ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - 80 -> sp <= pal -> pal + 768 <= sp0 ->
frm_zero (@fp_csr fy) -> fregs_kept89 f0 (@fp_regs fy) -> gl_fp_facts g fy n ->
getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 8 = Z_to_bv 64 pal -> getr regs 9 = Z_to_bv 64 (tn_addr n) ->
gp_pin_facts g regs regs0 (tn_addr n) pal ->
(forall r : reg, In r GP_UNTOUCHED -> getr regs r = getr regs0 r) ->
obj_at segs memg (sp - 64) LAY_GPF (gpf_vals regs0 f0) ->
In (tn_addr n, NODE_SIZE) (blocks Lc Ac) ->
obj_at segs memg (tn_addr n) LAY_Node (node_vals c0 c1 n 1) -> length (tn_mean n) = 3%nat ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
mbyte segs memg a = mbyte segs mem a) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 (gp_pc g)) memg rom) md)
(gp_postR regs0 f0 STK sp0 FP L A mem0 md0 Lc Ac md mem (sp - 80) (sp - 64) pal).
Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma node_facts : forall Lc Ac memc mdc u (n : tnode),
heap_ok MR Lc Ac memc mdc ->
(forall b, In b (tree_blocks u) -> In b (blocks Lc Ac)) -> In n (tree_nodes u) ->
4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Proof.
intros Lc Ac memc mdc u n HH Hbl Hin.
apply (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc); [exact HH | | unfold NODE_SIZE; lia].
apply Hbl. apply tree_blocks_in_nodes. exists n. auto.
Qed.


Lemma seed_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_dec k 64).
- replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.
Lemma seed_ro_in_img : forall a, SRC2_RO_LO <= a < SRC2_RO_HI -> in_img ubs2_msyms a.
Proof.
intros a Ha. split; [vm_compute; discriminate|].
exists (nth 0 (segments_reserved (ms_segs ubs2_msyms)) (Z_to_bv 64 0, Z_to_bv 64 0)). split; [apply nth_In; vm_compute; lia|].
match goal with |- ?lo <= a < ?hi => let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) end.
unfold SRC2_RO_LO, SRC2_RO_HI in Ha. lia.
Qed.
Lemma seed_blk_off_ro : forall Lc Ac memc mdc b sz,
heap_ok MR Lc Ac memc mdc -> In (b, sz) (blocks Lc Ac) -> 0 < sz -> b + sz <= SRC2_RO_LO \/ SRC2_RO_HI <= b.
Proof.
intros Lc Ac memc mdc b sz HH Hin Hsz. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
destruct (Z_lt_le_dec SRC2_RO_LO (b + sz)) as [H1|H1]; [|left; lia].
destruct (Z_lt_le_dec b SRC2_RO_HI) as [H2|H2]; [|right; lia].
exfalso. apply blocks_In in Hin as (p & Hp & Hpin).
apply (il_blocks IMG Lc Ac memc mdc p sz (Z.max b SRC2_RO_LO - b) (proj1 HH) Hpin ltac:(lia)).
rewrite Hp. apply seed_ro_in_img. lia.
Qed.
Lemma gp_seed : forall (fy : FPState) (g : nat) (regs0 f0 regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(pal : Z) (n : tnode) (c0 c1 leafv : Z),
let sp := spZ regs0 in
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md -> ubs2_rgb_rodata_ok mem ->
sp mod 16 = 0 -> sp0 - STK <= sp - 64 -> sp <= pal -> pal + 768 <= sp0 ->
getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 8 = Z_to_bv 64 pal -> getr regs 9 = Z_to_bv 64 (tn_addr n) ->
gp_pin_facts g regs regs0 (tn_addr n) pal ->
obj_at segs mem (sp - 64) LAY_GPF (gpf_vals regs0 f0) ->
In (tn_addr n, NODE_SIZE) (blocks Lc Ac) ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
(g = 4%nat -> 4096 <= c1 /\ c1 + NODE_SIZE <= alloc_ceiling /\ c1 mod 16 = 0) ->
@st_ok segs fy (Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)) (ss_gp g leafv) (@mkst fy regs (Z_to_bv 64 (gp_pc g)) mem rom).
Proof.
intros fy g regs0 f0 regs mem STK sp0 FP L A mem0 md0 Lc Ac md pal n c0 c1 leafv sp
  HJ HRO Hal16 Hwlo Hpal Hpalhi G2 G8 G9 Gpin Ofr Hinn Ond Hlen Hc1.
pose proof HJ as (HH & _ & _ & _ & _ & (Hsal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNSv : NODE_SIZE = 56) by reflexivity.
pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md (tn_addr n) NODE_SIZE HH Hinn ltac:(unfold NODE_SIZE; lia)) as (Hn4096 & Hnceil & Hn16).
pose proof (seed_blk_off_ro Lc Ac mem md (tn_addr n) NODE_SIZE HH Hinn ltac:(unfold NODE_SIZE; lia)) as Hnro.
assert (Hnv8 : nth_error (node_vals c0 c1 n leafv) 8 = Some (tn_cidx n)).
{ rewrite (node_vals_expand c0 c1 n leafv Hlen). reflexivity. }
pose proof (obj_at_nth segs _ _ _ _ 8%nat (49, 1%N) (tn_cidx n) Ond eq_refl Hnv8) as [_ Rcidx].
cbn [snd Z.of_N] in Rcidx. change (2 ^ (8 * 1)) with 256 in Rcidx.
set (E := Ereg regs (gp_extra regs0 f0 c0 c1 n leafv pal)).
assert (HE : forall j (rr : reg), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVF : forall j v, nth_error (gpf_vals regs0 f0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply gp_EF; exact Hj).
assert (HVN : forall j v, nth_error (node_vals c0 c1 n leafv) j = Some v -> ew E (39 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply gp_EN; exact Hj).
assert (E49 : ew E 49 = Z_to_bv 64 (pal + 3 * tn_cidx n)) by (subst E; apply gp_E49; exact Hlen).
assert (E50 : ew E 50 = Z_to_bv 64 (2 ^ 64 - 1 - pal)) by (subst E; apply gp_E50; exact Hlen).
assert (E47 : ew E 47 = Z_to_bv 64 (tn_cidx n)) by exact (HVN 8%nat (tn_cidx n) Hnv8).
assert (E8 : ew E 8 = Z_to_bv 64 pal) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (E9 : ew E 9 = Z_to_bv 64 (tn_addr n)) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (Rsp : alloc_ceiling <= sp - 64 /\ sp - 64 < 2 ^ 63) by lia.
assert (U2 : bv_unsigned (ew E 2) = sp - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = tn_addr n) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U47 : bv_unsigned (ew E 47) = tn_cidx n) by (rewrite E47; apply unsigned_lit_small; lia).
assert (U49 : bv_unsigned (ew E 49) = pal + 3 * tn_cidx n) by (rewrite E49; apply unsigned_lit_small; lia).
assert (U50 : bv_unsigned (ew E 50) = 2 ^ 64 - 1 - pal) by (rewrite E50; apply unsigned_lit_small; lia).
assert (Hsp16 : (sp - 64) mod 16 = 0) by (replace (sp - 64) with (sp + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
unfold ss_gp. apply entry_st_ok_full.
- destruct g as [|[|[|[|g]]]]; cbn [gp_regs gp_pin_facts] in Gpin |- *.
  1,2,5: apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | rewrite (proj1 Gpin); reflexivity].
  all: apply regs_ok_pin;
    [ apply regs_ok_pin;
      [ apply regs_ok_Ereg | intros HH0; discriminate HH0
      | rewrite (proj1 Gpin); cbn [sv_denot]; fold E; rewrite U50, Z.add_0_r; reflexivity ]
    | intros HH0; discriminate HH0
    | rewrite (proj2 Gpin); cbn [sv_denot]; fold E; rewrite U9; reflexivity ].
- vm_compute. reflexivity.
- unfold gp_mem. repeat apply Forall_cons; try apply Forall_nil.
  + eapply (region_ok_obj_gen segs _ mem 2 (sp - 64)); [exact U2 | lia | lia | exact Ofr | reflexivity | exact HVF | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
  + eapply (region_ok_obj_gen segs _ mem 9 (tn_addr n)); [exact U9 | lia | lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
    intros j z Hj. rewrite (node_vals_expand c0 c1 n leafv Hlen).
    do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
  + unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U49.
    split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hstw. lia.
  + apply ro_region_ok. exact HRO.
- unfold gp_mem, ro_region. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U2, U9, U49. repeat split; lia.
- assert (HB : atoms_ok E (f_atoms (gp_facts 0))).
  { cbn [gp_facts f_atoms app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite U2, U9, U47, U49, U50. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; first [exact Hsp16 | exact Hn16 | lia]. }
  split; [|split; [exact I|]].
  + destruct (Nat.eq_dec g 4) as [Hg|Hg].
    * subst g. destruct (Hc1 eq_refl) as (C1a & C1b & C1c).
      change (afact_ok E 40 (mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) /\ atoms_ok E (f_atoms (gp_facts 0))).
      split; [|exact HB].
      assert (E40 : ew E 40 = Z_to_bv 64 c1) by exact (HVN 1%nat c1 eq_refl).
      assert (U40 : bv_unsigned (ew E 40) = c1) by (rewrite E40; apply unsigned_lit_small; lia).
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U40. change (2 ^ 4) with 16.
      repeat split; first [exact C1c | lia].
    * destruct g as [|[|[|[|[|g]]]]]; [exact HB | exact HB | exact HB | exact HB | congruence | exact HB].
  + cbn [gp_facts f_alias alias_ok gp_alias]. split; [|split; [|exact I]].
    * fold E. apply U_inj. unfold gp_3cidx. rewrite !U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 8 pal E8) by lia. rewrite (U_atom E 47 (tn_cidx n) E47) by lia. rewrite U_SLit.
      rewrite (U_atom E 49 (pal + 3 * tn_cidx n) E49) by lia.
      change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      rewrite (zcanon_id (tn_cidx n * 2)) by (unfold M64; lia). rewrite (zcanon_id (tn_cidx n * 2 + tn_cidx n)) by (unfold M64; lia).
      rewrite zcanon_id by (unfold M64; lia). lia.
    * fold E. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 8 pal E8) by lia. rewrite U_SLit.
      rewrite (U_atom E 50 (2 ^ 64 - 1 - pal) E50) by lia.
      change (zcanon (-1)) with (2 ^ 64 - 1). rewrite seed_lxor_ones64 by lia. apply zcanon_id. unfold M64. lia.
Qed.


Lemma gl_call : forall (g : nat) (n : tnode), gl_stmt (Datatypes.S g) n -> (g <= 2)%nat ->
forall E ss ms (regs0 f0 : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (pal c0 c1 : Z),
let sp := spZ regs0 in
st_okF segs E ss ms -> ss_pc ss = ubs2_A_round -> ss_resv ss = None ->
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac (ms_mem ms) md -> ubs2_rgb_rodata_ok (ms_mem ms) ->
tnode_wf n -> tnode_means_ok n ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - 80 -> sp <= pal -> pal + 768 <= sp0 ->
sv_denot E (sr_get (ss_regs ss) 1) = Z_to_bv 64 (gp_pc (Datatypes.S g)) ->
sv_denot E (sr_get (ss_regs ss) 2) = Z_to_bv 64 (sp - 64) -> sv_denot E (sr_get (ss_regs ss) 8) = Z_to_bv 64 pal ->
sv_denot E (sr_get (ss_regs ss) 9) = Z_to_bv 64 (tn_addr n) ->
(g = 0%nat -> sv_denot E (sr_get (ss_regs ss) 18) = Z_to_bv 64 2 /\ sv_denot E (sr_get (ss_regs ss) 19) = getr regs0 19) ->
((1 <= g)%nat -> sv_denot E (sr_get (ss_regs ss) 18) = Z_to_bv 64 (2 ^ 64 - 1 - pal) /\
sv_denot E (sr_get (ss_regs ss) 19) = Z_to_bv 64 (tn_addr n + 16)) ->
sv_denot E (sfr_get (ss_fregs ss) 10) = Z_to_bv 64 (nth g (tn_mean n) 0) ->
((1 <= g)%nat -> sv_denot E (sfr_get (ss_fregs ss) 8) = Z_to_bv 64 Cm1 /\ sv_denot E (sfr_get (ss_fregs ss) 9) = Z_to_bv 64 C256) ->
fregs_kept89 f0 (ms_fregs ms) ->
(forall r : reg, In r GP_UNTOUCHED -> sv_denot E (sr_get (ss_regs ss) r) = getr regs0 r) ->
obj_at segs (ms_mem ms) (sp - 64) LAY_GPF (gpf_vals regs0 f0) ->
In (tn_addr n, NODE_SIZE) (blocks Lc Ac) ->
obj_at segs (ms_mem ms) (tn_addr n) LAY_Node (node_vals c0 c1 n 1) -> length (tn_mean n) = 3%nat ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
mbyte segs (ms_mem ms) a = mbyte segs mem a) ->
SR segs (mkCfg ms md) (gp_postR regs0 f0 STK sp0 FP L A mem0 md0 Lc Ac md mem (sp - 80) (sp - 64) pal).
Proof.
intros g n HN Hg E ss ms regs0 f0 mem STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 sp
HS Hpc Hrv HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hpal Hpalhi D1 D2 D8 D9 Dp0 Dp1 Df10 Df89 HK89 Dkeep Ofr Hinn Ond Hlen KEEP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
assert (RG : forall r : reg, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)) by (intros r; exact (st_okF_reg segs E ss ms r HS)).
assert (FG : forall r : reg, reg_get (ms_fregs ms) r = sv_denot E (sfr_get (ss_fregs ss) r)) by (intros r; exact (st_okF_freg segs E ss ms r HS)).
pose proof (st_okF_frm segs E ss ms HS) as Hfrm.
assert (Hsp : spZ (ms_regs ms) = sp - 64).
{ unfold spZ. rewrite RG, D2. apply unsigned_lit_small. lia. }
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms) 1)).
{ rewrite RG, D1. apply ret_ok_even. destruct g as [|[|[|g]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia]. }
assert (Hal1 : spZ (ms_regs ms) mod 16 = 0).
{ rewrite Hsp. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
assert (Hlo1 : sp0 - STK <= spZ (ms_regs ms) - ROUND_STK) by (rewrite Hsp; unfold ROUND_STK; lia).
assert (Hhi1 : spZ (ms_regs ms) <= sp0) by (rewrite Hsp; lia).
pose proof (ubs2_round (fx:=fp_of ms) API IMG STK sp0 FP L A mem0 md0 Lc Ac (ms_mem ms) md (ms_regs ms) HJ Hra1 Hal1 Hlo1 Hhi1 Hfrm HRO) as HR.
pose proof (st_okF_mkst segs E ss ms HS Hrv) as Hms. rewrite Hpc in Hms. rewrite Hms. clear Hms.
eapply SR_bind; [exact HR|].
cbv beta. intros c' (fx' & regs1 & mem1 & -> & Hfrm1 & Hfa1 & Hfp1 & HJ1 & HP1 & HM1).
change (@fp_regs (fp_of ms)) with (ms_fregs ms) in Hfa1, Hfp1.
rewrite Hsp in HM1. unfold ROUND_STK in HM1.
assert (PRr : forall r : reg, In r CALLEE_SAVED -> getr regs1 r = getr (ms_regs ms) r) by (intros r Hr; exact (regs_preserved_in _ _ r HP1 Hr)).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac (ms_mem ms) md (tn_addr n) NODE_SIZE HH Hinn ltac:(unfold NODE_SIZE; lia)) as (Hn0 & Hn1 & _).
assert (HRO1 : ubs2_rgb_rodata_ok mem1).
{ intros a Ha. rewrite (HM1 a ltac:(lia) ltac:(lia)). exact (HRO a Ha). }
assert (K89 : fregs_kept89 f0 (@fp_regs fx')).
{ intros r Hr H8 H9. rewrite (Hfp1 r Hr). exact (HK89 r Hr H8 H9). }
assert (FPF : gl_fp_facts (Datatypes.S g) fx' n).
{ destruct g as [|[|[|g]]]; [ | | | lia]; cbn [gl_fp_facts].
- rewrite Hfa1, FG, Df10. reflexivity.
- destruct (Df89 ltac:(lia)) as (Df8 & Df9).
split; [rewrite Hfa1, FG, Df10; reflexivity|].
split; [rewrite (Hfp1 8%bv ltac:(cbv; tauto)), FG; exact Df8 | rewrite (Hfp1 9%bv ltac:(cbv; tauto)), FG; exact Df9].
- destruct (Df89 ltac:(lia)) as (Df8 & Df9).
split; [rewrite Hfa1, FG, Df10; reflexivity|].
split; [rewrite (Hfp1 8%bv ltac:(cbv; tauto)), FG; exact Df8 | rewrite (Hfp1 9%bv ltac:(cbv; tauto)), FG; exact Df9]. }
assert (R2 : getr regs1 2 = Z_to_bv 64 (sp - 64)) by (rewrite (PRr 2%bv ltac:(cbv; tauto)), RG; exact D2).
assert (R8 : getr regs1 8 = Z_to_bv 64 pal) by (rewrite (PRr 8%bv ltac:(cbv; tauto)), RG; exact D8).
assert (R9 : getr regs1 9 = Z_to_bv 64 (tn_addr n)) by (rewrite (PRr 9%bv ltac:(cbv; tauto)), RG; exact D9).
assert (PIN : gp_pin_facts (Datatypes.S g) regs1 regs0 (tn_addr n) pal).
{ destruct g as [|[|[|g]]]; [ | | | lia]; cbn [gp_pin_facts].
- destruct (Dp0 eq_refl) as (D18 & D19).
rewrite (PRr 18%bv ltac:(cbv; tauto)), (PRr 19%bv ltac:(cbv; tauto)), !RG. split; [exact D18 | exact D19].
- destruct (Dp1 ltac:(lia)) as (D18 & D19).
rewrite (PRr 18%bv ltac:(cbv; tauto)), (PRr 19%bv ltac:(cbv; tauto)), !RG. split; [exact D18 | exact D19].
- destruct (Dp1 ltac:(lia)) as (D18 & D19).
rewrite (PRr 18%bv ltac:(cbv; tauto)), (PRr 19%bv ltac:(cbv; tauto)), !RG. split; [exact D18 | exact D19]. }
assert (UNT : forall r : reg, In r GP_UNTOUCHED -> getr regs1 r = getr regs0 r).
{ intros r Hr. rewrite (PRr r ltac:(cbv [GP_UNTOUCHED In] in Hr; cbv [CALLEE_SAVED In]; intuition)), RG. exact (Dkeep r Hr). }
assert (OF1 : obj_at segs mem1 (sp - 64) LAY_GPF (gpf_vals regs0 f0)).
{ eapply obj_at_transport_range with (sz := 64); [exact Ofr | reflexivity | ]. intros i Hi. apply HM1; lia. }
assert (ON1 : obj_at segs mem1 (tn_addr n) LAY_Node (node_vals c0 c1 n 1)).
{ eapply obj_at_transport_range; [exact Ond | apply (proj1 lay_inside_Node) | ]. intros i Hi. apply HM1; lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
mbyte segs mem1 a = mbyte segs mem a).
{ intros a Ha Hx1 Hx2. rewrite (HM1 a Ha ltac:(lia)). exact (KEEP a Ha Hx1 Hx2). }
rewrite (RG 1%bv), D1.
exact (HN fx' regs0 f0 regs1 mem mem1 STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 HJ1 HRO1 Hwfn Hmokn Hra Hal16 Hwlo Hpal Hpalhi
Hfrm1 K89 FPF R2 R8 R9 PIN UNT OF1 Hinn ON1 Hlen KEEP1).
Qed.


Lemma gl3_beq_w1_w0 : branch_taken BC_EQ w1 (Z_to_bv 64 0) = false.
Proof. vm_compute. reflexivity. Qed.
Local Ltac gl3_den :=
lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Local Ltac gl3_wr U49 :=
wr_ok_eval;
repeat first [ apply wr_ok_nil
| apply wr_ok_cons_ro; [cbn; lia | ]
| eapply wr_ok_cons_win; [reflexivity | exact U49 | cbn [YQ0b.r_wlo]; lia | cbn [YQ0b.r_whi]; lia | ] ].
Local Ltac gl3_keep HF KEEP U49 sp pal mem :=
lazymatch type of HF with frame_of _ _ _ ?m2 =>
let KE2 := fresh "KEEP" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
mbyte segs m2 a = mbyte segs mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hx1 := fresh "Hx" in let Hx2 := fresh "Hx" in
intros a Ha Hx1 Hx2; mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?U49; lia); exact (KEEP a Ha Hx1 Hx2));
clear KEEP HF; rename KE2 into KEEP;
repeat match goal with H : mem_grows _ _ |- _ => clear H end
end.
Local Ltac gl3_refute Hc Ha Hb Hd Rm1 R256 Hchk :=
exfalso; cbn [sv_denot] in Hc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc;
rewrite fcmp_denot in Hc; cbn [fcmp_sem fp_format] in Hc; rewrite !fp_arg_D in Hc;
rewrite ?Ha, ?Hb, ?Hd in Hc; rewrite ?Rm1, ?R256 in Hc;
first [ rewrite (proj1 Hchk) in Hc | rewrite (proj2 Hchk) in Hc ]; cbv beta iota in Hc;
rewrite gl3_beq_w1_w0 in Hc; discriminate Hc.
Lemma gl3 : forall n, gl_stmt 3 n.
Proof.
intros n fy regs0 f0 regs mem memg STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hpal Hpalhi Hfrm HK89 Hfp G2 G8 G9 Gpin Gkeep Ofr Hinn Ond Hlen KEEP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof Hwfn as (_ & Hci & _ & _ & _ & Hmr).
pose proof (gp_seed fy 3%nat regs0 f0 regs memg STK sp0 FP L A mem0 md0 Lc Ac md pal n c0 c1 1 HJ HRO Hal16
ltac:(change (spZ regs0) with sp; lia) Hpal Hpalhi G2 G8 G9 Gpin Ofr Hinn Ond Hlen ltac:(intros Hq; discriminate Hq)) as HS0.
pose proof (st_ok_enterF segs fy 51 _ _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS. clear HS0.
set (E := ew_fregs (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) 51 (@fp_regs fy)) in HS.
assert (EV : forall j, (j < 51)%nat -> ew E j = ew (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) j) by (intros j Hj; apply ew_fregs_low; exact Hj).
assert (HEf : forall r : reg, ew E (51 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (U49 : bv_unsigned (ew E 49) = pal + 3 * tn_cidx n).
{ rewrite (EV 49%nat ltac:(lia)), (gp_E49 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. lia. }
assert (U2 : bv_unsigned (ew E 2) = sp - 64).
{ rewrite (EV 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl), G2. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = reg_get f0 9).
{ rewrite (EV 32%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (reg_get f0 9)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 0 _ eq_refl). }
assert (E33 : ew E 33 = reg_get f0 8).
{ rewrite (EV 33%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (reg_get f0 8)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 1 _ eq_refl). }
assert (E34 : ew E 34 = getr regs0 19).
{ rewrite (EV 34%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (getr regs0 19)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 2 _ eq_refl). }
assert (E35 : ew E 35 = getr regs0 18).
{ rewrite (EV 35%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (getr regs0 18)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 3 _ eq_refl). }
assert (E36 : ew E 36 = getr regs0 9).
{ rewrite (EV 36%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (getr regs0 9)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 4 _ eq_refl). }
assert (E37 : ew E 37 = getr regs0 8).
{ rewrite (EV 37%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (getr regs0 8)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 5 _ eq_refl). }
assert (E38 : ew E 38 = getr regs0 1).
{ rewrite (EV 38%nat ltac:(lia)), <- (Z_to_bv_bv_unsigned 64 (getr regs0 1)). exact (gp_EF regs regs0 f0 c0 c1 n 1 pal 6 _ eq_refl). }
destruct Hfp as (Gf10 & Gf8 & Gf9).
assert (Ha61 : ew E 61 = round_bits (Z_to_bv 64 (nth 2 (tn_mean n) 0))) by (rewrite <- Gf10; exact (HEf 10%bv)).
assert (Ha59 : ew E 59 = Z_to_bv 64 Cm1) by (rewrite <- Gf8; exact (HEf 8%bv)).
assert (Ha60 : ew E 60 = Z_to_bv 64 C256) by (rewrite <- Gf9; exact (HEf 9%bv)).
assert (Rm1 : bv_unsigned (Z_to_bv 64 Cm1) = Cm1) by (apply unsigned_lit_small; unfold Cm1; lia).
assert (R256 : bv_unsigned (Z_to_bv 64 C256) = C256) by (apply unsigned_lit_small; unfold C256; lia).
unfold tnode_means_ok in Hmokn.
assert (Hchk : fst (fp_lt fmt_double Cm1 (bv_unsigned (round_bits (Z_to_bv 64 (nth 2 (tn_mean n) 0))))) = true /\
fst (fp_lt fmt_double (bv_unsigned (round_bits (Z_to_bv 64 (nth 2 (tn_mean n) 0)))) C256) = true).
{ apply (round_checks_mean _ RNE).
- rewrite Forall_forall in Hmokn. apply Hmokn. apply nth_In. rewrite Hlen. lia.
- rewrite Forall_forall in Hmr. apply Hmr. apply nth_In. rewrite Hlen. lia. }
clearbody E.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp] in HS.
change memg with (ms_mem (@mkst fy regs (Z_to_bv 64 (gp_pc 3)) memg rom)) in HJ.
jrunF LAWS ubs2tbl_ok HS HJ. { gl3_wr U49. }
cbn [ms_mem mkst] in HF. gl3_keep HF KEEP U49 sp pal mem.
jbranchF ubs2tbl HS; [gl3_refute Hc Ha59 Ha60 Ha61 Rm1 R256 Hchk | clear Hc].
jrunF LAWS ubs2tbl_ok HS HJ. { gl3_wr U49. }
gl3_keep HF KEEP U49 sp pal mem.
jbranchF ubs2tbl HS; [gl3_refute Hc Ha59 Ha60 Ha61 Rm1 R256 Hchk | clear Hc].
jrunF LAWS ubs2tbl_ok HS HJ. { gl3_wr U49. }
gl3_keep HF KEEP U49 sp pal mem.
pose proof (st_okF_frm segs _ _ _ HS) as Hfrm'.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
lazymatch type of HS with st_okF _ ?E1 ?ss1 ?ms1 =>
eapply (SR_ret_at (fx:=(fp_of ms1)) segs ubs2tbl E1 ss1 ms1 _ _ ubs2tbl_ok);
[ exact Hh | exact Hlz | exact (st_okF_to_legacy segs E1 ss1 ms1 HS) | reflexivity | vm_compute; reflexivity | ];
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1)
end.
split.
{ pose proof (st_okF_reg segs E _ _ 1%bv HS) as Q1. eval_sr_get_in Q1. cbn [sv_denot] in Q1.
rewrite Z.add_0_r, E38, Z_to_bv_bv_unsigned in Q1. rewrite Q1, Hra. reflexivity. }
split; [exact Hfrm'|].
split.
{ intros r Hr. cbn [fp_regs fp_of]. cbv [FCALLEE_SAVED In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- reg_get _ ?rr = reg_get _ _ =>
first
[ rewrite (st_okF_fregs_kept segs E _ _ 51 (@fp_regs fy) [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HEf ltac:(vm_compute; reflexivity) rr ltac:(cbv; tauto));
apply HK89; [cbv; tauto | intros Hq; discriminate Hq | intros Hq; discriminate Hq]
| rewrite (st_okF_freg segs E _ _ rr HS); gl3_den; first [rewrite E33; reflexivity | rewrite E32; reflexivity] ]
end | ]).
destruct Hr. }
split; [exact HJ|].
split.
{ apply regs_preserved_of_list. intros rr Hrr.
rewrite (st_okF_reg segs E _ _ rr HS).
cbv [CALLEE_SAVED In] in Hrr.
repeat (destruct Hrr as [<- | Hrr];
[ gl3_den;
first [ rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity | rewrite E37; reflexivity
| rewrite U2; replace (sp - 64 + 64) with sp by lia; subst sp; unfold spZ; apply Z_to_bv_bv_unsigned
| lazymatch goal with |- ew _ ?k = getr regs0 ?q =>
rewrite (EV k ltac:(lia)), <- (Gkeep q ltac:(cbv; tauto)); apply ew_Ereg_nat; vm_compute; reflexivity end ] | ]).
destruct Hrr. }
intros a Ha Hx1 Hx2. exact (KEEP a Ha Hx1 Hx2).
Qed.


Lemma gl2_beq_w1_w0 : branch_taken BC_EQ w1 (Z_to_bv 64 0) = false.
Proof. unfold branch_taken, bv_eqb, w1. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma gl2_mean_nth : forall c0 c1 n lf j, length (tn_mean n) = 3%nat -> (j < 3)%nat ->
nth_error (node_vals c0 c1 n lf) (2 + j) = Some (nth j (tn_mean n) 0).
Proof.
intros c0 c1 n lf j Hlen Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.
Local Ltac gl2_refute Hc Ha Hb Hd Hchk :=
exfalso; cbn [sv_denot] in Hc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc;
rewrite fcmp_denot in Hc; cbn [fcmp_sem fp_format] in Hc; rewrite !fp_arg_D in Hc;
rewrite ?Ha, ?Hb, ?Hd in Hc; rewrite ?unsigned_lit_small in Hc by (unfold Cm1, C256; lia);
first [ rewrite (proj1 Hchk) in Hc | rewrite (proj2 Hchk) in Hc ]; rewrite gl2_beq_w1_w0 in Hc; discriminate Hc.
Local Ltac gl2_den :=
lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Local Ltac gl2_wr U49 :=
wr_ok_eval; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|];
eapply wr_ok_cons_win; [reflexivity | exact U49 | cbn [YQ0b.r_wlo]; lia | cbn [YQ0b.r_whi]; lia | ];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Local Ltac gl2_mb U49 :=
repeat match goal with HFx : frame_of _ _ _ ?m2 |- context [mbyte ubs2segs ?m2 _] =>
  mb_frame_g HFx ltac:(lia) ltac:(rewrite ?U49; lia) end.
Lemma gl2 : forall n, gl_stmt 3 n -> gl_stmt 2 n.
Proof.
intros n H3 fy regs0 f0 regs mem memg STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hpal Hpalhi Hfrm HK89 Hfp G2 G8 G9 Gpin Gkeep Ofr Hinn Ond Hlen KEEP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
pose proof Hwfn as (_ & Hci & _ & _ & _ & Hmr).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memg md (tn_addr n) NODE_SIZE HH Hinn ltac:(unfold NODE_SIZE; lia)) as (Hn0 & Hn1 & _).
assert (HNS : NODE_SIZE = 56) by reflexivity.
pose proof (gp_seed fy 2%nat regs0 f0 regs memg STK sp0 FP L A mem0 md0 Lc Ac md pal n c0 c1 1 HJ HRO Hal16
ltac:(change (spZ regs0) with sp; lia) Hpal Hpalhi G2 G8 G9 Gpin Ofr Hinn Ond Hlen ltac:(intros Hq; discriminate Hq)) as HS0.
pose proof (st_ok_enterF segs fy 51 _ _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS. clear HS0.
set (E := ew_fregs (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) 51 (@fp_regs fy)) in HS.
assert (EV : forall j, (j < 51)%nat -> ew E j = ew (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) j) by (intros j Hj; apply ew_fregs_low; exact Hj).
assert (HEf : forall r : reg, ew E (51 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (U49 : bv_unsigned (ew E 49) = pal + 3 * tn_cidx n).
{ rewrite (EV 49%nat ltac:(lia)), (gp_E49 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. lia. }
assert (E43 : ew E 43 = Z_to_bv 64 (nth 2 (tn_mean n) 0)).
{ rewrite (EV 43%nat ltac:(lia)). exact (gp_EN regs regs0 f0 c0 c1 n 1 pal 4%nat _ (gl2_mean_nth c0 c1 n 1 2%nat Hlen ltac:(lia))). }
assert (E50 : ew E 50 = Z_to_bv 64 (2 ^ 64 - 1 - pal)).
{ rewrite (EV 50%nat ltac:(lia)). exact (gp_E50 regs regs0 f0 c0 c1 n 1 pal Hlen). }
cbn [gl_fp_facts] in Hfp. destruct Hfp as (Gf10 & Gf8 & Gf9).
assert (Ha61 : ew E 61 = round_bits (Z_to_bv 64 (nth 1 (tn_mean n) 0))) by (rewrite <- Gf10; exact (HEf 10%bv)).
assert (Ha59 : ew E 59 = Z_to_bv 64 Cm1) by (rewrite <- Gf8; exact (HEf 8%bv)).
assert (Ha60 : ew E 60 = Z_to_bv 64 C256) by (rewrite <- Gf9; exact (HEf 9%bv)).
pose proof Hmokn as Hmk. unfold tnode_means_ok in Hmk.
assert (Hchk : fst (fp_lt fmt_double Cm1 (bv_unsigned (round_bits (Z_to_bv 64 (nth 1 (tn_mean n) 0))))) = true /\
fst (fp_lt fmt_double (bv_unsigned (round_bits (Z_to_bv 64 (nth 1 (tn_mean n) 0)))) C256) = true).
{ apply (round_checks_mean _ RTZ).
- rewrite Forall_forall in Hmk. apply Hmk. apply nth_In. rewrite Hlen. lia.
- rewrite Forall_forall in Hmr. apply Hmr. apply nth_In. rewrite Hlen. lia. }
clearbody E.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp] in HS.
change memg with (ms_mem (@mkst fy regs (Z_to_bv 64 (gp_pc 2)) memg rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ ubs2_A_round. { gl2_wr U49. }
cbn [ms_mem mkst] in HF.
jbranchF ubs2tbl HS; [gl2_refute Hc Ha59 Ha60 Ha61 Hchk | clear Hc].
jrunF_to LAWS ubs2tbl_ok HS HJ ubs2_A_round. { gl2_wr U49. }
jbranchF ubs2tbl HS; [gl2_refute Hc Ha59 Ha60 Ha61 Hchk | clear Hc].
jrunF_to LAWS ubs2tbl_ok HS HJ ubs2_A_round. { gl2_wr U49. }
lazymatch type of HS with st_okF _ _ _ ?msF =>
assert (HRO1 : ubs2_rgb_rodata_ok (ms_mem msF)) by (intros a Ha; gl2_mb U49; exact (HRO a Ha));
assert (OF1 : obj_at segs (ms_mem msF) (sp - 64) LAY_GPF (gpf_vals regs0 f0))
  by (eapply obj_at_transport_range with (sz := 64); [exact Ofr | reflexivity | ]; intros i Hi; gl2_mb U49; reflexivity);
assert (ON1 : obj_at segs (ms_mem msF) (tn_addr n) LAY_Node (node_vals c0 c1 n 1))
  by (eapply obj_at_transport_range; [exact Ond | apply (proj1 lay_inside_Node) | ]; intros i Hi; gl2_mb U49; reflexivity);
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
  mbyte segs (ms_mem msF) a = mbyte segs mem a)
  by (intros a Ha Hx1 Hx2; gl2_mb U49; exact (KEEP a Ha Hx1 Hx2))
end.
eapply (gl_call 2%nat n H3 ltac:(lia) _ _ _ regs0 f0 mem STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 HS).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact HJ.
- exact HRO1.
- exact Hwfn.
- exact Hmokn.
- exact Hra.
- exact Hal16.
- exact Hwlo.
- exact Hpal.
- exact Hpalhi.
- gl2_den. reflexivity.
- gl2_den. rewrite (EV 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl). exact G2.
- gl2_den. rewrite (EV 8%nat ltac:(lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl). exact G8.
- gl2_den. rewrite (EV 9%nat ltac:(lia)), (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact G9.
- intros Hc. exfalso. lia.
- intros _. split.
  + gl2_den. exact E50.
  + gl2_den. rewrite (EV 9%nat ltac:(lia)), (ew_Ereg_nat regs _ 9 9%bv eq_refl), G9.
    rewrite unsigned_lit_small by lia. reflexivity.
- gl2_den. exact E43.
- intros _. split; [gl2_den; exact Ha59 | gl2_den; exact Ha60].
- intros r Hr H8 H9.
  rewrite (st_okF_fregs_kept segs E _ _ 51 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) r Hr).
  exact (HK89 r Hr H8 H9).
- intros r Hr. rewrite <- (Gkeep r Hr). cbv [GP_UNTOUCHED In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [gl2_den; rewrite EV by lia; apply ew_Ereg_nat; vm_compute; reflexivity |]).
  destruct Hr.
- exact OF1.
- exact Hinn.
- exact ON1.
- exact Hlen.
- exact KEEP1.
Qed.


Lemma gl1_reg_atom : forall (regs : bvmap 5 word) extra fr (r : reg) k, Z.of_nat k = bv_unsigned r ->
  sv_denot (ew_fregs (Ereg regs extra) 51 fr) (SOff k 0) = getr regs r.
Proof.
intros regs extra fr r k Hk. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite ew_fregs_low by lia. apply ew_Ereg_nat. exact Hk.
Qed.
Lemma gl1_mean_nth : forall c0 c1 n lf j, length (tn_mean n) = 3%nat -> (j < 3)%nat ->
  nth_error (node_vals c0 c1 n lf) (2 + j) = Some (nth j (tn_mean n) 0).
Proof.
intros c0 c1 n lf j Hlen Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.
Local Ltac gl1_vm :=
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
Local Ltac gl1_wr U :=
  wr_ok_eval; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|];
  eapply wr_ok_cons_win; [reflexivity | exact U | cbn [r_wlo]; lia | cbn [r_whi]; lia | ];
  apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Local Ltac gl1_km HF KM m0 pal cidx U :=
  lazymatch type of HF with frame_of _ _ _ ?m2 =>
  let K := fresh "KM" in
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (pal + 3 * cidx <= a < pal + 3 * cidx + 3) ->
    mbyte ubs2segs m2 a = mbyte ubs2segs m0 a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
        mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?U; lia); exact (KM a Ha Hn));
  clear KM HF; rename K into KM end.
Local Ltac gl1_refute Hc Ha Hchk :=
  exfalso; cbn [sv_denot] in Hc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc;
  rewrite fcmp_denot in Hc; cbn [fcmp_sem fp_format] in Hc; rewrite !fp_arg_D in Hc;
  rewrite Ha in Hc; rewrite ?unsigned_lit_small in Hc by lia;
  first [ rewrite (proj1 Hchk) in Hc | rewrite (proj2 Hchk) in Hc ]; vm_compute in Hc; discriminate Hc.
Lemma gl1 : forall n, gl_stmt 2 n -> gl_stmt 1 n.
Proof.
intros n H2 fy regs0 f0 regs mem memg STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 sp
  HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hpal1 Hpal2 Hfrm Hkeep Gfp G2 G8 G9 Gpin Gun Ofr Hinn Ond Hlen KEEP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memg md (tn_addr n) NODE_SIZE HH Hinn ltac:(unfold NODE_SIZE; lia)) as (Hn0 & Hn1 & _).
unfold NODE_SIZE in Hn1.
pose proof Hwfn as (_ & Hcidx & _ & _ & _ & Hmr).
pose proof (gp_seed fy 1%nat regs0 f0 regs memg STK sp0 FP L A mem0 md0 Lc Ac md pal n c0 c1 1
  HJ HRO Hal16 ltac:(lia) Hpal1 Hpal2 G2 G8 G9 Gpin Ofr Hinn Ond Hlen ltac:(intros Hc; discriminate Hc)) as HS.
pose proof (st_ok_enterF segs fy 51 _ _ _ HS ltac:(vm_compute; reflexivity) Hfrm) as HSF. clear HS.
cbn [gl_fp_facts] in Gfp.
assert (U49 : bv_unsigned (ew (ew_fregs (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) 51 (@fp_regs fy)) 49) = pal + 3 * tn_cidx n).
{ rewrite ew_fregs_low by lia. rewrite (gp_E49 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. lia. }
assert (Ha61 : ew (ew_fregs (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) 51 (@fp_regs fy)) 61 =
  round_bits (Z_to_bv 64 (nth 0 (tn_mean n) 0))).
{ rewrite <- Gfp. exact (ew_fregs_at _ 51 _ 10%bv). }
pose proof Hmokn as Hmo. unfold tnode_means_ok in Hmo. rewrite Forall_forall in Hmo, Hmr.
assert (Hm0 : mean_ok (nth 0 (tn_mean n) 0)) by (apply Hmo; apply nth_In; rewrite Hlen; lia).
assert (Hr0 : 0 <= nth 0 (tn_mean n) 0 < 2 ^ 64) by (apply Hmr; apply nth_In; rewrite Hlen; lia).
pose proof (round_checks_mean _ RTZ Hm0 Hr0) as Hchk. unfold Cm1, C256 in Hchk.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (pal + 3 * tn_cidx n <= a < pal + 3 * tn_cidx n + 3) ->
  mbyte ubs2segs memg a = mbyte ubs2segs memg a) by (intros; reflexivity).
change memg with (ms_mem (@mkst fy regs (Z_to_bv 64 (gp_pc 1)) memg rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HSF HJ ubs2_A_round.
{ gl1_wr U49. }
gl1_km HF KM memg pal (tn_cidx n) U49. clear HG.
jbranchF ubs2tbl HSF; [gl1_refute Hc Ha61 Hchk | clear Hc].
jrunF_to LAWS ubs2tbl_ok HSF HJ ubs2_A_round.
{ gl1_wr U49. }
gl1_km HF KM memg pal (tn_cidx n) U49. clear HG.
jbranchF ubs2tbl HSF; [gl1_refute Hc Ha61 Hchk | clear Hc].
jrunF_to LAWS ubs2tbl_ok HSF HJ ubs2_A_round.
{ gl1_wr U49. }
gl1_km HF KM memg pal (tn_cidx n) U49. clear HG.
lazymatch type of HSF with st_okF _ _ _ ?msf =>
assert (HRO2 : ubs2_rgb_rodata_ok (ms_mem msf))
  by (intros a Ha; rewrite (KM a ltac:(lia) ltac:(lia)); exact (HRO a Ha));
assert (Ofr2 : obj_at segs (ms_mem msf) (sp - 64) LAY_GPF (gpf_vals regs0 f0))
  by (apply (obj_at_transport_range segs memg (ms_mem msf) (sp - 64) LAY_GPF (gpf_vals regs0 f0) 64 Ofr);
      [vm_compute; reflexivity | intros i Hi; apply KM; lia]);
assert (Ond2 : obj_at segs (ms_mem msf) (tn_addr n) LAY_Node (node_vals c0 c1 n 1))
  by (apply (obj_at_transport_range segs memg (ms_mem msf) (tn_addr n) LAY_Node (node_vals c0 c1 n 1) NODE_SIZE Ond (proj1 lay_inside_Node));
      intros i Hi; unfold NODE_SIZE in Hi; apply KM; lia);
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
  mbyte segs (ms_mem msf) a = mbyte segs mem a)
  by (intros a Ha Hk1 Hk2; rewrite (KM a Ha ltac:(lia)); exact (KEEP a Ha Hk1 Hk2));
assert (FK : fregs_kept89 f0 (ms_fregs msf))
end.
{ intros r Hr H8 H9.
  assert (Hr' : In r [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv).
  { cbv [FCALLEE_SAVED In] in Hr. cbv [In].
    destruct Hr as [<- | [<- | Hr]]; [exfalso; apply H8; reflexivity | exfalso; apply H9; reflexivity | exact Hr]. }
  rewrite (st_okF_fregs_kept segs _ _ _ 51 (@fp_regs fy) [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HSF (ew_fregs_at _ 51 _) ltac:(vm_compute; reflexivity) r Hr').
  apply Hkeep; assumption. }
eapply (gl_call 1%nat n H2 ltac:(lia) _ _ _ regs0 f0 mem STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 HSF eq_refl eq_refl HJ HRO2
  Hwfn Hmokn Hra Hal16 Hwlo Hpal1 Hpal2).
- gl1_vm. cbn [sv_denot]. reflexivity.
- gl1_vm. rewrite (gl1_reg_atom regs _ _ 2%bv 2%nat eq_refl). exact G2.
- gl1_vm. rewrite (gl1_reg_atom regs _ _ 8%bv 8%nat eq_refl). exact G8.
- gl1_vm. rewrite (gl1_reg_atom regs _ _ 9%bv 9%nat eq_refl). exact G9.
- intros Hc. discriminate Hc.
- intros _. split.
  + gl1_vm. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_fregs_low by lia.
    exact (gp_E50 regs regs0 f0 c0 c1 n 1 pal Hlen).
  + gl1_vm. cbn [sv_denot]. rewrite ew_fregs_low by lia. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), G9.
    rewrite unsigned_lit_small by lia. reflexivity.
- gl1_vm. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_fregs_low by lia.
  exact (gp_EN regs regs0 f0 c0 c1 n 1 pal 3 _ (gl1_mean_nth c0 c1 n 1 1 Hlen ltac:(lia))).
- intros _. split; gl1_vm; cbn [sv_denot]; reflexivity.
- exact FK.
- intros r Hr. rewrite <- (Gun r Hr). cbv [GP_UNTOUCHED In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [gl1_vm; apply gl1_reg_atom; reflexivity |]). destruct Hr.
- exact Ofr2.
- exact Hinn.
- exact Ond2.
- exact Hlen.
- exact KEEP2.
Qed.


Local Ltac gl0_den :=
lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Lemma gl0 : forall n, gl_stmt 1 n -> gl_stmt 0 n.
Proof.
intros n H1 fy regs0 f0 regs mem memg STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 sp
HJ HRO Hwfn Hmokn Hra Hal16 Hwlo Hpal Hpalhi Hfrm HK89 Hfp G2 G8 G9 Gpin Gkeep Ofr Hinn Ond Hlen KEEP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
pose proof Hwfn as (_ & Hci & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memg md (tn_addr n) NODE_SIZE HH Hinn ltac:(unfold NODE_SIZE; lia)) as (Hn0 & Hn1 & _).
pose proof (gp_seed fy 0%nat regs0 f0 regs memg STK sp0 FP L A mem0 md0 Lc Ac md pal n c0 c1 1 HJ HRO Hal16
ltac:(change (spZ regs0) with sp; lia) Hpal Hpalhi G2 G8 G9 Gpin Ofr Hinn Ond Hlen ltac:(intros Hq; discriminate Hq)) as HS0.
pose proof (st_ok_enterF segs fy 51 _ _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS. clear HS0.
set (E := ew_fregs (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) 51 (@fp_regs fy)) in HS.
assert (EV : forall j, (j < 51)%nat -> ew E j = ew (Ereg regs (gp_extra regs0 f0 c0 c1 n 1 pal)) j) by (intros j Hj; apply ew_fregs_low; exact Hj).
assert (HEf : forall r : reg, ew E (51 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; apply ew_fregs_at).
assert (U49 : bv_unsigned (ew E 49) = pal + 3 * tn_cidx n).
{ rewrite (EV 49%nat ltac:(lia)), (gp_E49 regs regs0 f0 c0 c1 n 1 pal Hlen). apply unsigned_lit_small. lia. }
assert (E41 : ew E 41 = Z_to_bv 64 (nth 0 (tn_mean n) 0)).
{ rewrite (EV 41%nat ltac:(lia)). apply (gp_EN regs regs0 f0 c0 c1 n 1 pal 2%nat). unfold node_vals.
destruct (tn_mean n) as [|m0 ms0] eqn:Hm; [cbn in Hlen; discriminate Hlen | reflexivity]. }
clearbody E.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_gp] in HS.
change memg with (ms_mem (@mkst fy regs (Z_to_bv 64 (gp_pc 0)) memg rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ ubs2_A_round.
{ wr_ok_eval. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | exact U49 | cbn [YQ0b.r_wlo]; lia | cbn [YQ0b.r_whi]; lia | ].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (HRO1 : ubs2_rgb_rodata_ok (ms_mem ms)).
{ intros a Ha. mb_frame_g HF ltac:(lia) ltac:(rewrite ?U49; lia). exact (HRO a Ha). }
assert (OF1 : obj_at segs (ms_mem ms) (sp - 64) LAY_GPF (gpf_vals regs0 f0)).
{ eapply obj_at_transport_range with (sz := 64); [exact Ofr | reflexivity | ]. intros i Hi.
mb_frame_g HF ltac:(lia) ltac:(rewrite ?U49; lia). reflexivity. }
assert (ON1 : obj_at segs (ms_mem ms) (tn_addr n) LAY_Node (node_vals c0 c1 n 1)).
{ eapply obj_at_transport_range; [exact Ond | apply (proj1 lay_inside_Node) | ]. intros i Hi.
assert (HNS : NODE_SIZE = 56) by reflexivity.
mb_frame_g HF ltac:(lia) ltac:(rewrite ?U49; lia). reflexivity. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
mbyte segs (ms_mem ms) a = mbyte segs mem a).
{ intros a Ha Hx1 Hx2. mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?U49; lia). exact (KEEP a Ha Hx1 Hx2). }
eapply (gl_call 0%nat n H1 ltac:(lia) _ _ _ regs0 f0 mem STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 HS).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact HJ.
- exact HRO1.
- exact Hwfn.
- exact Hmokn.
- exact Hra.
- exact Hal16.
- exact Hwlo.
- exact Hpal.
- exact Hpalhi.
- gl0_den. reflexivity.
- gl0_den. rewrite (EV 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl). exact G2.
- gl0_den. rewrite (EV 8%nat ltac:(lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl). exact G8.
- gl0_den. rewrite (EV 9%nat ltac:(lia)), (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact G9.
- intros _. split.
+ gl0_den. reflexivity.
+ gl0_den. rewrite (EV 19%nat ltac:(lia)), (ew_Ereg_nat regs _ 19 19%bv eq_refl). exact (proj2 Gpin).
- intros Hc. exfalso. lia.
- gl0_den. exact E41.
- intros Hc. exfalso. lia.
- intros r Hr H8 H9.
rewrite (st_okF_fregs_kept segs E _ _ 51 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) r Hr).
exact (HK89 r Hr H8 H9).
- intros r Hr. rewrite <- (Gkeep r Hr). cbv [GP_UNTOUCHED In] in Hr.
repeat (destruct Hr as [<- | Hr]; [gl0_den; rewrite EV by lia; apply ew_Ereg_nat; vm_compute; reflexivity |]).
destruct Hr.
- exact OF1.
- exact Hinn.
- exact ON1.
- exact Hlen.
- exact KEEP1.
Qed.


Definition rall_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 39 (gp_lits 0)) ].
Lemma rall_submem : submem rall_mem (gp_mem 0).
Proof.
unfold rall_mem, gp_mem. apply submem_drop. apply submem_keep; [|apply submem_nil].
split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [left; cbn; lia|]. intros c Hc; exact Hc.
Qed.
Lemma rall_root : forall t, tree_full t -> exists nr, troot t = tn_addr nr /\ In nr (tree_nodes t).
Proof.
intros t Hf. destruct t as [|nr|nr tl tr]; [destruct Hf| |]; exists nr; (split; [reflexivity | left; reflexivity]).
Qed.
Lemma gp_R_all : (forall t, gp_R_stmt t -> gp_P_stmt t) -> (forall n, gl_stmt 0 n) -> forall u, gp_R_stmt u.
Proof.
intros HPR HGL u. induction u as [|n|n l IHl r IHr];
intros fy regs0 f0 regs mem STK sp0 FP L A mem0 md0 Lc Ac md pal sp HJ HRO Hra Hal16 Hbud Hpal Hpalhi Hfrm Hfk
Hr2 Hr8 Hr9 Hr18 Hr19 Hun Hfr Htree Hfull Hwf Hmok Hbl.
- destruct Hfull.
- destruct Htree as (Hnz & Hlen & c0 & c1 & Hobj).
assert (HG0 : GPB (theight (TLeaf n)) = 80) by reflexivity. rewrite HG0 in Hbud |- *.
exact (HGL n fy regs0 f0 regs mem mem STK sp0 FP L A mem0 md0 Lc Ac md pal c0 c1 HJ HRO (Forall_inv Hwf) (Forall_inv Hmok)
Hra Hal16 Hbud Hpal Hpalhi Hfrm Hfk I Hr2 Hr8 Hr9 (conj Hr18 Hr19) Hun Hfr (Hbl (tn_addr n, NODE_SIZE) (or_introl eq_refl)) Hobj Hlen
(fun _ _ _ _ => eq_refl)).
- pose proof HJ as (HH & _ & _ & _ & _ & (_ & Hstk0 & Hceil & _ & _) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof ro_bounds as Hro.
assert (HNSv : NODE_SIZE = 56) by reflexivity.
pose proof (u64_range (getr regs0 2)) as Hsp. change (bv_unsigned (getr regs0 2)) with sp in Hsp. assert (Hspd : sp = spZ regs0) by reflexivity.
set (h := theight (TNode n l r)) in *.
pose proof (theight_node_l n l r : theight l + 1 <= h) as Hhl.
pose proof (theight_node_r n l r : theight r + 1 <= h) as Hhr.
pose proof (theight_nonneg l) as Hhl0. pose proof (theight_nonneg r) as Hhr0.
assert (HGl : GPB (theight l) + 64 <= GPB h) by (unfold GPB; lia).
assert (HGr : GPB (theight r) <= GPB h) by (unfold GPB; lia).
assert (HGl0 : 64 <= GPB (theight l)) by (unfold GPB; lia).
assert (Hb64 : sp0 - STK <= sp - 64) by lia.
assert (Hbudr : sp0 - STK <= sp - GPB (theight r)) by lia.
cbn [troot] in Hr9. destruct Htree as (Hnz & Hlen & Hobj & Htl & Htr).
destruct Hfull as [Hfl Hfr'].
apply tree_forall_node in Hwf as (Hwfn & Hwfl & Hwfr).
apply tree_forall_node in Hmok as (Hmokn & Hmokl & Hmokr).
assert (Hinn : In (tn_addr n, NODE_SIZE) (blocks Lc Ac)) by (apply Hbl; left; reflexivity).
assert (Hbll : forall b, In b (tree_blocks l) -> In b (blocks Lc Ac)) by (intros b Hb; apply Hbl; right; apply in_app_iff; left; exact Hb).
assert (Hblr : forall b, In b (tree_blocks r) -> In b (blocks Lc Ac)) by (intros b Hb; apply Hbl; right; apply in_app_iff; right; exact Hb).
assert (HND : forall n', In n' (tree_nodes (TNode n l r)) -> 4096 <= tn_addr n' /\ tn_addr n' + NODE_SIZE <= alloc_ceiling).
{ intros n' Hn'. destruct (node_facts Lc Ac mem md (TNode n l r) n' HH Hbl Hn') as (B1 & B2 & _). split; assumption. }
destruct (rall_root r Hfr') as (nr & Hroot & Hinr).
destruct (node_facts Lc Ac mem md (TNode n l r) nr HH Hbl ltac:(right; apply in_app_iff; right; exact Hinr)) as (Hc0 & Hc1 & Hc16).
rewrite <- Hroot in Hc0, Hc1, Hc16.
pose proof (gp_seed fy 0%nat regs0 f0 regs mem STK sp0 FP L A mem0 md0 Lc Ac md pal n (troot l) (troot r) 0
HJ HRO Hal16 Hb64 Hpal Hpalhi Hr2 Hr8 Hr9 (conj Hr18 Hr19) Hfr Hinn Hobj Hlen ltac:(intros Hc; discriminate Hc)) as HS0.
set (E0 := Ereg regs (gp_extra regs0 f0 (troot l) (troot r) n 0 pal)) in HS0.
pose proof (st_ok_submem segs E0 _ _ rall_mem HS0 rall_submem ltac:(vm_compute; reflexivity)) as HS1.
pose proof (st_ok_enterF segs fy 51 E0 _ _ HS1 ltac:(vm_compute; reflexivity) Hfrm) as HS.
clear HS0 HS1.
set (E := ew_fregs E0 51 (@fp_regs fy)) in HS.
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). subst E. rewrite ew_fregs_low by lia. subst E0. apply ew_Ereg_nat. exact Hk. }
assert (E39 : ew E 39 = Z_to_bv 64 (troot l)).
{ subst E. rewrite ew_fregs_low by lia. subst E0. exact (gp_EN regs regs0 f0 (troot l) (troot r) n 0 pal 0%nat (troot l) eq_refl). }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 (gp_pc 0)) mem rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ ubs2_A_get_palette_from_decision_tree.
{ wr_ok_eval. apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rename ms into ms1, HS into HS1, HJ into HJ1, HF into HF1, HG into HG1.
assert (Heq1 : forall x, ms_mem ms1 x = mem x).
{ lazymatch type of HF1 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF1) end. }
assert (Hmb1 : forall a, mbyte segs (ms_mem ms1) a = mbyte segs mem a) by (intros a; unfold mbyte; rewrite Heq1; reflexivity).
pose proof (st_okF_regs_kept segs E _ _ regs [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS1
ltac:(intros rr _; apply HE0; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as K1.
pose proof (st_okF_fregs_kept segs E _ _ 51 (@fp_regs fy) FCALLEE_SAVED HS1 ltac:(intros rr; subst E; apply ew_fregs_at) ltac:(vm_compute; reflexivity)) as F1.
pose proof (st_okF_reg segs E _ _ 1%bv HS1) as R1. eval_sr_get_in R1. cbn [sv_denot] in R1.
assert (R1' : getr (ms_regs ms1) 1 = Z_to_bv 64 (gp_pc 4)) by (rewrite R1; reflexivity).
pose proof (st_okF_reg segs E _ _ 10%bv HS1) as R10. eval_sr_get_in R10. cbn [sv_denot] in R10.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E39 in R10.
pose proof (st_okF_reg segs E _ _ 11%bv HS1) as R11. eval_sr_get_in R11. cbn [sv_denot] in R11.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE0 8%nat 8%bv eq_refl), Hr8 in R11.
pose proof (st_okF_reg segs E _ _ 18%bv HS1) as R18. eval_sr_get_in R18. cbn [sv_denot] in R18.
assert (Usp1 : spZ (ms_regs ms1) = sp - 64).
{ unfold spZ. rewrite (K1 2%bv ltac:(cbv; tauto)), Hr2. apply unsigned_lit_small. lia. }
assert (HRO1 : ubs2_rgb_rodata_ok (ms_mem ms1)) by (intros a Ha; rewrite Hmb1; apply HRO; exact Ha).
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite R1'; apply ret_ok_even; vm_compute; reflexivity).
assert (Hal1 : spZ (ms_regs ms1) mod 16 = 0).
{ rewrite Usp1. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (Hbud1 : sp0 - STK <= spZ (ms_regs ms1) - GPB (theight l)) by (rewrite Usp1; lia).
assert (Hpal1 : spZ (ms_regs ms1) <= pal) by (rewrite Usp1; lia).
assert (Htl1 : tree_at segs (ms_mem ms1) l) by (apply (tree_at_frame segs mem (ms_mem ms1) l Htl); intros n' a _ _; apply Hmb1).
rewrite (st_okF_mkst segs E _ _ HS1 eq_refl). cbn [ss_pc].
eapply SR_bind.
{ exact (HPR l IHl (fp_of ms1) (ms_regs ms1) (ms_mem ms1) STK sp0 FP L A mem0 md0 Lc Ac md pal HJ1 HRO1 Hra1 Hal1 Hbud1 Hpal1 Hpalhi
(st_okF_frm segs E _ _ HS1) R10 R11 Htl1 Hfl Hwfl Hmokl Hbll). }
cbv beta. intros c' (fx2 & regs2 & mem2 & -> & Hfrm2 & Hfp2 & HJ2 & HP2 & Hmem2).
rewrite Usp1 in Hmem2. rewrite R1'.
assert (K2 : forall rr, In rr [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP2) by (cbv [CALLEE_SAVED In] in Hrr |- *; tauto). apply K1. exact Hrr. }
assert (G2 : getr regs2 2 = Z_to_bv 64 (sp - 64)) by (rewrite (K2 2%bv ltac:(cbv; tauto)); exact Hr2).
assert (G8 : getr regs2 8 = Z_to_bv 64 pal) by (rewrite (K2 8%bv ltac:(cbv; tauto)); exact Hr8).
assert (G9 : getr regs2 9 = Z_to_bv 64 (tn_addr n)) by (rewrite (K2 9%bv ltac:(cbv; tauto)); exact Hr9).
assert (G18 : getr regs2 18 = Z_to_bv 64 2) by (rewrite (regs_preserved_in _ _ 18%bv HP2 ltac:(cbv; tauto)); exact R18).
assert (G19 : getr regs2 19 = getr regs0 19) by (rewrite (K2 19%bv ltac:(cbv; tauto)); exact Hr19).
assert (Hmb2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 - GPB (theight l) <= a < sp - 64) -> ~ (pal <= a < pal + 768) ->
mbyte segs mem2 a = mbyte segs mem a).
{ intros a Ha H1 H2. rewrite (Hmem2 a Ha H1 H2). apply Hmb1. }
assert (Hfr2 : obj_at segs mem2 (sp - 64) LAY_GPF (gpf_vals regs0 f0)).
{ apply (obj_at_transport_range segs mem mem2 (sp - 64) LAY_GPF _ 64 Hfr eq_refl). intros i Hi. apply Hmb2; lia. }
assert (Hobj2 : obj_at segs mem2 (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0)).
{ apply (obj_at_transport_range segs mem mem2 (tn_addr n) LAY_Node _ NODE_SIZE Hobj (proj1 lay_inside_Node)).
intros i Hi. destruct (HND n ltac:(left; reflexivity)) as (B1 & B2). apply Hmb2; lia. }
assert (HRO2 : ubs2_rgb_rodata_ok mem2) by (intros a Ha; rewrite Hmb2 by lia; apply HRO; exact Ha).
assert (Htr2 : tree_at segs mem2 r).
{ apply (tree_at_frame segs mem mem2 r Htr). intros n' a Hn' Ha.
destruct (HND n' ltac:(right; apply in_app_iff; right; exact Hn')) as (B1 & B2). apply Hmb2; lia. }
pose proof (gp_seed fx2 4%nat regs0 f0 regs2 mem2 STK sp0 FP L A mem0 md0 Lc Ac md pal n (troot l) (troot r) 0
HJ2 HRO2 Hal16 Hb64 Hpal Hpalhi G2 G8 G9 (conj G18 G19) Hfr2 Hinn Hobj2 Hlen (fun _ => conj Hc0 (conj Hc1 Hc16))) as HT0.
set (E0' := Ereg regs2 (gp_extra regs0 f0 (troot l) (troot r) n 0 pal)) in HT0.
pose proof (st_ok_submem segs E0' _ _ rall_mem HT0 rall_submem ltac:(vm_compute; reflexivity)) as HT1.
pose proof (st_ok_enterF segs fx2 51 E0' _ _ HT1 ltac:(vm_compute; reflexivity) Hfrm2) as HT.
clear HT0 HT1.
set (E' := ew_fregs E0' 51 (@fp_regs fx2)) in HT.
assert (HE0' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E' k = getr regs2 rr).
{ intros k rr Hk. pose proof (u5_range rr). subst E'. rewrite ew_fregs_low by lia. subst E0'. apply ew_Ereg_nat. exact Hk. }
assert (E40 : ew E' 40 = Z_to_bv 64 (troot r)).
{ subst E'. rewrite ew_fregs_low by lia. subst E0'. exact (gp_EN regs2 regs0 f0 (troot l) (troot r) n 0 pal 1%nat (troot r) eq_refl). }
change mem2 with (ms_mem (@mkst fx2 regs2 (Z_to_bv 64 (gp_pc 4)) mem2 rom)) in HJ2.
jrunF_to LAWS ubs2tbl_ok HT HJ2 (gp_pc 0).
{ wr_ok_eval. apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ2.
rename ms into ms3, HF into HF3, HG into HG3.
assert (Heq3 : forall x, ms_mem ms3 x = mem2 x).
{ lazymatch type of HF3 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF3) end. }
assert (Hmb3 : forall a, mbyte segs (ms_mem ms3) a = mbyte segs mem2 a) by (intros a; unfold mbyte; rewrite Heq3; reflexivity).
pose proof (st_okF_regs_kept segs E' _ _ regs2 [2; 3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HT
ltac:(intros rr _; apply HE0'; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as K3.
pose proof (st_okF_fregs_kept segs E' _ _ 51 (@fp_regs fx2) FCALLEE_SAVED HT ltac:(intros rr; subst E'; apply ew_fregs_at) ltac:(vm_compute; reflexivity)) as F3.
pose proof (st_okF_reg segs E' _ _ 9%bv HT) as Q9. eval_sr_get_in Q9. cbn [sv_denot] in Q9.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E40 in Q9.
pose proof (st_okF_reg segs E' _ _ 18%bv HT) as Q18. eval_sr_get_in Q18. cbn [sv_denot] in Q18.
assert (H32 : getr (ms_regs ms3) 2 = Z_to_bv 64 (sp - 64)) by (rewrite (K3 2%bv ltac:(cbv; tauto)); exact G2).
assert (H38 : getr (ms_regs ms3) 8 = Z_to_bv 64 pal) by (rewrite (K3 8%bv ltac:(cbv; tauto)); exact G8).
assert (H319 : getr (ms_regs ms3) 19 = getr regs0 19) by (rewrite (K3 19%bv ltac:(cbv; tauto)); exact G19).
assert (Hun3 : forall rr : reg, In rr GP_UNTOUCHED -> getr (ms_regs ms3) rr = getr regs0 rr).
{ intros rr Hrr. rewrite (K3 rr) by (cbv [GP_UNTOUCHED In] in Hrr |- *; tauto).
rewrite (K2 rr) by (cbv [GP_UNTOUCHED In] in Hrr |- *; tauto). apply Hun. exact Hrr. }
assert (Hfk3 : fregs_kept89 f0 (@fp_regs (fp_of ms3))).
{ intros rr Hrr N8 N9. cbn [fp_regs fp_of]. rewrite (F3 rr Hrr), (Hfp2 rr Hrr). cbn [fp_regs fp_of]. rewrite (F1 rr Hrr). exact (Hfk rr Hrr N8 N9). }
assert (Hfr3 : obj_at segs (ms_mem ms3) (sp - 64) LAY_GPF (gpf_vals regs0 f0)).
{ apply (obj_at_transport_range segs mem2 (ms_mem ms3) (sp - 64) LAY_GPF _ 64 Hfr2 eq_refl). intros i Hi. apply Hmb3. }
assert (Htr3 : tree_at segs (ms_mem ms3) r) by (apply (tree_at_frame segs mem2 (ms_mem ms3) r Htr2); intros n' a _ _; apply Hmb3).
assert (HRO3 : ubs2_rgb_rodata_ok (ms_mem ms3)) by (intros a Ha; rewrite Hmb3; apply HRO2; exact Ha).
rewrite (st_okF_mkst segs E' _ _ HT eq_refl). cbn [ss_pc].
eapply SR_mono.
{ exact (IHr (fp_of ms3) regs0 f0 (ms_regs ms3) (ms_mem ms3) STK sp0 FP L A mem0 md0 Lc Ac md pal
HJ2 HRO3 Hra Hal16 Hbudr Hpal Hpalhi (st_okF_frm segs E' _ _ HT) Hfk3 H32 H38 Q9 Q18 H319 Hun3 Hfr3 Htr3 Hfr' Hwfr Hmokr Hblr). }
cbv beta. intros c' (fx' & regs' & mem' & -> & Hfrm' & Hfp' & HJ' & HP' & Hmem').
try (change (spZ regs0) with sp in Hmem').
exists fx', regs', mem'. split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact Hfp'|]. split; [exact HJ'|]. split; [exact HP'|].
intros a Ha H1 H2. rewrite (Hmem' a Ha ltac:(lia) H2), Hmb3. apply Hmb2; [exact Ha | lia | exact H2].
Qed.


Lemma pofr_r8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Definition pofr_ss : sstate :=
mkSS ubs2_A_get_palette_from_decision_tree sr_atoms [ YQ0b.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [] ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 64) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Lemma gp_P_of_R : forall t, gp_R_stmt t -> gp_P_stmt t.
Proof.
intros t HR fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md pal HJ HRO Hra Hal16 Hbud Hpal Hpalhi Hfrm Ha0 Ha1 Htree Hfull Hwf Hmok Hbl.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
pose proof (theight_nonneg t) as Hh0. assert (HG80 : 80 <= GPB (theight t)) by (unfold GPB; lia).
assert (Hroot : exists n, In n (tree_nodes t) /\ troot t = tn_addr n).
{ destruct t as [|n|n l r]; [destruct Hfull | exists n; split; [left; reflexivity | reflexivity] | exists n; split; [left; reflexivity | reflexivity]]. }
destruct Hroot as (n & Hin & Hrt).
destruct (node_facts Lc Ac mem md t n HH Hbl Hin) as (Hn0 & Hn1 & Hn16).
pose proof Ha0 as Ha0n. rewrite Hrt in Ha0n.
set (E0 := Ereg regs []).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HU20 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (HE0 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E0 10) = tn_addr n) by (rewrite (HE0 10%nat 10%bv eq_refl), Ha0n; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 pofr_ss (@mkst fy regs (Z_to_bv 64 ubs2_A_get_palette_from_decision_tree) mem rom)).
{ unfold pofr_ss. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack segs _ mem 2 (spZ regs)); [exact HU20 | lia | lia | intros a Ha; apply Hstw; lia].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU20, HU10. change (2 ^ 4) with 16. repeat split; lia. }
pose proof (st_ok_enterF segs fy 32 E0 _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
clear HS0.
set (E := ew_fregs E0 32 (@fp_regs fy)) in HS.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). subst E. rewrite ew_fregs_low by lia. apply HE0. exact Hk. }
assert (HEf : forall r : reg, ew E (32 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; subst E; apply ew_fregs_at).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 ubs2_A_get_palette_from_decision_tree) mem rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ (gp_pc 0).
{ wr_ok_eval. eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
pose proof (st_okF_to_legacy segs E _ _ HS) as HSL.
assert (HRO' : ubs2_rgb_rodata_ok (ms_mem ms)).
{ intros a Ha. rewrite <- (HRO a Ha). mb_frame_g HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
assert (Hfk : fregs_kept89 (@fp_regs fy) (@fp_regs (fp_of ms))).
{ intros r Hr _ _. exact (st_okF_fregs_kept segs E _ _ 32 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) r Hr). }
assert (Hun : forall r : reg, In r GP_UNTOUCHED -> getr (ms_regs ms) r = getr regs r).
{ apply (st_okF_regs_kept segs E _ _ regs GP_UNTOUCHED HS).
- intros r _. apply HE. pose proof (u5_range r). unfold ridx. lia.
- vm_compute. reflexivity. }
assert (Hq2 : getr (ms_regs ms) 2 = Z_to_bv 64 (spZ regs - 64)).
{ rewrite (st_okF_reg segs E _ _ 2%bv HS). eval_sr_get. cbn [sv_denot]. rewrite HU2. first [reflexivity | f_equal; lia]. }
assert (Hq8 : getr (ms_regs ms) 8 = Z_to_bv 64 pal).
{ rewrite (st_okF_reg segs E _ _ 8%bv HS). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, (HE 11%nat 11%bv eq_refl), Z_to_bv_bv_unsigned. exact Ha1. }
assert (Hq9 : getr (ms_regs ms) 9 = Z_to_bv 64 (troot t)).
{ rewrite (st_okF_reg segs E _ _ 9%bv HS). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, (HE 10%nat 10%bv eq_refl), Z_to_bv_bv_unsigned. exact Ha0. }
assert (Hq18 : getr (ms_regs ms) 18 = Z_to_bv 64 2).
{ rewrite (st_okF_reg segs E _ _ 18%bv HS). eval_sr_get. reflexivity. }
assert (Hq19 : getr (ms_regs ms) 19 = getr regs 19).
{ rewrite (st_okF_reg segs E _ _ 19%bv HS). eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned. reflexivity. }
assert (HF41 : ew E 41 = reg_get (@fp_regs fy) 9) by exact (HEf 9%bv).
assert (HF40 : ew E 40 = reg_get (@fp_regs fy) 8) by exact (HEf 8%bv).
assert (Hobj : obj_at segs (ms_mem ms) (spZ regs - 64) LAY_GPF (gpf_vals regs (@fp_regs fy))).
{ unfold LAY_GPF, gpf_vals. cbn [obj_at]. unfold field_ok. cbn [fst snd].
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 8) with (spZ regs + -56) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-56) 8%N (SOff 41 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, HF41, Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 16) with (spZ regs + -48) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-48) 8%N (SOff 40 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, HF40, Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 24) with (spZ regs + -40) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-40) 8%N (SOff 19 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 32) with (spZ regs + -32) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-32) 8%N (SOff 18 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 40) with (spZ regs + -24) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-24) 8%N (SOff 9 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 48) with (spZ regs + -16) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-16) 8%N (SOff 8 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
split; [split; [|apply pofr_r8] |].
{ replace (spZ regs - 64 + 56) with (spZ regs + -8) by lia.
eapply (st_chunk_val segs E _ _ 0%nat _ 2%nat (-8) 8%N (SOff 1 0) (spZ regs) _ HSL);
[reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply pofr_r8 | lia]. }
exact I. }
assert (Htree' : tree_at segs (ms_mem ms) t).
{ eapply tree_at_frame; [exact Htree|]. intros n' a Hn' Ha.
destruct (node_facts Lc Ac mem md t n' HH Hbl Hn') as (Hc0 & Hc1 & _).
mb_frame_g HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
pose proof (HR (fp_of ms) regs (@fp_regs fy) (ms_regs ms) (ms_mem ms) STK sp0 FP L A mem0 md0 Lc Ac md pal
HJ HRO' Hra Hal16 Hbud Hpal Hpalhi (st_okF_frm segs E _ _ HS) Hfk Hq2 Hq8 Hq9 Hq18 Hq19 Hun Hobj Htree' Hfull Hwf Hmok Hbl) as HR'.
lazymatch type of HS with st_okF _ _ ?s _ => assert (Hpc : ss_pc s = gp_pc 0) by (vm_compute; reflexivity) end.
rewrite (st_okF_mkst segs E _ _ HS eq_refl), Hpc.
eapply SR_mono; [exact HR' |].
cbv beta. intros c' (fx' & regs2 & mem2 & -> & Hfrm' & Hfp' & HJ2 & HP2 & Hmem2).
exists fx', regs2, mem2. split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact Hfp'|]. split; [exact HJ2|]. split; [exact HP2|].
intros a Ha Hno Hnp. rewrite (Hmem2 a Ha ltac:(lia) Hnp). mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?HU2; lia). reflexivity.
Qed.


Lemma gl_all : forall n, gl_stmt 0 n.
Proof. intros n. apply gl0, gl1, gl2, gl3. Qed.
Lemma gp_P_all : forall t, gp_P_stmt t.
Proof. intros t. apply gp_P_of_R. apply gp_R_all; [exact gp_P_of_R | exact gl_all]. Qed.
Theorem ubs2_getpal : getpal_spec API.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs t pal HJ Hra Hal16 Hbud Hsp Hfrm Ha0 Ha1 Htree Hfull Hh Hwf Hmok Hbl Hpal Hpalhi HRO.
pose proof (theight_nonneg t) as Hh0.
assert (HG : GPB (theight t) <= GETPAL_STK) by (unfold GPB, GETPAL_STK, theight, TREE_HMAX in *; lia).
eapply SR_mono.
{ exact (gp_P_all t fx regs memc STK sp0 FP L A mem md Lc Ac mdc pal HJ HRO Hra Hal16 ltac:(lia) Hpal Hpalhi Hfrm Ha0 Ha1 Htree Hfull Hwf Hmok Hbl). }
cbv beta. intros c' (fx' & regs2 & mem2 & -> & Hfrm' & Hfp' & HJ2 & HP2 & Hmem2).
exists fx', regs2, mem2. split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact Hfp'|]. split; [exact HJ2|]. split; [exact HP2|].
intros a Ha Hno Hnp. apply Hmem2; [exact Ha | lia | exact Hnp].
Qed.
End S.
End c.
