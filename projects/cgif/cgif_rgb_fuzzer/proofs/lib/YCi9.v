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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c YI0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition GL_LOOP : Z := 0x85b54.
Definition GL_FLW : Z := 0x85bd8.
Definition GL_FLD : Z := 0x85bdc.
Definition GL_XORI : Z := 0x85be8.
Definition gl_lits (ocut : option Z) (leaf : Z) : list (option Z) :=
[None; None; None; None; None; None; None; ocut; None; Some leaf].
Definition EregD (regs : bvmap 5 word) (extra : list word) (bytes : list byte) : env :=
mkEnv (fun i => if (i <? 32)%nat then getr regs (Z_to_bv 5 (Z.of_nat i)) else nth (i - 32) extra (Z_to_bv 64 0))
(fun _ => bytes).
Lemma ew_EregD : forall regs extra bytes k, ew (EregD regs extra bytes) k = ew (Ereg regs extra) k.
Proof. reflexivity. Qed.
Lemma regs_ok_EregD : forall regs extra bytes, regs_ok (EregD regs extra bytes) sr_atoms regs.
Proof.
intros regs extra bytes. apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite Z.add_0_r, ew_EregD, ew_Ereg_lt by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regs ?x)) =>
let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity ]
| ]).
destruct Hr.
Qed.
Section GL.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Definition gl_post (regs0 f0 : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem0 md0 own lyc Sc (W : world trbsegs)
(mem : word -> option byte) (k : Z) (t : tree) : world trbsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists (fx' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs0 1) mem2 (seg_rom trbsegs)) md2 /\ frm_zero (@fp_csr fx') /\
(forall r : bv 5, In r TGLNI_FKEEP -> reg_get (@fp_regs fx') r = reg_get f0 r) /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs0 regs2 /\
(exists nl, In nl (tree_leaves t) /\ getr regs2 10 = w64 (tn_cidx nl)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - TGLNI_STK <= a < spZ regs0) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a).
Definition gl_G_stmt (t : tree) : Prop :=
forall (fy : FPState) (regs0 f0 regs : bvmap 5 word) mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (fb nF rgb : Z),
let sp := spZ regs0 in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memg md k ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - TGLNI_STK -> sp <= sp0 ->
frm_zero (@fp_csr fy) -> (forall r : bv 5, In r TGLNI_FKEEP -> reg_get (@fp_regs fy) r = reg_get f0 r) ->
getr regs 2 = w64 (sp - 16) -> getr regs 10 = w64 (troot t) -> getr regs 11 = w64 rgb -> getr regs 14 = w64 SB ->
getr regs 15 = w64 (2 ^ 64 - 1 - rgb) -> getr regs 16 = w64 2 -> getr regs 17 = w64 3 ->
(forall r : bv 5, In r CALLEE_SAVED -> r <> 2%bv -> getr regs r = getr regs0 r) ->
val_mem trbsegs (mrestrict (w_H W) memg) (sp - 8) 8 (bv_unsigned (getr regs0 1)) ->
In (fb, nF) (ablocks B lyc Sc) -> fb <= rgb -> rgb + 12 <= fb + nF -> rgb mod 4 = 0 ->
tree_full t -> tree_forall tnode_wf t -> tree_at trbsegs (mrestrict (w_H W) memg) t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TGLNI_STK <= a < sp) -> aview trbsegs (w_H W) memg a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memg a) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 GL_LOOP) memg (seg_rom trbsegs)) md)
(gl_post regs0 f0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k t).
Definition gl_alias : list (sv * sv) := [ (SAlu ALU_XOR (SOff 10 16) (SLit (-1)), SOff 43 0) ].
Definition gl_mem (ocut : option Z) (leaf : Z) : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 16 0 0 [YQ0b.mkChunk 8 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 33 (gl_lits ocut leaf)) ].
Definition gl_facts (inner : bool) : facts :=
mkFacts ([ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 2); (14%nat, mkAF SB SB 0);
(15%nat, mkAF 18446603336221196287 18446744073709547519 0); (41%nat, mkAF 0 255 0);
(43%nat, mkAF 18446603336221196287 18446744073709547519 0) ]
++ (if inner then [ (33%nat, mkAF 4096 140737479966720 4); (34%nat, mkAF 4096 140737479966720 4) ] else [])) [] gl_alias.
Definition gl_regs (g : nat) (cb : Z) : list sv :=
let base := sr_set (sr_set sr_atoms 16%bv (SLit 2)) 17%bv (SLit 3) in
match g with
| 0%nat => base
| _ => sr_set base 12%bv (SLit cb)
end.
Definition gl_pc (g : nat) : Z := match g with 0%nat => GL_LOOP | _ => GL_XORI end.
Definition gl_pin_facts (g : nat) (regs : bvmap 5 word) (cb : Z) : Prop :=
match g with
| 0%nat => True
| _ => getr regs 12 = w64 cb
end.
Definition ss_gl (g : nat) (ocut : option Z) (leaf cb : Z) (inner : bool) : sstate := mkSS (gl_pc g) (gl_regs g cb) (gl_mem ocut leaf) None (gl_facts inner).
Definition gl_Bx : sv := SOff 14 0.
Definition gl_SH : list shent := [ mkSHE 10 0 NODE_SIZE; mkSHE 11 0 12 ].
Definition gl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gl_extra (regs0 : bvmap 5 word) (c0 c1 : Z) (n : tnode) (leaf : Z) : list word :=
map (Z_to_bv 64) ([bv_unsigned (getr regs0 1)] ++ node_vals c0 c1 n leaf ++ [2 ^ 64 - 1 - (tn_addr n + 16)]) ++ [].
Lemma gl_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
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
Lemma gl_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; [exact H2|]. cbn [app atoms_ok] in *. destruct H1 as [Ha Hb]. split; [exact Ha | exact (IH Hb)]. Qed.
Lemma u64_range8' : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma gl_EN : forall regs regs0 c0 c1 n leaf j v, nth_error (node_vals c0 c1 n leaf) j = Some v ->
ew (Ereg regs (gl_extra regs0 c0 c1 n leaf)) (33 + j) = Z_to_bv 64 v.
Proof.
intros regs regs0 c0 c1 n leaf j v Hj. unfold gl_extra. change (33 + j)%nat with (32 + (1 + j))%nat. apply Ereg_vals.
cbn [app nth_error Nat.add]. rewrite nth_error_app1 by (apply nth_error_Some; congruence). exact Hj.
Qed.
Lemma gl_E43 : forall regs regs0 c0 c1 n leaf, length (tn_mean n) = 3%nat ->
ew (Ereg regs (gl_extra regs0 c0 c1 n leaf)) 43 = Z_to_bv 64 (2 ^ 64 - 1 - (tn_addr n + 16)).
Proof.
intros regs regs0 c0 c1 n leaf Hlen. unfold gl_extra. change 43%nat with (32 + 11)%nat. apply Ereg_vals.
cbn [app nth_error]. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity.
Qed.
Lemma gl_seed : forall (fy : FPState) (g : nat) (ocut : option Z) (cb : Z) (inner : bool) (regs0 regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k
(fb nF rgb : Z) (n : tnode) (c0 c1 leaf : Z),
let sp := spZ regs0 in
let E := Ereg regs (gl_extra regs0 c0 c1 n leaf) in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
sp mod 16 = 0 -> sp0 - STK <= sp - TGLNI_STK -> sp <= sp0 ->
getr regs 2 = w64 (sp - 16) -> getr regs 10 = w64 (tn_addr n) -> getr regs 11 = w64 rgb -> getr regs 14 = w64 SB ->
getr regs 15 = w64 (2 ^ 64 - 1 - rgb) -> getr regs 16 = w64 2 -> getr regs 17 = w64 3 ->
gl_pin_facts g regs cb -> (forall c, ocut = Some c -> tn_cut n = c) ->
val_mem trbsegs (mrestrict (w_H W) mem) (sp - 8) 8 (bv_unsigned (getr regs0 1)) ->
In (fb, nF) (ablocks B lyc Sc) -> fb <= rgb -> rgb + 12 <= fb + nF -> rgb mod 4 = 0 ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trbsegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n leaf) -> length (tn_mean n) = 3%nat ->
0 <= tn_cut n <= 2 ->
(inner = true -> In (c0, NODE_SIZE) (ablocks B lyc Sc) /\ In (c1, NODE_SIZE) (ablocks B lyc Sc)) ->
@st_ok trbsegs fy E (ss_gl g ocut leaf cb inner) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (gl_pc g)) mem (seg_rom trbsegs)))
/\ sh_ok trbsegs gl_Bx gl_SH E (mrestrict (w_H W) mem).
Proof.
intros fy g ocut cb inner regs0 regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb n c0 c1 leaf sp E
HJ Hal16 Hwlo Hwhi G2 G10 G11 G14 G15 G16 G17 Gpin Hoc Vra Hinf Hf1 Hf2 Hf4 Hinn Ond Hlen Hcut Hinner.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold TGLNI_STK in Hwlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & _ & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as Hnh_img.
change (req_size NODE_SIZE) with 56 in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR Hinf) as (_ & Hf4096 & Hfceil & Hfh_ia & _ & _ & HnF0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrnF].
pose proof (blk_off_img _ _ _ _ _ _ fb nF HAR Hinf) as Hfh_img.
pose proof (obj_at_nth trbsegs _ _ _ _ 8%nat (49, 1%N) (tn_cidx n) Ond eq_refl) as Fcidx.
assert (Hnv8 : nth_error (node_vals c0 c1 n leaf) 8 = Some (tn_cidx n)).
{ unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity. }
specialize (Fcidx Hnv8). destruct Fcidx as [_ Rcidx]. cbn [snd Z.of_N] in Rcidx. change (2 ^ (8 * 1)) with 256 in Rcidx.
rewrite restrict_mkst_fx.
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVN : forall j v, nth_error (node_vals c0 c1 n leaf) j = Some v -> ew E (33 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply gl_EN; exact Hj).
assert (E32 : ew E 32 = Z_to_bv 64 (bv_unsigned (getr regs0 1))) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E43 : ew E 43 = Z_to_bv 64 (2 ^ 64 - 1 - (tn_addr n + 16))) by (subst E; apply gl_E43; exact Hlen).
assert (E41 : ew E 41 = Z_to_bv 64 (tn_cidx n)) by (apply (HVN 8%nat); exact Hnv8).
assert (E2 : ew E 2 = getr regs 2) by (apply (HE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = w64 (tn_addr n)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = w64 rgb) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (E14 : ew E 14 = w64 SB) by (rewrite (HE 14%nat 14%bv eq_refl); exact G14).
assert (E15 : ew E 15 = w64 (2 ^ 64 - 1 - rgb)) by (rewrite (HE 15%nat 15%bv eq_refl); exact G15).
assert (Hspr : 0 <= sp - 16 < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 Hstk0; lia).
assert (U2 : bv_unsigned (ew E 2) = sp - 16) by (rewrite E2, G2; apply unsigned_lit_small; exact Hspr).
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
assert (Rrgb : 4096 <= rgb /\ rgb + 12 <= 140737479966720) by (clear - Hf4096 Hfceil Hf1 Hf2 HrnF C1; lia).
assert (U10 : bv_unsigned (ew E 10) = tn_addr n) by (rewrite E10; apply unsigned_lit_small; clear - Rn; lia).
assert (U11 : bv_unsigned (ew E 11) = rgb) by (rewrite E11; apply unsigned_lit_small; clear - Rrgb; lia).
assert (U15 : bv_unsigned (ew E 15) = 2 ^ 64 - 1 - rgb) by (rewrite E15; apply unsigned_lit_small; clear - Rrgb; lia).
assert (U43 : bv_unsigned (ew E 43) = 2 ^ 64 - 1 - (tn_addr n + 16)) by (rewrite E43; apply unsigned_lit_small; clear - Rn; lia).
split.
- unfold ss_gl. apply (entry_st_ok_full trbsegs).
+ assert (Hbase : regs_ok E (sr_set (sr_set sr_atoms 16%bv (SLit 2)) 17%bv (SLit 3)) regs).
{ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
- rewrite G16. reflexivity.
- rewrite G17. reflexivity. }
destruct g as [|g]; cbn [gl_regs gl_pin_facts] in *.
* exact Hbase.
* apply regs_ok_pin; [exact Hbase | intros HH0; discriminate HH0 |]. rewrite Gpin. reflexivity.
+ destruct g as [|g]; destruct inner; destruct ocut; vm_compute; reflexivity.
+ unfold gl_mem. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U2.
split; [clear - Hspr; lia|]. split; [clear - Hspr Hwhi Hshi H47; subst sp; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val trbsegs E _ (sp - 16) 8 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
[ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range8' | zside | ].
replace (sp - 16 + 8) with (sp - 8) by lia. exact Vra.
* eapply (region_ok_obj_gen trbsegs _ _ 10 (tn_addr n)); [exact U10 | lia | unfold NODE_SIZE; clear - Rn; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
do 7 (destruct j as [|j]; [cbn in Hj; congruence|]).
destruct j as [|j]; [cbn in Hj |- *; injection Hj as Hj; rewrite (Hoc z Hj); reflexivity|].
destruct j as [|j]; [cbn in Hj; congruence|]. destruct j as [|j]; [cbn in Hj |- *; congruence|]. destruct j; discriminate Hj.
+ apply pairwise_disjoint_of_extents. unfold gl_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U2, U10. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
subst sp. revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 Hstk0 Rn Hnceil. clear. intros. repeat split; lia.
+ split; [|split; [exact I|]].
* assert (Hch : inner = true -> (4096 <= c0 <= 140737479966720 /\ c0 mod 16 = 0) /\ (4096 <= c1 <= 140737479966720 /\ c1 mod 16 = 0)).
{ intros Hi. destruct (Hinner Hi) as [Hc0 Hc1].
destruct (al_blocks _ _ LAWS _ _ _ _ _ c0 NODE_SIZE HAR Hc0) as (Hc016 & Hc04096 & Hc0ceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c1 NODE_SIZE HAR Hc1) as (Hc116 & Hc14096 & Hc1ceil & _).
change (req_size NODE_SIZE) with 56 in *. clear - Hc016 Hc04096 Hc0ceil Hc116 Hc14096 Hc1ceil C1. lia. }
assert (E33 : ew E 33 = Z_to_bv 64 c0) by (apply (HVN 0%nat); reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 c1) by (apply (HVN 1%nat); reflexivity).
cbn [gl_facts f_atoms]. apply gl_atoms_ok_app; [|destruct inner; [|exact I]].
-- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U2, U10, U11, U15, U43, E14, E41, !unsigned_lit_small by (unfold SB; clear - Rcidx; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
subst sp. revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 C1 C3 Hstk0 Rn Hn16 Rrgb Hf4 Rcidx. clear.
unfold SB. intros. repeat match goal with |- _ /\ _ => split end; try lia.
replace (spZ regs0 - 16) with (spZ regs0 + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
-- destruct (Hch eq_refl) as [(R0 & A0) (R1 & A1)].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite E33, E34, !unsigned_lit_small by (clear - R0 R1; lia). change (2 ^ 4) with 16. clear - R0 A0 R1 A1. lia.
* cbn [gl_facts f_alias alias_ok gl_alias]. split; [|exact I].
fold E. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 10 (tn_addr n) 16 E10) by (clear - Rn; lia). rewrite U_SLit.
rewrite (U_atom E 43 (2 ^ 64 - 1 - (tn_addr n + 16)) E43) by (clear - Rn; lia).
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite gl_lxor_ones64 by (clear - Rn; lia). apply zcanon_id. unfold M64. clear - Rn. lia.
- unfold sh_ok, gl_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block trbsegs B LAWS lyc Sc W mem md E gl_Bx 10 (tn_addr n) NODE_SIZE 0 NODE_SIZE HAR Hinn).
* unfold U, gl_Bx. cbn [sv_denot]. rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
* lia.
* change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
+ apply (shent_ok_of_range trbsegs (w_H W) mem E gl_Bx 11 rgb 12 rgb 0 12).
* apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md fb nF _ _ HAR Hinf); clear - Hf1 Hf2 HrnF; lia.
* unfold U, gl_Bx. cbn [sv_denot]. rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U11.
* lia.
* lia.
* intros x Hx. revert Hx Hfh_ia Hfh_img Hf4096 Hfceil Hf1 Hf2 HrnF C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Lemma gl_root : forall m t, tree_full t -> tree_at trbsegs m t ->
exists n c0 c1 leafv, troot t = tn_addr n /\ In (tn_addr n, NODE_SIZE) (tree_blocks t) /\ length (tn_mean n) = 3%nat /\
obj_at trbsegs m (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) /\ (leafv = 0 \/ leafv = 1).
Proof.
intros m t Hf Hat. destruct t as [|n|n l r]; [destruct Hf | |]; cbn [tree_at troot tree_blocks] in *.
- destruct Hat as (_ & Hlen & c0 & c1 & Ho). exists n, c0, c1, 1. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. right. reflexivity.
- destruct Hat as (_ & Hlen & Ho & _ & _). exists n, (troot l), (troot r), 0. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Ho|]. left. reflexivity.
Qed.
Definition ss_glB0 : sstate :=
mkSS GL_FLW sr_atoms [ YQ0b.mkRegion (Some 12%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CData 0 0 4)] ] None
(mkFacts [ (12%nat, mkAF 4096 140737479966720 2) ] [] []).
Lemma gl_bytes_of_present : forall (H : word -> bool) (m : word -> option byte) a n,
(forall i, 0 <= i < Z.of_nat n -> apresent H m (a + i)) ->
exists bs, length bs = n /\ forall i, (i < n)%nat -> mbyte trbsegs (mrestrict H m) (a + Z.of_nat i) = nth_error bs i.
Proof.
intros H m a n HP.
exists (map (fun i => match mbyte trbsegs (mrestrict H m) (a + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
split; [rewrite length_map, length_seq; reflexivity|].
intros i Hi. rewrite nth_error_map. rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hi).
rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
destruct (HP (Z.of_nat i) ltac:(lia)) as [Hh [b Hb]]. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.
Lemma glB_entry : forall (fy : FPState) (H : word -> bool) (regs : bvmap 5 word) mem (a : Z) (bytes : list byte),
getr regs 12 = w64 a -> 4096 <= a -> a + 4 <= 140737479966720 -> a mod 4 = 0 ->
length bytes = 4%nat -> (forall i, (i < 4)%nat -> mbyte trbsegs (mrestrict H mem) (a + Z.of_nat i) = nth_error bytes i) ->
@st_ok trbsegs fy (EregD regs [] bytes) ss_glB0 (restrict H (@mkst fy regs (Z_to_bv 64 GL_FLW) mem (seg_rom trbsegs))).
Proof.
intros fy H regs mem a bytes Hr12 Ha0 Ha1 Ha4 Hbl Hbytes.
rewrite restrict_mkst_fx.
assert (HU12 : bv_unsigned (ew (EregD regs [] bytes) 12) = a).
{ rewrite ew_EregD, (ew_Ereg_nat regs [] 12 12%bv eq_refl), Hr12. apply unsigned_lit_small. lia. }
unfold ss_glB0. apply (entry_st_ok_env trbsegs).
- apply regs_ok_EregD.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite HU12.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
cbn [ed EregD]. rewrite Z.add_0_l, Z.add_0_r.
destruct (nth_error bytes (Z.to_nat i)) as [b|] eqn:Hb.
+ exists b. split; [reflexivity|]. rewrite <- Hb, <- (Hbytes (Z.to_nat i)) by lia. rewrite Z2Nat.id by lia. reflexivity.
+ exfalso. apply nth_error_None in Hb. lia.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU12.
change (2 ^ 2) with 4. repeat split; lia.
Qed.
Definition GL_KL : list (bv 5) := [1; 2; 3; 4; 8; 9; 11; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition gl_inv (regs0 regs : bvmap 5 word) (H : word -> bool) (m : word -> option byte) (rgb : Z) : Prop :=
getr regs 2 = w64 (spZ regs0 - 16) /\ getr regs 11 = w64 rgb /\ getr regs 14 = w64 SB /\ getr regs 15 = w64 (2 ^ 64 - 1 - rgb) /\
getr regs 16 = w64 2 /\ getr regs 17 = w64 3 /\
(forall r : bv 5, In r CALLEE_SAVED -> r <> 2%bv -> getr regs r = getr regs0 r) /\
val_mem trbsegs (mrestrict H m) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)).
Lemma gl_inv_step : forall regs0 regs regs' H m m' rgb,
gl_inv regs0 regs H m rgb -> (forall r : bv 5, In r GL_KL -> getr regs' r = getr regs r) ->
getr regs' 16 = w64 2 -> getr regs' 17 = w64 3 ->
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs H m' a = aview trbsegs H m a) -> 0 <= spZ regs0 - 16 -> spZ regs0 < 2 ^ 64 ->
gl_inv regs0 regs' H m' rgb.
Proof.
intros regs0 regs regs' H m m' rgb (I2 & I11 & I14 & I15 & I16 & I17 & IK & IV) KL G16 G17 SAME Hs1 Hs2.
split; [rewrite (KL (2%bv : bv 5) ltac:(cbv; tauto)); exact I2|].
split; [rewrite (KL (11%bv : bv 5) ltac:(cbv; tauto)); exact I11|].
split; [rewrite (KL (14%bv : bv 5) ltac:(cbv; tauto)); exact I14|].
split; [rewrite (KL (15%bv : bv 5) ltac:(cbv; tauto)); exact I15|].
split; [exact G16|]. split; [exact G17|]. split.
- intros r Hr N2. rewrite (KL r ltac:(cbv [CALLEE_SAVED In] in Hr; cbv [GL_KL In]; intuition)). exact (IK r Hr N2).
- apply (YCcz.val_mem_kept trbsegs H H m m' _ 8 _); [|exact IV]. intros kk Hkk. apply SAME. cbn in Hkk. lia.
Qed.
Lemma gl_blk_same : forall ly S W mem md (m m' : word -> option byte),
AR trbsegs B ly S W mem md -> (forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) m' a = aview trbsegs (w_H W) m a) ->
forall b sz, In (b, sz) (ablocks B ly S) -> rg_blk_kept (w_H W) (w_H W) m m' b (req_size sz).
Proof.
intros ly S W mem md m m' HAR SAME b sz Hb i Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR Hb) as (_ & Hb4096 & Hbceil & _). pose proof asan_consts as (C1 & _).
apply SAME. lia.
Qed.
Definition ss_glC0 : sstate :=
mkSS GL_FLD sr_atoms [ YQ0b.mkRegion (Some 13%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (13%nat, mkAF 4096 140737479966720 0) ] [] []).
Lemma glC_entry : forall (fy : FPState) (H : word -> bool) (regs : bvmap 5 word) mem (a v : Z),
getr regs 13 = w64 a -> 4096 <= a -> a + 8 <= 140737479966720 ->
val_mem trbsegs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 ->
@st_ok trbsegs fy (Ereg regs [Z_to_bv 64 v]) ss_glC0 (restrict H (@mkst fy regs (Z_to_bv 64 GL_FLD) mem (seg_rom trbsegs))).
Proof.
intros fy H regs mem a v Hr13 Ha0 Ha1 Hv Rv.
rewrite restrict_mkst_fx.
assert (HU13 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 v]) 13) = a).
{ rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), Hr13. apply unsigned_lit_small. lia. }
unfold ss_glC0. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite HU13.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val trbsegs _ _ a 0 8 (SOff 32 0) v);
[ cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r; cbn [nth]; rewrite Z_to_bv_bv_unsigned; reflexivity | exact Rv | zside | ].
rewrite Z.add_0_r. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU13.
rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.
Lemma gl_mean_cell : forall m c0 c1 n leaf, length (tn_mean n) = 3%nat -> 0 <= tn_cut n <= 2 ->
obj_at trbsegs m (tn_addr n) LAY_Node (node_vals c0 c1 n leaf) ->
exists v, val_mem trbsegs m (tn_addr n + (16 + 8 * tn_cut n)) 8 v /\ 0 <= v < 2 ^ 64.
Proof.
intros m c0 c1 n leaf Hlen Hcut Ond.
assert (Hc3 : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by lia.
unfold node_vals in Ond. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
destruct Hc3 as [Hc | [Hc | Hc]]; rewrite Hc.
- destruct (obj_at_nth trbsegs _ _ _ _ 2%nat (16, 8%N) m0 Ond eq_refl eq_refl) as [V R]. exists m0. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in V, R. split; [exact V | exact R].
- destruct (obj_at_nth trbsegs _ _ _ _ 3%nat (24, 8%N) m1 Ond eq_refl eq_refl) as [V R]. exists m1. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in V, R. split; [exact V | exact R].
- destruct (obj_at_nth trbsegs _ _ _ _ 4%nat (32, 8%N) m2 Ond eq_refl eq_refl) as [V R]. exists m2. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in V, R. split; [exact V | exact R].
Qed.
Lemma gl_BCD : forall n l r, gl_G_stmt l -> gl_G_stmt r ->
forall (fy : FPState) (regs0 f0 regs : bvmap 5 word) mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (fb nF rgb : Z),
let sp := spZ regs0 in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memg md k ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 -> sp0 - STK <= sp - TGLNI_STK -> sp <= sp0 ->
frm_zero (@fp_csr fy) -> (forall r0 : bv 5, In r0 TGLNI_FKEEP -> reg_get (@fp_regs fy) r0 = reg_get f0 r0) ->
gl_inv regs0 regs (w_H W) memg rgb -> getr regs 10 = w64 (tn_addr n) ->
getr regs 12 = w64 (rgb + 4 * tn_cut n) -> getr regs 13 = w64 (tn_addr n + (16 + 8 * tn_cut n)) ->
In (fb, nF) (ablocks B lyc Sc) -> fb <= rgb -> rgb + 12 <= fb + nF -> rgb mod 4 = 0 ->
tree_full (TNode n l r) -> tree_forall tnode_wf (TNode n l r) -> tree_at trbsegs (mrestrict (w_H W) memg) (TNode n l r) ->
(forall b, In b (tree_blocks (TNode n l r)) -> In b (ablocks B lyc Sc)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TGLNI_STK <= a < sp) -> aview trbsegs (w_H W) memg a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memg a) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 GL_FLW) memg (seg_rom trbsegs)) md)
(gl_post regs0 f0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem k (TNode n l r)).
Proof.
intros n l r HGl HGr fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb sp
HJ Hra Hal16 Hwlo Hwhi Hfrm HFK INV G10 G12 G13 Hinf Hf1 Hf2 Hf4 Hfull Hwf Hat Hblk KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & Ond & Hatl & Hatr).
cbn [tree_full] in Hfull. destruct Hfull as [Hfl Hfr].
apply tree_forall_node in Hwf. destruct Hwf as (Hwfn & Hwfl & Hwfr).
destruct Hwfn as (Hcut & Hcidx & _).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
assert (Hblkl : forall b, In b (tree_blocks l) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; left; exact Hb).
assert (Hblkr : forall b, In b (tree_blocks r) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; right; exact Hb).
destruct (gl_root _ l Hfl Hatl) as (nl & cl0 & cl1 & lvl & Hrootl & Hinbl & _).
destruct (gl_root _ r Hfr Hatr) as (nr & cr0 & cr1 & lvr & Hrootr & Hinbr & _).
assert (Hinner : true = true -> In (troot l, NODE_SIZE) (ablocks B lyc Sc) /\ In (troot r, NODE_SIZE) (ablocks B lyc Sc)).
{ intros _. split; [rewrite Hrootl; apply Hblkl; exact Hinbl | rewrite Hrootr; apply Hblkr; exact Hinbr]. }
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold TGLNI_STK in Hwlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR0 Hinn) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR0 Hinf) as (_ & Hf4096 & Hfceil & _ & HPf & _ & HnF0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrnF].
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
assert (Rrgb : 4096 <= rgb /\ rgb + 12 <= 140737479966720) by (clear - Hf4096 Hfceil Hf1 Hf2 HrnF C1; lia).
assert (Hspr : 0 <= sp - 16 /\ sp < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 Hstk0; lia).
destruct (gl_bytes_of_present (w_H W) memg (rgb + 4 * tn_cut n) 4
ltac:(intros i Hi; apply (proj1 (HPf (rgb + 4 * tn_cut n + i) ltac:(cbn in Hi; clear - Hi Hf1 Hf2 HrnF Hcut; lia)))))
as (bytes & Hbl & Hbytes).
pose proof (glB_entry fy (w_H W) regs memg (rgb + 4 * tn_cut n) bytes G12
ltac:(clear - Rrgb Hcut; lia) ltac:(clear - Rrgb Hcut; lia)
ltac:(clear - Hf4 Hcut; replace (rgb + 4 * tn_cut n) with (rgb + tn_cut n * 4) by lia; rewrite Z_mod_plus_full; exact Hf4) Hbl Hbytes) as HSB0.
pose proof (st_ok_enterF trbsegs fy 32 _ _ _ HSB0 ltac:(vm_compute; reflexivity) Hfrm) as HSB.
set (EB := ew_fregs (EregD regs [] bytes) 32 (@fp_regs fy)) in *.
assert (SHOKB : sh_ok trbsegs gl_Bx [] EB (mrestrict (w_H W) memg)) by constructor.
assert (HEfB : forall r0 : bv 5, ew EB (32 + ridx r0)%nat = reg_get (@fp_regs fy) r0) by (intros r0; apply ew_fregs_at).
assert (HExB : forall r0 : bv 5, ew EB (ridx r0) = getr regs r0).
{ intros r0. subst EB. rewrite ew_fregs_low by (pose proof (u5_range r0); unfold ridx; lia). rewrite ew_EregD. unfold ridx. apply ew_Ereg_reg. }
clear HSB0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_glB0] in HSB.
aj_run_to_tokF trbtbl_lib_ok HSB HJ SHOKB gl_Bspan GL_FLD; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msB := msx) in * end.
assert (SAMEB : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msB) a = aview trbsegs (w_H W) memg a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRB : forall a, apresent (w_H W) memg a -> apresent (w_H W) (ms_mem msB) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
pose proof (st_okF_regs_kept trbsegs _ _ _ regs ([10; 13; 16; 17]%bv ++ GL_KL) HSB ltac:(intros r0 _; apply HExB) ltac:(vm_compute; reflexivity)) as KB. cbn [ms_regs restrict] in KB.
pose proof (st_okF_fregs_kept trbsegs _ _ _ 32 (@fp_regs fy) TGLNI_FKEEP HSB HEfB ltac:(vm_compute; reflexivity)) as FKB. cbn [ms_fregs restrict] in FKB.
pose proof INV as (I2 & I11 & I14 & I15 & I16 & I17 & IK & IV).
assert (INVB : gl_inv regs0 (ms_regs msB) (w_H W) (ms_mem msB) rgb).
{ apply (gl_inv_step regs0 regs _ _ memg _ rgb INV); [intros r0 Hr0; apply KB; apply in_or_app; right; exact Hr0 | | | exact SAMEB | apply Hspr | apply Hspr].
- rewrite (KB (16%bv : bv 5) ltac:(cbv; tauto)). exact I16.
- rewrite (KB (17%bv : bv 5) ltac:(cbv; tauto)). exact I17. }
assert (G10B : getr (ms_regs msB) 10 = w64 (tn_addr n)) by (rewrite (KB (10%bv : bv 5) ltac:(cbv; tauto)); exact G10).
assert (G13B : getr (ms_regs msB) 13 = w64 (tn_addr n + (16 + 8 * tn_cut n))) by (rewrite (KB (13%bv : bv 5) ltac:(cbv; tauto)); exact G13).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msB) HAR0 SAMEB) as BKB.
assert (OndB : obj_at trbsegs (mrestrict (w_H W) (ms_mem msB)) (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0))
by (apply (rg_obj_at_blk_kept (w_H W) (w_H W) memg (ms_mem msB) (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)); exact (BKB _ _ Hinn)).
pose proof (st_okF_frm trbsegs _ _ _ HSB) as HfrmB.
pose proof (st_okF_to_legacy trbsegs _ _ _ HSB) as HSBL.
rewrite (@st_ok_restrict_mkst trbsegs (fp_of (restrict (w_H W) msB)) (w_H W) _ _ msB HSBL eq_refl); cbn [ss_pc].
destruct (gl_mean_cell _ _ _ n 0 Hlen Hcut OndB) as (mv & Vmv & Rmv).
pose proof (glC_entry (fp_of (restrict (w_H W) msB)) (w_H W) (ms_regs msB) (ms_mem msB) (tn_addr n + (16 + 8 * tn_cut n)) mv G13B ltac:(clear - Rn Hcut; lia) ltac:(clear - Hnceil C1 Hcut; lia) Vmv Rmv) as HSC0.
pose proof (st_ok_enterF trbsegs (fp_of (restrict (w_H W) msB)) 33 _ _ _ HSC0 ltac:(vm_compute; reflexivity) HfrmB) as HSC.
set (EC := ew_fregs (Ereg (ms_regs msB) [Z_to_bv 64 mv]) 33 (@fp_regs (fp_of (restrict (w_H W) msB)))) in *.
assert (SHOKC : sh_ok trbsegs gl_Bx [] EC (mrestrict (w_H W) (ms_mem msB))) by constructor.
assert (HEfC : forall r0 : bv 5, ew EC (33 + ridx r0)%nat = reg_get (@fp_regs (fp_of (restrict (w_H W) msB))) r0) by (intros r0; apply ew_fregs_at).
assert (HExC : forall r0 : bv 5, ew EC (ridx r0) = getr (ms_regs msB) r0).
{ intros r0. subst EC. rewrite ew_fregs_low by (pose proof (u5_range r0); unfold ridx; lia). unfold ridx. apply ew_Ereg_reg. }
clear HSC0 HSB HSBL SHOKB. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_glC0] in HSC.
aj_run_to_tokF trbtbl_lib_ok HSC HJ SHOKC gl_Bspan GL_XORI; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msC := msx) in * end.
assert (SAMEC : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msC) a = aview trbsegs (w_H W) (ms_mem msB) a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRC : forall a, apresent (w_H W) (ms_mem msB) a -> apresent (w_H W) (ms_mem msC) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
pose proof (st_okF_regs_kept trbsegs _ _ _ (ms_regs msB) ([10; 16; 17]%bv ++ GL_KL) HSC ltac:(intros r0 _; apply HExC) ltac:(vm_compute; reflexivity)) as KC. cbn [ms_regs restrict] in KC.
pose proof (st_okF_fregs_kept trbsegs _ _ _ 33 _ TGLNI_FKEEP HSC HEfC ltac:(vm_compute; reflexivity)) as FKC. cbn [ms_fregs restrict fp_regs fp_of] in FKC.
pose proof (st_okF_reg trbsegs _ _ _ (12%bv : bv 5) HSC) as RC12. cbn [ms_regs restrict] in RC12.
lazymatch type of RC12 with _ = sv_denot ?Ex ?e => let e' := eval vm_compute in e in change e with e' in RC12 end.
cbn [sv_denot] in RC12. rewrite fcmp_denot in RC12.
pose proof INVB as (IB2 & IB11 & IB14 & IB15 & IB16 & IB17 & IBK & IBV).
assert (INVC : gl_inv regs0 (ms_regs msC) (w_H W) (ms_mem msC) rgb).
{ apply (gl_inv_step regs0 (ms_regs msB) _ _ (ms_mem msB) _ rgb INVB); [intros r0 Hr0; apply KC; apply in_or_app; right; exact Hr0 | | | exact SAMEC | apply Hspr | apply Hspr].
- rewrite (KC (16%bv : bv 5) ltac:(cbv; tauto)). exact IB16.
- rewrite (KC (17%bv : bv 5) ltac:(cbv; tauto)). exact IB17. }
pose proof INVC as (IC2 & IC11 & IC14 & IC15 & IC16 & IC17 & ICK & ICV).
assert (G10C : getr (ms_regs msC) 10 = w64 (tn_addr n)) by (rewrite (KC (10%bv : bv 5) ltac:(cbv; tauto)); exact G10B).
assert (SAMEBC : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msC) a = aview trbsegs (w_H W) memg a)
by (intros a Ha; rewrite (SAMEC a Ha); exact (SAMEB a Ha)).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msC) HAR0 SAMEBC) as BKC.
assert (OndC : obj_at trbsegs (mrestrict (w_H W) (ms_mem msC)) (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0))
by (apply (rg_obj_at_blk_kept (w_H W) (w_H W) memg (ms_mem msC) (tn_addr n) LAY_Node _ NODE_SIZE Ond (proj1 lay_inside_Node)); exact (BKC _ _ Hinn)).
pose proof (st_okF_frm trbsegs _ _ _ HSC) as HfrmC.
pose proof (st_okF_to_legacy trbsegs _ _ _ HSC) as HSCL.
assert (FKall : forall r0 : bv 5, In r0 TGLNI_FKEEP -> reg_get (@fp_regs (fp_of (restrict (w_H W) msC))) r0 = reg_get f0 r0).
{ intros r0 Hr0. cbn [fp_regs fp_of restrict ms_fregs]. rewrite (FKC r0 Hr0). cbn [fp_regs fp_of restrict ms_fregs]. rewrite (FKB r0 Hr0). exact (HFK r0 Hr0). }
rewrite (@st_ok_restrict_mkst trbsegs (fp_of (restrict (w_H W) msC)) (w_H W) _ _ msC HSCL eq_refl); cbn [ss_pc].
clear HSC HSCL SHOKC.
lazymatch type of RC12 with _ = (if ?c then _ else _) => destruct c end.
-
destruct (gl_seed (fp_of (restrict (w_H W) msC)) 1%nat None 1 true regs0 (ms_regs msC) (ms_mem msC) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb n (troot l) (troot r) 0
HJ Hal16 Hwlo Hwhi IC2 G10C IC11 IC14 IC15 IC16 IC17 RC12 ltac:(intros c0 X; discriminate X) ICV Hinf Hf1 Hf2 Hf4 Hinn OndC Hlen Hcut Hinner) as [HSD SHOKD].
set (ED := Ereg (ms_regs msC) (gl_extra regs0 (troot l) (troot r) n 0)) in *.
assert (HAED : env_agree 32 (Ereg (ms_regs msC) (gl_extra regs0 (troot l) (troot r) n 0)) ED) by (split; [intros m0' Hm0'; reflexivity | reflexivity]).
cbn [ss_gl gl_pc gl_regs] in HSD.
aj_run_to_tok trbtbl_lib_ok HSD HJ SHOKD gl_Bspan GL_LOOP; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msD := msx) in * end.
assert (SAMED : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msD) a = aview trbsegs (w_H W) (ms_mem msC) a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRD : forall a, apresent (w_H W) (ms_mem msC) a -> apresent (w_H W) (ms_mem msD) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
lazymatch type of HSD with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 (Ereg (ms_regs msC) (gl_extra regs0 (troot l) (troot r) n 0)) Ex) by (env_agree_chain HAED) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ (ms_regs msC) _ GL_KL HSD HAEx ltac:(vm_compute; reflexivity)) as KD. cbn [ms_regs restrict] in KD.
rreg HSD (10%bv : bv 5) RD10. rreg HSD (16%bv : bv 5) RD16. rreg HSD (17%bv : bv 5) RD17.
assert (INVD : gl_inv regs0 (ms_regs msD) (w_H W) (ms_mem msD) rgb)
by (apply (gl_inv_step regs0 (ms_regs msC) _ _ (ms_mem msC) _ rgb INVC); [exact KD | rewrite RD16; reflexivity | rewrite RD17; reflexivity | exact SAMED | apply Hspr | apply Hspr]).
pose proof INVD as (ID2 & ID11 & ID14 & ID15 & ID16 & ID17 & IDK & IDV).
assert (G10D : getr (ms_regs msD) 10 = w64 (troot l)).
{ rewrite RD10. subst ED. exact (gl_EN (ms_regs msC) regs0 (troot l) (troot r) n 0 0%nat (troot l) eq_refl). }
assert (SAMEALL : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msD) a = aview trbsegs (w_H W) memg a)
by (intros a Ha; rewrite (SAMED a Ha); exact (SAMEBC a Ha)).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msD) HAR0 SAMEALL) as BKD.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msD HSD eq_refl); cbn [ss_pc].
eapply SRr_mono.
{ eapply (HGl (fp_of (restrict (w_H W) msC)) regs0 f0 (ms_regs msD) mem (ms_mem msD) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb
HJ Hra Hal16 Hwlo Hwhi HfrmC FKall ID2 G10D ID11 ID14 ID15 ID16 ID17 IDK IDV Hinf Hf1 Hf2 Hf4 Hfl Hwfl).
- apply (rg_tree_at_kept (w_H W) (w_H W) memg (ms_mem msD) l Hatl). intros b sz Hb. apply BKD. exact (Hblkl _ Hb).
- exact Hblkl.
- intros a Ha Hn. rewrite (SAMEALL a Ha). exact (KEEP a Ha Hn).
- intros a Ha. apply PRD. apply PRC. apply PRB. apply PR. exact Ha. }
intros W' c' _ (HW & fx' & regs2 & mem2 & md2 & Hc' & Hfz & HFK' & HJ2 & Hpr & (nlf & Hnlf & Ha0) & Hk2 & Hp2).
split; [exact HW|]. exists fx', regs2, mem2, md2.
split; [exact Hc'|]. split; [exact Hfz|]. split; [exact HFK'|]. split; [exact HJ2|]. split; [exact Hpr|].
split; [exists nlf; split; [cbn [tree_leaves]; apply in_or_app; left; exact Hnlf | exact Ha0]|].
split; [exact Hk2 | exact Hp2].
-
destruct (gl_seed (fp_of (restrict (w_H W) msC)) 1%nat None 0 true regs0 (ms_regs msC) (ms_mem msC) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb n (troot l) (troot r) 0
HJ Hal16 Hwlo Hwhi IC2 G10C IC11 IC14 IC15 IC16 IC17 RC12 ltac:(intros c0 X; discriminate X) ICV Hinf Hf1 Hf2 Hf4 Hinn OndC Hlen Hcut Hinner) as [HSD SHOKD].
set (ED := Ereg (ms_regs msC) (gl_extra regs0 (troot l) (troot r) n 0)) in *.
assert (HAED : env_agree 32 (Ereg (ms_regs msC) (gl_extra regs0 (troot l) (troot r) n 0)) ED) by (split; [intros m0' Hm0'; reflexivity | reflexivity]).
cbn [ss_gl gl_pc gl_regs] in HSD.
aj_run_to_tok trbtbl_lib_ok HSD HJ SHOKD gl_Bspan GL_LOOP; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msD := msx) in * end.
assert (SAMED : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msD) a = aview trbsegs (w_H W) (ms_mem msC) a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRD : forall a, apresent (w_H W) (ms_mem msC) a -> apresent (w_H W) (ms_mem msD) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
lazymatch type of HSD with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 (Ereg (ms_regs msC) (gl_extra regs0 (troot l) (troot r) n 0)) Ex) by (env_agree_chain HAED) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ (ms_regs msC) _ GL_KL HSD HAEx ltac:(vm_compute; reflexivity)) as KD. cbn [ms_regs restrict] in KD.
rreg HSD (10%bv : bv 5) RD10. rreg HSD (16%bv : bv 5) RD16. rreg HSD (17%bv : bv 5) RD17.
assert (INVD : gl_inv regs0 (ms_regs msD) (w_H W) (ms_mem msD) rgb)
by (apply (gl_inv_step regs0 (ms_regs msC) _ _ (ms_mem msC) _ rgb INVC); [exact KD | rewrite RD16; reflexivity | rewrite RD17; reflexivity | exact SAMED | apply Hspr | apply Hspr]).
pose proof INVD as (ID2 & ID11 & ID14 & ID15 & ID16 & ID17 & IDK & IDV).
assert (G10D : getr (ms_regs msD) 10 = w64 (troot r)).
{ rewrite RD10. subst ED. exact (gl_EN (ms_regs msC) regs0 (troot l) (troot r) n 0 1%nat (troot r) eq_refl). }
assert (SAMEALL : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msD) a = aview trbsegs (w_H W) memg a)
by (intros a Ha; rewrite (SAMED a Ha); exact (SAMEBC a Ha)).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msD) HAR0 SAMEALL) as BKD.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msD HSD eq_refl); cbn [ss_pc].
eapply SRr_mono.
{ eapply (HGr (fp_of (restrict (w_H W) msC)) regs0 f0 (ms_regs msD) mem (ms_mem msD) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb
HJ Hra Hal16 Hwlo Hwhi HfrmC FKall ID2 G10D ID11 ID14 ID15 ID16 ID17 IDK IDV Hinf Hf1 Hf2 Hf4 Hfr Hwfr).
- apply (rg_tree_at_kept (w_H W) (w_H W) memg (ms_mem msD) r Hatr). intros b sz Hb. apply BKD. exact (Hblkr _ Hb).
- exact Hblkr.
- intros a Ha Hn. rewrite (SAMEALL a Ha). exact (KEEP a Ha Hn).
- intros a Ha. apply PRD. apply PRC. apply PRB. apply PR. exact Ha. }
intros W' c' _ (HW & fx' & regs2 & mem2 & md2 & Hc' & Hfz & HFK' & HJ2 & Hpr & (nlf & Hnlf & Ha0) & Hk2 & Hp2).
split; [exact HW|]. exists fx', regs2, mem2, md2.
split; [exact Hc'|]. split; [exact Hfz|]. split; [exact HFK'|]. split; [exact HJ2|]. split; [exact Hpr|].
split; [exists nlf; split; [cbn [tree_leaves]; apply in_or_app; right; exact Hnlf | exact Ha0]|].
split; [exact Hk2 | exact Hp2].
Qed.
Lemma gl_node : forall n l r, gl_G_stmt l -> gl_G_stmt r -> gl_G_stmt (TNode n l r).
Proof.
intros n l r HGl HGr fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb sp
HJ Hra Hal16 Hwlo Hwhi Hfrm HFK G2 G10 G11 G14 G15 G16 G17 Gkeep Vra Hinf Hf1 Hf2 Hf4 HfullN HwfN HatN Hblk KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
cbn [troot] in G10. pose proof HatN as Hat. cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & Ond & Hatl & Hatr).
pose proof HfullN as Hfull. cbn [tree_full] in Hfull. destruct Hfull as [Hfl Hfr].
pose proof HwfN as Hwf. apply tree_forall_node in Hwf. destruct Hwf as (Hwfn & Hwfl & Hwfr).
destruct Hwfn as (Hcut & Hcidx & _).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
assert (Hblkl : forall b, In b (tree_blocks l) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; left; exact Hb).
assert (Hblkr : forall b, In b (tree_blocks r) -> In b (ablocks B lyc Sc)) by (intros b Hb; apply Hblk; right; apply in_app_iff; right; exact Hb).
destruct (gl_root _ l Hfl Hatl) as (nl & cl0 & cl1 & lvl & Hrootl & Hinbl & _).
destruct (gl_root _ r Hfr Hatr) as (nr & cr0 & cr1 & lvr & Hrootr & Hinbr & _).
assert (Hinner : true = true -> In (troot l, NODE_SIZE) (ablocks B lyc Sc) /\ In (troot r, NODE_SIZE) (ablocks B lyc Sc)).
{ intros _. split; [rewrite Hrootl; apply Hblkl; exact Hinbl | rewrite Hrootr; apply Hblkr; exact Hinbr]. }
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold TGLNI_STK in Hwlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR0 Hinn) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR0 Hinf) as (_ & Hf4096 & Hfceil & _ & _ & _ & HnF0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrnF].
assert (Rn : 4096 <= tn_addr n <= 140737479966720) by (clear - Hn4096 Hnceil C1; lia).
assert (Rrgb : 4096 <= rgb /\ rgb + 12 <= 140737479966720) by (clear - Hf4096 Hfceil Hf1 Hf2 HrnF C1; lia).
assert (Hspr : 0 <= sp - 16 /\ sp < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 Hstk0; lia).
assert (INV0 : gl_inv regs0 regs (w_H W) memg rgb) by (unfold gl_inv; tauto).
destruct (gl_seed fy 0%nat (Some (tn_cut n)) 0 true regs0 regs memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb n (troot l) (troot r) 0
HJ Hal16 Hwlo Hwhi G2 G10 G11 G14 G15 G16 G17 I ltac:(intros c0 X; injection X as <-; reflexivity) Vra Hinf Hf1 Hf2 Hf4 Hinn Ond Hlen Hcut Hinner) as [HS SHOK].
set (E := Ereg regs (gl_extra regs0 (troot l) (troot r) n 0)) in *.
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HAE : env_agree 32 (Ereg regs (gl_extra regs0 (troot l) (troot r) n 0)) E) by (split; [intros m Hm; reflexivity | reflexivity]).
assert (Hc3 : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by (clear - Hcut; lia).
destruct Hc3 as [Hc | [Hc | Hc]]; rewrite Hc in HS.
-
cbn [ss_gl gl_pc gl_regs] in HS.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK gl_Bspan GL_FLW; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (SAMEA : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) memg a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRA : forall a, apresent (w_H W) memg a -> apresent (w_H W) (ms_mem msA) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 (Ereg regs (gl_extra regs0 (troot l) (troot r) n 0)) Ex) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ (10%bv :: GL_KL) HS HAEx ltac:(vm_compute; reflexivity)) as KA. cbn [ms_regs restrict] in KA.
rreg HS (12%bv : bv 5) RA12. rreg HS (13%bv : bv 5) RA13. rreg HS (16%bv : bv 5) RA16. rreg HS (17%bv : bv 5) RA17.
assert (G12A : getr (ms_regs msA) 12 = w64 (rgb + 4 * tn_cut n))
by (rewrite RA12, Hc, (ER 11%nat 11%bv eq_refl), G11; unfold w64; rewrite ?unsigned_lit_small by (clear - Rrgb; lia); f_equal; lia).
assert (G13A : getr (ms_regs msA) 13 = w64 (tn_addr n + (16 + 8 * tn_cut n)))
by (rewrite RA13, Hc, (ER 10%nat 10%bv eq_refl), G10; unfold w64; rewrite ?unsigned_lit_small by (clear - Rn; lia); f_equal; lia).
assert (INVA : gl_inv regs0 (ms_regs msA) (w_H W) (ms_mem msA) rgb)
by (apply (gl_inv_step regs0 regs _ _ memg _ rgb INV0); [intros r0 Hr0; apply KA; right; exact Hr0 | rewrite RA16; reflexivity | rewrite RA17; reflexivity | exact SAMEA | apply Hspr | apply Hspr]).
assert (G10A : getr (ms_regs msA) 10 = w64 (tn_addr n)) by (rewrite (KA (10%bv : bv 5) ltac:(left; reflexivity)); exact G10).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msA) HAR0 SAMEA) as BKA.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msA HS eq_refl); cbn [ss_pc].
eapply (gl_BCD n l r HGl HGr fy regs0 f0 (ms_regs msA) mem (ms_mem msA) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb
HJ Hra Hal16 Hwlo Hwhi Hfrm HFK INVA G10A G12A G13A Hinf Hf1 Hf2 Hf4 HfullN HwfN).
+ apply (rg_tree_at_kept (w_H W) (w_H W) memg (ms_mem msA) (TNode n l r) HatN). intros b sz Hb. apply BKA. exact (Hblk _ Hb).
+ exact Hblk.
+ intros a Ha Hn. rewrite (SAMEA a Ha). exact (KEEP a Ha Hn).
+ intros a Ha. apply PRA. apply PR. exact Ha.
-
cbn [ss_gl gl_pc gl_regs] in HS.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK gl_Bspan GL_FLW; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (SAMEA : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) memg a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRA : forall a, apresent (w_H W) memg a -> apresent (w_H W) (ms_mem msA) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 (Ereg regs (gl_extra regs0 (troot l) (troot r) n 0)) Ex) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ (10%bv :: GL_KL) HS HAEx ltac:(vm_compute; reflexivity)) as KA. cbn [ms_regs restrict] in KA.
rreg HS (12%bv : bv 5) RA12. rreg HS (13%bv : bv 5) RA13. rreg HS (16%bv : bv 5) RA16. rreg HS (17%bv : bv 5) RA17.
assert (G12A : getr (ms_regs msA) 12 = w64 (rgb + 4 * tn_cut n))
by (rewrite RA12, Hc, (ER 11%nat 11%bv eq_refl), G11; unfold w64; rewrite ?unsigned_lit_small by (clear - Rrgb; lia); f_equal; lia).
assert (G13A : getr (ms_regs msA) 13 = w64 (tn_addr n + (16 + 8 * tn_cut n)))
by (rewrite RA13, Hc, (ER 10%nat 10%bv eq_refl), G10; unfold w64; rewrite ?unsigned_lit_small by (clear - Rn; lia); f_equal; lia).
assert (INVA : gl_inv regs0 (ms_regs msA) (w_H W) (ms_mem msA) rgb)
by (apply (gl_inv_step regs0 regs _ _ memg _ rgb INV0); [intros r0 Hr0; apply KA; right; exact Hr0 | rewrite RA16; reflexivity | rewrite RA17; reflexivity | exact SAMEA | apply Hspr | apply Hspr]).
assert (G10A : getr (ms_regs msA) 10 = w64 (tn_addr n)) by (rewrite (KA (10%bv : bv 5) ltac:(left; reflexivity)); exact G10).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msA) HAR0 SAMEA) as BKA.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msA HS eq_refl); cbn [ss_pc].
eapply (gl_BCD n l r HGl HGr fy regs0 f0 (ms_regs msA) mem (ms_mem msA) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb
HJ Hra Hal16 Hwlo Hwhi Hfrm HFK INVA G10A G12A G13A Hinf Hf1 Hf2 Hf4 HfullN HwfN).
+ apply (rg_tree_at_kept (w_H W) (w_H W) memg (ms_mem msA) (TNode n l r) HatN). intros b sz Hb. apply BKA. exact (Hblk _ Hb).
+ exact Hblk.
+ intros a Ha Hn. rewrite (SAMEA a Ha). exact (KEEP a Ha Hn).
+ intros a Ha. apply PRA. apply PR. exact Ha.
-
cbn [ss_gl gl_pc gl_regs] in HS.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK gl_Bspan GL_FLW; [awr_ok_tac|].
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (SAMEA : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) memg a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
assert (PRA : forall a, apresent (w_H W) memg a -> apresent (w_H W) (ms_mem msA) a) by (intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 (Ereg regs (gl_extra regs0 (troot l) (troot r) n 0)) Ex) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ (10%bv :: GL_KL) HS HAEx ltac:(vm_compute; reflexivity)) as KA. cbn [ms_regs restrict] in KA.
rreg HS (12%bv : bv 5) RA12. rreg HS (13%bv : bv 5) RA13. rreg HS (16%bv : bv 5) RA16. rreg HS (17%bv : bv 5) RA17.
assert (G12A : getr (ms_regs msA) 12 = w64 (rgb + 4 * tn_cut n))
by (rewrite RA12, Hc, (ER 11%nat 11%bv eq_refl), G11; unfold w64; rewrite ?unsigned_lit_small by (clear - Rrgb; lia); f_equal; lia).
assert (G13A : getr (ms_regs msA) 13 = w64 (tn_addr n + (16 + 8 * tn_cut n)))
by (rewrite RA13, Hc, (ER 10%nat 10%bv eq_refl), G10; unfold w64; rewrite ?unsigned_lit_small by (clear - Rn; lia); f_equal; lia).
assert (INVA : gl_inv regs0 (ms_regs msA) (w_H W) (ms_mem msA) rgb)
by (apply (gl_inv_step regs0 regs _ _ memg _ rgb INV0); [intros r0 Hr0; apply KA; right; exact Hr0 | rewrite RA16; reflexivity | rewrite RA17; reflexivity | exact SAMEA | apply Hspr | apply Hspr]).
assert (G10A : getr (ms_regs msA) 10 = w64 (tn_addr n)) by (rewrite (KA (10%bv : bv 5) ltac:(left; reflexivity)); exact G10).
pose proof (gl_blk_same _ _ _ _ _ memg (ms_mem msA) HAR0 SAMEA) as BKA.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msA HS eq_refl); cbn [ss_pc].
eapply (gl_BCD n l r HGl HGr fy regs0 f0 (ms_regs msA) mem (ms_mem msA) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb
HJ Hra Hal16 Hwlo Hwhi Hfrm HFK INVA G10A G12A G13A Hinf Hf1 Hf2 Hf4 HfullN HwfN).
+ apply (rg_tree_at_kept (w_H W) (w_H W) memg (ms_mem msA) (TNode n l r) HatN). intros b sz Hb. apply BKA. exact (Hblk _ Hb).
+ exact Hblk.
+ intros a Ha Hn. rewrite (SAMEA a Ha). exact (KEEP a Ha Hn).
+ intros a Ha. apply PRA. apply PR. exact Ha.
Qed.
Lemma gl_leaf : forall n, gl_G_stmt (TLeaf n).
Proof.
intros n fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb sp
HJ Hra Hal16 Hwlo Hwhi Hfrm HFK G2 G10 G11 G14 G15 G16 G17 Gkeep Vra Hinf Hf1 Hf2 Hf4 Hfull Hwf Hat Hblk KEEP PR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
cbn [troot] in G10. cbn [tree_at] in Hat. destruct Hat as (Hn0 & Hlen & c0 & c1 & Ond).
assert (Hwfn : tnode_wf n) by (apply (proj1 (Forall_cons_iff _ _ _) Hwf)). destruct Hwfn as (Hcut & Hcidx & _).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; left; reflexivity).
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold TGLNI_STK in Hwlo.
assert (Hspr : 0 <= sp - 16 /\ sp < 2 ^ 64) by (subst sp; clear - Hwlo Hwhi Hslo Hshi H47 Hceil C1 Hstk0; lia).
destruct (gl_seed fy 0%nat None 0 false regs0 regs memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb n c0 c1 1
HJ Hal16 Hwlo Hwhi G2 G10 G11 G14 G15 G16 G17 I ltac:(intros c X; discriminate X) Vra Hinf Hf1 Hf2 Hf4 Hinn Ond Hlen Hcut
ltac:(intros X; discriminate X)) as [HS SHOK].
set (E := Ereg regs (gl_extra regs0 c0 c1 n 1)) in *.
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E32 : ew E 32 = Z_to_bv 64 (bv_unsigned (getr regs0 1))) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E41 : ew E 41 = Z_to_bv 64 (tn_cidx n)).
{ subst E. apply (gl_EN regs regs0 c0 c1 n 1 8%nat). unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen. reflexivity. }
cbn [ss_gl gl_pc gl_regs] in HS.
aj_run_tok trbtbl_lib_ok HS HJ SHOK gl_Bspan; [awr_ok_tac|].
assert (SAMEA : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem ms) a = aview trbsegs (w_H W) memg a)
by (apply (lg_kept_ro _ _ _ _ _ HFr); intros rr Hin; vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia).
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gl_post. split; [reflexivity|].
rewrite R1. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite ?ew_ewset_other by lia. rewrite E32, Z_to_bv_bv_unsigned, Hra.
exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [exact Hfrm|]. split; [exact HFK|].
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ|].
split; [|split; [|split]].
- intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
repeat (destruct Hc as [-> | Hc]); [ | | | | | | | | | | | | | | subst r];
[ assert (X : getr (ms_regs ms) (2%bv : bv 5) = getr regs0 (2%bv : bv 5)); [|exact X]; rreg HS (2%bv : bv 5) Rk; rewrite Rk; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite (ER 2%nat 2%bv eq_refl), G2;
unfold w64; rewrite unsigned_lit_small by lia; replace (sp - 16 + 16) with sp by lia; subst sp; unfold spZ; apply Z_to_bv_bv_unsigned
| assert (X : getr (ms_regs ms) (3%bv : bv 5) = getr regs0 (3%bv : bv 5)); [|exact X]; rreg HS (3%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 3%nat 3%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (4%bv : bv 5) = getr regs0 (4%bv : bv 5)); [|exact X]; rreg HS (4%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 4%nat 4%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (8%bv : bv 5) = getr regs0 (8%bv : bv 5)); [|exact X]; rreg HS (8%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 8%nat 8%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (9%bv : bv 5) = getr regs0 (9%bv : bv 5)); [|exact X]; rreg HS (9%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 9%nat 9%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (18%bv : bv 5) = getr regs0 (18%bv : bv 5)); [|exact X]; rreg HS (18%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 18%nat 18%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (19%bv : bv 5) = getr regs0 (19%bv : bv 5)); [|exact X]; rreg HS (19%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 19%nat 19%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (20%bv : bv 5) = getr regs0 (20%bv : bv 5)); [|exact X]; rreg HS (20%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 20%nat 20%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (21%bv : bv 5) = getr regs0 (21%bv : bv 5)); [|exact X]; rreg HS (21%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 21%nat 21%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (22%bv : bv 5) = getr regs0 (22%bv : bv 5)); [|exact X]; rreg HS (22%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 22%nat 22%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (23%bv : bv 5) = getr regs0 (23%bv : bv 5)); [|exact X]; rreg HS (23%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 23%nat 23%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (24%bv : bv 5) = getr regs0 (24%bv : bv 5)); [|exact X]; rreg HS (24%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 24%nat 24%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (25%bv : bv 5) = getr regs0 (25%bv : bv 5)); [|exact X]; rreg HS (25%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 25%nat 25%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (26%bv : bv 5) = getr regs0 (26%bv : bv 5)); [|exact X]; rreg HS (26%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 26%nat 26%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate]
| assert (X : getr (ms_regs ms) (27%bv : bv 5) = getr regs0 (27%bv : bv 5)); [|exact X]; rreg HS (27%bv : bv 5) Rk; rewrite Rk; rewrite ?ew_ewset_other by lia; rewrite (ER 27%nat 27%bv eq_refl); apply Gkeep; [cbv; tauto | discriminate] ].
- exists n. split; [left; reflexivity|]. cbn [ms_regs]. rewrite R10. rewrite ?ew_ewset_other by lia. exact E41.
- intros a Ha Hn. cbn [ms_mem]. rewrite (SAMEA a Ha). exact (KEEP a Ha Hn).
- intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG). apply PR. exact Ha.
Qed.
Lemma gl_G_all : forall t, gl_G_stmt t.
Proof.
induction t as [|n|n l IHl r IHr].
- intros fy regs0 f0 regs mem memg md STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb sp HJ Hra Hal16 Hwlo Hwhi Hfrm HFK G2 G10 G11 G14 G15 G16 G17 Gkeep Vra Hinf Hf1 Hf2 Hf4 Hfull.
destruct Hfull.
- apply gl_leaf.
- apply gl_node; assumption.
Qed.
Definition gle_mem : smem := [ stack_region 16; got_region; bcell_region 32 ].
Definition gle_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_gle : sstate := mkSS A_get_leave_node_index sr_atoms gle_mem None gle_facts.
Definition gle_Bx : sv := SOff 32 0.
Definition gle_extra : list word := map (Z_to_bv 64) [SB].
Lemma gl_seed_entry : forall (fy : FPState) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (node fb nF rgb : Z),
let E := Ereg regs gle_extra in
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TGLNI_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 node -> getr regs 11 = w64 rgb ->
In (node, NODE_SIZE) (ablocks B lyc Sc) ->
In (fb, nF) (ablocks B lyc Sc) -> fb <= rgb -> rgb + 12 <= fb + nF -> rgb mod 4 = 0 ->
@st_ok trbsegs fy E ss_gle (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 A_get_leave_node_index) memc (seg_rom trbsegs))).
Proof.
intros fy regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k node fb nF rgb E HJ Hal16 Hwlo Hwhi G10 G11 Hinn Hinf Hf1 Hf2 Hf4.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold TGLNI_STK in Hwlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ node NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR Hinf) as (_ & Hf4096 & Hfceil & _ & _ & _ & HnF0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrnF].
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 node) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = w64 rgb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = node) by (rewrite E10; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (U11 : bv_unsigned (ew E 11) = rgb) by (rewrite E11; apply unsigned_lit_small; clear - Hf4096 Hfceil Hf1 Hf2 HrnF C1; lia).
unfold ss_gle. apply (entry_st_ok_full trbsegs).
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold gle_mem, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite Usp.
split; [clear - Hwlo Hwhi Hslo Hceil C1 Hstk0; lia|]. split; [clear - Hwhi Hshi H47; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. clear - Ho Hwlo Hwhi. lia.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa3250) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xa3250 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kgot).
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xab278) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xab278 8 gle_Bx SB);
[cbn [sv_denot gle_Bx]; fold E; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold gle_mem, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite Usp. unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hwlo Hwhi C1 C3 Hstk0. clear. unfold ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gle_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite Usp, U10, U11, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hwlo Hwhi Hal16 C1 C3 Hstk0 Hnceil Hn4096 Hn16 Hf4096 Hfceil Hf1 Hf2 HrnF Hf4. clear.
unfold SB, ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Theorem trb_get_leave_node_index : forall {fx : FPState}, tglni_spec B.
Proof.
intros fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fb nF rgb t
HJ Hra Hra4 Hal16 Hwlo Hwhi Hfrm G10 G11 Hinf Hf1 Hf2 Hf4 Hfull Hwf Hat Hblk.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
destruct (gl_root _ t Hfull Hat) as (n & c0 & c1 & leafv & Hroot & Hinb & Hlen & Ond & Hlv).
assert (Hinn : In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc)) by (apply Hblk; exact Hinb).
pose proof (gl_seed_entry fx regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (tn_addr n) fb nF rgb HJ Hal16 Hwlo Hwhi
ltac:(rewrite <- Hroot; exact G10) G11 Hinn Hinf Hf1 Hf2 Hf4) as HS.
set (E := Ereg regs gle_extra) in *.
assert (SHOK : sh_ok trbsegs gle_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (ER : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HAE : env_agree 32 (Ereg regs gle_extra) E) by (split; [intros m Hm; reflexivity | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%nat 2%bv eq_refl); reflexivity).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR Hinf) as (_ & Hf4096 & Hfceil & _ & _ & _ & HnF0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrnF].
assert (Rrgb : 4096 <= rgb /\ rgb + 12 <= 140737479966720) by (clear - Hf4096 Hfceil Hf1 Hf2 HrnF C1; lia).
unfold cfg_at. change (w64 A_get_leave_node_index) with (Z_to_bv 64 A_get_leave_node_index).
assert (Hwlo' : sp0 - STK <= spZ regs - 16) by (unfold TGLNI_STK in Hwlo; exact Hwlo).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK gl_Bspan GL_LOOP.
{ cbn [ss_mem ss_gle gle_mem]. eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite Usp; clear; lia | cbn; clear - Hwlo'; lia | cbn; clear - Hwhi; lia | awr_ok_tac]. }
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
rename HFr into HFr1; clear HF.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TGLNI_STK <= a < spZ regs) ->
aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) memc a).
{ intros a Ha Hnw. unfold TGLNI_STK in Hnw. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem ss_gle gle_mem] in Hin. unfold stack_region, got_region, bcell_region in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; unfold stack_region, got_region, bcell_region in Hr;
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; try rewrite Usp in Hr; clear - Hr Hnw; lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 (Ereg regs gle_extra) Ex) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ [1; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAEx ltac:(vm_compute; reflexivity)) as KA. cbn [ms_regs restrict] in KA.
rreg HS (2%bv : bv 5) R2. rreg HS (14%bv : bv 5) R14. rreg HS (15%bv : bv 5) R15. rreg HS (16%bv : bv 5) R16. rreg HS (17%bv : bv 5) R17.
assert (Vra : val_mem trbsegs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 8) 8 (bv_unsigned (getr regs 1))).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let rs := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx _ 0%nat rs HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ?ew_ewset_other by (cbv; lia); exact Usp);
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (slot_of_region Ex _ (spZ regs) cs lo hi wlo whi (-8) (SOff 1 0) (bv_unsigned (getr regs 1)) HRstk UspX ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite (ER 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq)) as V end end.
replace (spZ regs - 8) with (spZ regs + -8) by lia. exact V. }
assert (Hat1 : tree_at trbsegs (mrestrict (w_H W) (ms_mem msA)) t).
{ apply (rg_tree_at_kept (w_H W) (w_H W) memc (ms_mem msA) t Hat). intros b sz Hb i Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Hblk _ Hb)) as (_ & Hb4096 & Hbceil & _).
apply KEEP; [clear - Hi Hb4096 Hbceil C1; lia | unfold TGLNI_STK; clear - Hi Hbceil Hwlo' Hwhi Hslo Hceil Hstk0; lia]. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msA HS eq_refl); cbn [ss_pc].
eapply SRr_mono.
{ eapply (gl_G_all t fx regs (@fp_regs fx) (ms_regs msA) memc (ms_mem msA) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k fb nF rgb
HJ Hra Hal16 Hwlo Hwhi Hfrm ltac:(intros r0 _; reflexivity)).
- rewrite R2, Usp. unfold w64. first [reflexivity | f_equal; lia].
- rewrite (KA (10%bv : bv 5) ltac:(cbv; tauto)). exact G10.
- rewrite (KA (11%bv : bv 5) ltac:(cbv; tauto)). exact G11.
- rewrite R14. exact E32.
- rewrite R15. rewrite ?ew_ewset_other by lia. rewrite (ER 11%nat 11%bv eq_refl), G11. unfold w64. apply bv_eq.
rewrite alu64_unsigned. cbn [zalu_raw]. rewrite (unsigned_lit_small rgb) by (clear - Rrgb; lia).
change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). rewrite gl_lxor_ones64 by (clear - Rrgb; lia).
rewrite unsigned_lit_small by (clear - Rrgb; lia). unfold bv_wrap. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). clear - Rrgb. lia.
- rewrite R16. reflexivity.
- rewrite R17. reflexivity.
- intros r0 Hr0 N2. apply KA. cbv [CALLEE_SAVED In] in Hr0. cbv [In]. intuition; exfalso; apply N2; symmetry; assumption.
- exact Vra.
- exact Hinf.
- exact Hf1.
- exact Hf2.
- exact Hf4.
- exact Hfull.
- exact Hwf.
- exact Hat1.
- exact Hblk.
- exact KEEP.
- intros a Ha. exact (apresent_grows _ _ _ _ HG Ha). }
intros W' c' _ Hpost. exact Hpost.
Qed.
End GL.
