(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI0x YI1h YI08 YI0c YI0f YI3h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition GP_BODY : Z := 0x14944.
Definition GP_RET1 : Z := 0x14950.
Definition GP_TEST : Z := 0x14954.
Definition GP_LEAF : Z := 0x1495c.
Definition GPB (h : Z) : Z := 32 * (h + 1).
Definition LAY_GPF : layout_t := [(8, 8%N); (16, 8%N); (24, 8%N)].
Definition pc_of (u : tree) : Z := match u with TLeaf _ => GP_LEAF | _ => GP_BODY end.
Definition leaf_of (u : tree) : Z := match u with TLeaf _ => 1 | _ => 0 end.
Definition tn_of (u : tree) (d : tnode) : tnode := match u with TLeaf n => n | TNode n _ _ => n | TNull => d end.
Definition node_lits (leaf : Z) : list (option Z) :=
[None; None; None; None; None; None; None; None; None; Some leaf].
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Local Notation segs := src2segs.
Local Notation rom := (seg_rom src2segs).
Definition ss_gpP (leaf : Z) : sstate :=
mkSS src2_A_get_palette_from_decision_tree sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (node_lits leaf)) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 32) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Definition ss_gpN (pc leaf : Z) : sstate :=
mkSS pc sr_atoms
[ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (node_lits leaf)) ]
None
(mkFacts [ (9%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Definition gpL_alias : sv := SAlu ALU_ADD (SMd M_MUL (SOff 43 0) (SLit 3)) (SOff 8 0).
Definition ss_gpL0 : sstate :=
mkSS GP_LEAF sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 32 0 0
[mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 16 (CVal 8 (SOff 33 0)); mkChunk 24 (CVal 8 (SOff 34 0))] ;
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 35 (node_lits 1)) ;
YQ0b.mkRegion (Some 45%nat) 0 3 0 3 [] ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4);
(43%nat, mkAF 0 255 0); (45%nat, mkAF CEIL_MIN (2^63) 0) ] [] [(gpL_alias, SOff 45%nat 0)]).
Definition ss_gpL : sstate :=
mkSST GP_LEAF sr_atoms (sfr_atoms 48) (ss_mem ss_gpL0) None (ss_facts ss_gpL0).
Definition gp_R_stmt (u : tree) : Prop :=
forall (fy : FPState) (regs0 regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (pal : Z),
let sp := spZ regs0 in
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
YK0s.ret_ok (getr regs0 1) -> sp mod 16 = 0 ->
sp0 - STK <= sp - GPB (theight u) -> sp <= pal -> pal + 768 <= sp0 ->
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 8 = Z_to_bv 64 pal -> getr regs 9 = Z_to_bv 64 (troot u) ->
(forall r : reg, In r CALLEE_SAVED -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> getr regs r = getr regs0 r) ->
obj_at segs mem (sp - 32) LAY_GPF [bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1)] ->
tree_at segs mem u -> tree_full u -> tree_forall tnode_wf u ->
(forall b, In b (tree_blocks u) -> In b (blocks Lc Ac)) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 (pc_of u)) mem rom) md)
(fun c' => exists (fx' : FPState) regs2 mem2,
c' = mkCfg (@mkst fx' regs2 (getr regs0 1) mem2 rom) md /\ frm_zero (@fp_csr fx') /\
fregs_preserved (@fp_regs fy) (@fp_regs fx') /\
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem2 md /\
regs_preserved regs0 regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - GPB (theight u) <= a < sp - 32) -> ~ (pal <= a < pal + 768) ->
mbyte segs mem2 a = mbyte segs mem a)).
Definition gp_P_stmt (t : tree) : Prop :=
forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (pal : Z),
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - GPB (theight t) -> spZ regs <= pal -> pal + 768 <= sp0 ->
frm_zero (@fp_csr fy) ->
getr regs 10 = Z_to_bv 64 (troot t) -> getr regs 11 = Z_to_bv 64 pal ->
tree_at segs mem t -> tree_full t -> tree_forall tnode_wf t ->
(forall b, In b (tree_blocks t) -> In b (blocks Lc Ac)) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 src2_A_get_palette_from_decision_tree) mem rom) md)
(fun c' => exists (fx' : FPState) regs2 mem2,
c' = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 rom) md /\ frm_zero (@fp_csr fx') /\
fregs_preserved (@fp_regs fy) (@fp_regs fx') /\
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem2 md /\
regs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GPB (theight t) <= a < spZ regs) -> ~ (pal <= a < pal + 768) ->
mbyte segs mem2 a = mbyte segs mem a)).

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma node_facts : forall Lc Ac memc mdc u (n : tnode),
heap_ok MR Lc Ac memc mdc ->
(forall b, In b (tree_blocks u) -> In b (blocks Lc Ac)) -> In n (tree_nodes u) ->
4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Proof.
intros Lc Ac memc mdc u n HH Hbl Hin.
apply (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc); [exact HH | | unfold NODE_SIZE; lia].
apply Hbl. apply tree_blocks_in_nodes. exists n. auto.
Qed.
Lemma gpL_entry : forall (fy : FPState) (regs0 regs : bvmap 5 word) mem (n : tnode) c0 c1 (pal : Z),
let sp := spZ regs0 in
getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 8 = Z_to_bv 64 pal -> getr regs 9 = Z_to_bv 64 (tn_addr n) ->
obj_at segs mem (sp - 32) LAY_GPF [bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1)] ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 1) -> length (tn_mean n) = 3%nat -> 0 <= tn_cidx n < 256 ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
alloc_ceiling <= sp - 32 -> sp mod 16 = 0 -> sp <= pal -> pal + 768 <= 2 ^ 63 ->
(forall a, pal <= a < pal + 768 -> writable_at segs mem a) ->
frm_zero (@fp_csr fy) ->
let vals := [bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1);
c0; c1; nth 0 (tn_mean n) 0; nth 1 (tn_mean n) 0; nth 2 (tn_mean n) 0; tn_imin n; tn_imax n; tn_cut n; tn_cidx n; 1;
pal + 3 * tn_cidx n] in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 48 (@fp_regs fy) in
st_okF segs E ss_gpL (@mkst fy regs (Z_to_bv 64 GP_LEAF) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
ew E 32 = getr regs0 9 /\ ew E 33 = getr regs0 8 /\ ew E 34 = getr regs0 1 /\
bv_unsigned (ew E 2) = sp - 32 /\ bv_unsigned (ew E 45) = pal + 3 * tn_cidx n.
Proof.
intros fy regs0 regs mem n c0 c1 pal sp Hr2 Hr8 Hr9 Hfr Hobj Hlen Hcidx Hn0 Hn1 Hn16 Hsplo Hal16 Hpal Hpalhi Hwp Hfrm vals E0 E.
rewrite (node_vals_expand c0 c1 n 1 Hlen) in Hobj.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU2 : bv_unsigned (ew E0 2) = sp - 32) by (rewrite (HE0 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E0 8) = pal) by (rewrite (HE0 8%nat 8%bv eq_refl), Hr8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E0 9) = tn_addr n) by (rewrite (HE0 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU43 : ew E0 43 = Z_to_bv 64 (tn_cidx n)) by (apply (HV 11%nat); reflexivity).
assert (HU45 : bv_unsigned (ew E0 45) = pal + 3 * tn_cidx n).
{ change 45%nat with (32 + 13)%nat. rewrite (HV 13%nat (pal + 3 * tn_cidx n)); [apply unsigned_lit_small; lia | reflexivity]. }
assert (HS0 : @st_ok segs fy E0 ss_gpL0 (@mkst fy regs (Z_to_bv 64 GP_LEAF) mem rom)).
{ unfold ss_gpL0. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ change [mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 16 (CVal 8 (SOff 33 0)); mkChunk 24 (CVal 8 (SOff 34 0))]
with (obj_chunks_gen LAY_GPF 32 []).
eapply (region_ok_obj_gen segs _ mem 2 (sp - 32)); [exact HU2 | lia | lia | exact Hfr | reflexivity | | | intros i Hi; lia].
* intros j v Hj. apply (HV j v). do 3 (destruct j as [|j]; [exact Hj|]). destruct j; discriminate Hj.
* intros j z Hj. destruct j; discriminate Hj.
+ eapply (region_ok_obj_gen segs _ mem 9 (tn_addr n)); [exact HU9 | lia | lia | exact Hobj | reflexivity | | | intros i Hi; lia].
* intros j v Hj. apply (HV (3 + j)%nat v).
do 10 (destruct j as [|j]; [exact Hj|]). destruct j; discriminate Hj.
* intros j z Hj.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU45.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hwp. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU9, HU45. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms ss_facts atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU9, HU43, HU45, unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
rewrite !Z.mod_1_r.
assert ((sp - 32) mod 16 = 0) by (replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; lia.
+ cbn [f_alias ss_facts alias_ok]. split; [|exact I]. unfold gpL_alias.
rewrite (denot_add_mul3 _ 43 8 (tn_cidx n) pal HU43 Hcidx) by (first [rewrite <- HU8; apply eq_sym; apply Z_to_bv_bv_unsigned | lia]).
cbn [sv_denot]. rewrite Z.add_0_r, HU45. reflexivity. }
split; [exact (st_ok_enterF segs fy 48 E0 ss_gpL0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia.
split; [rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 9)); apply (HV 0%nat); reflexivity|].
split; [rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 8)); apply (HV 1%nat); reflexivity|].
split; [rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 1)); apply (HV 2%nat); reflexivity|].
split; [exact HU2 | exact HU45].
Qed.
Lemma gpN_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (n : tnode) c0 c1 leaf pc,
getr regs 9 = Z_to_bv 64 (tn_addr n) ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n leaf) -> length (tn_mean n) = 3%nat ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
let E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 n leaf) ++ []) in
@st_ok segs fy E (ss_gpN pc leaf) (@mkst fy regs (Z_to_bv 64 pc) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
ew E 32 = Z_to_bv 64 c0 /\ ew E 33 = Z_to_bv 64 c1.
Proof.
intros fy regs mem n c0 c1 leaf pc Hr9 Hobj Hlen Hn0 Hn1 Hn16 E.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n leaf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU9 : bv_unsigned (ew E 9) = tn_addr n) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
split.
{ unfold ss_gpN. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
eapply (region_ok_obj_gen segs _ mem 9 (tn_addr n)); [exact HU9 | lia | lia | exact Hobj | reflexivity | exact HV | | intros i Hi; lia].
intros j z Hj. rewrite (node_vals_expand c0 c1 n leaf Hlen).
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU9.
change (2 ^ 4) with 16. repeat split; lia. }
split; [exact HE|]. split; [apply (HV 0%nat); reflexivity | apply (HV 1%nat); reflexivity].
Qed.
Lemma gp_body : forall (fy : FPState) (regs : bvmap 5 word) mem (n : tnode) c0 c1,
getr regs 9 = Z_to_bv 64 (tn_addr n) ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> length (tn_mean n) = 3%nat ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
exists regs', msteps segs (@mkst fy regs (Z_to_bv 64 GP_BODY) mem rom)
(@mkst fy regs' (Z_to_bv 64 src2_A_get_palette_from_decision_tree) mem rom) /\
getr regs' 10 = Z_to_bv 64 c0 /\ getr regs' 11 = getr regs 8 /\ getr regs' 1 = Z_to_bv 64 GP_RET1 /\
(forall rr : reg, In rr CALLEE_SAVED -> getr regs' rr = getr regs rr).
Proof.
intros fy regs mem n c0 c1 Hr9 Hobj Hlen Hn0 Hn1 Hn16.
destruct (gpN_entry fy regs mem n c0 c1 0 GP_BODY Hr9 Hobj Hlen Hn0 Hn1 Hn16) as (HS & HE & HE32 & HE33).
set (E := Ereg regs _) in HS, HE, HE32, HE33.
pure_to src2tbl_ok HS src2_A_get_palette_from_decision_tree.
exists regs0. split; [exact Hms|].
jreg HS (10%bv:reg) as Hq10. jreg HS (11%bv:reg) as Hq11. jreg HS (1%bv:reg) as Hq1. cbn [ms_regs mkst] in Hq10, Hq11, Hq1.
split; [rewrite Hq10, HE32; reflexivity|]. split; [rewrite Hq11, (HE 8%nat 8%bv eq_refl); reflexivity|].
split; [exact Hq1|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ CALLEE_SAVED HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition CS_no9 : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma CS_no9_in : forall rr : reg, In rr CALLEE_SAVED -> rr <> 9%bv -> In rr CS_no9.
Proof.
intros rr Hrr H9. cbv [CALLEE_SAVED In] in Hrr. cbv [CS_no9 In].
repeat (destruct Hrr as [Hq|Hrr]; [first [congruence | tauto] |]). destruct Hrr.
Qed.
Lemma gp_ret1 : forall (fy : FPState) (regs : bvmap 5 word) mem (n : tnode) c0 c1,
getr regs 9 = Z_to_bv 64 (tn_addr n) ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> length (tn_mean n) = 3%nat ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
exists regs', msteps segs (@mkst fy regs (Z_to_bv 64 GP_RET1) mem rom) (@mkst fy regs' (Z_to_bv 64 GP_TEST) mem rom) /\
getr regs' 9 = Z_to_bv 64 c1 /\
(forall rr : reg, In rr CS_no9 -> getr regs' rr = getr regs rr).
Proof.
intros fy regs mem n c0 c1 Hr9 Hobj Hlen Hn0 Hn1 Hn16.
destruct (gpN_entry fy regs mem n c0 c1 0 GP_RET1 Hr9 Hobj Hlen Hn0 Hn1 Hn16) as (HS & HE & HE32 & HE33).
set (E := Ereg regs _) in HS, HE, HE32, HE33.
pure_to src2tbl_ok HS GP_TEST.
exists regs0. split; [exact Hms|].
jreg HS (9%bv:reg) as Hq9. cbn [ms_regs mkst] in Hq9. split; [rewrite Hq9, HE33; reflexivity|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ CS_no9 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma gp_test : forall (fy : FPState) (regs : bvmap 5 word) mem (r : tree) Lc Ac memc mdc,
heap_ok MR Lc Ac memc mdc -> (forall b, In b (tree_blocks r) -> In b (blocks Lc Ac)) ->
getr regs 9 = Z_to_bv 64 (troot r) -> tree_at segs mem r -> tree_full r ->
exists regs', msteps segs (@mkst fy regs (Z_to_bv 64 GP_TEST) mem rom) (@mkst fy regs' (Z_to_bv 64 (pc_of r)) mem rom) /\
(forall rr : reg, In rr CALLEE_SAVED -> getr regs' rr = getr regs rr).
Proof.
intros fy regs mem r Lc Ac memc mdc HH Hbl Hr9 Htree Hfull.
destruct r as [|n|n l r']; [destruct Hfull| |].
- destruct (node_facts Lc Ac memc mdc (TLeaf n) n HH Hbl ltac:(left; reflexivity)) as (Hn0 & Hn1 & Hn16).
destruct Htree as (Hnz & Hlen & c0 & c1 & Hobj). cbn [troot] in Hr9.
destruct (gpN_entry fy regs mem n c0 c1 1 GP_TEST Hr9 Hobj Hlen Hn0 Hn1 Hn16) as (HS & HE & HE32 & HE33).
set (E := Ereg regs _) in HS, HE, HE32, HE33.
pure_to src2tbl_ok HS GP_LEAF.
exists regs0. split; [exact Hms|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ CALLEE_SAVED HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
- destruct (node_facts Lc Ac memc mdc (TNode n l r') n HH Hbl ltac:(left; reflexivity)) as (Hn0 & Hn1 & Hn16).
destruct Htree as (Hnz & Hlen & Hobj & _ & _). cbn [troot] in Hr9.
destruct (gpN_entry fy regs mem n (troot l) (troot r') 0 GP_TEST Hr9 Hobj Hlen Hn0 Hn1 Hn16) as (HS & HE & HE32 & HE33).
set (E := Ereg regs _) in HS, HE, HE32, HE33.
pure_to src2tbl_ok HS GP_BODY.
exists regs0. split; [exact Hms|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ CALLEE_SAVED HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma gp_R_all : (forall t, gp_R_stmt t -> gp_P_stmt t) -> forall u, gp_R_stmt u.
Proof.
intros HPR u. induction u as [|n|n l IHl r IHr];
intros fy regs0 regs mem STK sp0 FP L A mem0 md0 Lc Ac md pal sp HJ Hra Hal16 Hbud Hpal Hpalhi Hfrm Hr2 Hr8 Hr9 Hcs Hfr Htree Hfull Hwf Hbl.
-   destruct Hfull.
-
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (HG0 : GPB (theight (TLeaf n)) = 32) by reflexivity. rewrite HG0 in *.
destruct (node_facts Lc Ac mem md (TLeaf n) n HH Hbl ltac:(left; reflexivity)) as (Hn0 & Hn1 & Hn16).
cbn [troot] in Hr9. destruct Htree as (Hnz & Hlen & c0 & c1 & Hobj).
assert (Hwfn : tnode_wf n) by (apply (proj1 (Forall_cons_iff _ _ _) Hwf)).
destruct Hwfn as (Hcut & Hcidx & _).
destruct (gpL_entry fy regs0 regs mem n c0 c1 pal Hr2 Hr8 Hr9 Hfr Hobj Hlen Hcidx Hn0 Hn1 Hn16
ltac:(lia) Hal16 Hpal ltac:(lia) ltac:(intros a Ha; apply Hstw; lia) Hfrm)
as (HS & HE & HEf & HE32 & HE33 & HE34 & HU2 & HU45).
set (E := ew_fregs _ 48 _) in HS, HE, HEf, HE32, HE33, HE34, HU2, HU45.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 GP_LEAF) mem rom)) in HJ.
change (pc_of (TLeaf n)) with GP_LEAF.
jrunF LAWS src2tbl_ok HS HJ.
{ wr_ok_eval. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_win; [reflexivity | exact HU45 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
lazymatch type of HS with st_okF _ ?E1 ?ss1 ?ms1 =>
eapply (SR_ret_at (fx:=(fp_of ms1)) segs src2tbl E1 ss1 ms1 _ _ src2tbl_ok);
[ exact Hh | exact Hlz | exact (st_okF_to_legacy segs E1 ss1 ms1 HS) | reflexivity | vm_compute; reflexivity | ];
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1)
end.
split.
{ pose proof (st_okF_reg segs E _ _ 1%bv HS) as Q1. eval_sr_get_in Q1. cbn [sv_denot] in Q1.
rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned in Q1. rewrite Q1, Hra. reflexivity. }
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [intros rr Hrr; cbn [fp_regs fp_of]; exact (st_okF_fregs_kept segs E _ _ 48 (@fp_regs fy) FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) rr Hrr)|].
split; [exact HJ|].
split.
{ apply regs_preserved_of_list. intros rr Hrr.
rewrite (st_okF_reg segs E _ _ rr HS).
cbv [CALLEE_SAVED In] in Hrr.
pose proof Hrr as Hrr'. cbv [CALLEE_SAVED In] in Hrr.
repeat (destruct Hrr as [<-|Hrr];
[ match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end;
cbn [sv_denot]; rewrite ?Z.add_0_r;
lazymatch goal with
| |- Z_to_bv 64 (bv_unsigned (ew _ 2) + 32) = _ => rewrite HU2, Z.sub_add; apply Z_to_bv_bv_unsigned
| |- Z_to_bv 64 (bv_unsigned (ew _ 33)) = _ => rewrite HE33; apply Z_to_bv_bv_unsigned
| |- Z_to_bv 64 (bv_unsigned (ew _ 32)) = _ => rewrite HE32; apply Z_to_bv_bv_unsigned
| |- Z_to_bv 64 (bv_unsigned (ew _ ?k)) = getr _ ?rr =>
rewrite (HE k rr eq_refl), Z_to_bv_bv_unsigned; apply (Hcs rr Hrr'); intros HH0; discriminate HH0
end |]).
destruct Hrr. }
intros a Ha Hno Hnp. mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?HU45; lia). reflexivity.
-
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNSv : NODE_SIZE = 56) by reflexivity.
destruct (heap_model _ _ LAWS _ _ _ _ HH) as (Hh & Hlz & _).
set (h := theight (TNode n l r)) in *.
pose proof (theight_node_l n l r : theight l + 1 <= h) as Hhl.
pose proof (theight_node_r n l r : theight r + 1 <= h) as Hhr.
pose proof (theight_nonneg l) as Hhl0. pose proof (theight_nonneg r) as Hhr0.
assert (HGl : GPB (theight l) + 32 <= GPB h) by (unfold GPB; lia).
assert (HGr : GPB (theight r) + 32 <= GPB h) by (unfold GPB; lia).
assert (HGl0 : 32 <= GPB (theight l)) by (unfold GPB; lia).
assert (HGr0 : 32 <= GPB (theight r)) by (unfold GPB; lia).
destruct (node_facts Lc Ac mem md (TNode n l r) n HH Hbl ltac:(left; reflexivity)) as (Hn0 & Hn1 & Hn16).
cbn [troot] in Hr9. destruct Htree as (Hnz & Hlen & Hobj & Htl & Htr).
destruct Hfull as [Hfl Hfr'].
apply tree_forall_node in Hwf as (Hwfn & Hwfl & Hwfr).
assert (Hbll : forall b, In b (tree_blocks l) -> In b (blocks Lc Ac)) by (intros b Hb; apply Hbl; right; apply in_app_iff; left; exact Hb).
assert (Hblr : forall b, In b (tree_blocks r) -> In b (blocks Lc Ac)) by (intros b Hb; apply Hbl; right; apply in_app_iff; right; exact Hb).
destruct (gp_body fy regs mem n (troot l) (troot r) Hr9 Hobj Hlen Hn0 Hn1 Hn16) as (regs1 & Hms1 & Hq10 & Hq11 & Hq1 & Hk1).
change (pc_of (TNode n l r)) with GP_BODY.
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms1).
assert (Hsp1 : spZ regs1 = sp - 32).
{ unfold spZ. rewrite (Hk1 2%bv ltac:(cbv; tauto)), Hr2. apply unsigned_lit_small. lia. }
eapply SR_bind.
{ apply (HPR l IHl fy regs1 mem STK sp0 FP L A mem0 md0 Lc Ac md pal HJ);
[ rewrite Hq1; apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp1; replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| rewrite Hsp1; lia | rewrite Hsp1; lia | exact Hpalhi | exact Hfrm
| exact Hq10 | rewrite Hq11; exact Hr8 | exact Htl | exact Hfl | exact Hwfl | exact Hbll ]. }
cbv beta. intros c' (fx2 & regs2 & mem2 & -> & Hfrm2 & Hfp2 & HJ2 & HP2 & Hmem2). rewrite Hq1, Hsp1 in *.
assert (Kn : forall i, 0 <= i < NODE_SIZE -> mbyte segs mem2 (tn_addr n + i) = mbyte segs mem (tn_addr n + i)).
{ intros i Hi. apply Hmem2; lia. }
assert (Hobj2 : obj_at segs mem2 (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0)).
{ eapply obj_at_transport_range; [exact Hobj | apply (proj1 lay_inside_Node) | exact Kn]. }
assert (Hfr2 : obj_at segs mem2 (sp - 32) LAY_GPF [bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 1)]).
{ eapply obj_at_transport; [exact Hfr|]. intros f i Hf Hi. cbv [LAY_GPF In] in Hf.
destruct Hf as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; (apply Hmem2; lia). }
assert (Htr2 : tree_at segs mem2 r).
{ eapply tree_at_frame; [exact Htr|]. intros n' a Hn' Ha.
destruct (node_facts Lc Ac mem md (TNode n l r) n' HH Hbl ltac:(right; apply in_app_iff; right; exact Hn')) as (Hb0 & Hb1 & _).
apply Hmem2; lia. }
pose proof (regs_preserved_in _ _ 9%bv HP2 ltac:(cbv; tauto)) as Hp9. rewrite (Hk1 9%bv ltac:(cbv; tauto)), Hr9 in Hp9.
destruct (gp_ret1 fx2 regs2 mem2 n (troot l) (troot r) Hp9 Hobj2 Hlen Hn0 Hn1 Hn16) as (regs3 & Hms3 & Hq9 & Hk3).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms3).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (gp_test fx2 regs3 mem2 r Lc Ac mem2 md HH2 Hblr Hq9 Htr2 Hfr') as (regs4 & Hms4 & Hk4).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms4).
assert (HR2 : forall rr : reg, In rr CS_no9 -> getr regs4 rr = getr regs rr).
{ intros rr Hrr. assert (Hc : In rr CALLEE_SAVED) by (cbv [CS_no9 In] in Hrr; cbv [CALLEE_SAVED In]; tauto).
rewrite (Hk4 rr Hc), (Hk3 rr Hrr), (regs_preserved_in _ _ rr HP2 Hc). apply Hk1. exact Hc. }
eapply SR_mono.
{ apply (IHr fx2 regs0 regs4 mem2 STK sp0 FP L A mem0 md0 Lc Ac md pal HJ2 Hra Hal16 ltac:(lia) Hpal Hpalhi Hfrm2);
[ rewrite (HR2 2%bv ltac:(cbv; tauto)); exact Hr2
| rewrite (HR2 8%bv ltac:(cbv; tauto)); exact Hr8
| rewrite (Hk4 9%bv ltac:(cbv; tauto)); exact Hq9
| intros rr Hrr N2 N8 N9; rewrite (HR2 rr (CS_no9_in rr Hrr N9)); apply Hcs; assumption
| exact Hfr2 | exact Htr2 | exact Hfr' | exact Hwfr | exact Hblr ]. }
cbv beta. intros c' (fx3 & regs5 & mem3 & -> & Hfrm3 & Hfp3 & HJ3 & HP3 & Hmem3).
exists fx3, regs5, mem3. split; [reflexivity|]. split; [exact Hfrm3|].
split; [eapply fregs_preserved_trans; [exact Hfp2 | exact Hfp3]|].
split; [exact HJ3|]. split; [exact HP3|].
intros a Ha Hno Hnp. rewrite (Hmem3 a Ha) by lia. apply Hmem2; lia.
Qed.
Definition CS_no289 : list reg := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma CS_no289_in : forall rr : reg, In rr CALLEE_SAVED -> rr <> 2%bv -> rr <> 8%bv -> rr <> 9%bv -> In rr CS_no289.
Proof.
intros rr Hrr H2 H8 H9. cbv [CALLEE_SAVED In] in Hrr. cbv [CS_no289 In].
repeat (destruct Hrr as [Hq|Hrr]; [first [congruence | tauto] |]). destruct Hrr.
Qed.
Lemma gp_prologue : forall (fy : FPState) (regs : bvmap 5 word) mem (n : tnode) (leaf pc c0 c1 : Z)
STK sp0 FP L A mem0 md0 Lc Ac md (pal : Z) (Q : config -> Prop),
(leaf = 0 /\ pc = GP_BODY) \/ (leaf = 1 /\ pc = GP_LEAF) ->
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 32 -> spZ regs <= pal -> pal + 768 <= sp0 ->
getr regs 10 = Z_to_bv 64 (tn_addr n) -> getr regs 11 = Z_to_bv 64 pal ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n leaf) -> length (tn_mean n) = 3%nat ->
4096 <= tn_addr n -> tn_addr n + NODE_SIZE <= alloc_ceiling -> tn_addr n mod 16 = 0 ->
(forall (regsP : bvmap 5 word) memP,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac memP md ->
getr regsP 2 = Z_to_bv 64 (spZ regs - 32) -> getr regsP 8 = Z_to_bv 64 pal -> getr regsP 9 = Z_to_bv 64 (tn_addr n) ->
(forall r : reg, In r CALLEE_SAVED -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> getr regsP r = getr regs r) ->
obj_at segs memP (spZ regs - 32) LAY_GPF [bv_unsigned (getr regs 9); bv_unsigned (getr regs 8); bv_unsigned (getr regs 1)] ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> mbyte segs memP a = mbyte segs mem a) ->
SR segs (mkCfg (@mkst fy regsP (Z_to_bv 64 pc) memP rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 src2_A_get_palette_from_decision_tree) mem rom) md) Q.
Proof.
intros fy regs mem n leaf pc c0 c1 STK sp0 FP L A mem0 md0 Lc Ac md pal Q Hcase HJ Hal16 Hbud Hpal Hpalhi Ha0 Ha1 Hobj Hlen Hn0 Hn1 Hn16 HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNSv : NODE_SIZE = 56) by reflexivity.
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 n leaf) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n leaf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = tn_addr n) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E (ss_gpP leaf) (@mkst fy regs (Z_to_bv 64 src2_A_get_palette_from_decision_tree) mem rom)).
{ unfold ss_gpP. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack segs _ mem 2 (spZ regs)); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj_gen segs _ mem 10 (tn_addr n)); [exact HU10 | lia | lia | exact Hobj | reflexivity | exact HV | | intros i Hi; lia].
intros j z Hj. rewrite (node_vals_expand c0 c1 n leaf Hlen).
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10.
change (2 ^ 4) with 16. repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 src2_A_get_palette_from_decision_tree) mem rom)) in HJ.
destruct Hcase as [[-> ->] | [-> ->]];
[ jrun_to LAWS src2tbl_ok HS HJ GP_BODY | jrun_to LAWS src2tbl_ok HS HJ GP_LEAF ].
1,3: wr_ok_eval; eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]].
all: cbn [ms_mem mkst] in HF, HJ.
all: rewrite (st_ok_mkst segs E _ _ HS eq_refl); cbn [ss_pc].
all: jreg HS (2%bv:reg) as Hq2; jreg HS (8%bv:reg) as Hq8; jreg HS (9%bv:reg) as Hq9.
all: apply HK;
[ exact HJ
| rewrite Hq2, HU2; reflexivity
| rewrite Hq8, (HE 11%nat 11%bv eq_refl); exact Ha1
| rewrite Hq9, (HE 10%nat 10%bv eq_refl); exact Ha0
| intros rr Hrr N2 N8 N9; exact (regs_kept_of_st_ok _ _ _ _ regs _ CS_no289 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) rr (CS_no289_in rr Hrr N2 N8 N9))
| cbn [obj_at LAY_GPF]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
pose proof (u64_range (getr regs 9)) as R9; pose proof (u64_range (getr regs 8)) as R8; pose proof (u64_range (getr regs 1)) as R1;
repeat split; try lia;
[ replace (spZ regs - 32 + 8) with (spZ regs + (-24)) by lia;
eapply (st_chunk_val segs _ _ _ 0%nat _ 2%nat (-24) 8%N (SOff 9 0) (spZ regs) _ HS); [reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia]
| replace (spZ regs - 32 + 16) with (spZ regs + (-16)) by lia;
eapply (st_chunk_val segs _ _ _ 0%nat _ 2%nat (-16) 8%N (SOff 8 0) (spZ regs) _ HS); [reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia]
| replace (spZ regs - 32 + 24) with (spZ regs + (-8)) by lia;
eapply (st_chunk_val segs _ _ _ 0%nat _ 2%nat (-8) 8%N (SOff 1 0) (spZ regs) _ HS); [reflexivity | reflexivity | cbv; tauto | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia] ]
| intros a Ha Hno; mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?HU2; lia); reflexivity ].
Qed.
Lemma gp_P_of_R : forall t, gp_R_stmt t -> gp_P_stmt t.
Proof.
intros t HR fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md pal HJ Hra Hal16 Hbud Hpal Hpalhi Hfrm Ha0 Ha1 Htree Hfull Hwf Hbl.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof (theight_nonneg t) as Hh0. assert (HG0 : 32 <= GPB (theight t)) by (unfold GPB; lia).
assert (Hroot : exists n leaf pc c0 c1, ((leaf = 0 /\ pc = GP_BODY) \/ (leaf = 1 /\ pc = GP_LEAF)) /\ pc = pc_of t /\
troot t = tn_addr n /\ In n (tree_nodes t) /\ length (tn_mean n) = 3%nat /\
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n leaf)).
{ destruct t as [|n|n l r]; [destruct Hfull| |].
- destruct Htree as (Hnz & Hlen & c0 & c1 & Hobj). exists n, 1, GP_LEAF, c0, c1.
cbn [pc_of troot tree_nodes]. split; [right; split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [left; reflexivity|]. split; [exact Hlen | exact Hobj].
- destruct Htree as (Hnz & Hlen & Hobj & _). exists n, 0, GP_BODY, (troot l), (troot r).
cbn [pc_of troot tree_nodes]. split; [left; split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [left; reflexivity|]. split; [exact Hlen | exact Hobj]. }
destruct Hroot as (n & leaf & pc & c0 & c1 & Hcase & Hpc & Hrt & Hin & Hlen & Hobj).
destruct (node_facts Lc Ac mem md t n HH Hbl Hin) as (Hn0 & Hn1 & Hn16).
rewrite Hrt in Ha0.
eapply (gp_prologue fy regs mem n leaf pc c0 c1 STK sp0 FP L A mem0 md0 Lc Ac md pal _ Hcase HJ Hal16 ltac:(lia) Hpal Hpalhi Ha0 Ha1 Hobj Hlen Hn0 Hn1 Hn16).
intros regsP memP HJP Hq2 Hq8 Hq9 Hcs HfrP HmemP.
assert (HtreeP : tree_at segs memP t).
{ eapply tree_at_frame; [exact Htree|]. intros n' a Hn' Ha.
destruct (node_facts Lc Ac mem md t n' HH Hbl Hn') as (Hb0 & Hb1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & Hceil & _ & _) & _). pose proof (proj1 alloc_ceiling_val).
apply HmemP; lia. }
rewrite Hpc. rewrite <- Hrt in Hq9.
eapply SR_mono.
{ exact (HR fy regs regsP memP STK sp0 FP L A mem0 md0 Lc Ac md pal HJP Hra Hal16 Hbud Hpal Hpalhi Hfrm Hq2 Hq8 Hq9 Hcs HfrP HtreeP Hfull Hwf Hbl). }
cbv beta. intros c' (fx' & regs2 & mem2 & -> & Hfrm' & Hfp' & HJ2 & HP2 & Hmem2).
exists fx', regs2, mem2. split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact Hfp'|]. split; [exact HJ2|]. split; [exact HP2|].
intros a Ha Hno Hnp. rewrite (Hmem2 a Ha) by lia. apply HmemP; lia.
Qed.
Lemma gp_P_all : forall t, gp_P_stmt t.
Proof. intros t. apply gp_P_of_R. apply gp_R_all. exact gp_P_of_R. Qed.
Theorem src2_getpal : getpal_spec API.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs t pal HJ Hra Hal16 Hbud Hsp Hfrm Ha0 Ha1 Htree Hfull Hh Hwf Hbl Hpal Hpalhi.
pose proof (theight_nonneg t) as Hh0.
assert (HG : GPB (theight t) <= GETPAL_STK) by (unfold GPB, GETPAL_STK, theight, TREE_HMAX in *; lia).
eapply SR_mono.
{ exact (gp_P_all t fx regs memc STK sp0 FP L A mem md Lc Ac mdc pal HJ Hra Hal16 ltac:(lia) Hpal Hpalhi Hfrm Ha0 Ha1 Htree Hfull Hwf Hbl). }
cbv beta. intros c' (fx' & regs2 & mem2 & -> & Hfrm' & Hfp' & HJ2 & HP2 & Hmem2).
exists fx', regs2, mem2. split; [reflexivity|]. split; [exact Hfrm'|]. split; [exact Hfp'|]. split; [exact HJ2|]. split; [exact HP2|].
intros a Ha Hno Hnp. apply Hmem2; [exact Ha | lia | exact Hnp].
Qed.
End S.
End c.
