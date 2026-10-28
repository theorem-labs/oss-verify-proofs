(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i YI0x UI1h YI08 YI0c YI0f UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FT_JAL1 : Z := ubs2_A_free_decision_tree + 0x30.
Definition FT_RET1 : Z := ubs2_A_free_decision_tree + 0x34.
Definition FT_RET2 : Z := ubs2_A_free_decision_tree + 0x3c.
Ltac wr_ok_ft HU2 :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end;
eapply wr_ok_cons_stack; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |];
apply wr_ok_cons_ro; [cbn [r_whi r_wlo]; lia|]; apply wr_ok_nil.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Definition node_lits (leaf : Z) : list (option Z) :=
[None; None; None; None; None; None; None; None; None; Some leaf].
Definition ss_ft (leaf : Z) : sstate :=
mkSS ubs2_A_free_decision_tree sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 (node_lits leaf)) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FT_STK 0) (2^63) 4); (10%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4) ] [] []).
Definition ss_ft_null : sstate :=
mkSS ubs2_A_free_decision_tree (sr_set sr_atoms 10%bv (SLit 0)) [ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FT_STK 0) (2^63) 4) ] [] []).
Definition ft_post (t : tree) (rest : list (Z * Z)) (regs : bvmap 5 word) L A mem md : config -> Prop :=
fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' rom) md' /\
journal ubs2_msyms MR (FT_STK (theight t)) (spZ regs) (blocks_fp (tree_blocks t)) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest.
Lemma ft_entry : forall leaf c0 c1 (n : tnode) (regs : bvmap 5 word) mem L A md h,
fn_pre ubs2_msyms MR (FT_STK h) L A regs mem md -> 0 <= h ->
getr regs 10 = Z_to_bv 64 (tn_addr n) ->
In (tn_addr n, NODE_SIZE) (blocks L A) ->
length (tn_mean n) = 3%nat ->
obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n leaf) ->
let E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 n leaf) ++ []) in
st_ok segs E (ss_ft leaf) (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
bv_unsigned (ew E 2) = spZ regs /\ bv_unsigned (ew E 10) = tn_addr n /\
ew E 32 = Z_to_bv 64 c0 /\ ew E 33 = Z_to_bv 64 c1 /\
4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Proof.
intros leaf c0 c1 n regs mem L A md h HPRE Hh Ha0 Hin Hlen Hobj E.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HF0 : FT_STK 0 = 16 + ALLOC_STACK) by reflexivity.
assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (HFh : FT_STK 0 <= FT_STK h) by (unfold FT_STK; lia).
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
destruct (heap_blocks_range ubs2_msyms MR LAWS L A mem md (tn_addr n) NODE_SIZE HH Hin ltac:(lia)) as (Hn0 & Hn1 & Hn16).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n leaf) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = tn_addr n) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
split.
{ unfold ss_ft. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack segs _ mem 2 (spZ regs)); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj_gen segs _ mem 10 (tn_addr n)); [exact HU10 | lia | lia | exact Hobj | reflexivity | exact HV | | intros i Hi; lia].
intros j z Hj. destruct (tnode_mean3 n Hlen) as (m0 & m1 & m2 & En). rewrite En.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10.
change (2 ^ 4) with 16. repeat split; lia. }
split; [exact HE|]. split; [exact HU2|]. split; [exact HU10|].
split; [apply (HV 0%nat); reflexivity|]. split; [apply (HV 1%nat); reflexivity|]. lia.
Qed.
Lemma free_tree_gen : forall t L A (regs : bvmap 5 word) mem md (rest : list (Z * Z)),
fn_pre ubs2_msyms MR (FT_STK (theight t)) L A regs mem md ->
getr regs 10 = Z_to_bv 64 (troot t) ->
tree_at segs mem t ->
Permutation (blocks L A) (tree_blocks t ++ rest) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom) md) (ft_post t rest regs L A mem md).
Proof.
induction t as [|n|n l IHl r IHr]; intros L A regs mem md rest HPRE Ha0 Htree HB.
-
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HF0 : FT_STK 0 = 16 + ALLOC_STACK) by reflexivity.
assert (HASv : ALLOC_STACK = 8192) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (HFT : FT_STK 0 <= FT_STK (theight TNull)) by (apply Z.le_refl).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok segs E ss_ft_null (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom)).
{ unfold ss_ft_null. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | rewrite Ha0; reflexivity].
- vm_compute. reflexivity.
- constructor; [|constructor].
apply (region_ok_stack segs _ mem 2 (spZ regs)); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs2_msyms MR (FT_STK (theight TNull)) (blocks_fp (tree_blocks TNull)) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom)) in HJ.
jrun LAWS ubs2tbl_ok HS HJ.
{ wr_ok_tac. exact HU2. }
eapply (SR_ret_at segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
exists L, A, (ms_regs ms), (ms_mem ms), md.
split.
{ cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra; reflexivity end. }
split; [exact HJ|].
split; [exact (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))|].
cbn [tree_blocks app] in HB. exact HB.
-
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HF0 : FT_STK 0 = 16 + ALLOC_STACK) by reflexivity.
assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (HFT : FT_STK (theight (TLeaf n)) = FT_STK 0) by reflexivity. rewrite HFT in *.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
cbn [troot] in Ha0. destruct Htree as (Hnz & Hlen & c0 & c1 & Hobj).
assert (Hin : In (tn_addr n, NODE_SIZE) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]).
destruct (ft_entry 1 c0 c1 n regs mem L A md 0 HPRE ltac:(lia) Ha0 Hin Hlen Hobj) as (HS & HE & HU2 & HU10 & HE32 & HE33 & Hn0 & Hn1 & Hn16).
set (E := Ereg regs _) in HS, HE, HU2, HU10, HE32, HE33.
pose proof (journal_init ubs2_msyms MR (FT_STK 0) (blocks_fp (tree_blocks (TLeaf n))) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free.
{ wr_ok_tac. exact HU2. }
jreg HS (10%bv:reg) as Hq10. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 10)), HU10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
cbn [tree_blocks app] in HB.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hin | exact Hq10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | reflexivity | exact HU2 | reflexivity | lia | lia
| exact Hq4 | rewrite (HE 4%nat 4%bv eq_refl); exact Htp | exact Hq1 | rewrite (HE 1%nat 1%bv eq_refl); exact Hra
| intros _ i Hi; exists (tn_addr n, tn_addr n + NODE_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hrm7 & Hkeep7 & Hhi7).
exists L7, A7, regs7, mem7, md7. rewrite (HE 1%nat 1%bv eq_refl). split; [reflexivity|]. split; [exact HJ7|].
split; [eapply regs_preserved_trans; [| exact HP7];
exact (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))|].
eapply perm_after_rm1; [exact HB | exact Hrm7].
-
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HF0 : FT_STK 0 = 16 + ALLOC_STACK) by reflexivity.
assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
set (h := theight (TNode n l r)) in *.
pose proof (theight_node_l n l r : theight l + 1 <= h) as Hhl.
pose proof (theight_node_r n l r : theight r + 1 <= h) as Hhr.
pose proof (theight_nonneg l) as Hhl0. pose proof (theight_nonneg r) as Hhr0.
assert (HFl : FT_STK (theight l) + 16 <= FT_STK h) by (unfold FT_STK; lia).
assert (HFr : FT_STK (theight r) + 16 <= FT_STK h) by (unfold FT_STK; lia).
assert (HFl0 : 0 <= FT_STK (theight l)) by (unfold FT_STK; lia).
assert (HFr0 : 0 <= FT_STK (theight r)) by (unfold FT_STK; lia).
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
cbn [troot] in Ha0. destruct Htree as (Hnz & Hlen & Hobj & Htl & Htr).
cbn [tree_blocks app] in HB. rewrite <- app_assoc in HB.
assert (Hin : In (tn_addr n, NODE_SIZE) (blocks L A)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]).
destruct (ft_entry 0 (troot l) (troot r) n regs mem L A md h HPRE ltac:(lia) Ha0 Hin Hlen Hobj) as (HS & HE & HU2 & HU10 & HE32 & HE33 & Hn0 & Hn1 & Hn16).
set (E := Ereg regs _) in HS, HE, HU2, HU10, HE32, HE33.
pose proof (journal_init ubs2_msyms MR (FT_STK h) (blocks_fp ((tn_addr n, NODE_SIZE) :: tree_blocks l ++ tree_blocks r)) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom)) in HJ.
assert (Hspm : (spZ regs - 16) mod 16 = 0) by (replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (sp0 := spZ regs) in *.
assert (HBl : Permutation (blocks L A) (tree_blocks l ++ ((tn_addr n, NODE_SIZE) :: tree_blocks r ++ rest))).
{ eapply Permutation_trans; [exact HB | apply Permutation_middle]. }
jrun_to LAWS ubs2tbl_ok HS HJ FT_JAL1.
{ wr_ok_ft HU2. }
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free_decision_tree.
{ wr_ok_ft HU2. }
frame_chain HF HF1 HF2. clear HF HF1 HG HG0.
cbn [ms_mem mkst] in HF2, HJ.
assert (Hlow : forall b m, In (b, m) (tree_blocks l ++ (tn_addr n, NODE_SIZE) :: tree_blocks r ++ rest) -> 4096 <= b /\ b + m <= alloc_ceiling).
{ intros b m Hbm. eapply (blocks_range _ _ LAWS L A mem md); [exact HH|]. eapply Permutation_in; [apply Permutation_sym; exact HBl | exact Hbm]. }
assert (Htl1 : tree_at segs (ms_mem ms0) l).
{ eapply tree_at_frame; [exact Htl|]. intros n' a Hn' Ha.
destruct (Hlow (tn_addr n') NODE_SIZE ltac:(apply in_app_iff; left; apply tree_blocks_in_nodes; exists n'; auto)) as [Hb0 Hb1].
mb_frame_g HF2 ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
assert (Htr1 : tree_at segs (ms_mem ms0) r).
{ eapply tree_at_frame; [exact Htr|]. intros n' a Hn' Ha.
destruct (Hlow (tn_addr n') NODE_SIZE ltac:(apply in_app_iff; right; right; apply in_app_iff; left; apply tree_blocks_in_nodes; exists n'; auto)) as [Hb0 Hb1].
mb_frame_g HF2 ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
jreg HS (10%bv:reg) as Hr10. rewrite HE32 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (sp0 + -16) with (sp0 - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms0) = sp0 - 16) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FT_STK (theight l)) (FP1 := blocks_fp (tree_blocks l))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) =>
Permutation (blocks L5 A5) ((tn_addr n, NODE_SIZE) :: tree_blocks r ++ rest));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hspm | exact HFl0
| rewrite Hspms; lia
| rewrite Hspms; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ exact (IHl _ _ _ _ _ ((tn_addr n, NODE_SIZE) :: tree_blocks r ++ rest) HPRE1 Hr10 Htl1 HBl). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. left. apply inFP_blocks_fp in Ha as (b & m & Hbm & Hab). split.
+ apply inFP_blocks_fp. exists b, m. split; [right; apply in_app_iff; left; exact Hbm | exact Hab].
+ destruct (Hlow b m ltac:(apply in_app_iff; left; exact Hbm)). lia. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5.
pose proof HJc5 as (HH5 & _ & Hhi5 & Hblk5 & _).
assert (Hin5 : In (tn_addr n, NODE_SIZE) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5 | left; reflexivity]).
assert (KR : forall b m i, In (b, m) ((tn_addr n, NODE_SIZE) :: tree_blocks r) -> 0 <= i < m ->
mbyte segs mem5 (b + i) = mbyte segs (ms_mem ms0) (b + i)).
{ intros b m i Hbm Hi. apply (Hblk5 b m i).
- eapply Permutation_in; [apply Permutation_sym; exact HBl |]. apply in_app_iff. right.
destruct Hbm as [Hbm|Hbm]; [left; exact Hbm | right; apply in_app_iff; left; exact Hbm].
- eapply blocks_perm_in; [exact HB5 |]. destruct Hbm as [Hbm|Hbm]; [left; symmetry; exact Hbm | right; apply in_app_iff; left; exact Hbm].
- exact Hi.
- intros HF1. apply inFP_blocks_fp in HF1 as (b' & m' & Hbm' & Hab').
pose proof (heap_sep_app2 _ _ LAWS L A mem md (tree_blocks l) ((tn_addr n, NODE_SIZE) :: tree_blocks r ++ rest) (b', m') (b, m) HH HBl Hbm'
ltac:(destruct Hbm as [Hbm|Hbm]; [left; exact Hbm | right; apply in_app_iff; left; exact Hbm])) as Hsep.
cbn [fst snd] in Hsep. lia. }
assert (Htr5 : tree_at segs mem5 r).
{ eapply tree_at_frame; [exact Htr1|]. intros n' a Hn' Ha. replace a with (tn_addr n' + (a - tn_addr n')) by lia.
apply (KR (tn_addr n') NODE_SIZE (a - tn_addr n')); [| lia]. right. apply tree_blocks_in_nodes. exists n'. auto. }
jafter_call_keep HS 42%nat regs5 mem5 HP5 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack segs _ _ _ 2); [exact HU2 | exact Hhi5 | lia | lia | rewrite Hspms; lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise segs _ _ _ 10); [exact HU10 | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (tn_addr n + (a - tn_addr n)) by lia.
apply (KR (tn_addr n) NODE_SIZE (a - tn_addr n)); [left; reflexivity | lia]. }
clear HS Hr10 Hr2 Hr4 Hr1 Hspms. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_free_decision_tree.
{ wr_ok_ft HU2. }
cbn [ms_regs ms_mem mkst] in HF, HJ5.
assert (HBr : Permutation (blocks L5 A5) (tree_blocks r ++ (tn_addr n, NODE_SIZE) :: rest)).
{ eapply Permutation_trans; [exact HB5 | apply Permutation_middle]. }
assert (Htr6 : tree_at segs (ms_mem ms1) r).
{ eapply tree_at_frame; [exact Htr5|]. intros n' a Hn' Ha.
destruct (Hlow (tn_addr n') NODE_SIZE ltac:(apply in_app_iff; right; right; apply in_app_iff; left; apply tree_blocks_in_nodes; exists n'; auto)) as [Hb0 Hb1].
mb_frame_g HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
jreg HS (10%bv:reg) as Hr10. rewrite HE33 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2. replace (sp0 + -16) with (sp0 - 16) in Hr2 by lia.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
assert (Hspms : spZ (ms_regs ms1) = sp0 - 16) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; lia).
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FT_STK (theight r)) (FP1 := blocks_fp (tree_blocks r))
(K := fun L6 A6 (regs6 : bvmap 5 word) (mem6 : word -> option byte) (md6 : Model) =>
Permutation (blocks L6 A6) ((tn_addr n, NODE_SIZE) :: rest));
[ exact HS | reflexivity | exact HJ5 | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hspm | exact HFr0
| rewrite Hspms; lia
| rewrite Hspms; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ exact (IHr _ _ _ _ _ ((tn_addr n, NODE_SIZE) :: rest) HPRE1 Hr10 Htr6 HBr). }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJc6 & HP6 & HB6).
exists L6, A6, regs6, mem6, md6. split; [rewrite Hr1; reflexivity|]. split; [exact HJc6|]. split; [exact HP6 | exact HB6].
- intros a Ha. left. apply inFP_blocks_fp in Ha as (b & m & Hbm & Hab). split.
+ apply inFP_blocks_fp. exists b, m. split; [right; apply in_app_iff; right; exact Hbm | exact Hab].
+ destruct (Hlow b m ltac:(apply in_app_iff; right; right; apply in_app_iff; left; exact Hbm)). lia. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HP6 & HB6). clear HJ5.
cbn [ms_regs ms_mem mkst] in HJc6, HP6.
pose proof HJc6 as (HH6 & _ & Hhi6 & Hblk6 & _).
assert (Hin6 : In (tn_addr n, NODE_SIZE) (blocks L6 A6)) by (eapply blocks_perm_in; [exact HB6 | left; reflexivity]).
assert (KR6 : forall i, 0 <= i < NODE_SIZE -> mbyte segs mem6 (tn_addr n + i) = mbyte segs (ms_mem ms1) (tn_addr n + i)).
{ intros i Hi. apply (Hblk6 (tn_addr n) NODE_SIZE i Hin5 Hin6 Hi).
intros HF1. apply inFP_blocks_fp in HF1 as (b' & m' & Hbm' & Hab').
pose proof (heap_sep_app2 _ _ LAWS L5 A5 mem5 md5 (tree_blocks r) ((tn_addr n, NODE_SIZE) :: rest) (b', m') (tn_addr n, NODE_SIZE) HH5 HBr Hbm'
ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep. lia. }
jafter_call_keep HS 58%nat regs6 mem6 HP6 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | lia | lia | rewrite Hspms; lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise segs _ _ _ 10); [ew_havoc; exact HU10 | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (tn_addr n + (a - tn_addr n)) by lia.
apply KR6. lia. }
clear HS Hr10 Hr2 Hr4 Hr1 Hspms HF HG. rename HS2 into HS.
jrun_to LAWS ubs2tbl_ok HS HJ6 ubs2_A_free.
{ wr_ok_ft HU2. }
cbn [ms_regs ms_mem mkst] in HF, HJ6.
jreg HS (10%bv:reg) as Hq10. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 10)), HU10 in Hq10.
jreg HS (4%bv:reg) as Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_mono.
{ eapply (jfree _ _ LAWS ubs2_errno_low IMG (aa_free API));
[ exact HS | reflexivity | reflexivity | exact HJ6 | exact Hin6 | exact Hq10
| exact (st_ok_reg _ _ _ _ 2%bv HS) | ew_havoc; reflexivity | exact HU2 | reflexivity | lia | unfold FT_STK; lia
| exact Hq4 | ew_havoc; rewrite (HE 4%nat 4%bv eq_refl); exact Htp | exact Hq1 | rewrite (HE 1%nat 1%bv eq_refl); exact Hra
| intros _ i Hi; exists (tn_addr n, tn_addr n + NODE_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hrm7 & Hkeep7 & Hhi7).
exists L7, A7, regs7, mem7, md7. rewrite (HE 1%nat 1%bv eq_refl). split; [reflexivity|]. split; [exact HJ7|].
split.
{ eapply regs_preserved_trans; [| exact HP7].
exact (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 58 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 42 _ _ _ ltac:(lia) (env_agree_refl _ _)))
ltac:(vm_compute; reflexivity)). }
eapply perm_after_rm1; [exact HB6 | exact Hrm7].
Qed.
Theorem ubs2_free_tree : free_tree_spec API.
Proof.
intros L A regs mem md t rest HPRE Ha0 Htree Hh HB.
pose proof (theight_nonneg t) as Hh0. unfold theight in Hh0.
pose proof (FT_STK_le_FREETREE (Z.of_nat (tree_height t)) ltac:(lia)) as Hle.
eapply SR_mono.
{ apply (free_tree_gen t L A regs mem md rest); [| exact Ha0 | exact Htree | exact HB].
eapply fn_pre_stk_le; [exact HPRE | exact Hle]. }
cbv beta. intros c' (L' & A' & regs' & mem' & md' & -> & HJ & HP & HB').
exists L', A', regs', mem', md'. split; [reflexivity|]. split; [| split; [exact HP | exact HB']].
eapply journal_stk_le; [exact HJ | apply (proj2 Hle) |]. exact (proj1 (proj2 (proj2 HPRE))).
Qed.
End S.
End c.
