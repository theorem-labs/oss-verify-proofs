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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x UI56 UI57 UI16 UI1h YP14 YP16 YI08 YI0c YI0f
YI09 UI3h UI4v UI3q UI3p UI3r.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_CL : Z := 0x14198.
Definition holds (P : Prop) : Prop := P.
Lemma in_bv5' : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst. exact Hin. Qed.
Ltac inl := apply in_bv5'; vm_compute; reflexivity.
Lemma in_wins1_false : forall lo hi i, in_wins [(lo, hi)] i = false -> ~ (lo <= i < hi).
Proof.
intros lo hi i H Hi. unfold in_wins in H. cbn [existsb fst snd] in H. rewrite Bool.orb_false_r in H.
apply andb_false_iff in H. destruct H as [H | H]; [apply Z.leb_gt in H | apply Z.ltb_ge in H]; lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis NTN : forall fx', ntn_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation segs := ubs2segs (only parsing).
Local Notation rom := (seg_rom ubs2segs) (only parsing).
Local Notation sp := (sp regs0).
Local Notation sp0 := (sp0 regs0).
Local Notation RINV := (rgba_inv (fx:=fx) API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation FPF := (FPfoot r g bef beffmt s N).
Section h.
Variables (ha pnew fimg : Z) (imgl : list Z) (C : cht) (cnt fdp : Z) (fdl pal0 : list Z).
Let p : Z := ch_p C.
Let T : Z := ch_T C.
Let E0 : list entry := ents_of pal0 fdl cnt.
Let tail : list Z := skipn (Z.to_nat (3 * cnt)) pal0.
Definition SB : list (Z * Z) := BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, 4 * cnt)].
Hypothesis Hfmt : holds (fmt = 3 \/ fmt = 4).
Hypothesis HN1 : 1 <= N.
Hypothesis Hha : holds (ha = 0 \/ (ha = 1 /\ fmt = 4)).
Hypothesis Hcnt : 256 <= cnt /\ cnt <= RGB_NMAX.
Hypothesis Hpal0 : zlen pal0 = 3 * T /\ 3 * cnt <= 3 * T.
Hypothesis Hfdl : zlen fdl = cnt.
Hypothesis HE0 : ent_ok E0 /\ List.NoDup (map fst E0) /\ zsum (fr_vals E0) <= N.
Hypothesis Htmp : ~ In (p, 3 * T) (blocks L A) /\ ~ In (fdp, 4 * cnt) (blocks L A).
Hypothesis Hnz : holds (pnew <> 0 /\ fimg <> 0 /\ fdp <> 0).
Hypothesis HTch : In T ts_chain /\ (forall b, In b (cht_blks C) -> 4096 <= fst b).
Definition cr_statics (memc : word -> option byte) : Prop :=
slots_mid regs0 cfp N memc pnew fimg /\ slots_q regs0 W bef beffmt img fmt fattr memc ha /\
fcfg_at regs0 fattr delay memc fimg 0 0 /\ rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\
cgif_at memc g s /\ img_at N img fmt memc imgl /\
obj_at segs memc (ch_c C) LAY_Cht [ch_f C; ch_h C; ch_u C; ch_p C; ch_x C; cnt; ch_T C].
Definition SBs : list (Z * Z) :=
BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++
[(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T); (ch_x C, 4 * T)].
Lemma SB_perm : Permutation SB (SBs ++ [(p, 3 * T); (fdp, 4 * cnt)]).
Proof.
unfold SB, SBs, cht_blks, cht_blocks. subst p T. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
cbn [app]. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip.
apply (Permutation_trans (l' := (ch_x C, 4 * ch_T C) :: (ch_p C, 3 * ch_T C) :: [(fdp, 4 * cnt)])); [apply perm_swap | apply Permutation_refl].
Qed.
Definition static_byte (x : Z) : Prop :=
(sp <= x < sp + 934) \/ (sp + 5040 <= x < 2 ^ 64) \/
(exists b m, In (b, m) SBs /\ b <= x < b + m).
Definition cr_unchanged (m m' : word -> option byte) : Prop :=
forall x, static_byte x -> mbyte segs m' x = mbyte segs m x.
Definition cl_slots (memc : word -> option byte) (root : Z) : Prop :=
slot regs0 memc SL_56 1 /\ slot regs0 memc SL_72 (2 ^ 64 - 1 - (sp + 936)) /\ slot regs0 memc SL_80 root.
Definition CLB : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25]%bv.
Definition cl_base (regs : bvmap 5 word) (q : Z) : Prop :=
rgba_regs regs0 regs /\ getr regs 9 = Z_to_bv 64 q /\
getr regs 22 = Z_to_bv 64 (sp + 5038) /\ getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) /\ getr regs 18 = Z_to_bv 64 (2 ^ 64 - 1 - fdp) /\
getr regs 19 = Z_to_bv 64 2 /\ getr regs 8 = Z_to_bv 64 r /\ getr regs 20 = Z_to_bv 64 (ch_c C) /\
getr regs 25 = Z_to_bv 64 p /\ getr regs 24 = Z_to_bv 64 fdp /\ getr regs 21 = Z_to_bv 64 2.
Lemma cl_base_upd : forall (regs regs' : bvmap 5 word) (KL : list reg) (q q' : Z),
(forall rr : reg, In rr KL -> getr regs' rr = getr regs rr) ->
forallb (fun x => existsb (bv_eqb x) KL) CLB = true -> getr regs' 9 = Z_to_bv 64 q' -> cl_base regs q -> cl_base regs' q'.
Proof.
intros regs regs' KL q q' K HF G9 ((R2 & R3 & R4) & _ & B22 & B23 & B18 & B19 & B8 & B20 & B25 & B24 & B21).
assert (KK : forall rr, In rr CLB -> getr regs' rr = getr regs rr).
{ intros rr Hr. apply K. apply in_bv5'. exact (proj1 (forallb_forall _ _) HF rr Hr). }
unfold cl_base, rgba_regs.
rewrite (KK 2%bv ltac:(inl)), (KK 3%bv ltac:(inl)), (KK 4%bv ltac:(inl)), (KK 22%bv ltac:(inl)), (KK 23%bv ltac:(inl)), (KK 18%bv ltac:(inl)),
(KK 19%bv ltac:(inl)), (KK 8%bv ltac:(inl)), (KK 20%bv ltac:(inl)), (KK 25%bv ltac:(inl)), (KK 24%bv ltac:(inl)), (KK 21%bv ltac:(inl)).
tauto.
Qed.
Definition cl_regs (atcl : bool) (regs : bvmap 5 word) (q Lf : Z) : Prop :=
cl_base regs q /\ getr regs 29 = Z_to_bv 64 Lf /\
(if atcl then getr regs 14 = Z_to_bv 64 (sp + 936) /\ getr regs 15 = Z_to_bv 64 512 /\ getr regs 16 = Z_to_bv 64 255 else True).
Definition cl_nodes (memc : word -> option byte) (ns : list (anode (A := entry))) (tns : list tnode) : Prop :=
elen tns = elen ns /\
(forall j, 0 <= j < elen ns -> node_mem segs memc ns tns j /\ tn_matches (tnth tns j) (node ns j)) /\
(forall j, 0 <= j < elen ns -> word_mem segs memc (sp + 936 + 8 * j) (tn_addr (tnth tns j))) /\
(forall j blc i, 0 <= j < elen ns -> In (tn_addr (tnth tns j), NODE_SIZE) blc -> 0 <= i < NODE_SIZE ->
wr_byte RGBA_STK sp0 FPF (blocks L A) blc (tn_addr (tnth tns j) + i)) /\
(forall j, 0 <= j < elen ns -> tnode_means_ok (tnth tns j)).
Definition node_blocks (tns : list tnode) (m : Z) : list (Z * Z) :=
map (fun j => (tn_addr (tnth tns j), NODE_SIZE)) (zseq 0 m).
Definition kblocks (k : list tnode) : list (Z * Z) := map (fun t => (tn_addr t, NODE_SIZE)) k.
Lemma means_of_facts : forall (t : tnode) (nd : anode (A := entry)) E lo hi,
tn_facts t nd -> ent_ok E -> 0 <= lo -> hi < elen E -> n_seg nd = zsub E lo hi -> length (tn_mean t) = 3%nat ->
tnode_means_ok t.
Proof.
intros t nd E lo hi [TF _] HE Hlo Hhi Hseg Hlen. rewrite Hseg in TF. unfold tnode_means_ok.
assert (M : forall d, 0 <= d <= 2 -> mean_ok (nth (Z.to_nat d) (tn_mean t) 0)).
{ intros d Hd. exists (wdot (dseg d E lo hi)), (wsum (dseg d E lo hi)). split; [exact (TF d Hd)|].
pose proof (wdot_bounds _ (dseg_node_ok d E lo hi HE Hlo Hhi)). lia. }
destruct (tn_mean t) as [|m0 [|m1 [|m2 [|]]]]; try discriminate Hlen.
constructor; [exact (M 0 ltac:(lia))|]. constructor; [exact (M 1 ltac:(lia))|]. constructor; [exact (M 2 ltac:(lia)) | constructor].
Qed.
Definition at_CL (fy : FPState) (regs : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(st : cstate (A := entry)) (tns : list tnode) : Prop :=
RINV Lc Ac memc mdc /\ frm_zero (@fp_csr fy) /\
cinv cnt E0 st /\ nleaves (c_ns st) <= 254 /\
cl_regs true regs (c_q st) (nleaves (c_ns st)) /\
cr_statics memc /\ cl_slots memc (tn_addr (tnth tns 0)) /\
arr8 segs memc p (pal_bytes (c_E st) ++ tail) /\ arr32 segs memc fdp (fr_vals (c_E st)) /\
val_mem segs memc (sp + 934) 2 (nleaves (c_ns st)) /\
cl_nodes memc (c_ns st) tns /\
(forall j, c_q st <= j < elen (c_ns st) -> tn_facts (tnth tns j) (node (c_ns st) j)) /\
Permutation (blocks Lc Ac) (SB ++ node_blocks tns (elen (c_ns st))).
Lemma cr_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5168 /\ NTN_STK = 8352 /\ NODE_SIZE = 56 /\ RGB_NMAX = 10000 /\
(CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ elen E0 = cnt /\ 0 <= zlen tail /\ 3 * cnt + zlen tail = 3 * T.
Proof.
do 5 (split; [reflexivity|]). split; [exact (proj1 alloc_ceiling_val)|].
split; [subst E0; apply elen_ents_of; lia|]. split; [unfold zlen; lia|].
subst tail. unfold zlen in *. rewrite length_skipn. destruct Hpal0. lia.
Qed.
Lemma sp_facts : forall Lc Ac memc mdc, RINV Lc Ac memc mdc ->
sp = sp0 - 5168 /\ sp0 mod 16 = 0 /\ sp mod 16 = 0 /\ alloc_ceiling + RGBA_STK <= sp0 /\ sp0 < 2 ^ 63 /\
(forall a, sp0 - RGBA_STK <= a < sp0 -> writable_at segs memc a).
Proof.
intros Lc Ac memc mdc (HJ & _ & _ & _ & Hal0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & Hceil & H63 & Hstw) & _).
split; [reflexivity|]. split; [exact Hal0|]. split; [| split; [exact Hceil | split; [exact H63 | exact Hstw]]].
unfold UI4v.sp, RGBA_FRAME. replace (UI4v.sp0 regs0 - 5168) with (UI4v.sp0 regs0 + (-323) * 16) by lia.
rewrite Z.mod_add; [exact Hal0 | lia].
Qed.
Lemma SB_in_p : In (p, 3 * T) SB.
Proof. unfold SB, cht_blks, cht_blocks. rewrite !in_app_iff. cbn [In]. subst p T. tauto. Qed.
Lemma SB_in_fdp : In (fdp, 4 * cnt) SB.
Proof. unfold SB. rewrite !in_app_iff. cbn [In]. tauto. Qed.
Lemma blocks_of_CL : forall Lc Ac tns m x, Permutation (blocks Lc Ac) (SB ++ node_blocks tns m) ->
(In x SB \/ In x (node_blocks tns m)) -> In x (blocks Lc Ac).
Proof. intros Lc Ac tns m x HP Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. exact Hx. Qed.
Lemma node_block_in : forall tns m j, 0 <= j < m -> In (tn_addr (tnth tns j), NODE_SIZE) (node_blocks tns m).
Proof. intros tns m j Hj. unfold node_blocks. apply in_map_iff. exists j. split; [reflexivity | apply In_zseq; lia]. Qed.
Lemma cl_heap_facts : forall Lc Ac memc mdc tns m,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (SB ++ node_blocks tns m) ->
(4096 <= p /\ p + 3 * T <= alloc_ceiling /\ p mod 16 = 0) /\
(4096 <= fdp /\ fdp + 4 * cnt <= alloc_ceiling /\ fdp mod 16 = 0) /\
disj_blocks p (3 * T) fdp (4 * cnt) /\
(forall j, 0 <= j < m -> 4096 <= tn_addr (tnth tns j) /\ tn_addr (tnth tns j) + NODE_SIZE <= alloc_ceiling /\ tn_addr (tnth tns j) mod 16 = 0 /\
disj_blocks (tn_addr (tnth tns j)) NODE_SIZE p (3 * T) /\
disj_blocks (tn_addr (tnth tns j)) NODE_SIZE fdp (4 * cnt)) /\
(forall b n j, In (b, n) SB -> 0 <= j < m -> b + n <= tn_addr (tnth tns j) \/ tn_addr (tnth tns j) + NODE_SIZE <= b) /\
(forall b n, In (b, n) SB -> (b, n) <> (p, 3 * T) -> b + n <= p \/ p + 3 * T <= b) /\
(forall b n, In (b, n) SB -> (b, n) <> (fdp, 4 * cnt) -> b + n <= fdp \/ fdp + 4 * cnt <= b).
Proof.
intros Lc Ac memc mdc tns m HH HP. pose proof cr_consts as (_ & _ & _ & HNS & _ & Hac & _ & Htl & HT3).
assert (Hp : In (p, 3 * T) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HP | left; apply SB_in_p]).
assert (Hf : In (fdp, 4 * cnt) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HP | left; apply SB_in_fdp]).
assert (SEP : forall x y, In x SB -> In y (node_blocks tns m) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x).
{ intros x y Hx Hy. exact (heap_sep_app2 ubs2_msyms MR LAWS Lc Ac memc mdc SB (node_blocks tns m) x y HH HP Hx Hy). }
split; [exact (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc p (3 * T) HH Hp ltac:(lia))|].
split; [exact (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc fdp (4 * cnt) HH Hf ltac:(lia))|].
split. { unfold disj_blocks. destruct (heap_sep_in2 ubs2_msyms MR LAWS Lc Ac memc mdc (p, 3 * T) (fdp, 4 * cnt) HH Hp Hf) as [X|X]; [| cbn in X; lia | cbn in X; lia].
intros Heq. injection Heq as E1 E2. destruct Htmp as [H1 H2]. rewrite E1, E2 in H1.
pose proof (heap_sep_in2 ubs2_msyms MR LAWS Lc Ac memc mdc (fdp, 4 * cnt) (fdp, 4 * cnt) HH Hf Hf) as Y. cbn in Y.
clear Y. exfalso.
pose proof (Permutation_NoDup' := I). clear Permutation_NoDup'.
assert (Hdup : exists l1 l2 l3, SB ++ node_blocks tns m = l1 ++ (fdp, 4 * cnt) :: l2 ++ (fdp, 4 * cnt) :: l3).
{ unfold SB, cht_blks, cht_blocks. subst p T. rewrite <- E1, <- E2.
exists (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)]).
exists [(ch_x C, 4 * ch_T C)], (node_blocks tns m). rewrite E1, E2. rewrite <- !app_assoc. cbn [app]. repeat (f_equal; try reflexivity). }
destruct Hdup as (l1 & l2 & l3 & Hdup). rewrite Hdup in HP.
assert (HP' : Permutation (blocks Lc Ac) ((fdp, 4 * cnt) :: l1 ++ (l2 ++ (fdp, 4 * cnt) :: l3))).
{ eapply Permutation_trans; [exact HP|]. apply Permutation_sym. apply Permutation_middle. }
pose proof (heap_sep_perm ubs2_msyms MR LAWS Lc Ac memc mdc (fdp, 4 * cnt) _ (fdp, 4 * cnt) HH HP' ltac:(apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) as Z1.
cbn in Z1. lia. }
split. { intros j Hj. pose proof (node_block_in tns m j Hj) as Hn.
assert (Hb : In (tn_addr (tnth tns j), NODE_SIZE) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HP | right; exact Hn]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc _ _ HH Hb ltac:(rewrite HNS; lia)) as (B0 & B1 & B2).
pose proof (SEP _ _ SB_in_p Hn) as S1. pose proof (SEP _ _ SB_in_fdp Hn) as S2. cbn [fst snd] in S1, S2.
unfold disj_blocks. repeat split; try assumption; lia. }
split. { intros b n j Hb Hj. pose proof (SEP _ _ Hb (node_block_in tns m j Hj)) as S1. cbn [fst snd] in S1. lia. }
split. { intros b n Hb Hne. assert (Hb' : In (b, n) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HP | left; exact Hb]).
pose proof (heap_sep_in2 ubs2_msyms MR LAWS Lc Ac memc mdc (b, n) (p, 3 * T) HH Hb' Hp Hne) as S1. cbn in S1. lia. }
intros b n Hb Hne. assert (Hb' : In (b, n) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HP | left; exact Hb]).
pose proof (heap_sep_in2 ubs2_msyms MR LAWS Lc Ac memc mdc (b, n) (fdp, 4 * cnt) HH Hb' Hf Hne) as S1. cbn in S1. lia.
Qed.
Lemma blocks_of_perm : forall Lc Ac (more : list (Z * Z)) x, Permutation (blocks Lc Ac) (SB ++ more) ->
(In x SB \/ In x more) -> In x (blocks Lc Ac).
Proof. intros Lc Ac more x HP Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. exact Hx. Qed.
Lemma node_blocks_app : forall tns k m, elen tns = m -> 0 <= m -> node_blocks (tns ++ k) (m + elen k) = node_blocks tns m ++ kblocks k.
Proof.
intros tns k m Hm H0. revert tns m Hm H0. induction k as [|t k IH] using rev_ind; intros tns m Hm H0.
- cbn [kblocks map elen length Z.of_nat]. rewrite !app_nil_r, Z.add_0_r. reflexivity.
- rewrite elen_app1.
transitivity ((node_blocks tns m ++ kblocks k) ++ [(tn_addr t, NODE_SIZE)]); [| unfold kblocks; rewrite map_app, <- app_assoc; reflexivity].
rewrite <- (IH tns m Hm H0).
replace (m + (elen k + 1)) with ((m + elen k) + 1) by lia. unfold node_blocks. rewrite map_zseq_snoc by (unfold elen; lia).
rewrite Z.add_0_l. f_equal.
+ apply map_zseq_ext. intros j Hj. rewrite app_assoc. rewrite (tnth_app_l (tns ++ k) [t]) by (unfold elen in *; rewrite length_app; lia). reflexivity.
+ f_equal. f_equal. rewrite app_assoc. rewrite tnth_app_r by (unfold elen in *; rewrite length_app; lia). unfold elen in *. rewrite length_app.
replace (m + Z.of_nat (length k) - Z.of_nat (length tns + length k)%nat) with 0 by lia. reflexivity.
Qed.
Lemma node_blocks_nth : forall tns m j, 0 <= j < m -> nth_error (node_blocks tns m) (Z.to_nat j) = Some (tn_addr (tnth tns j), NODE_SIZE).
Proof.
intros tns m j Hj. unfold node_blocks. rewrite nth_error_map.
rewrite (nth_error_nth' _ 0) by (rewrite zseq_length; lia). rewrite nth_zseq by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma nodes_disjoint : forall Lc Ac memc mdc tns m j j',
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (SB ++ node_blocks tns m) ->
0 <= j < m -> 0 <= j' < m -> j <> j' ->
tn_addr (tnth tns j) + NODE_SIZE <= tn_addr (tnth tns j') \/ tn_addr (tnth tns j') + NODE_SIZE <= tn_addr (tnth tns j).
Proof.
intros Lc Ac memc mdc tns m j j' HH HP Hj Hj' Hne.
destruct (nth_error_split _ _ (node_blocks_nth tns m j Hj)) as (l1 & l2 & Hspl & Hl1).
assert (Hy : In (tn_addr (tnth tns j'), NODE_SIZE) (l1 ++ l2)).
{ pose proof (node_blocks_nth tns m j' Hj') as Hn'. rewrite Hspl in Hn'.
destruct (Nat.lt_ge_cases (Z.to_nat j') (length l1)) as [Hlt|Hge].
- apply in_app_iff. left. rewrite nth_error_app1 in Hn' by exact Hlt. eapply nth_error_In. exact Hn'.
- apply in_app_iff. right. rewrite nth_error_app2 in Hn' by exact Hge.
destruct (Z.to_nat j' - length l1)%nat as [|k] eqn:Ek; [lia|]. cbn [nth_error] in Hn'. eapply nth_error_In. exact Hn'. }
assert (HP' : Permutation (blocks Lc Ac) ((tn_addr (tnth tns j), NODE_SIZE) :: SB ++ (l1 ++ l2))).
{ eapply Permutation_trans; [exact HP|]. rewrite Hspl. rewrite app_assoc. apply Permutation_sym.
replace ((tn_addr (tnth tns j), NODE_SIZE) :: SB ++ l1 ++ l2) with ((tn_addr (tnth tns j), NODE_SIZE) :: (SB ++ l1) ++ l2) by (rewrite app_assoc; reflexivity).
apply Permutation_middle. }
pose proof (heap_sep_perm ubs2_msyms MR LAWS Lc Ac memc mdc _ _ (tn_addr (tnth tns j'), NODE_SIZE) HH HP' ltac:(apply in_app_iff; right; exact Hy)) as S1.
cbn [fst snd] in S1. exact S1.
Qed.
Lemma SBs_in_SB : forall x, In x SBs -> In x SB.
Proof. intros x Hx. eapply Permutation_in; [apply Permutation_sym; apply SB_perm|]. apply in_app_iff. left. exact Hx. Qed.
Lemma cr_unchanged_intro : forall Lc Ac memc mdc tns m (memc' : word -> option byte),
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (SB ++ node_blocks tns m) -> alloc_ceiling + RGBA_STK <= sp0 -> sp0 < 2 ^ 63 ->
(forall x, 0 <= x < 2 ^ 64 ->
~ (sp - NTN_STK <= x < sp) -> ~ (sp + 934 <= x < sp + 5040) -> ~ (p <= x < p + 3 * T) -> ~ (fdp <= x < fdp + 4 * cnt) ->
(forall j, 0 <= j < m -> ~ (tn_addr (tnth tns j) <= x < tn_addr (tnth tns j) + NODE_SIZE)) ->
mbyte segs memc' x = mbyte segs memc x) ->
cr_unchanged memc memc'.
Proof.
intros Lc Ac memc mdc tns m memc' HH HP Hceil H63 HK x Hx.
pose proof cr_consts as (HRS & HFR & HNT & HNS & _ & Hac & _ & Htl & HT3).
assert (Hsp : sp = sp0 - 5168) by reflexivity.
destruct (cl_heap_facts Lc Ac memc mdc tns m HH HP) as (Pp & Pf & _ & Pn & Psn & Psp & Psf).
destruct Hx as [Hx | [Hx | (b & n & Hb & Hx)]].
- apply HK; [lia | lia | lia | lia | lia |]. intros j Hj. destruct (Pn j Hj) as (_ & B1 & _). lia.
- apply HK; [lia | lia | lia | lia | lia |]. intros j Hj. destruct (Pn j Hj) as (_ & B1 & _). lia.
- pose proof (SBs_in_SB _ Hb) as Hb'.
assert (Hbb : In (b, n) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HP | left; exact Hb']).
destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n (x - b) HH Hbb ltac:(lia)) as (_ & B0 & B1 & _).
assert (SEP2 : forall y, In y [(p, 3 * T); (fdp, 4 * cnt)] -> b + n <= fst y \/ fst y + snd y <= b).
{ intros y Hy. apply (heap_sep_app2 ubs2_msyms MR LAWS Lc Ac memc mdc SBs ([(p, 3 * T); (fdp, 4 * cnt)] ++ node_blocks tns m) (b, n) y HH); [| exact Hb | apply in_app_iff; left; exact Hy].
eapply Permutation_trans; [exact HP|]. rewrite app_assoc. apply Permutation_app_tail. apply SB_perm. }
pose proof (SEP2 (p, 3 * T) ltac:(left; reflexivity)) as S1. pose proof (SEP2 (fdp, 4 * cnt) ltac:(right; left; reflexivity)) as S2. cbn [fst snd] in S1, S2.
apply HK; [lia | lia | lia | lia | lia |]. intros j Hj. pose proof (Psn b n j Hb' Hj). lia.
Qed.
Lemma word_mem_frame : forall (m m' : word -> option byte) a v,
word_mem segs m a v -> (forall i, 0 <= i < 8 -> mbyte segs m' (a + i) = mbyte segs m (a + i)) -> word_mem segs m' a v.
Proof. intros m m' a v Hw Hf k Hk. rewrite Hf by lia. apply Hw. exact Hk. Qed.
Lemma SBs_perm_cgif : Permutation SBs (cgif_blocks g s N ++ ((r, RGB_SIZE) :: optb bef (beffmt * N) ++ img_block img fmt N ++ rest ++
[(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T); (ch_x C, 4 * T)])).
Proof. unfold SBs, BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. Qed.
Lemma statics_kept0 : forall memc memc', cr_statics memc ->
(forall x, sp + 16 <= x < sp + 56 \/ sp + 64 <= x < sp + 72 \/ sp + 88 <= x < sp + 934 -> mbyte segs memc' x = mbyte segs memc x) ->
(forall b n, In (b, n) SBs -> forall i, 0 <= i < n -> mbyte segs memc' (b + i) = mbyte segs memc (b + i)) ->
slot regs0 memc' SL_N N -> cr_statics memc'.
Proof.
intros memc memc' (Hsm & Hsq & Hfc & Hro & Hcg & Him & Hch) HU BLK H8.
assert (LOW : forall a, (sp + 16 <= a /\ a + 8 <= sp + 56) \/ (sp + 64 <= a /\ a + 8 <= sp + 72) \/ (sp + 88 <= a /\ a + 8 <= sp + 934) ->
forall i, 0 <= i < 8 -> mbyte segs memc' (a + i) = mbyte segs memc (a + i)).
{ intros a H1 i Hi. apply HU. lia. }
unfold cr_statics. unfold slots_mid, slots_q, slots_h, slot, SL_N, SL_cfp, SL_new, SL_fimg, SL_64, SL_88, SL_104, SL_112, SL_120, SL_32, SL_40 in *.
destruct Hsm as (S1 & S2 & S3 & S4). destruct Hsq as ((Q1 & Q2 & Q3 & Q4 & Q5) & Q6 & Q7).
split; [split; [exact H8 | repeat split; (eapply word_mem_frame; [eassumption | apply LOW; lia])]|].
split; [repeat split; (eapply word_mem_frame; [eassumption | apply LOW; lia])|].
split. { unfold fcfg_at, OFF_fcfg, OFF_apal in *. eapply (obj_at_transport_range _ _ _ _ _ _ 32); [exact Hfc | reflexivity |]. intros i Hi. apply HU. lia. }
split. { unfold rgb_obj in *. eapply obj_at_transport_range; [exact Hro | apply lay_inside_Rgb |]. apply (BLK r RGB_SIZE). unfold SBs, BASE. left. reflexivity. }
split. { first [eapply (cgif_at_kept _ _ g s N SBs) | eapply (cgif_at_kept API _ _ g s N SBs)]; [apply SBs_perm_cgif | exact Hcg |]. intros b n i Hb Hi. apply (BLK b n Hb i Hi). }
split. { destruct Him as [Ha Hl]. split; [|exact Hl]. eapply arr8_frame; [exact Ha|]. intros a H1. replace a with (img + (a - img)) by lia. apply (BLK img (fmt * N)); [|lia].
unfold SBs, BASE. apply in_app_iff. left. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block, fmt_okb. pose proof Hfmt as Hfmt'. unfold holds in Hfmt'. destruct Hfmt' as [-> | ->]; left; reflexivity. }
eapply obj_at_transport_range; [exact Hch | apply lay_inside_Cht |]. apply (BLK (ch_c C) CHT_SIZE). unfold SBs. rewrite !in_app_iff. right. right. left. reflexivity.
Qed.
Lemma statics_kept : forall memc memc', cr_statics memc -> cr_unchanged memc memc' -> cr_statics memc'.
Proof.
intros memc memc' STAT HU. apply (statics_kept0 memc memc' STAT).
- intros x Hx. apply HU. left. lia.
- intros b n Hb i Hi. apply HU. right. right. exists b, n. split; [exact Hb | lia].
- destruct STAT as ((S8 & _) & _). unfold slot, SL_N in *. eapply word_mem_frame; [exact S8|]. intros i Hi. apply HU. left. lia.
Qed.
Lemma cl_slots_kept : forall memc memc' root, cl_slots memc root -> cr_unchanged memc memc' -> cl_slots memc' root.
Proof.
intros memc memc' root (S56 & S72 & S80) HU. unfold cl_slots, slot, SL_56, SL_72, SL_80 in *.
split; [|split]; (eapply word_mem_frame; [eassumption|]); intros i Hi; apply HU; left; lia.
Qed.
Lemma rgba_inv_kept : forall Lc Ac memc mdc Lc' Ac' memc' mdc',
RINV Lc Ac memc mdc -> journal ubs2_msyms MR RGBA_STK sp0 FPF L A mem0 md0 Lc' Ac' memc' mdc' -> st_init_done Ac' = true ->
(forall x, sp + 5040 <= x < 2 ^ 64 -> mbyte segs memc' x = mbyte segs memc x) -> RINV Lc' Ac' memc' mdc'.
Proof.
intros Lc Ac memc mdc Lc' Ac' memc' mdc' HI HJ' Hid' HK.
destruct HI as (HJ & Hid & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hrest').
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & Hceil & H63 & _) & _). pose proof cr_consts as (HRS & _). rewrite HRS in Hceil.
assert (Hsp : sp = sp0 - 5168) by reflexivity.
split; [exact HJ'|]. split; [exact Hid'|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { intros j rr Hj k Hk. assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite HK by lia. apply (HRA j rr Hj). exact Hk. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply obj_at_transport_range; [exact Hcfp | apply lay_inside_RgbFrameConfig |]. intros i Hi. unfold RGBFC_SIZE in *. apply HK. lia. }
split; [exact Hro | exact Hrest'].
Qed.
Lemma node_mem_kept : forall (memc memc' : word -> option byte) ns tns j,
node_mem segs memc ns tns j ->
(forall i, 0 <= i < NODE_SIZE -> mbyte segs memc' (tn_addr (tnth tns j) + i) = mbyte segs memc (tn_addr (tnth tns j) + i)) ->
node_mem segs memc' ns tns j.
Proof. intros. eapply node_mem_frame; eassumption. Qed.
Definition at_SPLIT (fy : FPState) (regs : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(st : cstate (A := entry)) (tns : list tnode) (E' : list entry) (i : Z) : Prop :=
let ns := c_ns st in let q := c_q st in let nd := node ns q in
RINV Lc Ac memc mdc /\ frm_zero (@fp_csr fy) /\
cinv cnt E0 st /\ nleaves ns <= 254 /\ 0 <= q < elen ns /\ n_lo nd < n_hi nd /\
(exists P, pdone dentry P (n_lo nd) (n_hi nd) (c_E st) E' i) /\
cl_regs false regs q (nleaves ns) /\
getr regs 27 = Z_to_bv 64 (tn_addr (tnth tns q)) /\ getr regs 26 = Z_to_bv 64 i /\
cr_statics memc /\ cl_slots memc (tn_addr (tnth tns 0)) /\
arr8 segs memc p (pal_bytes E' ++ tail) /\ arr32 segs memc fdp (fr_vals E') /\
val_mem segs memc (sp + 934) 2 (nleaves ns) /\
cl_nodes memc ns tns /\
(forall j, q <= j < elen ns -> tn_facts (tnth tns j) (node ns j)) /\
Permutation (blocks Lc Ac) (SB ++ node_blocks tns (elen ns)).
Definition at_DONE (fy : FPState) (regs : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(st : cstate (A := entry)) (tns : list tnode) : Prop :=
let ns := c_ns st in
RINV Lc Ac memc mdc /\ frm_zero (@fp_csr fy) /\
cinv cnt E0 st /\ nleaves ns = 255 /\
cl_base regs (c_q st) /\
cr_statics memc /\ cl_slots memc (tn_addr (tnth tns 0)) /\
arr8 segs memc p (pal_bytes (c_E st) ++ tail) /\
cl_nodes memc ns tns /\
Permutation (blocks Lc Ac) (SB ++ node_blocks tns (elen ns)).
Definition at_FAIL (fy : FPState) (regs : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ns : list (anode (A := entry))) (tns : list tnode) (Lb : Z) : Prop :=
RINV Lc Ac memc mdc /\ frm_zero (@fp_csr fy) /\
par_ok ns /\ YP16.tree_ok ns 0 (Z.to_nat Lb) /\ 0 <= Lb <= 255 /\
(exists q', cl_base regs q') /\
cr_statics memc /\ cl_slots memc (tn_addr (tnth tns 0)) /\ (exists E', arr8 segs memc p (pal_bytes E' ++ tail) /\ Permutation E0 E') /\
elen tns = elen ns /\
(forall j, 0 <= j < elen ns -> node_mem segs memc ns tns j /\ length (tn_mean (tnth tns j)) = 3%nat /\ tn_addr (tnth tns j) <> 0) /\
Permutation (blocks Lc Ac) (SB ++ node_blocks tns (elen ns)).
Definition K_CLn (q : Z) : Prop := forall fy regs Lc Ac memc mdc st tns,
c_q st = q -> at_CL fy regs Lc Ac memc mdc st tns -> SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Definition K_DONE : Prop := forall fy regs Lc Ac memc mdc st tns,
at_DONE fy regs Lc Ac memc mdc st tns -> SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_QT) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Definition K_FAIL : Prop := forall fy regs Lc Ac memc mdc ns tns Lb,
at_FAIL fy regs Lc Ac memc mdc ns tns Lb -> SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_XT) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Definition kid_ok (memc : word -> option byte) (k : list tnode) (res lo hi cidx : Z) (seg : list entry) : Prop :=
match k with
| [] => res = 0
| [t] => res = tn_addr t /\ tn_addr t <> 0 /\ tn_imin t = lo /\ tn_imax t = hi /\ tn_cidx t = cidx /\ tnode_wf t /\
(exists c0 c1, obj_at segs memc (tn_addr t) LAY_Node (node_vals c0 c1 t 1)) /\
tn_facts t (mkN lo hi true cidx None None 0 0 seg) /\
(forall blc j, In (tn_addr t, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte RGBA_STK sp0 FPF (blocks L A) blc (tn_addr t + j))
| _ => False
end.
Definition cl_nodes_but (memc : word -> option byte) (ns : list (anode (A := entry))) (tns : list tnode) (q : Z) : Prop :=
elen tns = elen ns /\
(forall j, 0 <= j < elen ns -> j <> q -> node_mem segs memc ns tns j) /\
(forall j, 0 <= j < elen ns -> tn_matches (tnth tns j) (node ns j)) /\
(forall j, 0 <= j < elen ns -> word_mem segs memc (sp + 936 + 8 * j) (tn_addr (tnth tns j))) /\
(forall j blc i, 0 <= j < elen ns -> In (tn_addr (tnth tns j), NODE_SIZE) blc -> 0 <= i < NODE_SIZE ->
wr_byte RGBA_STK sp0 FPF (blocks L A) blc (tn_addr (tnth tns j) + i)) /\
(forall j, 0 <= j < elen ns -> tnode_means_ok (tnth tns j)).
Definition at_S23 (second : bool) (fy : FPState) (regs : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(st : cstate (A := entry)) (tns : list tnode) (E' : list entry) (i : Z) (k0 k1 : list tnode) (res0 res1 : Z) : Prop :=
let ns := c_ns st in let q := c_q st in let nd := node ns q in let tn := tnth tns q in let Lf := nleaves ns in
RINV Lc Ac memc mdc /\ frm_zero (@fp_csr fy) /\
cinv cnt E0 st /\ Lf <= 254 /\ 0 <= q < elen ns /\ n_lo nd < n_hi nd /\
(exists P, pdone dentry P (n_lo nd) (n_hi nd) (c_E st) E' i) /\
cl_base regs q /\
getr regs 27 = Z_to_bv 64 (tn_addr tn) /\ getr regs 26 = Z_to_bv 64 i /\ getr regs 10 = Z_to_bv 64 (if second then res1 else res0) /\
cr_statics memc /\ cl_slots memc (tn_addr (tnth tns 0)) /\
arr8 segs memc p (pal_bytes E' ++ tail) /\ arr32 segs memc fdp (fr_vals E') /\
val_mem segs memc (sp + 934) 2 (Lf - 1 + elen k0 + (if second then elen k1 else 0)) /\
(exists c0 c1, obj_at segs memc (tn_addr tn) LAY_Node (node_vals (if second then res0 else c0) c1 tn 0)) /\
cl_nodes_but memc ns tns q /\
(forall j, q < j < elen ns -> tn_facts (tnth tns j) (node ns j)) /\
kid_ok memc k0 res0 (n_lo nd) (i - 1) (n_col nd) (zsub E' (n_lo nd) (i - 1)) /\
(if second then kid_ok memc k1 res1 i (n_hi nd) (Lf - 1 + elen k0) (zsub E' i (n_hi nd)) else k1 = []) /\
Permutation (blocks Lc Ac) (SB ++ node_blocks tns (elen ns) ++ kblocks (k0 ++ k1)).
Definition at_XDm (fy : FPState) (regs : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
RINV Lc Ac memc mdc /\ frm_zero (@fp_csr fy) /\ rgba_regs regs0 regs /\
(getr regs 21 = Z_to_bv 64 2 /\ getr regs 20 = Z_to_bv 64 (ch_c C) /\ getr regs 8 = Z_to_bv 64 r /\ getr regs 18 = Z_to_bv 64 pnew) /\ getr regs 24 = Z_to_bv 64 fdp /\
cr_statics memc /\ arr8 segs memc p pal0 /\ Permutation (blocks Lc Ac) SB.
Definition K_XDm : Prop := forall fy regs Lc Ac memc mdc,
at_XDm fy regs Lc Ac memc mdc -> SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_XD) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation KQT := (K_QT (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KXT := (K_XT (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KXD := (K_XD (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Lemma chtq_of_statics : forall memc E, cr_statics memc -> arr8 segs memc p (pal_bytes E ++ tail) -> Permutation E0 E ->
chtq_ok memc C cnt (pal_bytes E ++ tail).
Proof.
intros memc E STAT Hpa HP. pose proof cr_consts as (_ & _ & _ & _ & _ & _ & HlenE0 & Htl & HT3). destruct STAT as (_ & _ & _ & _ & _ & _ & Sch).
split; [exact Sch|]. split; [exact Hpa|]. split; [| exact HTch].
rewrite zlen_app_pal. replace (elen E) with (elen E0) by (unfold elen; rewrite (Permutation_length HP); reflexivity). rewrite HlenE0. fold T. lia.
Qed.
Theorem XD_pack : KXD -> K_XDm.
Proof.
intros K fy regs Lc Ac memc mdc (HINV & Hfrm & RR & (G21 & Gc & Gr & G18) & G24 & STAT & Hpa & HB).
pose proof STAT as ((_ & _ & _ & S48) & Ssq & Sfc & Sro & Scg & Sim & Sch). pose proof Hnz as Hnz'. unfold holds in Hnz'. destruct Hnz' as (Z1 & Z2 & Z3).
pose proof Hfmt as Hfmt'. unfold holds in Hfmt'.
apply (K fy regs Lc Ac memc mdc ha pnew fimg C cnt pal0 fdp (4 * cnt) Hfrm).
split; [exact HINV|]. split; [exact RR|]. split; [exact Hfmt'|]. split; [exact G24|]. split; [exact G18|]. split; [exact Gc|]. split; [exact G21|]. split; [exact Gr|].
split; [exact S48|]. split; [exact Sro|]. split; [exact Scg|].
split; [split; [exact Sch|]; split; [exact Hpa|]; split; [| exact HTch]; fold T; lia|].
split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. exact HB.
Qed.
Theorem XT_pack : KXT -> K_FAIL.
Proof.
intros K fy regs Lc Ac memc mdc ns tns Lb (HINV & Hfrm & PO & TOK & HLb & (q' & CB) & STAT & (_ & _ & S80) & (E' & Hpa & HPE) & Hlen & NDS & HB).
destruct CB as (RR & _ & _ & _ & _ & _ & Gr & Gc & _ & G24 & G21).
pose proof STAT as ((_ & _ & S24 & S48) & Ssq & Sfc & Sro & Scg & Sim & Sch). pose proof Hnz as Hnz'. unfold holds in Hnz'. destruct Hnz' as (Z1 & Z2 & Z3).
pose proof Hfmt as Hfmt'. unfold holds in Hfmt'.
pose proof (tree_ok_node _ _ _ TOK) as [Hm0 Hh1].
set (t := build ns tns 0 (Z.to_nat Lb)).
apply (K fy regs Lc Ac memc mdc ha pnew fimg C cnt (pal_bytes E' ++ tail) fdp (4 * cnt) t Hfrm).
split; [exact HINV|]. split; [exact RR|]. split; [exact Hfmt'|].
split; [exact G24|]. split; [exact Gc|]. split; [exact G21|]. split; [exact Gr|].
split; [subst t; rewrite build_root by exact Hh1; exact S80|].
split; [exact S24|]. split; [exact S48|]. split; [exact Sro|]. split; [exact Scg|]. split; [exact (chtq_of_statics memc E' STAT Hpa HPE)|].
split; [subst t; apply (build_at segs memc ns tns _ 0 TOK); intros x Hx; exact (NDS x Hx)|].
split; [subst t; pose proof (build_height ns tns 0 (Z.to_nat Lb)); unfold TREE_HMAX; lia|].
split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
eapply Permutation_trans; [exact HB|]. unfold SB. rewrite <- !app_assoc. repeat (apply Permutation_app_head).
apply Permutation_sym. subst t. apply (build_blocks_root ns tns (Z.to_nat Lb) PO TOK).
Qed.
Theorem QT_pack : KQT -> K_DONE.
Proof.
intros K fy regs Lc Ac memc mdc [E ns q] tns (HINV & Hfrm & CINV & HL & CB & STAT & (_ & _ & S80) & Hpa & NODES & HB).
destruct CB as (RR & _ & _ & _ & _ & _ & Gr & Gc & _ & G24 & G21).
cbn [c_E c_ns c_q] in CINV, HL, Hpa, NODES, HB.
pose proof STAT as (Ssm & Ssq & Sfc & Sro & Scg & Sim & Sch). pose proof Hnz as Hnz'. unfold holds in Hnz'. destruct Hnz' as (Z1 & Z2 & Z3).
pose proof Hfmt as Hfmt'. unfold holds in Hfmt'. pose proof Hha as Hha'. unfold holds in Hha'.
pose proof cr_consts as (HRS & HFR & HNT & HNS & HNM & Hac & HlenE0 & Htl & HT3).
destruct NODES as (Hlen & NM & NL & NW & MOK).
pose proof (cinv_counts cnt E0 _ CINV) as (C1a & C1b & C1c & C1d & C1e). cbn [c_E c_ns c_q] in C1a, C1b, C1c, C1d, C1e.
pose proof (cinv_root_ok cnt E0 _ CINV) as TOK. cbn [c_ns] in TOK. rewrite HL in TOK.
pose proof (cinv_par_ok cnt E0 _ CINV) as PO. cbn [c_ns] in PO.
pose proof (proj1 (proj1 HINV)) as HH.
destruct (cl_heap_facts Lc Ac memc mdc tns (elen ns) HH HB) as (_ & _ & _ & Pn & _).
set (t := build ns tns 0 (Z.to_nat 255)).
apply (K fy regs Lc Ac memc mdc ha pnew fimg imgl C cnt fdp (pal_bytes E ++ tail) t Hfrm).
split; [exact HINV|]. split; [exact RR|]. split; [exact Hfmt'|]. split; [exact HN1|]. split; [exact Hha'|]. split; [lia|].
split; [exact G24|]. split; [exact Gc|]. split; [exact Gr|]. split; [exact G21|].
split; [exact Ssm|]. split; [exact Ssq|].
split; [subst t; rewrite build_root by lia; exact S80|].
split; [exact Sfc|]. split; [exact Sro|]. split; [exact Scg|]. split; [exact Sim|].
split; [exact (chtq_of_statics memc E STAT Hpa C1e)|].
split.
{
split; [subst t; apply (build_at segs memc ns tns _ 0 TOK); intros x Hx; destruct (NM x Hx) as [H1 (_ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tz)]; auto|].
split. { subst t. apply (build_full ns tns _ 0 TOK). intros x Hx Hl. destruct (cinv_kids cnt E0 _ CINV x ltac:(cbn; exact Hx) Hl) as (c & K0 & K1 & _). exists c. auto. }
split; [subst t; pose proof (build_height ns tns 0 (Z.to_nat 255)); unfold TREE_HMAX; lia|].
split; [subst t; apply (build_forall tnode_wf ns tns _ 0 PO TOK); intros x Hx; exact (proj1 (proj2 (proj2 (proj2 (proj2 (NM x Hx))))))|].
split; [subst t; apply (build_forall tnode_means_ok ns tns _ 0 PO TOK); intros x Hx; exact (MOK x Hx)|].
intros n Hn. subst t. destruct (In_nodes_build_root ns tns _ n PO TOK Hn) as (j & Hj & ->). destruct (Pn j Hj) as (B0 & B1 & B16 & _). auto. }
split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
eapply Permutation_trans; [exact HB|]. unfold SB. rewrite <- !app_assoc. repeat (apply Permutation_app_head).
apply Permutation_sym. subst t. apply (build_blocks_root ns tns (Z.to_nat 255) PO TOK).
Qed.
Theorem SPLIT_to_S2 : forall fy regs Lc Ac memc mdc st tns E' i Q,
at_SPLIT fy regs Lc Ac memc mdc st tns E' i ->
(forall fy' regs' Lc' Ac' memc' mdc' k0 res0, at_S23 false fy' regs' Lc' Ac' memc' mdc' st tns E' i k0 [] res0 0 ->
SR segs (mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_S2) memc' rom) mdc') Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_SPLIT) memc rom) mdc) Q.
Proof.
intros fy regs Lc Ac memc mdc [E ns q] tns E' i Q HAT HK.
unfold at_SPLIT in HAT. cbn [c_E c_ns c_q] in HAT.
destruct HAT as (HINV & Hfrm & CINV & HLf & Hq & Hlohi & (P & PD) & (CB & G29 & _) & G27 & G26 & STAT & SLOTS & Hpa & Hfa & Vnln & NODES & FACTS & HB).
pose proof cr_consts as (HRS & HFR & HNT & HNS & HNM & Hac & HlenE0 & Htl & HT3).
destruct (sp_facts Lc Ac memc mdc HINV) as (Hsp & Hal0 & Hal16 & Hceil & H63 & Hstw). rewrite HRS in Hceil, Hstw.
pose proof HINV as (HJ & Hinit & _ & Hra0 & _ & Htp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _).
pose proof CB as ((G2 & G3 & G4) & G9 & G22 & G23 & G18 & G19 & G8 & G20 & G25 & G24 & G21).
destruct NODES as (Hlen & NM & NL & NW & MOK).
set (m := elen ns) in *. set (Lf := nleaves ns) in *. set (nd := node ns q) in *. set (tn := tnth tns q) in *.
set (a := tn_addr tn) in *. set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
destruct HE0 as (HE0ok & HE0nd & HE0sum).
pose proof (cinv_counts cnt E0 _ CINV) as (C1a & C1b & C1c & C1d & C1e). cbn [c_E c_ns c_q] in C1a, C1b, C1c, C1d, C1e. fold m Lf in C1a, C1b, C1c.
pose proof (cinv_node cnt E0 _ CINV q ltac:(cbn; lia)) as CN. cbn [c_ns] in CN. fold nd in CN. cbv zeta in CN. fold lo hi in CN.
destruct CN as (CN1 & CN2 & CN3 & CN4 & CN5). fold Lf in CN4, CN5.
pose proof (cinv_unprocessed_leaf cnt E0 _ CINV q ltac:(cbn; lia)) as Hleaf. cbn [c_ns] in Hleaf. fold nd in Hleaf.
destruct (NM q ltac:(lia)) as [NMq TMq]. fold nd tn in NMq, TMq. unfold node_mem in NMq. fold nd tn in NMq. rewrite Hleaf in NMq.
destruct NMq as (c0 & c1 & OBJq). fold a in OBJq.
pose proof TMq as (Timin & Timax & Tcidx & Twf & Tnz). fold lo in Timin. fold hi in Timax.
assert (HEok : ent_ok E /\ List.NoDup (map fst E)) by (split; [exact (ent_ok_perm _ _ C1e HE0ok) | exact (NoDup_fst_perm _ _ C1e HE0nd)]).
destruct HEok as [HEok HEnd].
destruct (kids_segments P lo hi E E' i PD ltac:(lia) ltac:(rewrite C1d; lia) HEok) as (HlenE' & HE'ok & Ki1 & Ki2 & Ki3 & Ki4 & Kw).
pose proof PD as (PDi & PDlen & PDperm & _).
assert (HE'nd : List.NoDup (map fst E')) by exact (NoDup_fst_perm _ _ PDperm HEnd).
assert (HcntE' : elen E' = cnt) by (rewrite HlenE'; exact C1d).
pose proof (proj1 HJ) as HH.
destruct (cl_heap_facts Lc Ac memc mdc tns m HH HB) as (Pp & Pf & Ppf & Pn & Psn & _).
destruct (Pn q ltac:(lia)) as (A0 & A1 & A16 & Anp & Anf). fold tn a in A0, A1, A16, Anp, Anf.
assert (Hain : In (a, NODE_SIZE) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HB | right; apply node_block_in; lia]).
assert (Hcnt10000 : cnt <= 10000) by (clear -Hcnt; unfold RGB_NMAX in Hcnt; lia).
pose proof Twf as (Wcut & Wcidx & Wii & Wimax & Wlen & Wmean).
pose proof OBJq as OBJx. rewrite (node_vals_expand c0 c1 tn 1 Wlen) in OBJx.
assert (FLD : forall j f v, nth_error LAY_Node j = Some f -> nth_error [c0; c1; nth 0 (tn_mean tn) 0; nth 1 (tn_mean tn) 0; nth 2 (tn_mean tn) 0; tn_imin tn; tn_imax tn; tn_cut tn; tn_cidx tn; 1] j = Some v ->
val_mem segs memc (a + fst f) (N.to_nat (snd f)) v) by (intros j f v Hf Hv; exact (proj1 (obj_at_nth segs memc a LAY_Node _ j f v OBJx Hf Hv))).
pose proof (FLD 8%nat (49, 1%N) (tn_cidx tn) eq_refl eq_refl) as Vcidx. pose proof (FLD 9%nat (50, 1%N) 1 eq_refl eq_refl) as Vleaf.
pose proof (FLD 5%nat (40, 4%N) (tn_imin tn) eq_refl eq_refl) as Vlo.
cbn [fst snd N.to_nat] in Vcidx, Vleaf, Vlo. rewrite Tcidx in Vcidx. rewrite Timin in Vlo. clear FLD OBJx.
eapply (S1_stretch API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc a i lo Lf (n_col nd) sp _ HJ
(fun blc j Hb Hj => NW q blc j ltac:(lia) Hb Hj) Hain ltac:(lia) ltac:(lia) Hal16 G2 G27 G26 Vlo G29
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Vcidx Vleaf Vnln).
intros regs1 mem1 HJ1 Vleaf1 Vnln1 FR1 Q1 Q10 Q11 Q12 Q13 Q14 Q15 K1.
assert (NPA : forall x, p <= x < p + 3 * T -> ~ (a <= x < a + NODE_SIZE)) by (pose proof Anp as X; unfold disj_blocks in X; intros; lia).
assert (NFA : forall x, fdp <= x < fdp + 4 * cnt -> ~ (a <= x < a + NODE_SIZE)) by (pose proof Anf as X; unfold disj_blocks in X; intros; lia).
assert (Hpa1 : arr8 segs mem1 p (pal_bytes E' ++ tail)).
{ eapply arr8_frame; [exact Hpa|]. intros x Hx. rewrite zlen_app_pal, HcntE' in Hx. pose proof (NPA x ltac:(lia)). apply FR1; lia. }
assert (Hfa1 : arr32 segs mem1 fdp (fr_vals E')).
{ eapply arr32_frame; [exact Hfa|]. intros x Hx. rewrite zlen_fr_vals, HcntE' in Hx. pose proof (NFA x ltac:(lia)). apply FR1; lia. }
eapply SR_bind.
{ apply (NTN fy RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mem1 mdc regs1 p fdp (sp + 934) lo (i - 1) (n_col nd) (Lf - 1) (pal_bytes E' ++ tail) (fr_vals E') HJ1 Hinit).
- rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. exact Hal16.
- rewrite (K1 4%bv ltac:(inl)), G4. exact Htp0.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- exact Hfrm.
- rewrite Q10. exact G25.
- rewrite Q11. exact G24.
- exact Q12.
- exact Q13.
- exact Q14.
- exact Q15.
- exact Hpa1.
- exact Hfa1.
- lia.
- lia.
- rewrite zlen_app_pal, HcntE'. lia.
- rewrite zlen_fr_vals, HcntE'. lia.
- lia.
- lia.
- rewrite zlen_app_pal, HcntE'. lia.
- lia.
- rewrite zlen_fr_vals, HcntE'. lia.
- pose proof (Z.div_mod fdp 16 ltac:(lia)) as Hdm. destruct Pf as (_ & _ & Pf16). rewrite Pf16 in Hdm. rewrite Hdm.
replace (16 * (fdp / 16) + 0) with ((4 * (fdp / 16)) * 4) by lia. apply Z.mod_mul. lia.
- exists p, (3 * T). split; [apply (blocks_of_CL Lc Ac tns m); [exact HB | left; apply SB_in_p] | rewrite zlen_app_pal, HcntE'; lia].
- exists fdp, (4 * cnt). split; [apply (blocks_of_CL Lc Ac tns m); [exact HB | left; apply SB_in_fdp] | rewrite zlen_fr_vals, HcntE'; lia].
- rewrite zlen_app_pal, zlen_fr_vals, HcntE'. pose proof Ppf as X. unfold disj_blocks in X. lia.
- intros i0 Hi0. rewrite getz_fr_vals by lia. apply (proj2 (ent_ok_at E' i0 HE'ok ltac:(lia))).
- rewrite (node_list_dseg (pal_bytes E' ++ tail) E' lo (i - 1) 0 (pal_agrees_app E' tail) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
pose proof (Kw 0) as (Kw1 & _). pose proof (zsum_fr_perm E0 E C1e). rewrite HNM in HNmax |- *. lia.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- lia.
- pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 934) with ((8 * (sp / 16) + 467) * 2) by lia. apply Z.mod_mul. lia.
- exact Vnln1.
- lia. }
cbv beta. intros c' (fx1 & Lc1 & Ac1 & regs2 & mem2 & md2 & res0 & -> & Hfrm2 & HJ2 & Hinit2 & HP2 & R10 & Hhi2 & Hkeep2 & Hres0).
rewrite Q1.
assert (Hsp1 : spZ regs1 = sp) by (unfold spZ; rewrite (K1 2%bv ltac:(inl)), G2; apply unsigned_lit_small; lia). rewrite Hsp1 in Hhi2.
assert (STK2 : forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp - NTN_STK <= x < sp) -> ~ (sp + 934 <= x < sp + 936) -> mbyte segs mem2 x = mbyte segs memc x).
{ intros x Hx Hn1 Hn2. rewrite (Hhi2 x Hx Hn1 ltac:(lia)). apply FR1; lia. }
assert (BLK2 : forall b n i0, In (b, n) (blocks Lc Ac) -> 0 <= i0 < n -> ~ (b + i0 = a + 50) -> mbyte segs mem2 (b + i0) = mbyte segs memc (b + i0)).
{ intros b n i0 Hb Hi0 Hne. rewrite (Hkeep2 b n i0 Hb Hi0).
destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n i0 HH Hb Hi0) as (_ & B0 & B1 & _). apply FR1; lia. }
assert (CRU : cr_unchanged memc mem2).
{ intros x [Hx | [Hx | (b & n0 & Hb & Hx)]].
- apply STK2; lia.
- apply STK2; lia.
- pose proof (SBs_in_SB _ Hb) as Hb'. assert (Hbb : In (b, n0) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HB | left; exact Hb']).
pose proof (Psn b n0 q Hb' ltac:(lia)) as S1. fold tn a in S1.
replace x with (b + (x - b)) by lia. apply (BLK2 b n0 (x - b) Hbb ltac:(lia)). lia. }
assert (RINV2 : RINV Lc1 Ac1 mem2 md2).
{ apply (rgba_inv_kept Lc Ac memc mdc Lc1 Ac1 mem2 md2 HINV HJ2 Hinit2). intros x Hx. apply STK2; lia. }
assert (STAT2 : cr_statics mem2) by exact (statics_kept memc mem2 STAT CRU).
assert (Hpin : In (p, 3 * T) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HB | left; apply SB_in_p]).
assert (Hfin : In (fdp, 4 * cnt) (blocks Lc Ac)) by (apply (blocks_of_CL Lc Ac tns m); [exact HB | left; apply SB_in_fdp]).
assert (Hpa2 : arr8 segs mem2 p (pal_bytes E' ++ tail)).
{ eapply arr8_frame; [exact Hpa1|]. intros x Hx. rewrite zlen_app_pal, HcntE' in Hx. replace x with (p + (x - p)) by lia. apply (Hkeep2 p (3 * T)); [exact Hpin | lia]. }
assert (Hfa2 : arr32 segs mem2 fdp (fr_vals E')).
{ eapply arr32_frame; [exact Hfa1|]. intros x Hx. rewrite zlen_fr_vals, HcntE' in Hx. replace x with (fdp + (x - fdp)) by lia. apply (Hkeep2 fdp (4 * cnt)); [exact Hfin | lia]. }
assert (OBJ1 : obj_at segs mem1 a LAY_Node (node_vals c0 c1 tn 0)).
{ rewrite (node_vals_expand c0 c1 tn 0 Wlen). rewrite (node_vals_expand c0 c1 tn 1 Wlen) in OBJq.
eapply (obj_at_upd segs memc mem1 a LAY_Node NODE_SIZE _ _ [9%nat] [(50, 51)] OBJq (proj1 lay_inside_Node) eq_refl); [reflexivity | | |].
- intros i0 Hi0 Hw. apply in_wins1_false in Hw. apply FR1; lia.
- intros j f v' Hj Hf Hv'. destruct Hj as [<-|[]]. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-. split; [exact Vleaf1 | cbn; lia].
- intros j Hj. do 9 (destruct j as [|j]; [reflexivity|]). destruct j as [|j]; [exfalso; apply Hj; left; reflexivity | reflexivity]. }
assert (OBJ2 : obj_at segs mem2 a LAY_Node (node_vals c0 c1 tn 0)).
{ eapply obj_at_transport_range; [exact OBJ1 | apply (proj1 lay_inside_Node) |]. intros i0 Hi0. apply (Hkeep2 a NODE_SIZE); [exact Hain | exact Hi0]. }
assert (NB2 : cl_nodes_but mem2 ns tns q).
{ split; [exact Hlen|]. split.
{ intros j Hj Hne. apply (node_mem_kept memc mem2 ns tns j (proj1 (NM j Hj))). intros i0 Hi0.
pose proof (nodes_disjoint Lc Ac memc mdc tns m j q HH HB Hj ltac:(lia) Hne) as ND. fold tn a in ND.
apply (BLK2 _ NODE_SIZE i0); [apply (blocks_of_CL Lc Ac tns m); [exact HB | right; apply node_block_in; lia] | lia | lia]. }
split; [intros j Hj; exact (proj2 (NM j Hj))|]. split; [| split; [exact NW | exact MOK]].
intros j Hj. eapply word_mem_frame; [exact (NL j Hj)|]. intros i0 Hi0. apply STK2; lia. }
assert (HB2 : forall bl', Permutation bl' (kblocks ([] : list tnode)) \/ True -> True) by (intros; exact I). clear HB2.
assert (REGS : forall rr : reg, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP2) by (revert Hrr; clear; intros Hrr; cbv [In] in Hrr; cbv [CALLEE_SAVED In]; intuition congruence).
apply K1. apply in_bv5'. revert Hrr. clear. intros Hrr. cbv [In] in Hrr. intuition (subst; vm_compute; reflexivity). }
assert (CB2 : cl_base regs2 q) by exact (cl_base_upd regs regs2 _ q q REGS ltac:(vm_compute; reflexivity) ltac:(rewrite (REGS 9%bv ltac:(inl)); exact G9) CB).
assert (SL2 : cl_slots mem2 (tn_addr (tnth tns 0))) by exact (cl_slots_kept memc mem2 _ SLOTS CRU).
destruct Hres0 as [(Hr0 & Hbl & Vn) | (Hr0 & Hr16 & (b1 & b2 & Hbl1 & Hbl2) & Hwb0 & Vn & nd0 & Ha0 & Hi0 & Hx0 & Hc0 & Htree0 & Hwf0 & Hq0 & Hdim0)].
-
apply (HK fx1 regs2 Lc1 Ac1 mem2 md2 [] res0). unfold at_S23. cbn [c_E c_ns c_q]. fold m nd tn lo hi Lf. fold a.
split; [exact RINV2|]. split; [exact Hfrm2|]. split; [exact CINV|]. split; [exact HLf|]. split; [exact Hq|]. split; [exact Hlohi|].
split; [exists P; exact PD|].
split; [exact CB2|].
split; [rewrite (REGS 27%bv ltac:(inl)); exact G27|]. split; [rewrite (REGS 26%bv ltac:(inl)); exact G26|]. split; [exact R10|].
split; [exact STAT2|]. split; [exact SL2|]. split; [exact Hpa2|]. split; [exact Hfa2|].
split; [cbn [elen length Z.of_nat]; rewrite !Z.add_0_r; exact Vn|].
split; [exists c0, c1; exact OBJ2|]. split; [exact NB2|].
split; [intros j Hj; apply FACTS; lia|]. split; [exact Hr0|]. split; [reflexivity|].
cbn [kblocks map app]. rewrite app_nil_r, Hbl. exact HB.
-
apply (HK fx1 regs2 Lc1 Ac1 mem2 md2 [nd0] res0). unfold at_S23. cbn [c_E c_ns c_q]. fold m nd tn lo hi Lf. fold a.
split; [exact RINV2|]. split; [exact Hfrm2|]. split; [exact CINV|]. split; [exact HLf|]. split; [exact Hq|]. split; [exact Hlohi|].
split; [exists P; exact PD|].
split; [exact CB2|].
split; [rewrite (REGS 27%bv ltac:(inl)); exact G27|]. split; [rewrite (REGS 26%bv ltac:(inl)); exact G26|]. split; [exact R10|].
split; [exact STAT2|]. split; [exact SL2|]. split; [exact Hpa2|]. split; [exact Hfa2|].
split; [cbn [elen length Z.of_nat Pos.of_succ_nat]; rewrite Z.add_0_r; exact Vn|].
split; [exists c0, c1; exact OBJ2|]. split; [exact NB2|].
split; [intros j Hj; apply FACTS; lia|].
split. { cbn [kid_ok]. destruct Htree0 as (Tnz0 & Tlen0 & Tobj).
split; [symmetry; exact Ha0|]. split; [exact Tnz0|]. split; [exact Hi0|]. split; [exact Hx0|]. split; [exact Hc0|]. split; [exact Hwf0|].
split; [exact Tobj|]. split.
- apply (tn_facts_intro (pal_bytes E' ++ tail) E' lo (i - 1) nd0 (mkN lo (i - 1) true (n_col nd) None None 0 0 (zsub E' lo (i - 1)))
(pal_agrees_app E' tail) HE'ok HE'nd ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl eq_refl (proj1 Hwf0) Hq0 Hdim0).
- intros blc j Hb Hj. rewrite Ha0. apply Hwb0; [rewrite <- Ha0; exact Hb | exact Hj]. }
split; [reflexivity|].
cbn [kblocks map app]. rewrite Hbl1. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
rewrite Ha0. eapply Permutation_trans; [apply perm_skip; rewrite <- Hbl2; exact HB|]. rewrite app_assoc. apply Permutation_cons_append.
Qed.
Theorem S2_to_S3 : forall fy regs Lc Ac memc mdc st tns E' i k0 res0 Q,
at_S23 false fy regs Lc Ac memc mdc st tns E' i k0 [] res0 0 ->
(forall fy' regs' Lc' Ac' memc' mdc' k1 res1, at_S23 true fy' regs' Lc' Ac' memc' mdc' st tns E' i k0 k1 res0 res1 ->
SR segs (mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_S3) memc' rom) mdc') Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S2) memc rom) mdc) Q.
Proof.
intros fy regs Lc Ac memc mdc [E ns q] tns E' i k0 res0 Q HAT HK.
unfold at_S23 in HAT. cbn [c_E c_ns c_q] in HAT.
destruct HAT as (HINV & Hfrm & CINV & HLf & Hq & Hlohi & (P & PD) & CB & G27 & G26 & G10 &
STAT & SLOTS & Hpa & Hfa & Vnln & (c0 & c1 & OBJq) & NB & FACTS & KID0 & _ & HB).
pose proof CB as ((G2 & G3 & G4) & G9 & G22 & G23 & G18 & G19 & G8 & G20 & G25 & G24 & G21).
rewrite app_nil_r in HB. rewrite Z.add_0_r in Vnln.
pose proof cr_consts as (HRS & HFR & HNT & HNS & HNM & Hac & HlenE0 & Htl & HT3).
destruct (sp_facts Lc Ac memc mdc HINV) as (Hsp & Hal0 & Hal16 & Hceil & H63 & Hstw). rewrite HRS in Hceil, Hstw.
pose proof HINV as (HJ & Hinit & _ & Hra0 & _ & Htp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _).
destruct NB as (Hlen & NM & TM & NL & NW & MOK).
set (m := elen ns) in *. set (Lf := nleaves ns) in *. set (nd := node ns q) in *. set (tn := tnth tns q) in *.
set (a := tn_addr tn) in *. set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
destruct HE0 as (HE0ok & HE0nd & HE0sum).
pose proof (cinv_counts cnt E0 _ CINV) as (C1a & C1b & C1c & C1d & C1e). cbn [c_E c_ns c_q] in C1a, C1b, C1c, C1d, C1e. fold m Lf in C1a, C1b, C1c.
pose proof (cinv_node cnt E0 _ CINV q ltac:(cbn; lia)) as CN. cbn [c_ns] in CN. fold nd in CN. cbv zeta in CN. fold lo hi in CN.
destruct CN as (CN1 & CN2 & CN3 & CN4 & CN5). fold Lf in CN4, CN5.
pose proof (TM q ltac:(lia)) as TMq. fold nd tn in TMq. pose proof TMq as (Timin & Timax & Tcidx & Twf & Tnz). fold lo in Timin. fold hi in Timax.
pose proof Twf as (Wcut & Wcidx & Wii & Wimax & Wlen & Wmean).
assert (HEok : ent_ok E /\ List.NoDup (map fst E)) by (split; [exact (ent_ok_perm _ _ C1e HE0ok) | exact (NoDup_fst_perm _ _ C1e HE0nd)]).
destruct HEok as [HEok HEnd].
destruct (kids_segments P lo hi E E' i PD ltac:(lia) ltac:(rewrite C1d; lia) HEok) as (HlenE' & HE'ok & Ki1 & Ki2 & Ki3 & Ki4 & Kw).
pose proof PD as (PDi & PDlen & PDperm & _).
assert (HE'nd : List.NoDup (map fst E')) by exact (NoDup_fst_perm _ _ PDperm HEnd).
assert (HcntE' : elen E' = cnt) by (rewrite HlenE'; exact C1d).
assert (Hcnt10000 : cnt <= 10000) by (clear -Hcnt; unfold RGB_NMAX in Hcnt; lia).
assert (Hk0 : 0 <= elen k0 <= 1) by (destruct k0 as [|? [|? ?]]; [change (elen []) with 0; lia | change (elen [_]) with 1; lia | cbn in KID0; destruct KID0]).
pose proof (proj1 HJ) as HH.
assert (HB' : Permutation (blocks Lc Ac) (SB ++ node_blocks (tns ++ k0) (m + elen k0))) by (rewrite (node_blocks_app tns k0 m Hlen ltac:(lia)); exact HB).
destruct (cl_heap_facts Lc Ac memc mdc (tns ++ k0) (m + elen k0) HH HB') as (Pp & Pf & Ppf & Pn & Psn & _).
destruct (Pn q ltac:(lia)) as (A0 & A1 & A16 & Anp & Anf). rewrite (tnth_app_l tns k0 q) in A0, A1, A16, Anp, Anf by lia. fold tn a in A0, A1, A16, Anp, Anf.
assert (Hain : In (a, NODE_SIZE) (blocks Lc Ac)).
{ apply (blocks_of_perm Lc Ac _ _ HB). right. apply in_app_iff. left. apply node_block_in. lia. }
assert (NPA : forall x, p <= x < p + 3 * T -> ~ (a <= x < a + NODE_SIZE)) by (pose proof Anp as X; unfold disj_blocks in X; intros; lia).
assert (NFA : forall x, fdp <= x < fdp + 4 * cnt -> ~ (a <= x < a + NODE_SIZE)) by (pose proof Anf as X; unfold disj_blocks in X; intros; lia).
pose proof OBJq as OBJx. rewrite (node_vals_expand c0 c1 tn 0 Wlen) in OBJx.
pose proof (proj1 (obj_at_nth segs memc a LAY_Node _ 6%nat (44, 4%N) (tn_imax tn) OBJx eq_refl eq_refl)) as Vimax. cbn [fst snd N.to_nat] in Vimax.
rewrite Timax in Vimax. clear OBJx.
assert (Hres0rng : 0 <= res0 < 2 ^ 64).
{ destruct k0 as [|t [|]]; cbn [kid_ok] in KID0; [subst res0; lia | destruct KID0 as (Er & _) | destruct KID0].
destruct (Pn m ltac:(change (elen [t]) with 1; lia)) as (B0 & B1 & _). rewrite <- Hlen in B0, B1. rewrite (tnth_app_new0 tns t []) in B0, B1.
rewrite Er. clear -B0 B1 Hac HNS. lia. }
eapply (S2_stretch API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc a i hi (Lf - 1 + elen k0) res0 sp _ HJ
(fun blc j Hb Hj => NW q blc j ltac:(lia) Hb Hj) Hain ltac:(lia) ltac:(lia) Hal16 G2 G27 G26 G10
ltac:(lia) ltac:(lia) ltac:(lia) Hres0rng Vimax Vnln).
intros regs1 mem1 HJ1 Vc01 FR1 Q1 Q10 Q11 Q12 Q13 Q14 Q15 K1.
assert (Hpa1 : arr8 segs mem1 p (pal_bytes E' ++ tail)).
{ eapply arr8_frame; [exact Hpa|]. intros x Hx. rewrite zlen_app_pal, HcntE' in Hx. pose proof (NPA x ltac:(lia)). apply FR1; lia. }
assert (Hfa1 : arr32 segs mem1 fdp (fr_vals E')).
{ eapply arr32_frame; [exact Hfa|]. intros x Hx. rewrite zlen_fr_vals, HcntE' in Hx. pose proof (NFA x ltac:(lia)). apply FR1; lia. }
assert (Hpin : In (p, 3 * T) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB); left; apply SB_in_p).
assert (Hfin : In (fdp, 4 * cnt) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB); left; apply SB_in_fdp).
assert (Vnln1 : val_mem segs mem1 (sp + 934) 2 (Lf - 1 + elen k0)).
{ eapply val_mem_frame; [exact Vnln|]. intros i0 Hi0. apply FR1; lia. }
eapply SR_bind.
{ apply (NTN fy RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mem1 mdc regs1 p fdp (sp + 934) i hi (Lf - 1 + elen k0) (Lf - 1 + elen k0) (pal_bytes E' ++ tail) (fr_vals E') HJ1 Hinit).
- rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. exact Hal16.
- rewrite (K1 4%bv ltac:(inl)), G4. exact Htp0.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- exact Hfrm.
- rewrite Q10. exact G25.
- rewrite Q11. exact G24.
- exact Q12.
- exact Q13.
- exact Q14.
- exact Q15.
- exact Hpa1.
- exact Hfa1.
- lia.
- lia.
- rewrite zlen_app_pal, HcntE'. lia.
- rewrite zlen_fr_vals, HcntE'. lia.
- lia.
- lia.
- rewrite zlen_app_pal, HcntE'. lia.
- lia.
- rewrite zlen_fr_vals, HcntE'. lia.
- pose proof (Z.div_mod fdp 16 ltac:(lia)) as Hdm. destruct Pf as (_ & _ & Pf16). rewrite Pf16 in Hdm. rewrite Hdm.
replace (16 * (fdp / 16) + 0) with ((4 * (fdp / 16)) * 4) by lia. apply Z.mod_mul. lia.
- exists p, (3 * T). split; [exact Hpin | rewrite zlen_app_pal, HcntE'; lia].
- exists fdp, (4 * cnt). split; [exact Hfin | rewrite zlen_fr_vals, HcntE'; lia].
- rewrite zlen_app_pal, zlen_fr_vals, HcntE'. pose proof Ppf as X. unfold disj_blocks in X. lia.
- intros i0 Hi0. rewrite getz_fr_vals by lia. apply (proj2 (ent_ok_at E' i0 HE'ok ltac:(lia))).
- rewrite (node_list_dseg (pal_bytes E' ++ tail) E' i hi 0 (pal_agrees_app E' tail) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
pose proof (Kw 0) as (_ & Kw2 & _). pose proof (zsum_fr_perm E0 E C1e). rewrite HNM in HNmax |- *. lia.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- lia.
- pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 934) with ((8 * (sp / 16) + 467) * 2) by lia. apply Z.mod_mul. lia.
- exact Vnln1.
- lia. }
cbv beta. intros c' (fx1 & Lc1 & Ac1 & regs2 & mem2 & md2 & res1 & -> & Hfrm2 & HJ2 & Hinit2 & HP2 & R10 & Hhi2 & Hkeep2 & Hres1).
rewrite Q1.
assert (Hsp1 : spZ regs1 = sp) by (unfold spZ; rewrite (K1 2%bv ltac:(inl)), G2; apply unsigned_lit_small; lia). rewrite Hsp1 in Hhi2.
assert (STK2 : forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp - NTN_STK <= x < sp) -> ~ (sp + 934 <= x < sp + 936) -> mbyte segs mem2 x = mbyte segs memc x).
{ intros x Hx Hn1 Hn2. rewrite (Hhi2 x Hx Hn1 ltac:(lia)). apply FR1; lia. }
assert (BLK2 : forall b n i0, In (b, n) (blocks Lc Ac) -> 0 <= i0 < n -> ~ (a <= b + i0 < a + 8) -> mbyte segs mem2 (b + i0) = mbyte segs memc (b + i0)).
{ intros b n i0 Hb Hi0 Hne. rewrite (Hkeep2 b n i0 Hb Hi0).
destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n i0 HH Hb Hi0) as (_ & B0 & B1 & _). apply FR1; lia. }
assert (CRU : cr_unchanged memc mem2).
{ intros x [Hx | [Hx | (b & n0 & Hb & Hx)]].
- apply STK2; lia.
- apply STK2; lia.
- pose proof (SBs_in_SB _ Hb) as Hb'. assert (Hbb : In (b, n0) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB); left; exact Hb').
pose proof (Psn b n0 q Hb' ltac:(lia)) as S1. rewrite (tnth_app_l tns k0 q) in S1 by lia. fold tn a in S1.
replace x with (b + (x - b)) by lia. apply (BLK2 b n0 (x - b) Hbb ltac:(lia)). lia. }
assert (RINV2 : RINV Lc1 Ac1 mem2 md2).
{ apply (rgba_inv_kept Lc Ac memc mdc Lc1 Ac1 mem2 md2 HINV HJ2 Hinit2). intros x Hx. apply STK2; lia. }
assert (STAT2 : cr_statics mem2) by exact (statics_kept memc mem2 STAT CRU).
assert (Hpa2 : arr8 segs mem2 p (pal_bytes E' ++ tail)).
{ eapply arr8_frame; [exact Hpa1|]. intros x Hx. rewrite zlen_app_pal, HcntE' in Hx. replace x with (p + (x - p)) by lia. apply (Hkeep2 p (3 * T)); [exact Hpin | lia]. }
assert (Hfa2 : arr32 segs mem2 fdp (fr_vals E')).
{ eapply arr32_frame; [exact Hfa1|]. intros x Hx. rewrite zlen_fr_vals, HcntE' in Hx. replace x with (fdp + (x - fdp)) by lia. apply (Hkeep2 fdp (4 * cnt)); [exact Hfin | lia]. }
assert (OBJ1 : obj_at segs mem1 a LAY_Node (node_vals res0 c1 tn 0)).
{ rewrite (node_vals_expand res0 c1 tn 0 Wlen). rewrite (node_vals_expand c0 c1 tn 0 Wlen) in OBJq.
eapply (obj_at_upd segs memc mem1 a LAY_Node NODE_SIZE _ _ [0%nat] [(0, 8)] OBJq (proj1 lay_inside_Node) eq_refl); [reflexivity | | |].
- intros i0 Hi0 Hw. apply in_wins1_false in Hw. apply FR1; lia.
- intros j f v' Hj Hf Hv'. destruct Hj as [<-|[]]. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-. split; [rewrite Z.add_0_r; exact Vc01 | cbn; lia].
- intros j Hj. destruct j as [|j]; [exfalso; apply Hj; left; reflexivity | reflexivity]. }
assert (OBJ2 : obj_at segs mem2 a LAY_Node (node_vals res0 c1 tn 0)).
{ eapply obj_at_transport_range; [exact OBJ1 | apply (proj1 lay_inside_Node) |]. intros i0 Hi0. apply (Hkeep2 a NODE_SIZE); [exact Hain | exact Hi0]. }
assert (NB2 : cl_nodes_but mem2 ns tns q).
{ split; [exact Hlen|]. split.
{ intros j Hj Hne. apply (node_mem_kept memc mem2 ns tns j (NM j Hj Hne)). intros i0 Hi0.
pose proof (nodes_disjoint Lc Ac memc mdc (tns ++ k0) (m + elen k0) j q HH HB' ltac:(lia) ltac:(lia) Hne) as ND.
rewrite (tnth_app_l tns k0 q), (tnth_app_l tns k0 j) in ND by lia. fold tn a in ND.
apply (BLK2 _ NODE_SIZE i0); [apply (blocks_of_perm Lc Ac _ _ HB); right; apply in_app_iff; left; apply node_block_in; lia | lia | lia]. }
split; [exact TM|]. split; [| split; [exact NW | exact MOK]].
intros j Hj. eapply word_mem_frame; [exact (NL j Hj)|]. intros i0 Hi0. apply STK2; lia. }
assert (KID0' : kid_ok mem2 k0 res0 lo (i - 1) (n_col nd) (zsub E' lo (i - 1))).
{ destruct k0 as [|t [|]]; cbn [kid_ok] in KID0 |- *; [exact KID0 | | destruct KID0].
destruct KID0 as (Er & Tnz0 & Ti & Tx & Tc & Twf0 & (d0 & d1 & Tobj) & Tf & Twb).
refine (conj Er (conj Tnz0 (conj Ti (conj Tx (conj Tc (conj Twf0 (conj _ (conj Tf Twb)))))))).
exists d0, d1. eapply obj_at_transport_range; [exact Tobj | apply (proj1 lay_inside_Node) |]. intros i0 Hi0.
pose proof (nodes_disjoint Lc Ac memc mdc (tns ++ [t]) (m + 1) m q HH HB' ltac:(lia) ltac:(lia) ltac:(lia)) as ND.
rewrite (tnth_app_l tns [t] q) in ND by lia. rewrite <- Hlen in ND. rewrite (tnth_app_new0 tns t []) in ND. fold tn a in ND.
apply (BLK2 _ NODE_SIZE i0); [| lia | lia].
apply (blocks_of_perm Lc Ac _ _ HB). right. apply in_app_iff. right. left. reflexivity. }
assert (REGS : forall rr : reg, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP2) by (revert Hrr; clear; intros Hrr; cbv [In] in Hrr; cbv [CALLEE_SAVED In]; intuition congruence).
apply K1. apply in_bv5'. revert Hrr. clear. intros Hrr. cbv [In] in Hrr. intuition (subst; vm_compute; reflexivity). }
assert (COMMON : forall k1,
kid_ok mem2 k1 res1 i hi (Lf - 1 + elen k0) (zsub E' i hi) ->
val_mem segs mem2 (sp + 934) 2 (Lf - 1 + elen k0 + elen k1) ->
Permutation (blocks Lc1 Ac1) (SB ++ node_blocks tns m ++ kblocks (k0 ++ k1)) ->
at_S23 true fx1 regs2 Lc1 Ac1 mem2 md2 {| c_E := E; c_ns := ns; c_q := q |} tns E' i k0 k1 res0 res1).
{ intros k1 K1ok Vn HBn. unfold at_S23. cbn [c_E c_ns c_q]. fold m nd tn lo hi Lf. fold a.
split; [exact RINV2|]. split; [exact Hfrm2|]. split; [exact CINV|]. split; [exact HLf|]. split; [exact Hq|]. split; [exact Hlohi|].
split; [exists P; exact PD|].
split; [exact (cl_base_upd regs regs2 _ q q REGS ltac:(vm_compute; reflexivity) ltac:(rewrite (REGS 9%bv ltac:(inl)); exact G9) CB)|].
split; [rewrite (REGS 27%bv ltac:(inl)); exact G27|]. split; [rewrite (REGS 26%bv ltac:(inl)); exact G26|]. split; [exact R10|].
split; [exact STAT2|]. split; [exact (cl_slots_kept memc mem2 _ SLOTS CRU)|]. split; [exact Hpa2|]. split; [exact Hfa2|]. split; [exact Vn|].
split; [exists c0, c1; exact OBJ2|]. split; [exact NB2|]. split; [exact FACTS|]. split; [exact KID0'|]. split; [exact K1ok | exact HBn]. }
destruct Hres1 as [(Hr1 & Hbl & Vn) | (Hr1 & Hr16 & (b1 & b2 & Hbl1 & Hbl2) & Hwb1 & Vn & nd1 & Ha1 & Hi1 & Hx1 & Hc1 & Htree1 & Hwf1 & Hq1 & Hdim1)].
-
apply (HK fx1 regs2 Lc1 Ac1 mem2 md2 [] res1). apply COMMON.
+ exact Hr1.
+ change (elen []) with 0. rewrite Z.add_0_r. exact Vn.
+ rewrite app_nil_r, Hbl. exact HB.
-
apply (HK fx1 regs2 Lc1 Ac1 mem2 md2 [nd1] res1). apply COMMON.
+ cbn [kid_ok]. destruct Htree1 as (Tnz1 & Tlen1 & Tobj1).
split; [symmetry; exact Ha1|]. split; [exact Tnz1|]. split; [exact Hi1|]. split; [exact Hx1|]. split; [exact Hc1|]. split; [exact Hwf1|].
split; [exact Tobj1|]. split.
* apply (tn_facts_intro (pal_bytes E' ++ tail) E' i hi nd1 (mkN i hi true (Lf - 1 + elen k0) None None 0 0 (zsub E' i hi))
(pal_agrees_app E' tail) HE'ok HE'nd ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl eq_refl (proj1 Hwf1) Hq1 Hdim1).
* intros blc j Hb Hj. rewrite Ha1. apply Hwb1; [rewrite <- Ha1; exact Hb | exact Hj].
+ change (elen [nd1]) with 1. exact Vn.
+ unfold kblocks. rewrite map_app. cbn [map]. rewrite Hbl1. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
rewrite Ha1. eapply Permutation_trans; [apply perm_skip; rewrite <- Hbl2; exact HB|].
change (kblocks k0) with (map (fun t : tnode => (tn_addr t, NODE_SIZE)) k0). rewrite !app_assoc. apply Permutation_cons_append.
Qed.
Theorem S3_finish : forall fy regs Lc Ac memc mdc st tns E' i k0 k1 res0 res1,
at_S23 true fy regs Lc Ac memc mdc st tns E' i k0 k1 res0 res1 ->
K_CLn (c_q st + 1) -> K_DONE -> K_FAIL ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros fy regs Lc Ac memc mdc [E ns q] tns E' i k0 k1 res0 res1 HAT KCL KDONE KFAIL.
unfold at_S23 in HAT. cbn [c_E c_ns c_q] in HAT, KCL.
destruct HAT as (HINV & Hfrm & CINV & HLf & Hq & Hlohi & (P & PD) & CB & G27 & G26 & G10 &
STAT & SLOTS & Hpa & Hfa & Vnln & (c0 & c1 & OBJq) & NB & FACTS & KID0 & KID1 & HB).
pose proof CB as ((G2 & G3 & G4) & G9 & G22 & G23 & G18 & G19 & G8 & G20 & G25 & G24 & G21).
pose proof cr_consts as (HRS & HFR & HNT & HNS & HNM & Hac & HlenE0 & Htl & HT3).
destruct (sp_facts Lc Ac memc mdc HINV) as (Hsp & Hal0 & Hal16 & Hceil & H63 & Hstw). rewrite HRS in Hceil, Hstw.
pose proof HINV as (HJ & Hinit & _ & Hra0 & _ & Htp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _).
destruct NB as (Hlen & NM & TM & NL & NW & MOK).
set (m := elen ns) in *. set (Lf := nleaves ns) in *. set (nd := node ns q) in *. set (tn := tnth tns q) in *.
set (a := tn_addr tn) in *. set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
destruct HE0 as (HE0ok & HE0nd & HE0sum).
pose proof (cinv_counts cnt E0 _ CINV) as (C1a & C1b & C1c & C1d & C1e). cbn [c_E c_ns c_q] in C1a, C1b, C1c, C1d, C1e. fold m Lf in C1a, C1b, C1c.
pose proof (cinv_node cnt E0 _ CINV q ltac:(cbn; lia)) as CN. cbn [c_ns] in CN. fold nd in CN. cbv zeta in CN. fold lo hi in CN.
destruct CN as (CN1 & CN2 & CN3 & CN4 & CN5). fold Lf in CN4, CN5.
pose proof (TM q ltac:(lia)) as TMq. fold nd tn in TMq. pose proof TMq as (Timin & Timax & Tcidx & Twf & Tnz). fold lo in Timin. fold hi in Timax. fold a in Tnz.
pose proof Twf as (Wcut & Wcidx & Wii & Wimax & Wlen & Wmean).
pose proof PD as (PDi & PDlen & PDperm & _).
assert (HcntE' : elen E' = cnt) by (unfold elen in *; rewrite PDlen; exact C1d).
assert (Hk0 : 0 <= elen k0 <= 1) by (destruct k0 as [|? [|? ?]]; [change (elen []) with 0; lia | change (elen [_]) with 1; lia | cbn in KID0; destruct KID0]).
assert (Hk1 : 0 <= elen k1 <= 1) by (destruct k1 as [|? [|? ?]]; [change (elen []) with 0; lia | change (elen [_]) with 1; lia | cbn in KID1; destruct KID1]).
pose proof (proj1 HJ) as HH.
assert (HB' : Permutation (blocks Lc Ac) (SB ++ node_blocks (tns ++ (k0 ++ k1)) (m + elen (k0 ++ k1)))) by (rewrite (node_blocks_app tns (k0 ++ k1) m Hlen ltac:(lia)); exact HB).
assert (Hk01 : elen (k0 ++ k1) = elen k0 + elen k1) by (unfold elen; rewrite length_app; lia).
destruct (cl_heap_facts Lc Ac memc mdc (tns ++ (k0 ++ k1)) (m + elen (k0 ++ k1)) HH HB') as (Pp & Pf & Ppf & Pn & Psn & _).
destruct (Pn q ltac:(lia)) as (A0 & A1 & A16 & Anp & Anf). rewrite (tnth_app_l tns (k0 ++ k1) q) in A0, A1, A16, Anp, Anf by lia. fold tn a in A0, A1, A16, Anp, Anf.
assert (Hain : In (a, NODE_SIZE) (blocks Lc Ac)).
{ apply (blocks_of_perm Lc Ac _ _ HB). right. apply in_app_iff. left. apply node_block_in. lia. }
pose proof OBJq as OBJx. rewrite (node_vals_expand res0 c1 tn 0 Wlen) in OBJx.
pose proof (proj1 (obj_at_nth segs memc a LAY_Node _ 0%nat (0, 8%N) res0 OBJx eq_refl eq_refl)) as Vc0. cbn [fst snd N.to_nat] in Vc0. rewrite Z.add_0_r in Vc0.
clear OBJx.
assert (POST : forall (memF : word -> option byte) resv,
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> ~ (sp + 936 + 8 * m <= x < sp + 936 + 8 * m + 16) -> mbyte segs memF x = mbyte segs memc x) ->
val_mem segs memF (a + 8) 8 resv -> 0 <= resv < 2 ^ 64 ->
cr_statics memF /\ cl_slots memF (tn_addr (tnth tns 0)) /\ arr8 segs memF p (pal_bytes E' ++ tail) /\ arr32 segs memF fdp (fr_vals E') /\
obj_at segs memF a LAY_Node (node_vals res0 resv tn 0) /\
(forall j, 0 <= j < m -> j <> q -> node_mem segs memF ns tns j) /\
(forall j, 0 <= j < m -> word_mem segs memF (sp + 936 + 8 * j) (tn_addr (tnth tns j))) /\
kid_ok memF k0 res0 lo (i - 1) (n_col nd) (zsub E' lo (i - 1)) /\
kid_ok memF k1 res1 i hi (Lf - 1 + elen k0) (zsub E' i hi)).
{ intros memF resv FR Vres Hres.
assert (NPA : forall x, p <= x < p + 3 * T -> ~ (a <= x < a + NODE_SIZE)) by (pose proof Anp as X; unfold disj_blocks in X; intros; lia).
assert (NFA : forall x, fdp <= x < fdp + 4 * cnt -> ~ (a <= x < a + NODE_SIZE)) by (pose proof Anf as X; unfold disj_blocks in X; intros; lia).
assert (CRUF : cr_unchanged memc memF).
{ apply (cr_unchanged_intro Lc Ac memc mdc (tns ++ (k0 ++ k1)) (m + elen (k0 ++ k1)) memF HH HB' ltac:(lia) H63).
intros x Hx N1 N2 N3 N4 N5. pose proof (N5 q ltac:(lia)) as N6. rewrite (tnth_app_l tns (k0 ++ k1) q) in N6 by lia. fold tn a in N6. apply FR; lia. }
split; [exact (statics_kept memc memF STAT CRUF)|]. split; [exact (cl_slots_kept memc memF _ SLOTS CRUF)|].
split. { eapply arr8_frame; [exact Hpa|]. intros x Hx. rewrite zlen_app_pal, HcntE' in Hx. pose proof (NPA x ltac:(lia)). apply FR; lia. }
split. { eapply arr32_frame; [exact Hfa|]. intros x Hx. rewrite zlen_fr_vals, HcntE' in Hx. pose proof (NFA x ltac:(lia)). apply FR; lia. }
split. { rewrite (node_vals_expand res0 resv tn 0 Wlen). rewrite (node_vals_expand res0 c1 tn 0 Wlen) in OBJq.
eapply (obj_at_upd segs memc memF a LAY_Node NODE_SIZE _ _ [1%nat] [(8, 16)] OBJq (proj1 lay_inside_Node) eq_refl); [reflexivity | | |].
- intros i0 Hi0 Hw. apply in_wins1_false in Hw. apply FR; lia.
- intros j f v' Hj Hf Hv'. destruct Hj as [<-|[]]. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-. split; [exact Vres | cbn; lia].
- intros j Hj. destruct j as [|[|j]]; [reflexivity | exfalso; apply Hj; left; reflexivity | reflexivity]. }
split. { intros j Hj Hne. apply (node_mem_kept memc memF ns tns j (NM j Hj Hne)). intros i0 Hi0.
pose proof (nodes_disjoint Lc Ac memc mdc (tns ++ (k0 ++ k1)) (m + elen (k0 ++ k1)) j q HH HB' ltac:(lia) ltac:(lia) Hne) as ND.
rewrite (tnth_app_l tns (k0 ++ k1) q), (tnth_app_l tns (k0 ++ k1) j) in ND by lia. fold tn a in ND.
destruct (Pn j ltac:(lia)) as (B0 & B1 & _). rewrite (tnth_app_l tns (k0 ++ k1) j) in B0, B1 by lia. apply FR; lia. }
split. { intros j Hj. eapply word_mem_frame; [exact (NL j Hj)|]. intros i0 Hi0. apply FR; lia. }
assert (KID : forall k res lo' hi' cx seg jj, kid_ok memc k res lo' hi' cx seg -> (forall t, k = [t] -> tnth (tns ++ (k0 ++ k1)) jj = t /\ m <= jj < m + elen (k0 ++ k1)) ->
kid_ok memF k res lo' hi' cx seg).
{ intros k res lo' hi' cx seg jj K Hjj. destruct k as [|t [|]]; cbn [kid_ok] in K |- *; [exact K | | destruct K].
destruct K as (Er & Tnz0 & Ti & Tx & Tc & Twf0 & (d0 & d1 & Tobj) & Tf & Twb). destruct (Hjj t eq_refl) as [Htj Hjr].
refine (conj Er (conj Tnz0 (conj Ti (conj Tx (conj Tc (conj Twf0 (conj _ (conj Tf Twb)))))))).
exists d0, d1. eapply obj_at_transport_range; [exact Tobj | apply (proj1 lay_inside_Node) |]. intros i0 Hi0.
pose proof (nodes_disjoint Lc Ac memc mdc (tns ++ (k0 ++ k1)) (m + elen (k0 ++ k1)) jj q HH HB' ltac:(lia) ltac:(lia) ltac:(lia)) as ND.
rewrite (tnth_app_l tns (k0 ++ k1) q), Htj in ND by lia. fold tn a in ND.
destruct (Pn jj ltac:(lia)) as (B0 & B1 & _). rewrite Htj in B0, B1. apply FR; lia. }
split.
- apply (KID k0 res0 lo (i - 1) (n_col nd) _ m KID0). intros t ->. rewrite <- Hlen. split; [apply (tnth_app_new0 tns t k1) | rewrite Hlen; try change (elen ([t] ++ k1)) with (1 + elen k1)%nat; rewrite Hk01; change (elen [t]) with 1; lia].
- apply (KID k1 res1 i hi (Lf - 1 + elen k0) _ (m + elen k0) KID1). intros t ->. split.
+ destruct k0 as [|t0 [|]]; [| | cbn in KID0; destruct KID0].
* change (elen []) with 0. rewrite Z.add_0_r, <- Hlen. apply (tnth_app_new0 tns t []).
* change (elen [t0]) with 1. rewrite <- Hlen. apply (tnth_app_new1 tns t0 t []).
+ rewrite Hk01. change (elen [t]) with 1. lia. }
assert (OLDK : forall j, 0 <= j < m -> n_leaf (node ns j) = false -> forall c, (n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> 0 <= c < elen tns).
{ intros j Hj Hl c Hc. destruct (cinv_kids cnt E0 _ CINV j ltac:(cbn; lia) Hl) as (c' & K0 & K1 & R1 & R2). cbn [c_ns] in K0, K1, R2. fold m in R2.
rewrite K0, K1 in Hc. destruct Hc as [Hc|Hc]; injection Hc; lia. }
assert (HE0E' : Permutation E0 E') by (eapply Permutation_trans; [exact C1e | exact PDperm]).
assert (Hroot : tn_addr (tnth (tns ++ (k0 ++ k1)) 0) = tn_addr (tnth tns 0)) by (rewrite tnth_app_l by lia; reflexivity).
assert (FAILPACK : forall (fy' : FPState) regs' mem' (ok0 ok1 : bool),
ok0 = match k0 with [] => false | _ => true end -> ok1 = match k1 with [] => false | _ => true end ->
frm_zero (@fp_csr fy') -> journal ubs2_msyms MR RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mem' mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> mbyte segs mem' x = mbyte segs memc x) -> val_mem segs mem' (a + 8) 8 res1 -> 0 <= res1 < 2 ^ 64 ->
(exists q', cl_base regs' q') ->
at_FAIL fy' regs' Lc Ac mem' mdc (cfail_ns ns q i (Lf - 1 + elen k0) ok0 ok1) (tns ++ (k0 ++ k1)) (Lf + 1)).
{ intros fy' regs' mem' ok0 ok1 Hok0 Hok1 Hfrm' HJ' FR Vres Hres CB'.
destruct (POST mem' res1 ltac:(intros x Hx N1 N2; apply FR; [exact Hx | exact N1]) Vres Hres) as (STAT' & SL' & Hpa' & Hfa' & OBJ' & NM' & NL' & KID0' & KID1').
destruct (cfail_ok cnt E0 {| c_E := E; c_ns := ns; c_q := q |} i (Lf - 1 + elen k0) ok0 ok1 CINV ltac:(cbn; lia)) as (PO & TI & D0 & Hlen' & TOK).
cbn [c_ns c_q] in PO, TI, D0, Hlen', TOK. fold m Lf in Hlen'. fold Lf in TOK, TI.
destruct (cfail_nodes ns q i (Lf - 1 + elen k0) ok0 ok1 ltac:(lia)) as (_ & NDo & NDq & NK0 & NK1). fold m nd in NDo, NDq, NK0, NK1.
assert (Hb0 : elen k0 = (if ok0 then 1 else 0)) by (subst ok0; destruct k0 as [|? [|]]; [reflexivity | reflexivity | cbn in KID0; destruct KID0]).
assert (Hb1 : elen k1 = (if ok1 then 1 else 0)) by (subst ok1; destruct k1 as [|? [|]]; [reflexivity | reflexivity | cbn in KID1; destruct KID1]).
assert (Hlen2 : elen (cfail_ns ns q i (Lf - 1 + elen k0) ok0 ok1) = m + elen (k0 ++ k1)) by (rewrite Hlen', Hk01, Hb0, Hb1; destruct ok0, ok1; lia).
unfold at_FAIL. rewrite Hlen2.
split; [apply (rgba_inv_kept Lc Ac memc mdc Lc Ac mem' mdc HINV HJ' Hinit); intros x Hx; apply FR; lia|].
split; [exact Hfrm'|]. split; [exact PO|]. split; [exact TOK|]. split; [lia|].
split; [exact CB'|]. split; [exact STAT'|]. split; [rewrite Hroot; exact SL'|]. split; [exists E'; split; [exact Hpa' | exact HE0E']|].
split; [unfold elen in *; rewrite length_app; lia|]. split; [| exact HB'].
intros j Hj.
destruct (Z.eq_dec j q) as [->|Hnq].
{
rewrite (tnth_app_l tns (k0 ++ k1) q) by lia. fold tn a. split; [| split; [exact Wlen | exact Tnz]].
unfold node_mem. rewrite NDq. cbn [n_leaf n_k0 n_k1]. rewrite (tnth_app_l tns (k0 ++ k1) q) by lia. fold tn a.
assert (O0 : oaddr (tns ++ (k0 ++ k1)) (if ok0 then Some m else None) = res0).
{ subst ok0. destruct k0 as [|t0 [|]]; cbn [kid_ok] in KID0; [cbn; symmetry; exact KID0 | | destruct KID0].
cbn [oaddr app]. rewrite <- Hlen. rewrite (tnth_app_new0 tns t0 k1). symmetry. exact (proj1 KID0). }
assert (O1 : oaddr (tns ++ (k0 ++ k1)) (if ok1 then Some (m + (if ok0 then 1 else 0)) else None) = res1).
{ rewrite <- Hb0. subst ok1. destruct k1 as [|t1 [|]]; cbn [kid_ok] in KID1; [cbn; symmetry; exact KID1 | | destruct KID1].
cbn [oaddr]. destruct k0 as [|t0 [|]]; [| | cbn in KID0; destruct KID0].
- change (elen []) with 0. rewrite Z.add_0_r, <- Hlen. cbn [app]. rewrite (tnth_app_new0 tns t1 []). symmetry. exact (proj1 KID1).
- change (elen [t0]) with 1. rewrite <- Hlen. cbn [app]. rewrite (tnth_app_new1 tns t0 t1 []). symmetry. exact (proj1 KID1). }
rewrite O0, O1. exact OBJ'. }
destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
{
rewrite (tnth_app_l tns (k0 ++ k1) j) by lia. destruct (TM j ltac:(lia)) as (_ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tz).
split; [| split; [exact Wl | exact Tz]].
apply (node_mem_ext segs mem' ns _ tns (k0 ++ k1) j (NDo j ltac:(lia) Hnq) ltac:(lia) (OLDK j ltac:(lia)) (NM' j ltac:(lia) Hnq)). }
subst ok0 ok1.
destruct k0 as [|t0 [|]]; [| | cbn in KID0; destruct KID0]; destruct k1 as [|t1 [|]]; try (cbn in KID1; destruct KID1; fail);
cbn [app] in *; change (elen (@nil tnode)) with 0 in *; try change (elen [t0]) with 1 in *; try change (elen [t1]) with 1 in *;
try change (elen [t0; t1]) with 2 in *.
- exfalso. lia.
-
rewrite !Z.add_0_r in *. assert (Ej : j = m) by lia. subst j.
assert (Et : tnth (tns ++ [t1]) m = t1) by (rewrite <- Hlen; apply tnth_app_new0). rewrite Et.
cbn [kid_ok] in KID1'. destruct KID1' as (Er & Tnz1 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz1]]. unfold node_mem. rewrite (NK1 eq_refl). cbn [n_leaf]. rewrite Et. exact Tobj.
-
assert (Ej : j = m) by lia. subst j.
assert (Et : tnth (tns ++ [t0]) m = t0) by (rewrite <- Hlen; apply tnth_app_new0). rewrite Et.
cbn [kid_ok] in KID0'. destruct KID0' as (Er & Tnz0 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz0]]. unfold node_mem. rewrite (NK0 eq_refl). cbn [n_leaf]. rewrite Et. exact Tobj.
-
assert (Et0 : tnth (tns ++ [t0; t1]) m = t0) by (rewrite <- Hlen; apply tnth_app_new0).
assert (Et1 : tnth (tns ++ [t0; t1]) (m + 1) = t1) by (rewrite <- Hlen; apply tnth_app_new1).
destruct (Z.eq_dec j m) as [->|Hnm].
+ rewrite Et0. cbn [kid_ok] in KID0'. destruct KID0' as (Er & Tnz0 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz0]]. unfold node_mem. rewrite (NK0 eq_refl). cbn [n_leaf]. rewrite Et0. exact Tobj.
+ assert (Ej : j = m + 1) by lia. subst j. rewrite Et1.
cbn [kid_ok] in KID1'. destruct KID1' as (Er & Tnz1 & _ & _ & _ & (_ & _ & _ & _ & Wl & _) & Tobj & _).
split; [| split; [exact Wl | exact Tnz1]]. unfold node_mem. rewrite (NK1 eq_refl). cbn [n_leaf]. rewrite Et1. exact Tobj. }
assert (OKPACK : forall (mem' : word -> option byte) t0 t1,
k0 = [t0] -> k1 = [t1] ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> ~ (sp + 936 + 8 * m <= x < sp + 936 + 8 * m + 16) -> mbyte segs mem' x = mbyte segs memc x) ->
val_mem segs mem' (a + 8) 8 res1 -> word_mem segs mem' (sp + 936 + 8 * m) res0 -> word_mem segs mem' (sp + 936 + 8 * (m + 1)) res1 ->
let st' := csplit {| c_E := E; c_ns := ns; c_q := q |} E' i in
cinv cnt E0 st' /\ nleaves (c_ns st') = Lf + 1 /\ c_q st' = q + 1 /\ c_E st' = E' /\ elen (c_ns st') = m + 2 /\
cr_statics mem' /\ cl_slots mem' (tn_addr (tnth tns 0)) /\ arr8 segs mem' p (pal_bytes E' ++ tail) /\ arr32 segs mem' fdp (fr_vals E') /\ val_mem segs mem' (sp + 934) 2 (Lf + 1) /\
cl_nodes mem' (c_ns st') (tns ++ [t0; t1]) /\
(forall j, q + 1 <= j < m + 2 -> tn_facts (tnth (tns ++ [t0; t1]) j) (node (c_ns st') j)) /\
Permutation (blocks Lc Ac) (SB ++ node_blocks (tns ++ [t0; t1]) (m + 2)) /\
1 <= res0 < 2 ^ 63 /\ 1 <= res1 < 2 ^ 63).
{ intros mem' t0 t1 E0k E1k FR Vres W0 W1. subst k0 k1.
cbn [kid_ok] in KID0, KID1. change (elen [t0]) with 1 in *. change (elen [t0; t1]) with 2 in *. change (elen ([t0] ++ [t1])) with 2 in *. cbn [app] in *.
destruct KID0 as (Er0 & Tnz0 & Ti0 & Tx0 & Tc0 & Twf0 & _ & Tf0 & Twb0). destruct KID1 as (Er1 & Tnz1 & Ti1 & Tx1 & Tc1 & Twf1 & _ & Tf1 & Twb1).
assert (Et0 : tnth (tns ++ [t0; t1]) m = t0) by (rewrite <- Hlen; apply tnth_app_new0).
assert (Et1 : tnth (tns ++ [t0; t1]) (m + 1) = t1) by (rewrite <- Hlen; apply tnth_app_new1).
destruct (Pn m ltac:(lia)) as (B00 & B01 & _). rewrite Et0 in B00, B01. destruct (Pn (m + 1) ltac:(lia)) as (B10 & B11 & _). rewrite Et1 in B10, B11.
assert (Hres01 : 1 <= res0 < 2 ^ 63 /\ 1 <= res1 < 2 ^ 63) by (rewrite Er0, Er1; clear -B00 B01 B10 B11 Tnz0 Tnz1 Hac HNS; lia).
destruct (POST mem' res1 FR Vres ltac:(lia)) as (STAT' & SL' & Hpa' & Hfa' & OBJ' & NM' & NL' & KID0' & KID1').
assert (HE'ok : ent_ok E') by exact (ent_ok_perm _ _ HE0E' HE0ok).
cbn [kid_ok] in KID0', KID1'. destruct KID0' as (_ & _ & _ & _ & _ & _ & Tobj0 & _). destruct KID1' as (_ & _ & _ & _ & _ & _ & Tobj1 & _).
destruct (csplit_inv dentry cnt E0 {| c_E := E; c_ns := ns; c_q := q |} P E' i CINV ltac:(cbn; lia) Hlohi PD) as (CINV' & HL' & Hlen').
destruct (csplit_nodes {| c_E := E; c_ns := ns; c_q := q |} E' i ltac:(cbn; lia)) as (Hlen2 & NDo & NDq & ND0 & ND1 & Hq' & HE').
cbn [c_ns c_q c_E] in CINV', HL', Hlen', Hlen2, NDo, NDq, ND0, ND1, Hq', HE'. fold m nd Lf in Hlen2, NDo, NDq, ND0, ND1, HL'. fold lo hi in NDq, ND0, ND1.
set (ns' := c_ns (csplit {| c_E := E; c_ns := ns; c_q := q |} E' i)) in *.
cbv zeta. refine (conj CINV' (conj HL' (conj Hq' (conj HE' (conj Hlen2 (conj STAT' (conj SL' (conj Hpa' (conj Hfa' _))))))))).
split. { change (elen [t1]) with 1 in Vnln. replace (Lf - 1 + 1 + 1) with (Lf + 1) in Vnln by lia. eapply val_mem_frame; [exact Vnln | intros i0 Hi0; apply FR; lia]. }
split.
{
split; [rewrite Hlen2; unfold elen in *; rewrite length_app; cbn [length]; lia|].
split.
{ intros j Hj. rewrite Hlen2 in Hj.
destruct (Z.eq_dec j q) as [->|Hnq].
{ rewrite (tnth_app_l tns [t0; t1] q) by lia. fold tn. split.
- unfold node_mem. rewrite NDq. cbn [n_leaf n_k0 n_k1 oaddr]. rewrite Et0, Et1, (tnth_app_l tns [t0; t1] q) by lia. fold tn a. rewrite <- Er0, <- Er1. exact OBJ'.
- rewrite NDq. exact TMq. }
destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
{ rewrite (tnth_app_l tns [t0; t1] j) by lia. split.
- apply (node_mem_ext segs mem' ns _ tns [t0; t1] j (NDo j ltac:(lia) Hnq) ltac:(lia) (OLDK j ltac:(lia)) (NM' j ltac:(lia) Hnq)).
- rewrite (NDo j ltac:(lia) Hnq). apply TM. lia. }
destruct (Z.eq_dec j m) as [->|Hnm].
{ rewrite Et0. split; [unfold node_mem; rewrite ND0; cbn [n_leaf]; rewrite Et0; exact Tobj0|].
rewrite ND0. split; [exact Ti0|]. split; [exact Tx0|]. split; [exact Tc0|]. split; [exact Twf0 | exact Tnz0]. }
assert (Ej : j = m + 1) by lia. subst j. rewrite Et1.
split; [unfold node_mem; rewrite ND1; cbn [n_leaf]; rewrite Et1; exact Tobj1|].
rewrite ND1. split; [exact Ti1|]. split; [exact Tx1|]. split; [cbn [n_col]; rewrite Tc1; lia|]. split; [exact Twf1 | exact Tnz1]. }
split.
{ intros j Hj. rewrite Hlen2 in Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm]; [rewrite (tnth_app_l tns [t0; t1] j) by lia; apply NL'; lia|].
destruct (Z.eq_dec j m) as [->|Hnm]; [rewrite Et0, <- Er0; exact W0|].
assert (Ej : j = m + 1) by lia. subst j. rewrite Et1, <- Er1. exact W1. }
split.
{ intros j blc i0 Hj Hb Hi0. rewrite Hlen2 in Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- rewrite (tnth_app_l tns [t0; t1] j) in Hb |- * by lia. exact (NW j blc i0 ltac:(lia) Hb Hi0).
- destruct (Z.eq_dec j m) as [->|Hnm]; [rewrite Et0 in Hb |- *; exact (Twb0 blc i0 Hb Hi0)|].
assert (Ej : j = m + 1) by lia. subst j. rewrite Et1 in Hb |- *. exact (Twb1 blc i0 Hb Hi0). }
intros j Hj. rewrite Hlen2 in Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- rewrite (tnth_app_l tns [t0; t1] j) by lia. exact (MOK j ltac:(lia)).
- destruct (Z.eq_dec j m) as [->|Hnm].
+ rewrite Et0. exact (means_of_facts t0 _ E' lo (i - 1) Tf0 HE'ok ltac:(lia) ltac:(lia) eq_refl (proj1 (proj2 (proj2 (proj2 (proj2 Twf0)))))).
+ assert (Ej : j = m + 1) by lia. subst j. rewrite Et1. exact (means_of_facts t1 _ E' i hi Tf1 HE'ok ltac:(lia) ltac:(lia) eq_refl (proj1 (proj2 (proj2 (proj2 (proj2 Twf1)))))). }
split.
{ intros j Hj. destruct (Z_lt_le_dec j m) as [Hjm|Hjm].
- rewrite (tnth_app_l tns [t0; t1] j), (NDo j) by lia. apply FACTS. lia.
- destruct (Z.eq_dec j m) as [->|Hnm]; [rewrite Et0, ND0; exact Tf0|].
assert (Ej : j = m + 1) by lia. subst j. rewrite Et1, ND1. exact Tf1. }
split; [exact HB' | exact Hres01]. }
assert (NWq : forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte RGBA_STK sp0 FPF (blocks L A) blc (a + j)) by (intros blc j Hb Hj; exact (NW q blc j ltac:(lia) Hb Hj)).
destruct k1 as [|t1 [|]]; [| | cbn in KID1; destruct KID1].
-
cbn [kid_ok] in KID1.
assert (Rres0 : 0 <= res0 < 2 ^ 64).
{ destruct k0 as [|t0 [|]]; [cbn [kid_ok] in KID0; lia | | cbn in KID0; destruct KID0].
pose proof KID0 as K0'. cbn [kid_ok] in K0'. destruct K0' as (Er0 & Tnz0 & _).
assert (Et0 : tnth (tns ++ ([t0] ++ [])) m = t0) by (rewrite <- Hlen; apply tnth_app_new0).
destruct (Pn m ltac:(change (elen ([t0] ++ [])) with 1; lia)) as (B00 & B01 & _). rewrite Et0 in B00, B01.
rewrite Er0. clear -B00 B01 Tnz0 Hac HNS. lia. }
eapply (S3_fail1 API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc a res0 _ HJ NWq Hain G27 ltac:(rewrite G10, KID1; reflexivity) Rres0 Vc0).
intros regs' mem' HJ' Vc1 FR' K'.
apply (KFAIL fy regs' Lc Ac mem' mdc (cfail_ns ns q i (Lf - 1 + elen k0) (match k0 with [] => false | _ => true end) false) (tns ++ (k0 ++ [])) (Lf + 1)).
apply (FAILPACK fy regs' mem' _ false eq_refl eq_refl Hfrm HJ' FR' ltac:(rewrite KID1; exact Vc1) ltac:(lia)).
exists q. exact (cl_base_upd regs regs' _ q q K' ltac:(vm_compute; reflexivity) ltac:(rewrite (K' 9%bv ltac:(inl)); exact G9) CB).
- destruct k0 as [|t0 [|]]; [| | cbn in KID0; destruct KID0].
+
cbn [kid_ok] in KID0. pose proof KID1 as K1'. cbn [kid_ok] in K1'. destruct K1' as (Er1 & Tnz1 & _).
assert (Et1 : tnth (tns ++ [t1]) m = t1) by (rewrite <- Hlen; apply tnth_app_new0).
destruct (Pn m ltac:(change (elen ([] ++ [t1])) with 1; lia)) as (B10 & B11 & _). cbn [app] in B10, B11. rewrite Et1 in B10, B11.
eapply (S3_fail0 API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc a res1 _ HJ NWq Hain G27 G10
ltac:(rewrite Er1; clear -B10 B11 Tnz1 Hac HNS; lia) ltac:(rewrite <- KID0; exact Vc0)).
intros regs' mem' HJ' Vc1 FR' K'.
apply (KFAIL fy regs' Lc Ac mem' mdc (cfail_ns ns q i (Lf - 1 + elen (@nil tnode)) false true) (tns ++ ([] ++ [t1])) (Lf + 1)).
apply (FAILPACK fy regs' mem' false true eq_refl eq_refl Hfrm HJ' FR' Vc1 ltac:(rewrite Er1; clear -B10 B11 Tnz1 Hac HNS; lia)).
exists q. exact (cl_base_upd regs regs' _ q q K' ltac:(vm_compute; reflexivity) ltac:(rewrite (K' 9%bv ltac:(inl)); exact G9) CB).
+
cbn [app] in Hroot.
pose proof KID0 as K0'. pose proof KID1 as K1'. cbn [kid_ok] in K0', K1'. destruct K0' as (Er0 & Tnz0 & _). destruct K1' as (Er1 & Tnz1 & _).
assert (Et0 : tnth (tns ++ [t0; t1]) m = t0) by (rewrite <- Hlen; apply tnth_app_new0).
assert (Et1 : tnth (tns ++ [t0; t1]) (m + 1) = t1) by (rewrite <- Hlen; apply tnth_app_new1).
destruct (Pn m ltac:(change (elen ([t0] ++ [t1])) with 2; lia)) as (B00 & B01 & _). cbn [app] in B00, B01. rewrite Et0 in B00, B01.
destruct (Pn (m + 1) ltac:(change (elen ([t0] ++ [t1])) with 2; lia)) as (B10 & B11 & _). cbn [app] in B10, B11. rewrite Et1 in B10, B11.
change (elen [t0]) with 1 in Vnln. change (elen [t1]) with 1 in Vnln. replace (Lf - 1 + 1 + 1) with (Lf + 1) in Vnln by lia.
assert (Hnl : sp + 912 + 16 * (Lf + 1) = sp + 936 + 8 * m) by lia.
pose proof SLOTS as (_ & S72 & _).
destruct (Z_lt_le_dec (Lf + 1) 255) as [Hlt|Hge].
*
eapply (S3_loop API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc a q (Lf + 1) res0 res1 sp _ HJ NWq Hain
ltac:(lia) ltac:(lia) Hal16 G2 G27 G10 G9 ltac:(lia) ltac:(lia)
ltac:(rewrite Er0; clear -B00 B01 Tnz0 Hac HNS; lia) ltac:(rewrite Er1; clear -B10 B11 Tnz1 Hac HNS; lia) Vc0 Vnln S72).
intros regs' mem' (HJ' & Vc1 & W0 & W1 & FR' & R9 & R29 & R14 & R15 & R16 & K').
rewrite Hnl in W0, FR'. replace (sp + 920 + 16 * (Lf + 1)) with (sp + 936 + 8 * (m + 1)) in W1 by lia.
replace (sp + 928 + 16 * (Lf + 1)) with (sp + 936 + 8 * m + 16) in FR' by lia.
destruct (OKPACK mem' t0 t1 eq_refl eq_refl FR' Vc1 W0 W1) as (CINV' & HL' & Hq' & HE' & Hlen2 & STAT' & SL' & Hpa' & Hfa' & Vn' & NODES' & FACTS' & HB2 & _).
apply (KCL fy regs' Lc Ac mem' mdc (csplit {| c_E := E; c_ns := ns; c_q := q |} E' i) (tns ++ [t0; t1]) Hq').
unfold at_CL. rewrite Hq', HE', HL', Hlen2.
split; [apply (rgba_inv_kept Lc Ac memc mdc Lc Ac mem' mdc HINV HJ' Hinit); intros x Hx; apply FR'; lia|].
split; [exact Hfrm|]. split; [exact CINV'|]. split; [lia|].
split; [split; [exact (cl_base_upd regs regs' _ q (q + 1) K' ltac:(vm_compute; reflexivity) R9 CB) | split; [exact R29 | exact (conj R14 (conj R15 R16))]]|].
split; [exact STAT'|]. split; [rewrite Hroot; exact SL'|]. split; [exact Hpa'|]. split; [exact Hfa'|]. split; [exact Vn'|]. split; [exact NODES'|]. split; [exact FACTS' | exact HB2].
*
eapply (S3_exit API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc a q (Lf + 1) res0 res1 sp _ HJ NWq Hain
ltac:(lia) ltac:(lia) Hal16 G2 G27 G10 G9 ltac:(lia) ltac:(lia)
ltac:(rewrite Er0; clear -B00 B01 Tnz0 Hac HNS; lia) ltac:(rewrite Er1; clear -B10 B11 Tnz1 Hac HNS; lia) Vc0 Vnln S72).
intros regs' mem' (HJ' & Vc1 & W0 & W1 & FR' & R9 & R29 & R14 & R15 & R16 & K').
rewrite Hnl in W0, FR'. replace (sp + 920 + 16 * (Lf + 1)) with (sp + 936 + 8 * (m + 1)) in W1 by lia.
replace (sp + 928 + 16 * (Lf + 1)) with (sp + 936 + 8 * m + 16) in FR' by lia.
destruct (OKPACK mem' t0 t1 eq_refl eq_refl FR' Vc1 W0 W1) as (CINV' & HL' & Hq' & HE' & Hlen2 & STAT' & SL' & Hpa' & Hfa' & Vn' & NODES' & FACTS' & HB2 & _).
apply (KDONE fy regs' Lc Ac mem' mdc (csplit {| c_E := E; c_ns := ns; c_q := q |} E' i) (tns ++ [t0; t1])).
unfold at_DONE. rewrite HE', HL', Hlen2, Hq'.
split; [apply (rgba_inv_kept Lc Ac memc mdc Lc Ac mem' mdc HINV HJ' Hinit); intros x Hx; apply FR'; lia|].
split; [exact Hfrm|]. split; [exact CINV'|]. split; [lia|].
split; [exact (cl_base_upd regs regs' _ q (q + 1) K' ltac:(vm_compute; reflexivity) R9 CB)|].
split; [exact STAT'|]. split; [rewrite Hroot; exact SL'|]. split; [exact Hpa'|]. split; [exact NODES' | exact HB2].
Qed.
Theorem CL_step : forall fy regs Lc Ac memc mdc st tns,
at_CL fy regs Lc Ac memc mdc st tns ->
K_CLn (c_q st + 1) -> K_DONE -> K_FAIL ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros fy regs Lc Ac memc mdc [E ns q] tns HAT KCL KDONE KFAIL.
unfold at_CL in HAT. cbn [c_E c_ns c_q] in HAT, KCL.
destruct HAT as (HINV & Hfrm & CINV & HLf & CR & STAT & SLOTS & Hpa & Hfa & Vnln & NODES & FACTS & HB).
pose proof cr_consts as (HRS & HFR & HNT & HNS & HNM & Hac & HlenE0 & Htl & HT3).
destruct (sp_facts Lc Ac memc mdc HINV) as (Hsp & Hal0 & Hal16 & Hceil & H63 & Hstw). rewrite HRS in Hceil, Hstw.
pose proof HINV as (HJ & Hinit & _ & Hra0 & _ & Htp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _).
pose proof CR as (CB & G29 & G14x). cbv iota in G14x. destruct G14x as (G14 & G15 & G16).
pose proof CB as ((G2 & G3 & G4) & G9 & G22 & G23 & G18 & G19 & G8 & G20 & G25 & G24 & G21).
pose proof NODES as (Hlen & NM & NL & NW & MOK).
set (m := elen ns) in *. set (Lf := nleaves ns) in *.
destruct HE0 as (HE0ok & HE0nd & HE0sum).
destruct (crawl_continue cnt E0 _ CINV 255 ltac:(cbn; lia) ltac:(lia)) as (Hqm & Hq0 & Hm & Hm2 & Hleaf & Hlohi & Hhic & Hcol & HL1).
cbn [c_ns c_q] in Hqm, Hq0, Hm, Hm2, Hleaf, Hlohi, Hhic, Hcol, HL1. fold m Lf in Hqm, Hm, Hm2, Hcol, HL1.
set (nd := node ns q) in *. set (tn := tnth tns q) in *. set (a := tn_addr tn) in *. set (lo := n_lo nd) in *. set (hi := n_hi nd) in *.
pose proof (cinv_counts cnt E0 _ CINV) as (C1a & C1b & C1c & C1d & C1e). cbn [c_E c_ns c_q] in C1d, C1e.
destruct (NM q ltac:(lia)) as [NMq TMq]. fold nd tn in NMq, TMq. unfold node_mem in NMq. fold nd tn in NMq. rewrite Hleaf in NMq.
destruct NMq as (c0 & c1 & OBJq). fold a in OBJq.
pose proof TMq as (Timin & Timax & Tcidx & Twf & Tnz). fold lo in Timin. fold hi in Timax. fold a in Tnz.
pose proof Twf as (Wcut & Wcidx & Wii & Wimax & Wlen & Wmean).
pose proof (proj1 HJ) as HH.
destruct (cl_heap_facts Lc Ac memc mdc tns m HH HB) as (Pp & Pf & Ppf & Pn & Psn & _).
destruct (Pn q ltac:(lia)) as (A0 & A1 & A16 & Anp & Anf). fold tn a in A0, A1, A16, Anp, Anf.
assert (A8 : a mod 8 = 0).
{ pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm. rewrite A16 in Hdm. rewrite Hdm. replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hcnt10000 : cnt <= 10000) by (clear -Hcnt; unfold RGB_NMAX in Hcnt; lia).
pose proof OBJq as OBJx. rewrite (node_vals_expand c0 c1 tn 1 Wlen) in OBJx.
assert (FLD : forall j f v, nth_error LAY_Node j = Some f -> nth_error [c0; c1; nth 0 (tn_mean tn) 0; nth 1 (tn_mean tn) 0; nth 2 (tn_mean tn) 0; tn_imin tn; tn_imax tn; tn_cut tn; tn_cidx tn; 1] j = Some v ->
val_mem segs memc (a + fst f) (N.to_nat (snd f)) v) by (intros j f v Hf Hv; exact (proj1 (obj_at_nth segs memc a LAY_Node _ j f v OBJx Hf Hv))).
pose proof (FLD 5%nat (40, 4%N) (tn_imin tn) eq_refl eq_refl) as Vimin. pose proof (FLD 6%nat (44, 4%N) (tn_imax tn) eq_refl eq_refl) as Vimax.
pose proof (FLD 7%nat (48, 1%N) (tn_cut tn) eq_refl eq_refl) as Vcut.
cbn [fst snd N.to_nat] in Vimin, Vimax, Vcut. rewrite Timin in Vimin. rewrite Timax in Vimax. clear OBJx.
pose proof (NL q ltac:(lia)) as Wq. fold tn a in Wq.
destruct (heap_model _ _ LAWS _ _ _ _ HH) as (Hh & Hlz & _).
destruct (Z.eq_dec lo hi) as [Heq | Hne].
-
destruct (LH_skip fy regs memc q a lo sp Lf G2 G9 G14 G15 G16 G29 ltac:(lia) ltac:(lia) Hal16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A8 ltac:(lia)
Wq Vimin ltac:(rewrite Heq; exact Vimax)) as (regs1 & Hms1 & R9 & R14 & R15 & R16 & K1).
eapply (SR_msteps segs _ _ mdc _ Hh Hlz Hms1).
apply (KCL fy regs1 Lc Ac memc mdc (cskip {| c_E := E; c_ns := ns; c_q := q |}) tns eq_refl).
unfold at_CL, cskip. cbn [c_E c_ns c_q]. fold m Lf.
split; [exact HINV|]. split; [exact Hfrm|]. split; [exact (cskip_inv cnt E0 _ CINV ltac:(cbn; lia) Heq)|]. split; [exact HLf|].
split; [split; [exact (cl_base_upd regs regs1 _ q (q + 1) K1 ltac:(vm_compute; reflexivity) R9 CB) | split; [rewrite (K1 29%bv ltac:(inl)); exact G29 | exact (conj R14 (conj R15 R16))]]|].
split; [exact STAT|]. split; [exact SLOTS|]. split; [exact Hpa|]. split; [exact Hfa|]. split; [exact Vnln|]. split; [exact NODES|]. split; [| exact HB].
intros j Hj. apply FACTS. lia.
-
assert (Hlt : lo < hi) by lia.
destruct (LH_split fy regs memc q a lo hi sp Lf G2 G9 G14 G15 G16 G29 ltac:(lia) ltac:(lia) Hal16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A8 ltac:(lia) Hlt ltac:(lia)
Wq Vimin Vimax) as (regs1 & Hms1 & R27 & R26 & R11 & K1).
eapply (SR_msteps segs _ _ mdc _ Hh Hlz Hms1).
destruct (FACTS q ltac:(lia)) as [Fq Nq]. fold tn nd in Fq, Nq.
pose proof (cinv_seg cnt E0 _ CINV q ltac:(cbn; lia)) as Hseg. cbn [c_E c_ns c_q] in Hseg. fold nd lo hi in Hseg.
set (cut := tn_cut tn). set (mean := nth (Z.to_nat cut) (tn_mean tn) 0).
assert (Hmean : 0 <= mean < 2 ^ 64).
{ subst mean. apply (Forall_nth (fun x => 0 <= x < 2 ^ 64) (tn_mean tn)); [exact Wmean | rewrite Wlen; subst cut; lia]. }
assert (Vmean : val_mem segs memc (a + 16 + 8 * cut) 8 mean).
{ assert (Hc3 : cut = 0 \/ cut = 1 \/ cut = 2) by (subst cut; lia).
destruct Hc3 as [Ec | [Ec | Ec]]; rewrite Ec; subst mean; rewrite Ec.
- replace (a + 16 + 8 * 0) with (a + 16) by lia. exact (FLD 2%nat (16, 8%N) _ eq_refl eq_refl).
- replace (a + 16 + 8 * 1) with (a + 24) by lia. exact (FLD 3%nat (24, 8%N) _ eq_refl eq_refl).
- replace (a + 16 + 8 * 2) with (a + 32) by lia. exact (FLD 4%nat (32, 8%N) _ eq_refl eq_refl). }
assert (HEok : ent_ok E /\ List.NoDup (map fst E)) by (split; [exact (ent_ok_perm _ _ C1e HE0ok) | exact (NoDup_fst_perm _ _ C1e HE0nd)]).
destruct HEok as [HEok HEnd].
assert (HsumE : zsum (fr_vals E) = zsum (fr_vals E0)) by (apply zsum_fr_perm; exact C1e).
assert (Hq' : is_quot mean (wdot (dseg cut E lo hi)) (wsum (dseg cut E lo hi))).
{ unfold mean. change (dseg cut E lo hi) with (segd cut (zsub E lo hi)). rewrite Hseg. apply Fq. subst cut. lia. }
assert (HaN : forall x, 0 <= x < 56 -> ~ (p <= a + x < p + 3 * elen E) /\ ~ (fdp <= a + x < fdp + 4 * elen E) /\ ~ (sp + 5036 <= a + x < sp + 5039)).
{ intros x Hx. rewrite C1d. pose proof Anp as X1. pose proof Anf as X2. unfold disj_blocks in X1, X2. lia. }
assert (PI : pinv dentry (Ptest cut (wsum (dseg cut E lo hi)) (wdot (dseg cut E lo hi))) lo hi E E lo hi).
{ apply (pinv_start E lo hi cut HEok ltac:(lia) ltac:(lia) ltac:(rewrite C1d; lia)).
change (dseg cut E lo hi) with (segd cut (zsub E lo hi)). rewrite Hseg. apply Nq. exact Hlt. }
pose proof (pinv_meas_bound dentry _ _ _ _ _ _ _ PI) as HPM.
assert (S56 : word_mem segs memc (sp + 56) 1) by (destruct SLOTS as (S56 & _); exact S56).
assert (Hf31 : Forall (fun e => snd e < 2 ^ 31) E) by (apply ent_freq31; [exact HEok | rewrite HsumE, HNM in *; lia]).
assert (Hfn0' : ~ In (fdp, 4 * elen E) (blocks L A)) by (rewrite C1d; exact (proj2 Htmp)).
assert (Hlen' : 3 * elen E + zlen tail = 3 * T) by (rewrite C1d; exact HT3).
assert (Hpf' : disj_blocks p (3 * T) fdp (4 * elen E)) by (rewrite C1d; exact Ppf).
assert (Hcnt' : elen E < 2 ^ 29) by (rewrite C1d; lia).
assert (Hlohi' : 0 <= lo /\ lo < hi /\ hi < elen E) by (rewrite C1d; lia).
assert (Hcut' : 0 <= cut <= 2) by (subst cut; lia).
assert (Hwin' : sp0 - RGBA_STK <= sp + 5036 /\ sp + 5168 <= sp0 /\ sp mod 16 = 0) by lia.
assert (Ha' : 4096 <= a /\ a + 56 <= alloc_ceiling /\ a mod 8 = 0) by lia.
assert (CB1 : cl_base regs1 q) by exact (cl_base_upd regs regs1 _ q q K1 ltac:(vm_compute; reflexivity) ltac:(rewrite (K1 9%bv ltac:(inl)); exact G9) CB).
assert (KS : K_SPLIT API RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc p fdp sp lo hi cut E tail regs1 memc
(@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest)).
{ intros fy2 regs2 mem2 E' i Hfrm2 HJ2 PD Q26 K2 Hpa2 Hfa2 FR2.
assert (CRU : cr_unchanged memc mem2).
{ apply (cr_unchanged_intro Lc Ac memc mdc tns m mem2 HH HB ltac:(lia) H63). intros x Hx N1 N2 N3 N4 N5. apply FR2; [exact Hx | rewrite C1d; lia | rewrite C1d; lia | lia]. }
apply (SPLIT_to_S2 fy2 regs2 Lc Ac mem2 mdc {| c_E := E; c_ns := ns; c_q := q |} tns E' i).
2:{ intros fy3 regs3 Lc3 Ac3 mem3 md3 k0 res0 HS2.
apply (S2_to_S3 fy3 regs3 Lc3 Ac3 mem3 md3 _ tns E' i k0 res0 _ HS2).
intros fy4 regs4 Lc4 Ac4 mem4 md4 k1 res1 HS3.
exact (S3_finish fy4 regs4 Lc4 Ac4 mem4 md4 _ tns E' i k0 k1 res0 res1 HS3 KCL KDONE KFAIL). }
unfold at_SPLIT. cbn [c_E c_ns c_q]. fold m Lf nd tn lo hi. fold a.
split; [apply (rgba_inv_kept Lc Ac memc mdc Lc Ac mem2 mdc HINV HJ2 Hinit); intros x Hx; apply FR2; rewrite ?C1d; lia|].
split; [exact Hfrm2|]. split; [exact CINV|]. split; [exact HLf|]. split; [lia|]. split; [exact Hlt|].
split; [eexists; exact PD|].
split. { split; [exact (cl_base_upd regs1 regs2 _ q q K2 ltac:(vm_compute; reflexivity) ltac:(rewrite (K2 9%bv ltac:(inl)), (K1 9%bv ltac:(inl)); exact G9) CB1)|].
split; [rewrite (K2 29%bv ltac:(inl)), (K1 29%bv ltac:(inl)); exact G29 | exact I]. }
split; [rewrite (K2 27%bv ltac:(inl)); exact R27|]. split; [exact Q26|].
split; [exact (statics_kept memc mem2 STAT CRU)|]. split; [exact (cl_slots_kept memc mem2 _ SLOTS CRU)|]. split; [exact Hpa2|]. split; [exact Hfa2|].
split; [eapply val_mem_frame; [exact Vnln | intros i0 Hi0; apply FR2; rewrite ?C1d; lia]|].
split. { split; [exact Hlen|]. split.
- intros j Hj. split; [| exact (proj2 (NM j Hj))]. apply (node_mem_kept memc mem2 ns tns j (proj1 (NM j Hj))). intros i0 Hi0.
destruct (Pn j Hj) as (B0 & B1 & _ & Bp & Bf). unfold disj_blocks in Bp, Bf. apply FR2; rewrite ?C1d; lia.
- split; [| split; [exact NW | exact MOK]]. intros j Hj. eapply word_mem_frame; [exact (NL j Hj)|]. intros i0 Hi0. apply FR2; rewrite ?C1d; lia. }
split; [exact FACTS | exact HB]. }
assert (ATPR : at_PR API RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc p fdp sp T a lo hi cut mean E tail fy regs1 memc E lo hi).
{ unfold at_PR. split; [exact HJ|]. split; [exact Hfrm|].
split; [apply (blocks_of_CL Lc Ac tns m); [exact HB | left; apply SB_in_p]|].
split; [rewrite C1d; apply (blocks_of_CL Lc Ac tns m); [exact HB | left; apply SB_in_fdp]|].
split; [rewrite (K1 2%bv ltac:(inl)); exact G2|]. split; [exact R27|]. split; [exact R26|]. split; [exact R11|].
split; [rewrite (K1 25%bv ltac:(inl)); exact G25|]. split; [rewrite (K1 24%bv ltac:(inl)); exact G24|]. split; [rewrite (K1 23%bv ltac:(inl)); exact G23|].
split; [rewrite (K1 18%bv ltac:(inl)); exact G18|]. split; [rewrite (K1 19%bv ltac:(inl)); exact G19|]. split; [rewrite (K1 22%bv ltac:(inl)); exact G22|].
split; [exact S56|]. split; [exact Hpa|]. split; [exact Hfa|]. split; [exact Vcut|]. split; [exact Vmean|]. exact PI. }
eapply partition_SR with (API := API) (STK := RGBA_STK) (sp0 := sp0) (FP := FPF) (L := L) (A := A) (mem0 := mem0) (md0 := md0)
(Lc := Lc) (Ac := Ac) (md := mdc) (p := p) (fdp := fdp) (sp := sp) (T := T) (a := a) (lo := lo) (hi := hi) (cut := cut) (mean := mean)
(Ep := E) (tail := tail) (n := S (Z.to_nat (2 * (hi - lo) + 2))) (E := E) (i := lo) (k := hi).
all: first [exact KS | exact ATPR | exact IMG | exact (proj1 Htmp) | exact Hfn0' | exact Hlen' | exact HEok | exact Hf31 | exact Hpf' | exact Hcnt' |
exact Hlohi' | exact Hcut' | exact Hmean | exact Hq' | exact Hwin' | exact Ha' | exact HaN | lia].
Qed.
Theorem CL_loop : forall n fy regs Lc Ac memc mdc st tns,
510 - c_q st <= Z.of_nat n ->
at_CL fy regs Lc Ac memc mdc st tns -> K_DONE -> K_FAIL ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CL) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
induction n as [|n IH]; intros fy regs Lc Ac memc mdc st tns Hn HAT KDONE KFAIL.
- exfalso. destruct HAT as (_ & _ & CINV & HLf & _).
pose proof (cinv_counts cnt E0 st CINV) as (C1a & C1b & C1c & _). cbn in Hn. lia.
- apply (CL_step fy regs Lc Ac memc mdc st tns HAT); [| exact KDONE | exact KFAIL].
intros fy' regs' Lc' Ac' memc' mdc' st' tns' Hq' HAT'. apply (IH fy' regs' Lc' Ac' memc' mdc' st' tns'); [| exact HAT' | exact KDONE | exact KFAIL].
rewrite Hq'. rewrite Nat2Z.inj_succ in Hn. lia.
Qed.
Theorem CR_main : forall fy regs Lc Ac memc mdc,
frm_zero (@fp_csr fy) -> RINV Lc Ac memc mdc -> rgba_regs regs0 regs ->
getr regs 14 = Z_to_bv 64 (cnt - 1) -> getr regs 25 = Z_to_bv 64 p -> getr regs 24 = Z_to_bv 64 fdp -> getr regs 21 = Z_to_bv 64 2 ->
getr regs 18 = Z_to_bv 64 pnew -> getr regs 27 = Z_to_bv 64 N -> getr regs 20 = Z_to_bv 64 (ch_c C) -> getr regs 8 = Z_to_bv 64 r ->
cr_statics memc -> slot regs0 memc SL_96 (2 ^ 64 - 1 - fdp) -> arr8 segs memc p pal0 -> arr32 segs memc fdp fdl -> Permutation (blocks Lc Ac) SB ->
K_DONE -> K_FAIL -> K_XDm ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CR) memc rom) mdc) (@rgba_post _ API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros fy regs Lc Ac memc mdc Hfrm HINV (G2 & G3 & G4) G14 G25 G24 G21 G18 G27 Gc Gr STAT S96 Hpa Hfa HB KDONE KFAIL KXD.
pose proof cr_consts as (HRS & HFR & HNT & HNS & HNM & Hac & HlenE0 & Htl & HT3).
destruct (sp_facts Lc Ac memc mdc HINV) as (Hsp & Hal0 & Hal16 & Hceil & H63 & Hstw). rewrite HRS in Hceil, Hstw.
pose proof HINV as (HJ & Hinit & _ & Hra0 & _ & Htp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _).
destruct HE0 as (HE0ok & HE0nd & HE0sum).
assert (Hcnt10000 : cnt <= 10000) by (clear -Hcnt; unfold RGB_NMAX in Hcnt; lia).
pose proof (proj1 HJ) as HH.
assert (HB0 : Permutation (blocks Lc Ac) (SB ++ node_blocks [] 0)) by (change (node_blocks [] 0) with (@nil (Z * Z)); rewrite app_nil_r; exact HB).
destruct (cl_heap_facts Lc Ac memc mdc [] 0 HH HB0) as (Pp & Pf & Ppf & _ & Psn & _).
assert (Hpin : In (p, 3 * T) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB0); left; apply SB_in_p).
assert (Hfin : In (fdp, 4 * cnt) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB0); left; apply SB_in_fdp).
assert (Epal : pal_bytes E0 ++ tail = pal0) by (unfold E0, tail; apply pal_split_ents_of; lia).
assert (Efr : fr_vals E0 = fdl) by (unfold E0; apply fr_vals_ents_of; lia).
destruct (heap_model _ _ LAWS _ _ _ _ HH) as (Hh & Hlz & _).
eapply (R0_stretch API IMG fy regs memc RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mdc cnt sp _ HJ ltac:(lia) ltac:(lia) Hal16 G2 G14 ltac:(lia)).
intros regs1 mem1 HJ1 Vnln1 FR1 Q1 Q10 Q11 Q12 Q13 Q14 Q15 K1.
assert (Hpa1 : arr8 segs mem1 p (pal_bytes E0 ++ tail)).
{ rewrite Epal. eapply arr8_frame; [exact Hpa|]. intros x Hx. apply FR1; lia. }
assert (Hfa1 : arr32 segs mem1 fdp (fr_vals E0)).
{ rewrite Efr. eapply arr32_frame; [exact Hfa|]. intros x Hx. apply FR1; lia. }
pose proof (root_segment E0 0 HE0ok ltac:(lia)) as (_ & _ & Rw & _). rewrite HlenE0 in Rw.
eapply SR_bind.
{ apply (NTN fy RGBA_STK sp0 FPF L A mem0 md0 Lc Ac mem1 mdc regs1 p fdp (sp + 934) 0 (cnt - 1) 0 0 (pal_bytes E0 ++ tail) (fr_vals E0) HJ1 Hinit).
- rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. exact Hal16.
- rewrite (K1 4%bv ltac:(inl)), G4. exact Htp0.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- exact Hfrm.
- rewrite Q10. exact G25.
- rewrite Q11. exact G24.
- exact Q12.
- exact Q13.
- exact Q14.
- exact Q15.
- exact Hpa1.
- exact Hfa1.
- lia.
- lia.
- rewrite zlen_app_pal, HlenE0. lia.
- rewrite zlen_fr_vals, HlenE0. lia.
- lia.
- lia.
- rewrite zlen_app_pal, HlenE0. lia.
- lia.
- rewrite zlen_fr_vals, HlenE0. lia.
- pose proof (Z.div_mod fdp 16 ltac:(lia)) as Hdm. destruct Pf as (_ & _ & Pf16). rewrite Pf16 in Hdm. rewrite Hdm.
replace (16 * (fdp / 16) + 0) with ((4 * (fdp / 16)) * 4) by lia. apply Z.mod_mul. lia.
- exists p, (3 * T). split; [exact Hpin | rewrite zlen_app_pal, HlenE0; lia].
- exists fdp, (4 * cnt). split; [exact Hfin | rewrite zlen_fr_vals, HlenE0; lia].
- rewrite zlen_app_pal, zlen_fr_vals, HlenE0. pose proof Ppf as X. unfold disj_blocks in X. lia.
- intros i0 Hi0. rewrite getz_fr_vals by lia. apply (proj2 (ent_ok_at E0 i0 HE0ok ltac:(lia))).
- rewrite (node_list_dseg (pal_bytes E0 ++ tail) E0 0 (cnt - 1) 0 (pal_agrees_app E0 tail) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite Rw, HNM in *. lia.
- unfold spZ. rewrite (K1 2%bv ltac:(inl)), G2, unsigned_lit_small by lia. lia.
- lia.
- pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 934) with ((8 * (sp / 16) + 467) * 2) by lia. apply Z.mod_mul. lia.
- exact Vnln1.
- lia. }
cbv beta. intros c' (fx1 & Lc1 & Ac1 & regs2 & mem2 & md2 & res & -> & Hfrm2 & HJ2 & Hinit2 & HP2 & R10 & Hhi2 & Hkeep2 & Hres).
rewrite Q1.
assert (Hsp1 : spZ regs1 = sp) by (unfold spZ; rewrite (K1 2%bv ltac:(inl)), G2; apply unsigned_lit_small; lia). rewrite Hsp1 in Hhi2.
assert (STK2 : forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp - NTN_STK <= x < sp) -> ~ (sp + 934 <= x < sp + 936) -> mbyte segs mem2 x = mbyte segs memc x).
{ intros x Hx Hn1 Hn2. rewrite (Hhi2 x Hx Hn1 ltac:(lia)). apply FR1; lia. }
assert (BLK2 : forall b n i0, In (b, n) (blocks Lc Ac) -> 0 <= i0 < n -> mbyte segs mem2 (b + i0) = mbyte segs memc (b + i0)).
{ intros b n i0 Hb Hi0. rewrite (Hkeep2 b n i0 Hb Hi0).
destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n i0 HH Hb Hi0) as (_ & B0 & B1 & _). apply FR1; lia. }
assert (CRU : cr_unchanged memc mem2).
{ intros x [Hx | [Hx | (b & n0 & Hb & Hx)]].
- apply STK2; lia.
- apply STK2; lia.
- pose proof (SBs_in_SB _ Hb) as Hb'. assert (Hbb : In (b, n0) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB0); left; exact Hb').
replace x with (b + (x - b)) by lia. apply (BLK2 b n0 (x - b) Hbb ltac:(lia)). }
assert (RINV2 : RINV Lc1 Ac1 mem2 md2).
{ apply (rgba_inv_kept Lc Ac memc mdc Lc1 Ac1 mem2 md2 HINV HJ2 Hinit2). intros x Hx. apply STK2; lia. }
assert (STAT2 : cr_statics mem2) by exact (statics_kept memc mem2 STAT CRU).
assert (Hpa2 : arr8 segs mem2 p (pal_bytes E0 ++ tail)).
{ eapply arr8_frame; [exact Hpa1|]. intros x Hx. rewrite zlen_app_pal, HlenE0 in Hx. replace x with (p + (x - p)) by lia. apply (Hkeep2 p (3 * T)); [exact Hpin | lia]. }
assert (Hfa2 : arr32 segs mem2 fdp (fr_vals E0)).
{ eapply arr32_frame; [exact Hfa1|]. intros x Hx. rewrite zlen_fr_vals, HlenE0 in Hx. replace x with (fdp + (x - fdp)) by lia. apply (Hkeep2 fdp (4 * cnt)); [exact Hfin | lia]. }
assert (REGS : forall rr : reg, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. rewrite (regs_preserved_in _ _ rr HP2) by (revert Hrr; clear; intros Hrr; cbv [In] in Hrr; cbv [CALLEE_SAVED In]; intuition congruence).
apply K1. exact Hrr. }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh2 & Hlz2 & _).
destruct Hres as [(Hr0 & Hbl & Vn) | (Hr0 & Hr16 & (b1 & b2 & Hbl1 & Hbl2) & Hwb0 & Vn & nd0 & Ha0 & Him0 & Hix0 & Hc0 & Htree0 & Hwf0 & Hq0 & Hdim0)].
-
apply (R1_fail fx1 regs2 mem2 md2 _ Hh2 Hlz2 ltac:(rewrite R10, Hr0; reflexivity)).
intros regs3 K3. apply (KXD fx1 regs3 Lc1 Ac1 mem2 md2). unfold at_XDm.
split; [exact RINV2|]. split; [exact Hfrm2|].
split; [split; [rewrite (K3 2%bv ltac:(inl)), (REGS 2%bv ltac:(inl)); exact G2 | split; [rewrite (K3 3%bv ltac:(inl)), (REGS 3%bv ltac:(inl)); exact G3 | rewrite (K3 4%bv ltac:(inl)), (REGS 4%bv ltac:(inl)); exact G4]]|].
split; [split; [rewrite (K3 21%bv ltac:(inl)), (REGS 21%bv ltac:(inl)); exact G21 | split; [rewrite (K3 20%bv ltac:(inl)), (REGS 20%bv ltac:(inl)); exact Gc | split; [rewrite (K3 8%bv ltac:(inl)), (REGS 8%bv ltac:(inl)); exact Gr | rewrite (K3 18%bv ltac:(inl)), (REGS 18%bv ltac:(inl)); exact G18]]]|].
split; [rewrite (K3 24%bv ltac:(inl)), (REGS 24%bv ltac:(inl)); exact G24|].
split; [exact STAT2|]. split; [rewrite <- Epal; exact Hpa2|]. rewrite Hbl. exact HB.
-
destruct Htree0 as (Tnz0 & Tlen0 & Tobj0).
assert (Hroot_in : In (res, NODE_SIZE) (blocks Lc1 Ac1)) by (rewrite Hbl1; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc1 Ac1 mem2 md2 res NODE_SIZE (proj1 HJ2) Hroot_in ltac:(rewrite HNS; lia)) as (B0 & B1 & _).
assert (S962 : word_mem segs mem2 (sp + 96) (2 ^ 64 - 1 - fdp)).
{ unfold slot, SL_96 in S96. eapply word_mem_frame; [exact S96|]. intros i0 Hi0. apply STK2; lia. }
eapply (R1_ok API IMG fx1 regs2 mem2 RGBA_STK sp0 FPF L A mem0 md0 Lc1 Ac1 md2 res p N fdp sp _ HJ2 ltac:(lia) ltac:(lia) Hal16
ltac:(rewrite (REGS 2%bv ltac:(inl)); exact G2) R10 ltac:(rewrite HNS in B1; lia) ltac:(rewrite (REGS 25%bv ltac:(inl)); exact G25) ltac:(lia)
ltac:(rewrite (REGS 27%bv ltac:(inl)); exact G27) ltac:(lia) S962 ltac:(lia) Vn).
intros regs3 mem3 HJ3 W8 W80 Wnl W56 W72 FR3 R9 R29 R14 R15 R16 R18 R19 R22 R23 K3.
assert (STAT3 : cr_statics mem3).
{ apply (statics_kept0 mem2 mem3 STAT2).
- intros x Hx. apply FR3; lia.
- intros b n0 Hb i0 Hi0. pose proof (SBs_in_SB _ Hb) as Hb'. assert (Hbb : In (b, n0) (blocks Lc Ac)) by (apply (blocks_of_perm Lc Ac _ _ HB0); left; exact Hb').
destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n0 i0 HH Hbb Hi0) as (_ & B2 & B3 & _). apply FR3; lia.
- exact W8. }
apply (CL_loop 510%nat fx1 regs3 Lc1 Ac1 mem3 md2 (cinit E0) [nd0]); [cbn; lia | | exact KDONE | exact KFAIL].
unfold at_CL, cinit. cbn [c_E c_ns c_q].
assert (HL1 : nleaves [mkN 0 (elen E0 - 1) true 0 None None 0 0 E0] = 1) by reflexivity. rewrite HL1.
assert (Hm1 : elen [mkN 0 (elen E0 - 1) true 0 None None 0 0 E0] = 1) by reflexivity. rewrite Hm1.
assert (Ht0 : tnth [nd0] 0 = nd0) by reflexivity.
assert (Hzs : E0 = zsub E0 0 (cnt - 1)).
{ unfold zsub. rewrite Z.sub_0_r. replace (cnt - 1 + 1) with (elen E0) by lia. unfold elen. rewrite Nat2Z.id. cbn [Z.to_nat skipn]. symmetry. apply firstn_all. }
assert (TF0 : tn_facts nd0 (mkN 0 (elen E0 - 1) true 0 None None 0 0 E0)).
{ apply (tn_facts_intro (pal_bytes E0 ++ tail) E0 0 (cnt - 1) nd0 (mkN 0 (elen E0 - 1) true 0 None None 0 0 E0) (pal_agrees_app E0 tail) HE0ok HE0nd ltac:(lia) ltac:(lia) ltac:(lia) eq_refl
ltac:(cbn [n_hi]; lia) Hzs (proj1 Hwf0) Hq0 Hdim0). }
split; [apply (rgba_inv_kept Lc1 Ac1 mem2 md2 Lc1 Ac1 mem3 md2 RINV2 HJ3 Hinit2); intros x Hx; apply FR3; lia|].
split; [exact Hfrm2|]. split; [rewrite <- HlenE0 at 1; apply cinit_inv; lia|]. split; [lia|].
split. { split.
- split; [split; [rewrite (K3 2%bv ltac:(inl)), (REGS 2%bv ltac:(inl)); exact G2 | split; [rewrite (K3 3%bv ltac:(inl)), (REGS 3%bv ltac:(inl)); exact G3 | rewrite (K3 4%bv ltac:(inl)), (REGS 4%bv ltac:(inl)); exact G4]]|].
split; [exact R9|]. split; [exact R22|]. split; [exact R23|]. split; [exact R18|]. split; [exact R19|].
split; [rewrite (K3 8%bv ltac:(inl)), (REGS 8%bv ltac:(inl)); exact Gr|]. split; [rewrite (K3 20%bv ltac:(inl)), (REGS 20%bv ltac:(inl)); exact Gc|].
split; [rewrite (K3 25%bv ltac:(inl)), (REGS 25%bv ltac:(inl)); exact G25|]. split; [rewrite (K3 24%bv ltac:(inl)), (REGS 24%bv ltac:(inl)); exact G24|].
rewrite (K3 21%bv ltac:(inl)), (REGS 21%bv ltac:(inl)). exact G21.
- split; [exact R29 | exact (conj R14 (conj R15 R16))]. }
split; [exact STAT3|]. split; [rewrite Ht0, Ha0; exact (conj W56 (conj W72 W80))|].
split; [eapply arr8_frame; [exact Hpa2 | intros x Hx; rewrite zlen_app_pal, HlenE0 in Hx; apply FR3; lia]|].
split; [eapply arr32_frame; [exact Hfa2 | intros x Hx; rewrite zlen_fr_vals, HlenE0 in Hx; apply FR3; lia]|].
split; [eapply val_mem_frame; [exact Vn | intros i0 Hi0; apply FR3; lia]|].
split.
{ split; [reflexivity|]. split.
- intros j Hj. assert (j = 0) as -> by lia. rewrite Ht0. split.
+ unfold node_mem. cbn [node znth Z.to_nat nth n_leaf]. rewrite Ht0. destruct Tobj0 as (d0 & d1 & Hobj). exists d0, d1.
eapply obj_at_transport_range; [exact Hobj | apply (proj1 lay_inside_Node) |]. intros i0 Hi0. rewrite Ha0. apply FR3; rewrite <- ?Ha0; lia.
+ cbn [node znth Z.to_nat nth]. split; [exact Him0|]. split; [cbn [n_hi]; rewrite Hix0, HlenE0; reflexivity|]. split; [exact Hc0|]. split; [exact Hwf0 | exact Tnz0].
- split.
+ intros j Hj. assert (j = 0) as -> by lia. rewrite Ht0, Ha0. replace (sp + 936 + 8 * 0) with (sp + 936) by lia. exact Wnl.
+ split.
* intros j blc i0 Hj Hb Hi0. assert (j = 0) as -> by lia. rewrite Ht0, Ha0 in Hb |- *. apply Hwb0; [exact Hb | exact Hi0].
* intros j Hj. assert (j = 0) as -> by lia. rewrite Ht0.
exact (means_of_facts nd0 _ E0 0 (cnt - 1) TF0 HE0ok ltac:(lia) ltac:(lia) Hzs (proj1 (proj2 (proj2 (proj2 (proj2 Hwf0)))))). }
split.
{ intros j Hj. assert (j = 0) as -> by lia. rewrite Ht0. cbn [node znth Z.to_nat nth]. exact TF0. }
change (node_blocks [nd0] 1) with [(tn_addr (tnth [nd0] 0), NODE_SIZE)]. rewrite Ht0, Hbl1. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
rewrite Ha0, <- Hbl2. eapply Permutation_trans; [apply perm_skip; exact HB|]. apply Permutation_cons_append.
Qed.
End h.
Lemma zlen_le_zsum : forall l, (forall i, 0 <= i < zlen l -> 1 <= getz l i) -> zlen l <= zsum l.
Proof.
induction l as [|x l IH]; intros Hall; [unfold zlen; cbn [zsum length Z.of_nat]; lia|].
change (zsum (x :: l)) with (x + zsum l). replace (zlen (x :: l)) with (zlen l + 1) in * by (unfold zlen; cbn [length]; lia).
pose proof (Hall 0 ltac:(unfold zlen; lia)) as H0. change (1 <= x) in H0.
assert (IH' : zlen l <= zsum l).
{ apply IH. intros i Hi. pose proof (Hall (i + 1) ltac:(lia)) as Hi1. unfold getz in Hi1 |- *. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hi1 by lia. exact Hi1. }
lia.
Qed.
Lemma not_entry_block : forall Lc Ac memc mdc (X : list (Z * Z)) b,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (BASE r g N img fmt rest s bef beffmt ++ X) ->
Permutation (blocks L A) (BASE r g N img fmt rest s bef beffmt) -> In b X -> 0 < snd b -> ~ In b (blocks L A).
Proof.
intros Lc Ac memc mdc X b HH HP HP0 Hin Hsz Hb.
assert (Hb' : In b (BASE r g N img fmt rest s bef beffmt)) by (eapply Permutation_in; [exact HP0 | exact Hb]).
destruct (in_split _ _ Hb') as (l1 & l2 & E12). rewrite E12 in HP.
assert (HP' : Permutation (blocks Lc Ac) (b :: (l1 ++ l2) ++ X)).
{ eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. rewrite <- app_assoc. apply (Permutation_middle (l1) (l2 ++ X) b). }
pose proof (heap_sep_perm ubs2_msyms MR LAWS Lc Ac memc mdc b _ b HH HP' ltac:(apply in_app_iff; right; exact Hin)) as S1. lia.
Qed.
Theorem ubs2_rgbadd_CR : seg_CR API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KQT KXD KXT fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp fdl pal Hfrm HAT.
destruct HAT as (HINV & RR & Hfmt & HN1 & Hha & G14 & G25 & G24 & Gc & G18 & G27 & Gr & G21 & Ssm & Ssq & S96 & Sfc & Sro & Scg & Sim & CHT & DEN & Z1 & Z2 & Z3 & HB).
destruct CHT as (Sch & Hpa & Hzl & HTc & H4096). destruct DEN as (Hfa & Hfdl & H256 & H3 & Hf1 & Hsum & Hdist).
pose proof HINV as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _ & HBent). pose proof (proj1 HJ) as HH.
assert (H3' : 3 * cnt <= 3 * ch_T C) by (rewrite <- Hzl; exact H3).
assert (Hcnt : 256 <= cnt /\ cnt <= RGB_NMAX).
{ split; [exact H256|]. rewrite <- Hfdl. pose proof (zlen_le_zsum fdl ltac:(rewrite Hfdl; exact Hf1)). lia. }
assert (HE0 : ent_ok (ents_of pal fdl cnt) /\ List.NoDup (map fst (ents_of pal fdl cnt)) /\ zsum (fr_vals (ents_of pal fdl cnt)) <= N).
{ split; [| split].
- apply ent_ok_ents_of; [lia | | exact Hf1]. intros x Hx. exact (proj2 (arr8_getz ubs2segs memc (ch_p C) pal x Hpa ltac:(lia))).
- apply NoDup_ents_of. exact Hdist.
- rewrite fr_vals_ents_of by lia. exact Hsum. }
assert (Htmp : ~ In (ch_p C, 3 * ch_T C) (blocks L A) /\ ~ In (fdp, 4 * cnt) (blocks L A)).
{ split.
- eapply (not_entry_block Lc Ac memc mdc _ _ HH HB HBent); [| cbn]. { apply in_app_iff. right. apply in_app_iff. left. unfold cht_blks, cht_blocks. cbn [In]. tauto. }
clear -H3 H256 Hzl. lia.
- eapply (not_entry_block Lc Ac memc mdc _ _ HH HB HBent); [| cbn; lia]. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
eapply CR_main with (ha := ha) (pnew := pnew) (fimg := fimg) (imgl := imgl) (C := C) (cnt := cnt) (fdp := fdp) (fdl := fdl) (pal0 := pal).
all: first [eassumption | exact (conj Hzl H3') | exact (conj Z1 (conj Z2 Z3)) | exact (conj HTc H4096) |
exact (conj Ssm (conj Ssq (conj Sfc (conj Sro (conj Scg (conj Sim Sch)))))) |
(eapply QT_pack with (ha := ha) (pnew := pnew) (fimg := fimg) (imgl := imgl) (C := C) (cnt := cnt) (fdp := fdp) (fdl := fdl) (pal0 := pal);
first [eassumption | exact (conj Hzl H3') | exact (conj Z1 (conj Z2 Z3)) | exact (conj HTc H4096)]) |
(eapply XT_pack with (ha := ha) (pnew := pnew) (fimg := fimg) (imgl := imgl) (C := C) (cnt := cnt) (fdp := fdp) (fdl := fdl) (pal0 := pal);
first [eassumption | exact (conj Hzl H3') | exact (conj Z1 (conj Z2 Z3)) | exact (conj HTc H4096)]) |
(eapply XD_pack with (ha := ha) (pnew := pnew) (fimg := fimg) (imgl := imgl) (C := C) (cnt := cnt) (fdp := fdp) (pal0 := pal);
first [eassumption | exact (conj Hzl H3') | exact (conj Z1 (conj Z2 Z3)) | exact (conj HTc H4096)])].
Qed.
End e.
End d.
