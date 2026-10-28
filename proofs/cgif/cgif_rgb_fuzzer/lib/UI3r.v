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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x UI56 UI1h YP14 YI08 YI0c YI0f UI3h UI4v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_S1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xf00).
Definition PC_S2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xf28).
Definition PC_S3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xf48).
Definition PC_CL' : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xd2c).
Definition PC_R1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xcd8).
Definition PC_PR' : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xd58).
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Lemma in_bv5'' : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst. exact Hin. Qed.
Ltac inl := apply in_bv5''; vm_compute; reflexivity.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := ubs2segs (only parsing).
Local Notation rom := (seg_rom ubs2segs) (only parsing).
Section J.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition ss_S1 : sstate :=
mkSS PC_S1 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 40 51 50 51 [mkChunk 40 (CVal 4 (SOff 33 0)); mkChunk 49 (CVal 1 (SOff 32 0)); mkChunk 50 (CVal 1 (SLit 1))];
YQ0b.mkRegion (Some 2%nat) 934 936 934 936 [mkChunk 934 (CVal 2 (SOff 29 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (26%nat, mkAF 1 (2^30) 0); (29%nat, mkAF 1 254 0); (33%nat, mkAF 0 (2^30) 0);
(27%nat, mkAF 0 (2^48) 3); (32%nat, mkAF 0 255 0) ] [] []).
Definition S1_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29]%bv.
Lemma S1_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a i lo Lf cidx sp : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i -> val_mem segs mem (a + 40) 4 lo ->
getr regs 29 = Z_to_bv 64 Lf ->
1 <= i < 2 ^ 30 -> 0 <= lo < 2 ^ 30 -> 1 <= Lf <= 254 -> 0 <= cidx < 256 ->
val_mem segs mem (a + 49) 1 cidx -> val_mem segs mem (a + 50) 1 1 -> val_mem segs mem (sp + 934) 2 Lf ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (a + 50) 1 0 -> val_mem segs mem' (sp + 934) 2 (Lf - 1) ->
(forall x, 0 <= x < 2 ^ 64 -> x <> a + 50 -> ~ (sp + 934 <= x < sp + 936) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 1 = Z_to_bv 64 PC_S2 -> getr regs' 10 = getr regs 25 -> getr regs' 11 = getr regs 24 -> getr regs' 12 = Z_to_bv 64 (sp + 934) ->
getr regs' 13 = Z_to_bv 64 lo -> getr regs' 14 = Z_to_bv 64 (i - 1) -> getr regs' 15 = Z_to_bv 64 cidx ->
(forall r : reg, In r S1_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 ubs2_A_new_tree_node) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S1) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a i lo Lf cidx sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr9 Vlo Hr29 Hi Hlo HLf Hcidx Vcidx Vleaf Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & _).
set (E := Ereg regs (map (Z_to_bv 64) [cidx; lo] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 cidx) by (subst E; apply (Ereg_vals regs [cidx; lo] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [cidx; lo] [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 26) = i) by (rewrite (HE 26%nat 26%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU29 : bv_unsigned (ew E 29) = Lf) by (rewrite (HE 29%nat 29%bv eq_refl), Hr29; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = lo) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = cidx) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_S1 (@mkst fy regs (Z_to_bv 64 PC_S1) mem rom)).
{ unfold ss_S1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | exact Vlo].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vcidx].
* eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact Vleaf].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU29; reflexivity | cbn; lia | cbn; lia | exact Vnln].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU9, HU29, HU33, HU18, HU32. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (_ & _ & Ha16).
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S1) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_new_tree_node.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_byte E ssf ms 0%nat _ 27%nat 50 (SLit 0) a 0 HS eq_refl eq_refl ltac:(cbn; tauto) HU18 eq_refl ltac:(lia)) as Mleaf;
pose proof (st_chunk_val segs E ssf ms 1%nat _ 2%nat 934 2%N (SOff 29 (-1)) sp (Lf - 1) HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite HU29; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mnln
end.
change (N.to_nat 2) with 2%nat in Mnln.
apply HK.
- exact HJ.
- apply val_mem_1; [exact Mleaf | lia].
- exact Mnln.
- intros x Hx Hn1 Hn2. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU18; lia). reflexivity.
- jreg HS (1%bv:reg) as Hq; exact Hq.
- jreg HS (10%bv:reg) as Hq; rewrite Hq; exact (HE 25%nat 25%bv eq_refl).
- jreg HS (11%bv:reg) as Hq; rewrite Hq; exact (HE 24%nat 24%bv eq_refl).
- jreg HS (12%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- jreg HS (13%bv:reg) as Hq; rewrite Hq; exact A33.
- jreg HS (14%bv:reg) as Hq; rewrite Hq, (HE 26%nat 26%bv eq_refl), Hr9, unsigned_lit_small by lia. replace (i - 1) with (i + -1) by lia. reflexivity.
- jreg HS (15%bv:reg) as Hq; rewrite Hq; exact A32.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ S1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_S2 : sstate :=
mkSS PC_S2 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 0 8 0 8 [];
YQ0b.mkRegion (Some 27%nat) 44 48 0 0 [mkChunk 44 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 2%nat) 934 936 0 0 [mkChunk 934 (CVal 2 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (26%nat, mkAF 1 (2^30) 0); (27%nat, mkAF 0 (2^48) 3); (32%nat, mkAF 0 (2^30) 0); (33%nat, mkAF 0 255 0) ] [] []).
Definition S2_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29]%bv.
Lemma S2_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a i hi n1 res0 sp : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i -> getr regs 10 = Z_to_bv 64 res0 ->
1 <= i < 2 ^ 30 -> 0 <= hi < 2 ^ 30 -> 0 <= n1 <= 254 -> 0 <= res0 < 2 ^ 64 ->
val_mem segs mem (a + 44) 4 hi -> val_mem segs mem (sp + 934) 2 n1 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' a 8 res0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + 8) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 1 = Z_to_bv 64 PC_S3 -> getr regs' 10 = getr regs 25 -> getr regs' 11 = getr regs 24 -> getr regs' 12 = Z_to_bv 64 (sp + 934) ->
getr regs' 13 = Z_to_bv 64 i -> getr regs' 14 = Z_to_bv 64 hi -> getr regs' 15 = Z_to_bv 64 n1 ->
(forall r : reg, In r S2_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 ubs2_A_new_tree_node) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S2) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a i hi n1 res0 sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr9 Hr10 Hi Hhi Hn1 Hres0 Vhi Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
set (E := Ereg regs (map (Z_to_bv 64) [hi; n1] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 hi) by (subst E; apply (Ereg_vals regs [hi; n1] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 n1) by (subst E; apply (Ereg_vals regs [hi; n1] [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 26) = i) by (rewrite (HE 26%nat 26%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res0) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = hi) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = n1) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_S2 (@mkst fy regs (Z_to_bv 64 PC_S2) mem rom)).
{ unfold ss_S2. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vhi].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | exact Vnln].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU9, HU18, HU32, HU33. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S2) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_new_tree_node.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 27%nat 0 8%N (SOff 10 0) a res0 HS eq_refl eq_refl ltac:(cbn; tauto) HU18
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mc0
end.
change (N.to_nat 8) with 8%nat in Mc0. rewrite Z.add_0_r in Mc0.
apply HK.
- exact HJ.
- exact Mc0.
- intros x Hx Hn1'. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU18; lia). reflexivity.
- jreg HS (1%bv:reg) as Hq; exact Hq.
- jreg HS (10%bv:reg) as Hq; rewrite Hq; exact (HE 25%nat 25%bv eq_refl).
- jreg HS (11%bv:reg) as Hq; rewrite Hq; exact (HE 24%nat 24%bv eq_refl).
- jreg HS (12%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- jreg HS (13%bv:reg) as Hq; rewrite Hq, (HE 26%nat 26%bv eq_refl); exact Hr9.
- jreg HS (14%bv:reg) as Hq; rewrite Hq; exact A32.
- jreg HS (15%bv:reg) as Hq; rewrite Hq; exact A33.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ S2_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition s3_aliases : list (sv * sv) :=
[(SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 1)) (SLit (-3)), SOff 36%nat 0);
(SAlu ALU_ADD (SOff 2 936) (SAlu ALU_SLL (SOff 36 0) (SLit 3)), SOff 34%nat 0)].
Definition ss_S3c (c : acond) : sstate :=
mkSS PC_S3 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 0 16 8 16 [mkChunk 0 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 2%nat) 72 80 0 0 [mkChunk 72 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 2%nat) 934 936 0 0 [mkChunk 934 (CVal 2 (SOff 33 0))];
YQ0b.mkRegion (Some 34%nat) 0 16 0 16 [] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (10%nat, mkAF 1 (2^63) 0); (27%nat, mkAF 0 (2^48) 3); (9%nat, mkAF 0 (2^16) 0);
(32%nat, mkAF 1 (2^63) 0); (33%nat, mkAF 2 255 0); (34%nat, mkAF 0 (2^63) 3); (35%nat, mkAF (2^63 - 1) (2^64 - 1) 0);
(36%nat, mkAF 1 507 0) ] [c] s3_aliases).
Definition ss_S3L : sstate := ss_S3c (mkAC BC_LTU (SOff 33%nat 0) (SLit 255)).
Definition ss_S3Q : sstate := ss_S3c (mkAC BC_GEU (SOff 33%nat 0) (SLit 255)).
Definition S3_KEEP : list reg := [2; 3; 4; 8; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma S3_entry : forall (fy : FPState) (regs : bvmap 5 word) mem Lc Ac md (c : acond) (a q n2 res0 res1 sp STK sp0 : Z),
heap_ok MR Lc Ac mem md -> In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 -> alloc_ceiling + STK <= sp0 -> sp0 < 2 ^ 63 ->
(forall x, sp0 - STK <= x < sp0 -> writable_at segs mem x) ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> getr regs 9 = Z_to_bv 64 q ->
0 <= q < 2 ^ 16 -> 2 <= n2 <= 255 -> 1 <= res0 < 2 ^ 63 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 res0 -> val_mem segs mem (sp + 934) 2 n2 -> word_mem segs mem (sp + 72) (2 ^ 64 - 1 - (sp + 936)) ->
let E := Ereg regs (map (Z_to_bv 64) [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] ++ []) in
acond_ok E c ->
@st_ok segs fy E (ss_S3c c) (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
ew E 32 = Z_to_bv 64 res0 /\ ew E 33 = Z_to_bv 64 n2 /\ ew E 34 = Z_to_bv 64 (sp + 912 + 16 * n2) /\
bv_unsigned (ew E 2) = sp /\ bv_unsigned (ew E 10) = res1 /\ bv_unsigned (ew E 27) = a /\ bv_unsigned (ew E 34) = sp + 912 + 16 * n2 /\
bv_unsigned (ew E 32) = res0.
Proof.
intros fy regs mem Lc Ac md c a q n2 res0 res1 sp STK sp0 HH Hain Hwlo Hwhi Hal16 Hst0 H63 Hstw Hr2 Hr18 Hr10 Hr9 Hq Hn2 Hres0 Hres1 Vc0 Vnln V72 E Hc.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 res0) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 n2) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 (sp + 912 + 16 * n2)) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 (2 ^ 64 - 1 - (sp + 936))) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 3%nat); reflexivity).
assert (A36 : ew E 36 = Z_to_bv 64 (2 * n2 - 3)) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 4%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res1) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = q) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = res0) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = n2) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = sp + 912 + 16 * n2) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = 2 ^ 64 - 1 - (sp + 936)) by (rewrite A35; apply unsigned_lit_small; lia).
assert (HU36 : bv_unsigned (ew E 36) = 2 * n2 - 3) by (rewrite A36; apply unsigned_lit_small; lia).
split; [| repeat (split; [assumption|]); exact HU32].
unfold ss_S3c. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc0].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU35; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact V72].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | exact Vnln].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia| apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18, HU34. repeat split; lia.
- split; [|split; [split; [exact Hc | exact I] |]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU18, HU9, HU32, HU33, HU34, HU35, HU36. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
assert ((sp + 912 + 16 * n2) mod 8 = 0).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 912 + 16 * n2) with ((2 * (sp / 16) + 114 + 2 * n2) * 8) by lia. apply Z.mod_mul. lia. }
repeat split; lia.
+ cbn [f_alias alias_ok s3_aliases]. repeat split.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit, HU33, HU36, !Z.add_0_r.
rewrite (zcanon_id n2) by (unfold M64; lia). change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (n2 * 2)), (zcanon_id (2 * n2 - 3)) by (unfold M64; lia). unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
replace (n2 * 2 + -3) with (2 * n2 - 3) by lia. apply Z.mod_small. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU2, HU36, HU34, !Z.add_0_r.
rewrite (zcanon_id (sp + 936)), (zcanon_id (2 * n2 - 3)) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 3) with 8. rewrite (zcanon_id ((2 * n2 - 3) * 8)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Definition S3_post (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (a q n2 res0 res1 sp : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md /\
val_mem segs mem' (a + 8) 8 res1 /\ word_mem segs mem' (sp + 912 + 16 * n2) res0 /\ word_mem segs mem' (sp + 920 + 16 * n2) res1 /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> ~ (sp + 912 + 16 * n2 <= x < sp + 928 + 16 * n2) -> mbyte segs mem' x = mbyte segs mem x) /\
getr regs' 9 = Z_to_bv 64 (q + 1) /\ getr regs' 29 = Z_to_bv 64 n2 /\ getr regs' 14 = Z_to_bv 64 (sp + 936) /\
getr regs' 15 = Z_to_bv 64 512 /\ getr regs' 16 = Z_to_bv 64 255 /\
(forall r : reg, In r S3_KEEP -> getr regs' r = getr regs r).
Lemma S3_loop : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a q n2 res0 res1 sp : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> getr regs 9 = Z_to_bv 64 q ->
0 <= q < 2 ^ 16 -> 2 <= n2 < 255 -> 1 <= res0 < 2 ^ 63 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 res0 -> val_mem segs mem (sp + 934) 2 n2 -> word_mem segs mem (sp + 72) (2 ^ 64 - 1 - (sp + 936)) ->
(forall regs' mem', S3_post regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp regs' mem' ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_CL') mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr10 Hr9 Hq Hn2 Hres0 Hres1 Vc0 Vnln V72 HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (S3_entry fy regs mem Lc Ac md (mkAC BC_LTU (SOff 33%nat 0) (SLit 255)) a q n2 res0 res1 sp STK sp0 HH Hain Hwlo Hwhi Hal16 Hceil H63 Hstw
Hr2 Hr18 Hr10 Hr9 Hq ltac:(lia) Hres0 Hres1 Vc0 Vnln V72) as (HS & HE & A32 & A33 & A34 & HU2 & HU10 & HU18 & HU34 & HU32).
{ unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (U_atom _ 33 n2), U_SLit; [| apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 1%nat); reflexivity | lia].
change (zcanon 255) with 255. apply Z.ltb_lt. lia. }
set (E := Ereg regs _) in HS, HE, A32, A33, A34, HU2, HU10, HU18, HU34, HU32. change (ss_S3c _) with ss_S3L in HS.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_CL'.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 34); [reflexivity | exact HU34 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc ss_S3L ss_S3Q ss_S3c].
apply HK. unfold S3_post. split; [exact HJ|].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 27%nat 8 8%N (SOff 10 0) a res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU18
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mc1;
pose proof (st_chunk_val segs E ssf ms 3%nat _ 34%nat 0 8%N (SOff 32 0) (sp + 912 + 16 * n2) res0 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn0;
pose proof (st_chunk_val segs E ssf ms 3%nat _ 34%nat 8 8%N (SOff 10 0) (sp + 912 + 16 * n2) res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn1;
change (N.to_nat 8) with 8%nat in Mc1, Mn0, Mn1; rewrite Z.add_0_r in Mn0; replace (sp + 912 + 16 * n2 + 8) with (sp + 920 + 16 * n2) in Mn1 by lia;
split; [exact Mc1|]; split; [apply val_mem_word_mem; exact Mn0|]; split; [apply val_mem_word_mem; exact Mn1|];
split; [intros x Hx Hn1' Hn2'; mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU18, ?HU34; lia); reflexivity|];
split; [jreg HS (9%bv:reg) as Hq9; rewrite Hq9, (HE 9%nat 9%bv eq_refl), Hr9, unsigned_lit_small by lia; reflexivity|];
split; [jreg HS (29%bv:reg) as Hq29; rewrite Hq29; exact A33|];
split; [jreg HS (14%bv:reg) as Hq14; rewrite Hq14, HU2; reflexivity|];
split; [jreg HS (15%bv:reg) as Hq15; exact Hq15|];
split; [jreg HS (16%bv:reg) as Hq16; exact Hq16|];
exact (regs_kept_of_st_ok _ _ _ _ regs _ S3_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))
end.
Qed.
Lemma S3_exit : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a q n2 res0 res1 sp : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> getr regs 9 = Z_to_bv 64 q ->
0 <= q < 2 ^ 16 -> n2 = 255 -> 1 <= res0 < 2 ^ 63 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 res0 -> val_mem segs mem (sp + 934) 2 n2 -> word_mem segs mem (sp + 72) (2 ^ 64 - 1 - (sp + 936)) ->
(forall regs' mem', S3_post regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp regs' mem' ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_QT) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr10 Hr9 Hq Hn2 Hres0 Hres1 Vc0 Vnln V72 HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (S3_entry fy regs mem Lc Ac md (mkAC BC_GEU (SOff 33%nat 0) (SLit 255)) a q n2 res0 res1 sp STK sp0 HH Hain Hwlo Hwhi Hal16 Hceil H63 Hstw
Hr2 Hr18 Hr10 Hr9 Hq ltac:(lia) Hres0 Hres1 Vc0 Vnln V72) as (HS & HE & A32 & A33 & A34 & HU2 & HU10 & HU18 & HU34 & HU32).
{ unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (U_atom _ 33 n2), U_SLit; [| apply (Ereg_vals regs [res0; n2; sp + 912 + 16 * n2; 2 ^ 64 - 1 - (sp + 936); 2 * n2 - 3] [] 1%nat); reflexivity | lia].
change (zcanon 255) with 255. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
set (E := Ereg regs _) in HS, HE, A32, A33, A34, HU2, HU10, HU18, HU34, HU32. change (ss_S3c _) with ss_S3Q in HS.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_QT.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 34); [reflexivity | exact HU34 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc ss_S3L ss_S3Q ss_S3c].
apply HK. unfold S3_post. split; [exact HJ|].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 27%nat 8 8%N (SOff 10 0) a res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU18
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mc1;
pose proof (st_chunk_val segs E ssf ms 3%nat _ 34%nat 0 8%N (SOff 32 0) (sp + 912 + 16 * n2) res0 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn0;
pose proof (st_chunk_val segs E ssf ms 3%nat _ 34%nat 8 8%N (SOff 10 0) (sp + 912 + 16 * n2) res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn1;
change (N.to_nat 8) with 8%nat in Mc1, Mn0, Mn1; rewrite Z.add_0_r in Mn0; replace (sp + 912 + 16 * n2 + 8) with (sp + 920 + 16 * n2) in Mn1 by lia;
split; [exact Mc1|]; split; [apply val_mem_word_mem; exact Mn0|]; split; [apply val_mem_word_mem; exact Mn1|];
split; [intros x Hx Hn1' Hn2'; mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU18, ?HU34; lia); reflexivity|];
split; [jreg HS (9%bv:reg) as Hq9; rewrite Hq9, (HE 9%nat 9%bv eq_refl), Hr9, unsigned_lit_small by lia; reflexivity|];
split; [jreg HS (29%bv:reg) as Hq29; rewrite Hq29; exact A33|];
split; [jreg HS (14%bv:reg) as Hq14; rewrite Hq14, HU2; reflexivity|];
split; [jreg HS (15%bv:reg) as Hq15; exact Hq15|];
split; [jreg HS (16%bv:reg) as Hq16; exact Hq16|];
exact (regs_kept_of_st_ok _ _ _ _ regs _ S3_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))
end.
Qed.
Definition SF_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29]%bv.
Definition ss_SF1 : sstate :=
mkSS PC_S3 (sr_set sr_atoms 10%bv (SLit 0))
[ YQ0b.mkRegion (Some 27%nat) 0 16 8 16 [mkChunk 0 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (27%nat, mkAF 0 (2^48) 3) ] [] []).
Lemma S3_fail1 : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (a res0 : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 0 ->
0 <= res0 < 2 ^ 64 -> val_mem segs mem a 8 res0 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (a + 8) 8 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> mbyte segs mem' x = mbyte segs mem x) ->
(forall r : reg, In r SF_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_XT) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a res0 Q HJ Hwb Hain Hr18 Hr10 Hres0 Vc0 HK.
pose proof HJ as (HH & _). pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
set (E := Ereg regs (map (Z_to_bv 64) [res0] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 res0) by (subst E; apply (Ereg_vals regs [res0] [] 0%nat); reflexivity).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = res0) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_SF1 (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)).
{ unfold ss_SF1. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr10].
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc0].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU18. change (2 ^ 3) with 8.
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
Ltac wr_sf1 Hwb Hain HNS HU18 a :=
wr_ok_eval; eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] | apply wr_ok_nil].
jrun LAWS ubs2tbl_ok HS HJ. { wr_sf1 Hwb Hain HNS HU18 a. }
cbn [ms_mem mkst] in HF, HJ.
jbranch ubs2tbl HS; clear Hc.
all: jrun_to LAWS ubs2tbl_ok HS HJ PC_XT; [wr_sf1 Hwb Hain HNS HU18 a |].
all: cbn [ms_mem mkst] in HF0, HJ.
all: rewrite (st_ok_mkst segs E _ _ HS eq_refl); cbn [ss_pc].
all: lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (st_chunk_val segs E ssf msf 0%nat _ 27%nat 8 8%N (SLit 0) a 0 HS eq_refl eq_refl ltac:(cbn; tauto) HU18 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Mc1
end.
all: change (N.to_nat 8) with 8%nat in Mc1.
all: apply HK; [exact HJ | exact Mc1 | | exact (regs_kept_of_st_ok _ _ _ _ regs _ SF_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))].
all: intros x Hx Hn; mb_frame_g HF0 ltac:(exact Hx) ltac:(rewrite ?HU18; lia); mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU18; lia); reflexivity.
Qed.
Definition ss_SF0 : sstate :=
mkSS PC_S3 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 0 16 8 16 [mkChunk 0 (CVal 8 (SLit 0))] ] None
(mkFacts [ (10%nat, mkAF 1 (2^63) 0); (27%nat, mkAF 0 (2^48) 3) ] [] []).
Lemma S3_fail0 : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (a res1 : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 0 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (a + 8) 8 res1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> mbyte segs mem' x = mbyte segs mem x) ->
(forall r : reg, In r SF_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_XT) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a res1 Q HJ Hwb Hain Hr18 Hr10 Hres1 Vc0 HK.
pose proof HJ as (HH & _). pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res1) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_SF0 (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)).
{ unfold ss_SF0. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc0].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU18, HU10. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_XT.
{ wr_ok_eval. eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 27%nat 8 8%N (SOff 10 0) a res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU18
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mc1
end.
change (N.to_nat 8) with 8%nat in Mc1.
apply HK; [exact HJ | exact Mc1 | | exact (regs_kept_of_st_ok _ _ _ _ regs _ SF_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))].
intros x Hx Hn. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU18; lia). reflexivity.
Qed.
End J.
Definition lh_alias : sv := SAlu ALU_ADD (SOff 2 936) (SAlu ALU_SLL (SOff 9 0) (SLit 3)).
Definition ss_LH (cs : list acond) : sstate :=
mkSS PC_CL' (sr_set (sr_set (sr_set sr_atoms 14%bv (SOff 2%nat 936)) 15%bv (SLit 512)) 16%bv (SLit 255))
[ YQ0b.mkRegion (Some 32%nat) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 33%nat) 40 48 0 0 [mkChunk 40 (CVal 4 (SOff 34 0)); mkChunk 44 (CVal 4 (SOff 35 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (29%nat, mkAF 1 254 0); (9%nat, mkAF 0 511 0); (32%nat, mkAF 0 (2^63) 3);
(33%nat, mkAF 4096 (2^63) 3); (34%nat, mkAF 0 (2^30) 0); (35%nat, mkAF 0 (2^30) 0) ] cs [(lh_alias, SOff 32%nat 0)]).
Definition LH_KEEP : list reg := [1; 2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 29]%bv.
Definition LHS_KEEP : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 29]%bv.
Lemma LH_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (cs : list acond) (q a lo hi sp Lf : Z),
getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 q -> getr regs 14 = Z_to_bv 64 (sp + 936) ->
getr regs 15 = Z_to_bv 64 512 -> getr regs 16 = Z_to_bv 64 255 -> getr regs 29 = Z_to_bv 64 Lf ->
0 <= sp -> sp + 5168 < 2 ^ 63 -> sp mod 16 = 0 -> 0 <= q < 512 -> 1 <= Lf <= 254 -> 4096 <= a -> a + 56 <= sp -> a mod 8 = 0 ->
0 <= lo < 2 ^ 30 -> 0 <= hi < 2 ^ 30 ->
word_mem segs mem (sp + 936 + 8 * q) a -> val_mem segs mem (a + 40) 4 lo -> val_mem segs mem (a + 44) 4 hi ->
let E := Ereg regs (map (Z_to_bv 64) [sp + 936 + 8 * q; a; lo; hi] ++ []) in
conds_ok E cs ->
@st_ok segs fy E (ss_LH cs) (@mkst fy regs (Z_to_bv 64 PC_CL') mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
ew E 33 = Z_to_bv 64 a /\ ew E 34 = Z_to_bv 64 lo /\ ew E 35 = Z_to_bv 64 hi /\ bv_unsigned (ew E 2) = sp.
Proof.
intros fy regs mem cs q a lo hi sp Lf Hr2 Hr9 Hr14 Hr15 Hr16 Hr29 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Hhi Wq Vlo Vhi E Hcs.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (sp + 936 + 8 * q)) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; hi] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 a) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; hi] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; hi] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 hi) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; hi] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU29 : bv_unsigned (ew E 29) = Lf) by (rewrite (HE 29%nat 29%bv eq_refl), Hr29; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = q) by (rewrite (HE 9%nat 9%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = sp + 936 + 8 * q) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = a) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = lo) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = hi) by (rewrite A35; apply unsigned_lit_small; lia).
split; [| split; [exact HE | split; [exact A33 | split; [exact A34 | split; [exact A35 | exact HU2]]]]].
unfold ss_LH. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
+ cbn [sv_denot]. rewrite HU2. exact Hr14.
+ cbn [sv_denot]. exact Hr15.
+ cbn [sv_denot]. exact Hr16.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wq].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | exact Vlo].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU35; reflexivity | cbn; lia | cbn; lia | exact Vhi].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33. repeat split; lia.
- split; [|split; [exact Hcs|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU29, HU9, HU32, HU33, HU34, HU35. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
assert ((sp + 936 + 8 * q) mod 8 = 0).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 936 + 8 * q) with ((2 * (sp / 16) + 117 + q) * 8) by lia. apply Z.mod_mul. lia. }
repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold lh_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU2, HU9, HU32, Z.add_0_r.
rewrite (zcanon_id (sp + 936)), (zcanon_id q) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 3) with 8. rewrite (zcanon_id (q * 8)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma LH_skip : forall (fy : FPState) (regs : bvmap 5 word) mem (q a lo sp Lf : Z),
getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 q -> getr regs 14 = Z_to_bv 64 (sp + 936) ->
getr regs 15 = Z_to_bv 64 512 -> getr regs 16 = Z_to_bv 64 255 -> getr regs 29 = Z_to_bv 64 Lf ->
0 <= sp -> sp + 5168 < 2 ^ 63 -> sp mod 16 = 0 -> 0 <= q < 512 -> 1 <= Lf <= 254 -> 4096 <= a -> a + 56 <= sp -> a mod 8 = 0 ->
0 <= lo < 2 ^ 30 ->
word_mem segs mem (sp + 936 + 8 * q) a -> val_mem segs mem (a + 40) 4 lo -> val_mem segs mem (a + 44) 4 lo ->
exists regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_CL') mem rom) (@mkst fy regs' (Z_to_bv 64 PC_CL') mem rom) /\
getr regs' 9 = Z_to_bv 64 (q + 1) /\ getr regs' 14 = Z_to_bv 64 (sp + 936) /\ getr regs' 15 = Z_to_bv 64 512 /\
getr regs' 16 = Z_to_bv 64 255 /\
(forall r : reg, In r LH_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem q a lo sp Lf Hr2 Hr9 Hr14 Hr15 Hr16 Hr29 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Wq Vlo Vhi.
set (E := Ereg regs (map (Z_to_bv 64) [sp + 936 + 8 * q; a; lo; lo] ++ [])).
assert (B34 : ew E 34 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; lo] [] 2%nat); reflexivity).
assert (B35 : ew E 35 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; lo] [] 3%nat); reflexivity).
destruct (LH_entry fy regs mem [mkAC BC_EQ (SOff 35%nat 0) (SOff 34%nat 0)] q a lo lo sp Lf Hr2 Hr9 Hr14 Hr15 Hr16 Hr29 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Hlo Wq Vlo Vhi)
as (HS & HE & A33 & A34 & A35 & HU2).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, !U_SOff. fold E. rewrite B34, B35. apply Z.eqb_eq. reflexivity. }
fold E in HS, HE, A33, A34, A35, HU2.
pure_to ubs2tbl_ok HS (ubs2_A_cgif_rgb_addframe + 4008).
pure_to ubs2tbl_ok HS PC_CL'.
exists regs1. split; [exact (msteps_trans _ _ _ _ Hms Hms0)|].
jreg HS (9%bv:reg) as Hq9. jreg HS (14%bv:reg) as Hq14. jreg HS (15%bv:reg) as Hq15. jreg HS (16%bv:reg) as Hq16.
cbn [ms_regs mkst] in Hq9, Hq14, Hq15, Hq16.
split; [rewrite Hq9, (HE 9%nat 9%bv eq_refl), Hr9, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Hq14, HU2; reflexivity|]. split; [exact Hq15|]. split; [exact Hq16|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ LH_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma LH_split : forall (fy : FPState) (regs : bvmap 5 word) mem (q a lo hi sp Lf : Z),
getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 q -> getr regs 14 = Z_to_bv 64 (sp + 936) ->
getr regs 15 = Z_to_bv 64 512 -> getr regs 16 = Z_to_bv 64 255 -> getr regs 29 = Z_to_bv 64 Lf ->
0 <= sp -> sp + 5168 < 2 ^ 63 -> sp mod 16 = 0 -> 0 <= q < 512 -> 1 <= Lf <= 254 -> 4096 <= a -> a + 56 <= sp -> a mod 8 = 0 ->
0 <= lo -> lo < hi -> hi < 2 ^ 30 ->
word_mem segs mem (sp + 936 + 8 * q) a -> val_mem segs mem (a + 40) 4 lo -> val_mem segs mem (a + 44) 4 hi ->
exists regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_CL') mem rom) (@mkst fy regs' (Z_to_bv 64 PC_PR') mem rom) /\
getr regs' 27 = Z_to_bv 64 a /\ getr regs' 26 = Z_to_bv 64 lo /\ getr regs' 11 = Z_to_bv 64 hi /\
(forall r : reg, In r LHS_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem q a lo hi sp Lf Hr2 Hr9 Hr14 Hr15 Hr16 Hr29 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Hlh Hhi Wq Vlo Vhi.
set (E := Ereg regs (map (Z_to_bv 64) [sp + 936 + 8 * q; a; lo; hi] ++ [])).
assert (B34 : ew E 34 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; hi] [] 2%nat); reflexivity).
assert (B35 : ew E 35 = Z_to_bv 64 hi) by (subst E; apply (Ereg_vals regs [sp + 936 + 8 * q; a; lo; hi] [] 3%nat); reflexivity).
destruct (LH_entry fy regs mem [mkAC BC_NE (SOff 35%nat 0) (SOff 34%nat 0); mkAC BC_LTU (SOff 34%nat 0) (SOff 35%nat 0)] q a lo hi sp Lf
Hr2 Hr9 Hr14 Hr15 Hr16 Hr29 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 ltac:(lia) ltac:(lia) Wq Vlo Vhi)
as (HS & HE & A33 & A34 & A35 & HU2).
{ cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, branch_ltu_U, !U_SOff. fold E. rewrite B34, B35.
rewrite !Z.add_0_r, !unsigned_lit_small by lia. rewrite !zcanon_id by (unfold M64; lia).
split; [apply Bool.negb_true_iff; apply Z.eqb_neq; lia|]. split; [apply Z.ltb_lt; lia | exact I]. }
fold E in HS, HE, A33, A34, A35, HU2.
pure_to ubs2tbl_ok HS PC_PR'.
exists regs0. split; [exact Hms|].
jreg HS (27%bv:reg) as Hq27. jreg HS (26%bv:reg) as Hq26. jreg HS (11%bv:reg) as Hq11.
cbn [ms_regs mkst] in Hq27, Hq26, Hq11.
split; [rewrite Hq27; exact A33|]. split; [rewrite Hq26; exact A34|]. split; [rewrite Hq11; exact A35|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ LHS_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Section J2.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition ss_R0 : sstate :=
mkSS PC_CR sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 934 936 934 936 [] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (14%nat, mkAF 0 (2^30) 0) ] [] []).
Definition R0_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma R0_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (cnt sp : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 14 = Z_to_bv 64 (cnt - 1)   -> 1 <= cnt < 2 ^ 30 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (sp + 934) 2 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp + 934 <= x < sp + 936) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 1 = Z_to_bv 64 PC_R1 -> getr regs' 10 = getr regs 25 -> getr regs' 11 = getr regs 24 -> getr regs' 12 = Z_to_bv 64 (sp + 934) ->
getr regs' 13 = Z_to_bv 64 0 -> getr regs' 14 = Z_to_bv 64 (cnt - 1) -> getr regs' 15 = Z_to_bv 64 0 ->
(forall r : reg, In r R0_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 ubs2_A_new_tree_node) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CR) mem rom) md) Q.
Proof using IMG LAWS.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md cnt sp Q HJ Hwlo Hwhi Hal16 Hr2 Hr9 Hcnt HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _). pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 14) = cnt - 1) by (rewrite (HE 14%nat 14%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_R0 (@mkst fy regs (Z_to_bv 64 PC_CR) mem rom)).
{ unfold ss_R0. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU9.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_CR) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_new_tree_node.
{ wr_ok_eval. eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 2%nat 934 2%N (SLit 0) sp 0 HS eq_refl eq_refl ltac:(cbn; tauto) HU2 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Mnln
end.
change (N.to_nat 2) with 2%nat in Mnln.
apply HK.
- exact HJ.
- exact Mnln.
- intros x Hx Hn. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2; lia). reflexivity.
- jreg HS (1%bv:reg) as Hq; exact Hq.
- jreg HS (10%bv:reg) as Hq; rewrite Hq; exact (HE 25%nat 25%bv eq_refl).
- jreg HS (11%bv:reg) as Hq; rewrite Hq; exact (HE 24%nat 24%bv eq_refl).
- jreg HS (12%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- jreg HS (13%bv:reg) as Hq; exact Hq.
- jreg HS (14%bv:reg) as Hq; rewrite Hq; exact (eq_trans (HE 14%nat 14%bv eq_refl) Hr9).
- jreg HS (15%bv:reg) as Hq; exact Hq.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ R0_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_R1 : sstate :=
mkSS PC_R1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 16 8 16 [];
YQ0b.mkRegion (Some 2%nat) 56 64 56 64 [];
YQ0b.mkRegion (Some 2%nat) 72 88 72 88 [];
YQ0b.mkRegion (Some 2%nat) 96 104 0 0 [mkChunk 96 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 2%nat) 934 944 936 944 [mkChunk 934 (CVal 2 (SLit 1))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (10%nat, mkAF 1 (2^63) 0); (25%nat, mkAF 1 (2^63) 0) ] [] []).
Definition R1_KEEP : list reg := [2; 3; 4; 8; 20; 21; 24; 25; 26; 27]%bv.
Lemma R1_ok : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (root p N fdp sp : Z) Q,
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
sp0 - STK <= sp -> sp + 5168 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 root -> 1 <= root < 2 ^ 63 ->
getr regs 25 = Z_to_bv 64 p -> 1 <= p < 2 ^ 63 -> getr regs 27 = Z_to_bv 64 N -> 0 <= N < 2 ^ 64 ->
word_mem segs mem (sp + 96) (2 ^ 64 - 1 - fdp) -> 0 <= fdp < 2 ^ 64 ->
val_mem segs mem (sp + 934) 2 1 ->
(forall regs' mem',
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
word_mem segs mem' (sp + 8) N -> word_mem segs mem' (sp + 80) root -> word_mem segs mem' (sp + 936) root ->
word_mem segs mem' (sp + 56) 1 -> word_mem segs mem' (sp + 72) (2 ^ 64 - 1 - (sp + 936)) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp + 8 <= x < sp + 16) -> ~ (sp + 56 <= x < sp + 64) -> ~ (sp + 72 <= x < sp + 88) ->
~ (sp + 936 <= x < sp + 944) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 9 = Z_to_bv 64 0 -> getr regs' 29 = Z_to_bv 64 1 -> getr regs' 14 = Z_to_bv 64 (sp + 936) ->
getr regs' 15 = Z_to_bv 64 512 -> getr regs' 16 = Z_to_bv 64 255 -> getr regs' 18 = Z_to_bv 64 (2 ^ 64 - 1 - fdp) ->
getr regs' 19 = Z_to_bv 64 2 -> getr regs' 22 = Z_to_bv 64 (sp + 5038) -> getr regs' 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
(forall r : reg, In r R1_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_CL') mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_R1) mem rom) md) Q.
Proof using IMG LAWS.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md root p nv fdp sp Q HJ Hwlo Hwhi Hal16 Hr2 Hr10 Hroot Hr25 Hp Hr27 Hnv W96 Hfdp Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _). pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs (map (Z_to_bv 64) [2 ^ 64 - 1 - fdp] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (2 ^ 64 - 1 - fdp)) by (subst E; apply (Ereg_vals regs [2 ^ 64 - 1 - fdp] [] 0%nat); reflexivity).
assert (A2 : ew E 2 = Z_to_bv 64 sp) by (rewrite (HE 2%nat 2%bv eq_refl); exact Hr2).
assert (A25 : ew E 25 = Z_to_bv 64 p) by (rewrite (HE 25%nat 25%bv eq_refl); exact Hr25).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite A2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = root) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU25 : bv_unsigned (ew E 25) = p) by (rewrite A25; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew E 27) = nv) by (rewrite (HE 27%nat 27%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = 2 ^ 64 - 1 - fdp) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_R1 (@mkst fy regs (Z_to_bv 64 PC_R1) mem rom)).
{ unfold ss_R1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
all: unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]; rewrite HU2.
all: split; [lia|]; split; [lia|]; split; [intros o Ho; apply Hstw; lia|].
all: try apply Forall_nil.
+ apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W96].
+ apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact Vnln].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite !HU2. repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU25.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_R1) mem rom)) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_CL'.
{ wr_ok_eval. repeat (eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |]). apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
apply HK.
- exact HJ.
- apply val_mem_word_mem. lazymatch type of HS with st_ok _ _ ?ssf _ =>
exact (st_chunk_val segs E ssf ms 0%nat _ 2%nat 8 8%N (SOff 27 0) sp nv HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU27; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) end.
- apply val_mem_word_mem. lazymatch type of HS with st_ok _ _ ?ssf _ =>
exact (st_chunk_val segs E ssf ms 2%nat _ 2%nat 80 8%N (SOff 10 0) sp root HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) end.
- apply val_mem_word_mem. lazymatch type of HS with st_ok _ _ ?ssf _ =>
exact (st_chunk_val segs E ssf ms 4%nat _ 2%nat 936 8%N (SOff 10 0) sp root HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) end.
- apply val_mem_word_mem. lazymatch type of HS with st_ok _ _ ?ssf _ =>
exact (st_chunk_val segs E ssf ms 1%nat _ 2%nat 56 8%N (SLit 1) sp 1 HS eq_refl eq_refl ltac:(cbn; tauto) HU2
eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end.
- apply val_mem_word_mem. lazymatch type of HS with st_ok _ _ ?ssf _ =>
exact (st_chunk_val segs E ssf ms 2%nat _ 2%nat 72 8%N (SAlu ALU_XOR (SOff 2 936) (SLit (-1))) sp (2 ^ 64 - 1 - (sp + 936)) HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(rewrite YQ0c.denot_lit_U, (YI01.U_not_off E 2 sp 936 A2 ltac:(lia) ltac:(lia)); reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) end.
- intros x Hx Hn1 Hn2 Hn3 Hn4. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2; lia). reflexivity.
- jreg HS (9%bv:reg) as Hq; exact Hq.
- jreg HS (29%bv:reg) as Hq; exact Hq.
- jreg HS (14%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- jreg HS (15%bv:reg) as Hq; exact Hq.
- jreg HS (16%bv:reg) as Hq; exact Hq.
- jreg HS (18%bv:reg) as Hq; rewrite Hq; exact A32.
- jreg HS (19%bv:reg) as Hq; exact Hq.
- jreg HS (22%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- pose proof (st_ok_reg _ E _ ms 23%bv HS) as Hq. eval_sr_get_in Hq. rewrite Hq, YQ0c.denot_lit_U, (YI01.U_not E 25 p A25 ltac:(lia)). reflexivity.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ R1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_R1f : sstate := mkSS PC_R1 (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
Lemma R1_fail : forall (fy : FPState) (regs : bvmap 5 word) mem md Q,
m_halted md = None -> m_vm_lazy md = [] ->
getr regs 10 = Z_to_bv 64 0 ->
(forall regs', (forall r : reg, In r R0_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_XD) mem rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_R1) mem rom) md) Q.
Proof using.
intros fy regs mem md Q Hh Hl Hr10 HK.
set (E := Ereg regs []).
assert (HS : @st_ok segs fy E ss_R1f (@mkst fy regs (Z_to_bv 64 PC_R1) mem rom)).
{ unfold ss_R1f. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr10].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [exact I | split; exact I]. }
pure_to ubs2tbl_ok HS PC_XD.
eapply (SR_msteps segs _ _ md _ Hh Hl Hms). apply HK.
exact (regs_kept_of_st_ok _ _ _ _ regs _ R0_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
End J2.
End b.
