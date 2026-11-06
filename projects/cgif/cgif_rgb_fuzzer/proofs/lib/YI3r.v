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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI07
YI1e YI1i YI0x YI56 YI1h YP14 YI08 YI0c YI0f YI3h YI4v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_S1 : Z := 0x13f00.
Definition PC_S2 : Z := 0x13f24.
Definition PC_S3 : Z := 0x13f44.
Definition PC_CL' : Z := 0x13dbc.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Lemma in_bv5'' : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst. exact Hin. Qed.
Ltac inl := apply in_bv5''; vm_compute; reflexivity.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := src2segs (only parsing).
Local Notation rom := (seg_rom src2segs) (only parsing).
Section J.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition ss_S1 : sstate :=
mkSS PC_S1 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 49 51 50 51 [mkChunk 49 (CVal 1 (SOff 32 0)); mkChunk 50 (CVal 1 (SLit 1))];
YQ0b.mkRegion (Some 2%nat) 926 928 926 928 [mkChunk 926 (CVal 2 (SOff 11 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (26%nat, mkAF 1 (2^30) 0); (11%nat, mkAF 1 254 0); (13%nat, mkAF 0 (2^30) 0);
(27%nat, mkAF 0 (2^48) 3); (32%nat, mkAF 0 255 0) ] [] []).
Definition S1_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma S1_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a i lo Lf cidx sp : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 lo ->
getr regs 11 = Z_to_bv 64 Lf ->
1 <= i < 2 ^ 30 -> 0 <= lo < 2 ^ 30 -> 1 <= Lf <= 254 -> 0 <= cidx < 256 ->
val_mem segs mem (a + 49) 1 cidx -> val_mem segs mem (a + 50) 1 1 -> val_mem segs mem (sp + 926) 2 Lf ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (a + 50) 1 0 -> val_mem segs mem' (sp + 926) 2 (Lf - 1) ->
(forall x, 0 <= x < 2 ^ 64 -> x <> a + 50 -> ~ (sp + 926 <= x < sp + 928) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 1 = Z_to_bv 64 PC_S2 -> getr regs' 10 = getr regs 25 -> getr regs' 11 = getr regs 24 -> getr regs' 12 = Z_to_bv 64 (sp + 926) ->
getr regs' 13 = Z_to_bv 64 lo -> getr regs' 14 = Z_to_bv 64 (i - 1) -> getr regs' 15 = Z_to_bv 64 cidx ->
(forall r : reg, In r S1_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 src2_A_new_tree_node) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S1) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a i lo Lf cidx sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr9 Hr13 Hr11 Hi Hlo HLf Hcidx Vcidx Vleaf Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & _).
set (E := Ereg regs (map (Z_to_bv 64) [cidx] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 cidx) by (subst E; apply (Ereg_vals regs [cidx] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 26) = i) by (rewrite (HE 26%nat 26%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = Lf) by (rewrite (HE 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (HU13 : bv_unsigned (ew E 13) = lo) by (rewrite (HE 13%nat 13%bv eq_refl), Hr13; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = cidx) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_S1 (@mkst fy regs (Z_to_bv 64 PC_S1) mem rom)).
{ unfold ss_S1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vcidx].
* eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact Vleaf].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU11; reflexivity | cbn; lia | cbn; lia | exact Vnln].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU9, HU11, HU13, HU18, HU32. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (_ & _ & Ha16).
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S1) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_new_tree_node.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_byte E ssf ms 0%nat _ 27%nat 50 (SLit 0) a 0 HS eq_refl eq_refl ltac:(cbn; tauto) HU18 eq_refl ltac:(lia)) as Mleaf;
pose proof (st_chunk_val segs E ssf ms 1%nat _ 2%nat 926 2%N (SOff 11 (-1)) sp (Lf - 1) HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite HU11; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mnln
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
- jreg HS (13%bv:reg) as Hq; rewrite Hq, (HE 13%nat 13%bv eq_refl); exact Hr13.
- jreg HS (14%bv:reg) as Hq; rewrite Hq, (HE 26%nat 26%bv eq_refl), Hr9, unsigned_lit_small by lia. replace (i - 1) with (i + -1) by lia. reflexivity.
- jreg HS (15%bv:reg) as Hq; rewrite Hq; exact A32.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ S1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_S2 : sstate :=
mkSS PC_S2 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 0 8 0 8 [];
YQ0b.mkRegion (Some 27%nat) 44 48 0 0 [mkChunk 44 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 2%nat) 926 928 0 0 [mkChunk 926 (CVal 2 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (26%nat, mkAF 1 (2^30) 0); (27%nat, mkAF 0 (2^48) 3); (32%nat, mkAF 0 (2^30) 0); (33%nat, mkAF 0 255 0) ] [] []).
Definition S2_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma S2_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a i hi n1 res0 sp : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i -> getr regs 10 = Z_to_bv 64 res0 ->
1 <= i < 2 ^ 30 -> 0 <= hi < 2 ^ 30 -> 0 <= n1 <= 254 -> 0 <= res0 < 2 ^ 64 ->
val_mem segs mem (a + 44) 4 hi -> val_mem segs mem (sp + 926) 2 n1 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' a 8 res0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + 8) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 1 = Z_to_bv 64 PC_S3 -> getr regs' 10 = getr regs 25 -> getr regs' 11 = getr regs 24 -> getr regs' 12 = Z_to_bv 64 (sp + 926) ->
getr regs' 13 = Z_to_bv 64 i -> getr regs' 14 = Z_to_bv 64 hi -> getr regs' 15 = Z_to_bv 64 n1 ->
(forall r : reg, In r S2_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 src2_A_new_tree_node) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S2) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a i hi n1 res0 sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr9 Hr10 Hi Hhi Hn1 Hres0 Vhi Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
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
intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))).
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
jrun_to LAWS src2tbl_ok HS HJ src2_A_new_tree_node.
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
[(SAlu ALU_ADD (SOff 2 904) (SAlu ALU_SLL (SOff 33 0) (SLit 4)), SOff 34%nat 0);
(SAlu ALU_ADD (SOff 2 912) (SAlu ALU_SLL (SOff 33 0) (SLit 4)), SOff 34%nat 8)].
Definition ss_S3c (c : acond) : sstate :=
mkSS PC_S3 sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 0 16 8 16 [mkChunk 0 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 2%nat) 926 928 0 0 [mkChunk 926 (CVal 2 (SOff 33 0))];
YQ0b.mkRegion (Some 34%nat) 0 16 0 16 [] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (10%nat, mkAF 1 (2^63) 0); (27%nat, mkAF 0 (2^48) 3); (19%nat, mkAF 0 (2^16) 0);
(32%nat, mkAF 1 (2^63) 0); (33%nat, mkAF 2 255 0); (34%nat, mkAF 0 (2^63) 3) ] [c] s3_aliases).
Definition ss_S3L : sstate := ss_S3c (mkAC BC_LTU (SOff 33%nat 0) (SLit 255)).
Definition ss_S3Q : sstate := ss_S3c (mkAC BC_GEU (SOff 33%nat 0) (SLit 255)).
Definition S3_KEEP : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma S3_entry : forall (fy : FPState) (regs : bvmap 5 word) mem Lc Ac md (c : acond) (a q n2 res0 res1 sp STK sp0 : Z),
heap_ok MR Lc Ac mem md -> In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 -> alloc_ceiling + STK <= sp0 -> sp0 < 2 ^ 63 ->
(forall x, sp0 - STK <= x < sp0 -> writable_at segs mem x) ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> getr regs 19 = Z_to_bv 64 q ->
0 <= q < 2 ^ 16 -> 2 <= n2 <= 255 -> 1 <= res0 < 2 ^ 63 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 res0 -> val_mem segs mem (sp + 926) 2 n2 ->
let E := Ereg regs (map (Z_to_bv 64) [res0; n2; sp + 904 + 16 * n2] ++ []) in
acond_ok E c ->
@st_ok segs fy E (ss_S3c c) (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
ew E 32 = Z_to_bv 64 res0 /\ ew E 33 = Z_to_bv 64 n2 /\ ew E 34 = Z_to_bv 64 (sp + 904 + 16 * n2) /\
bv_unsigned (ew E 2) = sp /\ bv_unsigned (ew E 10) = res1 /\ bv_unsigned (ew E 27) = a /\ bv_unsigned (ew E 34) = sp + 904 + 16 * n2 /\
bv_unsigned (ew E 32) = res0.
Proof.
intros fy regs mem Lc Ac md c a q n2 res0 res1 sp STK sp0 HH Hain Hwlo Hwhi Hal16 Hst0 H63 Hstw Hr2 Hr18 Hr10 Hr25 Hq Hn2 Hres0 Hres1 Vc0 Vnln E Hc.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 res0) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 904 + 16 * n2] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 n2) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 904 + 16 * n2] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 (sp + 904 + 16 * n2)) by (subst E; apply (Ereg_vals regs [res0; n2; sp + 904 + 16 * n2] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = res1) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU25 : bv_unsigned (ew E 19) = q) by (rewrite (HE 19%nat 19%bv eq_refl), Hr25; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = res0) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = n2) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = sp + 904 + 16 * n2) by (rewrite A34; apply unsigned_lit_small; lia).
split; [| repeat (split; [assumption|]); exact HU32].
unfold ss_S3c. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc0].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU33; reflexivity | cbn; lia | cbn; lia | exact Vnln].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia| apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU18, HU34. repeat split; lia.
- split; [|split; [split; [exact Hc | exact I] |]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU18, HU25, HU32, HU33, HU34. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
assert ((sp + 904 + 16 * n2) mod 8 = 0).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 904 + 16 * n2) with ((2 * (sp / 16) + 113 + 2 * n2) * 8) by lia. apply Z.mod_mul. lia. }
repeat split; lia.
+ cbn [f_alias alias_ok s3_aliases]. repeat split.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU2, HU33, HU34, Z.add_0_r.
rewrite (zcanon_id (sp + 904)), (zcanon_id n2) by (unfold M64; lia). change (Z.land (zcanon 4) 63) with 4. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 4) with 16. rewrite (zcanon_id (n2 * 16)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU2, HU33, HU34.
rewrite (zcanon_id (sp + 912)), (zcanon_id (n2 + 0)) by (unfold M64; lia). change (Z.land (zcanon 4) 63) with 4. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 4) with 16. rewrite (zcanon_id ((n2 + 0) * 16)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Definition S3_post (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (a q n2 res0 res1 sp : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md /\
val_mem segs mem' (a + 8) 8 res1 /\ word_mem segs mem' (sp + 904 + 16 * n2) res0 /\ word_mem segs mem' (sp + 912 + 16 * n2) res1 /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> ~ (sp + 904 + 16 * n2 <= x < sp + 920 + 16 * n2) -> mbyte segs mem' x = mbyte segs mem x) /\
getr regs' 19 = Z_to_bv 64 (q + 1) /\ getr regs' 11 = Z_to_bv 64 n2 /\ getr regs' 14 = Z_to_bv 64 (sp + 928) /\ getr regs' 13 = Z_to_bv 64 255 /\
getr regs' 12 = getr regs 9   /\
(forall r : reg, In r S3_KEEP -> getr regs' r = getr regs r).
Lemma S3_loop : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a q n2 res0 res1 sp : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> getr regs 19 = Z_to_bv 64 q ->
0 <= q < 2 ^ 16 -> 2 <= n2 < 255 -> 1 <= res0 < 2 ^ 63 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 res0 -> val_mem segs mem (sp + 926) 2 n2 ->
(forall regs' mem', S3_post regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp regs' mem' ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_CL') mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr10 Hr25 Hq Hn2 Hres0 Hres1 Vc0 Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (S3_entry fy regs mem Lc Ac md (mkAC BC_LTU (SOff 33%nat 0) (SLit 255)) a q n2 res0 res1 sp STK sp0 HH Hain Hwlo Hwhi Hal16 Hceil H63 Hstw
Hr2 Hr18 Hr10 Hr25 Hq ltac:(lia) Hres0 Hres1 Vc0 Vnln) as (HS & HE & A32 & A33 & A34 & HU2 & HU10 & HU18 & HU34 & HU32).
{ unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (U_atom _ 33 n2), U_SLit; [| apply (Ereg_vals regs [res0; n2; sp + 904 + 16 * n2] [] 1%nat); reflexivity | lia].
change (zcanon 255) with 255. apply Z.ltb_lt. lia. }
set (E := Ereg regs _) in HS, HE, A32, A33, A34, HU2, HU10, HU18, HU34, HU32. change (ss_S3c _) with ss_S3L in HS.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_CL'.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 34); [reflexivity | exact HU34 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc ss_S3L ss_S3Q ss_S3c].
apply HK. unfold S3_post. split; [exact HJ|].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 27%nat 8 8%N (SOff 10 0) a res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU18
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mc1;
pose proof (st_chunk_val segs E ssf ms 2%nat _ 34%nat 0 8%N (SOff 32 0) (sp + 904 + 16 * n2) res0 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn0;
pose proof (st_chunk_val segs E ssf ms 2%nat _ 34%nat 8 8%N (SOff 10 0) (sp + 904 + 16 * n2) res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn1;
change (N.to_nat 8) with 8%nat in Mc1, Mn0, Mn1; rewrite Z.add_0_r in Mn0; replace (sp + 904 + 16 * n2 + 8) with (sp + 912 + 16 * n2) in Mn1 by lia;
split; [exact Mc1|]; split; [apply val_mem_word_mem; exact Mn0|]; split; [apply val_mem_word_mem; exact Mn1|];
split; [intros x Hx Hn1' Hn2'; mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU18, ?HU34; lia); reflexivity|];
split; [jreg HS (19%bv:reg) as Hq25; rewrite Hq25, (HE 19%nat 19%bv eq_refl), Hr25, unsigned_lit_small by lia; reflexivity|];
split; [jreg HS (11%bv:reg) as Hq11; rewrite Hq11; exact A33|];
split; [jreg HS (14%bv:reg) as Hq26; rewrite Hq26, HU2; reflexivity|];
split; [jreg HS (13%bv:reg) as Hq20; exact Hq20|];
split; [jreg HS (12%bv:reg) as Hq12; rewrite Hq12; apply (HE 9%nat 9%bv eq_refl)|];
exact (regs_kept_of_st_ok _ _ _ _ regs _ S3_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))
end.
Qed.
Lemma S3_exit : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(a q n2 res0 res1 sp : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> getr regs 19 = Z_to_bv 64 q ->
0 <= q < 2 ^ 16 -> n2 = 255 -> 1 <= res0 < 2 ^ 63 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 res0 -> val_mem segs mem (sp + 926) 2 n2 ->
(forall regs' mem', S3_post regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp regs' mem' ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_QT) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a q n2 res0 res1 sp Q HJ Hwb Hain Hwlo Hwhi Hal16 Hr2 Hr18 Hr10 Hr25 Hq Hn2 Hres0 Hres1 Vc0 Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (S3_entry fy regs mem Lc Ac md (mkAC BC_GEU (SOff 33%nat 0) (SLit 255)) a q n2 res0 res1 sp STK sp0 HH Hain Hwlo Hwhi Hal16 Hceil H63 Hstw
Hr2 Hr18 Hr10 Hr25 Hq ltac:(lia) Hres0 Hres1 Vc0 Vnln) as (HS & HE & A32 & A33 & A34 & HU2 & HU10 & HU18 & HU34 & HU32).
{ unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (U_atom _ 33 n2), U_SLit; [| apply (Ereg_vals regs [res0; n2; sp + 904 + 16 * n2] [] 1%nat); reflexivity | lia].
change (zcanon 255) with 255. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
set (E := Ereg regs _) in HS, HE, A32, A33, A34, HU2, HU10, HU18, HU34, HU32. change (ss_S3c _) with ss_S3Q in HS.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_QT.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 27); [reflexivity | exact HU18 | cbn [r_wlo r_whi]; intros x Hx; replace x with (a + (x - a)) by lia; apply Hwb; [exact Hain | rewrite HNS; lia] |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 34); [reflexivity | exact HU34 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc ss_S3L ss_S3Q ss_S3c].
apply HK. unfold S3_post. split; [exact HJ|].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 27%nat 8 8%N (SOff 10 0) a res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU18
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mc1;
pose proof (st_chunk_val segs E ssf ms 2%nat _ 34%nat 0 8%N (SOff 32 0) (sp + 904 + 16 * n2) res0 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn0;
pose proof (st_chunk_val segs E ssf ms 2%nat _ 34%nat 8 8%N (SOff 10 0) (sp + 904 + 16 * n2) res1 HS eq_refl eq_refl ltac:(cbn; tauto) HU34
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mn1;
change (N.to_nat 8) with 8%nat in Mc1, Mn0, Mn1; rewrite Z.add_0_r in Mn0; replace (sp + 904 + 16 * n2 + 8) with (sp + 912 + 16 * n2) in Mn1 by lia;
split; [exact Mc1|]; split; [apply val_mem_word_mem; exact Mn0|]; split; [apply val_mem_word_mem; exact Mn1|];
split; [intros x Hx Hn1' Hn2'; mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2, ?HU18, ?HU34; lia); reflexivity|];
split; [jreg HS (19%bv:reg) as Hq25; rewrite Hq25, (HE 19%nat 19%bv eq_refl), Hr25, unsigned_lit_small by lia; reflexivity|];
split; [jreg HS (11%bv:reg) as Hq11; rewrite Hq11; exact A33|];
split; [jreg HS (14%bv:reg) as Hq26; rewrite Hq26, HU2; reflexivity|];
split; [jreg HS (13%bv:reg) as Hq20; exact Hq20|];
split; [jreg HS (12%bv:reg) as Hq12; rewrite Hq12; apply (HE 9%nat 9%bv eq_refl)|];
exact (regs_kept_of_st_ok _ _ _ _ regs _ S3_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity))
end.
Qed.
Definition SF_KEEP : list reg := [2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ss_SF1 : sstate :=
mkSS PC_S3 (sr_set sr_atoms 10%bv (SLit 0))
[ YQ0b.mkRegion (Some 27%nat) 0 16 8 16 [mkChunk 0 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (27%nat, mkAF 0 (2^48) 3) ] [] []).
Lemma S3_fail1 : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (a res0 : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 0 ->
0 <= res0 < 2 ^ 64 -> val_mem segs mem a 8 res0 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (a + 8) 8 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> mbyte segs mem' x = mbyte segs mem x) ->
(forall r : reg, In r SF_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_XT) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a res0 Q HJ Hwb Hain Hr18 Hr10 Hres0 Vc0 HK.
pose proof HJ as (HH & _). pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
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
{ intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
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
jrun LAWS src2tbl_ok HS HJ. { wr_sf1 Hwb Hain HNS HU18 a. }
cbn [ms_mem mkst] in HF, HJ.
jbranch src2tbl HS; clear Hc.
all: jrun_to LAWS src2tbl_ok HS HJ PC_XT; [wr_sf1 Hwb Hain HNS HU18 a |].
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
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
(forall blc j, In (a, NODE_SIZE) blc -> 0 <= j < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (a + j)) ->
In (a, NODE_SIZE) (blocks Lc Ac) ->
getr regs 27 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 res1 -> 1 <= res1 < 2 ^ 63 ->
val_mem segs mem a 8 0 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (a + 8) 8 res1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a + 8 <= x < a + 16) -> mbyte segs mem' x = mbyte segs mem x) ->
(forall r : reg, In r SF_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_XT) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md a res1 Q HJ Hwb Hain Hr18 Hr10 Hres1 Vc0 HK.
pose proof HJ as (HH & _). pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNS : NODE_SIZE = 56) by reflexivity.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE HH Hain ltac:(rewrite HNS; lia)) as (Ha0 & Ha1 & Ha16).
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
{ intros o Ho. apply (present_writable src2_msyms). apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md a NODE_SIZE o HH Hain ltac:(rewrite HNS; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vc0].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU18, HU10. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (a mod 8 = 0) by (pose proof (Z.div_mod a 16 ltac:(lia)) as Hdm; rewrite Ha16 in Hdm; rewrite Hdm; replace (16 * (a / 16) + 0) with ((2 * (a / 16)) * 8) by lia; apply Z.mod_mul; lia).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_S3) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_XT.
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
Definition lh_alias : sv := SAlu ALU_ADD (SOff 2 928) (SAlu ALU_SLL (SOff 19 0) (SLit 3)).
Definition ss_LH (cs : list acond) : sstate :=
mkSS PC_CL' (sr_set (sr_set sr_atoms 14%bv (SOff 2%nat 928)) 13%bv (SLit 255))
[ YQ0b.mkRegion (Some 32%nat) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 33%nat) 40 48 0 0 [mkChunk 40 (CVal 4 (SOff 34 0)); mkChunk 44 (CVal 4 (SOff 35 0))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (11%nat, mkAF 1 254 0); (19%nat, mkAF 0 1023 0); (32%nat, mkAF 0 (2^63) 3);
(33%nat, mkAF 0 (2^63) 3); (34%nat, mkAF 0 (2^30) 0); (35%nat, mkAF 0 (2^30) 0) ] cs [(lh_alias, SOff 32%nat 0)]).
Definition LH_KEEP : list reg := [1; 2; 3; 4; 8; 9; 11; 18; 20; 21; 22; 23; 24; 25]%bv.
Lemma LH_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (cs : list acond) (q a lo hi sp Lf : Z),
getr regs 2 = Z_to_bv 64 sp -> getr regs 19 = Z_to_bv 64 q -> getr regs 14 = Z_to_bv 64 (sp + 928) -> getr regs 13 = Z_to_bv 64 255 ->
getr regs 11 = Z_to_bv 64 Lf ->
0 <= sp -> sp + 5136 < 2 ^ 63 -> sp mod 16 = 0 -> 0 <= q < 512 -> 1 <= Lf <= 254 -> 0 <= a -> a + 56 <= sp -> a mod 8 = 0 ->
0 <= lo < 2 ^ 30 -> 0 <= hi < 2 ^ 30 ->
word_mem segs mem (sp + 928 + 8 * q) a -> val_mem segs mem (a + 40) 4 lo -> val_mem segs mem (a + 44) 4 hi ->
let E := Ereg regs (map (Z_to_bv 64) [sp + 928 + 8 * q; a; lo; hi] ++ []) in
conds_ok E cs ->
@st_ok segs fy E (ss_LH cs) (@mkst fy regs (Z_to_bv 64 PC_CL') mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
ew E 33 = Z_to_bv 64 a /\ ew E 34 = Z_to_bv 64 lo /\ ew E 35 = Z_to_bv 64 hi /\ bv_unsigned (ew E 2) = sp.
Proof.
intros fy regs mem cs q a lo hi sp Lf Hr2 Hr25 Hr26 Hr20 Hr11 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Hhi Wq Vlo Vhi E Hcs.
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 (sp + 928 + 8 * q)) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; hi] [] 0%nat); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 a) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; hi] [] 1%nat); reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; hi] [] 2%nat); reflexivity).
assert (A35 : ew E 35 = Z_to_bv 64 hi) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; hi] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = Lf) by (rewrite (HE 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (HU25 : bv_unsigned (ew E 19) = q) by (rewrite (HE 19%nat 19%bv eq_refl), Hr25; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = sp + 928 + 8 * q) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = a) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = lo) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = hi) by (rewrite A35; apply unsigned_lit_small; lia).
split; [| split; [exact HE | split; [exact A33 | split; [exact A34 | split; [exact A35 | exact HU2]]]]].
unfold ss_LH. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
+ cbn [sv_denot]. rewrite HU2. exact Hr26.
+ cbn [sv_denot]. exact Hr20.
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
rewrite HU2, HU11, HU25, HU32, HU33, HU34, HU35. change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
assert ((sp + 928 + 8 * q) mod 8 = 0).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as Hdm. rewrite Hal16 in Hdm. rewrite Hdm.
replace (16 * (sp / 16) + 0 + 928 + 8 * q) with ((2 * (sp / 16) + 116 + q) * 8) by lia. apply Z.mod_mul. lia. }
repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold lh_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU2, HU25, HU32, Z.add_0_r.
rewrite (zcanon_id (sp + 928)), (zcanon_id q) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 3) with 8. rewrite (zcanon_id (q * 8)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma LH_skip : forall (fy : FPState) (regs : bvmap 5 word) mem (q a lo sp Lf : Z),
getr regs 2 = Z_to_bv 64 sp -> getr regs 19 = Z_to_bv 64 q -> getr regs 14 = Z_to_bv 64 (sp + 928) -> getr regs 13 = Z_to_bv 64 255 ->
getr regs 11 = Z_to_bv 64 Lf ->
0 <= sp -> sp + 5136 < 2 ^ 63 -> sp mod 16 = 0 -> 0 <= q < 512 -> 1 <= Lf <= 254 -> 0 <= a -> a + 56 <= sp -> a mod 8 = 0 ->
0 <= lo < 2 ^ 30 ->
word_mem segs mem (sp + 928 + 8 * q) a -> val_mem segs mem (a + 40) 4 lo -> val_mem segs mem (a + 44) 4 lo ->
exists regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_CL') mem rom) (@mkst fy regs' (Z_to_bv 64 PC_CL') mem rom) /\
getr regs' 19 = Z_to_bv 64 (q + 1) /\ getr regs' 14 = Z_to_bv 64 (sp + 928) /\ getr regs' 13 = Z_to_bv 64 255 /\
getr regs' 12 = getr regs 12   /\
(forall r : reg, In r LH_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem q a lo sp Lf Hr2 Hr25 Hr26 Hr20 Hr11 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Wq Vlo Vhi.
set (E := Ereg regs (map (Z_to_bv 64) [sp + 928 + 8 * q; a; lo; lo] ++ [])).
assert (B34 : ew E 34 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; lo] [] 2%nat); reflexivity).
assert (B35 : ew E 35 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; lo] [] 3%nat); reflexivity).
destruct (LH_entry fy regs mem [mkAC BC_EQ (SOff 35%nat 0) (SOff 34%nat 0)] q a lo lo sp Lf Hr2 Hr25 Hr26 Hr20 Hr11 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Hlo Wq Vlo Vhi)
as (HS & HE & A33 & A34 & A35 & HU2).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, !U_SOff. fold E. rewrite B34, B35. apply Z.eqb_eq. reflexivity. }
fold E in HS, HE, A33, A34, A35, HU2.
pure_to src2tbl_ok HS 0x13dd4.
pure_to src2tbl_ok HS PC_CL'.
exists regs1. split; [exact (msteps_trans _ _ _ _ Hms Hms0)|].
jreg HS (19%bv:reg) as Hq25. jreg HS (14%bv:reg) as Hq26. jreg HS (13%bv:reg) as Hq20. cbn [ms_regs mkst] in Hq25, Hq26, Hq20.
split; [rewrite Hq25, (HE 19%nat 19%bv eq_refl), Hr25, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Hq26, HU2; reflexivity|]. split; [exact Hq20|].
split; [jreg HS (12%bv:reg) as Hq12; cbn [ms_regs mkst] in Hq12; rewrite Hq12; apply (HE 12%nat 12%bv eq_refl)|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ LH_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma LH_split : forall (fy : FPState) (regs : bvmap 5 word) mem (q a lo hi sp Lf : Z),
getr regs 2 = Z_to_bv 64 sp -> getr regs 19 = Z_to_bv 64 q -> getr regs 14 = Z_to_bv 64 (sp + 928) -> getr regs 13 = Z_to_bv 64 255 ->
getr regs 11 = Z_to_bv 64 Lf ->
0 <= sp -> sp + 5136 < 2 ^ 63 -> sp mod 16 = 0 -> 0 <= q < 512 -> 1 <= Lf <= 254 -> 0 <= a -> a + 56 <= sp -> a mod 8 = 0 ->
0 <= lo -> lo < hi -> hi < 2 ^ 30 ->
word_mem segs mem (sp + 928 + 8 * q) a -> val_mem segs mem (a + 40) 4 lo -> val_mem segs mem (a + 44) 4 hi ->
exists regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_CL') mem rom) (@mkst fy regs' (Z_to_bv 64 0x13de0) mem rom) /\
getr regs' 27 = Z_to_bv 64 a /\ getr regs' 12 = Z_to_bv 64 (a + 16) /\ getr regs' 26 = Z_to_bv 64 lo /\ getr regs' 10 = Z_to_bv 64 hi /\
getr regs' 19 = Z_to_bv 64 q /\ getr regs' 14 = Z_to_bv 64 (sp + 928) /\ getr regs' 13 = Z_to_bv 64 255 /\
(forall r : reg, In r LH_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem q a lo hi sp Lf Hr2 Hr25 Hr26 Hr20 Hr11 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 Hlo Hlh Hhi Wq Vlo Vhi.
set (E := Ereg regs (map (Z_to_bv 64) [sp + 928 + 8 * q; a; lo; hi] ++ [])).
assert (B34 : ew E 34 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; hi] [] 2%nat); reflexivity).
assert (B35 : ew E 35 = Z_to_bv 64 hi) by (subst E; apply (Ereg_vals regs [sp + 928 + 8 * q; a; lo; hi] [] 3%nat); reflexivity).
destruct (LH_entry fy regs mem [mkAC BC_NE (SOff 35%nat 0) (SOff 34%nat 0); mkAC BC_LTU (SOff 34%nat 0) (SOff 35%nat 0)] q a lo hi sp Lf
Hr2 Hr25 Hr26 Hr20 Hr11 Hsp0 Hsp1 Hal16 Hq HLf Ha0 Ha1 Ha8 ltac:(lia) ltac:(lia) Wq Vlo Vhi)
as (HS & HE & A33 & A34 & A35 & HU2).
{ cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, branch_ltu_U, !U_SOff. fold E. rewrite B34, B35.
rewrite !Z.add_0_r, !unsigned_lit_small by lia. rewrite !zcanon_id by (unfold M64; lia).
split; [apply Bool.negb_true_iff; apply Z.eqb_neq; lia|]. split; [apply Z.ltb_lt; lia | exact I]. }
fold E in HS, HE, A33, A34, A35, HU2.
pure_to src2tbl_ok HS 0x13de0.
exists regs0. split; [exact Hms|].
jreg HS (27%bv:reg) as Hq18. jreg HS (12%bv:reg) as Hq12. jreg HS (26%bv:reg) as Hq9. jreg HS (10%bv:reg) as Hq10.
jreg HS (19%bv:reg) as Hq25. jreg HS (14%bv:reg) as Hq26. jreg HS (13%bv:reg) as Hq20.
cbn [ms_regs mkst] in Hq18, Hq12, Hq9, Hq10, Hq25, Hq26, Hq20.
split; [rewrite Hq18; exact A33|]. split; [rewrite Hq12, A33, unsigned_lit_small by lia; reflexivity|].
split; [rewrite Hq9; exact A34|]. split; [rewrite Hq10; exact A35|].
split; [rewrite Hq25; exact (eq_trans (HE 19%nat 19%bv eq_refl) Hr25)|]. split; [rewrite Hq26, HU2; reflexivity|]. split; [exact Hq20|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ LH_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Section J2.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition ss_R0 : sstate :=
mkSS PC_CR sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 926 928 926 928 [] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (14%nat, mkAF 0 (2^30) 0) ] [] []).
Definition R0_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma R0_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (cnt sp : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 14 = Z_to_bv 64 (cnt - 1)   -> 1 <= cnt < 2 ^ 30 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
val_mem segs mem' (sp + 926) 2 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp + 926 <= x < sp + 928) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 1 = Z_to_bv 64 0x13d84 -> getr regs' 10 = getr regs 25 -> getr regs' 11 = getr regs 24 -> getr regs' 12 = Z_to_bv 64 (sp + 926) ->
getr regs' 13 = Z_to_bv 64 0 -> getr regs' 14 = Z_to_bv 64 (cnt - 1) -> getr regs' 15 = Z_to_bv 64 0 ->
(forall r : reg, In r R0_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 src2_A_new_tree_node) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_CR) mem rom) md) Q.
Proof.
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
jrun_to LAWS src2tbl_ok HS HJ src2_A_new_tree_node.
{ wr_ok_eval. eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 2%nat 926 2%N (SLit 0) sp 0 HS eq_refl eq_refl ltac:(cbn; tauto) HU2 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Mnln
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
mkSS 0x13d84 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 926 936 928 936 [mkChunk 926 (CVal 2 (SLit 1))] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (10%nat, mkAF 1 (2^63) 0) ] [] []).
Definition R1_KEEP : list reg := [2; 3; 4; 8; 20; 21; 22; 24; 25; 26; 27]%bv.
Lemma R1_ok : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md (root sp : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
sp0 - STK <= sp -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 root -> 1 <= root < 2 ^ 63 ->
val_mem segs mem (sp + 926) 2 1 ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
word_mem segs mem' (sp + 928) root ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp + 928 <= x < sp + 936) -> mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 9 = Z_to_bv 64 root -> getr regs' 12 = Z_to_bv 64 root -> getr regs' 18 = getr regs 9 ->
getr regs' 11 = Z_to_bv 64 1 -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 14 = Z_to_bv 64 (sp + 928) ->
getr regs' 13 = Z_to_bv 64 255 -> getr regs' 23 = Z_to_bv 64 (sp + 5028) ->
(forall r : reg, In r R1_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_CL') mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 0x13d84) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md root sp Q HJ Hwlo Hwhi Hal16 Hr2 Hr10 Hroot Vnln HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _). pose proof (proj1 alloc_ceiling_val) as Hac.
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = root) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_R1 (@mkst fy regs (Z_to_bv 64 0x13d84) mem rom)).
{ unfold ss_R1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia |].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact Vnln].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HU2, HU10.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 0x13d84) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_CL'.
{ wr_ok_eval. eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs E _ ms HS eq_refl). cbn [ss_pc].
lazymatch type of HS with st_ok _ _ ?ssf _ =>
pose proof (st_chunk_val segs E ssf ms 0%nat _ 2%nat 928 8%N (SOff 10 0) sp root HS eq_refl eq_refl ltac:(cbn; tauto) HU2
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mnl
end.
change (N.to_nat 8) with 8%nat in Mnl.
apply HK.
- exact HJ.
- apply val_mem_word_mem. exact Mnl.
- intros x Hx Hn. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?HU2; lia). reflexivity.
- jreg HS (9%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact Hr10.
- jreg HS (12%bv:reg) as Hq; rewrite Hq, (HE 10%nat 10%bv eq_refl); exact Hr10.
- jreg HS (18%bv:reg) as Hq; rewrite Hq; exact (HE 9%nat 9%bv eq_refl).
- jreg HS (11%bv:reg) as Hq; exact Hq.
- jreg HS (19%bv:reg) as Hq; exact Hq.
- jreg HS (14%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- jreg HS (13%bv:reg) as Hq; exact Hq.
- jreg HS (23%bv:reg) as Hq; rewrite Hq, HU2; reflexivity.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ R1_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_R1f : sstate := mkSS 0x13d84 (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
Lemma R1_fail : forall (fy : FPState) (regs : bvmap 5 word) mem md Q,
m_halted md = None -> m_vm_lazy md = [] ->
getr regs 10 = Z_to_bv 64 0 ->
(forall regs', (forall r : reg, In r R0_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_XD) mem rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 0x13d84) mem rom) md) Q.
Proof.
intros fy regs mem md Q Hh Hl Hr10 HK.
set (E := Ereg regs []).
assert (HS : @st_ok segs fy E ss_R1f (@mkst fy regs (Z_to_bv 64 0x13d84) mem rom)).
{ unfold ss_R1f. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hr10].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [exact I | split; exact I]. }
pure_to src2tbl_ok HS PC_XD.
eapply (SR_msteps segs _ _ md _ Hh Hl Hms). apply HK.
exact (regs_kept_of_st_ok _ _ _ _ regs _ R0_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
End J2.
End b.
