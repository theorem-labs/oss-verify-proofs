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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI07
YI1e YI1i YI0x YI56 YI1h YP14 YP16 YI08 YI0c YI0f YI09 YI3q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_PR : Z := 0x13de0.
Definition PC_SPLIT : Z := 0x13f00.
Definition PART_KEEP : list reg := [1; 2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 24; 25; 27]%bv.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Ltac ridx_of HE := intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia.
Definition disj_blocks (p n q m : Z) : Prop := p + n <= q \/ q + m <= p.
Lemma in_bv5 : forall (r : reg) (L : list reg), existsb (bv_eqb r) L = true -> In r L.
Proof. intros r L H. apply existsb_exists in H as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst. exact Hin. Qed.
Ltac inl := apply in_bv5; vm_compute; reflexivity.

Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := src2segs (only parsing).
Local Notation rom := (seg_rom src2segs) (only parsing).
Definition pra_alias : sv := SAlu ALU_ADD (SOff 27 16) (SAlu ALU_SLL (SOff 32 0) (SLit 3)).
Definition ss_PRA0 : sstate :=
mkSS PC_PR (sr_set sr_atoms 12%bv (SOff 27%nat 16))
[ YQ0b.mkRegion (Some 27%nat) 48 49 0 0 [mkChunk 48 (CVal 1 (SOff 32 0))];
YQ0b.mkRegion (Some 33%nat) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (26%nat, mkAF 0 (2^30) 0); (27%nat, mkAF 0 (2^48) 3); (32%nat, mkAF 0 2 0); (33%nat, mkAF 0 (2^48) 3) ]
[] [(pra_alias, SOff 33%nat 0)]).
Definition ss_PRA : sstate := mkSST PC_PR (ss_regs ss_PRA0) (sfr_atoms 48) (ss_mem ss_PRA0) None (ss_facts ss_PRA0).
Definition PRA_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Lemma PR_to_SU : forall (fy : FPState) (regs : bvmap 5 word) mem (a i cut mean : Z),
getr regs 27 = Z_to_bv 64 a -> getr regs 12 = Z_to_bv 64 (a + 16) -> getr regs 26 = Z_to_bv 64 i ->
0 <= i < 2 ^ 29 -> 0 <= a -> a + 56 < 2 ^ 48 -> a mod 8 = 0 -> 0 <= cut <= 2 -> 0 <= mean < 2 ^ 64 ->
val_mem segs mem (a + 48) 1 cut -> val_mem segs mem (a + 16 + 8 * cut) 8 mean ->
frm_zero (@fp_csr fy) ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_PR) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SU) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 14 = Z_to_bv 64 (3 * i) /\ getr regs' 26 = Z_to_bv 64 (i - 1) /\
getr regs' 12 = Z_to_bv 64 (a + 16) /\
(forall r : reg, In r PRA_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem a i cut mean Hr18 Hr12 Hr9 Hi Ha0 Ha1 Ha8 Hcut Hmean Vcut Vmean Hfrm.
set (E0 := Ereg regs (map (Z_to_bv 64) [cut; a + 16 + 8 * cut; mean] ++ [])).
set (E := ew_fregs E0 48 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [cut; a + 16 + 8 * cut; mean] j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HEf : forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; subst E; apply ew_fregs_at).
assert (HU9 : bv_unsigned (ew E0 26) = i) by (rewrite (HE0 26%nat 26%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E0 27) = a) by (rewrite (HE0 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (A32 : ew E0 32 = Z_to_bv 64 cut) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 (a + 16 + 8 * cut)) by (apply (HV 1%nat); reflexivity).
assert (A34 : ew E0 34 = Z_to_bv 64 mean) by (apply (HV 2%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E0 32) = cut) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E0 33) = a + 16 + 8 * cut) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E0 34) = mean) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_PRA0 (@mkst fy regs (Z_to_bv 64 PC_PR) mem rom)).
{ unfold ss_PRA0. subst E0. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |]. cbn [sv_denot]. rewrite HU18. exact Hr12.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vcut].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vmean].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU18, HU33. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU9, HU18, HU32, HU33. change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
assert ((a + 16 + 8 * cut) mod 8 = 0) by (replace (a + 16 + 8 * cut) with (a + (2 + cut) * 8) by lia; rewrite Z.mod_add by lia; exact Ha8).
repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold pra_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU18, HU32, HU33, !Z.add_0_r.
rewrite (zcanon_id (a + 16)), (zcanon_id cut) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (zcanon_id (cut * 8)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia. }
pose proof (st_ok_enterF segs fy 48 E0 ss_PRA0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 48 (@fp_regs fy)) with E in HS.
change (mkSST _ _ _ _ _ _) with ss_PRA in HS.
pureF_to src2tbl_ok HS PC_SU.
exists (fp_of ms), (ms_regs ms).
split; [rewrite Hsh in Hms; exact Hms|].
split; [exact (st_okF_frm segs E _ _ HS)|].
split. { cbn [fp_regs fp_of]. rewrite (st_okF_freg segs E _ _ 15%bv HS).
match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end.
cbn [sv_denot]. rewrite Z.add_0_r, HEE by lia. rewrite HU34. reflexivity. }
jregF HS (13%bv:reg) as Hq13. jregF HS (26%bv:reg) as Hq9.
pose proof (st_okF_reg segs E _ _ 14%bv HS) as Hq14. eval_sr_get_in Hq14.
split; [rewrite Hq13, HEE by lia; exact A32|].
split; [rewrite Hq14; apply (denot_mul3 E 26 i); [rewrite (HE 26%nat 26%bv eq_refl); exact Hr9 | lia]|].
split; [rewrite Hq9, (HE 26%nat 26%bv eq_refl), Hr9, unsigned_lit_small by lia; replace (i - 1) with (i + -1) by lia; reflexivity|].
jregF HS (12%bv:reg) as Hq12.
split; [rewrite Hq12, HEE by lia; rewrite (HE0 27%nat 27%bv eq_refl), Hr18, unsigned_lit_small by lia; reflexivity|].
exact (st_okF_regs_kept segs E _ _ regs PRA_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_BGD : sstate :=
mkSS PC_BG sr_atoms
[ YQ0b.mkRegion (Some 27%nat) 40 44 0 0 [mkChunk 40 (CVal 4 (SOff 32 0))] ] None
(mkFacts [ (26%nat, mkAF 0 (2^30) 0); (10%nat, mkAF 0 (2^30) 0); (27%nat, mkAF 0 (2^48) 3); (32%nat, mkAF 0 (2^30) 0) ]
[mkAC BC_GEU (SOff 26%nat 0) (SOff 10%nat 0)] []).
Definition BGD_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma BG_done : forall (fy : FPState) (regs : bvmap 5 word) mem (a i1 k1 lo : Z),
getr regs 27 = Z_to_bv 64 a -> getr regs 26 = Z_to_bv 64 i1 -> getr regs 10 = Z_to_bv 64 k1 ->
0 <= k1 <= i1 -> i1 < 2 ^ 29 -> 0 <= a -> a + 56 < 2 ^ 48 -> a mod 8 = 0 -> 0 <= lo < 2 ^ 29 ->
val_mem segs mem (a + 40) 4 lo ->
exists regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom) (@mkst fy regs' (Z_to_bv 64 PC_SPLIT) mem rom) /\
getr regs' 13 = Z_to_bv 64 lo /\
(forall r : reg, In r BGD_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem a i1 k1 lo Hr18 Hr9 Hr10 Hki Hi1 Ha0 Ha1 Ha8 Hlo Vlo.
set (E := Ereg regs (map (Z_to_bv 64) [lo] ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 lo) by (subst E; apply (Ereg_vals regs [lo] [] 0%nat); reflexivity).
assert (HU9 : bv_unsigned (ew E 26) = i1) by (rewrite (HE 26%nat 26%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew E 10) = k1) by (rewrite (HE 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 27) = a) by (rewrite (HE 27%nat 27%bv eq_refl), Hr18; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = lo) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok segs fy E ss_BGD (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom)).
{ unfold ss_BGD. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia | exact Vlo].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [|exact I]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU9, HU10, HU18, HU32. change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, !U_SOff, HU9, HU10, !Z.add_0_r, !zcanon_id by (unfold M64; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
pure_to src2tbl_ok HS PC_SPLIT.
exists regs0. split; [exact Hms|].
jreg HS (13%bv:reg) as Hq13. cbn [ms_regs mkst] in Hq13.
split; [rewrite Hq13; exact A32|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ BGD_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition pack2 (n1 n0 : nat) : sv := SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0).
Lemma U_pack2 : forall E n1 n0 b1 b0, ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
U E (pack2 n1 n0) = b0 + 256 * b1.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. unfold pack2. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite (U_atom E n1 b1 H1), (U_atom E n0 b0 H0) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b1 * 256)) by (unfold M64; lia). rewrite lor_shl8 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_pack2_hi : forall E n1 n0 b1 b0, ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
sv_denot E (SAlu ALU_SRL (pack2 n1 n0) (SLit 8)) = Z_to_bv 64 b1.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_pack2 E n1 n0 b1 b0 H1 H0 R1 R0), U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite div_256 by lia.
apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_pack2_lo : forall E n1 n0 b1 b0, ew E n1 = Z_to_bv 64 b1 -> ew E n0 = Z_to_bv 64 b0 -> 0 <= b1 < 256 -> 0 <= b0 < 256 ->
sv_denot E (SExt false 8 (pack2 n1 n0)) = Z_to_bv 64 b0.
Proof.
intros E n1 n0 b1 b0 H1 H0 R1 R0. rewrite denot_lit_U. f_equal. rewrite U_SExt. rewrite (U_pack2 E n1 n0 b1 b0 H1 H0 R1 R0).
change (2 ^ Z.of_N 8) with 256. rewrite mod_256 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_small by lia. rewrite swrap32_id by lia. apply zcanon_id. unfold M64; lia.
Qed.
Definition sw_aliases : list (sv * sv) :=
[(SAlu ALU_ADD (SOff 14 0) (SOff 25 0), SOff 40%nat 0);
(SAlu ALU_ADD (SOff 38 0) (SOff 25 0), SOff 41%nat 0);
(SAlu ALU_ADD (SAlu ALU_SLL (SOff 26 0) (SLit 2)) (SOff 24 0), SOff 42%nat 0);
(SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 2)) (SOff 24 0), SOff 43%nat 0)].
Definition ss_SW : sstate :=
mkSS PC_BG (sr_set (sr_set sr_atoms 15%bv (SOff 38%nat (-3))) 23%bv (SOff 2%nat 5028))
[ YQ0b.mkRegion (Some 40%nat) 0 3 0 3 [mkChunk 0 (CVal 1 (SOff 44 0)); mkChunk 1 (CVal 1 (SOff 45 0)); mkChunk 2 (CVal 1 (SOff 46 0))];
YQ0b.mkRegion (Some 41%nat) 0 3 0 3 [mkChunk 0 (CVal 1 (SOff 47 0)); mkChunk 1 (CVal 1 (SOff 48 0)); mkChunk 2 (CVal 1 (SOff 49 0))];
YQ0b.mkRegion (Some 42%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SOff 50 0))];
YQ0b.mkRegion (Some 43%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SOff 51 0))];
YQ0b.mkRegion (Some 2%nat) 5028 5031 5028 5031 [] ] None
(mkFacts [ (2%nat, mkAF 0 (2^63) 4); (26%nat, mkAF 0 (2^30) 0); (10%nat, mkAF 0 (2^30) 0); (14%nat, mkAF 0 (2^31) 0);
(25%nat, mkAF 0 (2^48) 0); (24%nat, mkAF 0 (2^48) 2); (38%nat, mkAF 0 (2^31) 0);
(44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0);
(47%nat, mkAF 0 255 0); (48%nat, mkAF 0 255 0); (49%nat, mkAF 0 255 0);
(50%nat, mkAF 0 (2^31) 0); (51%nat, mkAF 0 (2^31) 0) ]
[mkAC BC_LTU (SOff 26%nat 0) (SOff 10%nat 0)] sw_aliases).
Definition ss_SW_out : sstate := Eval vm_compute in (fst (sym_run_toN segs src2tbl FUEL PC_PR ss_SW)).

Definition CARRY3 : list reg := [1; 2; 3; 4; 8; 9; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Definition CARRY1 : list reg := [1; 2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Definition SW_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Section J.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Lemma SW_stretch : forall (fy : FPState) (regs : bvmap 5 word) mem STK sp0 FP L A mem0 md0 Lc Ac md
(E : list entry) (tail : list Z) (i1 k1 p fdp sp T : Z) Q,
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md ->
In (p, 3 * T) (blocks Lc Ac) -> ~ In (p, 3 * T) (blocks L A) ->
In (fdp, 4 * elen E) (blocks Lc Ac) -> ~ In (fdp, 4 * elen E) (blocks L A) ->
disj_blocks p (3 * T) fdp (4 * elen E) ->
arr8 segs mem p (pal_bytes E ++ tail) -> 3 * elen E + zlen tail = 3 * T -> arr32 segs mem fdp (fr_vals E) ->
ent_ok E -> Forall (fun e => snd e < 2 ^ 31) E ->
0 <= i1 -> i1 < k1 -> k1 < elen E -> elen E < 2 ^ 29 ->
sp0 - STK <= sp + 5028 -> sp + 5136 <= sp0 -> sp mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 sp -> getr regs 14 = Z_to_bv 64 (3 * i1) -> getr regs 15 = Z_to_bv 64 (3 * k1 - 3) ->
getr regs 10 = Z_to_bv 64 k1 -> getr regs 26 = Z_to_bv 64 i1 -> getr regs 25 = Z_to_bv 64 p -> getr regs 24 = Z_to_bv 64 fdp ->
getr regs 23 = Z_to_bv 64 (sp + 5028) ->
(forall regs' mem',
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
arr8 segs mem' p (pal_bytes (eswap dentry E i1 k1) ++ tail) -> arr32 segs mem' fdp (fr_vals (eswap dentry E i1 k1)) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (p <= x < p + 3 * elen E) -> ~ (fdp <= x < fdp + 4 * elen E) -> ~ (sp + 5028 <= x < sp + 5031) ->
mbyte segs mem' x = mbyte segs mem x) ->
getr regs' 23 = Z_to_bv 64 (sp + 5028) ->
(forall r : reg, In r SW_KEEP -> getr regs' r = getr regs r) ->
SR segs (mkCfg (@mkst fy regs' (Z_to_bv 64 PC_PR) mem' rom) md) Q) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom) md) Q.
Proof.
intros fy regs mem STK sp0 FP L A mem0 md0 Lc Ac md E tail i1 k1 p fdp sp T Q
HJ Hpin Hpn0 Hfin Hfn0 Hdisj Hpa Hlen Hfa HE Hf31 Hi0 Hik Hk1 Hcnt Hwlo Hwhi Hal16
Hr2 Hr14 Hr15 Hr10 Hr9 Hr22 Hr27 Hr19 HK.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (Htl : 0 <= zlen tail) by (unfold zlen; lia).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md p (3 * T) HH Hpin ltac:(lia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) HH Hfin ltac:(lia)) as (Hf0 & Hf1 & _).
pose proof (pal_bytes_bytes E HE) as HB. pose proof (zlen_pal_bytes E) as HLp. pose proof (zlen_fr_vals E) as HLf.
assert (PB : forall x, 0 <= x < 3 * elen E -> mbyte segs mem (p + x) = Some (Z_to_bv 8 (getz (pal_bytes E) x)) /\ 0 <= getz (pal_bytes E) x < 256).
{ intros x Hx. destruct (arr8_getz segs mem p (pal_bytes E ++ tail) x Hpa ltac:(rewrite zlen_app_pal; lia)) as [H1 H2].
rewrite getz_app_l in H1, H2 by lia. auto. }
assert (FB : forall j, 0 <= j < elen E -> val_mem segs mem (fdp + 4 * j) 4 (getz (fr_vals E) j) /\ 0 <= getz (fr_vals E) j < 2 ^ 31).
{ intros j Hj. destruct (arr32_getz segs mem fdp (fr_vals E) j Hfa ltac:(lia)) as [H1 H2]. split; [exact H1|].
rewrite getz_fr_vals by lia. pose proof (proj1 (Forall_forall _ _) Hf31 _ (znth_In dentry E j Hj)) as X. cbn beta in X.
pose proof (proj2 (ent_ok_at E j HE Hj)). unfold efreq in *. lia. }
destruct (PB (3 * i1) ltac:(lia)) as [B0 R0]. destruct (PB (3 * i1 + 1) ltac:(lia)) as [B1 R1]. destruct (PB (3 * i1 + 2) ltac:(lia)) as [B2 R2].
destruct (PB (3 * k1) ltac:(lia)) as [C0 Q0]. destruct (PB (3 * k1 + 1) ltac:(lia)) as [C1 Q1]. destruct (PB (3 * k1 + 2) ltac:(lia)) as [C2 Q2].
destruct (FB i1 ltac:(lia)) as [Fi Ri]. destruct (FB k1 ltac:(lia)) as [Fk Rk].
set (vals := [0; 0; 0; 0; 0; 0; 3 * k1; 0; p + 3 * i1; p + 3 * k1; fdp + 4 * i1; fdp + 4 * k1;
getz (pal_bytes E) (3 * i1); getz (pal_bytes E) (3 * i1 + 1); getz (pal_bytes E) (3 * i1 + 2);
getz (pal_bytes E) (3 * k1); getz (pal_bytes E) (3 * k1 + 1); getz (pal_bytes E) (3 * k1 + 2);
getz (fr_vals E) i1; getz (fr_vals E) k1]).
set (Ev := Ereg regs (map (Z_to_bv 64) vals ++ [])).
assert (HE' : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew Ev k = getr regs rr) by (intros; subst Ev; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew Ev (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst Ev; apply Ereg_vals; exact Hj).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew Ev (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
assert (HU2 : bv_unsigned (ew Ev 2) = sp) by (rewrite (HE' 2%nat 2%bv eq_refl), Hr2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew Ev 26) = i1) by (rewrite (HE' 26%nat 26%bv eq_refl), Hr9; apply unsigned_lit_small; lia).
assert (HU10 : bv_unsigned (ew Ev 10) = k1) by (rewrite (HE' 10%nat 10%bv eq_refl), Hr10; apply unsigned_lit_small; lia).
assert (HU14 : bv_unsigned (ew Ev 14) = 3 * i1) by (rewrite (HE' 14%nat 14%bv eq_refl), Hr14; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew Ev 25) = p) by (rewrite (HE' 25%nat 25%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (HU27 : bv_unsigned (ew Ev 24) = fdp) by (rewrite (HE' 24%nat 24%bv eq_refl), Hr27; apply unsigned_lit_small; lia).
pose proof (HA 6%nat (3 * k1) eq_refl ltac:(lia)) as A38. pose proof (HA 8%nat (p + 3 * i1) eq_refl ltac:(lia)) as A40.
pose proof (HA 9%nat (p + 3 * k1) eq_refl ltac:(lia)) as A41. pose proof (HA 10%nat (fdp + 4 * i1) eq_refl ltac:(lia)) as A42.
pose proof (HA 11%nat (fdp + 4 * k1) eq_refl ltac:(lia)) as A43.
pose proof (HA 12%nat _ eq_refl ltac:(lia)) as A44. pose proof (HA 13%nat _ eq_refl ltac:(lia)) as A45. pose proof (HA 14%nat _ eq_refl ltac:(lia)) as A46.
pose proof (HA 15%nat _ eq_refl ltac:(lia)) as A47. pose proof (HA 16%nat _ eq_refl ltac:(lia)) as A48. pose proof (HA 17%nat _ eq_refl ltac:(lia)) as A49.
pose proof (HA 18%nat _ eq_refl ltac:(lia)) as A50. pose proof (HA 19%nat _ eq_refl ltac:(lia)) as A51.
cbn [Nat.add] in A38, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51.
assert (HS : @st_ok segs fy Ev ss_SW (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom)).
{ unfold ss_SW. subst Ev. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |] | intros HH0; discriminate HH0 |].
+ cbn [sv_denot]. rewrite A38. rewrite Hr15. replace (3 * k1 - 3) with (3 * k1 + -3) by lia. reflexivity.
+ cbn [sv_denot]. rewrite HU2. exact Hr19.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A40.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md p (3 * T) (3 * i1 + o) HH Hpin ltac:(lia))). }
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A44, ?A45, ?A46; reflexivity | cbn; lia | cbn; lia |]);
(apply val_mem_1; [|lia]); [rewrite Z.add_0_r; exact B0 | rewrite <- Z.add_assoc; exact B1 | rewrite <- Z.add_assoc; exact B2].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A41.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md p (3 * T) (3 * k1 + o) HH Hpin ltac:(lia))). }
repeat apply Forall_cons; [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?A47, ?A48, ?A49; reflexivity | cbn; lia | cbn; lia |]);
(apply val_mem_1; [|lia]); [rewrite Z.add_0_r; exact C0 | rewrite <- Z.add_assoc; exact C1 | rewrite <- Z.add_assoc; exact C2].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A42.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) (4 * i1 + o) HH Hfin ltac:(lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A50; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Fi].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite A43.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src2_msyms). rewrite <- Z.add_assoc. apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) (4 * k1 + o) HH Hfin ltac:(lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A51; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Fk].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, A40, A41, A42, A43. unfold disj_blocks in Hdisj. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU2, HU9, HU10, HU14, HU22, HU27, A38, A44, A45, A46, A47, A48, A49, A50, A51.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.mod_1_r.
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md fdp (4 * elen E) HH Hfin ltac:(lia)) as (_ & _ & Hf16).
assert (fdp mod 4 = 0) by (pose proof (Z.div_mod fdp 16 ltac:(lia)) as Hdm; rewrite Hf16 in Hdm; rewrite Hdm; replace (16 * (fdp / 16) + 0) with ((4 * (fdp / 16)) * 4) by lia; apply Z.mod_mul; lia).
repeat split; lia.
+ cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_ltu_U, !U_SOff, HU9, HU10, !Z.add_0_r, !zcanon_id by (unfold M64; lia). apply Z.ltb_lt. lia.
+ cbn [f_alias alias_ok sw_aliases]. repeat split.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, HU14, HU22, A40, !Z.add_0_r.
rewrite (zcanon_id (3 * i1)), (zcanon_id p) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, A38, HU22, A41, !Z.add_0_r.
rewrite (zcanon_id (3 * k1)), (zcanon_id p) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU9, HU27, A42, !Z.add_0_r.
rewrite (zcanon_id i1), (zcanon_id fdp) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (i1 * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, HU10, HU27, A43, !Z.add_0_r.
rewrite (zcanon_id k1), (zcanon_id fdp) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (k1 * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_BG) mem rom)) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_PR.
{ wr_ok_eval.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 40); [reflexivity | exact A40 | cbn [r_wlo r_whi]; intros a Ha; right; right; exists p, (3 * T); split; [exact Hpin | split; [exact Hpn0 | lia]] |].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 41); [reflexivity | exact A41 | cbn [r_wlo r_whi]; intros a Ha; right; right; exists p, (3 * T); split; [exact Hpin | split; [exact Hpn0 | lia]] |].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 42); [reflexivity | exact A42 | cbn [r_wlo r_whi]; intros a Ha; right; right; exists fdp, (4 * elen E); split; [exact Hfin | split; [exact Hfn0 | lia]] |].
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 43); [reflexivity | exact A43 | cbn [r_wlo r_whi]; intros a Ha; right; right; exists fdp, (4 * elen E); split; [exact Hfin | split; [exact Hfn0 | lia]] |].
eapply (wr_ok_cons_win _ _ _ _ _ _ _ _ 2); [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst segs Ev _ ms HS eq_refl). cbn [ss_pc ss_SW_out].
assert (NB : forall (off : Z) (e : sv) (v : Z) (i : nat) (n : nat) (b : Z),
nth_error (ss_mem ss_SW_out) i = Some (nth i (ss_mem ss_SW_out) (YQ0b.mkRegion None 0 0 0 0 [])) ->
r_base (nth i (ss_mem ss_SW_out) (YQ0b.mkRegion None 0 0 0 0 [])) = Some n ->
In (mkChunk off (CVal 1 e)) (r_chunks (nth i (ss_mem ss_SW_out) (YQ0b.mkRegion None 0 0 0 0 []))) ->
bv_unsigned (ew Ev n) = b -> sv_denot Ev e = Z_to_bv 64 v -> 0 <= v < 256 ->
mbyte segs (ms_mem ms) (b + off) = Some (Z_to_bv 8 v)).
{ intros off e v i n b Hi Hb Hin Hn He Hv. exact (st_chunk_byte Ev ss_SW_out ms i _ n off e b v HS Hi Hb Hin Hn He Hv). }
assert (D44 : ew Ev 44 = Z_to_bv 64 (getz (pal_bytes E) (3 * i1))) by (rewrite <- A44; symmetry; apply Z_to_bv_bv_unsigned).
assert (D45 : ew Ev 45 = Z_to_bv 64 (getz (pal_bytes E) (3 * i1 + 1))) by (rewrite <- A45; symmetry; apply Z_to_bv_bv_unsigned).
assert (D50 : ew Ev 50 = Z_to_bv 64 (getz (fr_vals E) i1)) by (rewrite <- A50; symmetry; apply Z_to_bv_bv_unsigned).
assert (D51 : ew Ev 51 = Z_to_bv 64 (getz (fr_vals E) k1)) by (rewrite <- A51; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dat : forall n v, bv_unsigned (ew Ev n) = v -> sv_denot Ev (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Z.add_0_r, Hn. reflexivity. }
pose proof (NB 0 _ _ 0%nat 40%nat _ eq_refl eq_refl ltac:(cbn; tauto) A40 (Dat 47%nat _ A47) ltac:(lia)) as M0.
pose proof (NB 1 _ _ 0%nat 40%nat _ eq_refl eq_refl ltac:(cbn; tauto) A40 (Dat 48%nat _ A48) ltac:(lia)) as M1.
pose proof (NB 2 _ _ 0%nat 40%nat _ eq_refl eq_refl ltac:(cbn; tauto) A40 (Dat 49%nat _ A49) ltac:(lia)) as M2.
pose proof (NB 2 _ _ 1%nat 41%nat _ eq_refl eq_refl ltac:(cbn; tauto) A41 (Dat 46%nat _ A46) ltac:(lia)) as N2.
pose proof (NB 1 _ _ 1%nat 41%nat _ eq_refl eq_refl ltac:(cbn; tauto) A41 (denot_pack2_hi Ev 45 44 _ _ D45 D44 ltac:(lia) ltac:(lia)) ltac:(lia)) as N1.
pose proof (NB 0 _ _ 1%nat 41%nat _ eq_refl eq_refl ltac:(cbn; tauto) A41 (denot_pack2_lo Ev 45 44 _ _ D45 D44 ltac:(lia) ltac:(lia)) ltac:(lia)) as N0.
pose proof (st_chunk_val segs Ev ss_SW_out ms 2%nat _ 42%nat 0 4%N _ _ _ HS eq_refl eq_refl ltac:(cbn; tauto) A42 (denot_sext32_small Ev 51 _ D51 Rk) ltac:(cbn; lia) ltac:(cbn; lia)) as W1.
pose proof (st_chunk_val segs Ev ss_SW_out ms 3%nat _ 43%nat 0 4%N _ _ _ HS eq_refl eq_refl ltac:(cbn; tauto) A43 (denot_sext32_small Ev 50 _ D50 Ri) ltac:(cbn; lia) ltac:(cbn; lia)) as W2.
change (N.to_nat 4) with 4%nat in W1, W2. rewrite Z.add_0_r in M0, N0, W1, W2.
apply HK.
- exact HJ.
- apply (arr8_eswap segs mem (ms_mem ms) p E tail i1 k1 Hpa HE ltac:(lia) ltac:(lia) Hik).
+ intros x Hx Hn1 Hn2. mb_frame_g HF ltac:(lia) ltac:(rewrite ?A40, ?A41, ?A42, ?A43, ?HU2; unfold disj_blocks in Hdisj; lia). reflexivity.
+ intros d Hd. assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]]; [rewrite !Z.add_0_r; exact M0 | exact M1 | exact M2].
+ intros d Hd. assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]]; [rewrite !Z.add_0_r; exact N0 | exact N1 | exact N2].
- apply (arr32_eswap segs mem (ms_mem ms) fdp E i1 k1 Hfa ltac:(lia) ltac:(lia) Hik).
+ intros x Hx Hn1 Hn2. mb_frame_g HF ltac:(lia) ltac:(rewrite ?A40, ?A41, ?A42, ?A43, ?HU2; unfold disj_blocks in Hdisj; lia). reflexivity.
+ exact W1.
+ exact W2.
- intros x Hx Hn1 Hn2 Hn3. mb_frame_g HF ltac:(exact Hx) ltac:(rewrite ?A40, ?A41, ?A42, ?A43, ?HU2; lia). reflexivity.
- jreg HS (23%bv:reg) as Hq19. rewrite Hq19, HU2. reflexivity.
- exact (regs_kept_of_st_ok _ _ _ _ regs _ SW_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Lemma val_mem_frame : forall (m m' : word -> option byte) a n v,
val_mem segs m a n v -> (forall i, 0 <= i < Z.of_nat n -> mbyte segs m' (a + i) = mbyte segs m (a + i)) -> val_mem segs m' a n v.
Proof. intros m m' a n v H Hf k Hk. rewrite Hf by lia. apply H. exact Hk. Qed.
Lemma keep_sub : forall (l L : list reg) (f g : reg -> word),
forallb (fun r => existsb (bv_eqb r) L) l = true ->
(forall r, In r L -> f r = g r) -> forall r, In r l -> f r = g r.
Proof.
intros l L f g Hs H r Hr. apply H. pose proof (proj1 (forallb_forall _ _) Hs r Hr) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin.
Qed.
Section h.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (L : layout) (A : astate) (mem0 : word -> option byte) (md0 : Model).
Variables (Lc : layout) (Ac : astate) (md : Model).
Variables (p fdp sp T a lo hi cut mean : Z) (Ep : list entry) (tail : list Z).
Let l := dseg cut Ep lo hi.
Let P := Ptest cut (wsum l) (wdot l).
Let cnt := elen Ep.
Hypothesis Hpn0 : ~ In (p, 3 * T) (blocks L A).
Hypothesis Hfn0 : ~ In (fdp, 4 * cnt) (blocks L A).
Hypothesis Hlen : 3 * cnt + zlen tail = 3 * T.
Hypothesis HEp : ent_ok Ep.
Hypothesis Hf31 : Forall (fun e => snd e < 2 ^ 31) Ep.
Hypothesis Hpf : disj_blocks p (3 * T) fdp (4 * cnt).
Hypothesis Hcnt : cnt < 2 ^ 29.
Hypothesis Hlohi : 0 <= lo /\ lo < hi /\ hi < cnt.
Hypothesis Hcut : 0 <= cut <= 2.
Hypothesis Hmean : 0 <= mean < 2 ^ 64.
Hypothesis Hq : is_quot mean (wdot l) (wsum l).
Hypothesis Hwin : sp0 - STK <= sp + 5028 /\ sp + 5136 <= sp0 /\ sp mod 16 = 0.
Hypothesis Ha : 4096 <= a /\ a + 56 <= alloc_ceiling /\ a mod 8 = 0.
Hypothesis HaN : forall x, 0 <= x < 56 ->
~ (p <= a + x < p + 3 * cnt) /\ ~ (fdp <= a + x < fdp + 4 * cnt) /\ ~ (sp + 5028 <= a + x < sp + 5031).
Definition at_PR (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (E : list entry) (i k : Z) : Prop :=
journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem md /\ frm_zero (@fp_csr fy) /\
In (p, 3 * T) (blocks Lc Ac) /\ In (fdp, 4 * cnt) (blocks Lc Ac) /\
getr regs 2 = Z_to_bv 64 sp /\ getr regs 27 = Z_to_bv 64 a /\ getr regs 12 = Z_to_bv 64 (a + 16) /\
getr regs 26 = Z_to_bv 64 i /\ getr regs 10 = Z_to_bv 64 k /\ getr regs 25 = Z_to_bv 64 p /\ getr regs 24 = Z_to_bv 64 fdp /\
getr regs 23 = Z_to_bv 64 (sp + 5028) /\
arr8 segs mem p (pal_bytes E ++ tail) /\ arr32 segs mem fdp (fr_vals E) /\
val_mem segs mem (a + 48) 1 cut /\ val_mem segs mem (a + 16 + 8 * cut) 8 mean /\ val_mem segs mem (a + 40) 4 lo /\
pinv dentry P lo hi Ep E i k.
Definition K_SPLIT (regs : bvmap 5 word) (mem : word -> option byte) (Q : config -> Prop) : Prop :=
forall (fy' : FPState) regs' mem' E' i',
frm_zero (@fp_csr fy') -> journal src2_msyms MR STK sp0 FP L A mem0 md0 Lc Ac mem' md ->
pdone dentry P lo hi Ep E' i' ->
getr regs' 13 = Z_to_bv 64 lo -> getr regs' 26 = Z_to_bv 64 i' -> getr regs' 12 = Z_to_bv 64 (a + 16) -> getr regs' 23 = Z_to_bv 64 (sp + 5028) ->
(forall r : reg, In r PART_KEEP -> getr regs' r = getr regs r) ->
arr8 segs mem' p (pal_bytes E' ++ tail) -> arr32 segs mem' fdp (fr_vals E') ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (p <= x < p + 3 * cnt) -> ~ (fdp <= x < fdp + 4 * cnt) -> ~ (sp + 5028 <= x < sp + 5031) ->
mbyte segs mem' x = mbyte segs mem x) ->
SR segs (mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_SPLIT) mem' rom) md) Q.
Lemma ptest_of_smallb : forall E x, Permutation Ep E -> 0 <= x < cnt ->
ptest (pal_bytes E ++ tail) cut (wsum l) (wdot l) x = smallb dentry P E x.
Proof.
intros E x HP Hx. symmetry. apply smallb_ptest; [apply pal_agrees_app | lia |].
unfold cnt in Hx. unfold elen in *. rewrite <- (Permutation_length HP). exact Hx.
Qed.
Theorem partition_SR : forall n (fy : FPState) (regs : bvmap 5 word) mem E i k Q,
part_meas dentry P E i k < Z.of_nat n ->
at_PR fy regs mem E i k -> K_SPLIT regs mem Q ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_PR) mem rom) md) Q.
Proof.
induction n as [|n IH]; intros fy regs mem E i k Q Hn HAT HK.
{ exfalso. destruct HAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PI). pose proof (pinv_meas_bound dentry P _ _ _ _ _ _ PI). lia. }
destruct HAT as (HJ & Hfrm & Hpin & Hfin & G2 & G18 & G12 & G9 & G10 & G22 & G27 & G19 & Hpa & Hfa & Vcut & Vmean & Vlo & PI).
pose proof HJ as (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. destruct Hwin as (Hw1 & Hw2 & Hw3). destruct Ha as (Ha1 & Ha2 & Ha3).
destruct Hlohi as (Hlo0 & Hlh & Hhc). assert (Htl : 0 <= zlen tail) by (unfold zlen; lia).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md p (3 * T) HH Hpin ltac:(lia)) as (Hp0 & Hp1 & _).
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac mem md fdp (4 * cnt) HH Hfin ltac:(lia)) as (Hq0 & Hq1 & _).
pose proof PI as (PIik & PIk & _ & PIhi & PIlen & PIperm & _).
assert (HlenE : elen E = cnt) by (unfold cnt, elen in *; rewrite PIlen; reflexivity).
destruct (part_round_spec dentry P lo hi Ep E i k PI) as (i' & k' & _ & _ & Hi' & Hk' & Sbig & Ssmall & Sup & Sdn & Hcase).
destruct (PR_to_SU fy regs mem a i cut mean G18 G12 G9 ltac:(lia) ltac:(lia) ltac:(lia) Ha3 Hcut Hmean Vcut Vmean Hfrm)
as (fy1 & regs1 & Hms1 & Hfrm1 & Hf1 & R13 & R14 & R9 & R12 & K1).
destruct (heap_model _ _ LAWS _ _ _ _ HH) as (Hh & Hlz & _).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms1).
assert (HpaZ : 3 * i' + cut < zlen (pal_bytes E ++ tail)) by (rewrite zlen_app_pal; lia).
destruct (SU_loop (Z.to_nat (i' - i)) fy1 regs1 mem i i' cut p mean (wsum l) (wdot l) k (pal_bytes E ++ tail)
ltac:(lia) ltac:(lia) ltac:(lia) Hpa HpaZ ltac:(lia) ltac:(rewrite zlen_app_pal; lia)
ltac:(intros z Hz; rewrite (ptest_of_smallb E z PIperm ltac:(lia)); apply Sup; lia)
ltac:(rewrite (ptest_of_smallb E i' PIperm ltac:(lia)); exact Sbig)
Hcut Hfrm1 Hf1 Hmean Hq R13 R14 R9 ltac:(rewrite (K1 25%bv ltac:(inl)); exact G22)
ltac:(rewrite (K1 10%bv ltac:(inl)); exact G10) ltac:(lia))
as (fy2 & regs2 & Hms2 & Hfrm2 & Hf2 & S13 & S14 & S9 & S22 & S15 & S10 & K2).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms2).
assert (HpaZ' : 3 * k + cut < zlen (pal_bytes E ++ tail)) by (rewrite zlen_app_pal; lia).
destruct (SD_loop (Z.to_nat (k - k')) fy2 regs2 mem k k' cut p mean (wsum l) (wdot l) (pal_bytes E ++ tail)
ltac:(lia) ltac:(lia) ltac:(lia) Hpa HpaZ' ltac:(lia) ltac:(rewrite zlen_app_pal; lia)
ltac:(intros z Hz; rewrite (ptest_of_smallb E z PIperm ltac:(lia)); apply Sdn; lia)
ltac:(rewrite (ptest_of_smallb E k' PIperm ltac:(lia)); exact Ssmall)
Hcut Hfrm2 Hf2 Hmean Hq S13 S15 ltac:(rewrite S10; reflexivity) S22)
as (fy3 & regs3 & Hms3 & Hfrm3 & T13 & T15 & T10 & T22 & K3).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms3).
assert (C3 : forall r : reg, In r CARRY3 -> getr regs3 r = getr regs1 r).
{ intros r Hr. rewrite (keep_sub CARRY3 SD_KEEP _ _ ltac:(vm_compute; reflexivity) K3 r Hr). apply (keep_sub CARRY3 SUX_KEEP _ _ ltac:(vm_compute; reflexivity) K2 r Hr). }
assert (C1 : forall r : reg, In r CARRY1 -> getr regs1 r = getr regs r).
{ intros r Hr. apply (keep_sub CARRY1 PRA_KEEP _ _ ltac:(vm_compute; reflexivity) K1 r Hr). }
assert (T9 : getr regs3 26 = Z_to_bv 64 i') by (rewrite (K3 26%bv ltac:(inl)); exact S9).
assert (T14 : getr regs3 14 = Z_to_bv 64 (3 * i')) by (rewrite (K3 14%bv ltac:(inl)); exact S14).
assert (T18 : getr regs3 27 = Z_to_bv 64 a) by (rewrite (C3 27%bv ltac:(inl)), (C1 27%bv ltac:(inl)); exact G18).
assert (T2 : getr regs3 2 = Z_to_bv 64 sp) by (rewrite (C3 2%bv ltac:(inl)), (C1 2%bv ltac:(inl)); exact G2).
assert (T27 : getr regs3 24 = Z_to_bv 64 fdp) by (rewrite (C3 24%bv ltac:(inl)), (C1 24%bv ltac:(inl)); exact G27).
assert (T19 : getr regs3 23 = Z_to_bv 64 (sp + 5028)) by (rewrite (C3 23%bv ltac:(inl)), (C1 23%bv ltac:(inl)); exact G19).
assert (T12 : getr regs3 12 = Z_to_bv 64 (a + 16)) by (rewrite (C3 12%bv ltac:(inl)); exact R12).
destruct Hcase as [(Hle & _ & Hk'eq & Hdone) | (Hlt & _ & PI' & Hmeas)].
-
destruct (BG_done fy3 regs3 mem a i' k' lo T18 T9 T10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ha3 ltac:(lia) Vlo)
as (regs4 & Hms4 & U13 & K4).
eapply (SR_msteps segs _ _ md _ Hh Hlz Hms4).
apply (HK fy3 regs4 mem E i' Hfrm3 HJ Hdone U13).
+ rewrite (K4 26%bv ltac:(inl)). exact T9.
+ rewrite (K4 12%bv ltac:(inl)). exact T12.
+ rewrite (K4 23%bv ltac:(inl)). exact T19.
+ intros r Hr. rewrite (keep_sub PART_KEEP BGD_KEEP _ _ ltac:(vm_compute; reflexivity) K4 r Hr).
rewrite (keep_sub PART_KEEP CARRY3 _ _ ltac:(vm_compute; reflexivity) C3 r Hr). apply (keep_sub PART_KEEP CARRY1 _ _ ltac:(vm_compute; reflexivity) C1 r Hr).
+ exact Hpa.
+ exact Hfa.
+ intros; reflexivity.
-
eapply (SW_stretch fy3 regs3 mem STK sp0 FP L A mem0 md0 Lc Ac md E tail i' k' p fdp sp T _ HJ Hpin Hpn0);
[rewrite HlenE; exact Hfin | rewrite HlenE; exact Hfn0 | rewrite HlenE; exact Hpf | exact Hpa | rewrite HlenE; exact Hlen | exact Hfa
| exact (ent_ok_perm _ _ PIperm HEp) | exact (Permutation_Forall PIperm Hf31) | lia | exact Hlt | lia | lia | exact Hw1 | exact Hw2 | exact Hw3
| exact T2 | exact T14 | exact T15 | exact T10 | exact T9 | exact T22 | exact T27 | exact T19 | ].
intros regs5 mem5 HJ5 Hpa5 Hfa5 Hfr5 U19 K5.
apply (IH fy3 regs5 mem5 (eswap dentry E i' k') i' k' Q ltac:(lia)).
+ split; [exact HJ5|]. split; [exact Hfrm3|]. split; [exact Hpin|]. split; [exact Hfin|].
split; [rewrite (K5 2%bv ltac:(inl)); exact T2|]. split; [rewrite (K5 27%bv ltac:(inl)); exact T18|].
split; [rewrite (K5 12%bv ltac:(inl)); exact T12|]. split; [rewrite (K5 26%bv ltac:(inl)); exact T9|].
split; [rewrite (K5 10%bv ltac:(inl)); exact T10|]. split; [rewrite (K5 25%bv ltac:(inl)); exact T22|].
split; [rewrite (K5 24%bv ltac:(inl)); exact T27|]. split; [exact U19|].
split; [exact Hpa5|]. split; [exact Hfa5|].
assert (NF : forall i0, 0 <= i0 < 56 -> mbyte segs mem5 (a + i0) = mbyte segs mem (a + i0)).
{ intros i0 Hi0. destruct (HaN i0 Hi0) as (X1 & X2 & X3). apply Hfr5; [lia | rewrite HlenE; exact X1 | rewrite HlenE; exact X2 | exact X3]. }
split; [eapply val_mem_frame; [exact Vcut | intros; rewrite <- Z.add_assoc; apply NF; lia]|].
split; [eapply val_mem_frame; [exact Vmean | intros; rewrite <- !Z.add_assoc; apply NF; lia]|].
split; [eapply val_mem_frame; [exact Vlo | intros; rewrite <- Z.add_assoc; apply NF; lia]|].
exact PI'.
+ intros fy' regs' mem' E' i'' Hfrm' HJ' Hdone' W13 W9 W12 W19 K' Hpa' Hfa' Hfr'.
apply (HK fy' regs' mem' E' i'' Hfrm' HJ' Hdone' W13 W9 W12 W19); [| exact Hpa' | exact Hfa' |].
* intros r Hr. rewrite (K' r Hr). rewrite (keep_sub PART_KEEP SW_KEEP _ _ ltac:(vm_compute; reflexivity) K5 r Hr).
rewrite (keep_sub PART_KEEP CARRY3 _ _ ltac:(vm_compute; reflexivity) C3 r Hr). apply (keep_sub PART_KEEP CARRY1 _ _ ltac:(vm_compute; reflexivity) C1 r Hr).
* intros x Hx N1 N2 N3. rewrite (Hfr' x Hx N1 N2 N3). apply Hfr5; [exact Hx | rewrite HlenE; exact N1 | rewrite HlenE; exact N2 | exact N3].
Qed.
End h.
End J.
End c.
