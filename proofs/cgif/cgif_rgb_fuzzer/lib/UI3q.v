(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 YI00 YI02 YP14 YI0c YI0f YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_RH : Z := 0x14200.
Definition PC_SUL : Z := 0x14218.
Definition PC_SDE : Z := 0x1425c.
Definition PC_SDL : Z := 0x14278.
Definition PC_BG : Z := 0x142a8.
Definition SU_KEEP : list reg := [1; 2; 3; 4; 8; 9; 10; 11; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 27; 29; 30; 31]%bv.
Definition SD_KEEP : list reg := [1; 2; 3; 4; 6; 7; 8; 9; 10; 12; 13; 14; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma bne_bool_w : forall t : bool, branch_taken BC_NE (if t then w1 else w0) (Z_to_bv 64 0) = t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma fle_cvt_test : forall md (bw mw : word) (b mean s m : Z),
bw = Z_to_bv 64 b -> mw = Z_to_bv 64 mean -> 0 <= b < 256 -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
fpop2_denot (FP2_cmp F_LE FMT_D) (fpop1_denot (FP1_cvt FC_D FC_WU md) bw) mw = if b * s <=? m then w1 else w0.
Proof.
intros md bw mw b mean s m -> -> Hb Hm Hq. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
rewrite fp_arg_fcvt_d_wu, fp_arg_D, !unsigned_lit_small by lia.
rewrite (crawl_scan_le md b mean m s ltac:(lia) Hq). reflexivity.
Qed.
Lemma flt_cvt_test : forall md (bw mw : word) (b mean s m : Z),
bw = Z_to_bv 64 b -> mw = Z_to_bv 64 mean -> 0 <= b < 256 -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
fpop2_denot (FP2_cmp F_LT FMT_D) mw (fpop1_denot (FP1_cvt FC_D FC_WU md) bw) = if b * s <=? m then w0 else w1.
Proof.
intros md bw mw b mean s m -> -> Hb Hm Hq. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
rewrite fp_arg_fcvt_d_wu, fp_arg_D, !unsigned_lit_small by lia.
rewrite (crawl_scan_gt md b mean m s ltac:(lia) Hq).
destruct (Z.leb_spec (b * s) m); destruct (Z.ltb_spec m (b * s)); try reflexivity; lia.
Qed.
Lemma val_mem_of_byte : forall segs m a v, mbyte segs m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem segs m a 1 v.
Proof.
intros segs m a v H Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Notation segs := ubs2segs (only parsing).
Local Notation rom := (seg_rom ubs2segs) (only parsing).
Definition PC_FLD : Z := 0x14228.
Definition SA_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma SU_SA : forall r : reg, In r SU_KEEP -> In r SA_KEEP.
Proof.
intros r H. cbv [SU_KEEP In] in H. cbv [SA_KEEP In].
repeat (destruct H as [<-|H]; [repeat (first [left; reflexivity | right]) |]). destruct H.
Qed.
Ltac ridx_of HE := intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia.
Lemma beq_bool_w : forall t : bool, branch_taken BC_EQ (if t then w1 else w0) (Z_to_bv 64 0) = negb t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma beq_bool_w_neg : forall t : bool, branch_taken BC_EQ (if t then w0 else w1) (Z_to_bv 64 0) = t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma bgeu_U : forall E a b, branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_ltu, U. reflexivity. Qed.
Lemma uat : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof.
intros E n v H Hv. rewrite U_SOff, H, Z.add_0_r. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ulit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
Lemma denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U. f_equal. exact H. Qed.
Lemma U_mul3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 40 -> U E (SMd M_MUL (SOff n 0) (SLit 3)) = 3 * v.
Proof.
intros E n v Hn Hv. rewrite U_SMd. cbn [zmd_raw]. rewrite (uat E n v Hn) by lia. rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_sll_k : forall E a k, 0 <= k < 64 -> U E (SAlu ALU_SLL a (SLit k)) = (U E a * 2 ^ k) mod 2 ^ 64.
Proof.
intros E a k Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite ulit by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma U_zext32_add : forall E a b,
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 32)) (SAlu ALU_SLL b (SLit 32))) (SLit 32)) = (U E a + U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_sll_k by lia. rewrite U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold zcanon, M64.
set (x := U E a) in *. set (y := U E b) in *.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite <- Zplus_mod. replace (x * 2 ^ 32 + y * 2 ^ 32) with ((x + y) * 2 ^ 32) by lia.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (x + y) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma zc_cut3 : forall cut, 0 <= cut <= 2 -> zcanon (cut - 3) = 2 ^ 64 + cut - 3.
Proof.
intros cut Hc. unfold zcanon, M64. replace (cut - 3) with (2 ^ 64 + cut - 3 + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma U_cut3 : forall E n cut, ew E n = Z_to_bv 64 (cut - 3) -> 0 <= cut <= 2 -> U E (SOff n 0) = 2 ^ 64 + cut - 3.
Proof.
intros E n cut Hn Hc. rewrite U_SOff, Hn, unsigned_lit, Z.add_0_r, (zc_cut3 cut Hc). apply zcanon_id. unfold M64. lia.
Qed.
Lemma mod32_cut3 : forall y cut, 1 <= y < 2 ^ 29 -> 0 <= cut <= 2 -> (2 ^ 64 + cut - 3 + 3 * y) mod 2 ^ 32 = 3 * (y - 1) + cut.
Proof.
intros y cut Hy Hc. replace (2 ^ 64 + cut - 3 + 3 * y) with (3 * (y - 1) + cut + 2 ^ 32 * 2 ^ 32) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Definition sul_at (regs : bvmap 5 word) (x a cut p : Z) : Prop :=
getr regs 5 = Z_to_bv 64 (8 * cut) /\ getr regs 6 = Z_to_bv 64 (a + 16 + 8 * cut) /\ getr regs 7 = Z_to_bv 64 (cut + 3) /\
getr regs 12 = Z_to_bv 64 (3 * x) /\ getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - (a + 16)) /\ getr regs 15 = Z_to_bv 64 cut /\
getr regs 16 = Z_to_bv 64 (3 * x) /\ getr regs 17 = Z_to_bv 64 (3 * x + cut) /\ getr regs 19 = Z_to_bv 64 2 /\
getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) /\ getr regs 25 = Z_to_bv 64 p /\ getr regs 26 = Z_to_bv 64 x.
Definition ss_RH0 : sstate :=
mkSS PC_RH sr_atoms [] None
(mkFacts [ (13%nat, mkAF 4112 CEIL_MAX 0); (15%nat, mkAF 0 2 0); (26%nat, mkAF 0 (2 ^ 29) 0) ] [] []).
Definition ss_RH : sstate := mkSST PC_RH (ss_regs ss_RH0) (sfr_atoms 48) (ss_mem ss_RH0) None (ss_facts ss_RH0).
Lemma RH_SUL : forall (fy : FPState) (regs : bvmap 5 word) mem (x a cut p : Z),
getr regs 15 = Z_to_bv 64 cut -> getr regs 13 = Z_to_bv 64 (a + 16) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - (a + 16)) ->
getr regs 26 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 (3 * x) -> getr regs 17 = Z_to_bv 64 (3 * x + cut) ->
getr regs 25 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 2 -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> 0 <= x < 2 ^ 29 -> frm_zero (@fp_csr fy) ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_RH) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SUL) mem rom) /\
frm_zero (@fp_csr fy') /\ sul_at regs' x a cut p /\ (forall r : reg, In r SU_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem x a cut p R15 R13 R14 R26 R12 R17 R25 R19 R23 Hcut Ha0 Ha1 Hx Hfrm.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E0 := Ereg regs []).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (U13 : bv_unsigned (ew E0 13) = a + 16) by (rewrite (HE0 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E0 15) = cut) by (rewrite (HE0 15%nat 15%bv eq_refl), R15; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E0 26) = x) by (rewrite (HE0 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_RH0 (@mkst fy regs (Z_to_bv 64 PC_RH) mem rom)).
{ unfold ss_RH0. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U13, U15, U26. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pose proof (st_ok_enterF segs fy 48 E0 ss_RH0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 48 (@fp_regs fy)) in HS.
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (E13 : ew E 13 = Z_to_bv 64 (a + 16)) by (rewrite (HE 13%nat 13%bv eq_refl); exact R13).
assert (E15 : ew E 15 = Z_to_bv 64 cut) by (rewrite (HE 15%nat 15%bv eq_refl); exact R15).
assert (E26 : ew E 26 = Z_to_bv 64 x) by (rewrite (HE 26%nat 26%bv eq_refl); exact R26).
pureF_to ubs2tbl_ok HS PC_SUL.
exists (fp_of ms), (ms_regs ms).
split; [rewrite Hsh in Hms; exact Hms|].
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [|exact (st_okF_regs_kept segs E _ _ regs SU_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity))].
pose proof (st_okF_reg segs E _ _ 5%bv HS) as Q5. eval_sr_get_in Q5.
pose proof (st_okF_reg segs E _ _ 6%bv HS) as Q6. eval_sr_get_in Q6.
pose proof (st_okF_reg segs E _ _ 12%bv HS) as Q12. eval_sr_get_in Q12.
jregF HS (7%bv:reg) as Q7. jregF HS (14%bv:reg) as Q14. jregF HS (15%bv:reg) as Q15. jregF HS (16%bv:reg) as Q16.
jregF HS (17%bv:reg) as Q17. jregF HS (19%bv:reg) as Q19. jregF HS (23%bv:reg) as Q23. jregF HS (25%bv:reg) as Q25.
jregF HS (26%bv:reg) as Q26.
unfold sul_at.
split. { rewrite Q5. apply denot_U. rewrite U_sll_k by lia. rewrite (uat E 15 cut E15) by lia. rewrite Z.mod_small by lia. lia. }
split. { rewrite Q6. apply denot_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_sll_k by lia.
rewrite (uat E 15 cut E15), (uat E 13 (a + 16) E13) by lia. rewrite (Z.mod_small (cut * 2 ^ 3)) by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
split. { rewrite Q7, E15, unsigned_lit_small by lia. reflexivity. }
split. { rewrite Q12. exact (denot_U E _ _ (U_mul3 E 26 x E26 ltac:(lia))). }
split. { rewrite Q14, (HE 14%nat 14%bv eq_refl). exact R14. }
split. { rewrite Q15. exact E15. }
split. { rewrite Q16, (HE 12%nat 12%bv eq_refl). exact R12. }
split. { rewrite Q17, (HE 17%nat 17%bv eq_refl). exact R17. }
split. { rewrite Q19, (HE 19%nat 19%bv eq_refl). exact R19. }
split. { rewrite Q23, (HE 23%nat 23%bv eq_refl). exact R23. }
split. { rewrite Q25, (HE 25%nat 25%bv eq_refl). exact R25. }
rewrite Q26. exact E26.
Qed.
Definition sa_alias : sv := SAlu ALU_ADD (SOff 25 0) (SOff 17 0).
Definition ss_SA0 : sstate :=
mkSS PC_SUL sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ] None
(mkFacts [ (5%nat, mkAF 0 16 0); (14%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4112) 0); (15%nat, mkAF 0 2 0);
(17%nat, mkAF 0 (3 * 2 ^ 29 + 2) 0); (19%nat, mkAF 2 2 0); (25%nat, mkAF 0 (2 ^ 48) 0); (33%nat, mkAF 0 255 0) ]
[] [(sa_alias, SOff 32%nat 0)]).
Definition ss_SA : sstate := mkSST PC_SUL (ss_regs ss_SA0) (sfr_atoms 48) (ss_mem ss_SA0) None (ss_facts ss_SA0).
Lemma SA_run : forall (fy : FPState) (regs : bvmap 5 word) mem (x a cut p b : Z),
sul_at regs x a cut p ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + (3 * x + cut)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 -> frm_zero (@fp_csr fy) ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SUL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_FLD) mem rom) /\
frm_zero (@fp_csr fy') /\ getr regs' 17 = Z_to_bv 64 b /\ (forall r : reg, In r SA_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem x a cut p b (R5 & R6 & R7 & R12 & R14 & R15 & R16 & R17 & R19 & R23 & R25 & R26) Hcut Ha0 Ha1 Hx Hp Hb Hbr Hfrm.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E0 := Ereg regs (map (Z_to_bv 64) [p + (3 * x + cut); b] ++ [])).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [p + (3 * x + cut); b] j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (U5 : bv_unsigned (ew E0 5) = 8 * cut) by (rewrite (HE0 5%nat 5%bv eq_refl), R5; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E0 14) = 2 ^ 64 - 1 - (a + 16)) by (rewrite (HE0 14%nat 14%bv eq_refl), R14; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E0 15) = cut) by (rewrite (HE0 15%nat 15%bv eq_refl), R15; apply unsigned_lit_small; lia).
assert (U17 : bv_unsigned (ew E0 17) = 3 * x + cut) by (rewrite (HE0 17%nat 17%bv eq_refl), R17; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = 2) by (rewrite (HE0 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E0 25) = p) by (rewrite (HE0 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (A32 : ew E0 32 = Z_to_bv 64 (p + (3 * x + cut))) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 b) by (apply (HV 1%nat); reflexivity).
assert (U32 : bv_unsigned (ew E0 32) = p + (3 * x + cut)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = b) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_SA0 (@mkst fy regs (Z_to_bv 64 PC_SUL) mem rom)).
{ unfold ss_SA0. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, U33; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. apply val_mem_of_byte; [exact Hb | exact Hbr].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U5, U14, U15, U17, U19, U25, U33. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold sa_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U25, U17, U32, !Z.add_0_r.
rewrite (zcanon_id p), (zcanon_id (3 * x + cut)) by (unfold M64; lia). reflexivity. }
pose proof (st_ok_enterF segs fy 48 E0 ss_SA0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 48 (@fp_regs fy)) in HS.
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
pureF_to ubs2tbl_ok HS PC_FLD.
exists (fp_of ms), (ms_regs ms).
split; [rewrite Hsh in Hms; exact Hms|].
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [|exact (st_okF_regs_kept segs E _ _ regs SA_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity))].
jregF HS (17%bv:reg) as Q17. rewrite Q17, HEE by lia. exact A33.
Qed.
Definition ss_SB0 : sstate :=
mkSS PC_FLD sr_atoms
[ YQ0b.mkRegion (Some 6%nat) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (7%nat, mkAF 3 5 0); (12%nat, mkAF 0 (3 * 2 ^ 29) 0); (17%nat, mkAF 0 255 0);
(23%nat, mkAF (2 ^ 64 - 1 - 2 ^ 48) (2 ^ 64 - 1) 0); (26%nat, mkAF 0 (2 ^ 29) 0) ] [] []).
Definition ss_SB : sstate := mkSST PC_FLD (ss_regs ss_SB0) (sfr_atoms 48) (ss_mem ss_SB0) None (ss_facts ss_SB0).
Definition ss_SB_br : sstate := Eval vm_compute in (fst (sym_runFN segs ubs2tbl FUEL ss_SB)).
Definition sb_cond : sv := SF2 (FP2_cmp F_LE FMT_D) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 17 0)) (SOff 32 0).
Lemma SB_run1 : sym_runFN segs ubs2tbl FUEL ss_SB = (ss_SB_br, RS_stopped (SR_branch BC_EQ sb_cond (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma SB_iter : forall (fy : FPState) (regs : bvmap 5 word) mem (x a cut p b mean s m : Z),
getr regs 6 = Z_to_bv 64 (a + 16 + 8 * cut) -> getr regs 7 = Z_to_bv 64 (cut + 3) -> getr regs 12 = Z_to_bv 64 (3 * x) ->
getr regs 17 = Z_to_bv 64 b -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) -> getr regs 26 = Z_to_bv 64 x ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 -> 0 <= b < 256 ->
val_mem segs mem (a + 16 + 8 * cut) 8 mean -> frm_zero (@fp_csr fy) -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
exists E ms1,
msteps segs (@mkst fy regs (Z_to_bv 64 PC_FLD) mem rom) ms1 /\ ms_mem ms1 = mem /\
st_okF segs E (add_cond ss_SB_br (mkAC (if b * s <=? m then BC_NE else BC_EQ) sb_cond (SLit 0))) ms1 /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\ ew E 32 = Z_to_bv 64 mean.
Proof.
intros fy regs mem x a cut p b mean s m R6 R7 R12 R17 R23 R26 Hcut Ha0 Ha1 Hx Hp Hbr Hmv Hfrm Hmean Hq.
pose proof (proj1 alloc_ceiling_val) as Hac.
set (E0 := Ereg regs (map (Z_to_bv 64) [mean] ++ [])).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [mean] j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (A32 : ew E0 32 = Z_to_bv 64 mean) by (apply (HV 0%nat); reflexivity).
assert (U6 : bv_unsigned (ew E0 6) = a + 16 + 8 * cut) by (rewrite (HE0 6%nat 6%bv eq_refl), R6; apply unsigned_lit_small; lia).
assert (U7 : bv_unsigned (ew E0 7) = cut + 3) by (rewrite (HE0 7%nat 7%bv eq_refl), R7; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E0 12) = 3 * x) by (rewrite (HE0 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; lia).
assert (U17 : bv_unsigned (ew E0 17) = b) by (rewrite (HE0 17%nat 17%bv eq_refl), R17; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E0 23) = 2 ^ 64 - 1 - p) by (rewrite (HE0 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E0 26) = x) by (rewrite (HE0 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_SB0 (@mkst fy regs (Z_to_bv 64 PC_FLD) mem rom)).
{ unfold ss_SB0. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U6.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact A32 | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Hmv.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U7, U12, U17, U23, U26. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pose proof (st_ok_enterF segs fy 48 E0 ss_SB0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 48 (@fp_regs fy)) in HS.
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
destruct (pure_stretchF segs ubs2tbl ubs2tbl_ok FUEL E ss_SB _ _ _ HS SB_run1 I ltac:(vm_compute; reflexivity) ltac:(reflexivity))
as (ms1 & Hms1 & HS1 & Hmem1 & _).
assert (H32 : ew E 32 = Z_to_bv 64 mean) by (rewrite HEE by lia; exact A32).
assert (H17 : ew E 17 = Z_to_bv 64 b) by (rewrite (HE 17%nat 17%bv eq_refl); exact R17).
exists E, ms1. split; [exact Hms1|]. split; [exact Hmem1|]. split; [|split; [exact HE | exact H32]].
assert (Hc : branch_taken BC_EQ (sv_denot E sb_cond) (sv_denot E (SLit 0)) = negb (b * s <=? m)).
{ unfold sb_cond. cbn [sv_denot]. rewrite !Z.add_0_r, H17, !Z_to_bv_bv_unsigned.
rewrite (fle_cvt_test RNE _ _ b mean s m eq_refl H32 Hbr Hmean Hq). apply beq_bool_w. }
destruct (b * s <=? m) eqn:Et; cbn [negb] in Hc.
- change BC_NE with (neg_bc BC_EQ). apply st_okF_add_cond_neg; [exact HS1 | exact Hc].
- apply st_okF_add_cond; [exact HS1 | exact Hc].
Qed.
Lemma SU_step : forall (fy : FPState) (regs : bvmap 5 word) mem (x a cut p b mean s m : Z),
sul_at regs x a cut p ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + (3 * x + cut)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
val_mem segs mem (a + 16 + 8 * cut) 8 mean -> frm_zero (@fp_csr fy) -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = true ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SUL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SUL) mem rom) /\
frm_zero (@fp_csr fy') /\ sul_at regs' (x + 1) a cut p /\ (forall r : reg, In r SU_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem x a cut p b mean s m HA Hcut Ha0 Ha1 Hx Hp Hb Hbr Hmv Hfrm Hmean Hq Ht.
pose proof HA as (G5 & G6 & G7 & G12 & G14 & G15 & G16 & G17 & G19 & G23 & G25 & G26).
destruct (SA_run fy regs mem x a cut p b HA Hcut Ha0 Ha1 Hx Hp Hb Hbr Hfrm) as (fy1 & regs1 & Hms1 & Hfrm1 & R17 & K1).
assert (KR : forall r : reg, In r SA_KEEP -> forall v, getr regs r = v -> getr regs1 r = v) by (intros r Hr v Hv; rewrite (K1 r Hr); exact Hv).
pose proof (KR 6%bv ltac:(cbv; tauto) _ G6) as R6. pose proof (KR 7%bv ltac:(cbv; tauto) _ G7) as R7.
pose proof (KR 12%bv ltac:(cbv; tauto) _ G12) as R12. pose proof (KR 23%bv ltac:(cbv; tauto) _ G23) as R23.
pose proof (KR 26%bv ltac:(cbv; tauto) _ G26) as R26.
destruct (SB_iter fy1 regs1 mem x a cut p b mean s m R6 R7 R12 R17 R23 R26 Hcut Ha0 Ha1 Hx Hp Hbr Hmv Hfrm1 Hmean Hq)
as (E & ms2 & Hms2 & Hmem2 & HS & HE & H32).
rewrite Ht in HS.
pureF_to ubs2tbl_ok HS PC_SUL.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem2 in Hms. exact (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms)). }
split; [exact (st_okF_frm segs E _ _ HS)|].
pose proof (st_okF_regs_kept segs E _ _ regs1 SU_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)) as K2.
split; [|intros r Hr; rewrite (K2 r Hr); exact (K1 r (SU_SA r Hr))].
assert (E7 : ew E 7 = Z_to_bv 64 (cut + 3)) by (rewrite (HE 7%nat 7%bv eq_refl); exact R7).
assert (E12 : ew E 12 = Z_to_bv 64 (3 * x)) by (rewrite (HE 12%nat 12%bv eq_refl); exact R12).
assert (E26 : ew E 26 = Z_to_bv 64 x) by (rewrite (HE 26%nat 26%bv eq_refl); exact R26).
pose proof (st_okF_reg segs E _ _ 16%bv HS) as Q16. eval_sr_get_in Q16.
pose proof (st_okF_reg segs E _ _ 17%bv HS) as Q17. eval_sr_get_in Q17.
jregF HS (5%bv:reg) as Q5. jregF HS (6%bv:reg) as Q6. jregF HS (7%bv:reg) as Q7. jregF HS (12%bv:reg) as Q12.
jregF HS (14%bv:reg) as Q14. jregF HS (15%bv:reg) as Q15. jregF HS (19%bv:reg) as Q19. jregF HS (23%bv:reg) as Q23.
jregF HS (25%bv:reg) as Q25. jregF HS (26%bv:reg) as Q26.
unfold sul_at.
split. { rewrite Q5, (HE 5%nat 5%bv eq_refl). exact (KR 5%bv ltac:(cbv; tauto) _ G5). }
split. { rewrite Q6, (HE 6%nat 6%bv eq_refl). exact R6. }
split. { rewrite Q7. exact E7. }
split. { rewrite Q12, E12, unsigned_lit_small by lia. f_equal; lia. }
split. { rewrite Q14, (HE 14%nat 14%bv eq_refl). exact (KR 14%bv ltac:(cbv; tauto) _ G14). }
split. { rewrite Q15, (HE 15%nat 15%bv eq_refl). exact (KR 15%bv ltac:(cbv; tauto) _ G15). }
split. { rewrite Q16. apply denot_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_mul3 E 26 x E26) by lia. rewrite ulit by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
split. { rewrite Q17. apply denot_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite (uat E 7 _ E7), (uat E 12 _ E12) by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
split. { rewrite Q19, (HE 19%nat 19%bv eq_refl). exact (KR 19%bv ltac:(cbv; tauto) _ G19). }
split. { rewrite Q23, (HE 23%nat 23%bv eq_refl). exact R23. }
split. { rewrite Q25, (HE 25%nat 25%bv eq_refl). exact (KR 25%bv ltac:(cbv; tauto) _ G25). }
rewrite Q26, E26, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma SU_exit : forall (fy : FPState) (regs : bvmap 5 word) mem (x a cut p b mean s m : Z),
sul_at regs x a cut p ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + (3 * x + cut)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
val_mem segs mem (a + 16 + 8 * cut) 8 mean -> frm_zero (@fp_csr fy) -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = false ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SUL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SDE) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 26 = Z_to_bv 64 x /\ getr regs' 12 = Z_to_bv 64 (3 * x) /\ getr regs' 16 = Z_to_bv 64 (3 * x) /\
(forall r : reg, In r SU_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem x a cut p b mean s m HA Hcut Ha0 Ha1 Hx Hp Hb Hbr Hmv Hfrm Hmean Hq Ht.
pose proof HA as (G5 & G6 & G7 & G12 & G14 & G15 & G16 & G17 & G19 & G23 & G25 & G26).
destruct (SA_run fy regs mem x a cut p b HA Hcut Ha0 Ha1 Hx Hp Hb Hbr Hfrm) as (fy1 & regs1 & Hms1 & Hfrm1 & R17 & K1).
assert (KR : forall r : reg, In r SA_KEEP -> forall v, getr regs r = v -> getr regs1 r = v) by (intros r Hr v Hv; rewrite (K1 r Hr); exact Hv).
pose proof (KR 6%bv ltac:(cbv; tauto) _ G6) as R6. pose proof (KR 7%bv ltac:(cbv; tauto) _ G7) as R7.
pose proof (KR 12%bv ltac:(cbv; tauto) _ G12) as R12. pose proof (KR 23%bv ltac:(cbv; tauto) _ G23) as R23.
pose proof (KR 26%bv ltac:(cbv; tauto) _ G26) as R26.
destruct (SB_iter fy1 regs1 mem x a cut p b mean s m R6 R7 R12 R17 R23 R26 Hcut Ha0 Ha1 Hx Hp Hbr Hmv Hfrm1 Hmean Hq)
as (E & ms2 & Hms2 & Hmem2 & HS & HE & H32).
rewrite Ht in HS.
pureF_to ubs2tbl_ok HS PC_SDE.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem2 in Hms. exact (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms)). }
split; [exact (st_okF_frm segs E _ _ HS)|].
split. { jfregF HS (15%bv:reg) as F15. exact (eq_trans F15 H32). }
pose proof (st_okF_regs_kept segs E _ _ regs1 SA_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)) as K2.
split; [rewrite (K2 26%bv ltac:(cbv; tauto)); exact R26|].
split; [rewrite (K2 12%bv ltac:(cbv; tauto)); exact R12|].
split; [rewrite (K2 16%bv ltac:(cbv; tauto)), (K1 16%bv ltac:(cbv; tauto)); exact G16|].
intros r Hr. rewrite (K2 r (SU_SA r Hr)). exact (K1 r (SU_SA r Hr)).
Qed.
Lemma SU_from : forall n (fy : FPState) (regs : bvmap 5 word) mem (x i1 a cut p mean s m : Z) (palc : list Z),
i1 - x <= Z.of_nat n -> 0 <= x <= i1 -> i1 < 2 ^ 29 ->
arr8 segs mem p palc -> 3 * i1 + cut < zlen palc -> 0 <= p -> p + zlen palc < 2 ^ 48 ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> val_mem segs mem (a + 16 + 8 * cut) 8 mean ->
frm_zero (@fp_csr fy) -> 0 <= mean < 2 ^ 64 -> is_quot mean m s -> sul_at regs x a cut p ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SUL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SDE) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 26 = Z_to_bv 64 i1 /\ getr regs' 12 = Z_to_bv 64 (3 * i1) /\ getr regs' 16 = Z_to_bv 64 (3 * i1) /\
(forall r : reg, In r SU_KEEP -> getr regs' r = getr regs r).
Proof.
induction n as [|n IH]; intros fy regs mem x i1 a cut p mean s m palc Hn Hx Hi1 Hpa Hlen Hp0 Hp1 Hsm Hbig Hcut Ha0 Ha1 Hmv Hfrm Hmean Hq HA.
- assert (x = i1) as -> by lia.
destruct (arr8_getz segs mem p palc (3 * i1 + cut) Hpa ltac:(lia)) as [Hb Hbr].
exact (SU_exit fy regs mem i1 a cut p _ mean s m HA Hcut Ha0 Ha1 ltac:(lia) ltac:(lia) Hb Hbr Hmv Hfrm Hmean Hq Hbig).
- destruct (Z.eq_dec x i1) as [->|Hne].
+ destruct (arr8_getz segs mem p palc (3 * i1 + cut) Hpa ltac:(lia)) as [Hb Hbr].
exact (SU_exit fy regs mem i1 a cut p _ mean s m HA Hcut Ha0 Ha1 ltac:(lia) ltac:(lia) Hb Hbr Hmv Hfrm Hmean Hq Hbig).
+ destruct (arr8_getz segs mem p palc (3 * x + cut) Hpa ltac:(lia)) as [Hb Hbr].
destruct (SU_step fy regs mem x a cut p _ mean s m HA Hcut Ha0 Ha1 ltac:(lia) ltac:(lia) Hb Hbr Hmv Hfrm Hmean Hq (Hsm x ltac:(lia)))
as (fy1 & regs1 & Hms1 & Hfrm1 & HA1 & K1).
destruct (IH fy1 regs1 mem (x + 1) i1 a cut p mean s m palc ltac:(lia) ltac:(lia) Hi1 Hpa Hlen Hp0 Hp1
ltac:(intros z Hz; apply Hsm; lia) Hbig Hcut Ha0 Ha1 Hmv Hfrm1 Hmean Hq HA1)
as (fy2 & regs2 & Hms2 & Hfrm2 & Hf2 & F26 & F12 & F16 & K2).
exists fy2, regs2. split; [exact (msteps_trans _ _ _ _ Hms1 Hms2)|].
repeat (split; [assumption|]). intros r Hr. rewrite (K2 r Hr). apply K1. exact Hr.
Qed.
Definition sdl_at (regs : bvmap 5 word) (y cut p : Z) : Prop :=
getr regs 5 = Z_to_bv 64 (3 * y + cut) /\ getr regs 11 = Z_to_bv 64 y /\ getr regs 15 = Z_to_bv 64 (cut - 3) /\
getr regs 17 = Z_to_bv 64 (3 * y) /\ getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) /\ getr regs 25 = Z_to_bv 64 p.
Definition ss_SE0 : sstate :=
mkSS PC_SDE sr_atoms [] None
(mkFacts [ (11%nat, mkAF 0 (2 ^ 29) 0); (15%nat, mkAF 0 2 0); (23%nat, mkAF (2 ^ 64 - 1 - 2 ^ 48) (2 ^ 64 - 1) 0);
(25%nat, mkAF 0 (2 ^ 48) 0) ] [] []).
Definition ss_SE : sstate := mkSST PC_SDE (ss_regs ss_SE0) (sfr_atoms 48) (ss_mem ss_SE0) None (ss_facts ss_SE0).
Lemma SE_SDL : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p mean : Z),
getr regs 11 = Z_to_bv 64 y -> getr regs 15 = Z_to_bv 64 cut -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) -> getr regs 25 = Z_to_bv 64 p ->
0 <= y < 2 ^ 29 -> 0 <= cut <= 2 -> 0 <= p < 2 ^ 48 -> frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SDE) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SDL) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\ sdl_at regs' y cut p /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem y cut p mean R11 R15 R23 R25 Hy Hcut Hp Hfrm Hf15.
set (E0 := Ereg regs []).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (U11 : bv_unsigned (ew E0 11) = y) by (rewrite (HE0 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E0 15) = cut) by (rewrite (HE0 15%nat 15%bv eq_refl), R15; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E0 23) = 2 ^ 64 - 1 - p) by (rewrite (HE0 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E0 25) = p) by (rewrite (HE0 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_SE0 (@mkst fy regs (Z_to_bv 64 PC_SDE) mem rom)).
{ unfold ss_SE0. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U11, U15, U23, U25. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
pose proof (st_ok_enterF segs fy 48 E0 ss_SE0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 48 (@fp_regs fy)) in HS.
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HEf : forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; subst E; apply ew_fregs_at).
assert (E11 : ew E 11 = Z_to_bv 64 y) by (rewrite (HE 11%nat 11%bv eq_refl); exact R11).
assert (E15 : ew E 15 = Z_to_bv 64 cut) by (rewrite (HE 15%nat 15%bv eq_refl); exact R15).
pureF_to ubs2tbl_ok HS PC_SDL.
exists (fp_of ms), (ms_regs ms).
split; [rewrite Hsh in Hms; exact Hms|].
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [cbn [fp_regs fp_of]; exact (eq_trans (st_okF_fregs_kept segs E _ _ 48 (@fp_regs fy) [15%bv] HS HEf ltac:(vm_compute; reflexivity) 15%bv ltac:(left; reflexivity)) Hf15)|].
split; [|exact (st_okF_regs_kept segs E _ _ regs SD_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity))].
pose proof (st_okF_reg segs E _ _ 5%bv HS) as Q5. eval_sr_get_in Q5.
pose proof (st_okF_reg segs E _ _ 17%bv HS) as Q17. eval_sr_get_in Q17.
jregF HS (11%bv:reg) as Q11. jregF HS (15%bv:reg) as Q15. jregF HS (23%bv:reg) as Q23. jregF HS (25%bv:reg) as Q25.
unfold sdl_at.
split. { rewrite Q5. apply denot_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_mul3 E 11 y E11), (uat E 15 cut E15) by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
split. { rewrite Q11. exact E11. }
split. { rewrite Q15, E15, unsigned_lit_small by lia. f_equal; lia. }
split. { rewrite Q17. exact (denot_U E _ _ (U_mul3 E 11 y E11 ltac:(lia))). }
split. { rewrite Q23, (HE 23%nat 23%bv eq_refl). exact R23. }
rewrite Q25, (HE 25%nat 25%bv eq_refl). exact R25.
Qed.
Definition sl_alias : sv := SAlu ALU_ADD (SOff 25 0) (SOff 5 0).
Definition ss_SL0 : sstate :=
mkSS PC_SDL sr_atoms
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ] None
(mkFacts [ (5%nat, mkAF 0 (3 * 2 ^ 29 + 2) 0); (11%nat, mkAF 0 (2 ^ 29) 0); (15%nat, mkAF (2 ^ 64 - 3) (2 ^ 64 - 1) 0);
(17%nat, mkAF 0 (3 * 2 ^ 29) 0); (23%nat, mkAF (2 ^ 64 - 1 - 2 ^ 48) (2 ^ 64 - 1) 0); (25%nat, mkAF 0 (2 ^ 48) 0);
(33%nat, mkAF 0 255 0) ] [] [(sl_alias, SOff 32%nat 0)]).
Definition ss_SL : sstate := mkSST PC_SDL (ss_regs ss_SL0) (sfr_atoms 48) (ss_mem ss_SL0) None (ss_facts ss_SL0).
Definition ss_SL_br : sstate := Eval vm_compute in (fst (sym_runFN segs ubs2tbl FUEL ss_SL)).
Definition sl_cond : sv := SF2 (FP2_cmp F_LT FMT_D) (SOff 63 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 33 0)).
Lemma SL_run1 : sym_runFN segs ubs2tbl FUEL ss_SL = (ss_SL_br, RS_stopped (SR_branch BC_EQ sl_cond (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition sl_t0 : sv := SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 32)) (SAlu ALU_SLL (SOff 17 0) (SLit 32))) (SLit 32).
Definition ss_SL_br2 : sstate := Eval vm_compute in (fst (sym_runFN segs ubs2tbl FUEL (add_cond ss_SL_br (mkAC BC_NE sl_cond (SLit 0))))).
Lemma SL_run2 : sym_runFN segs ubs2tbl FUEL (add_cond ss_SL_br (mkAC BC_NE sl_cond (SLit 0))) =
(ss_SL_br2, RS_stopped (SR_branch BC_GEU (SOff 23 0) sl_t0)).
Proof. vm_compute. reflexivity. Qed.
Lemma SL_iter : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b mean s m : Z),
sdl_at regs y cut p -> 0 <= cut <= 2 -> 0 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + (3 * y + cut)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
exists E ms1,
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SDL) mem rom) ms1 /\ ms_mem ms1 = mem /\
st_okF segs E (add_cond ss_SL_br (mkAC (if b * s <=? m then BC_EQ else BC_NE) sl_cond (SLit 0))) ms1 /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r).
Proof.
intros fy regs mem y cut p b mean s m (R5 & R11 & R15 & R17 & R23 & R25) Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq.
set (E0 := Ereg regs (map (Z_to_bv 64) [p + (3 * y + cut); b] ++ [])).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [p + (3 * y + cut); b] j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (U5 : bv_unsigned (ew E0 5) = 3 * y + cut) by (rewrite (HE0 5%nat 5%bv eq_refl), R5; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E0 11) = y) by (rewrite (HE0 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E0 15) = 2 ^ 64 + cut - 3) by (rewrite (HE0 15%nat 15%bv eq_refl), R15, unsigned_lit; apply zc_cut3; lia).
assert (U17 : bv_unsigned (ew E0 17) = 3 * y) by (rewrite (HE0 17%nat 17%bv eq_refl), R17; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E0 23) = 2 ^ 64 - 1 - p) by (rewrite (HE0 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E0 25) = p) by (rewrite (HE0 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (A32 : ew E0 32 = Z_to_bv 64 (p + (3 * y + cut))) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 b) by (apply (HV 1%nat); reflexivity).
assert (U32 : bv_unsigned (ew E0 32) = p + (3 * y + cut)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = b) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_SL0 (@mkst fy regs (Z_to_bv 64 PC_SDL) mem rom)).
{ unfold ss_SL0. subst E0. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, U33; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. apply val_mem_of_byte; [exact Hb | exact Hbr].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite U5, U11, U15, U17, U23, U25, U33. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold sl_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U25, U5, U32, !Z.add_0_r.
rewrite (zcanon_id p), (zcanon_id (3 * y + cut)) by (unfold M64; lia). reflexivity. }
pose proof (st_ok_enterF segs fy 48 E0 ss_SL0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs E0 48 (@fp_regs fy)) in HS.
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HEf : forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; subst E; apply ew_fregs_at).
destruct (pure_stretchF segs ubs2tbl ubs2tbl_ok FUEL E ss_SL _ _ _ HS SL_run1 I ltac:(vm_compute; reflexivity) ltac:(reflexivity))
as (ms1 & Hms1 & HS1 & Hmem1 & _).
exists E, ms1. split; [exact Hms1|]. split; [exact Hmem1|]. split; [|split; [exact HE | exact HEf]].
assert (Hc : branch_taken BC_EQ (sv_denot E sl_cond) (sv_denot E (SLit 0)) = (b * s <=? m)).
{ unfold sl_cond. cbn [sv_denot].
assert (H33 : ew E 33 = Z_to_bv 64 b) by (rewrite HEE by lia; exact A33).
assert (H63 : ew E 63 = Z_to_bv 64 mean) by (rewrite <- Hf15; exact (HEf (15%bv : reg))).
rewrite !Z.add_0_r, H33, !Z_to_bv_bv_unsigned.
rewrite (flt_cvt_test RNE _ _ b mean s m eq_refl H63 Hbr Hmean Hq). apply beq_bool_w_neg. }
destruct (b * s <=? m) eqn:Et.
- apply st_okF_add_cond; [exact HS1 | exact Hc].
- change BC_NE with (neg_bc BC_EQ). apply st_okF_add_cond_neg; [exact HS1 | exact Hc].
Qed.
Lemma SD_step : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b mean s m : Z),
sdl_at regs y cut p -> 0 <= cut <= 2 -> 1 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + (3 * y + cut)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = false ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SDL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SDL) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\ sdl_at regs' (y - 1) cut p /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem y cut p b mean s m HA Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq Ht.
pose proof HA as (R5 & R11 & R15 & R17 & R23 & R25).
destruct (SL_iter fy regs mem y cut p b mean s m HA Hcut ltac:(lia) Hp Hb Hbr Hfrm Hf15 Hmean Hq) as (E & ms1 & Hms1 & Hmem1 & HS & HE & HEf).
rewrite Ht in HS.
destruct (pure_stretchF segs ubs2tbl ubs2tbl_ok FUEL E (add_cond ss_SL_br (mkAC BC_NE sl_cond (SLit 0))) _ _ _ HS SL_run2 I
ltac:(vm_compute; reflexivity) ltac:(reflexivity)) as (ms2 & Hms2 & HS2 & Hmem2 & _).
assert (E11 : ew E 11 = Z_to_bv 64 y) by (rewrite (HE 11%nat 11%bv eq_refl); exact R11).
assert (E15 : ew E 15 = Z_to_bv 64 (cut - 3)) by (rewrite (HE 15%nat 15%bv eq_refl); exact R15).
assert (E17 : ew E 17 = Z_to_bv 64 (3 * y)) by (rewrite (HE 17%nat 17%bv eq_refl); exact R17).
assert (E23 : ew E 23 = Z_to_bv 64 (2 ^ 64 - 1 - p)) by (rewrite (HE 23%nat 23%bv eq_refl); exact R23).
assert (UT : U E sl_t0 = 3 * (y - 1) + cut).
{ unfold sl_t0. rewrite U_zext32_add, (U_cut3 E 15 cut E15 Hcut), (uat E 17 (3 * y) E17) by lia. apply mod32_cut3; lia. }
assert (Hg : branch_taken BC_GEU (sv_denot E (SOff 23 0)) (sv_denot E sl_t0) = true).
{ rewrite bgeu_U, UT, (uat E 23 _ E23) by lia.
destruct (Z.ltb_spec (2 ^ 64 - 1 - p) (3 * (y - 1) + cut)) as [Hl|Hl]; [exfalso; lia | reflexivity]. }
pose proof (st_okF_add_cond segs E _ _ BC_GEU (SOff 23 0) sl_t0 HS2 Hg) as HS3.
pureF_to ubs2tbl_ok HS3 PC_SDL.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem2, Hmem1 in Hms. exact (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms)). }
split; [exact (st_okF_frm segs E _ _ HS3)|].
split; [cbn [fp_regs fp_of]; exact (eq_trans (st_okF_fregs_kept segs E _ _ 48 (@fp_regs fy) [15%bv] HS3 HEf ltac:(vm_compute; reflexivity) 15%bv ltac:(left; reflexivity)) Hf15)|].
split; [|exact (st_okF_regs_kept segs E _ _ regs SD_KEEP HS3 ltac:(ridx_of HE) ltac:(vm_compute; reflexivity))].
pose proof (st_okF_reg segs E _ _ 5%bv HS3) as Q5. eval_sr_get_in Q5.
jregF HS3 (11%bv:reg) as Q11. jregF HS3 (15%bv:reg) as Q15. jregF HS3 (17%bv:reg) as Q17. jregF HS3 (23%bv:reg) as Q23.
jregF HS3 (25%bv:reg) as Q25.
unfold sdl_at.
split. { rewrite Q5. apply denot_U. exact UT. }
split. { rewrite Q11, E11, unsigned_lit_small by lia. f_equal; lia. }
split. { rewrite Q15. exact E15. }
split. { rewrite Q17, E17, unsigned_lit_small by lia. f_equal; lia. }
split. { rewrite Q23. exact E23. }
rewrite Q25, (HE 25%nat 25%bv eq_refl). exact R25.
Qed.
Lemma SD_exit : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b mean s m : Z),
sdl_at regs y cut p -> 0 <= cut <= 2 -> 0 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + (3 * y + cut)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = true ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SDL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_BG) mem rom) /\
frm_zero (@fp_csr fy') /\ getr regs' 11 = Z_to_bv 64 y /\ getr regs' 17 = Z_to_bv 64 (3 * y) /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem y cut p b mean s m HA Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq Ht.
pose proof HA as (R5 & R11 & R15 & R17 & R23 & R25).
destruct (SL_iter fy regs mem y cut p b mean s m HA Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq) as (E & ms1 & Hms1 & Hmem1 & HS & HE & HEf).
rewrite Ht in HS.
pureF_to ubs2tbl_ok HS PC_BG.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem1 in Hms. exact (msteps_trans _ _ _ _ Hms1 Hms). }
split; [exact (st_okF_frm segs E _ _ HS)|].
jregF HS (11%bv:reg) as Q11. jregF HS (17%bv:reg) as Q17.
split; [rewrite Q11, (HE 11%nat 11%bv eq_refl); exact R11|].
split; [rewrite Q17, (HE 17%nat 17%bv eq_refl); exact R17|].
exact (st_okF_regs_kept segs E _ _ regs SD_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)).
Qed.
Lemma SD_from : forall n (fy : FPState) (regs : bvmap 5 word) mem (y k1 cut p mean s m : Z) (palc : list Z),
y - k1 <= Z.of_nat n -> 0 <= k1 <= y -> y < 2 ^ 29 ->
arr8 segs mem p palc -> 3 * y + cut < zlen palc -> 0 <= p -> p + zlen palc < 2 ^ 48 ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
0 <= cut <= 2 -> frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
sdl_at regs y cut p ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SDL) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_BG) mem rom) /\
frm_zero (@fp_csr fy') /\ getr regs' 11 = Z_to_bv 64 k1 /\ getr regs' 17 = Z_to_bv 64 (3 * k1) /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
induction n as [|n IH]; intros fy regs mem y k1 cut p mean s m palc Hn Hy Hy1 Hpa Hlen Hp0 Hp1 Hbg Hsm Hcut Hfrm Hf15 Hmean Hq HA.
- assert (y = k1) as -> by lia.
destruct (arr8_getz segs mem p palc (3 * k1 + cut) Hpa ltac:(lia)) as [Hb Hbr].
exact (SD_exit fy regs mem k1 cut p _ mean s m HA Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq Hsm).
- destruct (Z.eq_dec y k1) as [->|Hne].
+ destruct (arr8_getz segs mem p palc (3 * k1 + cut) Hpa ltac:(lia)) as [Hb Hbr].
exact (SD_exit fy regs mem k1 cut p _ mean s m HA Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq Hsm).
+ destruct (arr8_getz segs mem p palc (3 * y + cut) Hpa ltac:(lia)) as [Hb Hbr].
destruct (SD_step fy regs mem y cut p _ mean s m HA Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq (Hbg y ltac:(lia)))
as (fy1 & regs1 & Hms1 & Hfrm1 & Hf1 & HA1 & K1).
destruct (IH fy1 regs1 mem (y - 1) k1 cut p mean s m palc ltac:(lia) ltac:(lia) ltac:(lia) Hpa ltac:(lia) Hp0 Hp1
ltac:(intros z Hz; apply Hbg; lia) Hsm Hcut Hfrm1 Hf1 Hmean Hq HA1)
as (fy2 & regs2 & Hms2 & Hfrm2 & F11 & F17 & K2).
exists fy2, regs2. split; [exact (msteps_trans _ _ _ _ Hms1 Hms2)|].
repeat (split; [assumption|]). intros r Hr. rewrite (K2 r Hr). apply K1. exact Hr.
Qed.
Lemma SU_loop : forall n (fy : FPState) (regs : bvmap 5 word) mem (x i1 a cut p mean s m : Z) (palc : list Z),
i1 - x <= Z.of_nat n -> 0 <= x <= i1 -> i1 < 2 ^ 29 ->
arr8 segs mem p palc -> 3 * i1 + cut < zlen palc -> 0 <= p -> p + zlen palc < 2 ^ 48 ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
0 <= cut <= 2 -> 4096 <= a -> a + 56 <= alloc_ceiling -> val_mem segs mem (a + 16 + 8 * cut) 8 mean ->
frm_zero (@fp_csr fy) -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
getr regs 15 = Z_to_bv 64 cut -> getr regs 13 = Z_to_bv 64 (a + 16) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - (a + 16)) ->
getr regs 26 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 (3 * x) -> getr regs 17 = Z_to_bv 64 (3 * x + cut) ->
getr regs 25 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 2 -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_RH) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SDE) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 26 = Z_to_bv 64 i1 /\ getr regs' 12 = Z_to_bv 64 (3 * i1) /\ getr regs' 16 = Z_to_bv 64 (3 * i1) /\
(forall r : reg, In r SU_KEEP -> getr regs' r = getr regs r).
Proof.
intros n fy regs mem x i1 a cut p mean s m palc Hn Hx Hi1 Hpa Hlen Hp0 Hp1 Hsm Hbig Hcut Ha0 Ha1 Hmv Hfrm Hmean Hq
R15 R13 R14 R26 R12 R17 R25 R19 R23.
destruct (RH_SUL fy regs mem x a cut p R15 R13 R14 R26 R12 R17 R25 R19 R23 Hcut Ha0 Ha1 ltac:(lia) Hfrm)
as (fy1 & regs1 & Hms1 & Hfrm1 & HA & K1).
destruct (SU_from n fy1 regs1 mem x i1 a cut p mean s m palc Hn Hx Hi1 Hpa Hlen Hp0 Hp1 Hsm Hbig Hcut Ha0 Ha1 Hmv Hfrm1 Hmean Hq HA)
as (fy2 & regs2 & Hms2 & Hfrm2 & Hf2 & G26 & G12 & G16 & K2).
exists fy2, regs2. split; [exact (msteps_trans _ _ _ _ Hms1 Hms2)|].
repeat (split; [assumption|]). intros r Hr. rewrite (K2 r Hr). exact (K1 r Hr).
Qed.
Lemma SD_loop : forall n (fy : FPState) (regs : bvmap 5 word) mem (y k1 cut p mean s m : Z) (palc : list Z),
y - k1 <= Z.of_nat n -> 0 <= k1 <= y -> y < 2 ^ 29 ->
arr8 segs mem p palc -> 3 * y + cut < zlen palc -> 0 <= p -> p + zlen palc < 2 ^ 48 ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
0 <= cut <= 2 -> frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
getr regs 15 = Z_to_bv 64 cut -> getr regs 11 = Z_to_bv 64 y -> getr regs 25 = Z_to_bv 64 p -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - p) ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SDE) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_BG) mem rom) /\
frm_zero (@fp_csr fy') /\ getr regs' 11 = Z_to_bv 64 k1 /\ getr regs' 17 = Z_to_bv 64 (3 * k1) /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
intros n fy regs mem y k1 cut p mean s m palc Hn Hy Hy1 Hpa Hlen Hp0 Hp1 Hbg Hsm Hcut Hfrm Hf15 Hmean Hq R15 R11 R25 R23.
destruct (SE_SDL fy regs mem y cut p mean R11 R15 R23 R25 ltac:(lia) Hcut ltac:(lia) Hfrm Hf15) as (fy1 & regs1 & Hms1 & Hfrm1 & Hf1 & HA & K1).
destruct (SD_from n fy1 regs1 mem y k1 cut p mean s m palc Hn Hy Hy1 Hpa Hlen Hp0 Hp1 Hbg Hsm Hcut Hfrm1 Hf1 Hmean Hq HA)
as (fy2 & regs2 & Hms2 & Hfrm2 & F11 & F17 & K2).
exists fy2, regs2. split; [exact (msteps_trans _ _ _ _ Hms1 Hms2)|].
split; [exact Hfrm2|]. split; [exact F11|]. split; [exact F17|].
intros r Hr. rewrite (K2 r Hr). exact (K1 r Hr).
Qed.
End c.
