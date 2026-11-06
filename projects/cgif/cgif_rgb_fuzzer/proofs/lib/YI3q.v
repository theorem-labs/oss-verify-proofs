(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YI00 YI02 YP14 YI0c YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_SU : Z := 0x13e00.
Definition PC_SD : Z := 0x13e38.
Definition PC_BG : Z := 0x13e60.
Definition SU_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition SUX_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition SD_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
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
Local Notation segs := src2segs (only parsing).
Local Notation rom := (seg_rom src2segs) (only parsing).
Definition su_alias : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SOff 14 0)) (SOff 25 0).
Definition ss_SU0 : sstate :=
mkSS PC_SU (sr_set sr_atoms 26%bv (SOff 32%nat (-1)))
[ YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ] None
(mkFacts [ (13%nat, mkAF 0 2 0); (14%nat, mkAF 0 (2^31) 0); (25%nat, mkAF 0 (2^48) 0); (32%nat, mkAF 0 (2^30) 0); (34%nat, mkAF 0 255 0) ]
[] [(su_alias, SOff 33%nat 0)]).
Definition ss_SU : sstate := mkSST PC_SU (ss_regs ss_SU0) (sfr_atoms 48) (ss_mem ss_SU0) None (ss_facts ss_SU0).
Lemma SU_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (x cut p b : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 14 = Z_to_bv 64 (3 * x) -> getr regs 26 = Z_to_bv 64 (x - 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * x + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) ->
let E0 := Ereg regs (map (Z_to_bv 64) [x; p + 3 * x + cut; b] ++ []) in
let E := ew_fregs E0 48 (@fp_regs fy) in
st_okF segs E ss_SU (@mkst fy regs (Z_to_bv 64 PC_SU) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
ew E 32 = Z_to_bv 64 x /\ ew E 34 = Z_to_bv 64 b.
Proof.
intros fy regs mem x cut p b Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm E0 E.
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [x; p + 3 * x + cut; b] j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU13 : bv_unsigned (ew E0 13) = cut) by (rewrite (HE0 13%nat 13%bv eq_refl), Hr13; apply unsigned_lit_small; lia).
assert (HU14 : bv_unsigned (ew E0 14) = 3 * x) by (rewrite (HE0 14%nat 14%bv eq_refl), Hr14; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E0 25) = p) by (rewrite (HE0 25%nat 25%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (A32 : ew E0 32 = Z_to_bv 64 x) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 (p + 3 * x + cut)) by (apply (HV 1%nat); reflexivity).
assert (A34 : ew E0 34 = Z_to_bv 64 b) by (apply (HV 2%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E0 32) = x) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E0 33) = p + 3 * x + cut) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E0 34) = b) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_SU0 (@mkst fy regs (Z_to_bv 64 PC_SU) mem rom)).
{ unfold ss_SU0. subst E0. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |]. cbn [sv_denot]. rewrite HU32. exact Hr9.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. apply val_mem_of_byte; [exact Hb | exact Hbr].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU13, HU14, HU22, HU32, HU34. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold su_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, HU13, HU14, HU22, HU33, !Z.add_0_r.
rewrite (zcanon_id cut), (zcanon_id (3 * x)), (zcanon_id p) by (unfold M64; lia). rewrite (zcanon_id (cut + 3 * x)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia. }
split; [exact (st_ok_enterF segs fy 48 E0 ss_SU0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia. split; [exact A32 | exact A34].
Qed.
Definition ss_SU_br : sstate := Eval vm_compute in (fst (sym_runFN segs src2tbl FUEL ss_SU)).
Definition su_cond : sv := SF2 (FP2_cmp F_LE FMT_D) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 34 0)) (SOff 63 0).
Lemma SU_run1 : sym_runFN segs src2tbl FUEL ss_SU = (ss_SU_br, RS_stopped (SR_branch BC_NE su_cond (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma SU_iter : forall (fy : FPState) (regs : bvmap 5 word) mem (x cut p b mean s m : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 14 = Z_to_bv 64 (3 * x) -> getr regs 26 = Z_to_bv 64 (x - 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * x + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
exists E ms1,
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SU) mem rom) ms1 /\ ms_mem ms1 = mem /\
st_okF segs E (add_cond ss_SU_br (mkAC (if b * s <=? m then BC_NE else BC_EQ) su_cond (SLit 0))) ms1 /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
ew E 32 = Z_to_bv 64 x.
Proof.
intros fy regs mem x cut p b mean s m Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm Hf15 Hmean Hq.
destruct (SU_entry fy regs mem x cut p b Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm) as (HS & HE & HEf & A32 & A34).
set (E := ew_fregs _ 48 _) in HS, HE, HEf, A32, A34.
destruct (pure_stretchF segs src2tbl src2tbl_ok FUEL E ss_SU _ _ _ HS SU_run1 I ltac:(vm_compute; reflexivity) ltac:(reflexivity))
as (ms1 & Hms1 & HS1 & Hmem1 & _).
exists E, ms1. split; [exact Hms1|]. split; [exact Hmem1|]. split; [| split; [exact HE | split; [exact HEf | exact A32]]].
assert (Hc : branch_taken BC_NE (sv_denot E su_cond) (sv_denot E (SLit 0)) = (b * s <=? m)).
{ unfold su_cond. cbn [sv_denot]. rewrite !Z.add_0_r, A34, !Z_to_bv_bv_unsigned.
assert (H63 : ew E 63 = Z_to_bv 64 mean) by (rewrite <- Hf15; exact (HEf (15%bv : reg))).
rewrite (fle_cvt_test RNE _ _ b mean s m eq_refl H63 Hbr Hmean Hq). apply bne_bool_w. }
destruct (b * s <=? m) eqn:Et.
- apply st_okF_add_cond; [exact HS1 | exact Hc].
- change BC_EQ with (neg_bc BC_NE). apply st_okF_add_cond_neg; [exact HS1 | exact Hc].
Qed.
Lemma denot_mul3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 40 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * v).
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n v Hn) by lia. rewrite U_SLit. rewrite (zcanon_id 3) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Ltac ridx_of HE := intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia.
Lemma SU_step : forall (fy : FPState) (regs : bvmap 5 word) mem (x cut p b mean s m : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 14 = Z_to_bv 64 (3 * x) -> getr regs 26 = Z_to_bv 64 (x - 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * x + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = true ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SU) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SU) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 14 = Z_to_bv 64 (3 * (x + 1)) /\ getr regs' 26 = Z_to_bv 64 (x + 1 - 1) /\
getr regs' 25 = Z_to_bv 64 p /\
(forall r : reg, In r SU_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem x cut p b mean s m Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm Hf15 Hmean Hq Ht.
destruct (SU_iter fy regs mem x cut p b mean s m Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm Hf15 Hmean Hq) as (E & ms1 & Hms1 & Hmem1 & HS & HE & HEf & A32).
rewrite Ht in HS.
pureF_to src2tbl_ok HS PC_SU.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem1 in Hms. exact (msteps_trans _ _ _ _ Hms1 Hms). }
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [cbn [fp_regs fp_of]; exact (eq_trans (st_okF_fregs_kept segs E _ _ 48 (@fp_regs fy) [15%bv] HS HEf ltac:(vm_compute; reflexivity) 15%bv ltac:(left; reflexivity)) Hf15)|].
jregF HS (13%bv:reg) as Hq13. jregF HS (14%bv:reg) as Hq14. jregF HS (26%bv:reg) as Hq9. jregF HS (25%bv:reg) as Hq22.
split; [rewrite Hq13, (HE 13%nat 13%bv eq_refl); exact Hr13|].
split; [rewrite Hq14, (HE 14%nat 14%bv eq_refl), Hr14, unsigned_lit_small by lia; replace (3 * (x + 1)) with (3 * x + 3) by lia; reflexivity|].
split; [rewrite Hq9, A32; replace (x + 1 - 1) with x by lia; reflexivity|].
split; [rewrite Hq22, (HE 25%nat 25%bv eq_refl); exact Hr22|].
exact (st_okF_regs_kept segs E _ _ regs SU_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)).
Qed.
Lemma SU_exit : forall (fy : FPState) (regs : bvmap 5 word) mem (x cut p b mean s m k : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 14 = Z_to_bv 64 (3 * x) -> getr regs 26 = Z_to_bv 64 (x - 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= x < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * x + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = false ->
getr regs 10 = Z_to_bv 64 k -> 0 <= k < 2 ^ 29 ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SU) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SD) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 14 = Z_to_bv 64 (3 * x) /\ getr regs' 26 = Z_to_bv 64 x /\
getr regs' 25 = Z_to_bv 64 p /\ getr regs' 15 = Z_to_bv 64 (3 * k) /\ getr regs' 10 = Z_to_bv 64 (k + 1) /\
(forall r : reg, In r SUX_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem x cut p b mean s m k Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm Hf15 Hmean Hq Ht Hr10 Hk.
destruct (SU_iter fy regs mem x cut p b mean s m Hr13 Hr14 Hr9 Hr22 Hcut Hx Hp Hb Hbr Hfrm Hf15 Hmean Hq) as (E & ms1 & Hms1 & Hmem1 & HS & HE & HEf & A32).
rewrite Ht in HS.
pureF_to src2tbl_ok HS PC_SD.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem1 in Hms. exact (msteps_trans _ _ _ _ Hms1 Hms). }
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [cbn [fp_regs fp_of]; exact (eq_trans (st_okF_fregs_kept segs E _ _ 48 (@fp_regs fy) [15%bv] HS HEf ltac:(vm_compute; reflexivity) 15%bv ltac:(left; reflexivity)) Hf15)|].
jregF HS (13%bv:reg) as Hq13. jregF HS (14%bv:reg) as Hq14. jregF HS (26%bv:reg) as Hq9. jregF HS (25%bv:reg) as Hq22.
jregF HS (10%bv:reg) as Hq10.
pose proof (st_okF_reg segs E _ _ 15%bv HS) as Hq15. eval_sr_get_in Hq15.
split; [rewrite Hq13, (HE 13%nat 13%bv eq_refl); exact Hr13|].
split; [rewrite Hq14, (HE 14%nat 14%bv eq_refl); exact Hr14|].
split; [rewrite Hq9, A32; reflexivity|].
split; [rewrite Hq22, (HE 25%nat 25%bv eq_refl); exact Hr22|].
split; [rewrite Hq15; apply (denot_mul3 E 10 k); [rewrite (HE 10%nat 10%bv eq_refl); exact Hr10 | lia]|].
split; [rewrite Hq10, (HE 10%nat 10%bv eq_refl), Hr10, unsigned_lit_small by lia; reflexivity|].
exact (st_okF_regs_kept segs E _ _ regs SUX_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)).
Qed.
Lemma SUX_SU : forall r : reg, In r SUX_KEEP -> In r SU_KEEP.
Proof.
intros r H. cbv [SUX_KEEP In] in H. cbv [SU_KEEP In].
repeat (destruct H as [<-|H]; [repeat (first [left; reflexivity | right]) |]). destruct H.
Qed.
Lemma SU_loop : forall n (fy : FPState) (regs : bvmap 5 word) mem (x i1 cut p mean s m k : Z) (palc : list Z),
i1 - x <= Z.of_nat n -> 0 <= x <= i1 -> i1 < 2 ^ 29 ->
arr8 segs mem p palc -> 3 * i1 + cut < zlen palc -> 0 <= p -> p + zlen palc < 2 ^ 48 ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
0 <= cut <= 2 -> frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
getr regs 13 = Z_to_bv 64 cut -> getr regs 14 = Z_to_bv 64 (3 * x) -> getr regs 26 = Z_to_bv 64 (x - 1) -> getr regs 25 = Z_to_bv 64 p ->
getr regs 10 = Z_to_bv 64 k -> 0 <= k < 2 ^ 29 ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SU) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SD) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 14 = Z_to_bv 64 (3 * i1) /\ getr regs' 26 = Z_to_bv 64 i1 /\
getr regs' 25 = Z_to_bv 64 p /\ getr regs' 15 = Z_to_bv 64 (3 * k) /\ getr regs' 10 = Z_to_bv 64 (k + 1) /\
(forall r : reg, In r SUX_KEEP -> getr regs' r = getr regs r).
Proof.
induction n as [|n IH]; intros fy regs mem x i1 cut p mean s m k palc Hn Hx Hi1 Hpa Hlen Hp0 Hp1 Hsm Hbig Hcut Hfrm Hf15 Hmean Hq Hr13 Hr14 Hr9 Hr22 Hr10 Hk.
- assert (x = i1) as -> by lia.
destruct (arr8_getz segs mem p palc (3 * i1 + cut) Hpa ltac:(lia)) as [Hb Hbr]. rewrite Z.add_assoc in Hb.
exact (SU_exit fy regs mem i1 cut p _ mean s m k Hr13 Hr14 Hr9 Hr22 Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq Hbig Hr10 Hk).
- destruct (Z.eq_dec x i1) as [->|Hne].
+ destruct (arr8_getz segs mem p palc (3 * i1 + cut) Hpa ltac:(lia)) as [Hb Hbr]. rewrite Z.add_assoc in Hb.
exact (SU_exit fy regs mem i1 cut p _ mean s m k Hr13 Hr14 Hr9 Hr22 Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq Hbig Hr10 Hk).
+ destruct (arr8_getz segs mem p palc (3 * x + cut) Hpa ltac:(lia)) as [Hb Hbr]. rewrite Z.add_assoc in Hb.
destruct (SU_step fy regs mem x cut p _ mean s m Hr13 Hr14 Hr9 Hr22 Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq (Hsm x ltac:(lia)))
as (fy1 & regs1 & Hms1 & Hfrm1 & Hf1 & G13 & G14 & G9 & G22 & K1).
destruct (IH fy1 regs1 mem (x + 1) i1 cut p mean s m k palc ltac:(lia) ltac:(lia) Hi1 Hpa Hlen Hp0 Hp1
ltac:(intros z Hz; apply Hsm; lia) Hbig Hcut Hfrm1 Hf1 Hmean Hq G13 G14 G9 G22
ltac:(rewrite (K1 10%bv ltac:(cbv; tauto)); exact Hr10) Hk)
as (fy2 & regs2 & Hms2 & Hfrm2 & Hf2 & F13 & F14 & F9 & F22 & F15 & F10 & K2).
exists fy2, regs2. split; [exact (msteps_trans _ _ _ _ Hms1 Hms2)|].
repeat (split; [assumption|]). intros r Hr. rewrite (K2 r Hr). apply K1. apply SUX_SU. exact Hr.
Qed.
Definition sd_alias : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SOff 15 0)) (SOff 25 0).
Definition ss_SD0 : sstate :=
mkSS PC_SD (sr_set sr_atoms 10%bv (SOff 32%nat 1))
[ YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ] None
(mkFacts [ (13%nat, mkAF 0 2 0); (15%nat, mkAF 0 (2^31) 0); (25%nat, mkAF 0 (2^48) 0); (32%nat, mkAF 0 (2^30) 0); (34%nat, mkAF 0 255 0) ]
[] [(sd_alias, SOff 33%nat 0)]).
Definition ss_SD : sstate := mkSST PC_SD (ss_regs ss_SD0) (sfr_atoms 48) (ss_mem ss_SD0) None (ss_facts ss_SD0).
Lemma SD_entry : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 15 = Z_to_bv 64 (3 * y) -> getr regs 10 = Z_to_bv 64 (y + 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * y + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) ->
let E0 := Ereg regs (map (Z_to_bv 64) [y; p + 3 * y + cut; b] ++ []) in
let E := ew_fregs E0 48 (@fp_regs fy) in
st_okF segs E ss_SD (@mkst fy regs (Z_to_bv 64 PC_SD) mem rom) /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
ew E 32 = Z_to_bv 64 y /\ ew E 34 = Z_to_bv 64 b.
Proof.
intros fy regs mem y cut p b Hr13 Hr15 Hr10 Hr22 Hcut Hy Hp Hb Hbr Hfrm E0 E.
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error [y; p + 3 * y + cut; b] j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall k, (k < 48)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HU13 : bv_unsigned (ew E0 13) = cut) by (rewrite (HE0 13%nat 13%bv eq_refl), Hr13; apply unsigned_lit_small; lia).
assert (HU15 : bv_unsigned (ew E0 15) = 3 * y) by (rewrite (HE0 15%nat 15%bv eq_refl), Hr15; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E0 25) = p) by (rewrite (HE0 25%nat 25%bv eq_refl), Hr22; apply unsigned_lit_small; lia).
assert (A32 : ew E0 32 = Z_to_bv 64 y) by (apply (HV 0%nat); reflexivity).
assert (A33 : ew E0 33 = Z_to_bv 64 (p + 3 * y + cut)) by (apply (HV 1%nat); reflexivity).
assert (A34 : ew E0 34 = Z_to_bv 64 b) by (apply (HV 2%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E0 32) = y) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E0 33) = p + 3 * y + cut) by (rewrite A33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E0 34) = b) by (rewrite A34; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok segs fy E0 ss_SD0 (@mkst fy regs (Z_to_bv 64 PC_SD) mem rom)).
{ unfold ss_SD0. subst E0. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |]. cbn [sv_denot]. rewrite HU32. exact Hr10.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU34; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. apply val_mem_of_byte; [exact Hb | exact Hbr].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
rewrite HU13, HU15, HU22, HU32, HU34. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [f_alias alias_ok]. split; [|exact I]. unfold sd_alias.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, HU13, HU15, HU22, HU33, !Z.add_0_r.
rewrite (zcanon_id cut), (zcanon_id (3 * y)), (zcanon_id p) by (unfold M64; lia). rewrite (zcanon_id (cut + 3 * y)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia. }
split; [exact (st_ok_enterF segs fy 48 E0 ss_SD0 _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia. split; [exact A32 | exact A34].
Qed.
Definition ss_SD_br : sstate := Eval vm_compute in (fst (sym_runFN segs src2tbl FUEL ss_SD)).
Definition sd_cond : sv := SF2 (FP2_cmp F_LT FMT_D) (SOff 63 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 34 0)).
Lemma SD_run1 : sym_runFN segs src2tbl FUEL ss_SD = (ss_SD_br, RS_stopped (SR_branch BC_NE sd_cond (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma bne_bool_w_neg : forall t : bool, branch_taken BC_NE (if t then w0 else w1) (Z_to_bv 64 0) = negb t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma SD_iter : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b mean s m : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 15 = Z_to_bv 64 (3 * y) -> getr regs 10 = Z_to_bv 64 (y + 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * y + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
exists E ms1,
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SD) mem rom) ms1 /\ ms_mem ms1 = mem /\
st_okF segs E (add_cond ss_SD_br (mkAC (if b * s <=? m then BC_EQ else BC_NE) sd_cond (SLit 0))) ms1 /\
(forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) /\
(forall r : reg, ew E (48 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
ew E 32 = Z_to_bv 64 y.
Proof.
intros fy regs mem y cut p b mean s m Hr13 Hr15 Hr10 Hr22 Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq.
destruct (SD_entry fy regs mem y cut p b Hr13 Hr15 Hr10 Hr22 Hcut Hy Hp Hb Hbr Hfrm) as (HS & HE & HEf & A32 & A34).
set (E := ew_fregs _ 48 _) in HS, HE, HEf, A32, A34.
destruct (pure_stretchF segs src2tbl src2tbl_ok FUEL E ss_SD _ _ _ HS SD_run1 I ltac:(vm_compute; reflexivity) ltac:(reflexivity))
as (ms1 & Hms1 & HS1 & Hmem1 & _).
exists E, ms1. split; [exact Hms1|]. split; [exact Hmem1|]. split; [| split; [exact HE | split; [exact HEf | exact A32]]].
assert (Hc : branch_taken BC_NE (sv_denot E sd_cond) (sv_denot E (SLit 0)) = negb (b * s <=? m)).
{ unfold sd_cond. cbn [sv_denot]. rewrite !Z.add_0_r, A34, !Z_to_bv_bv_unsigned.
assert (H63 : ew E 63 = Z_to_bv 64 mean) by (rewrite <- Hf15; exact (HEf (15%bv : reg))).
rewrite (flt_cvt_test RNE _ _ b mean s m eq_refl H63 Hbr Hmean Hq). apply bne_bool_w_neg. }
destruct (b * s <=? m) eqn:Et; cbn [negb] in Hc.
- change BC_EQ with (neg_bc BC_NE). apply st_okF_add_cond_neg; [exact HS1 | exact Hc].
- apply st_okF_add_cond; [exact HS1 | exact Hc].
Qed.
Lemma SD_step : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b mean s m : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 15 = Z_to_bv 64 (3 * y) -> getr regs 10 = Z_to_bv 64 (y + 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 1 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * y + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = false ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SD) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_SD) mem rom) /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : reg) = Z_to_bv 64 mean /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 15 = Z_to_bv 64 (3 * (y - 1)) /\ getr regs' 10 = Z_to_bv 64 (y - 1 + 1) /\
getr regs' 25 = Z_to_bv 64 p /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem y cut p b mean s m Hr13 Hr15 Hr10 Hr22 Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq Ht.
destruct (SD_iter fy regs mem y cut p b mean s m Hr13 Hr15 Hr10 Hr22 Hcut ltac:(lia) Hp Hb Hbr Hfrm Hf15 Hmean Hq) as (E & ms1 & Hms1 & Hmem1 & HS & HE & HEf & A32).
rewrite Ht in HS.
pureF_to src2tbl_ok HS PC_SD.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem1 in Hms. exact (msteps_trans _ _ _ _ Hms1 Hms). }
split; [exact (st_okF_frm segs E _ _ HS)|].
split; [cbn [fp_regs fp_of]; exact (eq_trans (st_okF_fregs_kept segs E _ _ 48 (@fp_regs fy) [15%bv] HS HEf ltac:(vm_compute; reflexivity) 15%bv ltac:(left; reflexivity)) Hf15)|].
jregF HS (13%bv:reg) as Hq13. jregF HS (15%bv:reg) as Hq15. jregF HS (10%bv:reg) as Hq10. jregF HS (25%bv:reg) as Hq22.
split; [rewrite Hq13, (HE 13%nat 13%bv eq_refl); exact Hr13|].
split. { rewrite Hq15, (HE 15%nat 15%bv eq_refl), Hr15, unsigned_lit_small by lia. replace (3 * (y - 1)) with (3 * y + -3) by lia. reflexivity. }
split; [rewrite Hq10, A32; replace (y - 1 + 1) with y by lia; reflexivity|].
split; [rewrite Hq22, (HE 25%nat 25%bv eq_refl); exact Hr22|].
exact (st_okF_regs_kept segs E _ _ regs SD_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)).
Qed.
Lemma SD_exit : forall (fy : FPState) (regs : bvmap 5 word) mem (y cut p b mean s m : Z),
getr regs 13 = Z_to_bv 64 cut -> getr regs 15 = Z_to_bv 64 (3 * y) -> getr regs 10 = Z_to_bv 64 (y + 1) -> getr regs 25 = Z_to_bv 64 p ->
0 <= cut <= 2 -> 0 <= y < 2 ^ 29 -> 0 <= p < 2 ^ 48 ->
mbyte segs mem (p + 3 * y + cut) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
(b * s <=? m) = true ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SD) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_BG) mem rom) /\
frm_zero (@fp_csr fy') /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 15 = Z_to_bv 64 (3 * y - 3) /\ getr regs' 10 = Z_to_bv 64 y /\
getr regs' 25 = Z_to_bv 64 p /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
intros fy regs mem y cut p b mean s m Hr13 Hr15 Hr10 Hr22 Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq Ht.
destruct (SD_iter fy regs mem y cut p b mean s m Hr13 Hr15 Hr10 Hr22 Hcut Hy Hp Hb Hbr Hfrm Hf15 Hmean Hq) as (E & ms1 & Hms1 & Hmem1 & HS & HE & HEf & A32).
rewrite Ht in HS.
pureF_to src2tbl_ok HS PC_BG.
exists (fp_of ms), (ms_regs ms).
split. { rewrite Hsh, Hmem1 in Hms. exact (msteps_trans _ _ _ _ Hms1 Hms). }
split; [exact (st_okF_frm segs E _ _ HS)|].
jregF HS (13%bv:reg) as Hq13. jregF HS (15%bv:reg) as Hq15. jregF HS (10%bv:reg) as Hq10. jregF HS (25%bv:reg) as Hq22.
split; [rewrite Hq13, (HE 13%nat 13%bv eq_refl); exact Hr13|].
split. { rewrite Hq15, (HE 15%nat 15%bv eq_refl), Hr15, unsigned_lit_small by lia. replace (3 * y - 3) with (3 * y + -3) by lia. reflexivity. }
split; [rewrite Hq10, A32; reflexivity|].
split; [rewrite Hq22, (HE 25%nat 25%bv eq_refl); exact Hr22|].
exact (st_okF_regs_kept segs E _ _ regs SD_KEEP HS ltac:(ridx_of HE) ltac:(vm_compute; reflexivity)).
Qed.
Lemma SD_loop : forall n (fy : FPState) (regs : bvmap 5 word) mem (y k1 cut p mean s m : Z) (palc : list Z),
y - k1 <= Z.of_nat n -> 0 <= k1 <= y -> y < 2 ^ 29 ->
arr8 segs mem p palc -> 3 * y + cut < zlen palc -> 0 <= p -> p + zlen palc < 2 ^ 48 ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
0 <= cut <= 2 -> frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : reg) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
getr regs 13 = Z_to_bv 64 cut -> getr regs 15 = Z_to_bv 64 (3 * y) -> getr regs 10 = Z_to_bv 64 (y + 1) -> getr regs 25 = Z_to_bv 64 p ->
exists (fy' : FPState) regs',
msteps segs (@mkst fy regs (Z_to_bv 64 PC_SD) mem rom) (@mkst fy' regs' (Z_to_bv 64 PC_BG) mem rom) /\
frm_zero (@fp_csr fy') /\
getr regs' 13 = Z_to_bv 64 cut /\ getr regs' 15 = Z_to_bv 64 (3 * k1 - 3) /\ getr regs' 10 = Z_to_bv 64 k1 /\
getr regs' 25 = Z_to_bv 64 p /\
(forall r : reg, In r SD_KEEP -> getr regs' r = getr regs r).
Proof.
induction n as [|n IH]; intros fy regs mem y k1 cut p mean s m palc Hn Hy Hy1 Hpa Hlen Hp0 Hp1 Hbg Hsm Hcut Hfrm Hf15 Hmean Hq Hr13 Hr15 Hr10 Hr22.
- assert (y = k1) as -> by lia.
destruct (arr8_getz segs mem p palc (3 * k1 + cut) Hpa ltac:(lia)) as [Hb Hbr]. rewrite Z.add_assoc in Hb.
exact (SD_exit fy regs mem k1 cut p _ mean s m Hr13 Hr15 Hr10 Hr22 Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq Hsm).
- destruct (Z.eq_dec y k1) as [->|Hne].
+ destruct (arr8_getz segs mem p palc (3 * k1 + cut) Hpa ltac:(lia)) as [Hb Hbr]. rewrite Z.add_assoc in Hb.
exact (SD_exit fy regs mem k1 cut p _ mean s m Hr13 Hr15 Hr10 Hr22 Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq Hsm).
+ destruct (arr8_getz segs mem p palc (3 * y + cut) Hpa ltac:(lia)) as [Hb Hbr]. rewrite Z.add_assoc in Hb.
destruct (SD_step fy regs mem y cut p _ mean s m Hr13 Hr15 Hr10 Hr22 Hcut ltac:(lia) ltac:(lia) Hb Hbr Hfrm Hf15 Hmean Hq (Hbg y ltac:(lia)))
as (fy1 & regs1 & Hms1 & Hfrm1 & Hf1 & G13 & G15 & G10 & G22 & K1).
destruct (IH fy1 regs1 mem (y - 1) k1 cut p mean s m palc ltac:(lia) ltac:(lia) ltac:(lia) Hpa ltac:(lia) Hp0 Hp1
ltac:(intros z Hz; apply Hbg; lia) Hsm Hcut Hfrm1 Hf1 Hmean Hq G13 G15 G10 G22)
as (fy2 & regs2 & Hms2 & Hfrm2 & F13 & F15 & F10 & F22 & K2).
exists fy2, regs2. split; [exact (msteps_trans _ _ _ _ Hms1 Hms2)|].
repeat (split; [assumption|]). intros r Hr. rewrite (K2 r Hr). apply K1. exact Hr.
Qed.
End c.
