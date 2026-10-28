(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI07 YI05 YI5a UI5d UI5f UI1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition ng_b1 (b : rbound) : rbound := rb_malloc b FILE_BLOCK.
Definition ng_b2 (b : rbound) : rbound := rb_malloc (ng_b1 b) CGIF_SIZE.
Definition ng_b3 (b : rbound) (attr ngp : Z) : rbound := if Z.land attr 4 =? 0 then rb_malloc (ng_b2 b) (3 * ngp) else ng_b2 b.
Lemma prN_small : forall n, 0 <= n <= MMAP_THRESHOLD -> prN n = 0.
Proof. intros n Hn. unfold prN. destruct (Z.ltb_spec MMAP_THRESHOLD n); [lia | reflexivity]. Qed.
Lemma ng_b1_le : forall b, rb_le (ng_b1 b) (rb_acc b 1 0).
Proof.
intros b. unfold ng_b1. eapply rb_le_trans; [apply rb_malloc_acc; unfold FILE_BLOCK; lia|].
rewrite prN_small by (unfold FILE_BLOCK, MMAP_THRESHOLD; lia). apply rb_le_refl.
Qed.
Lemma ng_b2_le : forall b, rb_le (ng_b2 b) (rb_acc b 2 0).
Proof.
intros b. unfold ng_b2. eapply rb_le_trans; [apply rb_malloc_acc; unfold CGIF_SIZE; lia|].
rewrite prN_small by (unfold CGIF_SIZE, MMAP_THRESHOLD; lia).
replace (rb_acc b 2 0) with (rb_acc (rb_acc b 1 0) 1 0) by (rewrite rb_acc_acc; reflexivity).
apply rb_acc_mono; [apply ng_b1_le | lia | lia].
Qed.
Lemma ng_b3_le : forall b attr ngp, 0 <= 3 * ngp <= PALMAX -> rb_le (ng_b3 b attr ngp) (rb_acc b 3 PALSLACK).
Proof.
intros b attr ngp Hn. unfold ng_b3. destruct (Z.land attr 4 =? 0).
- eapply rb_le_trans; [apply rb_malloc_acc; lia|].
replace (rb_acc b 3 PALSLACK) with (rb_acc (rb_acc b 2 0) 1 PALSLACK) by (rewrite rb_acc_acc; reflexivity).
apply rb_acc_mono; [apply ng_b2_le | lia | pose proof (prN_pal (3 * ngp) Hn); lia].
- eapply rb_le_trans; [apply ng_b2_le|]. apply rb_acc_mono; [apply rb_le_refl | lia | unfold PALSLACK; lia].
Qed.
Lemma ng_room1 : forall b, newgif_room b -> room b FILE_BLOCK.
Proof.
intros b H. eapply (room_mono b (rb_acc b NEWGIF_K PALSLACK) FILE_BLOCK PALMAX); [apply rb_acc_le; unfold NEWGIF_K, PALSLACK; lia | unfold FILE_BLOCK, PALMAX; lia | exact H].
Qed.
Lemma ng_room2 : forall b, newgif_room b -> room (ng_b1 b) CGIF_SIZE.
Proof.
intros b H. eapply (room_mono (ng_b1 b) (rb_acc b NEWGIF_K PALSLACK) CGIF_SIZE PALMAX); [| unfold CGIF_SIZE, PALMAX; lia | exact H].
eapply rb_le_trans; [apply ng_b1_le|]. apply rb_acc_mono; [apply rb_le_refl | unfold NEWGIF_K; lia | unfold PALSLACK; lia].
Qed.
Lemma ng_room3 : forall b ngp, newgif_room b -> 0 <= 3 * ngp <= PALMAX -> room (ng_b2 b) (3 * ngp).
Proof.
intros b ngp H Hn. eapply (room_mono (ng_b2 b) (rb_acc b NEWGIF_K PALSLACK) (3 * ngp) PALMAX); [| lia | exact H].
eapply rb_le_trans; [apply ng_b2_le|]. apply rb_acc_mono; [apply rb_le_refl | unfold NEWGIF_K; lia | unfold PALSLACK; lia].
Qed.
Lemma ng_room4 : forall b attr ngp, newgif_room b -> 0 <= 3 * ngp <= PALMAX -> rawnew_room (ng_b3 b attr ngp).
Proof.
intros b attr ngp H Hn. unfold rawnew_room.
eapply (room_mono (ng_b3 b attr ngp) (rb_acc b NEWGIF_K PALSLACK) RAW_SIZE PALMAX); [| unfold RAW_SIZE, PALMAX; lia | exact H].
eapply rb_le_trans; [apply ng_b3_le; exact Hn|]. apply rb_acc_mono; [apply rb_le_refl | unfold NEWGIF_K; lia | lia].
Qed.
Lemma ng_fin_ok : forall b attr ngp, 0 <= 3 * ngp <= PALMAX -> rb_le (rawnew_rb (ng_b3 b attr ngp)) (newgif_rb b).
Proof.
intros b attr ngp Hn. unfold rawnew_rb, newgif_rb, NEWGIF_K.
eapply rb_le_trans; [apply rb_malloc_acc; unfold RAW_SIZE; lia|]. rewrite prN_small by (unfold RAW_SIZE, MMAP_THRESHOLD; lia).
replace (rb_acc b 4 PALSLACK) with (rb_acc (rb_acc b 3 PALSLACK) 1 0) by (rewrite rb_acc_acc; f_equal; lia).
apply rb_acc_mono; [apply ng_b3_le; exact Hn | lia | lia].
Qed.
Lemma ng_b1_fin : forall b, rb_le (ng_b1 b) (newgif_rb b).
Proof. intros b. eapply rb_le_trans; [apply ng_b1_le|]. unfold newgif_rb, NEWGIF_K. apply rb_acc_mono; [apply rb_le_refl | lia | unfold PALSLACK; lia]. Qed.
Lemma ng_b3_fin : forall b attr ngp, 0 <= 3 * ngp <= PALMAX -> rb_le (ng_b3 b attr ngp) (newgif_rb b).
Proof. intros b attr ngp Hn. eapply rb_le_trans; [apply ng_b3_le; exact Hn|]. unfold newgif_rb, NEWGIF_K. apply rb_acc_mono; [apply rb_le_refl | lia | lia]. Qed.
Lemma inFP_token : forall a, inFP [sink_token] a -> a < 4096.
Proof. intros a (r & [<-|[]] & Hr). cbn in Hr. lia. Qed.
Lemma land_pow2 : forall x n, 0 <= n -> Z.land x (2 ^ n) = 2 ^ n * Z.b2z (Z.testbit x n).
Proof.
intros x n Hn. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.testbit x n) eqn:T.
- cbn [Z.b2z]. rewrite Z.mul_1_r, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec n m) as [<-|Hne]; [rewrite T; reflexivity | apply andb_false_r].
- cbn [Z.b2z]. rewrite Z.mul_0_r, Z.bits_0. destruct (Z.eqb_spec n m) as [<-|Hne]; [rewrite T; reflexivity | apply andb_false_r].
Qed.
Lemma raw_attr_bits : forall x, 0 <= x ->
Z.lor ((x / 2) mod 2) (Z.land (x / 8) 2) = raw_attr_of x.
Proof.
intros x Hx. unfold raw_attr_of, YO07.flag.
assert (B1 : (x / 2) mod 2 = Z.b2z (Z.testbit x 1)).
{ rewrite Z.testbit_spec' by lia. reflexivity. }
assert (B4 : Z.land (x / 8) 2 = 2 * Z.b2z (Z.testbit x 4)).
{ change 8 with (2 ^ 3). change 2 with (2 ^ 1) at 2. rewrite land_pow2 by lia. rewrite Z.div_pow2_bits by lia. reflexivity. }
assert (L2 : Z.land x 2 = 2 * Z.b2z (Z.testbit x 1)) by (change 2 with (2 ^ 1) at 1; rewrite land_pow2 by lia; reflexivity).
assert (L16 : Z.land x 16 = 16 * Z.b2z (Z.testbit x 4)) by (change 16 with (2 ^ 4) at 1; rewrite land_pow2 by lia; reflexivity).
rewrite L2, L16, B1, B4. destruct (Z.testbit x 1), (Z.testbit x 4); reflexivity.
Qed.
Lemma raw_attr_mod32 : forall x, 0 <= x -> raw_attr_of (x mod 2 ^ 32) = raw_attr_of x.
Proof.
intros x Hx. unfold raw_attr_of, YO07.flag. rewrite <- (Z.land_ones x 32) by lia.
rewrite <- !Z.land_assoc. change (Z.land (Z.ones 32) 2) with 2. change (Z.land (Z.ones 32) 16) with 16. reflexivity.
Qed.
Lemma raw_attr_exec : forall E n x,
U E (SOff n 0) = x -> 0 <= x < 2 ^ 64 ->
U E (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 63)) (SAlu ALU_AND (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SLit 2)))
= raw_attr_of (x mod 2 ^ 32).
Proof.
intros E n x Hx Rx. rewrite raw_attr_mod32 by lia. rewrite <- raw_attr_bits by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SAlu. cbn [zalu_raw]. rewrite ?U_SAlu. cbn [zalu_raw]. rewrite ?U_SLit, ?Hx.
change (Z.land (zcanon 62) 63) with 62. change (Z.land (zcanon 63) 63) with 63. change (Z.land (zcanon 3) 63) with 3. change (zcanon 2) with 2.
rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
assert (B1 : (x / 2) mod 2 = Z.b2z (Z.testbit x 1)) by (rewrite Z.testbit_spec' by lia; reflexivity).
assert (B4 : Z.land (x / 8) 2 = 2 * Z.b2z (Z.testbit x 4)).
{ change 8 with (2 ^ 3). change 2 with (2 ^ 1) at 2. rewrite land_pow2 by lia. rewrite Z.div_pow2_bits by lia. reflexivity. }
assert (A : zcanon (x * 2 ^ 62) = (x mod 4) * 2 ^ 62).
{ unfold zcanon, M64. change (2 ^ 64) with (4 * 2 ^ 62). rewrite Z.mul_mod_distr_r by lia. reflexivity. }
rewrite A.
assert (A2 : x mod 4 * 2 ^ 62 / 2 ^ 63 = Z.b2z (Z.testbit x 1)).
{ change (2 ^ 63) with (2 * 2 ^ 62). rewrite Z.div_mul_cancel_r by lia.
rewrite <- (Z.mod_pow2_bits_low x 2 1) by lia. change 4 with (2 ^ 2). rewrite Z.testbit_spec' by lia.
pose proof (Z.mod_pos_bound x (2 ^ 2) ltac:(lia)) as Hr. change (2 ^ 1) with 2.
rewrite (Z.mod_small (x mod 2 ^ 2 / 2) 2); [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite A2.
assert (A3 : zcanon (x / 2 ^ 3) = x / 8).
{ unfold zcanon, M64. change (2 ^ 3) with 8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite A3, B4, B1.
unfold zcanon, M64. destruct (Z.testbit x 1), (Z.testbit x 4); reflexivity.
Qed.
Lemma np2_aux_ge : forall f n p, 0 <= p -> n <= 2 ^ (p + Z.of_nat f) -> n <= 2 ^ YO07.np2_aux f n p /\ p <= YO07.np2_aux f n p <= p + Z.of_nat f.
Proof.
induction f as [|f IH]; intros n p Hp Hn; cbn [YO07.np2_aux].
- rewrite Z.add_0_r in Hn. lia.
- destruct (Z.ltb_spec (2 ^ p) n) as [Hl|Hl].
+ assert (Hn' : n <= 2 ^ (p + 1 + Z.of_nat f)) by (replace (p + 1 + Z.of_nat f) with (p + Z.of_nat (S f)) by lia; exact Hn).
pose proof (IH n (p + 1) ltac:(lia) Hn'). lia.
+ lia.
Qed.
Lemma pal_pow_bounds : forall n, 0 <= n <= 256 -> n <= 2 ^ YO07.pal_pow n /\ 1 <= YO07.pal_pow n <= 8.
Proof.
intros n Hn. unfold YO07.pal_pow, YO07.calcNextPower2Ex.
pose proof (np2_aux_ge 17 n 0 ltac:(lia) ltac:(cbn; lia)) as [G1 G2].
assert (G3 : forall f p, 0 <= p <= 8 -> YO07.np2_aux f n p <= 8).
{ induction f as [|f IH]; intros p Hp; cbn [YO07.np2_aux]; [lia|].
destruct (Z.ltb_spec (2 ^ p) n) as [Hl|Hl]; [|lia].
assert (p < 8) by (destruct (Z.eq_dec p 8) as [->|]; [change (2 ^ 8) with 256 in Hl; lia | lia]).
apply IH. lia. }
pose proof (G3 17%nat 0 ltac:(lia)).
split; [| lia]. eapply Z.le_trans; [exact G1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma raw_header_length : forall W H sgct gct rattr loops, 0 <= sgct <= 256 ->
Z.of_nat (length (YO07.raw_header W H sgct gct rattr loops)) <= 800.
Proof.
intros W H sgct gct rattr loops Hs. unfold YO07.raw_header, YO07.u16le, YO07.zeros.
rewrite !length_app.
assert (P : Z.of_nat (length (if sgct =? 0 then [] else firstn (Z.to_nat (sgct * 3)) gct ++ repeat 0 (Z.to_nat (((2 ^ YO07.pal_pow sgct - sgct) * 3) mod 65536)))) <= 768).
{ destruct (Z.eqb_spec sgct 0) as [->|Hnz]; [cbn; lia|].
rewrite length_app, repeat_length. pose proof (firstn_le_length (Z.to_nat (sgct * 3)) gct) as F.
destruct (pal_pow_bounds sgct Hs) as [T1 PP].
assert (T : 2 ^ YO07.pal_pow sgct <= 256) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
rewrite Z.mod_small by lia. lia. }
assert (Q : Z.of_nat (length (if YO07.flag rattr 1 && negb (YO07.flag rattr 2)
then [33; 255; 11; 78; 69; 84; 83; 67; 65; 80; 69; 50; 46; 48; 3; 1] ++ [loops mod 256; loops / 256 mod 256] ++ [0] else [])) <= 19).
{ destruct (YO07.flag rattr 1 && negb (YO07.flag rattr 2)); cbn; lia. }
cbn [length] in *. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Theorem ubs0_freeCGIF_res :
forall L A regs mem md g vals attr pal palsz rest b,
fn_pre ubs0_msyms MR FREECGIF_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 g ->
obj_at ubs0segs mem g LAY_CGIF vals ->
nth_error vals CG_attr = Some attr -> nth_error vals CG_pal = Some pal ->
Permutation (blocks L A) ((g, CGIF_SIZE) :: gpals_of attr pal palsz ++ rest) ->
res_ok A b ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_freeCGIF) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FREECGIF_STK (spZ regs) (fp_freeCGIF g attr pal palsz) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest /\ st_init_done A' = true /\ res_ok A' b).
Proof using IMG LAWS.
intros L A regs mem md g vals attr pal palsz rest b HPRE Ha0 Hobj Hattr Hpal HB HRb.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : FREECGIF_STK = 8208) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hgin : In (g, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_nth ubs0segs mem g LAY_CGIF vals 5 _ _ Hobj eq_refl Hattr) as [_ Hattr_r]. cbn [snd] in Hattr_r.
pose proof (obj_at_nth ubs0segs mem g LAY_CGIF vals 3 _ _ Hobj eq_refl Hpal) as [_ Hpal_r]. cbn [snd] in Hpal_r.
assert (HS : st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) vals ++ [])) ss_freeCGIF
(mkst regs (Z_to_bv 64 ubs0_A_freeCGIF) mem (seg_rom ubs0segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity). reflexivity.
+ eapply (region_ok_obj ubs0segs _ mem 10 g); [ | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Ha0. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite Ha0, unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. repeat split; lia. }
pose proof (journal_init ubs0_msyms MR FREECGIF_STK (fp_freeCGIF g attr pal palsz) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_freeCGIF) mem (seg_rom ubs0segs))) in HJ.
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 2 = getr regs 2)
by (apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 1 = getr regs 1)
by (apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE4 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 4 = getr regs 4)
by (apply (ew_Ereg_nat regs _ 4 4%bv); vm_compute; reflexivity).
assert (HE10 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 10 = Z_to_bv 64 g).
{ rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). exact Ha0. }
assert (HE37 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 37 = Z_to_bv 64 attr) by (apply (Ereg_vals regs vals [] 5); exact Hattr).
assert (HE35 : ew (Ereg regs (map (Z_to_bv 64) vals ++ [])) 35 = Z_to_bv 64 pal) by (apply (Ereg_vals regs vals [] 3); exact Hpal).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (Hsp63 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ in *; lia).
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jbranch ubs0tbl HS.
-
rewrite branch_ne_U, U_and_lit, U_zext, (U_atom _ 37 attr HE37), U_lit in Hc by lia.
change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_4 in Hc by lia.
assert (Hattr4 : Z.land attr 4 <> 0) by (intros E0; rewrite E0 in Hc; discriminate).
assert (Hpals : gpals_of attr pal palsz = []).
{ unfold gpals_of. destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity]. }
rewrite Hpals in HB. cbn [app] in HB.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. rewrite HE10 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HE2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite HE4, Htp in Hr4. jreg HS (1%bv:reg) as Hr1. rewrite HE1 in Hr1.
eapply SR_mono.
{ eapply (jfree_at_res API IMG) with (spc := spZ regs);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hgin | exact HRb | exact Hr10
| rewrite Hr2; unfold spZ; rewrite ?Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hsp63 | exact Hal16 | lia | lia
| exact Hr4 | exact Hr1 | exact Hra
| intros _ i Hi; exists (g, g + CGIF_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP2]|].
split; [eapply perm_after_rm1; [exact HB | exact Hrm]|]. split; [exact Hid2|].
eapply res_ok_mono; [apply rb_free_le | exact HR2].
-
rewrite branch_ne_U, U_and_lit, U_zext, (U_atom _ 37 attr HE37), U_lit in Hc by lia.
change (2 ^ Z.of_N 8) with 256 in Hc. rewrite land_mod256_4 in Hc by lia.
assert (Hattr4 : Z.land attr 4 = 0) by (destruct (Z.eqb_spec (Z.land attr 4) 0); [assumption | discriminate]).
assert (Hpals : gpals_of attr pal palsz = [(pal, palsz)]) by (unfold gpals_of; rewrite Hattr4; reflexivity).
rewrite Hpals in HB. cbn [app] in HB.
assert (Hpalin : In (pal, palsz) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
pose proof (heap_sep_perm ubs0_msyms MR LAWS L A mem md (g, CGIF_SIZE) _ (pal, palsz) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_free.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. rewrite HE35 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite HE2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite HE4, Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jfree_at_res API IMG) with (spc := spZ regs - 16);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hpalin | exact HRb | exact Hr10
| rewrite Hr2; unfold spZ; f_equal; lia | lia
| replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16 | lia | lia
| exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity
| intros _ i Hi; exists (pal, pal + palsz); split; [right; rewrite Hattr4; left; reflexivity | cbn; lia] ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2). clear HJ.
assert (HB2 : Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: rest)).
{ eapply perm_after_rm1; [|exact Hrm]. eapply Permutation_trans; [exact HB|]. apply perm_swap. }
assert (Hg2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep, Hhi2. cbn [ms_regs ms_mem mkst] in HP2, Hkeep, Hhi2, HJ2.
jafter_call HS 49%nat regs2 mem2 HP2 HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK)] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | lia | lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hg2 | exact Hkeep | lia | lia | lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ wr_ok_tac. ew_havoc. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 49 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hq10. first [rewrite HE10 in Hq10 | rewrite ew_havoc_old, HE10 in Hq10 by lia].
jreg HS (2%bv:reg) as Hq2. first [rewrite HE2 in Hq2 | rewrite ew_havoc_old, HE2 in Hq2 by lia].
jreg HS (4%bv:reg) as Hq4. first [rewrite HE4, Htp in Hq4 | rewrite ew_havoc_old, HE4, Htp in Hq4 by lia].
jreg HS (1%bv:reg) as Hq1. first [rewrite HE1 in Hq1 | rewrite ew_havoc_old, HE1 in Hq1 by lia].
eapply SR_mono.
{ eapply (jfree_at_res API IMG) with (spc := spZ regs);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hg2 | exact HR2 | exact Hq10
| rewrite Hq2; unfold spZ; rewrite ?Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hsp63 | exact Hal16 | lia | lia
| exact Hq4 | exact Hq1 | exact Hra
| intros _ i Hi; exists (g, g + CGIF_SIZE); split; [left; reflexivity | cbn; lia] ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & Hid3 & HR3).
exists L3, A3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [eapply regs_preserved_trans; [exact HPR | exact HP3]|].
split; [eapply perm_after_rm1; [exact HB2 | exact Hrm3]|]. split; [exact Hid3|].
eapply res_ok_mono; [apply rb_free_le|]. eapply res_ok_mono; [apply rb_free_le | exact HR3].
Qed.
End S.
End c.
