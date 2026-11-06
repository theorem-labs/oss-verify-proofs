(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths, module names and numbers changed; 436 of its 511 lines of code are new or changed and 197 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC4b YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j YK00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Definition TFIND_ENTRY_STK : Z := 48 + 2 * ESTACK.
Definition tfind_entry_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (T P : list byte)
  : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TFIND_ENTRY_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\ (exists r, getr regs' 10 = Z_to_bv 64 r /\ find_res T P r) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TFIND_ENTRY_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition tfind_entry_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t p : Z) (T P : list byte),
  afn_pre SEGS B TFIND_ENTRY_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 p ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> 0 < p -> p + 6 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  length P = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned P) ->
  amem_range t 400 -> amem_range p 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p 6 ->
  (t + 400 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= t) ->
  off_img t 400 ->
  (p + 6 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= p) ->
  tbl_T1 T ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_find_entry) regs mem md) (tfind_entry_post fq regs ly S W mem md T P).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Definition fe_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 33;
YP09.mkRegion (Some 10%nat) 0 400 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 32 0))] ].
Definition fe_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 401) 3);
(32%nat, mkAF 0 8 0); (33%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_fe : sstate := mkSS AF_find_entry sr_atoms fe_regions None fe_facts.
Definition fe_SH : list shent := [ mkSHE 10 0 400 ].
Definition FBx : sv := SOff 33 0.
Definition FBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition fe_extra (n : Z) : list word := map (Z_to_bv 64) [n; SHADOW_OFF].
Definition EF (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (fe_extra n)).
Lemma fe_getr8 : forall (regs : bvmap 5 word) v (r : bv 5), r <> 8%bv -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 v r Hr). Qed.
Lemma fe_spZ8 : forall (regs : bvmap 5 word) v, spZ (regupd regs 8 v) = spZ regs.
Proof. intros regs v. unfold spZ. rewrite fe_getr8; [reflexivity|]. intros X. apply (f_equal bv_unsigned) in X. discriminate X. Qed.
Lemma fe_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t n : Z),
afn_pre SEGS B TFIND_ENTRY_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 -> amem_range t 400 -> off_img t 400 ->
(t + 400 <= spZ regs - TFIND_ENTRY_STK \/ spZ regs <= t) ->
0 <= n <= 8 -> val_mem SEGS (mrestrict (w_H W) mem) (t + 384) 4 n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
st_ok_pi (fx := fq) SEGS VAL (EF regs n) ss_fe
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_find_entry)) mem (seg_rom SEGS)))
/\ sh_ok SEGS FBx fe_SH (EF regs n) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch t n HPRE H10 Ht0 Ht8 AMt OIt DTt Rn VN RAt.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite fe_spZ8 in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TFIND_ENTRY_STK = 8240) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
rewrite restrict_mkst_fx.
set (E := EF regs n).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (fe_extra n)) k) by (intros k Hk; subst E; unfold EF; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_fe. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold fe_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
[cbn [sv_denot]; rewrite E66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 33 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat t E10) by (unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia). split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ t 384 4 (SOff 32 0) n); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VN].
+ apply pairwise_disjoint_of_extents. unfold fe_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by (unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia). rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR OIt DTt. clear. unfold off_img, IMG_LO, IMG_TOP in *. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fe_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemEnd in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
pose proof (Z.div_mod t 8 ltac:(lia)) as Dt. rewrite Ht8 in Dt.
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 AMt Ht0 Ht8 Rn Dt. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; first [assumption | lia | match goal with |- ?g => idtac "FACTFAIL" g; fail end].
- unfold sh_ok, fe_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E FBx 10 t 400 t 0 400 RAt).
+ unfold U, FBx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia.
+ lia. + lia.
+ intros x Hx. revert AMt Hx. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros. lia.
Qed.
Lemma fe_sub_nth : forall (T : list byte) (j w k : nat), (k < w)%nat ->
nth_error (sub T (Z.of_nat j) w) k = nth_error T (j + k).
Proof. intros T j w k Hk. unfold sub. rewrite Nat2Z.id, nth_error_firstn. destruct (Nat.ltb_spec k w); [|lia]. apply nth_error_skipn. Qed.
Lemma fe_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
garr8 SEGS m base (map bv_unsigned L) -> nth_error L j = Some b ->
mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base (map bv_unsigned L) j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth (map bv_unsigned L) j 0 (map_nth_error bv_unsigned j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma fe_swrap_small : forall u, 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u -> bv_swrap 32 u = u.
Proof. intros u Hu Hs. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with 4294967296 in *. change (2 ^ (Z.of_N 32 - 1)) with 2147483648 in *. lia. Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma fe_n_val : forall H (m : word -> option byte) t (T : list byte), length T = 400%nat ->
garr8 SEGS (mrestrict H m) t (map bv_unsigned T) -> 0 <= n_of T <= 8 ->
val_mem SEGS (mrestrict H m) (t + 384) 4 (n_of T).
Proof.
intros H m t T LT GT Rn k Hk.
assert (Hlen : length (sub T 384 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn, LT; reflexivity).
pose proof (bytes_le_to_Z_bound (sub T 384 4)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub T 384 4)) as Hb0. rewrite Hlen in Hb1.
assert (Hb : 0 <= bytes_le_to_Z (sub T 384 4) < 2 ^ (8 * Z.of_nat 4)) by (split; [exact Hb0 | exact Hb1]).
assert (Hu : n_of T = u_at T 384 4).
{ unfold n_of, s32_at, u_at in *. apply fe_swrap_small; [|lia]. change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)). exact Hb. }
destruct (nth_error T (384 + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + 384 + Z.of_nat k) with (t + Z.of_nat (384 + k)) by lia.
rewrite (fe_garr8_nth _ t T (384 + k) b GT Hb2). f_equal.
rewrite le_byte_small by first [lia | rewrite Hu; unfold u_at; exact Hb].
rewrite <- (fe_sub_nth T 384 4 k Hk) in Hb2. change (Z.of_nat 384) with 384 in Hb2.
pose proof (YA0j.nth_error_le_byte _ _ _ Hb2) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite Hu. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma fe_bge_n : forall E k (n : Z), ew E k = Z_to_bv 64 n -> 0 <= n <= 8 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (n <=? 0).
Proof.
intros E k n Hk Hn. cbn [branch_taken sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned. unfold bv_lts.
rewrite !YK00.bv_signed_small by lia. rewrite Z.leb_antisym. reflexivity.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma fe_bne_k : forall E k (n c : Z), ew E k = Z_to_bv 64 n -> 0 <= n <= 8 -> -8 <= c <= 0 ->
branch_taken BC_NE (sv_denot E (SOff k c)) (sv_denot E (SLit 0)) = negb (n + c =? 0).
Proof.
intros E k n c Hk Hn Hc. rewrite branch_ne_U, U_SOff, U_lit by lia. rewrite Hk, unsigned_lit_small by lia.
f_equal. unfold zcanon, M64. destruct (Z.eqb_spec ((n + c) mod 2 ^ 64) 0), (Z.eqb_spec (n + c) 0); lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma fe_beq_v : forall E k (v : word), ew E k = v ->
(branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = true <-> v = w64 0).
Proof.
intros E k v Hk. rewrite branch_eq_U, U_SOff, U_lit by lia. rewrite Hk, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 v) as Hv. change (bv_modulus 64) with (2 ^ 64) in Hv.
rewrite zcanon_small by lia. rewrite Z.eqb_eq. unfold w64. rewrite bv_eq, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma fe_aview_nth : forall H (m : word -> option byte) base (L : list byte) j b,
garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> nth_error L j = Some b ->
aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned b).
Proof. intros H m base L j b G Hj. unfold aview. rewrite (fe_garr8_nth _ base L j b G Hj). reflexivity. Qed.
Lemma fe_aview_some : forall H (m : word -> option byte) base (L : list byte) a,
garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> base <= a < base + Z.of_nat (length L) ->
aview SEGS H m a <> None.
Proof.
intros H m base L a G Ha.
destruct (nth_error L (Z.to_nat (a - base))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
replace a with (base + Z.of_nat (Z.to_nat (a - base))) by lia. rewrite (fe_aview_nth H m base L _ b G Hb). discriminate.
Qed.
Lemma fe_mac : forall H (m : word -> option byte) t p (T P : list byte) i,
length T = 400%nat -> length P = 6%nat -> 0 <= i <= 7 ->
garr8 SEGS (mrestrict H m) t (map bv_unsigned T) -> garr8 SEGS (mrestrict H m) p (map bv_unsigned P) ->
((forall i0, 0 <= i0 < 6 -> aview SEGS H m (t + 48 * i + i0) = aview SEGS H m (p + i0)) <-> mac_of T i = P).
Proof.
intros H m t p T P i LT LP Ri GT GP. unfold mac_of.
assert (NT : forall k, (k < 6)%nat -> nth_error (sub T (48 * i) 6) k = nth_error T (Z.to_nat (48 * i) + k)).
{ intros k Hk. replace (48 * i) with (Z.of_nat (Z.to_nat (48 * i))) at 1 by lia. apply fe_sub_nth. exact Hk. }
assert (LS : length (sub T (48 * i) 6) = 6%nat) by (unfold sub; rewrite length_firstn, length_skipn, LT; lia).
assert (VT : forall k b, nth_error T (Z.to_nat (48 * i) + k) = Some b -> aview SEGS H m (t + 48 * i + Z.of_nat k) = Some (bv_unsigned b)).
{ intros k b Hb. replace (t + 48 * i + Z.of_nat k) with (t + Z.of_nat (Z.to_nat (48 * i) + k)) by lia. exact (fe_aview_nth H m t T _ b GT Hb). }
assert (VP : forall k b, nth_error P k = Some b -> aview SEGS H m (p + Z.of_nat k) = Some (bv_unsigned b)).
{ intros k b Hb. exact (fe_aview_nth H m p P k b GP Hb). }
split.
- intros HE. apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
+ rewrite (NT k Hk).
destruct (nth_error T (Z.to_nat (48 * i) + k)) as [b1|] eqn:E1; [|apply nth_error_None in E1; lia].
destruct (nth_error P k) as [b2|] eqn:E2; [|apply nth_error_None in E2; lia].
pose proof (HE (Z.of_nat k) ltac:(lia)) as Hq. rewrite (VT k b1 E1), (VP k b2 E2) in Hq.
injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
+ rewrite (proj2 (nth_error_None (sub T (48 * i) 6) k) ltac:(lia)), (proj2 (nth_error_None P k) ltac:(lia)). reflexivity.
- intros HE i0 Hi0. pose proof (NT (Z.to_nat i0) ltac:(lia)) as Hn. rewrite HE in Hn.
destruct (nth_error P (Z.to_nat i0)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
replace i0 with (Z.of_nat (Z.to_nat i0)) by lia. rewrite (VP _ b Eb). symmetry in Hn. rewrite (VT _ b Hn). reflexivity.
Qed.
Lemma fe_hull_sub : forall rd a n a' n', shadow_hull_vis rd a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> 0 < n' ->
shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' HV Ha H1 H2 Hn s Hs. apply HV. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma fe_meq_frame : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m1 a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 lo hi HF Hw HM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 (fun a => lo <= a < hi) HF Hw a Ha Hn). exact (HM a Ha Hn).
Qed.
Theorem pb_find_entry : tfind_entry_spec.
Proof.
unfold tfind_entry_spec.
intros fq ly S W regs mem md ch t p T P HPRE HRO H10 H11 Ht0 Ht8 Ht63 Hp0 Hp63 LT GT LP GP AMt AMp RAt SHt RAp SHp DTt OIt DTp T1.
pose proof (pa_segs_low) as Hsegs.
set (n := n_of T) in *.
assert (Rn : 0 <= n <= 8) by exact T1.
pose proof (fe_n_val (w_H W) mem t T LT GT T1) as VN. fold n in VN.
destruct (fe_entry fq ly S W regs mem md ch t n HPRE H10 Ht0 Ht8 AMt OIt DTt Rn VN RAt) as [HS SHOK].
pose proof (ajournal_init SEGS B TFIND_ENTRY_STK [] ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch HPRE) as HJ.
rewrite fe_spZ8 in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite fe_spZ8 in Hstk, Hpres.
assert (N1 : (1%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
assert (N3 : (3%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
assert (N4 : (4%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
unfold raZ in Hra4. rewrite (fe_getr8 regs _ 1 N1) in Hra, Hra4. rewrite (fe_getr8 regs _ 3 N3) in Hgp. rewrite (fe_getr8 regs _ 4 N4) in Htp.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TFIND_ENTRY_STK = 8240) by reflexivity.
remember (EF regs n) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EF; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (fe_extra n)) k) by (intros k Hk; subst E; unfold EF; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fe_extra n)) E) by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_find_entry)) with (Z_to_bv 64 (BASE + AF_find_entry)).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
assert (AG0 : forall k, (k < 512)%nat -> ew E k = ew E k) by (intros; reflexivity).
assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TFIND_ENTRY_STK <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
assert (NP0 : forall j, 0 <= j < 0 -> mac_of T j <> P) by (intros; lia).
let fe_win AG := (idtac;
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros b wlo whi a Hin Ha; vm_compute in Hin;
repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; cbn [base_val] in Ha; rewrite ?AG in Ha by lia; rewrite ?Usp in Ha; unfold TFIND_ENTRY_STK, ESTACK; lia|]);
destruct Hin) in
let upd_meq := idtac;
lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ mem a |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Eh k = ew E k |- _ => H end in
let MEQ2 := fresh "MEQ" in
pose proof (fe_meq_frame Eh rs (w_H W) mem m1 m2 (spZ regs - TFIND_ENTRY_STK) (spZ regs) HFr ltac:(fe_win AG) MEQ) as MEQ2;
clear MEQ
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end in
let rebase_env En :=
tryif is_var En then idtac else
lazymatch goal with AG : forall k, (k < 512)%nat -> ew ?Eo k = ew E k, HAE : env_agree 32 (Ereg regs (fe_extra n)) ?Eo |- _ =>
let E2 := fresh "Ec" in
set (E2 := En) in *;
let AG2 := fresh "AG" in let HAE2 := fresh "HAE" in
assert (AG2 : forall k, (k < 512)%nat -> ew E2 k = ew E k) by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
assert (HAE2 : env_agree 32 (Ereg regs (fe_extra n)) E2) by (split; [intros kk Hkk; rewrite AG2 by lia; rewrite <- (AG kk) by lia; exact (proj1 HAE kk Hkk) | subst E2; cbn [ed ewset havoc]; exact (proj2 HAE)]);
lazymatch Eo with
| E => idtac
| _ => repeat match goal with H : ew Eo ?kk = ?vv |- _ => let H2 := fresh "EV" in assert (H2 : ew E2 kk = vv) by (subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact H); clear H end
end;
clearbody E2; clear AG HAE;
repeat match goal with H : img_env _ _ ?Ex |- _ => lazymatch Ex with E2 => fail | _ => clear H end end
end in
let rebase := idtac;
lazymatch goal with
| HS : st_ok_pi _ _ ?En _ _ |- _ => rebase_env En
| HS : st_ok _ ?En _ _ |- _ => rebase_env En
end in
let awr := idtac; awr_ok_tac; first [exact Usp | lazymatch goal with AG : forall k, (k < 512)%nat -> ew ?Eo k = ew E k |- _ => rewrite ?AG by lia; exact Usp end] in
let conv := idtac;
lazymatch goal with
| Hc : branch_taken BC_GE (sv_denot ?Ex (SLit 0)) (sv_denot ?Ex (SOff 32 0)) = ?bb |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ex k = ew E k |- _ => H end in
rewrite (fe_bge_n Ex 32 n (eq_trans (AG 32%nat ltac:(lia)) E32) Rn) in Hc;
lazymatch bb with
| true => apply Z.leb_le in Hc
| false => apply Z.leb_gt in Hc; let H' := fresh "HLT" in rename Hc into H'
end
| Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff ?kk 0)) (sv_denot ?Ex (SLit 0)) = ?bb |- _ =>
lazymatch goal with EV : ew Ex kk = ?v, XC : ?v = w64 0 <-> mac_of T ?i = P |- _ =>
let MI := fresh "MI" in
lazymatch bb with
| true => pose proof (proj1 XC (proj1 (fe_beq_v Ex kk v EV) Hc)) as MI
| false =>
assert (MI : mac_of T i <> P) by (let X := fresh in intros X; apply (proj2 XC) in X; apply (proj2 (fe_beq_v Ex kk v EV)) in X; rewrite X in Hc; discriminate Hc);
lazymatch goal with NP : forall j, 0 <= j < ?i0 -> mac_of T j <> P |- _ =>
let i1 := eval vm_compute in (i + 1) in
let NP2 := fresh "NP" in
assert (NP2 : forall j, 0 <= j < i1 -> mac_of T j <> P) by (let j := fresh in let Hj := fresh in intros j Hj; destruct (Z.eq_dec j i) as [->|?]; [exact MI | apply NP; lia]);
clear NP
end
end; clear Hc EV XC
end
| Hc : branch_taken BC_NE (sv_denot ?Ex (SOff 32 ?c)) (sv_denot ?Ex (SLit 0)) = ?bb |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ex k = ew E k |- _ => H end in
rewrite (fe_bne_k Ex 32 n c (eq_trans (AG 32%nat ltac:(lia)) E32) Rn ltac:(lia)) in Hc;
lazymatch bb with
| true => apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc;
lazymatch goal with HLT : ?i < n |- _ =>
let i1 := eval vm_compute in (i + 1) in
let H2 := fresh "HLT" in assert (H2 : i1 < n) by lia; clear HLT Hc end
| false => apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc
end
end in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ssx (restrict _ ?msc) |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ec k = ew E k |- _ => H end in
let HAEc := lazymatch goal with H : env_agree 32 (Ereg regs (fe_extra n)) Ec |- _ => H end in
let MEQ := lazymatch goal with H : forall a, _ -> _ -> aview _ _ (ms_mem msc) a = aview _ _ mem a |- _ => H | H : forall a, _ -> _ -> aview _ _ _ a = aview _ _ mem a |- _ => H end in
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold tfind_entry_post; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; rewrite ?AG by lia; rewrite E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (fe_extra n) HS); [exact HAEc | vm_compute; reflexivity]|];
split; [apply Permutation_refl|];
split; [| exact MEQ];
let a0v := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in
lazymatch a0v with
| SLit 18446744073709551615 => exists (-1)
| SLit ?z => exists z
end;
split; [cbn [ms_regs]; rewrite R10; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|];
unfold find_res;
first [ left; split; [reflexivity|]; let j := fresh in let Hj := fresh in intros j Hj; first [lia | lazymatch goal with NP : forall j, 0 <= j < _ -> mac_of T j <> P |- _ => apply NP; lia end]
| right; split; [lia|]; split; [assumption | lazymatch goal with NP : forall j, 0 <= j < _ -> mac_of T j <> P |- _ => exact NP end]
| match goal with |- ?g => idtac "LEAFFAIL" g end; fail ]
end in
let call := idtac;
lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX) |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ec k = ew E k |- _ => H end in
let HAEc := lazymatch goal with H : env_agree 32 (Ereg regs (fe_extra n)) Ec |- _ => H end in
let HEIc := lazymatch goal with H : img_env _ _ Ec |- _ => H end in
let MEQ := lazymatch goal with H : forall a, _ -> _ -> aview _ _ _ a = aview _ _ mem a |- _ => H end in
let a0sv := eval vm_compute in (sr_get (ss_regs ssc) 10%bv) in
let c := lazymatch a0sv with SOff 10%nat ?c => c end in
let i := eval vm_compute in (c / 48) in
let K := run_K_hi HS in
let K4 := eval vm_compute in (K + 4)%nat in
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
rewrite ?AG in Ra0, Ra1, Qsp, Qgp, Qtp by lia;
rewrite ?E10 in Ra0; rewrite ?E11 in Ra1; rewrite ?Usp in Qsp; rewrite ?E3 in Qgp; rewrite ?E4 in Qtp;
let HspU := fresh "HspU" in
assert (HspU : spZ (ms_regs msX) = spZ regs + -48) by (unfold spZ at 1; rewrite Qsp; apply unsigned_lit_small; lia);
pmkst HS;
eapply SRr_bind;
[ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS Hsegs (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs msX) (ms_mem msX) TFIND_ENTRY_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (t + 48 * i) p 6 (-48) (Z_to_bv 64 (BASE + 13852)) HJ);
[ rewrite Ra0; unfold w64; f_equal; rewrite ?unsigned_lit_small by lia; lia
| exact Ra1
| exact Ra2
| lia | lia | lia | lia | lia
| exact HspU
| reflexivity | lia | unfold TFIND_ENTRY_STK, ESTACK; lia
| rewrite Qgp; exact Hgp
| rewrite Qtp; exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [lia | reflexivity]
| let a := fresh in let Ha := fresh in intros a Ha; split; [rewrite MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia); apply (fe_aview_some (w_H W) mem t T a GT); rewrite LT; cbn; lia | rewrite HspU; unfold ESTACK; lia]
| let a := fresh in let Ha := fresh in intros a Ha; split; [rewrite MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia); apply (fe_aview_some (w_H W) mem p P a GP); rewrite LP; cbn; lia | rewrite HspU; unfold ESTACK; lia]
| let a := fresh in let Ha := fresh in intros a Ha; unfold ESTACK; lia
| let a := fresh in let Ha := fresh in intros a Ha; unfold ESTACK; lia
| unfold amem_range in *; lia
| exact AMp
| apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TFIND_ENTRY_STK) (spZ regs));
[ let s := fresh in let Hs := fresh in let Hn := fresh in intros s Hs Hn; apply MEQ; [exact Hs | exact Hn] | rewrite C2; unfold TFIND_ENTRY_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia
| apply (range_addressable_sub _ _ t 400); [exact RAt | lia | lia] ]
| intros _; apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TFIND_ENTRY_STK) (spZ regs));
[ let s := fresh in let Hs := fresh in let Hn := fresh in intros s Hs Hn; apply MEQ; [exact Hs | exact Hn] | rewrite C2; unfold TFIND_ENTRY_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | lia
| apply (fe_hull_sub _ t 400); [exact SHt | lia | lia | lia | lia] ]
| apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TFIND_ENTRY_STK) (spZ regs));
[ let s := fresh in let Hs := fresh in let Hn := fresh in intros s Hs Hn; apply MEQ; [exact Hs | exact Hn] | rewrite C2; unfold TFIND_ENTRY_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia
| exact RAp ]
| intros _; apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TFIND_ENTRY_STK) (spZ regs));
[ let s := fresh in let Hs := fresh in let Hn := fresh in intros s Hs Hn; apply MEQ; [exact Hs | exact Hn] | rewrite C2; unfold TFIND_ENTRY_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | lia
| exact SHp ] ]
| cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
let v := fresh "v" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let Hv := fresh "Hv" in let Hcmp := fresh "Hcmp" in
let Hfr2 := fresh "Hfr2" in let Hpres2 := fresh "Hpres2" in let HPP := fresh "HPP" in
intros W2 c2 _ HPP; destruct HPP as (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2);
let XC := fresh "XC" in
assert (XC : v = w64 0 <-> mac_of T i = P)
by (rewrite Hcmp; rewrite <- (fe_mac (w_H W) mem t p T P i LT LP ltac:(lia) GT GP);
let HH := fresh "HH" in let i0 := fresh "i0" in let Hi0 := fresh "Hi0" in split; intros HH i0 Hi0; specialize (HH i0 Hi0);
[ rewrite !MEQ in HH by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia); exact HH
| rewrite !MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia); exact HH ]);
let MEQ2 := fresh "MEQ" in
assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TFIND_ENTRY_STK <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
by (let a := fresh in let Ha := fresh in let Hn := fresh in intros a Ha Hn; rewrite Hfr2 by (unfold TFIND_ENTRY_STK, ESTACK in *; lia); apply MEQ; assumption);
let HS2 := fresh "HS" in
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
match type of HS2 with ?tt -> _ => let HRK := fresh in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
eapply region_kept_aview;
[ rewrite ?AG by lia; exact Usp
| let a := fresh in let Ha := fresh in intros a Ha; apply Hfr2; unfold ESTACK; lia
| exact Hpres2 ]
| clear HS; rewrite <- restrict_mkst_fx in HS2;
lazymatch type of HS2 with st_ok_pi _ _ ?En _ _ =>
let E2 := fresh "Ec" in
set (E2 := En) in HS2;
let HEI2 := fresh "HEI" in let AG2 := fresh "AG" in let HAE2 := fresh "HAE" in let EV := fresh "EV" in let SHOK2 := fresh "SHOK" in
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc_hi; [exact HEIc | cbv; lia]);
assert (AG2 : forall k, (k < 512)%nat -> ew E2 k = ew E k) by (intros kk Hkk; subst E2; rewrite ew_havoc_old by lia; apply AG; exact Hkk);
assert (HAE2 : env_agree 32 (Ereg regs (fe_extra n)) E2) by (subst E2; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]);
assert (EV : ew E2 K4 = v) by (subst E2; change K4 with (K + 4)%nat; rewrite (ew_havoc_new Ec K _ 4 (Z_to_bv 64 0)) by (cbn; lia); exact Hv);
clearbody E2;
pose proof (Forall_nil (shent_ok SEGS FBx E2 (mrestrict (w_H W) mem2)) : sh_ok SEGS FBx [] E2 (mrestrict (w_H W) mem2)) as SHOK2;
clear AG HAEc HEIc MEQ Hcmp Hfr2 Hpres2 HP2 Hv Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp HspU;
repeat match goal with H : sh_ok _ _ _ ?Ex _ |- _ => lazymatch Ex with E2 => fail | _ => clear H end end;
clear HJ; rename HJ2 into HJ
end ] ]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK FBspan; [awr |];
upd_meq; rebase;
lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => call; go
| HS' : st_ok_pi _ _ ?Ec ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx FBspan SH (start K Bx FBspan SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' FBspan;
[ conv; first [ exfalso; lazymatch goal with HLT : _ < n |- _ => clear - HLT Rn; lia end | go ]
| conv; first [ exfalso; lazymatch goal with HLT : _ < n |- _ => clear - HLT Rn; lia end | go ] ]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End h.
End f.
End d.
