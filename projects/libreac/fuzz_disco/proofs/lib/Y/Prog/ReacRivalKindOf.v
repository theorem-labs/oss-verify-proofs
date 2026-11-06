(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue_defect.v, with its module paths, module names and numbers changed; 282 of its 366 lines of code are new or changed and 575 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rival_kind_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_RIVAL_KIND_OF_STK : Z := 16 + ESTACK.
Definition treac_rival_kind_of_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (e r d s c : Z) : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B REAC_RIVAL_KIND_OF_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if e =? 0 then 0 else reac_rival_kind_model d r s c) /\
       Permutation (ablocks B ly' S') (ablocks B ly S) /\ W' = W /\
       (forall a : word, ~ (spZ regs - REAC_RIVAL_KIND_OF_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a)).
Definition treac_rival_kind_of_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e r d s c : Z),
  afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  (e <> 0 ->
     e + 24 <= 2 ^ 63 /\ in_app (e + 8) 16 /\ off_img (e + 8) 16 /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 16 /\
     (forall a, e + 8 <= a < e + 24 -> apresent (w_H W) mem a) /\
     -2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_rival_kind_of) regs mem md)
    (treac_rival_kind_of_post fq regs ly S W mem md e r d s c).
Section w.
Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
Import YN3v YI04 YI09 YI08 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC8g YM05.
Context {fx : YK11.FPState}.
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Definition SB_RK : Z := 0x7fff8000.
Definition Bspan_RK : Z * Z := (SB_RK, SB_RK + 2 ^ 44 - 1).
Definition Bx_RK : sv := SOff 36 0.
Definition Bx_RK0 : sv := SLit SB_RK.
Definition rk_regions : smem := [stack_region 16; got_regionP; bcell_regionP 36;
YP09.mkRegion (Some 10%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0)); YP09.mkChunk 12 (CVal 1 (SOff 33 0));
YP09.mkChunk 16 (CVal 1 (SOff 34 0)); YP09.mkChunk 20 (CVal 4 (SOff 35 0))]].
Definition rk_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4088 140737479966720 3); (32%nat, mkAF 0 4294967295 0);
(33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 4294967295 0); (36%nat, mkAF SB_RK SB_RK 0)] [] [].
Definition ss_rk : sstate := mkSS AF_both3_reac_rival_kind_of sr_atoms rk_regions None rk_facts.
Definition ss_rk0 : sstate := mkSS AF_both3_reac_rival_kind_of sr_atoms [stack_region 16] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition ss_rk0p : sstate := mkSS AF_both3_reac_rival_kind_of (sr_set sr_atoms 10%bv (SLit 0)) [stack_region 16] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition rk_SH : list shent := [mkSHE 10 8 24].
Definition rk_extra (r d s c : Z) : list word := map (Z_to_bv 64) [r mod 2 ^ 32; d; s; c; SB_RK].
Lemma val_mem_mod32 : forall (m : word -> option byte) a v, val_mem SEGS m a 4 v -> val_mem SEGS m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity. rewrite Zmod_mod. reflexivity.
Qed.
Lemma rk_kept_step : forall E rs (m0 m1 m2 : word -> option byte) lo hi,
frame_of E rs m1 m2 ->
(forall rr a, In rr rs -> base_val E (r_base rr) + r_wlo rr <= a < base_val E (r_base rr) + r_whi rr -> lo <= a < hi) ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> m1 x = m0 x) ->
forall x : word, ~ (lo <= bv_unsigned x < hi) -> m2 x = m0 x.
Proof.
intros E rs m0 m1 m2 lo hi HF Hw K x Hx. rewrite (HF x); [exact (K x Hx)|].
intros (rr & Hin & Ha). exact (Hx (Hw rr _ Hin Ha)).
Qed.
Lemma rk_entry : forall ly S W (regs : bvmap 5 word) mem md ch (e r d s c : Z),
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
in_app (e + 8) 16 -> off_img (e + 8) 16 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 16 ->
-2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= s < 2 ^ 8 -> 0 <= c < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rk_extra r d s c))) ss_rk
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_rival_kind_of)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx_RK rk_SH (Eimg (Ereg regs (rk_extra r d s c))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch e r d s c HPRE H10 Re He8 Hia Hoi Hrad Rr Rd Rs Rc M8 M12 M16 M20.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
assert (Heb : 4096 <= e + 8 /\ e + 24 <= 140737479966720) by (revert Hia C1; clear; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 12)) as VR12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rk_extra r d s c))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rk_extra r d s c)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 e) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (r mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 SB_RK) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E43 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Rm : 0 <= r mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
split.
- unfold ss_rk. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rk_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 36 0) SB_RK);
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_RK; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat e E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
-- apply (chunk_ok_val SEGS E _ e 8 4 _ (r mod 2 ^ 32)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_mod32 _ _ _ M8).
-- apply (chunk_ok_val SEGS E _ e 12 1 _ d); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M12].
-- apply (chunk_ok_val SEGS E _ e 16 1 _ s); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M16].
-- apply (chunk_ok_val SEGS E _ e 20 4 _ c); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M20].
+ apply pairwise_disjoint_of_extents. unfold rk_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat e E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hia Hoi C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rk_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB_RK; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 Hia C1 C3 WS Hstk0 Rm Rd Rs Rc He8. clear.
unfold SB_RK, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rk_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bx_RK 10 (e + 8) 16 e 8 24 Hrad).
+ unfold U, Bx_RK. cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB_RK; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. revert Hia Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma rk_agree_ewset : forall k E E' n v, (k <= n)%nat -> env_agree k E E' -> env_agree k E (ewset E' n v).
Proof. intros k E E' n v Hk [A D]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply A; lia | exact D]. Qed.
Lemma U_sx32_val : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if v <? 2 ^ 31 then v else v + 2 ^ 64 - 2 ^ 32.
Proof.
intros E n v H Hv. rewrite U_SExt, (U_atom E n v H) by lia. cbv beta iota.
change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small v) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with 2147483648 by reflexivity. replace (bv_modulus 32) with 4294967296 by reflexivity.
destruct (Z.ltb_spec v (2 ^ 31)); Z.div_mod_to_equations; lia.
Qed.
Lemma U_sx32_eqk_s : forall E n r k, ew E n = Z_to_bv 64 (r mod 2 ^ 32) -> -2 ^ 31 <= r < 2 ^ 31 -> 0 <= k < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? k) = (r =? k).
Proof.
intros E n r k H Hr Hk. rewrite (U_sx32_val E n (r mod 2 ^ 32) H) by (apply Z.mod_pos_bound; lia).
apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq.
destruct (Z.ltb_spec (r mod 2 ^ 32) (2 ^ 31)); split; intros; Z.div_mod_to_equations; lia.
Qed.
Lemma U_sx32_eqk_u : forall E n c k, ew E n = Z_to_bv 64 c -> 0 <= c < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? k) = (c =? k).
Proof.
intros E n c k H Hc Hk. rewrite (U_sx32_val E n c H Hc).
apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. destruct (Z.ltb_spec c (2 ^ 31)); split; intros; lia.
Qed.
Lemma U_sx32_ltk_u : forall E n c k, ew E n = Z_to_bv 64 c -> 0 <= c < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) <? k) = (c <? k).
Proof.
intros E n c k H Hc Hk. rewrite (U_sx32_val E n c H Hc).
apply Bool.eq_iff_eq_true. rewrite !Z.ltb_lt. destruct (Z.ltb_spec c (2 ^ 31)); split; intros; lia.
Qed.
Lemma U_m1_lt39 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
(U E (SOff n (-1)) <? 39) = ((1 <=? v) && (v <? 40)).
Proof.
intros E n v H Hv. rewrite U_SOff, H, unsigned_lit_small by lia. unfold zcanon, M64.
apply Bool.eq_iff_eq_true. rewrite andb_true_iff, !Z.ltb_lt, Z.leb_le.
destruct (Z.eqb_spec v 0) as [->|Hv0].
- change ((0 + -1) mod 2 ^ 64) with (2 ^ 64 - 1). split; intros; lia.
- rewrite Z.mod_small by lia. split; intros; lia.
Qed.
Lemma rk_entry0 : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_rk0p
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_rival_kind_of)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx_RK0 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE H10. split; [|constructor].
apply (st_ok_pi_pin_reg' _ ss_rk0 _ 10%bv 0); [| cbn [restrict ms_regs mkst]; exact H10 | reflexivity].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew (Eimg (Ereg regs [])) 10) = 0)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; reflexivity).
rewrite restrict_mkst_fx. unfold ss_rk0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16.
revert Hslo Hshi H47 Hceil Hal16 C1 WS Hstk0. clear. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Ltac rk_side := first [ cbn [ew ewset Nat.eqb]; assumption | lia ].
Ltac rk_wr Usp :=
let rr := fresh "rr" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros rr a Hin Ha;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
cbn [In] in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction; subst rr;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
first [ lia | (cbn [ew ewset Nat.eqb] in Ha; rewrite Usp in Ha; lia) ].
Ltac rk_kept Usp :=
lazymatch goal with KEPT : forall x : word, ~ (?lo <= bv_unsigned x < ?hi) -> ?m1 x = ?m0 x, HF : frame_of ?Ex ?rs ?m1 ?m2 |- _ =>
let K2 := fresh "KEPT" in
pose proof (rk_kept_step Ex rs m0 m1 m2 lo hi HF ltac:(rk_wr Usp) KEPT) as K2; clear KEPT HF; rename K2 into KEPT end.
Ltac rk_U r d s c H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_lit in H by lia;
rewrite ?(U_sx32_eqk_s _ 32 r) in H by rk_side;
rewrite ?(U_sx32_eqk_u _ 35 c) in H by rk_side;
rewrite ?(U_sx32_ltk_u _ 35 c) in H by rk_side;
rewrite ?(U_m1_lt39 _ 34 s) in H by rk_side;
rewrite ?(U_atom _ 33 d) in H by rk_side;
rewrite ?(U_atom _ 34 s) in H by rk_side.
Ltac rk_leaf ly S Hra Hsegs HAE E1 :=
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_rival_kind_of_post; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS);
  [repeat first [exact HAE | apply rk_agree_ewset; [cbv; lia|]] | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10|];
[| split; [apply Permutation_refl|]; split; [reflexivity|];
  lazymatch goal with K : forall x : word, ~ _ -> _ x = _ x |- _ =>
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; apply K; unfold REAC_RIVAL_KIND_OF_STK, ESTACK in Hx; lia end ]
end.
Ltac rk_go leafm ly S Hra Hsegs HAE E1 Usp Bsp :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bsp; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
rk_kept Usp;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HS' : st_ok_pi _ _ ?Ex ?ss0 _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss0) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx Bsp SH (start K Bx Bsp SH ss0) end in
lazymatch why with
| SR_jalr _ => rk_leaf ly S Hra Hsegs HAE E1; leafm
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bsp; [rk_go leafm ly S Hra Hsegs HAE E1 Usp Bsp | rk_go leafm ly S Hra Hsegs HAE E1 Usp Bsp]
end end end.
Lemma rk_walk : forall ly S W (regs : bvmap 5 word) mem md ch (e r d s c : Z),
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
(e <> 0 ->
e + 24 <= 2 ^ 63 /\ in_app (e + 8) 16 /\ off_img (e + 8) 16 /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 16 /\
(forall a, e + 8 <= a < e + 24 -> apresent (w_H W) mem a) /\
-2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_rival_kind_of) regs mem md)
(treac_rival_kind_of_post fx regs ly S W mem md e r d s c).
Proof.
intros ly S W regs mem md ch e r d s c HPRE HRO H10 Re He8 HF.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof (ajournal_init SEGS B REAC_RIVAL_KIND_OF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (KEPT : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mem x = mem x) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_rival_kind_of)) with (Z_to_bv 64 (BASE + AF_both3_reac_rival_kind_of)).
destruct (Z.eq_dec e 0) as [He0 | He0].
- subst e. clear HF.
destruct (rk_entry0 ly S W regs mem md ch HPRE H10) as [HS SHOK].
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
rk_go ltac:(first [rewrite E10, H10; reflexivity | reflexivity]) ly S Hra Hsegs HAE E1 Usp Bspan_RK.
- destruct (HF He0) as (He24 & Hia & Hoi & Hrad & Hpr & Rr & Rd & Rs & Rc & M8 & M12 & M16 & M20). clear HF.
destruct (rk_entry ly S W regs mem md ch e r d s c HPRE H10 Re He8 Hia Hoi Hrad Rr Rd Rs Rc M8 M12 M16 M20) as [HS SHOK].
remember (Eimg (Ereg regs (rk_extra r d s c))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rk_extra r d s c)) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (r mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rk_extra r d s c)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
rk_go ltac:(repeat match goal with H : branch_taken _ _ _ = _ |- _ => rk_U r d s c H; revert H end; intros;
  unfold w64; f_equal; rewrite (proj2 (Z.eqb_neq e 0) He0); unfold reac_rival_kind_model;
  repeat match goal with H : ?t = ?b |- context [if ?t then _ else _] => rewrite H end;
  reflexivity) ly S Hra Hsegs HAE E1 Usp Bspan_RK.
Qed.
End w.
Theorem pb_reac_rival_kind_of : treac_rival_kind_of_spec.
Proof. intros fq. exact (rk_walk (fx := fq)). Qed.
End h.
End f.
End d.
