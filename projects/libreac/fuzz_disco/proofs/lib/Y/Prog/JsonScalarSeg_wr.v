(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/JtokIs.v, with its module paths and module names changed; 173 of its 222 lines of code are new or changed and 580 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s YC85 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import JtokIs.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import JsonScalarCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Variables MC_CONSTS_LO MC_CONSTS_HI : Z.
Hypothesis ASTRLEN : forall fq : YK11.FPState, astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis AMEMCHR : forall fq : YK11.FPState, amemchr_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_memchr).
Hypothesis MCROM : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom SEGS a.
Hypothesis GLOBS : globs_marked SEGS B tfib_globs.
Hypothesis IMGV : img_shadow_vis SEGS B.
Hypothesis ROU : tfib_ro_unowned B.
#[local] Notation tjson_scalar_str := (@tjson_scalar_str rc PI).
#[local] Notation tjson_scalar_img := (@tjson_scalar_img rc PI).

Section w.
Context {fx : YK11.FPState}.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sa : astate) (W0 : world SEGS) (mem0 : word -> option byte)
  (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (kk : Z) (b i n v spe : Z) (BS : list byte).
#[local] Notation BZ := (@BZ BS).
Hypothesis ZL : Z.of_nat (length BS) = n.
Hypothesis Zin : 0 <= i < n.
Hypothesis Zb0 : 0 < b.
Hypothesis Zbm : amem_range b n.
Hypothesis ZBg : garr8 SEGS (mrestrict (w_H W) memc) b BZ.
Hypothesis Zbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n.
Hypothesis Zbsh : shadow_hull_vis (aview SEGS (w_H W) memc) b n.
Hypothesis Zbw : b + n <= spe - TJSON_SCALAR_STK \/ spe <= b.
Hypothesis Zboi : off_img b n.
Hypothesis Zbv : b + n <= v \/ v + 20 <= b.
Hypothesis Zv0 : 0 < v.
Hypothesis Zv8 : v mod 8 = 0.
Hypothesis Zvm : amem_range v 20.
Hypothesis Zvw : spe <= v \/ v + 20 <= spe - TJSON_SCALAR_STK.
Hypothesis Zvoi : off_img v 20.
Hypothesis Zvwr : forall a, v <= a < v + 20 ->
  awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Hypothesis Zvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20.
Hypothesis Zvsh : shadow_hull_vis (aview SEGS (w_H W) memc) v 20.
Hypothesis Zspa : alloc_ceiling <= spe - TJSON_SCALAR_STK.
Hypothesis Zsp47 : spe <= 2 ^ 47.
Hypothesis Zsp16 : spe mod 16 = 0.
Hypothesis ZspS : sp0 - STK <= spe - TJSON_SCALAR_STK.
Hypothesis Zsp0 : spe <= sp0.
Hypothesis Zsp016 : sp0 mod 16 = 0.
Hypothesis ZIMG : tjson_scalar_img W memc.
Hypothesis ZCV : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc.
#[local] Notation JW := (@JW rc PI W memc spe).
#[local] Notation MK := (@MK rc PI W spe).
#[local] Notation SEGPOST := (@SEGPOST rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W kk b v spe).
#[local] Notation js_nums := (@js_nums rc sp0 b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_low := (@jw_low rc PI sp0 W memc i n v spe BS Zin Zv0 Zsp47).
#[local] Notation jw_of_mk := (@jw_of_mk rc PI sp0 W memc i n v spe BS Zin).
#[local] Notation mk_refl := (@mk_refl rc PI W spe).
#[local] Notation mk_trans := (@mk_trans rc PI W b i n v spe Zin Zbw Zbv Zvw).
#[local] Notation mk_frame := (@mk_frame rc PI sp0 W b i n v spe BS Zin Zbw Zbv Zvw).
#[local] Notation mk_call := (@mk_call rc PI sp0 W b i n v spe BS Zin Zb0 Zbw Zbv Zv0 Zvw Zsp16 Zsp0 Zsp016).
#[local] Notation seg_chain := (@seg_chain rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W kk b i n v spe Zin Zbw Zbv Zvw).
#[local] Notation jw_B := (@jw_B rc PI sp0 W memc b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_Bra := (@jw_Bra rc PI sp0 W memc b i n v spe BS Zin Zb0 Zbm Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_vra := (@jw_vra rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zvra Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_vpres := (@jw_vpres rc PI B STK sp0 FP ly Sa own lyc Sc W memc v spe Zvwr).
#[local] Notation jw_cv := (@jw_cv rc PI MC_CONSTS_LO MC_CONSTS_HI MCROM sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZCV).
#[local] Notation jw_imgaddr := (@jw_imgaddr rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_tstr := (@jw_tstr rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_litab := (@jw_litab rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZIMG).
#[local] Notation jw_str14 := (@jw_str14 rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZIMG).
#[local] Notation jstr_fuel := (@jstr_fuel sp0 i n v spe BS Zin).
#[local] Notation jstr_fuel_eq := (@jstr_fuel_eq sp0 i n v spe BS Zin Zv0).
#[local] Notation jstr_fuel_any := (@jstr_fuel_any sp0 i n v spe BS Zin Zv0).
#[local] Notation jdigits_fuel := (@jdigits_fuel sp0 i n v spe BS Zin).
#[local] Notation jdigits_fuel_any := (@jdigits_fuel_any sp0 i n v spe BS Zin Zv0).
#[local] Notation ew_EiR := (@ew_EiR rc PI sp0 i n v spe BS Zin).
#[local] Notation ew_EiX := (@ew_EiX rc PI sp0 i n v spe BS Zin).
#[local] Notation js_awr_v := (@js_awr_v rc PI B STK sp0 FP ly Sa own lyc Sc W memc v Zvwr).
#[local] Notation js_v_app := (@js_v_app rc sp0 i n v spe BS Zin Zv0 Zv8 Zvm).
#[local] Notation jrest_exp := (@jrest_exp i BS).
#[local] Notation jrest_frac := (@jrest_frac i BS).
#[local] Notation jx_extra := (@jx_extra b BS).
#[local] Notation jbyte_range := (@jbyte_range sp0 i n v spe BS Zin).
#[local] Notation garr8_at := (@garr8_at rc PI sp0 i n v spe BS Zin Zv0).
#[local] Notation st_ok_pi_add_cond := (@st_ok_pi_add_cond rc PI fx).
#[local] Notation U_offm := (@U_offm sp0 i n v spe BS Zin).
#[local] Notation z256 := (@z256 sp0 i n v spe BS Zin Zv0).
#[local] Notation bf_digit_ltu := (@bf_digit_ltu sp0 i n v spe BS Zin Zv0).
#[local] Notation jlen_BZ := (@jlen_BZ n BS ZL).
#[local] Notation jdigits_nd := (@jdigits_nd sp0 i n v spe BS ZL Zin Zv0).
#[local] Notation jdigits_d := (@jdigits_d sp0 i n v spe BS ZL Zin Zv0).
#[local] Notation jdigits_n := (@jdigits_n n BS ZL).
#[local] Notation jrest_exp_n := (@jrest_exp_n i n BS ZL).
#[local] Notation add_breg := (@add_breg rc PI fx sp0 W memc b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation obl_B := (@obl_B rc PI sp0 W memc b i n v spe BS Zin Zb0 Zbm Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jdig_at_ge := (@jdig_at_ge sp0 i n v spe BS ZL Zin).
#[local] Notation jdig_at_lt := (@jdig_at_lt sp0 i n v spe BS ZL Zin).
#[local] Notation jstr_ge := (@jstr_ge sp0 i n v spe BS ZL Zin).
#[local] Notation bf_hex2 := (@bf_hex2 sp0 i n v spe BS Zin Zv0).
#[local] Notation bf_hex1 := (@bf_hex1 sp0 i n v spe BS Zin Zv0).
#[local] Notation SLP := (@SLP rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS).
#[local] Notation HXP := (@HXP rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe).
#[local] Notation jm_extra := (@jm_extra b i BS).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Ltac ereg q r H := rewrite (ew_EiR _ _ q r) by (cbv; first [lia | reflexivity]); exact H.
Lemma U_subf : forall E0 a c x y, ew E0 a = Z_to_bv 64 x -> ew E0 c = Z_to_bv 64 y -> 0 <= y <= x -> x < 2 ^ 64 ->
  U E0 (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff c 0) (SLit (-1)))) = x - y.
Proof.
intros E0 a c x y Ha Hc Hy Hx. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E0 a x Ha), (U_atom E0 c y Hc), U_SLit by lia.
unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (x + y * (2 ^ 64 - 1)) with ((x - y) + y * 2 ^ 64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Definition vreg9 : YP09.region := YP09.mkRegion (Some 9%nat) 0 20 0 20 [].
Definition wr_facts : facts :=
  mkFacts [ (2%nat, jSP); (10%nat, mkAF 0 (2 ^ 47 - 1) 0); (15%nat, jIDX); (9%nat, jVP); (18%nat, mkAF 1 (2 ^ 47 - 2) 0); (27%nat, jSB) ] [] [].
Definition ss_wr : sstate := mkSS A_WR sr_atoms [vreg9] None wr_facts.
Lemma seg_wr : forall regs m md j3,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 10 = w64 j3 -> getr regs 15 = w64 i -> getr regs 9 = w64 v ->
  getr regs 18 = w64 (b + i) -> getr regs 27 = w64 SHADOW_OFF -> i <= j3 <= n ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_WR)) m (seg_rom SEGS)) md) (SEGPOST m regs (Some (j3, 2, i, j3 - i))).
Proof.
intros regs m md j3 HJ HW H2 H10 H15 H9 H18 H27 Hj.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E10 : ew E 10 = Z_to_bv 64 j3) by (subst E; ereg 10%nat (10%bv : bv 5) H10).
assert (E15 : ew E 15 = Z_to_bv 64 i) by (subst E; ereg 15%nat (15%bv : bv 5) H15).
assert (E9 : ew E 9 = Z_to_bv 64 v) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (HS : st_ok_pi SEGS VAL E ss_wr (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_WR)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_wr. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, vreg9. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply (jw_vpres m HW). lia.
  - cbn. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jIDX, jVP, jSB. cbn [af_lo af_hi af_al2].
    rewrite E2, E10, E15, E9, E18, E27, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((spe - 128) mod 16 = 0) by (rewrite Zminus_mod, Zsp16; reflexivity).
    unfold SHADOW_OFF. repeat split; lia. }
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [mkSHE 9 0 20] E (mrestrict (w_H W) m)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) m E jsBx 9 v 20 v 0 20 (jw_vra m HW) UBx); [rewrite (U_atom E 9 v E9) by lia; reflexivity | lia | lia |].
  intros y Hy. change (Z.min 0 20) with 0 in Hy. change (Z.max 0 20) with 20 in Hy. apply js_v_app. lia. }
paj_run_tok RUN HS HJ SHOK jsBsp.
{ unfold ss_wr. cbn [ss_mem]. eapply awr_ok_cons_gen; [reflexivity | rewrite E9, unsigned_lit_small by lia; reflexivity | | apply awr_ok_nil].
  intros a Ha. apply js_awr_v. unfold vreg9 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }

assert (MKw : MK m (ms_mem ms) (fun a => v <= a < v + 20)).
{ apply (mk_frame m m (ms_mem ms) E (ss_mem ss_wr) _ (mk_refl m _) HFr HG).
  intros a (r & Hr0 & Hr). unfold ss_wr, vreg9 in Hr0. cbn [ss_mem In] in Hr0. destruct Hr0 as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9, unsigned_lit_small in Hr by lia. left. lia. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (OLD : forall q, (q < 512)%nat -> ew E1 q = ew E q) by (intros q Hq; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as RV. cbn [ms_mem restrict] in RV.
pose proof (field_of_region_any (segs := SEGS) E1 _ 9 v _ _ _ _ _ 0 8 (SOff 18 0) RV ltac:(rewrite OLD, E9 by lia; apply unsigned_lit_small; lia) ltac:(right; right; left; reflexivity) ltac:(lia)) as F0.
pose proof (field_of_region_any (segs := SEGS) E1 _ 9 v _ _ _ _ _ 8 8 _ RV ltac:(rewrite OLD, E9 by lia; apply unsigned_lit_small; lia) ltac:(right; left; reflexivity) ltac:(lia)) as F8.
pose proof (field_of_region_any (segs := SEGS) E1 _ 9 v _ _ _ _ _ 16 4 _ RV ltac:(rewrite OLD, E9 by lia; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(lia)) as F16.
pmkst HS.
apply SRr_ret. unfold SEGPOST. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mm _) ?d = _ /\ _ => exists rg, mm, d end.
split; [reflexivity|]. split; [exact HJ|].
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
cbn [ms_regs]. rewrite R2, R3, R4. rewrite ?OLD by lia. rewrite E2, E3, E4, H2.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [rewrite R10; rewrite ?OLD by lia; rewrite E10; reflexivity|].
split; [|split; [|split; [|exact MKw]]].
- replace v with (v + 0) by lia. replace (b + i) with ((bv_unsigned (sv_denot E1 (SOff 18 0))) mod 2 ^ (8 * Z.of_N 8)); [exact F0|].
  change (bv_unsigned (sv_denot E1 (SOff 18 0))) with (U E1 (SOff 18 0)). rewrite (U_atom E1 18 (b + i)) by (try (rewrite OLD by lia; exact E18); lia).
  apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia.
- replace (j3 - i) with ((bv_unsigned (sv_denot E1 (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 15 0) (SLit (-1)))))) mod 2 ^ (8 * Z.of_N 8)); [exact F8|].
  change (bv_unsigned (sv_denot E1 (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 15 0) (SLit (-1)))))) with (U E1 (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 15 0) (SLit (-1))))).
  rewrite (U_subf E1 10 15 j3 i) by (try (rewrite OLD by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia); assumption); clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia.
- replace 2 with ((bv_unsigned (sv_denot E1 (SLit 2))) mod 2 ^ (8 * Z.of_N 4)) at 2; [exact F16|]. reflexivity.
Qed.
End w.
End h.
End f.
End d.
