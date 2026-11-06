(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/JtokIs.v, with its module paths and module names changed; 898 of its 969 lines of code are new or changed and 558 lines of the source are left out. *)
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
Hypothesis seg_num0 : forall regs m md j0,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 10 = w64 j0 -> getr regs 15 = w64 i -> getr regs 9 = w64 v ->
  getr regs 18 = w64 (b + i) -> getr regs 27 = w64 SHADOW_OFF -> getr regs 19 = w64 n -> getr regs 20 = w64 b ->
  getr regs 16 = w64 (2 ^ 64 - 1 - b) -> j0 = (if jbyte BZ i =? 45 then i + 1 else i) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_N0)) m (seg_rom SEGS)) md) (SEGPOST m regs (jnum BZ i)).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac ereg q r H := rewrite (ew_EiR _ _ q r) by (cbv; first [lia | reflexivity]); exact H.
Ltac mk_tac HM HFr HG :=
  eapply (mk_frame _ _ _ _ _ _ HM HFr HG);
  let a := fresh "a" in let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in
  intros a (r & Hr0 & Hr);
  lazymatch type of Hr0 with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr0 end;
  cbn [In] in Hr0;
  repeat (destruct Hr0 as [<- | Hr0]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try (try clear Zbw; try clear Zbv; try clear Zvw; try clear Zv8; try clear Zsp16; try clear Zsp016; lia) |]);
  try (destruct Hr0).

Ltac hcU H :=
  rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in H;
  repeat match type of H with context [U ?Ex (SOff ?q ?k)] =>
    erewrite (U_offm Ex q k) in H by (first [ (rewrite ?ew_ewset_other by (try clear Zbw; try clear Zbv; try clear Zvw; try clear Zv8; try clear Zsp16; try clear Zsp016; lia); eassumption) | (try clear Zbw; try clear Zbv; try clear Zvw; try clear Zv8; try clear Zsp16; try clear Zsp016; lia) ]) end;
  rewrite ?U_litm in H.

Definition A_MT : Z := AF_both3_json_scalar + 0x368.
Definition lt_spill2 : YP09.region := YP09.mkRegion (Some 2%nat) 8 24 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition lt_vreg : YP09.region := YP09.mkRegion (Some 32%nat) 0 20 0 20 [].
Definition lt_mt_facts : facts := mkFacts [ (2%nat, jSP); (27%nat, jSB); (32%nat, jVP); (33%nat, jIDX) ] [] [].
Definition ss_lmt : sstate := mkSS A_MT sr_atoms [lt_spill2; lt_vreg] None lt_mt_facts.
Lemma lit_match : forall regs m md l,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 18 = w64 (b + i) -> getr regs 21 = w64 l -> getr regs 27 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 120) 8 v -> val_mem SEGS (mrestrict (w_H W) m) (spe - 112) 8 i ->
  0 <= l -> i + l <= n ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_MT)) m (seg_rom SEGS)) md) (SEGPOST m regs (Some (i + l, 3, i, l))).
Proof.
intros regs m md l HJ HW H2 H18 H21 H27 Vv Vi Hl0 Hl.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs (map (Z_to_bv 64) [v; i]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E21 : ew E 21 = Z_to_bv 64 l) by (subst E; ereg 21%nat (21%bv : bv 5) H21).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; exact (ew_EiX regs (map (Z_to_bv 64) [v; i]) 0 ltac:(cbv; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 i) by (subst E; exact (ew_EiX regs (map (Z_to_bv 64) [v; i]) 1 ltac:(cbv; lia))).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_lmt (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_MT)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lmt. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, lt_spill2. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (spe - 128) 8 8 (SOff 32 0) v);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        replace (spe - 128 + 8) with (spe - 120) by lia. exact Vv.
      * apply (chunk_ok_val SEGS E _ (spe - 128) 16 8 (SOff 33 0) i);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        replace (spe - 128 + 16) with (spe - 112) by lia. exact Vi.
    + unfold region_ok, lt_vreg. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (jw_vpres m HW). lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, lt_spill2, lt_vreg. cbn [r_base r_lo r_hi base_val].
    rewrite E2, E32, !unsigned_lit_small by lia. split; [split; [lia | exact I] | exact (conj I I)].
  - split; [|split; [exact I | exact I]].
    cbn [lt_mt_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jIDX, jVP, jSB. cbn [af_lo af_hi af_al2].
    rewrite E2, E27, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((spe - 128) mod 16 = 0) by (rewrite Zminus_mod, Zsp16; reflexivity).
    unfold SHADOW_OFF. repeat split; lia. }
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [mkSHE 32 0 20] E (mrestrict (w_H W) m)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) m E jsBx 32 v 20 v 0 20 (jw_vra m HW) UBx); [rewrite (U_atom E 32 v E32) by lia; reflexivity | lia | lia |].
  intros y Hy. change (Z.min 0 20) with 0 in Hy. change (Z.max 0 20) with 20 in Hy. apply js_v_app. lia. }
paj_run_tok RUN HS HJ SHOK jsBsp.
{ unfold ss_lmt. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | rewrite E32, unsigned_lit_small by lia; reflexivity | | apply awr_ok_nil].
  intros a Ha. apply js_awr_v. unfold lt_vreg in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
assert (MKw : MK m (ms_mem ms) (fun a => v <= a < v + 20)).
{ apply (mk_frame m m (ms_mem ms) E (ss_mem ss_lmt) _ (mk_refl m _) HFr HG).
  intros a (r & Hr0 & Hr). unfold ss_lmt, lt_spill2, lt_vreg in Hr0. cbn [ss_mem In] in Hr0. destruct Hr0 as [<-|[<-|[]]].
  - cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
  - cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E32, unsigned_lit_small in Hr by lia. left. lia. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (OLD : forall q, (q < 512)%nat -> ew E1 q = ew E q) by (intros q Hq; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 1 _ HS eq_refl) as RV. cbn [ms_mem restrict] in RV.
pose proof (field_of_region_any (segs := SEGS) E1 _ 32 v _ _ _ _ _ 0 8 (SOff 18 0) RV ltac:(rewrite OLD, E32 by lia; apply unsigned_lit_small; lia) ltac:(right; right; left; reflexivity) ltac:(lia)) as F0.
pose proof (field_of_region_any (segs := SEGS) E1 _ 32 v _ _ _ _ _ 8 8 _ RV ltac:(rewrite OLD, E32 by lia; apply unsigned_lit_small; lia) ltac:(right; left; reflexivity) ltac:(lia)) as F8.
pose proof (field_of_region_any (segs := SEGS) E1 _ 32 v _ _ _ _ _ 16 4 _ RV ltac:(rewrite OLD, E32 by lia; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(lia)) as F16.
pmkst HS.
apply SRr_ret. unfold SEGPOST. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mm _) ?d = _ /\ _ => exists rg, mm, d end.
split; [reflexivity|]. split; [exact HJ|].
cbn [ms_regs]. rewrite R2, R3, R4. rewrite ?OLD by lia. rewrite E2, E3, E4, H2.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ rewrite R10, E21, E33. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. unfold w64. rewrite !unsigned_lit_small by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
split; [|split; [|split; [|exact MKw]]].
- replace v with (v + 0) by lia. replace (b + i) with ((bv_unsigned (sv_denot E1 (SOff 18 0))) mod 2 ^ (8 * Z.of_N 8)); [exact F0|].
  change (bv_unsigned (sv_denot E1 (SOff 18 0))) with (U E1 (SOff 18 0)). rewrite (U_atom E1 18 (b + i)) by (try (rewrite OLD by lia; exact E18); lia).
  apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia.
- assert (X : bv_unsigned (sv_denot E1 (SOff 21 0)) mod 2 ^ (8 * Z.of_N 8) = l).
  { change (bv_unsigned (sv_denot E1 (SOff 21 0))) with (U E1 (SOff 21 0)). rewrite (U_atom E1 21 l) by (try (rewrite OLD by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia); exact E21); clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia).
    apply Z.mod_small. change (8 * Z.of_N 8) with 64. clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia. }
  rewrite X in F8. exact F8.
- assert (X : bv_unsigned (sv_denot E1 (SLit 3)) mod 2 ^ (8 * Z.of_N 4) = 3) by reflexivity.
  rewrite X in F16. exact F16.
Qed.

Lemma w64_off : forall z c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 z) + c) = Z_to_bv 64 (z + c).
Proof.
intros z c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma mk_vm8 : forall m m' a x, MK m m' (fun _ => False) -> spe - 128 <= a -> a + 8 <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) a 8 x -> val_mem SEGS (mrestrict (w_H W) m') a 8 x.
Proof.
intros m m' a x [HK _] Ha Ha2 V. pose proof js_nums as (N1 & N2 & N3 & N4 & N5).
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a 8 x); [|exact V].
intros q Hq. apply HK; [lia | lia | tauto].
Qed.
Lemma lt_bne : forall E0 k, (k < 3)%nat -> ew E0 25 = Z_to_bv 64 (-8 * Z.of_nat k) -> ew E0 24 = Z_to_bv 64 (-24) ->
  branch_taken BC_NE (sv_denot E0 (SOff 25 (-8))) (sv_denot E0 (SOff 24 0)) = negb (Nat.eqb k 2).
Proof.
intros E0 k Hk H25 H24. rewrite branch_ne_U, !U_SOff, H25, H24.
destruct k as [|[|[|k]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Lemma lt_j0 : forall c x, 0 <= c < 256 -> 0 <= x < 2 ^ 63 ->
  alu64 ALU_ADD (Z_to_bv 64 x) (alu64 ALU_SLTU (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 c) + -45)) (Z_to_bv 64 1)) =
  Z_to_bv 64 (if c =? 45 then x + 1 else x).
Proof.
intros c x Hc Hx. rewrite jt_seqz. rewrite (unsigned_lit_small c) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec c 45) as [->|Hn].
- change ((45 + -45) mod 2 ^ 64 =? 0) with true. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite !unsigned_lit_small by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
- replace ((c + -45) mod 2 ^ 64 =? 0) with false.
  + apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
    rewrite !unsigned_lit_small by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r. apply Z.mod_small. lia.
  + symmetry. apply Z.eqb_neq. intros X. pose proof (Z.div_mod (c + -45) (2 ^ 64) ltac:(lia)). lia.
Qed.
Ltac preg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac lreg R :=
  rewrite R; rewrite ?ew_ewset_other by lia;
  first [ reflexivity
        | match goal with H : ew _ _ = _ |- _ => rewrite H end;
          first [ reflexivity | unfold w64; rewrite ?w64_off; f_equal; lia ] ].

Definition A_NX : Z := AF_both3_json_scalar + 0x2c8.
Definition jSHX : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 27 0).
Definition lt_spill : YP09.region := YP09.mkRegion (Some 2%nat) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition lt_B : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition lt_nx_facts : facts := mkFacts [ (2%nat, jSP); (27%nat, jSB); (18%nat, mkAF 1 (2 ^ 47 - 2) 0); (35%nat, jBYTE) ] [] [].
Definition ss_lnx : sstate := mkSS A_NX (jR 8%bv jSHX sr_atoms) [lt_spill; lt_B] None lt_nx_facts.
Definition nx_extra : list word := map (Z_to_bv 64) [2 ^ 64 - 1 - b; v; i; jbyte BZ i].
Definition LITP (k : nat) : Prop := forall regs m md,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 25 = w64 (- 8 * Z.of_nat k) -> getr regs 24 = w64 (-24) ->
  getr regs 23 = w64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k) -> getr regs 9 = w64 (VAL (A_OBJ 20) + 8 * Z.of_nat k) ->
  getr regs 26 = w64 (n - i) -> getr regs 18 = w64 (b + i) -> getr regs 8 = w64 (SHADOW_OFF + (b + i) / 8) ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 19 = w64 n -> getr regs 20 = w64 b ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 128) 8 (2 ^ 64 - 1 - b) ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 120) 8 v -> val_mem SEGS (mrestrict (w_H W) m) (spe - 112) 8 i ->
  jbyte BZ i <> 34 -> jlit BZ i jlit_words = jlit BZ i (skipn k jlit_words) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_LIT)) m (seg_rom SEGS)) md)
    (SEGPOST m regs (match jlit BZ i (skipn k jlit_words) with Some t => Some t | None => jnum BZ i end)).
Lemma lit_next : forall k, (k < 3)%nat -> (forall k', k' = Datatypes.S k -> (k' < 3)%nat -> LITP k') ->
  forall regs m md,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 25 = w64 (- 8 * Z.of_nat k) -> getr regs 24 = w64 (-24) ->
  getr regs 23 = w64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k) -> getr regs 9 = w64 (VAL (A_OBJ 20) + 8 * Z.of_nat k) ->
  getr regs 26 = w64 (n - i) -> getr regs 18 = w64 (b + i) -> getr regs 8 = w64 (SHADOW_OFF + (b + i) / 8) ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 19 = w64 n -> getr regs 20 = w64 b ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 128) 8 (2 ^ 64 - 1 - b) ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 120) 8 v -> val_mem SEGS (mrestrict (w_H W) m) (spe - 112) 8 i ->
  jbyte BZ i <> 34 -> jlit BZ i jlit_words = jlit BZ i (skipn (Datatypes.S k) jlit_words) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_NX)) m (seg_rom SEGS)) md)
    (SEGPOST m regs (match jlit BZ i (skipn (Datatypes.S k) jlit_words) with Some t => Some t | None => jnum BZ i end)).
Proof.
intros k Hk IH regs m md HJ HW H2 H3 H4 H25 H24 H23 H9 H26 H18 H8 H27 H19 H20 V0 V8 V16 Hq Hlit.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (jbyte_range i) as RBi.
remember (Eimg (Ereg regs nx_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (SHADOW_OFF + (b + i) / 8)) by (subst E; ereg 8%nat (8%bv : bv 5) H8).
assert (E9 : ew E 9 = Z_to_bv 64 (VAL (A_OBJ 20) + 8 * Z.of_nat k)) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E23 : ew E 23 = Z_to_bv 64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k)) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E24 : ew E 24 = Z_to_bv 64 (-24)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E25 : ew E 25 = Z_to_bv 64 (- 8 * Z.of_nat k)) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E26 : ew E 26 = Z_to_bv 64 (n - i)) by (subst E; ereg 26%nat (26%bv : bv 5) H26).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E32 : ew E 32 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; exact (ew_EiX regs nx_extra 0 ltac:(cbv; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 v) by (subst E; exact (ew_EiX regs nx_extra 1 ltac:(cbv; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 i) by (subst E; exact (ew_EiX regs nx_extra 2 ltac:(cbv; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (jbyte BZ i)) by (subst E; exact (ew_EiX regs nx_extra 3 ltac:(cbv; lia))).
pose proof (jw_B m HW) as HGB.
destruct (garr8_at _ _ _ i HGB ltac:(unfold BZ; rewrite length_map; lia)) as [VBi _].
assert (D8 : sv_denot E jSHX = Z_to_bv 64 (SHADOW_OFF + (b + i) / 8)).
{ unfold jSHX. rewrite (denot_shx E 18 27 0 (b + i) SHADOW_OFF E18 E27) by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E ss_lnx (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_NX)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lnx. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite D8; exact H8].
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, lt_spill. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (spe - 128) 0 8 (SOff 32 0) (2 ^ 64 - 1 - b));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        rewrite Z.add_0_r. exact V0.
      * apply (chunk_ok_val SEGS E _ (spe - 128) 8 8 (SOff 33 0) v);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        replace (spe - 128 + 8) with (spe - 120) by lia. exact V8.
      * apply (chunk_ok_val SEGS E _ (spe - 128) 16 8 (SOff 34 0) i);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        replace (spe - 128 + 16) with (spe - 112) by lia. exact V16.
    + unfold region_ok, lt_B. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite E18, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (b + i) 0 1 (SOff 35 0) (jbyte BZ i));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
      rewrite Z.add_0_r. exact VBi.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, lt_spill, lt_B. cbn [r_base r_lo r_hi base_val].
    rewrite E2, E18, !unsigned_lit_small by lia. split; [split; [lia | exact I] | exact (conj I I)].
  - split; [|split; [exact I | exact I]].
    cbn [lt_nx_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jSB, jBYTE. cbn [af_lo af_hi af_al2].
    rewrite E2, E27, E18, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((spe - 128) mod 16 = 0) by (rewrite Zminus_mod, Zsp16; reflexivity).
    unfold SHADOW_OFF. repeat split; lia. }
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [] E (mrestrict (w_H W) m)) by constructor.
pose proof (mk_refl m (fun _ => False)) as HM0.
paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
assert (HM1 : MK m (ms_mem ms) (fun _ => False)) by (mk_tac HM0 HFr HG). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK jsBsp.
- rewrite (lt_bne _ k Hk ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(rewrite ?ew_ewset_other by lia; exact E24)) in Hc.
  assert (Hk2 : (Datatypes.S k < 3)%nat) by (destruct (Nat.eqb_spec k 2); [discriminate Hc | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_LIT. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end.
  preg_raw HS (8%bv : bv 5) R8.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (9%bv : bv 5) R9.
  prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (23%bv : bv 5) R23.
  prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
  pmkst HS.
  pose proof (IH (Datatypes.S k) eq_refl Hk2) as IHk. unfold LITP in IHk.
  eapply SRr_mono; [eapply (IHk _ _ _ HJ (jw_of_mk _ _ HW HM2)) | ].
  + lreg R2.
  + rewrite R3, E3. exact H3.
  + rewrite R4, E4. exact H4.
  + lreg R25.
  + lreg R24.
  + lreg R23.
  + lreg R9.
  + lreg R26.
  + lreg R18.
  + rewrite R8. rewrite (denot_shx _ 18 27 0 (b + i) SHADOW_OFF) by (try (rewrite ?ew_ewset_other by lia; assumption); unfold SHADOW_OFF; lia).
    rewrite Z.add_0_r. reflexivity.
  + lreg R27.
  + lreg R19.
  + lreg R20.
  + apply (mk_vm8 m _ _ _ HM2); [lia | lia | exact V0].
  + apply (mk_vm8 m _ _ _ HM2); [lia | lia | exact V8].
  + apply (mk_vm8 m _ _ _ HM2); [lia | lia | exact V16].
  + exact Hq.
  + exact Hlit.
  + intros W' c' _ HP. refine (seg_chain m regs _ _ _ HM2 _ _ _ W' c' HP).
    * rewrite R2, E2, H2. reflexivity.
    * rewrite R3, E3. reflexivity.
    * rewrite R4, E4. reflexivity.
- rewrite (lt_bne _ k Hk ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(rewrite ?ew_ewset_other by lia; exact E24)) in Hc.
  assert (Hk2 : k = 2%nat) by (destruct (Nat.eqb_spec k 2); [assumption | discriminate Hc]). subst k.
  paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_N0.
  { rewrite (U_atom E 18 (b + i) E18) by lia.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E jsBx (b + i) 1 b n (jw_Bra _ (jw_of_mk _ _ HW HM1)) UBx); lia. }
  { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (9%bv : bv 5) R9.
  prreg HS (10%bv : bv 5) R10. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16.
  prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (27%bv : bv 5) R27.
  pmkst HS.
  eapply SRr_mono; [eapply (seg_num0 _ _ _ (if jbyte BZ i =? 45 then i + 1 else i) HJ (jw_of_mk _ _ HW HM2)) | ].
  + lreg R2.
  + rewrite R10, E34, E35. apply lt_j0; [exact RBi | lia].
  + lreg R15.
  + lreg R9.
  + lreg R18.
  + lreg R27.
  + lreg R19.
  + lreg R20.
  + lreg R16.
  + reflexivity.
  + intros W' c' _ HP.
    replace (match jlit BZ i (skipn 3 jlit_words) with Some t => Some t | None => jnum BZ i end) with (jnum BZ i) by reflexivity.
    refine (seg_chain m regs _ _ _ HM2 _ _ _ W' c' HP).
    * rewrite R2, E2, H2. reflexivity.
    * rewrite R3, E3. reflexivity.
    * rewrite R4, E4. reflexivity.
Qed.

Lemma jlw_len : forall k, (k < 3)%nat -> (1 <= length (nth k jlit_words []) <= 5)%nat.
Proof. intros k Hk. destruct k as [|[|[|k]]]; cbn [nth jlit_words length]; lia. Qed.
Lemma nth_nil_z : forall q : nat, nth q (@nil Z) 0 = 0.
Proof. intros [|q]; reflexivity. Qed.
Lemma nth_skipn_z : forall p (l : list Z) q, nth q (skipn p l) 0 = nth (p + q) l 0.
Proof.
induction p as [|p IH]; intros l q; [reflexivity|].
destruct l as [|x l].
- cbn [skipn]. rewrite !nth_nil_z. reflexivity.
- cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma jpref_nth : forall (w r : list Z), jprefix w r = true <->
  ((length w <= length r)%nat /\ forall q, (q < length w)%nat -> nth q w 0 = nth q r 0).
Proof.
induction w as [|c w IH]; intros r; cbn [jprefix].
- split; [intros _; split; [cbn [length]; lia | intros q Hq; cbn [length] in Hq; lia] | intros _; reflexivity].
- destruct r as [|d r].
  + split; [discriminate | intros [Hl _]; cbn [length] in Hl; lia].
  + rewrite andb_true_iff, Z.eqb_eq, (IH r). split.
    * intros (Hc & Hl & Hn). split; [cbn [length]; lia|].
      intros [|q] Hq; [exact Hc | cbn [nth]; apply Hn; cbn [length] in Hq; lia].
    * intros (Hl & Hn). split; [exact (Hn 0%nat ltac:(cbn [length]; lia))|].
      split; [cbn [length] in Hl; lia|]. intros q Hq. exact (Hn (Datatypes.S q) ltac:(cbn [length]; lia)).
Qed.
Lemma jlit_unfold : forall kz, (kz < 3)%nat ->
  jlit BZ i (skipn kz jlit_words) =
  (if (Z.of_nat (length (nth kz jlit_words [])) <=? n - i) && jprefix (nth kz jlit_words []) (skipn (Z.to_nat i) BZ)
   then Some (i + Z.of_nat (length (nth kz jlit_words [])), 3, i, Z.of_nat (length (nth kz jlit_words [])))
   else jlit BZ i (skipn (Datatypes.S kz) jlit_words)).
Proof.
intros kz Hkz. rewrite <- jlen_BZ. destruct kz as [|[|[|kz]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.
Lemma hull_sub : forall rd a nn a' n', shadow_hull_vis rd a nn -> a <= a' -> 0 < n' -> a' + n' <= a + nn ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a nn a' n' H Ha Hn' Hle s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (a' + n' - 1) (a + nn - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + nn - 1) / 8) 8 ltac:(lia) ltac:(lia)).
clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia.
Qed.
Lemma jw_Bsh : forall m, JW m -> shadow_hull_vis (aview SEGS (w_H W) m) b n.
Proof.
intros m HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) _ (spe - TJSON_SCALAR_STK) spe);
  [exact (proj1 HW) | lia | lia | lia | lia | exact Zbsh].
Qed.
Lemma tstr_low : forall (m1 m2 : word -> option byte) a s,
  (forall x, 0 <= x < spe - TJSON_SCALAR_STK -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x) ->
  tjson_scalar_str W m1 a s -> tjson_scalar_str W m2 a s.
Proof.
intros m1 m2 a s HK (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlo : forall x, a <= x < a + Z.of_nat (length s) + 1 -> 0 <= x < kLowMemEnd)
  by (intros x Hx; exact (pa_segs_low x (H10 x Hx))).
assert (Hlow : a + Z.of_nat (length s) + 1 <= kLowMemEnd) by (pose proof (Hlo (a + Z.of_nat (length s)) ltac:(lia)); lia).
assert (HK2 : forall x, 0 <= x < 2 ^ 64 -> ~ (spe - TJSON_SCALAR_STK <= x < 2 ^ 64) -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x)
  by (intros x Hx Hn; apply HK; lia).
split; [exact H1|]. split.
{ intros q Hq. destruct (H2 q Hq) as [V R]. split; [|exact R].
  apply (val_mem_kept SEGS (w_H W) (w_H W) m1 m2 _ 1); [|exact V].
  intros r Hr. rewrite length_app in Hq. cbn [length] in Hq. apply HK. lia. }
split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [apply (range_addressable_kept_win (aview SEGS (w_H W) m1) _ (spe - TJSON_SCALAR_STK) (2 ^ 64)); [exact HK2 | lia | lia | lia | exact H7]|].
split; [apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) m1) _ (spe - TJSON_SCALAR_STK) (2 ^ 64)); [exact HK2 | lia | lia | lia | lia | exact H8]|].
split; [|exact H10].
intros x Hx. pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)). rewrite HK by lia. exact (H9 x Hx).
Qed.
Lemma tstr_JW : forall m m' a s, JW m -> JW m' -> tjson_scalar_str W m a s -> tjson_scalar_str W m' a s.
Proof.
intros m m' a s HW HW' Hs. apply (tstr_low m m'); [|exact Hs].
intros x Hx. rewrite (jw_low m' HW' x Hx), (jw_low m HW x Hx). reflexivity.
Qed.
Lemma tstr_fb : forall m a s, tjson_scalar_str W m a s ->
  first_byte SEGS W m a (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros m a s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
split; [lia|]. split.
- intros q Hq. exists (nth (Z.to_nat q) s 0). split.
  + replace (a + q) with (a + Z.of_nat (Z.to_nat q)) by lia.
    rewrite (jt_garr8_aview (w_H W) m a (s ++ [0]) (Z.to_nat q) H2 ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth1 by lia. reflexivity.
  + assert (HIn : In (nth (Z.to_nat q) s 0) s) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) H1 _ HIn) as HX. cbv beta in HX. lia.
- intros _.
  rewrite (jt_garr8_aview (w_H W) m a (s ++ [0]) (length s) H2 ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma tstr_src : forall m rr a s, tjson_scalar_str W m a s -> spZ rr = spe - 128 ->
  forall ln, 0 <= ln <= Z.of_nat (length s) + 1 -> src_ok SEGS W rr m a ln.
Proof.
intros m rr a s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) Hsp ln Hln x Hx.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_segs_low x (H10 x ltac:(lia))) as Hlow.
split.
- replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  rewrite (jt_garr8_aview (w_H W) m a (s ++ [0]) (Z.to_nat (x - a)) H2 ltac:(rewrite length_app; cbn [length]; lia)).
  discriminate.
- rewrite Hsp. unfold ESTACK. lia.
Qed.
Lemma B_src : forall m rr x ln, JW m -> spZ rr = spe - 128 -> b <= x -> x + ln <= b + n -> 0 <= ln ->
  src_ok SEGS W rr m x ln.
Proof.
intros m rr x ln HW Hsp Hx1 Hx2 Hln a Ha.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (jw_B m HW) as HGB. split.
- replace a with (b + Z.of_nat (Z.to_nat (a - b))) by lia.
  rewrite (jt_garr8_aview (w_H W) m b BZ (Z.to_nat (a - b)) HGB ltac:(unfold BZ; rewrite length_map; lia)). discriminate.
- rewrite Hsp. unfold ESTACK. destruct Zbw as [Hw|Hw]; lia.
Qed.
Lemma mbyte_of_aview0 : forall m a, aview SEGS (w_H W) m a = Some 0 ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some (Z_to_bv 8 0).
Proof.
intros m a H. unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) m) a) as [bb|] eqn:Hm; cbn [option_map] in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. rewrite H. reflexivity.
Qed.
Lemma lt_tabrange : forall m, JW m ->
  0 <= VAL (A_OBJ 20) /\ VAL (A_OBJ 20) + 24 <= kLowMemEnd /\ VAL (A_OBJ 20) mod 8 = 0.
Proof.
intros m HW. destruct (jw_litab m HW) as (t1 & t2 & t3 & L8 & Li & _).
pose proof (pa_segs_low _ (Li (VAL (A_OBJ 20)) ltac:(lia))).
pose proof (pa_segs_low _ (Li (VAL (A_OBJ 20) + 23) ltac:(lia))).
repeat split; lia.
Qed.
Lemma lt_shz : forall m kz, JW m -> 0 <= kz < 3 ->
  mbyte SEGS (mrestrict (w_H W) m) (SHADOW_OFF + VAL (A_OBJ 20) / 8 + kz) = Some (Z_to_bv 8 0).
Proof.
intros m kz HW Hkz. destruct (jw_litab m HW) as (t1 & t2 & t3 & L8 & Li & Lra & _).
destruct (lt_tabrange m HW) as (T0 & T24 & T8).
pose proof (Z.div_pos (VAL (A_OBJ 20)) 8 ltac:(lia) ltac:(lia)).
assert (HM : (VAL (A_OBJ 20) + 8 * kz) mod 8 = 0) by (rewrite Zplus_mod, T8; rewrite (Z.mul_comm 8 kz), Z_mod_mult; reflexivity).
pose proof (Z.div_mod (VAL (A_OBJ 20) + 8 * kz) 8 ltac:(lia)).
assert (HD : SHADOW_OFF + VAL (A_OBJ 20) / 8 + kz = SHADOW_OFF + (VAL (A_OBJ 20) + 8 * kz) / 8).
{ replace (VAL (A_OBJ 20) + 8 * kz) with (VAL (A_OBJ 20) + kz * 8) by lia. rewrite Z.div_add by lia. lia. }
destruct (Lra (VAL (A_OBJ 20) + 8 * kz) ltac:(lia)) as (sv & Hs & _).
pose proof (check_passes_whole (aview SEGS (w_H W) m) SHADOW_OFF (VAL (A_OBJ 20)) 24 (VAL (A_OBJ 20) + 8 * kz) 8 sv
  Lra ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hz. subst sv.
unfold shadow_of_addr in Hs. rewrite HD. apply mbyte_of_aview0. exact Hs.
Qed.
Lemma lt_tab_at : forall m k, JW m -> (k < 3)%nat -> exists t,
  val_mem SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 20) + 8 * Z.of_nat k) 8 t /\
  tjson_scalar_str W m t (nth k jlit_words []).
Proof.
intros m k HW Hk. destruct (jw_litab m HW) as (t1 & t2 & t3 & L8 & Li & Lra & V1 & V2 & V3 & S1 & S2 & S3).
destruct k as [|[|[|k]]].
- exists t1. rewrite Z.mul_0_r, Z.add_0_r. split; [exact V1 | exact S1].
- exists t2. replace (8 * Z.of_nat 1) with 8 by reflexivity. split; [exact V2 | exact S2].
- exists t3. replace (8 * Z.of_nat 2) with 16 by reflexivity. split; [exact V3 | exact S3].
- lia.
Qed.
Lemma lt_cmp_iff : forall m t s, JW m -> tjson_scalar_str W m t s -> Z.of_nat (length s) <= n - i ->
  ((forall q, 0 <= q < Z.of_nat (length s) -> aview SEGS (w_H W) m (b + i + q) = aview SEGS (w_H W) m (t + q))
   <-> jprefix s (skipn (Z.to_nat i) BZ) = true).
Proof.
intros m t s HW Hs Hlen. pose proof (jw_B m HW) as HGB.
pose proof Hs as (HF & HG & Ha0 & Hab & Hl32 & Hmr & Hra & Hhv & Hsl & Himg).
assert (HA : forall q, 0 <= q < Z.of_nat (length s) -> aview SEGS (w_H W) m (t + q) = Some (nth (Z.to_nat q) s 0)).
{ intros q Hq. replace (t + q) with (t + Z.of_nat (Z.to_nat q)) by lia.
  rewrite (jt_garr8_aview (w_H W) m t (s ++ [0]) (Z.to_nat q) HG ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite app_nth1 by lia. reflexivity. }
assert (HB : forall q, 0 <= q < Z.of_nat (length s) -> aview SEGS (w_H W) m (b + i + q) = Some (nth (Z.to_nat (i + q)) BZ 0)).
{ intros q Hq. replace (b + i + q) with (b + Z.of_nat (Z.to_nat (i + q))) by lia.
  rewrite (jt_garr8_aview (w_H W) m b BZ (Z.to_nat (i + q)) HGB ltac:(unfold BZ; rewrite length_map; lia)). reflexivity. }
assert (KEY : forall q, 0 <= q < Z.of_nat (length s) ->
  (aview SEGS (w_H W) m (b + i + q) = aview SEGS (w_H W) m (t + q) <-> nth (Z.to_nat q) s 0 = nth (Z.to_nat (i + q)) BZ 0)).
{ intros q Hq. rewrite (HA q Hq), (HB q Hq).
  split; [intros X; injection X as X; lia | intros X; rewrite X; reflexivity]. }
rewrite jpref_nth. split.
- intros Hall. split.
  + rewrite length_skipn. unfold BZ. rewrite length_map. lia.
  + intros q Hq.
    assert (HK : nth (Z.to_nat (Z.of_nat q)) s 0 = nth (Z.to_nat (i + Z.of_nat q)) BZ 0)
      by (apply (proj1 (KEY (Z.of_nat q) ltac:(lia))); apply Hall; lia).
    rewrite Nat2Z.id in HK. rewrite HK, nth_skipn_z. f_equal. lia.
- intros (Hl & Hn) q Hq. apply (proj2 (KEY q Hq)).
  specialize (Hn (Z.to_nat q) ltac:(lia)). rewrite nth_skipn_z in Hn.
  replace (Z.to_nat i + Z.to_nat q)%nat with (Z.to_nat (i + q)) in Hn by lia. exact Hn.
Qed.

Lemma lt_o16 : (spe - 128 - sp0) mod 16 = 0.
Proof.
pose proof (Z.div_mod spe 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite Zsp16 in D1. rewrite Zsp016 in D2.
replace (spe - 128 - sp0) with ((spe / 16 - 8 - sp0 / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Definition lt_shtab : YP09.region := YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CZero 1)].
Definition lt_tabr : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition lt_lit_facts : facts := mkFacts [ (2%nat, jSP); (27%nat, jSB) ] [] [].
Definition ss_lit : sstate := mkSS A_LIT sr_atoms [lt_shtab; lt_tabr] None lt_lit_facts.
Definition lit_extra (t : Z) : list word := [Z_to_bv 64 t].
Lemma lit_step : forall k, (k < 3)%nat -> (forall k', k' = Datatypes.S k -> (k' < 3)%nat -> LITP k') -> LITP k.
Proof.
intros k Hk IH regs m md HJ HW H2 H3 H4 H25 H24 H23 H9 H26 H18 H8 H27 H19 H20 V0 V8 V16 Hq Hlit.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (jlw_len k Hk) as HLS.
destruct (lt_tabrange m HW) as (T0 & T24 & T8).
pose proof (Z.div_pos (VAL (A_OBJ 20)) 8 ltac:(lia) ltac:(lia)) as TD.
pose proof (Z.div_mod (VAL (A_OBJ 20)) 8 ltac:(lia)) as TDM.
destruct (lt_tab_at m k HW Hk) as (t & Vt & Hstr).
remember (nth k jlit_words []) as sw eqn:Hsw.
pose proof Hstr as (SF & SG & St0 & Stb & St32 & Stm & Stra & Sthv & Stsl & Stimg).
pose proof (pa_segs_low t (Stimg t ltac:(lia))) as Htlow0.
pose proof (pa_segs_low (t + Z.of_nat (length sw)) (Stimg (t + Z.of_nat (length sw)) ltac:(lia))) as Htlow.
remember (Eimg (Ereg regs (lit_extra t))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E8 : ew E 8 = Z_to_bv 64 (SHADOW_OFF + (b + i) / 8)) by (subst E; ereg 8%nat (8%bv : bv 5) H8).
assert (E9 : ew E 9 = Z_to_bv 64 (VAL (A_OBJ 20) + 8 * Z.of_nat k)) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E23 : ew E 23 = Z_to_bv 64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k)) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E24 : ew E 24 = Z_to_bv 64 (-24)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E25 : ew E 25 = Z_to_bv 64 (- 8 * Z.of_nat k)) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E26 : ew E 26 = Z_to_bv 64 (n - i)) by (subst E; ereg 26%nat (26%bv : bv 5) H26).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E32 : ew E 32 = Z_to_bv 64 t) by (subst E; exact (ew_EiX regs (lit_extra t) 0 ltac:(cbv; lia))).
assert (HS : st_ok_pi SEGS VAL E ss_lit (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_LIT)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lit. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, lt_shtab. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite E23, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. unfold YP09.chunk_ok. cbn [YP09.c_off YP09.c_val c_len cv_len cbyte].
      intros o Ho. exists (Z_to_bv 8 0). split; [reflexivity|].
      replace (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k + 0 + o) with (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k) by lia.
      exact (lt_shz m (Z.of_nat k) HW ltac:(lia)).
    + unfold region_ok, lt_tabr. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 20) + 8 * Z.of_nat k) 0 8 (SOff 32 0) t);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      rewrite Z.add_0_r. exact Vt.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, lt_shtab, lt_tabr. cbn [r_base r_lo r_hi base_val].
    rewrite E23, E9, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    split; [split; [unfold SHADOW_OFF; lia | exact I] | exact (conj I I)].
  - split; [|split; [exact I | exact I]].
    cbn [lt_lit_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jSB. cbn [af_lo af_hi af_al2].
    rewrite E2, E27, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((spe - 128) mod 16 = 0) by (rewrite Zminus_mod, Zsp16; reflexivity).
    unfold SHADOW_OFF. repeat split; lia. }
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [] E (mrestrict (w_H W) m)) by constructor.
pose proof (mk_refl m (fun _ => False)) as HM0.
paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
assert (HM1 : MK m (ms_mem ms) (fun _ => False)) by (mk_tac HM0 HFr HG). clear HF HFr HG.
pose proof (jw_of_mk _ _ HW HM1) as HW1.
pose proof (tstr_JW m (ms_mem ms) t sw HW HW1 Hstr) as Hstr1.
pose proof Hstr1 as (SF1 & SG1 & St01 & Stb1 & St321 & Stm1 & Stra1 & Sthv1 & Stsl1 & Stimg1).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
prreg HS (4%bv : bv 5) R4. prreg HS (10%bv : bv 5) R10.
assert (HSP : spZ (ms_regs ms) = sp0 + (spe - 128 - sp0)) by (unfold spZ; rewrite R2, E2, unsigned_lit_small by lia; lia).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_strlen_at (fx := fx) B LAWS pa_segs_low MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen)
    (ASTRLEN fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc _ kk t (Z.of_nat (length sw))
    (spe - 128 - sp0) (Z_to_bv 64 (BASE + 12456)) HJ).
  - rewrite R10, E32. reflexivity.
  - exact St0.
  - lia.
  - lia.
  - lia.
  - exact HSP.
  - exact lt_o16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, E3. exact H3.
  - rewrite R4, E4. exact H4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact (tstr_fb (ms_mem ms) t sw Hstr1).
  - exact (tstr_src (ms_mem ms) (ms_regs ms) t sw Hstr1 ltac:(rewrite HSP; lia) (Z.of_nat (length sw) + 1) ltac:(lia)).
  - exact Stm1.
  - exact Stra1.
  - exact Sthv1.
  - exact Stsl1.
  - exact (jw_cv _ HW1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen2 & Hfr2 & Hpres2).
assert (HM2 : MK m mem2 (fun _ => False)).
{ eapply (mk_call m (ms_mem ms) mem2 _ _ _ HM1); [exact Hfr2 | exact Hpres2 | unfold ESTACK; lia | lia]. }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [apply Forall_nil | specialize (HS2 HQ); clear HQ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall q, (q < 36)%nat -> ew E5 q = ew E q) by (intros qq Hqq; rewrite HE5; apply ew_havoc_old; exact Hqq).
assert (G40r : ew E5 40 = getr regs2 10) by (rewrite HE5; reflexivity).
assert (G40 : ew E5 40 = Z_to_bv 64 (Z.of_nat (length sw))) by (rewrite G40r, Hlen2; reflexivity).
clear HE5.
assert (G2 : ew E5 2 = Z_to_bv 64 (spe - 128)) by (rewrite OLD by lia; exact E2).
assert (G3 : ew E5 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
assert (G4 : ew E5 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
assert (G8 : ew E5 8 = Z_to_bv 64 (SHADOW_OFF + (b + i) / 8)) by (rewrite OLD by lia; exact E8).
assert (G9 : ew E5 9 = Z_to_bv 64 (VAL (A_OBJ 20) + 8 * Z.of_nat k)) by (rewrite OLD by lia; exact E9).
assert (G18 : ew E5 18 = Z_to_bv 64 (b + i)) by (rewrite OLD by lia; exact E18).
assert (G19 : ew E5 19 = Z_to_bv 64 n) by (rewrite OLD by lia; exact E19).
assert (G20 : ew E5 20 = Z_to_bv 64 b) by (rewrite OLD by lia; exact E20).
assert (G23 : ew E5 23 = Z_to_bv 64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k)) by (rewrite OLD by lia; exact E23).
assert (G24 : ew E5 24 = Z_to_bv 64 (-24)) by (rewrite OLD by lia; exact E24).
assert (G25 : ew E5 25 = Z_to_bv 64 (- 8 * Z.of_nat k)) by (rewrite OLD by lia; exact E25).
assert (G26 : ew E5 26 = Z_to_bv 64 (n - i)) by (rewrite OLD by lia; exact E26).
assert (G27 : ew E5 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD by lia; exact E27).
assert (G32 : ew E5 32 = Z_to_bv 64 t) by (rewrite OLD by lia; exact E32).
assert (SHOK5 : sh_ok SEGS jsBx [] E5 (mrestrict (w_H W) mem2)) by constructor.
pose proof (jw_of_mk _ _ HW HM2) as HW2.
psrr_branch_tok RUN BR HS SHOK5 jsBsp.
- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply Z.ltb_lt in Hc.
  assert (Hlit2 : jlit BZ i jlit_words = jlit BZ i (skipn (Datatypes.S k) jlit_words)).
  { rewrite Hlit, (jlit_unfold k Hk), <- Hsw.
    replace (Z.of_nat (length sw) <=? n - i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  rewrite <- Hlit, Hlit2.
  paj_run_to_tok RUNTO HS HJ2 SHOK5 jsBsp A_NX. { awr_ok_tac. }
  assert (HM3 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
  repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
  prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
  prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
  prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
  pmkst HS.
  eapply SRr_mono; [eapply (lit_next k Hk IH _ _ _ HJ2 (jw_of_mk _ _ HW HM3)) | ].
  + lreg R2.
  + rewrite R3, G3. exact H3.
  + rewrite R4, G4. exact H4.
  + lreg R25.
  + lreg R24.
  + lreg R23.
  + lreg R9.
  + lreg R26.
  + lreg R18.
  + lreg R8.
  + lreg R27.
  + lreg R19.
  + lreg R20.
  + apply (mk_vm8 m _ _ _ HM3); [lia | lia | exact V0].
  + apply (mk_vm8 m _ _ _ HM3); [lia | lia | exact V8].
  + apply (mk_vm8 m _ _ _ HM3); [lia | lia | exact V16].
  + exact Hq.
  + exact Hlit2.
  + intros W' c' _ HP. refine (seg_chain m regs _ _ _ HM3 _ _ _ W' c' HP).
    * rewrite R2, G2, H2. reflexivity.
    * rewrite R3, G3. reflexivity.
    * rewrite R4, G4. reflexivity.
- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply Z.ltb_ge in Hc. rename Hc into Hle.
  paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
  assert (HM3 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
  pose proof (jw_of_mk _ _ HW HM3) as HW3.
  pose proof (tstr_JW m (ms_mem ms0) t sw HW HW3 Hstr) as Hstr3.
  pose proof Hstr3 as (SF3 & SG3 & St03 & Stb3 & St323 & Stm3 & Stra3 & Sthv3 & Stsl3 & Stimg3).
  repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) Ra2.
  assert (HSP3 : spZ (ms_regs ms0) = sp0 + (spe - 128 - sp0)).
  { unfold spZ. prreg HS (2%bv : bv 5) RX. rewrite RX, G2, unsigned_lit_small by lia. lia. }
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fx) W (ms_regs ms0)
      (ms_mem ms0) STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc _ kk (b + i) t (Z.of_nat (length sw))
      (spe - 128 - sp0) (Z_to_bv 64 (BASE + 12480)) HJ2).
    - rewrite R10, G18. reflexivity.
    - rewrite R11, G32. reflexivity.
    - rewrite Ra2, G40. reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HSP3.
    - exact lt_o16.
    - lia.
    - unfold ESTACK. lia.
    - rewrite R3, G3. exact H3.
    - rewrite R4, G4. exact H4.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - exact (B_src (ms_mem ms0) (ms_regs ms0) (b + i) (Z.of_nat (length sw)) HW3 ltac:(rewrite HSP3; lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (tstr_src (ms_mem ms0) (ms_regs ms0) t sw Hstr3 ltac:(rewrite HSP3; lia) (Z.of_nat (length sw)) ltac:(lia)).
    - intros a Ha. unfold ESTACK. destruct Zbw as [Hw|Hw]; lia.
    - intros a Ha. pose proof (pa_segs_low a (Stimg3 a ltac:(lia))). unfold ESTACK. lia.
    - unfold amem_range in Zbm |- *. lia.
    - unfold amem_range in Stm3 |- *. lia.
    - apply (range_addressable_sub _ _ b n); [exact (jw_Bra _ HW3) | lia | lia].
    - intros _. apply (hull_sub _ b n); [exact (jw_Bsh _ HW3) | lia | lia | lia].
    - apply (range_addressable_sub _ _ t (Z.of_nat (length sw) + 1)); [exact Stra3 | lia | lia].
    - intros _. apply (hull_sub _ t (Z.of_nat (length sw) + 1)); [exact Sthv3 | lia | lia | lia]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & vb & -> & HJ3 & HP3 & Hvb & Hcmp & Hfr3 & Hpres3).
  assert (HM4 : MK m mem3 (fun _ => False)).
  { eapply (mk_call m (ms_mem ms0) mem3 _ _ _ HM3); [exact Hfr3 | exact Hpres3 | unfold ESTACK; lia | lia]. }
  pose proof (lt_cmp_iff (ms_mem ms0) t sw HW3 Hstr3 ltac:(lia)) as HPR.
  jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W) mem3) HP3 (@nil nat) HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q); [apply Forall_nil | specialize (HS2 HQ); clear HQ] end.
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E5 52 (map (getr regs3) CLOB)) as E7 eqn:HE7 in HS.
  assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc; [exact HEI5 | cbv; lia]).
  assert (OLD7 : forall q, (q < 52)%nat -> ew E7 q = ew E5 q) by (intros qq Hqq; rewrite HE7; apply ew_havoc_old; exact Hqq).
  assert (K56r : ew E7 56 = getr regs3 10) by (rewrite HE7; reflexivity).
  assert (K56 : ew E7 56 = Z_to_bv 64 (bv_unsigned vb)) by (rewrite K56r, Hvb; symmetry; apply Z_to_bv_bv_unsigned).
  clear HE7.
  assert (K2 : ew E7 2 = Z_to_bv 64 (spe - 128)) by (rewrite OLD7 by lia; exact G2).
  assert (K3 : ew E7 3 = getr regs 3) by (rewrite OLD7 by lia; exact G3).
  assert (K4 : ew E7 4 = getr regs 4) by (rewrite OLD7 by lia; exact G4).
  assert (K8 : ew E7 8 = Z_to_bv 64 (SHADOW_OFF + (b + i) / 8)) by (rewrite OLD7 by lia; exact G8).
  assert (K9 : ew E7 9 = Z_to_bv 64 (VAL (A_OBJ 20) + 8 * Z.of_nat k)) by (rewrite OLD7 by lia; exact G9).
  assert (K18 : ew E7 18 = Z_to_bv 64 (b + i)) by (rewrite OLD7 by lia; exact G18).
  assert (K19 : ew E7 19 = Z_to_bv 64 n) by (rewrite OLD7 by lia; exact G19).
  assert (K20 : ew E7 20 = Z_to_bv 64 b) by (rewrite OLD7 by lia; exact G20).
  assert (K23 : ew E7 23 = Z_to_bv 64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k)) by (rewrite OLD7 by lia; exact G23).
  assert (K24 : ew E7 24 = Z_to_bv 64 (-24)) by (rewrite OLD7 by lia; exact G24).
  assert (K25 : ew E7 25 = Z_to_bv 64 (- 8 * Z.of_nat k)) by (rewrite OLD7 by lia; exact G25).
  assert (K26 : ew E7 26 = Z_to_bv 64 (n - i)) by (rewrite OLD7 by lia; exact G26).
  assert (K27 : ew E7 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD7 by lia; exact G27).
  assert (K40 : ew E7 40 = Z_to_bv 64 (Z.of_nat (length sw))) by (rewrite OLD7 by lia; exact G40).
  assert (SHOK7 : sh_ok SEGS jsBx [] E7 (mrestrict (w_H W) mem3)) by constructor.
  pose proof (jw_of_mk _ _ HW HM4) as HW4.
  pose proof (bv_unsigned_in_range 64 vb) as RVB. change (bv_modulus 64) with (2 ^ 64) in RVB.
  psrr_branch_tok RUN BR HS SHOK7 jsBsp.
  + rewrite branch_eq_U, (U_atom E7 56 (bv_unsigned vb) K56 ltac:(lia)), U_litm in Hc.
    apply Z.eqb_eq in Hc. rewrite Z.mod_small in Hc by lia.
    assert (HV0 : vb = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
    assert (HPT : jprefix sw (skipn (Z.to_nat i) BZ) = true) by (apply HPR, Hcmp, HV0).
    rewrite (jlit_unfold k Hk), <- Hsw.
    replace (Z.of_nat (length sw) <=? n - i) with true by (symmetry; apply Z.leb_le; lia).
    rewrite HPT. cbn [andb].
    paj_run_to_tok RUNTO HS HJ3 SHOK7 jsBsp A_MT. { awr_ok_tac. }
    assert (HM5 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM4 HFr HG). clear HF HFr HG.
    repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (18%bv : bv 5) R18. prreg HS (21%bv : bv 5) Rs5. prreg HS (27%bv : bv 5) R27.
    pmkst HS.
    eapply SRr_mono; [eapply (lit_match _ _ _ (Z.of_nat (length sw)) HJ3 (jw_of_mk _ _ HW HM5)) | ].
    * lreg R2.
    * lreg R18.
    * lreg Rs5.
    * lreg R27.
    * apply (mk_vm8 m _ _ _ HM5); [lia | lia | exact V8].
    * apply (mk_vm8 m _ _ _ HM5); [lia | lia | exact V16].
    * lia.
    * lia.
    * intros W' c' _ HP. refine (seg_chain m regs _ _ _ HM5 _ _ _ W' c' HP).
      -- rewrite R2, K2, H2. reflexivity.
      -- rewrite R3, K3. reflexivity.
      -- rewrite R4, K4. reflexivity.
  + rewrite branch_eq_U, (U_atom E7 56 (bv_unsigned vb) K56 ltac:(lia)), U_litm in Hc.
    rewrite Z.mod_small in Hc by lia.
    assert (HVN : vb <> w64 0).
    { intros X. rewrite X in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. rewrite Z.eqb_refl in Hc. discriminate Hc. }
    assert (HPF : jprefix sw (skipn (Z.to_nat i) BZ) = false).
    { apply Bool.not_true_iff_false. intros EP. apply HVN. apply Hcmp, HPR. exact EP. }
    assert (Hlit2 : jlit BZ i jlit_words = jlit BZ i (skipn (Datatypes.S k) jlit_words)).
    { rewrite Hlit, (jlit_unfold k Hk), <- Hsw, HPF. rewrite andb_false_r. reflexivity. }
    rewrite <- Hlit, Hlit2.
    paj_run_to_tok RUNTO HS HJ3 SHOK7 jsBsp A_NX. { awr_ok_tac. }
    assert (HM5 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM4 HFr HG). clear HF HFr HG.
    repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
    prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
    prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
    prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
    pmkst HS.
    eapply SRr_mono; [eapply (lit_next k Hk IH _ _ _ HJ3 (jw_of_mk _ _ HW HM5)) | ].
    * lreg R2.
    * rewrite R3, K3. exact H3.
    * rewrite R4, K4. exact H4.
    * lreg R25.
    * lreg R24.
    * lreg R23.
    * lreg R9.
    * lreg R26.
    * lreg R18.
    * lreg R8.
    * lreg R27.
    * lreg R19.
    * lreg R20.
    * apply (mk_vm8 m _ _ _ HM5); [lia | lia | exact V0].
    * apply (mk_vm8 m _ _ _ HM5); [lia | lia | exact V8].
    * apply (mk_vm8 m _ _ _ HM5); [lia | lia | exact V16].
    * exact Hq.
    * exact Hlit2.
    * intros W' c' _ HP. refine (seg_chain m regs _ _ _ HM5 _ _ _ W' c' HP).
      -- rewrite R2, K2, H2. reflexivity.
      -- rewrite R3, K3. reflexivity.
      -- rewrite R4, K4. reflexivity.
Qed.

Lemma lit_all : forall d k, (k < 3)%nat -> (3 <= k + d)%nat -> LITP k.
Proof.
induction d as [|d IHd]; intros k Hk Hd; [lia|].
apply (lit_step k Hk). intros k' -> Hk'. apply (IHd (Datatypes.S k) Hk'). lia.
Qed.

Lemma seg_lit : forall (k : nat) regs m md, (k < 3)%nat ->
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 25 = w64 (- 8 * Z.of_nat k) -> getr regs 24 = w64 (-24) ->
  getr regs 23 = w64 (SHADOW_OFF + VAL (A_OBJ 20) / 8 + Z.of_nat k) -> getr regs 9 = w64 (VAL (A_OBJ 20) + 8 * Z.of_nat k) ->
  getr regs 26 = w64 (n - i) -> getr regs 18 = w64 (b + i) -> getr regs 8 = w64 (SHADOW_OFF + (b + i) / 8) ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 19 = w64 n -> getr regs 20 = w64 b ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 128) 8 (2 ^ 64 - 1 - b) ->
  val_mem SEGS (mrestrict (w_H W) m) (spe - 120) 8 v -> val_mem SEGS (mrestrict (w_H W) m) (spe - 112) 8 i ->
  jbyte BZ i <> 34 -> jlit BZ i jlit_words = jlit BZ i (skipn k jlit_words) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_LIT)) m (seg_rom SEGS)) md)
    (SEGPOST m regs (match jlit BZ i (skipn k jlit_words) with Some t => Some t | None => jnum BZ i end)).
Proof.
intros k regs m md Hk. exact (lit_all 3 k Hk ltac:(lia) regs m md).
Qed.
End w.
End h.
End f.
End d.
