(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/JtokIs.v, with its module paths and module names changed; 407 of its 454 lines of code are new or changed and 582 lines of the source are left out. *)
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
Let BR := paj_branch (PI := PI).
Ltac ereg q r H := rewrite (ew_EiR _ _ q r) by (cbv; first [lia | reflexivity]); exact H.
Ltac jx_facts E HE regs j :=
  assert (E32 : ew E 32 = Z_to_bv 64 (b + j)) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 0 ltac:(cbv; lia)));
  assert (E33 : ew E 33 = Z_to_bv 64 (jbyte BZ j)) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 1 ltac:(cbv; lia)));
  assert (E34 : ew E 34 = Z_to_bv 64 (jbyte BZ (j + 1))) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 2 ltac:(cbv; lia)));
  assert (E35 : ew E 35 = Z_to_bv 64 (jbyte BZ (j + 2))) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 3 ltac:(cbv; lia)));
  assert (E36 : ew E 36 = Z_to_bv 64 (jbyte BZ (j + 3))) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 4 ltac:(cbv; lia)));
  assert (E37 : ew E 37 = Z_to_bv 64 (jbyte BZ (j + 4))) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 5 ltac:(cbv; lia)));
  assert (E38 : ew E 38 = Z_to_bv 64 (jbyte BZ (j + 5))) by (rewrite HE; exact (ew_EiX regs (jx_extra j) 6 ltac:(cbv; lia))).
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

Ltac prregs HS :=
  repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end;
  let R2 := fresh "R2" in prreg HS (2%bv : bv 5) R2; let R3 := fresh "R3" in prreg HS (3%bv : bv 5) R3; let R4 := fresh "R4" in prreg HS (4%bv : bv 5) R4; let R9 := fresh "R9" in prreg HS (9%bv : bv 5) R9; let R10 := fresh "R10" in prreg HS (10%bv : bv 5) R10; let R11 := fresh "R11" in prreg HS (11%bv : bv 5) R11; let R12 := fresh "R12" in prreg HS (12%bv : bv 5) R12; let R15 := fresh "R15" in prreg HS (15%bv : bv 5) R15; let R16 := fresh "R16" in prreg HS (16%bv : bv 5) R16; let R18 := fresh "R18" in prreg HS (18%bv : bv 5) R18; let R19 := fresh "R19" in prreg HS (19%bv : bv 5) R19; let R20 := fresh "R20" in prreg HS (20%bv : bv 5) R20; let R27 := fresh "R27" in prreg HS (27%bv : bv 5) R27.
Ltac hcU2 H := rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in H; rewrite ?U_SAlu in H; cbn [zalu_raw] in H; hcU H.
Ltac seg_exit0 HS HJ HM :=
  prregs HS; pmkst HS; apply SRr_ret; unfold SEGPOST; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mm _) ?d = _ /\ _ => exists rg, mm, d end;
  split; [reflexivity|]; split; [exact HJ|];
  cbn [ms_regs];
  lazymatch goal with
  | R2 : getr _ 2 = _, R3 : getr _ 3 = _, R4 : getr _ 4 = _, R10 : getr _ 10 = _,
    E2 : ew _ 2 = _, E3 : ew _ 3 = _, E4 : ew _ 4 = _, H2 : getr _ 2 = w64 _ |- _ =>
    split; [rewrite R2, E2, H2; reflexivity|]; split; [rewrite R3, E3; reflexivity|]; split; [rewrite R4, E4; reflexivity|];
    split; [rewrite R10; reflexivity | exact HM]
  end.
Ltac spec_all H := try (match type of H with ?P -> _ => let HP := fresh in assert (HP : P); [|specialize (H HP); clear HP; spec_all H] end).

Ltac addb HS c j :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) =>
    let HS2 := fresh "HS" in
    pose proof (add_breg Ex ss msx c j HS) as HS2; spec_all HS2
  end.

Ltac oblB HWm c j := cbn [ms_mem]; apply (obl_B _ _ c j HWm); [rewrite ?ew_ewset_other by lia; assumption | rewrite ?ew_ewset_other by lia; assumption | lia | lia | lia].

Definition hx_regs : list sv :=
  jR 8%bv (SOff 25 (-2)) (jR 26%bv (SLit 34) (jR 13%bv (SLit 32) (jR 14%bv (SLit 92) (jR 21%bv (SOff (A_OBJ 19) 0)
    (jR 15%bv (SLit 18446744073709551605) sr_atoms))))).
Definition ss_hx (pc : Z) : sstate := mkSS pc hx_regs [] None sl_facts.

Lemma hx_entry : forall pc regs m j, JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 20 = w64 b -> getr regs 25 = w64 (j + 1) -> getr regs 8 = w64 (j - 1) ->
  getr regs 26 = w64 34 -> getr regs 13 = w64 32 -> getr regs 14 = w64 92 -> getr regs 21 = w64 (VAL (A_OBJ 19)) ->
  getr regs 19 = w64 n -> getr regs 24 = w64 (2 ^ 64 - 1 - b) -> getr regs 9 = w64 i -> getr regs 23 = w64 v ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 (b + i) -> getr regs 15 = w64 18446744073709551605 ->
  i + 1 <= j -> j + 5 < n ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (jx_extra (j + 1)))) (ss_hx pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros pc regs m j HW H2 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15 Hj Hj5.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs (jx_extra (j + 1)))) as E eqn:HE.
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E25 : ew E 25 = Z_to_bv 64 (j + 1)) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E9 : ew E 9 = Z_to_bv 64 i) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E23 : ew E 23 = Z_to_bv 64 v) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
jx_facts E HE regs (j + 1).
pose proof (jbyte_range (j + 1)). pose proof (jbyte_range (j + 1 + 1)). pose proof (jbyte_range (j + 1 + 2)).
pose proof (jbyte_range (j + 1 + 3)). pose proof (jbyte_range (j + 1 + 4)). pose proof (jbyte_range (j + 1 + 5)).
rewrite restrict_mkst_fx. unfold ss_hx. apply pa_entry_st_ok_full.
- unfold hx_regs, jR. rewrite HE.
  repeat (apply regs_ok_pin; [| intros X; discriminate X | ]).
  + apply regs_ok_Eimg_Ereg.
  + rewrite H15. reflexivity.
  + rewrite H21. cbn [sv_denot]. rewrite (Eimg_img _ (A_OBJ 19)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite H14. reflexivity.
  + rewrite H13. reflexivity.
  + rewrite H26. reflexivity.
  + rewrite H8. rewrite <- HE. rewrite denot_lit_U, (U_atom_off E 25 (j + 1) (-2) E25) by lia. f_equal. lia.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- split; [|split; [exact I|]].
  + cbn [sl_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jIDX, jVP, jSB, jPTR, jNOTP, jBYTE. cbn [af_lo af_hi af_al2].
    rewrite E2, E20, E25, E19, E24, E9, E23, E27, E18, E32, E33, E34, E35, E36, E37, E38.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((spe - 128) mod 16 = 0) by (rewrite Zminus_mod, Zsp16; reflexivity).
    unfold SHADOW_OFF. repeat split; lia.
  + cbn [sl_facts f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 20 b E20), (U_atom E 25 (j + 1) E25), (U_atom E 32 (b + (j + 1)) E32) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Definition A_HX3 : Z := AF_both3_json_scalar + 0x19c.
Definition A_HX4 : Z := AF_both3_json_scalar + 0x1d4.
Ltac prregs_sl HS :=
  repeat match goal with H : getr (ms_regs _) _ = _ |- _ => clear H end;
  let R2 := fresh "R2" in prreg HS (2%bv : bv 5) R2; let R3 := fresh "R3" in prreg HS (3%bv : bv 5) R3;
  let R4 := fresh "R4" in prreg HS (4%bv : bv 5) R4; let R8 := fresh "R8" in prreg HS (8%bv : bv 5) R8;
  let R9 := fresh "R9" in prreg HS (9%bv : bv 5) R9; let R10 := fresh "R10" in prreg HS (10%bv : bv 5) R10;
  let R13 := fresh "R13" in prreg HS (13%bv : bv 5) R13; let R14 := fresh "R14" in prreg HS (14%bv : bv 5) R14;
  let R15 := fresh "R15" in prreg HS (15%bv : bv 5) R15; let R18 := fresh "R18" in prreg HS (18%bv : bv 5) R18;
  let R19 := fresh "R19" in prreg HS (19%bv : bv 5) R19; let R20 := fresh "R20" in prreg HS (20%bv : bv 5) R20;
  let R21 := fresh "R21" in prreg HS (21%bv : bv 5) R21; let R23 := fresh "R23" in prreg HS (23%bv : bv 5) R23;
  let R24 := fresh "R24" in prreg HS (24%bv : bv 5) R24; let R25 := fresh "R25" in prreg HS (25%bv : bv 5) R25;
  let R26 := fresh "R26" in prreg HS (26%bv : bv 5) R26; let R27 := fresh "R27" in prreg HS (27%bv : bv 5) R27.
Ltac rwr := lazymatch goal with |- getr ?rg ?r = _ =>
  match goal with R : getr rg r = _ |- _ => rewrite R end;
  rewrite ?ew_ewset_other by lia;
  first [ reflexivity
        | match goal with H : ew _ _ = _ |- _ => rewrite H end;
          first [ reflexivity
                | match goal with H : getr _ _ = w64 _ |- _ => rewrite H; reflexivity end
                | unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia ] ] end.
Ltac chain_tac HM :=
  let W' := fresh "W'" in let c' := fresh "c'" in let HP := fresh "HP" in
  intros W' c' _ HP; refine (seg_chain _ _ _ _ _ HM _ _ _ W' c' HP);
  [ match goal with Hx : getr ?r0 2 = w64 _ |- _ = getr ?r0 2 => rewrite Hx end; rwr | rwr | rwr ].
Lemma seg_hx4 : forall j, i + 1 <= j -> j + 5 < n -> (j + 6 < n -> SLP (j + 6)) ->
  HXP A_HX4 j (if negb (jhexd (jbyte BZ (j + 5))) then None else jstr BZ i (j + 6) (length BS)).
Proof.
intros j Hj Hj5 HSL regs m md HJ HW H2 H3 H4 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs (jx_extra (j + 1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E25 : ew E 25 = Z_to_bv 64 (j + 1)) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E9 : ew E 9 = Z_to_bv 64 i) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E23 : ew E 23 = Z_to_bv 64 v) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E260 : ew E 260 = Z_to_bv 64 (VAL (A_OBJ 19))) by (subst E; exact (Eimg_img _ (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
jx_facts E HE regs (j + 1).
pose proof (hx_entry A_HX4 regs m j HW H2 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15 Hj Hj5) as HS. rewrite <- HE in HS.
pose proof (jbyte_range (j + 1 + 4)). pose proof (jbyte_range (j + 5)).
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [] E (mrestrict (w_H W) m)) by constructor.
pose proof (mk_refl m (fun _ => False)) as HM0.
addb HS 4 (j + 1).
{ exact HW. } { exact E32. } { exact E37. } { lia. } { lia. } { lia. } { cbn. exact I. }
clear HS. rename HS0 into HS.
paj_run_tok RUN HS HJ SHOK jsBsp. { oblB HW 4 (j + 1). } { awr_ok_tac. }
assert (HM1 : MK m (ms_mem ms) (fun _ => False)) by (mk_tac HM0 HFr HG). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK jsBsp.
- hcU Hc. rewrite bf_hex1 in Hc by lia.
  assert (HX : jhexd (jbyte BZ (j + 5)) = true) by (replace (j + 5) with (j + 1 + 4) by lia; unfold jhexd; rewrite Hc; reflexivity).
  clear Hc. rewrite HX. cbn [negb].
  paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK jsBsp.
  + hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Q6.
    rewrite jstr_ge by lia.
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    seg_exit0 HS HJ HM3.
  + hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Q6.
    paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_SL. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    prregs_sl HS. pmkst HS.
    eapply SRr_mono; [eapply (HSL ltac:(lia) _ _ _ HJ (jw_of_mk _ _ HW HM3)) | chain_tac HM3].
    all: rwr.
- hcU Hc. rewrite bf_hex1 in Hc by lia. rename Hc into Qd.
  paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK jsBsp.
  + hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
    assert (HX : jhexd (jbyte BZ (j + 5)) = false) by (replace (j + 5) with (j + 1 + 4) by lia; apply negb_true_iff; exact Hc).
    clear Hc. rewrite HX. cbn [negb].
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    seg_exit0 HS HJ HM3.
  + hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
    assert (HX : jhexd (jbyte BZ (j + 5)) = true) by (replace (j + 5) with (j + 1 + 4) by lia; apply negb_false_iff; exact Hc).
    clear Hc. rewrite HX. cbn [negb].
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK jsBsp.
    * hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Q6.
      rewrite jstr_ge by lia.
      paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
      assert (HM4 : MK m (ms_mem ms2) (fun _ => False)) by (mk_tac HM3 HFr HG). clear HF HFr HG.
      seg_exit0 HS HJ HM4.
    * hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Q6.
      paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_SL. { awr_ok_tac. }
      assert (HM4 : MK m (ms_mem ms2) (fun _ => False)) by (mk_tac HM3 HFr HG). clear HF HFr HG.
      prregs_sl HS. pmkst HS.
      eapply SRr_mono; [eapply (HSL ltac:(lia) _ _ _ HJ (jw_of_mk _ _ HW HM4)) | chain_tac HM4].
      all: rwr.
Qed.

Lemma seg_hx3 : forall j, i + 1 <= j -> j + 5 < n -> (j + 6 < n -> SLP (j + 6)) ->
  HXP A_HX3 j (if negb (jhexd (jbyte BZ (j + 4)) && jhexd (jbyte BZ (j + 5))) then None else jstr BZ i (j + 6) (length BS)).
Proof.
intros j Hj Hj5 HSL regs m md HJ HW H2 H3 H4 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs (jx_extra (j + 1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E25 : ew E 25 = Z_to_bv 64 (j + 1)) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E9 : ew E 9 = Z_to_bv 64 i) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E23 : ew E 23 = Z_to_bv 64 v) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E260 : ew E 260 = Z_to_bv 64 (VAL (A_OBJ 19))) by (subst E; exact (Eimg_img _ (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
jx_facts E HE regs (j + 1).
pose proof (hx_entry A_HX3 regs m j HW H2 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15 Hj Hj5) as HS. rewrite <- HE in HS.
pose proof (jbyte_range (j + 1 + 3)). pose proof (jbyte_range (j + 4)).
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [] E (mrestrict (w_H W) m)) by constructor.
pose proof (mk_refl m (fun _ => False)) as HM0.
addb HS 3 (j + 1).
{ exact HW. } { exact E32. } { exact E36. } { lia. } { lia. } { lia. } { cbn. exact I. }
clear HS. rename HS0 into HS.
paj_run_tok RUN HS HJ SHOK jsBsp. { oblB HW 3 (j + 1). } { awr_ok_tac. }
assert (HM1 : MK m (ms_mem ms) (fun _ => False)) by (mk_tac HM0 HFr HG). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK jsBsp.
- hcU Hc. rewrite bf_hex1 in Hc by lia.
  assert (HX : jhexd (jbyte BZ (j + 4)) = true) by (replace (j + 4) with (j + 1 + 3) by lia; unfold jhexd; rewrite Hc; reflexivity).
  clear Hc. rewrite HX. cbn [andb].
  paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_HX4. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  prregs_sl HS. pmkst HS.
  eapply SRr_mono; [eapply (seg_hx4 j Hj Hj5 HSL _ _ _ HJ (jw_of_mk _ _ HW HM2)) | chain_tac HM2].
  all: rwr.
- hcU Hc. rewrite bf_hex1 in Hc by lia. rename Hc into Qd.
  paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK jsBsp.
  + hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
    assert (HX : jhexd (jbyte BZ (j + 4)) = false) by (replace (j + 4) with (j + 1 + 3) by lia; apply negb_true_iff; exact Hc).
    clear Hc. rewrite HX. cbn [andb negb].
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    seg_exit0 HS HJ HM3.
  + hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
    assert (HX : jhexd (jbyte BZ (j + 4)) = true) by (replace (j + 4) with (j + 1 + 3) by lia; apply negb_false_iff; exact Hc).
    clear Hc. rewrite HX. cbn [andb].
    paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_HX4. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    prregs_sl HS. pmkst HS.
    eapply SRr_mono; [eapply (seg_hx4 j Hj Hj5 HSL _ _ _ HJ (jw_of_mk _ _ HW HM3)) | chain_tac HM3].
    all: rwr.
Qed.

Lemma seg_hx2 : forall j, i + 1 <= j -> j + 5 < n -> (j + 6 < n -> SLP (j + 6)) ->
  HXP A_HX2 j (if negb (jhexd (jbyte BZ (j + 3)) && jhexd (jbyte BZ (j + 4)) && jhexd (jbyte BZ (j + 5))) then None else jstr BZ i (j + 6) (length BS)).
Proof.
intros j Hj Hj5 HSL regs m md HJ HW H2 H3 H4 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs (jx_extra (j + 1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E25 : ew E 25 = Z_to_bv 64 (j + 1)) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E9 : ew E 9 = Z_to_bv 64 i) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E23 : ew E 23 = Z_to_bv 64 v) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E260 : ew E 260 = Z_to_bv 64 (VAL (A_OBJ 19))) by (subst E; exact (Eimg_img _ (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
jx_facts E HE regs (j + 1).
pose proof (hx_entry A_HX2 regs m j HW H2 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 H15 Hj Hj5) as HS. rewrite <- HE in HS.
pose proof (jbyte_range (j + 1 + 2)). pose proof (jbyte_range (j + 3)).
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [] E (mrestrict (w_H W) m)) by constructor.
pose proof (mk_refl m (fun _ => False)) as HM0.
addb HS 2 (j + 1).
{ exact HW. } { exact E32. } { exact E35. } { lia. } { lia. } { lia. } { cbn. exact I. }
clear HS. rename HS0 into HS.
paj_run_tok RUN HS HJ SHOK jsBsp. { oblB HW 2 (j + 1). } { awr_ok_tac. }
assert (HM1 : MK m (ms_mem ms) (fun _ => False)) by (mk_tac HM0 HFr HG). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK jsBsp.
- hcU Hc. rewrite bf_hex1 in Hc by lia.
  assert (HX : jhexd (jbyte BZ (j + 3)) = true) by (replace (j + 3) with (j + 1 + 2) by lia; unfold jhexd; rewrite Hc; reflexivity).
  clear Hc. rewrite HX. cbn [andb].
  paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_HX3. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  prregs_sl HS. pmkst HS.
  eapply SRr_mono; [eapply (seg_hx3 j Hj Hj5 HSL _ _ _ HJ (jw_of_mk _ _ HW HM2)) | chain_tac HM2].
  all: rwr.
- hcU Hc. rewrite bf_hex1 in Hc by lia. rename Hc into Qd.
  paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK jsBsp.
  + hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
    assert (HX : jhexd (jbyte BZ (j + 3)) = false) by (replace (j + 3) with (j + 1 + 2) by lia; apply negb_true_iff; exact Hc).
    clear Hc. rewrite HX. cbn [andb negb].
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    seg_exit0 HS HJ HM3.
  + hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
    assert (HX : jhexd (jbyte BZ (j + 3)) = true) by (replace (j + 3) with (j + 1 + 2) by lia; apply negb_false_iff; exact Hc).
    clear Hc. rewrite HX. cbn [andb].
    paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_HX3. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    prregs_sl HS. pmkst HS.
    eapply SRr_mono; [eapply (seg_hx3 j Hj Hj5 HSL _ _ _ HJ (jw_of_mk _ _ HW HM3)) | chain_tac HM3].
    all: rwr.
Qed.
End w.
End h.
End f.
End d.
