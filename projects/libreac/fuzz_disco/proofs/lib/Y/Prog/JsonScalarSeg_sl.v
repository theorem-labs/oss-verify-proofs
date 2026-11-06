(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/JtokIs.v, with its module paths and module names changed; 629 of its 709 lines of code are new or changed and 549 lines of the source are left out. *)
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
#[local] Ltac LiaTwx2.zify_split_ranges ::= idtac.
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

Section mc.
Context {fx : YK11.FPState}.

Lemma aj_memchr_at : forall lo hi pc, amemchr_realizesM SEGS B lo hi pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c nn (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 nn ->
0 <= c < 256 -> 0 <= nn < 2 ^ 32 -> 0 < x -> x + nn <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok SEGS W regsT memT x nn -> amem_range x nn ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x nn ->
(0 < nn -> shadow_hull_vis (aview SEGS (w_H W) memT) x nn) ->
consts_view SEGS lo hi W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(exists kx, first_byte SEGS W memT x nn c kx /\ getr regs2 10 = (if kx <? nn then w64 (x + kx) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros lo hi pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c nn o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx Hcv.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x c nn HPRE Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsx Hmx Hrx Hhx Hcv). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; lia.
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End mc.

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
Hypothesis seg_hx2 : forall j, i + 1 <= j -> j + 5 < n -> (j + 6 < n -> SLP (j + 6)) ->
  HXP A_HX2 j (if negb (jhexd (jbyte BZ (j + 3)) && jhexd (jbyte BZ (j + 4)) && jhexd (jbyte BZ (j + 5))) then None else jstr BZ i (j + 6) (length BS)).
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

Lemma U_subk : forall E0 a c k x y, ew E0 a = Z_to_bv 64 x -> ew E0 c = Z_to_bv 64 y -> 0 <= y <= x + k -> 0 <= x < 2 ^ 64 -> x + k < 2 ^ 64 ->
  U E0 (SAlu ALU_ADD (SOff a k) (SMd M_MUL (SOff c 0) (SLit (-1)))) = x + k - y.
Proof.
intros E0 a c k x y Ha Hc Hy Hx Hk. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom_off E0 a x k Ha), (U_atom E0 c y Hc), U_SLit by lia.
unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (x + k + y * (2 ^ 64 - 1)) with ((x + k - y) + y * 2 ^ 64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma jstr_step : forall j, 0 <= j < n -> jstr BZ i j (length BS) =
  if jbyte BZ j =? 34 then Some (j + 1, 1, i + 1, j - i - 1)
  else if jbyte BZ j <? 32 then None
  else if jbyte BZ j =? 92 then
    if n <=? j + 1 then None
    else if negb (jesc (jbyte BZ (j + 1))) then None
    else if jbyte BZ (j + 1) =? 117 then
      if (n - (j + 1) <=? 4) || negb (jhexd (jbyte BZ (j + 2)) && jhexd (jbyte BZ (j + 3)) && jhexd (jbyte BZ (j + 4)) && jhexd (jbyte BZ (j + 5)))
      then None else jstr BZ i (j + 6) (length BS)
    else jstr BZ i (j + 2) (length BS)
  else jstr BZ i (j + 1) (length BS).
Proof.
intros j Hj.
assert (Hu : jstr BZ i j (length BS) = jstr BZ i j (Datatypes.S (length BS))) by (apply jstr_fuel; rewrite jlen_BZ, ZL; lia).
rewrite Hu. cbn [jstr]. rewrite jlen_BZ. replace (n <=? j) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
Qed.

Definition str14b : list Z := [34; 92; 47; 98; 102; 110; 114; 116; 117; 0].
Lemma esc_nf : forall c, (forall q, 0 <= q < 10 -> nth (Z.to_nat q) str14b 0 <> c) -> jesc c = false.
Proof.
intros c H. apply not_true_is_false. intros Ej. unfold jesc in Ej. apply existsb_exists in Ej as (y & Hy & Hc).
apply Z.eqb_eq in Hc. subst c. cbn [In] in Hy.
destruct Hy as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
  [apply (H 0) | apply (H 1) | apply (H 2) | apply (H 3) | apply (H 4) | apply (H 5) | apply (H 6) | apply (H 7) | apply (H 8)];
  first [lia | reflexivity].
Qed.
Lemma esc_f : forall q, 0 <= q < 10 -> nth (Z.to_nat q) str14b 0 <> 0 -> jesc (nth (Z.to_nat q) str14b 0) = true.
Proof.
intros q Hq Hn.
assert (q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9) as Hq' by lia.
destruct Hq' as [->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]; first [reflexivity | exfalso; apply Hn; reflexivity].
Qed.
Lemma sl_memchr : forall memT c kx, JW memT -> 0 <= c < 256 -> first_byte SEGS W memT (VAL (A_OBJ 19)) 10 c kx ->
  (kx < 10 -> c <> 0 -> jesc c = true) /\ (10 <= kx -> jesc c = false).
Proof.
intros memT c kx HW Hc (Hk & Hpre & Hat).
destruct (jw_str14 memT HW) as (_ & HG & _).
change ([34; 92; 47; 98; 102; 110; 114; 116; 117] ++ [0]) with str14b in HG.
assert (AV : forall q, 0 <= q < 10 -> aview SEGS (w_H W) memT (VAL (A_OBJ 19) + q) = Some (nth (Z.to_nat q) str14b 0)).
{ intros q Hq. pose proof (jt_garr8_aview _ _ _ _ (Z.to_nat q) HG ltac:(unfold str14b; cbn [length]; lia)) as V.
  rewrite Z2Nat.id in V by lia. exact V. }
split.
- intros Hk10 Hc0. specialize (Hat Hk10). rewrite AV in Hat by lia. injection Hat as Hat. subst c. apply esc_f; [lia | exact Hc0].
- intros Hk10. apply esc_nf. intros q Hq Heq. destruct (Hpre q ltac:(lia)) as (bb & Hb & Hne).
  rewrite AV in Hb by lia. injection Hb as Hb. subst bb. exact (Hne Heq).
Qed.
Definition sl_regs : list sv :=
  jR 8%bv (SOff 25 (-1)) (jR 26%bv (SLit 34) (jR 13%bv (SLit 32) (jR 14%bv (SLit 92) (jR 21%bv (SOff (A_OBJ 19) 0) sr_atoms)))).
Definition ss_sl : sstate := add_cond (mkSS A_SL sl_regs [breg 0] None sl_facts) (mkAC BC_LTU (SOff 25 0) (SOff 19 0)).
Lemma sl_entry : forall regs m j, JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 20 = w64 b -> getr regs 25 = w64 j -> getr regs 8 = w64 (j - 1) ->
  getr regs 26 = w64 34 -> getr regs 13 = w64 32 -> getr regs 14 = w64 92 -> getr regs 21 = w64 (VAL (A_OBJ 19)) ->
  getr regs 19 = w64 n -> getr regs 24 = w64 (2 ^ 64 - 1 - b) -> getr regs 9 = w64 i -> getr regs 23 = w64 v ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 (b + i) -> i + 1 <= j < n ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (jx_extra j))) ss_sl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_SL)) m (seg_rom SEGS))).
Proof.
intros regs m j HW H2 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 Hj.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs (jx_extra j))) as E eqn:HE.
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E25 : ew E 25 = Z_to_bv 64 j) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E9 : ew E 9 = Z_to_bv 64 i) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E23 : ew E 23 = Z_to_bv 64 v) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
jx_facts E HE regs j.
pose proof (jw_B m HW) as HGB.
destruct (garr8_at _ _ _ (j + 0) HGB ltac:(unfold BZ; rewrite length_map; lia)) as [VB0 RB0]. rewrite !Z.add_0_r in VB0, RB0.
pose proof (jbyte_range j). pose proof (jbyte_range (j + 1)). pose proof (jbyte_range (j + 2)).
pose proof (jbyte_range (j + 3)). pose proof (jbyte_range (j + 4)). pose proof (jbyte_range (j + 5)).
rewrite restrict_mkst_fx. unfold ss_sl. apply st_ok_pi_add_cond.
2:{ rewrite branch_ltu_U, (U_atom E 25 j E25), (U_atom E 19 n E19) by lia. apply Z.ltb_lt. lia. }
apply pa_entry_st_ok_full.
- unfold sl_regs, jR. rewrite HE.
  repeat (apply regs_ok_pin; [| intros X; discriminate X | ]).
  + apply regs_ok_Eimg_Ereg.
  + rewrite H21. cbn [sv_denot]. rewrite (Eimg_img _ (A_OBJ 19)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite H14. reflexivity.
  + rewrite H13. reflexivity.
  + rewrite H26. reflexivity.
  + rewrite H8. rewrite <- HE. rewrite denot_lit_U, (U_atom_off E 25 j (-1) E25) by lia. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, breg. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
  rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (b + j) 0 1 (SOff 33 0) (jbyte BZ j));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
  rewrite Z.add_0_r. exact VB0.
- cbn. exact (conj I I).
- split; [|split; [exact I|]].
  + cbn [sl_facts f_atoms atoms_ok]. unfold afact_ok, jSP, jIDX, jVP, jSB, jPTR, jNOTP, jBYTE. cbn [af_lo af_hi af_al2].
    rewrite E2, E20, E25, E19, E24, E9, E23, E27, E18, E32, E33, E34, E35, E36, E37, E38.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((spe - 128) mod 16 = 0) by (rewrite Zminus_mod, Zsp16; reflexivity).
    unfold SHADOW_OFF. repeat split; lia.
  + cbn [sl_facts f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 20 b E20), (U_atom E 25 j E25), (U_atom E 32 (b + j) E32) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Definition vreg23 : YP09.region := YP09.mkRegion (Some 23%nat) 0 20 0 20 [].
Lemma U_jmi : forall E0 x y, ew E0 25 = Z_to_bv 64 x -> ew E0 9 = Z_to_bv 64 y -> 0 <= y < x -> x < 2 ^ 64 ->
  U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 9 0) (SLit (-1))) (SLit (-1))) (SOff 25 0)) = x - 1 - y.
Proof.
intros E0 x y Hx Hy Hr Hx64. rewrite !U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E0 9 y Hy), (U_atom E0 25 x Hx), !U_SLit by lia.
unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia.
replace (y * (2 ^ 64 - 1) + (2 ^ 64 - 1 + x)) with ((x - 1 - y) + (y + 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
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
Ltac mkhm HS HMo HMn HF HFr HG :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    lazymatch type of HMo with MK ?m0 _ _ => assert (HMn : MK m0 (ms_mem msx) (fun _ => False)) by (mk_tac HMo HFr HG) end
  end; clear HF HFr HG.
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
Lemma seg_sl : forall (f : nat) regs m md j,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 20 = w64 b -> getr regs 25 = w64 j -> getr regs 8 = w64 (j - 1) ->
  getr regs 26 = w64 34 -> getr regs 13 = w64 32 -> getr regs 14 = w64 92 -> getr regs 21 = w64 (VAL (A_OBJ 19)) ->
  getr regs 19 = w64 n -> getr regs 24 = w64 (2 ^ 64 - 1 - b) -> getr regs 9 = w64 i -> getr regs 23 = w64 v ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 (b + i) ->
  i + 1 <= j < n -> n - j <= Z.of_nat f ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_SL)) m (seg_rom SEGS)) md) (SEGPOST m regs (jstr BZ i j (length BS))).
Proof.
induction f as [|f IH]; intros regs m md j HJ HW H2 H3 H4 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 Hj Hf; [lia|].
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSL : forall j2, i + 1 <= j2 < n -> n - j2 <= Z.of_nat f -> SLP j2).
{ intros j2 Hj2 Hf2 regs' m' md'. intros. eapply IH; eauto. }
rewrite (jstr_step j) by lia.
remember (Eimg (Ereg regs (jx_extra j))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (spe - 128)) by (subst E; ereg 2%nat (2%bv : bv 5) H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (subst E; ereg 20%nat (20%bv : bv 5) H20).
assert (E25 : ew E 25 = Z_to_bv 64 j) by (subst E; ereg 25%nat (25%bv : bv 5) H25).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (subst E; ereg 19%nat (19%bv : bv 5) H19).
assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; ereg 24%nat (24%bv : bv 5) H24).
assert (E9 : ew E 9 = Z_to_bv 64 i) by (subst E; ereg 9%nat (9%bv : bv 5) H9).
assert (E23 : ew E 23 = Z_to_bv 64 v) by (subst E; ereg 23%nat (23%bv : bv 5) H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; ereg 27%nat (27%bv : bv 5) H27).
assert (E18 : ew E 18 = Z_to_bv 64 (b + i)) by (subst E; ereg 18%nat (18%bv : bv 5) H18).
assert (E260 : ew E 260 = Z_to_bv 64 (VAL (A_OBJ 19))) by (subst E; exact (Eimg_img _ (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
jx_facts E HE regs j.
pose proof (sl_entry regs m j HW H2 H20 H25 H8 H26 H13 H14 H21 H19 H24 H9 H23 H27 H18 Hj) as HS. rewrite <- HE in HS.
pose proof (jbyte_range j). pose proof (jbyte_range (j + 1)). pose proof (jbyte_range (j + 2)).
pose proof (jbyte_range (j + 3)). pose proof (jbyte_range (j + 4)). pose proof (jbyte_range (j + 5)).
assert (UBx : U E jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jsBx [] E (mrestrict (w_H W) m)) by constructor.
pose proof (mk_refl m (fun _ => False)) as HM0.
paj_run_tok RUN HS HJ SHOK jsBsp. { oblB HW 0 j. } { awr_ok_tac. }
assert (HM1 : MK m (ms_mem ms) (fun _ => False)) by (mk_tac HM0 HFr HG). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK jsBsp.
- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. rewrite Hc. rename Hc into Q34.
  pose proof (jw_of_mk _ _ HW HM1) as HW1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (F23 : ew Ex 23 = Z_to_bv 64 v) by (rewrite ?ew_ewset_other by lia; exact E23);
    assert (F32 : ew Ex 32 = Z_to_bv 64 (b + j)) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (UB1 : U Ex jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom Ex 27 SHADOW_OFF) by (try (rewrite ?ew_ewset_other by lia; exact E27); unfold SHADOW_OFF; lia); reflexivity);
    pose proof (st_ok_pi_add_region Ex _ _ vreg23 HS eq_refl) as HSv
  end.
  match type of HSv with ?P1 -> ?P2 -> _ => assert (HP1 : P1); [|assert (HP2 : P2); [|specialize (HSv HP1 HP2); clear HP1 HP2]] end.
  { unfold region_ok, vreg23. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite F23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply (jw_vpres _ HW1). lia. }
  { apply all_disjoint_of_extents. unfold extent_of_region, vreg23.
    cbn [add_cond ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite F23, F32, !unsigned_lit_small by lia. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I; lia. }
  clear HS.
  lazymatch type of HSv with st_ok_pi _ _ ?Ex _ _ =>
    assert (SHOKv : sh_ok SEGS jsBx [mkSHE 23 0 20] Ex (mrestrict (w_H W) (ms_mem ms)))
  end.
  { constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) _ jsBx 23 v 20 v 0 20 (jw_vra _ HW1) UB1); [rewrite (U_atom _ 23 v F23) by lia; reflexivity | lia | lia |].
    intros y Hy. change (Z.min 0 20) with 0 in Hy. change (Z.max 0 20) with 20 in Hy. apply js_v_app. lia. }
  clear SHOK.
  paj_run_tok RUN HSv HJ SHOKv jsBsp.
  { eapply awr_ok_cons_gen; [reflexivity | rewrite F23, unsigned_lit_small by lia; reflexivity | | awr_ok_tac].
    intros a Ha. apply js_awr_v. cbn [YP09.r_wlo YP09.r_whi vreg23] in Ha. lia. }
  assert (MKw : MK m (ms_mem ms0) (fun a => v <= a < v + 20)).
  { apply (mk_trans m (ms_mem ms) (ms_mem ms0) _ HM1).
    apply (mk_frame (ms_mem ms) (ms_mem ms) (ms_mem ms0) _ _ _ (mk_refl _ _) HFr HG).
    intros a (r & Hr0 & Hr). lazymatch type of Hr0 with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr0 end.
    cbn [In] in Hr0. destruct Hr0 as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?F23, ?F32, ?unsigned_lit_small in Hr by lia; [left; lia | lia]. }
  clear HF HFr HG.
  prregs_sl HSv.
  pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HSv eq_refl) as RV. cbn [ms_mem restrict] in RV.
  lazymatch type of RV with region_ok _ ?E1 _ _ =>
    pose proof (field_of_region_any (segs := SEGS) E1 _ 23 v _ _ _ _ _ 0 8 (SOff 18 1) RV ltac:(rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia) ltac:(right; right; left; reflexivity) ltac:(lia)) as F0;
    pose proof (field_of_region_any (segs := SEGS) E1 _ 23 v _ _ _ _ _ 8 8 _ RV ltac:(rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia) ltac:(right; left; reflexivity) ltac:(lia)) as F8;
    pose proof (field_of_region_any (segs := SEGS) E1 _ 23 v _ _ _ _ _ 16 4 _ RV ltac:(rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(lia)) as F16;
    assert (U0 : U E1 (SOff 18 1) = b + i + 1) by (apply (U_atom_off E1 18 (b + i) 1); [rewrite ?ew_ewset_other by lia; exact E18 | lia | lia]);
    assert (U8 : U E1 (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 9 0) (SLit (-1))) (SLit (-1))) (SOff 25 0)) = j - 1 - i)
      by (apply U_jmi; [rewrite ?ew_ewset_other by lia; exact E25 | rewrite ?ew_ewset_other by lia; exact E9 | lia | lia]);
    change (bv_unsigned (sv_denot E1 (SOff 18 1))) with (U E1 (SOff 18 1)) in F0;
    change (bv_unsigned (sv_denot E1 (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 9 0) (SLit (-1))) (SLit (-1))) (SOff 25 0))))
      with (U E1 (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 9 0) (SLit (-1))) (SLit (-1))) (SOff 25 0))) in F8;
    rewrite U0 in F0; rewrite U8 in F8; cbn [sv_denot] in F16
  end.
  rewrite Z.add_0_r in F0. change (8 * Z.of_N 8) with 64 in F0, F8. change (8 * Z.of_N 4) with 32 in F16.
  rewrite Z.mod_small in F0, F8 by lia. rewrite unsigned_lit_small in F16 by lia. rewrite Z.mod_small in F16 by lia.
  pmkst HSv. apply SRr_ret. unfold SEGPOST. split; [reflexivity|].
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mm _) ?d = _ /\ _ => exists rg, mm, d end.
  split; [reflexivity|]. split; [exact HJ|].
  cbn [ms_regs]. rewrite R2, R3, R4, E2, E3, E4, H2.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite R10, E25, unsigned_lit_small by lia; reflexivity|].
  split; [replace (b + (i + 1)) with (b + i + 1) by lia; exact F0|].
  split; [replace (j - i - 1) with (j - 1 - i) by lia; exact F8|].
  split; [exact F16 | exact MKw].
- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. rewrite Hc. rename Hc into Q34.
  paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
  assert (HM2 : MK m (ms_mem ms0) (fun _ => False)) by (mk_tac HM1 HFr HG). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK jsBsp.
  + hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. rewrite Hc. rename Hc into Q32.
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    seg_exit0 HS HJ HM3.
  + hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. rewrite Hc. rename Hc into Q32.
    paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
    assert (HM3 : MK m (ms_mem ms1) (fun _ => False)) by (mk_tac HM2 HFr HG). clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK jsBsp.
    * hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. apply negb_true_iff in Hc. rewrite Hc. rename Hc into Q92.
      paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
      assert (HM4 : MK m (ms_mem ms2) (fun _ => False)) by (mk_tac HM3 HFr HG). clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK jsBsp.
      -- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Qn1.
         rewrite jstr_ge by lia.
         paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
         assert (HM5 : MK m (ms_mem ms3) (fun _ => False)) by (mk_tac HM4 HFr HG). clear HF HFr HG.
         seg_exit0 HS HJ HM5.
      -- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Qn1.
         paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_SL. { awr_ok_tac. }
         assert (HM5 : MK m (ms_mem ms3) (fun _ => False)) by (mk_tac HM4 HFr HG). clear HF HFr HG.
         prregs_sl HS. pmkst HS.
         eapply SRr_mono; [eapply (HSL (j + 1) ltac:(lia) ltac:(lia) _ _ _ HJ (jw_of_mk _ _ HW HM5)) | chain_tac HM5].
         all: rwr.
    * hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. apply negb_false_iff in Hc. rewrite Hc. rename Hc into Q92.
      paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
      assert (HM4 : MK m (ms_mem ms2) (fun _ => False)) by (mk_tac HM3 HFr HG). clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK jsBsp.
      -- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Qn1.
         replace (n <=? j + 1) with true by (symmetry; apply Z.leb_le; lia).
         paj_run_tok RUN HS HJ SHOK jsBsp. { awr_ok_tac. }
         assert (HM5 : MK m (ms_mem ms3) (fun _ => False)) by (mk_tac HM4 HFr HG). clear HF HFr HG.
         seg_exit0 HS HJ HM5.
      -- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Qn1.
         replace (n <=? j + 1) with false by (symmetry; apply Z.leb_gt; lia).
         addb HS 1 j.
         { exact (jw_of_mk _ _ HW HM4). }
         { rewrite ?ew_ewset_other by lia. exact E32. }
         { rewrite ?ew_ewset_other by lia. exact E34. }
         { lia. } { lia. } { lia. }
         { apply all_disjoint_of_extents. unfold extent_of_region, breg.
           cbn [add_cond ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val].
           rewrite ?ew_ewset_other by lia. rewrite E32, unsigned_lit_small by lia. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
           repeat split; try exact I; lia. }
         clear HS. rename HS0 into HS.
         paj_run_tok RUN HS HJ SHOK jsBsp. { oblB (jw_of_mk _ _ HW HM4) 1 j. } { awr_ok_tac. }
         assert (HM5 : MK m (ms_mem ms3) (fun _ => False)) by (mk_tac HM4 HFr HG). clear HF HFr HG.
         pose proof (jw_of_mk _ _ HW HM5) as HW5.
         prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
         prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
         pmkst HS.
         destruct (jw_str14 _ HW5) as (_ & S14g & S14a & S14b & _ & S14m & S14r & S14h & _ & S14i).
         change (Z.of_nat (length [34; 92; 47; 98; 102; 110; 114; 116; 117])) with 9 in S14b, S14m, S14r, S14h, S14i.
         change (9 + 1) with 10 in S14m, S14r, S14h.
         assert (Ho16 : (spe - 128 - sp0) mod 16 = 0).
         { pose proof (Z.div_mod spe 16 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). rewrite Zsp16 in *. rewrite Zsp016 in *.
           apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). exists (spe / 16 - 8 - sp0 / 16). lia. }
         eapply SRr_bind.
         { eapply (aj_memchr_at MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_memchr) (AMEMCHR fx) W (ms_regs ms3) (ms_mem ms3)
             STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc _ kk (VAL (A_OBJ 19)) (jbyte BZ (j + 1)) 10 (spe - 128 - sp0) (Z_to_bv 64 (BASE + 12024)) HJ).
           - rewrite Ra0, E260. reflexivity.
           - rewrite Ra1, E34. reflexivity.
           - rewrite Ra2. reflexivity.
           - lia.
           - lia.
           - exact S14a.
           - lia.
           - unfold spZ. rewrite Rsp, E2, unsigned_lit_small by lia. lia.
           - exact Ho16.
           - lia.
           - unfold TJSON_SCALAR_STK, ESTACK in *. lia.
           - rewrite Rgp, E3. exact H3.
           - rewrite Rtp, E4. exact H4.
           - exact Rra.
           - apply ret_ok_codeptr_v; [lia | reflexivity].
           - intros a Ha. split.
             + apply (jt_garr8_present W (ms_mem ms3) (VAL (A_OBJ 19)) _ a S14g).
               change (Z.of_nat (length ([34; 92; 47; 98; 102; 110; 114; 116; 117] ++ [0]))) with 10. lia.
             + unfold spZ. rewrite Rsp, E2, unsigned_lit_small by lia. pose proof (pa_segs_low a (S14i a ltac:(lia))).
               unfold TJSON_SCALAR_STK, ESTACK in *. lia.
           - exact S14m.
           - exact S14r.
           - intros _. exact S14h.
           - exact (jw_cv _ HW5). }
         cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kx & Hfb & Hres) & Hfr2 & Hpres2).
         assert (HM6 : MK m mem2 (fun _ => False)).
         { apply (mk_call m (ms_mem ms3) mem2 (spe - 128 - ESTACK) (spe - 128) _ HM5).
           - intros a Ha Hn. apply Hfr2; [exact Ha | intros X; apply Hn; lia].
           - exact Hpres2.
           - unfold TJSON_SCALAR_STK, ESTACK. lia.
           - lia. }
         pose proof (sl_memchr (ms_mem ms3) (jbyte BZ (j + 1)) kx HW5 ltac:(lia) Hfb) as [MF MN].
         jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
         match type of HS2 with ?Q -> _ => assert (HQ : Q); [|specialize (HS2 HQ); clear HQ] end.
         { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
           all: apply (region_kept_aview (segs := SEGS) _ (w_H W) (ms_mem ms3) mem2 32 (b + j));
             [rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia
             | intros a Ha; apply Hfr2; [lia | intros X; destruct Zbw; unfold TJSON_SCALAR_STK, ESTACK in *; lia]
             | exact Hpres2]. }
         clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
         lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E5 eqn:HE5 in HS end.
         assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [assumption | cbv; lia]).
         assert (OLD5 : forall q, (q < 40)%nat -> ew E5 q = ew E q)
           by (intros q Hq; rewrite HE5, ew_havoc_old by exact Hq; rewrite ?ew_ewset_other by lia; reflexivity).
         assert (G44 : ew E5 44 = getr regs2 10) by (rewrite HE5; reflexivity).
         assert (G260 : ew E5 260 = Z_to_bv 64 (VAL (A_OBJ 19)))
           by (rewrite HE5, ew_havoc_above by (rewrite length_map; unfold CLOB; cbn [length]; lia); rewrite ?ew_ewset_other by lia; exact E260).
         clear HE5.
         assert (G2 : ew E5 2 = Z_to_bv 64 (spe - 128)) by (rewrite OLD5 by lia; exact E2).
         assert (G3 : ew E5 3 = getr regs 3) by (rewrite OLD5 by lia; exact E3).
         assert (G4 : ew E5 4 = getr regs 4) by (rewrite OLD5 by lia; exact E4).
         assert (G20 : ew E5 20 = Z_to_bv 64 b) by (rewrite OLD5 by lia; exact E20).
         assert (G25 : ew E5 25 = Z_to_bv 64 j) by (rewrite OLD5 by lia; exact E25).
         assert (G19 : ew E5 19 = Z_to_bv 64 n) by (rewrite OLD5 by lia; exact E19).
         assert (G24 : ew E5 24 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (rewrite OLD5 by lia; exact E24).
         assert (G9 : ew E5 9 = Z_to_bv 64 i) by (rewrite OLD5 by lia; exact E9).
         assert (G23 : ew E5 23 = Z_to_bv 64 v) by (rewrite OLD5 by lia; exact E23).
         assert (G27 : ew E5 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD5 by lia; exact E27).
         assert (G18 : ew E5 18 = Z_to_bv 64 (b + i)) by (rewrite OLD5 by lia; exact E18).
         assert (G32 : ew E5 32 = Z_to_bv 64 (b + j)) by (rewrite OLD5 by lia; exact E32).
         assert (G34 : ew E5 34 = Z_to_bv 64 (jbyte BZ (j + 1))) by (rewrite OLD5 by lia; exact E34).
         assert (G35 : ew E5 35 = Z_to_bv 64 (jbyte BZ (j + 2))) by (rewrite OLD5 by lia; exact E35).
         clear OLD5.
         assert (SHOK5 : sh_ok SEGS jsBx [] E5 (mrestrict (w_H W) mem2)) by constructor.
         clear SHOK.
         paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
         mkhm HS HM6 HM7 HF HFr HG.
         pose proof (proj1 Hfb) as Hkx.
         rewrite Hres in G44. destruct (kx <? 10) eqn:Kx; unfold w64 in G44.
         ++ apply Z.ltb_lt in Kx.
            psrr_branch_tok RUN BR HS SHOK5 jsBsp.
            ** exfalso. hcU Hc. pose proof (Z.mod_small (VAL (A_OBJ 19) + kx) (2 ^ 64) ltac:(lia)) as Mx.
               rewrite Z.add_0_r, Mx in Hc. apply Z.eqb_eq in Hc. rewrite Zmod_0_l in Hc. lia.
            ** clear Hc.
               paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
               mkhm HS HM7 HM8 HF HFr HG.
               psrr_branch_tok RUN BR HS SHOK5 jsBsp.
               --- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. apply Z.eqb_eq in Hc. rename Hc into Qc0.
                   rewrite Qc0. change (jesc 0) with false. cbn [negb].
                   paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                   mkhm HS HM8 HM9 HF HFr HG.
                   seg_exit0 HS HJ2 HM9.
               --- hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. apply Z.eqb_neq in Hc. rename Hc into Qc0.
                   rewrite (MF Kx Qc0). cbn [negb].
                   paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                   mkhm HS HM8 HM9 HF HFr HG.
                   psrr_branch_tok RUN BR HS SHOK5 jsBsp.
                   +++ hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. apply negb_true_iff in Hc. rewrite Hc. rename Hc into Qu.
                       paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                       mkhm HS HM9 HM10 HF HFr HG.
                       psrr_branch_tok RUN BR HS SHOK5 jsBsp.
                       *** hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Qn2.
                           rewrite jstr_ge by lia.
                           paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                           mkhm HS HM10 HM11 HF HFr HG.
                           seg_exit0 HS HJ2 HM11.
                       *** hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Qn2.
                           paj_run_to_tok RUNTO HS HJ2 SHOK5 jsBsp A_SL. { awr_ok_tac. }
                           mkhm HS HM10 HM11 HF HFr HG.
                           prregs_sl HS. pmkst HS.
                           eapply SRr_mono; [eapply (HSL (j + 2) ltac:(lia) ltac:(lia) _ _ _ HJ2 (jw_of_mk _ _ HW HM11)) | chain_tac HM11].
                           all: rwr.
                   +++ hcU Hc. rewrite !Z.mod_small in Hc by (clear Zbw Zbv Zvw Zv8 Zsp16 Zsp016; lia). rewrite Z.add_0_r in Hc. apply negb_false_iff in Hc. rewrite Hc. rename Hc into Qu.
                       paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                       mkhm HS HM9 HM10 HF HFr HG.
                       psrr_branch_tok RUN BR HS SHOK5 jsBsp.
                       *** rewrite branch_ltu_U in Hc.
                           rewrite (U_subk _ 19 25 (-1) n j) in Hc by (first [rewrite ?ew_ewset_other by lia; assumption | lia]).
                           rewrite U_litm, (Z.mod_small 5) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Q5.
                           replace (n - (j + 1) <=? 4) with true by (symmetry; apply Z.leb_le; lia). cbn [orb].
                           paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                           mkhm HS HM10 HM11 HF HFr HG.
                           seg_exit0 HS HJ2 HM11.
                       *** rewrite branch_ltu_U in Hc.
                           rewrite (U_subk _ 19 25 (-1) n j) in Hc by (first [rewrite ?ew_ewset_other by lia; assumption | lia]).
                           rewrite U_litm, (Z.mod_small 5) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Q5.
                           replace (n - (j + 1) <=? 4) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb].
                           assert (HSL6 : j + 6 < n -> SLP (j + 6)) by (intros Hj6; apply HSL; lia).
                           addb HS 2 j.
                           { exact (jw_of_mk _ _ HW HM10). }
                           { rewrite ?ew_ewset_other by lia. exact G32. }
                           { rewrite ?ew_ewset_other by lia. exact G35. }
                           { lia. } { lia. } { lia. }
                           { apply all_disjoint_of_extents. unfold extent_of_region, breg.
                             cbn [add_cond ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val].
                             rewrite ?ew_ewset_other by lia. rewrite G32, unsigned_lit_small by lia. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
                             repeat split; try exact I; lia. }
                           clear HS. rename HS0 into HS.
                           paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { oblB (jw_of_mk _ _ HW HM10) 2 j. } { awr_ok_tac. }
                           mkhm HS HM10 HM11 HF HFr HG.
                           psrr_branch_tok RUN BR HS SHOK5 jsBsp.
                           ---- hcU Hc. rewrite bf_hex1 in Hc by lia.
                                assert (HX : jhexd (jbyte BZ (j + 2)) = true) by (unfold jhexd; rewrite Hc; reflexivity).
                                clear Hc. rewrite HX. cbn [andb].
                                paj_run_to_tok RUNTO HS HJ2 SHOK5 jsBsp A_HX2. { awr_ok_tac. }
                                mkhm HS HM11 HM12 HF HFr HG.
                                prregs_sl HS. pmkst HS.
                                eapply SRr_mono; [eapply (seg_hx2 j ltac:(lia) ltac:(lia) HSL6 _ _ _ HJ2 (jw_of_mk _ _ HW HM12)) | chain_tac HM12].
                                all: rwr.
                           ---- hcU Hc. rewrite bf_hex1 in Hc by lia. rename Hc into Qd.
                                paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                                mkhm HS HM11 HM12 HF HFr HG.
                                psrr_branch_tok RUN BR HS SHOK5 jsBsp.
                                ++++ hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
                                     assert (HX : jhexd (jbyte BZ (j + 2)) = false) by (apply negb_true_iff; exact Hc).
                                     clear Hc. rewrite HX. cbn [andb negb].
                                     paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
                                     mkhm HS HM12 HM13 HF HFr HG.
                                     seg_exit0 HS HJ2 HM13.
                                ++++ hcU2 Hc. rewrite bf_hex2 in Hc by (first [lia | exact Qd]).
                                     assert (HX : jhexd (jbyte BZ (j + 2)) = true) by (apply negb_false_iff; exact Hc).
                                     clear Hc. rewrite HX. cbn [andb].
                                     paj_run_to_tok RUNTO HS HJ2 SHOK5 jsBsp A_HX2. { awr_ok_tac. }
                                     mkhm HS HM12 HM13 HF HFr HG.
                                     prregs_sl HS. pmkst HS.
                                     eapply SRr_mono; [eapply (seg_hx2 j ltac:(lia) ltac:(lia) HSL6 _ _ _ HJ2 (jw_of_mk _ _ HW HM13)) | chain_tac HM13].
                                     all: rwr.
         ++ apply Z.ltb_ge in Kx.
            psrr_branch_tok RUN BR HS SHOK5 jsBsp.
            ** clear Hc. rewrite (MN Kx). cbn [negb].
               paj_run_tok RUN HS HJ2 SHOK5 jsBsp. { awr_ok_tac. }
               mkhm HS HM7 HM8 HF HFr HG.
               seg_exit0 HS HJ2 HM8.
            ** exfalso. hcU Hc. vm_compute in Hc. discriminate Hc.

Qed.
End w.
End h.
End f.
End d.
