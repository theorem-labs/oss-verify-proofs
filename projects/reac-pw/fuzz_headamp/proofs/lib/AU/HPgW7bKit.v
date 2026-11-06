(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/ACes.v:275-278
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/A/ACfk.v:194-195 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh9.v:115-118 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v at origin/ossv/recipes 2d2ff01bb6f2 (aj_strlen_at, as w7_strlen_at, over reac-pw/fuzz_role's image A: SEGS := rsegs, pa_segs_low := w7_segs_low, and the post also keeps the I/O state, same_io from the wrapper's same_but_materialized); the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bCall.v at 25d4b718638 (w7_strlen_at,
   w7_strlen_cstr's route) for reac-pw/fuzz_headamp's image B: the strlen call at image B's trampoline 0x41c18 on a
   HPgCaseB.cb_strok string; the memcpy step is lib/AU/HPgCaseB.v's cb_memcpy_at at image B's 0x51d8c; the two
   sources of a cb_strok fact (an image string as HPgBase.hd_cstr states it, the key's first part in ch) are new;
   w7_ -> hw7b_, module paths. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the two call steps of the walk of
   LLVMFuzzerTestOneInput from G 0x81afc to J 0x82618 and the string facts its turns use. Proves no function
   (kind: segment lemma).
   - hw7b_memcpy_at: the runtime's memcpy (0x51d8c) in the journal form (HPgCaseB.cb_memcpy_at at that pc).
   - hw7b_strlen_at: the strlen wrapper (lib/A/Rt/StrlenDef.v astrlen_realizes at STRLEN_ENTRY_B 0x41c18) on a
     cb_strok string, in the journal form keeping the I/O state.
   - hw7b_strok_cstr: a string of the image (HPgBase.hd_cstr, the hd_seg_pre clause hi_strs) is a cb_strok one.
   - hw7b_strok_ch: the key's first part in ch (F+0xa0, a frame object in scope) is a cb_strok one. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgMem HPgCaseB HPgW7bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- the memcpy step ---- *)
Lemma hw7b_memcpy_at : forall B, aintrin_realizes rsegs B OCpy HW7B_MEMCPY -> hw7b_memcpy_at_stmt B.
Proof.
intros B AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw.
exact (cb_memcpy_at B HW7B_MEMCPY AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw).
Qed.

(* ---- the strlen wrapper in the journal form (as reac_box_catalogue_defect.v's aj_strcmp_at for strcmp) ---- *)
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

Lemma hw7b_strlen_gen : forall pc, astrlen_realizes rsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte rsegs W memT x (k + 1) 0 k ->
src_ok rsegs W regsT memT x (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview rsegs (w_H W) memT) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview rsegs (w_H W) memT a <> None) ->
aro_unowned rsegs B (aview rsegs (w_H W) memT) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using LAWS.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
pose proof hw7b_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x k HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
    ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS hw7b_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact (same_io_materialized _ _ Hsame)|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End d.

(* the strlen call on a cb_strok string at the call site's stack top sp0 + o *)
Lemma hw7b_strlen_at : forall B, astrlen_realizes rsegs B HW7B_STRLEN -> hw7b_strlen_at_stmt B.
Proof.
intros B AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x s o raw
  HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HSO Hro.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HSO as (Hx0 & Hk32 & Hx63 & Hbytes & Hnul & Htail & Hstk & Hamx & Hrax & Hhux).
assert (HE : ESTACK = 4096) by reflexivity.
apply (hw7b_strlen_gen B LAWS HW7B_STRLEN AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x
  (Z.of_nat (length s)) o raw HJ Ha0 Hx0 ltac:(lia) Hk32 Hx63 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw).
- exact (cb_strok_first_byte W memT (sp0 + o) x s HSO).
- intros a Ha. split.
  + destruct (Z.eq_dec a (x + Z.of_nat (length s))) as [->|Hne]; [rewrite Hnul; discriminate|].
    destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
    replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
  + rewrite Hsp'. intros Hc. apply (Hstk a ltac:(lia)). lia.
- exact Hstk.
- exact Hamx.
- exact Hrax.
- exact Hhux.
- exact Htail.
- exact Hro.
Qed.

(* ---- the two sources of a cb_strok fact ---- *)
Lemma hw7b_strok_cstr : hw7b_strok_cstr_stmt.
Proof.
intros W m R x l HC Hst Hl.
destruct HC as (Hb & Hn & Hrng & H0 & Hhi & _ & Ham & Hra & Hhv & Htl).
unfold hd_zbytes in *. rewrite length_map in Hb, Hn, Hhi, Ham, Hra, Hhv, Htl.
assert (HE : ESTACK = 4096) by reflexivity.
split; [exact H0|]. split; [lia|]. split; [exact Hhi|].
split.
{ intros j Hj. specialize (Hb (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in Hb.
  assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
    rewrite map_nth. reflexivity. }
  rewrite Hnth in Hb. split; [exact Hb|].
  rewrite Forall_forall in Hrng. specialize (Hrng (bv_unsigned (nth j l (Z_to_bv 8 0)))).
  assert (0 < bv_unsigned (nth j l (Z_to_bv 8 0)) < 256); [|lia].
  apply Hrng. rewrite <- Hnth. apply nth_In. rewrite length_map. exact Hj. }
split; [exact Hn|]. split; [exact Htl|].
split; [intros a Ha; lia|].
split; [apply (hd_amem_range_le x _ (Z.of_nat (length l) + 8)); [lia | exact Ham]|].
split; [exact Hra | exact Hhv].
Qed.

Lemma hw7b_strok_ch : hw7b_strok_ch_stmt.
Proof.
intros W m R F chs Hfsh HF8 Happ HFR Hrd Hby Hnz Hl.
assert (HE : ESTACK = 4096) by reflexivity.
pose proof ASAN_CEIL_range as [[HC1 HC2] _].
assert (HFa : 4096 <= F /\ (F + 1024 <= kLowShadowBeg \/ (kHighMemBeg <= F /\ F + 1024 <= ASAN_CEIL)))
  by exact Happ.
destruct HFa as [HF0 HFa].
assert (L : length (chs ++ [NUL]) = S (length chs)) by (rewrite length_app; cbn [length]; lia).
pose proof (proj1 (hm_bytes_aview rsegs (w_H W) m (F + 0xa0) (chs ++ [NUL])) Hby) as Hv.
rewrite L in Hv.
split; [lia|]. split; [lia|].
split; [unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|].
split.
{ intros j Hj. specialize (Hv j ltac:(lia)). rewrite app_nth1 in Hv by exact Hj. split; [exact Hv|].
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hj. }
split.
{ specialize (Hv (length chs) ltac:(lia)). rewrite nth_middle in Hv. exact Hv. }
split.
{ intros a Ha. apply Hrd.
  assert (Hm : (F + 0xa0 + Z.of_nat (length chs)) mod 8 = Z.of_nat (length chs) mod 8).
  { replace (F + 0xa0 + Z.of_nat (length chs)) with (Z.of_nat (length chs) + (F / 8 + 20) * 8)
      by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
    apply Z.mod_add. lia. }
  rewrite Hm in Ha.
  assert (Hq : Z.of_nat (length chs) / 8 < 3) by (apply Z.div_lt_upper_bound; clear -Hl; lia).
  pose proof (Z.mod_pos_bound (Z.of_nat (length chs)) 8 ltac:(lia)) as Hm1.
  pose proof (Z.div_mod (Z.of_nat (length chs)) 8 ltac:(lia)) as Hm2.
  clear -Ha Hq Hm1 Hm2. lia. }
split; [intros a Ha; lia|].
split; [unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
split.
{ replace (F + 0xa0) with (F + HMU_CH + 0) by (unfold HMU_CH; lia).
  apply (hmu_B_ra_ch rsegs _ _ F true false false false true false false 0 (Z.of_nat (length chs) + 1) Hfsh HF8);
  lia. }
{ intros s Hs. unfold hd_fsh in Hfsh.
  assert (Hlen : Z.of_nat (length (hmu_sh true true false false false true false false)) = 116)
    by (rewrite hmu_sh_len; reflexivity).
  rewrite Hlen in Hfsh.
  unfold shadow_addr, SHADOW_OFF in *.
  set (L0 := Z.of_nat (length chs)) in *.
  assert (HL0 : 0 <= L0 <= 21) by (unfold L0; lia).
  assert (E1 : (F + 0xa0) / 8 = F / 8 + 20).
  { pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
    set (q := F / 8) in *. rewrite DF. replace (8 * q + 0xa0) with ((q + 20) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (E2 : (F + 0xa0 + (L0 + 1) - 1) / 8 < F / 8 + 23).
  { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF. lia. }
  rewrite E1 in Hs.
  pose proof (Z.div_mod (2147450880 + (F / 8 + 20)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (2147450880 + (F / 8 + 20)) 8 ltac:(lia)) as M1.
  pose proof (Z.mul_div_le (2147450880 + (F + 0xa0 + (L0 + 1) - 1) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  replace s with (2147450880 + F / 8 + (s - (2147450880 + F / 8))) by lia.
  rewrite (Hfsh (s - (2147450880 + F / 8)) ltac:(lia)). discriminate. }
Qed.
End b.

Print Assumptions hw7b_memcpy_at.
Print Assumptions hw7b_strlen_at.
Print Assumptions hw7b_strok_cstr.
Print Assumptions hw7b_strok_ch.
