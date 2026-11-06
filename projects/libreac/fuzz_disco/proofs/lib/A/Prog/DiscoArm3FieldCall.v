(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module names changed; 294 of its 331 lines of code are new or changed and 951 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnShared SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* the snprintf contract's premises are over the written part w = sn_len (n - 1) T <= n: the (d, n) facts give them *)
Lemma snp_zd_sub : forall x K sp d n w, w <= n ->
  Forall (zdisjoint x) (snp_out K sp d n) -> Forall (zdisjoint x) (snp_out K sp d w).
Proof.
  intros x K sp d n w Hw H. unfold snp_out in *.
  apply Forall_cons_iff in H as [H1 H]. apply Forall_cons_iff in H as [H2 _].
  apply Forall_cons; [exact H1|]. apply Forall_cons; [|apply Forall_nil].
  unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.
Lemma snp_pw_sub : forall K sp d n w, w <= n ->
  pairwise zdisjoint (snp_out K sp d n) -> pairwise zdisjoint (snp_out K sp d w).
Proof.
  intros K sp d n w Hw H. unfold snp_out in *. cbn [pairwise] in H |- *. destruct H as (H & _).
  split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons_iff in H as [H _]. apply Forall_cons; [|apply Forall_nil].
  unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.
Lemma snp_fmt_sub : forall rd K sp d n w f fmt, w <= n ->
  fmt_at rd (snp_out K sp d n) f fmt -> fmt_at rd (snp_out K sp d w) f fmt.
Proof.
  intros rd K sp d n w f fmt Hw (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact (snp_zd_sub _ _ _ _ _ _ Hw H3) | exact H4].
Qed.
Lemma snp_args_sub : forall rd K sp d n w ws args, w <= n ->
  pf_args_asan rd (snp_out K sp d n) ws args -> pf_args_asan rd (snp_out K sp d w) ws args.
Proof.
  intros rd K sp d n w ws args Hw. revert ws. induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
  destruct ws as [|w0 ws]; [destruct H|]. cbn [pf_args_asan] in H |- *. destruct H as [Ha Hr].
  split; [|exact (IH ws Hr)].
  destruct a; cbn [pf_arg_asan] in Ha |- *; try exact Ha.
  destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact (snp_zd_sub _ _ _ _ _ _ Hw A6) | exact A7].
Qed.
Lemma snp_hull_sub : forall rd d n w, 1 <= w <= n -> shadow_hull_vis rd d n -> shadow_hull_vis rd d w.
Proof.
  intros rd d n w Hw H s Hs. apply H. split; [lia|].
  assert (Hm : shadow_addr (d + w - 1) / 8 <= shadow_addr (d + n - 1) / 8).
  { apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Hypothesis TJTOK : tjtok_is_spec B.

Definition snp_ctx (W : world SEGS) (mem : word -> option byte) (sp d n : Z) : Prop :=
  SnprintfDef.consts_view SEGS W mem snp_cr /\
  Forall (fun r => Forall (zdisjoint r) (snp_out SNPRINTF_STK sp d n)) snp_cr /\
  (exists cval, rdword (aview SEGS (w_H W) mem) AE2k.FF_got_canary = Some AE2k.FF_canary /\
     rdword (aview SEGS (w_H W) mem) AE2k.FF_canary = Some cval) /\
  Forall (zdisjoint (AE2k.FF_got_canary, 8)) (snp_out SNPRINTF_STK sp d n) /\
  Forall (zdisjoint (AE2k.FF_canary, 8)) (snp_out SNPRINTF_STK sp d n) /\
  off_img d n.

Lemma snp_ctx_ok : forall W mem sp d n,
  (forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a) ->
  (forall a, Exists (in_zr a) snp_cr ->
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (exists cval, rdword (aview SEGS (w_H W) mem) AE2k.FF_got_canary = Some AE2k.FF_canary /\
     rdword (aview SEGS (w_H W) mem) AE2k.FF_canary = Some cval) ->
  off_img (sp - SNPRINTF_STK) SNPRINTF_STK -> off_img d n ->
  snp_ctx W mem sp d n.
Proof.
  intros W mem sp d n SNPRO SNPUN HA HG Hs Hd. pose proof Hd as Hd0. unfold off_img, IMG_LO, IMG_TOP in Hs, Hd.
  split.
  { intros a Ha. destruct (SNPUN a Ha) as [H1 H2]. exact (HA a (SNPRO a Ha) H1 H2). }
  split.
  { unfold snp_cr, snp_out. repeat (apply Forall_cons || apply Forall_nil); unfold zdisjoint; cbn [fst snd]; lia. }
  split; [exact HG|].
  unfold snp_out, AE2k.FF_got_canary, AE2k.FF_canary.
  split; [|split; [|exact Hd0]]; repeat (apply Forall_cons || apply Forall_nil); unfold zdisjoint; cbn [fst snd]; lia.
Qed.

Lemma mc_cv_ok : forall W mem,
  (forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a) ->
  (forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  ConstsViewDef.consts_view SEGS McConsts.MC_CONSTS_LO McConsts.MC_CONSTS_HI W mem.
Proof. intros W mem MCRO MCUN HA a Ha. destruct (MCUN a Ha) as [H1 H2]. exact (HA a (MCRO a Ha) H1 H2). Qed.

Lemma aj_snprintf_at : forall (fq : YK11.FPState) W regs memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
  d n f (fmt : list Z) (ps : list pf_piece) (xs ws : list Z) (args : list pf_arg) (T : list Z) (o : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SNPRINTF_STK - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regs 1) ->
  snp_ctx W memT (spZ regs) d n ->
  fmt_at (aview SEGS (w_H W) memT) (snp_out SNPRINTF_STK (spZ regs) d n) f fmt ->
  pf_parse fmt = Some ps -> Forall pf_disco_piece ps ->
  va_words regs (aview SEGS (w_H W) memT) (spZ regs) xs ws ->
  spZ regs + 8 * Z.of_nat (length xs) <= sp0 ->
  Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out SNPRINTF_STK (spZ regs) d n) ->
  pf_args_asan (aview SEGS (w_H W) memT) (snp_out SNPRINTF_STK (spZ regs) d n) ws args ->
  pf_text ps args = Some T ->
  1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + n <= 2 ^ 63 ->
  pairwise zdisjoint (snp_out SNPRINTF_STK (spZ regs) d n) ->
  (forall a, d <= a < d + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (spZ regs - SNPRINTF_STK <= a < spZ regs)) ->
  amem_range d (n + 8) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n ->
  disco_fmt_lo <= f -> f + Z.of_nat (length fmt) + 1 <= disco_fmt_hi -> fmt <> [] ->
  SnFF.pf_args_slack ws args -> SnFF.pf_args_amem ws args ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (SIGMA DS___interceptor_trampoline_snprintf) regs memT mdc)
    (fun W2 c2 => W2 = W /\ exists (fx2 : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst (fx := fx2) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       lib.Lib.FP.frm0 (@YK11.fp_csr fx2) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regs regs2 /\ same_but_materialized mdc md2 /\
       getr regs2 10 = w64 (Z.of_nat (length T)) /\
       (forall i, 0 <= i < Z.min (Z.of_nat (length T)) (n - 1) ->
          aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) T 0)) /\
       aview SEGS (w_H W) mem2 (d + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) ->
          ~ (spZ regs - SNPRINTF_STK <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros fq W regs memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt ps xs ws args T o
    HJ Ha0 Ha1 Ha2 Hsp Hal Hneg Hbud Hgp Htp Hraw Hctx Hfmt Hps Hpd Hva Hxs Hxd Hargs HT Hn HTl Hd0 Hdn Hpw
    Hdest Hamr Hra_d Hhull Hflo Hfhi Hfne Hsl Hamm Hfrm Haro.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (ESTACK = 4096) as Hes by reflexivity.
  assert (SNPRINTF_STK = 11776) as Hsn by reflexivity.
  pose proof asan_consts as (C1 & _).
  assert (HPRE : ecall_pre SEGS B lyc Sc W regs memT mdc).
  { eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regs o); try eassumption. lia. }
  assert (HSTK : ly_stk_lo lyc + SNPRINTF_STK <= spZ regs) by (rewrite Eslo, Hsp; lia).
  assert (HPR : forall a, spZ regs - SNPRINTF_STK <= a < spZ regs -> apresent (w_H W) memT a).
  { intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
  destruct Hctx as (HCV & HCRD & (cval & HG1 & HG2) & HGD1 & HGD2 & Himg).
  set (w := SnShared.sn_len (n - 1) T).
  assert (Hw : w = Z.min (Z.of_nat (length T)) (n - 1) + 1).
  { unfold w, SnShared.sn_len, SnShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
  assert (Hw1 : 1 <= w <= n) by (pose proof (Z.le_min_r (Z.of_nat (length T)) (n - 1)); lia).
  assert (HDEST : dest_ok SEGS B lyc Sc W regs memT d w).
  { intros a Ha. destruct (Hdest a ltac:(lia)) as [Hwb Hns].
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hwb) as [Hp Hno].
    split; [apply apresent_writable; exact Hp|]. split; [exact Hno | lia]. }
  assert (HCRD' : Forall (fun r => Forall (zdisjoint r) (snp_out SNPRINTF_STK (spZ regs) d w)) snp_cr).
  { eapply Forall_impl; [|exact HCRD]. intros r Hr. exact (snp_zd_sub _ _ _ _ _ _ (proj2 Hw1) Hr). }
  pose proof (snp_zd_sub _ _ _ _ _ _ (proj2 Hw1) HGD1) as HGD1'.
  pose proof (snp_zd_sub _ _ _ _ _ _ (proj2 Hw1) HGD2) as HGD2'.
  pose proof (snp_zd_sub _ _ _ _ _ _ (proj2 Hw1) Hxd) as Hxd'.
  assert (Hxs47 : spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47) by lia.
  assert (HFF : SnFF.FF_disco disco_fmt_lo disco_fmt_hi (aview SEGS (w_H W) memT)
    (snp_out SNPRINTF_STK (spZ regs) d w) f ws T).
  { exists fmt, ps, args.
    split; [exact (snp_fmt_sub _ _ _ _ _ _ _ _ (proj2 Hw1) Hfmt)|].
    split; [exact Hps|]. split; [exact Hpd|].
    split; [exact (snp_args_sub _ _ _ _ _ _ _ _ (proj2 Hw1) Hargs)|].
    split; [exact HT|]. split; [exact (SnShared.pf_disco_prec_pos ps args Hpd)|].
    split; [exact Hflo|]. split; [exact Hfhi|]. split; [exact Hsl|]. split; [exact Hfne | exact Hamm]. }
  pose proof (snp_pw_sub _ _ _ _ _ (proj2 Hw1) Hpw) as Hpw'.
  assert (Hamr' : amem_range d (w + 8)) by (unfold amem_range in *; lia).
  assert (Hra_d' : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d w) by (intros x Hx; apply Hra_d; lia).
  pose proof (snp_hull_sub _ d n w Hw1 Hhull) as Hhull'.
  assert (Himg' : zdisjoint (d, w) (YImgTop.IMG_LO, YImgTop.IMG_TOP - YImgTop.IMG_LO))
    by (unfold off_img in Himg; unfold zdisjoint; cbn [fst snd]; lia).
  assert (Hdw : d + w <= 2 ^ 63) by lia.
  eapply SRr_mono.
  { exact (ASNPRINTF fq lyc Sc W regs memT mdc d n f xs ws T cval HPRE Haro HSTK HPR Ha0 Ha1 Ha2
             HCV snp_cr_bounds HCRD' HG1 HG2 ltac:(unfold AE2k.FF_got_canary; lia) ltac:(unfold AE2k.FF_got_canary; lia)
             ltac:(unfold AE2k.FF_canary; lia) ltac:(unfold AE2k.FF_canary; lia) HGD1' HGD2'
             Hva Hxs47 Hxd' HFF Hn HTl Hd0 Hdw Hpw' HDEST Hamr' Hra_d' Hhull' Himg' Hfrm). }
  cbv beta. intros W2 c2 _ (-> & fx2 & regs2 & mem2 & md2 & -> & _ & Hfrm2 & HAR2 & HP & Hsame & Hres & Hwr & Hfr & Hpres2).
  fold w in Hwr, Hfr.
  assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) ->
    ~ (spZ regs - SNPRINTF_STK <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a).
  { intros a Ha H1 H2. apply Hfr; [exact Ha | intros H3; apply H1; lia | exact H2]. }
  assert (Hwr' : forall i, 0 <= i < Z.min (Z.of_nat (length T)) (n - 1) ->
    aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) T 0)).
  { intros i Hi. rewrite (Hwr i ltac:(lia)). f_equal. unfold SnShared.sn_bytes.
    rewrite app_nth1 by (rewrite length_firstn; lia).
    rewrite <- (firstn_skipn (Z.to_nat (n - 1)) T) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
  assert (Hnul' : aview SEGS (w_H W) mem2 (d + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0).
  { rewrite (Hwr (Z.min (Z.of_nat (length T)) (n - 1)) ltac:(pose proof (Z.le_min_r (Z.of_nat (length T)) (n - 1)); lia)).
    f_equal. unfold SnShared.sn_bytes. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Z.to_nat (Z.min (Z.of_nat (length T)) (n - 1)) - Nat.min (Z.to_nat (n - 1)) (length T))%nat with 0%nat by lia.
    reflexivity. }
  split; [reflexivity|]. exists fx2, regs2, mem2, md2.
  split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Hfrm2|].
  split.
  { eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
      (fun a => (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) \/ (spZ regs - SNPRINTF_STK <= a < spZ regs)) Sc own HJ).
    - intros a Ha Hna. apply (Hfr' a Ha); intros H'; apply Hna; [left | right]; exact H'.
    - exact Hpres2.
    - exact Hsame.
    - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a ltac:(lia))) | left; rewrite Hsp in Ha; lia].
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Hwr'|].
  split; [exact Hnul'|]. split; [exact Hfr' | exact Hpres2].
Qed.

Ltac fc_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Lemma afn_pre_fp0_at : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regs STK1 (o : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  afn_pre SEGS B STK1 lyc Sc W (regupd regs 8 (Z_to_bv 64 0)) memc mdc [].
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regs STK1 o HJ Hsp Hal Hneg Hstk1 Hbud Hraw Hra4 Hgp Htp.
  pose proof asan_consts as (C1 & _).
  eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k (regupd regs 8 (Z_to_bv 64 0)) STK1 o [] HJ).
  - unfold spZ. rewrite getr_other by fc_bvne. exact Hsp.
  - exact Hal.
  - exact Hneg.
  - exact Hstk1.
  - exact Hbud.
  - rewrite getr_other by fc_bvne. exact Hraw.
  - unfold raZ. rewrite getr_other by fc_bvne. exact Hra4.
  - rewrite getr_other by fc_bvne. exact Hgp.
  - rewrite getr_other by fc_bvne. exact Htp.
  - left. split; [|reflexivity]. left. unfold s0Z. rewrite getr_same by fc_bvne.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Lemma aj_jtok_at : forall (fq : YK11.FPState) W regs memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z)
  (v x kind vk vp vn : Z) (T slack P : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> TJTOK_IS_STK - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  ConstsViewDef.consts_view SEGS McConsts.MC_CONSTS_LO McConsts.MC_CONSTS_HI W memc ->
  getr regs 10 = w64 v -> getr regs 11 = Z_to_bv 64 kind -> getr regs 12 = w64 x ->
  -2 ^ 31 <= kind < 2 ^ 31 -> -2 ^ 31 <= vk < 2 ^ 31 ->
  0 < v -> v mod 8 = 0 -> v + 20 <= 2 ^ 63 ->
  val_mem SEGS (rd W memc) v 8 vp -> val_mem SEGS (rd W memc) (v + 8) 8 vn ->
  val_mem SEGS (rd W memc) (v + 16) 4 (vk mod 2 ^ 32) ->
  0 <= vp < 2 ^ 64 -> 0 <= vn < 2 ^ 64 ->
  amem_range v 20 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) v 20 ->
  (v + 20 <= spZ regs - TJTOK_IS_STK \/ spZ regs <= v) ->
  ~ In (Z_to_bv 8 0) T ->
  garr8 SEGS (rd W memc) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
  (- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < x -> x + Z.of_nat (length T + 1 + length slack) <= 2 ^ 63 ->
  Z.of_nat (length T) + 1 < 2 ^ 32 ->
  amem_range x (Z.of_nat (length T + 1)) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x (Z.of_nat (length T + 1)) ->
  shadow_hull_vis (aview SEGS (w_H W) memc) x (Z.of_nat (length T + 1)) ->
  (x + Z.of_nat (length T + 1 + length slack) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= x) ->
  (vk = kind -> vn = Z.of_nat (length T) ->
     length P = length T /\ garr8 SEGS (rd W memc) vp (map bv_unsigned P) /\
     0 <= vp /\ vp + Z.of_nat (length T) <= 2 ^ 63 /\
     amem_range vp (Z.of_nat (length T)) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF vp (Z.of_nat (length T)) /\
     (0 < Z.of_nat (length T) -> shadow_hull_vis (aview SEGS (w_H W) memc) vp (Z.of_nat (length T))) /\
     (vp + Z.of_nat (length T) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= vp)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_jtok_is) regs memc mdc)
    (fun W2 c2 => exists fq2 ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst (fx := fq2) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       (@YK11.fp_csr fq2 = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq2)) 5) 7 = 0) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k /\
       ajournal SEGS B TJTOK_IS_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 0 /\
       aregs_preserved regs regs2 /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       ((jtok_is_c.jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs2 10 = w64 1) \/
        (~ jtok_is_c.jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs2 10 = w64 0))).
Proof.
  intros fq W regs memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k o v x kind vk vp vn T slack P
    HJ Hsp Hal Hneg Hbud Hgp Htp Hraw Hra4 HRO HROM H10 H11 H12 Hk Hvk Hv0 Hv8 Hv63 Mvp Mvn Mvk Rvp Rvn
    AMv RAv SHv DSv NT GT SL Hx0 Hx63 HTl AMx RAx SHx DSx HP.
  assert (TJTOK_IS_STK = 8240) as Htk by reflexivity.
  pose proof (afn_pre_fp0_at STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regs TJTOK_IS_STK o HJ Hsp Hal Hneg
    ltac:(lia) Hbud Hraw Hra4 Hgp Htp) as HPRE.
  eapply SRr_mono.
  { exact (TJTOK fq lyc Sc W regs memc mdc [] v x kind vk vp vn T slack P HPRE HRO HROM H10 H11 H12 Hk Hvk Hv0 Hv8 Hv63
             Mvp Mvn Mvk Rvp Rvn AMv RAv SHv DSv NT GT SL Hx0 Hx63 HTl AMx RAx SHx DSx HP). }
  cbv beta. intros W2 c2 _ Hpost. unfold tjtok_is_post, apost_base in Hpost.
  destruct Hpost as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & _ & Hcsr2 & HJ1 & HPr & Hperm & Hfr & Hres).
  exists fq2, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hcsr2|].
  split.
  { pose proof (ajournal_sub SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k TJTOK_IS_STK
      (spZ regs) [] [] ly2 S2 W2 mem2 md2 0 HJ HJ1 ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ4.
    cbn [app] in HJ4. rewrite Z.add_0_r in HJ4. exact HJ4. }
  split; [exact HJ1|]. split; [exact HPr|]. split; [exact Hperm|]. split; [exact Hfr | exact Hres].
Qed.

End h.
End f.
End d.
