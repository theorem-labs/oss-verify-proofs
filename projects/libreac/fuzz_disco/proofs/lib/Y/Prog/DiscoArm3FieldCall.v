(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 759 of its 797 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntExit.v, with its module paths and module names changed; 325 of its 376 lines of code are new or changed and 746 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntryShapes DiscoArm3 DiscoYEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3JtokSpec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnShared SnSx SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma fc_snl_eq : forall n (T : list Z), 1 <= n ->
  SnShared.sn_len (n - 1) T = Z.min (Z.of_nat (length T)) (n - 1) + 1.
Proof.
  intros n T Hn. unfold SnShared.sn_len, SnShared.sn_bytes. rewrite length_app, length_firstn. cbn [length].
  rewrite Nat2Z.inj_add, Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

Lemma fc_snb_min : forall n (T : list Z), 1 <= n ->
  Z.to_nat (Z.min (Z.of_nat (length T)) (n - 1)) = length (firstn (Z.to_nat (n - 1)) T).
Proof.
  intros n T Hn. rewrite length_firstn. apply Nat2Z.inj.
  rewrite Z2Nat.id by lia. rewrite Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

Lemma fc_snb_lt : forall n (T : list Z) i, 1 <= n -> 0 <= i < Z.min (Z.of_nat (length T)) (n - 1) ->
  nth (Z.to_nat i) (SnShared.sn_bytes (n - 1) T) 0 = nth (Z.to_nat i) T 0.
Proof.
  intros n T i Hn Hi. unfold SnShared.sn_bytes.
  assert (Hl : (Z.to_nat i < length (firstn (Z.to_nat (n - 1)) T))%nat) by (rewrite <- (fc_snb_min n T Hn); lia).
  rewrite app_nth1 by exact Hl.
  rewrite <- (firstn_skipn (Z.to_nat (n - 1)) T) at 2. rewrite app_nth1 by exact Hl. reflexivity.
Qed.

Lemma fc_snb_end : forall n (T : list Z), 1 <= n ->
  nth (Z.to_nat (Z.min (Z.of_nat (length T)) (n - 1))) (SnShared.sn_bytes (n - 1) T) 0 = 0.
Proof.
  intros n T Hn. rewrite (fc_snb_min n T Hn). unfold SnShared.sn_bytes.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma fc_snp_w : forall r K sp d n w, w <= n ->
  Forall (zdisjoint r) (SnShared.snp_out K sp d n) -> Forall (zdisjoint r) (SnShared.snp_out K sp d w).
Proof.
  intros r K sp d n w Hw H. unfold SnShared.snp_out in H. unfold SnShared.snp_out.
  apply Forall_cons_iff in H as [H1 H]. apply Forall_cons_iff in H as [H2 _].
  apply Forall_cons; [exact H1|]. apply Forall_cons; [|apply Forall_nil].
  unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.

Lemma fc_snp_pw : forall K sp d n w, w <= n ->
  pairwise zdisjoint (SnShared.snp_out K sp d n) -> pairwise zdisjoint (SnShared.snp_out K sp d w).
Proof.
  intros K sp d n w Hw H. unfold SnShared.snp_out in H. unfold SnShared.snp_out. cbn [pairwise] in H |- *.
  destruct H as (H1 & _ & _). apply Forall_cons_iff in H1 as [H1 _].
  split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]].
  unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.

Lemma fc_slack_of_amem : forall rd rs ws args, SnShared.pf_args_asan rd rs ws args -> SnFF.pf_args_amem ws args ->
  SnFF.pf_args_slack ws args.
Proof.
  intros rd rs ws args. revert ws. induction args as [|a args IH]; intros ws Ha Hm.
  - destruct ws; exact I.
  - destruct ws as [|w ws]; [exact (False_ind _ Ha)|]. destruct Ha as [_ Ha].
    destruct a as [v | u | s]; cbn [SnFF.pf_args_amem SnFF.pf_args_slack] in Hm |- *.
    + exact (IH ws Ha Hm).
    + exact (IH ws Ha Hm).
    + destruct Hm as [Hm1 Hm2]. split; [|exact (IH ws Ha Hm2)].
      pose proof (SnFF.str_end_ge w s) as Hse.
      exact (SnSx.amem_range_le w (SnShared.str_end w s - w) (Z.of_nat (length s) + 8) ltac:(lia) Hm1).
Qed.

Lemma fc_snp_ff : forall flo fhi rd K sp d n w f fmt ps ws args T, w <= n ->
  SnShared.fmt_at rd (SnShared.snp_out K sp d n) f fmt -> pf_parse fmt = Some ps -> Forall pf_disco_piece ps ->
  SnShared.pf_args_asan rd (SnShared.snp_out K sp d n) ws args -> pf_text ps args = Some T ->
  flo <= f -> f + Z.of_nat (length fmt) + 1 <= fhi -> fmt <> [] -> SnFF.pf_args_amem ws args ->
  SnFF.FF_disco flo fhi rd (SnShared.snp_out K sp d w) f ws T.
Proof.
  intros flo fhi rd K sp d n w f fmt ps ws args T Hw Hf Hp Hd Ha Ht Hlo Hhi Hne Ham.
  pose proof (SnFF.FF_disco_mono flo fhi) as M. unfold SnShared.ff_mono in M.
  apply (M rd (SnShared.snp_out K sp d n)).
  - unfold SnFF.FF_disco. exists fmt, ps, args.
    split; [exact Hf|]. split; [exact Hp|]. split; [exact Hd|]. split; [exact Ha|].
    split; [exact Ht|]. split; [exact (SnShared.pf_disco_prec_pos ps args Hd)|].
    split; [exact Hlo|]. split; [exact Hhi|]. split; [exact (fc_slack_of_amem _ _ ws args Ha Ham)|].
    split; [exact Hne | exact Ham].
  - intros r' Hr'. unfold SnShared.snp_out in Hr' |- *. cbn [In] in Hr'.
    destruct Hr' as [<- | [<- | []]].
    + exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
    + exists (d, n). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi FF_got_canary FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Hypothesis TJTOK : tjtok_is_spec B.

Definition snp_ctx (W : world SEGS) (mem : word -> option byte) (sp d n : Z) : Prop :=
  SnprintfDef.consts_view SEGS W mem snp_cr /\
  Forall (fun r => Forall (zdisjoint r) (SnShared.snp_out SNPRINTF_STK sp d n)) snp_cr /\
  (exists cval, rdword (aview SEGS (w_H W) mem) FF_got_canary = Some FF_canary /\
     rdword (aview SEGS (w_H W) mem) FF_canary = Some cval) /\
  Forall (zdisjoint (FF_got_canary, 8)) (SnShared.snp_out SNPRINTF_STK sp d n) /\
  Forall (zdisjoint (FF_canary, 8)) (SnShared.snp_out SNPRINTF_STK sp d n) /\
  off_img d n.

Lemma snp_ctx_ok : forall W mem sp d n,
  (forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a) ->
  (forall a, Exists (in_zr a) snp_cr ->
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (exists cval, rdword (aview SEGS (w_H W) mem) FF_got_canary = Some FF_canary /\
     rdword (aview SEGS (w_H W) mem) FF_canary = Some cval) ->
  off_img (sp - SNPRINTF_STK) SNPRINTF_STK -> off_img d n ->
  snp_ctx W mem sp d n.
Proof.
  intros W mem sp d n SNPRO SNPUN HA HG Hs Hd. pose proof Hd as Hd0. unfold off_img, IMG_LO, IMG_TOP in Hs, Hd.
  split.
  { intros a Ha. destruct (SNPUN a Ha) as [H1 H2]. exact (HA a (SNPRO a Ha) H1 H2). }
  split.
  { unfold snp_cr, SnShared.snp_out. repeat (apply Forall_cons || apply Forall_nil); unfold zdisjoint; cbn [fst snd]; lia. }
  split; [exact HG|].
  unfold SnShared.snp_out, FF_got_canary, FF_canary.
  split; [|split; [|exact Hd0]]; repeat (apply Forall_cons || apply Forall_nil); unfold zdisjoint; cbn [fst snd]; lia.
Qed.

Lemma mc_cv_ok : forall W mem,
  (forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a) ->
  (forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  ConstsViewDef.consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem.
Proof. intros W mem MCRO MCUN HA a Ha. destruct (MCUN a Ha) as [H1 H2]. exact (HA a (MCRO a Ha) H1 H2). Qed.

Lemma snp_can_of : forall (K : asink_syms), asink_img_laws SEGS B K ->
  ak_can_got K = FF_got_canary -> ak_canary K = FF_canary ->
  forall ly S (W : world SEGS) m md cval, AR SEGS B ly S W m md ->
  val_mem SEGS (rd W m) FF_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
  exists cv, rdword (aview SEGS (w_H W) m) FF_got_canary = Some FF_canary /\
    rdword (aview SEGS (w_H W) m) FF_canary = Some cv.
Proof.
  intros K AIL KG KC ly S W m md cval HAR Hv Hc.
  assert (HG : val_mem SEGS (rd W m) (ak_can_got K) 8 (ak_canary K)) by (eapply acan_got_of_AR; eassumption).
  rewrite KG, KC in HG.
  exists cval. split.
  - apply rdword_of_val_mem; [exact HG | unfold FF_canary; lia].
  - apply rdword_of_val_mem; [exact Hv | exact Hc].
Qed.

Lemma aj_snprintf_at : forall (fq : YK11.FPState) W regs memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
  d n f (fmt : list Z) (ps : list pf_piece) (xs ws : list Z) (args : list pf_arg) (T : list Z) (o : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SNPRINTF_STK - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regs 1) ->
  snp_ctx W memT (spZ regs) d n ->
  SnShared.fmt_at (aview SEGS (w_H W) memT) (SnShared.snp_out SNPRINTF_STK (spZ regs) d n) f fmt ->
  pf_parse fmt = Some ps -> Forall pf_disco_piece ps ->
  disco_fmt_lo <= f -> f + Z.of_nat (length fmt) + 1 <= disco_fmt_hi -> fmt <> [] ->
  SnShared.va_words regs (aview SEGS (w_H W) memT) (spZ regs) xs ws ->
  spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
  Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (SnShared.snp_out SNPRINTF_STK (spZ regs) d n) ->
  SnShared.pf_args_asan (aview SEGS (w_H W) memT) (SnShared.snp_out SNPRINTF_STK (spZ regs) d n) ws args ->
  SnFF.pf_args_amem ws args ->
  pf_text ps args = Some T ->
  1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + n <= 2 ^ 63 ->
  pairwise zdisjoint (SnShared.snp_out SNPRINTF_STK (spZ regs) d n) ->
  (forall a, d <= a < d + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (spZ regs - SNPRINTF_STK <= a < spZ regs)) ->
  amem_range d (n + 8) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (SIGMA AS___interceptor_trampoline_snprintf) regs memT mdc)
    (fun W2 c2 => W2 = W /\ exists fq2 regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst (fx := fq2) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       lib.Lib.FP.frm0 (@YK11.fp_csr fq2) /\
       (forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@YK11.fp_regs fq2) r = Sem.reg_get (@YK11.fp_regs fq) r) /\
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
    HJ Hfrm Ha0 Ha1 Ha2 Hsp Hal Hneg Hbud Hgp Htp Hraw Hctx Hfmt Hps Hpd Hflo Hfhi Hne Hva Hxs Hxd Hargs Hamem HT
    Hn HTl Hd0 Hdn Hpw Hdest Hamr Hra_d Hhull Hrod.
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
  assert (HDEST : dest_ok SEGS B lyc Sc W regs memT d n).
  { intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno].
    split; [apply apresent_writable; exact Hp|]. split; [exact Hno | lia]. }
  destruct Hctx as (HCV & HCRD & (cval & HG1 & HG2) & HGD1 & HGD2 & Hoff).
  pose proof (fc_snl_eq n T ltac:(lia)) as Esl.
  assert (Hw : 1 <= SnShared.sn_len (n - 1) T <= n) by (rewrite Esl; lia).
  assert (HCRD' : Forall (fun r => Forall (zdisjoint r)
    (SnShared.snp_out SNPRINTF_STK (spZ regs) d (SnShared.sn_len (n - 1) T))) snp_cr).
  { apply Forall_forall. intros r Hr. apply (fc_snp_w r _ _ d n _ (proj2 Hw)).
    exact (proj1 (Forall_forall _ _) HCRD r Hr). }
  assert (HDEST' : dest_ok SEGS B lyc Sc W regs memT d (SnShared.sn_len (n - 1) T)).
  { intros a Ha. apply HDEST. lia. }
  assert (Hamr' : amem_range d (SnShared.sn_len (n - 1) T + 8))
    by exact (SnSx.amem_range_le d (SnShared.sn_len (n - 1) T + 8) (n + 8) ltac:(lia) Hamr).
  assert (Hra' : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d (SnShared.sn_len (n - 1) T)).
  { intros x Hx. apply Hra_d. lia. }
  assert (Hhull' : shadow_hull_vis (aview SEGS (w_H W) memT) d (SnShared.sn_len (n - 1) T)).
  { unfold shadow_hull_vis in *. intros s Hs. apply Hhull. unfold shadow_addr in *.
    assert (M1 : (d + SnShared.sn_len (n - 1) T - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : (SHADOW_OFF + (d + SnShared.sn_len (n - 1) T - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8)
      by (apply Z.div_le_mono; lia).
    lia. }
  assert (Hoff' : zdisjoint (d, SnShared.sn_len (n - 1) T) (YImgTop.IMG_LO, YImgTop.IMG_TOP - YImgTop.IMG_LO)).
  { unfold off_img in Hoff. unfold zdisjoint. cbn [fst snd]. lia. }
  eapply SRr_mono.
  { exact (ASNPRINTF fq lyc Sc W regs memT mdc d n f xs ws T cval HPRE Hrod HSTK HPR Ha0 Ha1 Ha2
             HCV snp_cr_bounds HCRD' HG1 HG2 ltac:(unfold FF_got_canary; lia) ltac:(unfold FF_got_canary; lia)
             ltac:(unfold FF_canary; lia) ltac:(unfold FF_canary; lia)
             (fc_snp_w _ _ _ d n _ (proj2 Hw) HGD1) (fc_snp_w _ _ _ d n _ (proj2 Hw) HGD2)
             Hva Hxs (fc_snp_w _ _ _ d n _ (proj2 Hw) Hxd)
             (fc_snp_ff _ _ _ _ _ d n _ f fmt ps ws args T (proj2 Hw) Hfmt Hps Hpd Hargs HT Hflo Hfhi Hne Hamem)
             Hn HTl Hd0 ltac:(lia) (fc_snp_pw _ _ d n _ (proj2 Hw) Hpw) HDEST' Hamr' Hra' Hhull' Hoff' Hfrm). }
  cbv beta.
  intros W2 c2 _ (-> & fq2 & regs2 & mem2 & md2 & -> & Hfpr & Hfrm2 & HAR2 & HP & Hsame & Hres & Hbytes & Hfr & Hpres2).
  assert (Heff : forall i, 0 <= i < Z.min (Z.of_nat (length T)) (n - 1) ->
    aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) T 0)).
  { intros i Hi. rewrite Hbytes by (rewrite Esl; lia). rewrite (fc_snb_lt n T i ltac:(lia) Hi). reflexivity. }
  assert (Hz : aview SEGS (w_H W) mem2 (d + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0).
  { rewrite Hbytes by (rewrite Esl; lia). rewrite (fc_snb_end n T ltac:(lia)). reflexivity. }
  assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) ->
    ~ (spZ regs - SNPRINTF_STK <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a).
  { intros a Ha H1 H2. apply Hfr; [exact Ha | rewrite Esl; lia | exact H2]. }
  split; [reflexivity|]. exists fq2, regs2, mem2, md2.
  split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Hfrm2|]. split; [exact Hfpr|].
  split.
  { eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
      (fun a => (d <= a <= d + Z.min (Z.of_nat (length T)) (n - 1)) \/ (spZ regs - SNPRINTF_STK <= a < spZ regs)) Sc own HJ).
    - intros a Ha Hna. apply (Hfr' a Ha); intros H'; apply Hna; [left | right]; exact H'.
    - exact Hpres2.
    - exact Hsame.
    - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a ltac:(lia))) | left; rewrite Hsp in Ha; lia].
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Heff|].
  split; [exact Hz|]. split; [exact Hfr' | exact Hpres2].
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
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> TJTOK_IS_STK - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  ConstsViewDef.consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc ->
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_jtok_is) regs memc mdc)
    (fun W2 c2 => exists fq2 ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst (fx := fq2) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       lib.Lib.FP.frm0 (@YK11.fp_csr fq2) /\
       (forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@YK11.fp_regs fq2) r = Sem.reg_get (@YK11.fp_regs fq) r) /\
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
    HJ Hfrm Hsp Hal Hneg Hbud Hgp Htp Hraw Hra4 HRO HROM H10 H11 H12 Hk Hvk Hv0 Hv8 Hv63 Mvp Mvn Mvk Rvp Rvn
    AMv RAv SHv DSv NT GT SL Hx0 Hx63 HTl AMx RAx SHx DSx HP.
  assert (TJTOK_IS_STK = 8240) as Htk by reflexivity.
  pose proof (afn_pre_fp0_at STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regs TJTOK_IS_STK o HJ Hsp Hal Hneg
    ltac:(lia) Hbud Hraw Hra4 Hgp Htp) as HPRE.
  eapply SRr_mono.
  { exact (TJTOK fq lyc Sc W regs memc mdc [] v x kind vk vp vn T slack P HPRE HRO HROM H10 H11 H12 Hk Hvk Hv0 Hv8 Hv63
             Mvp Mvn Mvk Rvp Rvn AMv RAv SHv DSv NT GT SL Hx0 Hx63 HTl AMx RAx SHx DSx HP). }
  cbv beta. intros W2 c2 _ Hpost. unfold tjtok_is_post, apost_base in Hpost.
  destruct Hpost as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfpr & Hcsr & HJ1 & HPr & Hperm & Hfr & Hres).
  exists fq2, ly2, S2, regs2, mem2, md2. split; [reflexivity|].
  split; [destruct Hcsr as [Hc | Hc]; [rewrite Hc; exact Hfrm | exact Hc]|].
  split; [exact Hfpr|].
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
