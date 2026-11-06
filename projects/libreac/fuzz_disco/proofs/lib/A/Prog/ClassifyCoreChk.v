(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 1355 of its 1430 lines of code are new or changed and 3265 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacPortsParse.v, with its module paths and module names changed; 69 of its 100 lines of code are new or changed and 1399 lines of the source are left out. *)
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
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlChecksumVerify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcModel disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma cchk_map_bytes : forall l : list byte, map (Z_to_bv 8) (cls_bytes l) = l.
Proof.
intros l. unfold cls_bytes. rewrite map_map.
induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply Z_to_bv_bv_unsigned.
Qed.

Lemma cchk_fsum : forall FB : list byte, length FB = 50%nat ->
RcModel.blocksum (map (Z_to_bv 8) (cls_bytes (skipn 18 FB))) = disco_classify_c.fsum FB.
Proof.
intros FB HL. rewrite cchk_map_bytes. unfold disco_classify_c.fsum, CtrlParsed.fld.
rewrite firstn_all2; [reflexivity|]. rewrite length_skipn. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma tchk_need_of_spec : treac_ctrl_checksum_verify_spec B -> tchk_need B.
Proof.
intros SPEC. unfold tchk_need.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch p FB
HJ HROD Hra Hra4 Hgp Htp H10 Hch Hal Hwin Hsp HLFB Hp0 Hp47 Ham Hoff Hband Hsep Hpres HRA HSHV Hg.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hjpres & (Hsp0al & Hstk0 & _) & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HN : CLS_CHK_NEED = 16 + ESTACK) by reflexivity.
assert (HPRE : afn_pre SEGS B REAC_CTRL_CHECKSUM_VERIFY_STK lyc Sc W regs memc mdc ch).
{ eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    REAC_CTRL_CHECKSUM_VERIFY_STK (spZ regs - sp0) ch HJ);
  unfold REAC_CTRL_CHECKSUM_VERIFY_STK; try assumption; try lia;
  rewrite Zminus_mod, Hal, Hsp0al; reflexivity. }
assert (HG : garr8 SEGS (mrestrict (w_H W) memc) (p + 18) (cls_bytes (skipn 18 FB))).
{ rewrite <- (firstn_skipn 18 FB) in Hg. unfold cls_bytes in Hg. rewrite map_app in Hg.
  apply garr8_app in Hg as [_ Hg2]. rewrite length_map, length_firstn in Hg2.
  replace (Z.of_nat (Nat.min 18 (length FB))) with 18 in Hg2 by (rewrite HLFB; reflexivity). exact Hg2. }
assert (HGL : length (cls_bytes (skipn 18 FB)) = 32%nat)
by (unfold cls_bytes; rewrite length_map, length_skipn, HLFB; reflexivity).
eapply SRr_mono.
{ apply (SPEC fq lyc Sc W regs memc mdc ch p (cls_bytes (skipn 18 FB)) HPRE H10); [|exact HG | exact HGL].
  unfold REAC_CTRL_CHECKSUM_VERIFY_STK. rewrite HN, Hes in Hsep.
  refine (conj Hp0 (conj Hp47 (conj Ham (conj Hoff (conj Hband (conj _ (conj Hpres (conj HRA HSHV)))))))).
  destruct Hsep as [Hs|Hs]; [left; exact Hs | right; lia]. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfx & Hcs & HJ2 & HP2 & (-> & -> & -> & Ha0)).
assert (HJo : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k).
{ pose proof (ajournal_sub SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    REAC_CTRL_CHECKSUM_VERIFY_STK (spZ regs) [] [] lyc Sc W mem2 md2 0 HJ HJ2) as HX.
  cbn [app] in HX. rewrite Z.add_0_r in HX. apply HX.
  - unfold REAC_CTRL_CHECKSUM_VERIFY_STK. rewrite HN, Hes in Hwin. lia.
  - exact Hsp.
  - intros a (r & Hr & _). destruct Hr. }
assert (HK : acall_kept SEGS B lyc Sc W memc W mem2 (spZ regs - REAC_CTRL_CHECKSUM_VERIFY_STK) (spZ regs) (fun _ => False)).
{ apply (acall_kept_of_journal SEGS B pa_segs_low REAC_CTRL_CHECKSUM_VERIFY_STK (spZ regs) [] [] lyc Sc W memc mdc
    lyc Sc W mem2 md2 0 (fun _ => False) HJ2 HAR).
  - intros a (r & Hr & _). destruct Hr.
  - intros b m i Hb _ _. exact Hb.
  - apply sink_closed_nil. }
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HJo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hopres & _).
exists fx', lyc, Sc, regs2, mem2, md2.
split; [exact Hc|]. split; [exact Hfx|]. split; [exact Hcs|].
split; [exact HJo|]. split; [exact HP2|]. split; [reflexivity|].
split; [apply Permutation_refl|].
split; [rewrite Ha0, cchk_fsum by exact HLFB; reflexivity|].
unfold REAC_CTRL_CHECKSUM_VERIFY_STK in *. rewrite HN, Hes in *.
split; [intros a Ha Hw _; apply K1; [exact Ha | lia]|].
split; [intros b m i Hb Hi _; exact (K2 b m i Hb Hi (fun x => x))|].
split; [exact K3|].
split; [intros cid pos a Hin Hr _; exact (K4 cid pos a Hin Hr (fun x => x))|].
split; [intros a Ha Hw; apply K5; [exact Ha | lia]|].
intros a Ha. apply Hopres. lia.
Qed.

End h.
End f.
End d.
