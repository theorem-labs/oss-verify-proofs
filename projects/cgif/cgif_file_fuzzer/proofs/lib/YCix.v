(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8a YChd YCjr YCj2 YCj0 YCjc YCje YCjm YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCis YCiu YCiv YCiw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section c.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Section d.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Definition wsc_scan (w h top left : Z) : Prop :=
(exists bot right c0, w = right - left + 1 /\ h = bot + 1 - top /\
0 <= top <= bot /\ bot < Hd /\ 0 <= left <= right /\ right < Wd /\ 0 <= c0 < Wd /\
PDp (top * Wd + c0) /\ (forall p, 0 * Wd <= p < top * Wd -> ~ PDp p) /\
(bot = top \/ exists c1, 0 <= c1 < Wd /\ PDp (bot * Wd + c1)) /\ (forall p, (bot + 1) * Wd <= p < (Hd - 1 + 1) * Wd -> ~ PDp p) /\
(exists y', top <= y' <= bot /\ PDp (y' * Wd + left)) /\ (forall i x', top <= i <= bot -> 0 <= x' < left -> ~ PDp (i * Wd + x')) /\
(exists y', top <= y' <= bot /\ PDp (y' * Wd + right)) /\ (forall i x', top <= i <= bot -> right < x' < Wd -> ~ PDp (i * Wd + x'))) \/
((w, h, top, left) = (1, 1, 0, 0) /\ (forall p, 0 * Wd <= p < Wd * Hd -> ~ PDp p)).
Definition wsc_postX : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' w h top left,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x25bc)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r ([2; 3; 4; 8; 9]%bv : list (bv 5)) -> getr regs' r = getr regs r) /\
getr regs' 21 = Z_to_bv 64 w /\ getr regs' 23 = Z_to_bv 64 h /\ getr regs' 22 = Z_to_bv 64 left /\ getr regs' 27 = Z_to_bv 64 Wd /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 152) 8 top /\
1 <= w /\ 0 <= left /\ left + w <= Wd /\ 1 <= h /\ 0 <= top /\ top + h <= Hd /\ wsc_scan w h top left.
Lemma fl_search_slowX : forall (regsE : bvmap 5 word) memE mdE,
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r ([2; 3; 4; 8; 9]%bv : list (bv 5)) -> getr regsE r = getr regs r) ->
getr regsE 29 = Z_to_bv 64 SB -> getr regsE 15 = Z_to_bv 64 g -> getr regsE 16 = Z_to_bv 64 cfp -> getr regsE 17 = Z_to_bv 64 bfp ->
getr regsE 26 = Z_to_bv 64 fimg -> getr regsE 24 = Z_to_bv 64 fimg ->
getr regsE 27 = Z_to_bv 64 bimg -> getr regsE 25 = Z_to_bv 64 bimg ->
getr regsE 10 = Z_to_bv 64 Wd -> getr regsE 18 = Z_to_bv 64 1 -> getr regsE 23 = Z_to_bv 64 1 ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 152) 8 0 -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1de4)) memE (seg_rom SEGS)) mdE) wsc_postX.
Proof.
intros regsE memE mdE HJE WK HKE E29r E15r E16r E17r E26r E24r E27r E25r E10r E18r E23r V152 V160.
pose proof HGEO as (RW & RH & HN & _).
eapply SRr_bind.
{ pose proof (fl_s1oX B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO (Z.to_nat Hd)) as S1O. unfold s1o_stmtX in S1O.
eapply (S1O 0 regsE memE mdE); [ rewrite Z2Nat.id by lia; lia | lia | exact HJE | exact WK | exact HKE | exact E29r | exact E15r | exact E16r | exact E17r
| rewrite E26r; f_equal; lia | rewrite E24r; f_equal; lia | rewrite E27r; f_equal; lia | rewrite E25r; f_equal; lia | exact E10r | exact E18r | exact E23r | exact V152 | exact V160 ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & pc5 & -> & HJ5 & WK5 & HK5 & Hexit).
destruct Hexit as [(-> & top & c0 & HtopR & Hc0 & HPDw & H115 & H185 & H245 & V1525 & V1605 & XN1) | (-> & H215 & H235 & H225 & H275 & V1525 & XNall)].
-
eapply SRr_bind.
{ eapply (fl_s2X B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO top regs5 mem5 md5);
[ exact HtopR | exact HJ5 | exact WK5 | exact HK5 | exact H115 | exact H185 | exact H245 | exact V1525 | exact V1605 ]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & bot1 & -> & HJ6 & WK6 & HK6 & HbotR & H246 & H136 & H186 & H266 & H146 & H156 & H116 & H176 & V1446 & V1526 & V1606 & XB2 & XN2).
eapply SRr_bind.
{ eapply (fl_s3X B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO c0 top bot1 regs6 mem6 md6);
[ exact Hc0 | lia | exact HbotR | exact HPDw | exact HJ6 | exact WK6 | exact HK6 | exact H246 | exact H136 | exact H186 | exact H266 | exact H146 | exact H156 | exact H116 | exact H176
| exact V1446 | exact V1526 | exact V1606 ]. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & left & -> & HJ7 & WK7 & HK7 & Hleft & H227 & H237 & H217 & H187 & H247 & H267 & V1447 & V1527 & V1607 & XT3 & XN3).
eapply SRr_mono.
{ eapply (fl_s4X B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO c0 top bot1 left regs7 mem7 md7);
[ exact Hleft | lia | lia | exact HbotR | exact HPDw | exact HJ7 | exact WK7 | exact HK7 | exact H227 | exact H237 | exact H217 | exact H187 | exact H247 | exact H267
| exact V1447 | exact V1527 | exact V1607 ]. }
cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & right & -> & HJ8 & WK8 & HK8 & Hright & H218 & H228 & H238 & H278 & V1528 & XT4 & XN4).
split; [reflexivity|]. exists regs8, mem8, md8, (right - left + 1), (bot1 - top), top, left.
split; [reflexivity|]. split; [exact HJ8|]. split; [exact WK8|]. split; [exact HK8|].
split; [exact H218|]. split; [exact H238|]. split; [exact H228|]. split; [exact H278|]. split; [exact V1528|].
do 6 (split; [lia|]).
left. exists (bot1 - 1), right, c0.
split; [reflexivity|]. split; [clear; lia|]. split; [clear - HtopR HbotR; lia|]. split; [clear - HbotR; lia|]. split; [clear - Hleft Hright Hc0; lia|]. split; [clear - Hright; lia|].
split; [exact Hc0|]. split; [exact HPDw|]. split; [exact XN1|]. split; [exact XB2|].
split; [replace (bot1 - 1 + 1) with bot1 by (clear; lia); exact XN2|].
destruct XT3 as (y3 & Hy3 & XT3). destruct XT4 as (y4 & Hy4 & XT4).
split; [exists y3; split; [clear - Hy3; lia | exact XT3]|].
split; [intros i x' Hi Hx'; apply XN3; [clear - Hi; lia | exact Hx']|].
split; [exists y4; split; [clear - Hy4; lia | exact XT4]|].
intros i x' Hi Hx'; apply XN4; [clear - Hi; lia | exact Hx'].
-
apply SRr_ret. split; [reflexivity|]. exists regs5, mem5, md5, 1, 1, 0, 0.
split; [reflexivity|]. split; [exact HJ5|]. split; [exact WK5|]. split; [exact HK5|].
split; [exact H215|]. split; [exact H235|]. split; [exact H225|]. split; [exact H275|]. split; [exact V1525|].
do 6 (split; [lia|]).
right. split; [reflexivity | exact XNall].
Qed.
End d.
End c.
End b.
End a.
