(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj2 ACj0 ACjc ACje ACjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACis ACiu ACiv ACiw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section c.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Section d.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd a176 a184 : Z) (sv2 sv4 : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HRES : 0 <= a176 < 2 ^ 64 /\ 0 <= a184 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 144) 8 a176 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 a184.
Hypothesis HFIMG : val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
Hypothesis HSAV : 0 <= sv2 < 2 ^ 64 /\ 0 <= sv4 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 96) 8 sv2 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 104) 8 sv4.
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
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x1f8c)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4 /\
getr regs' 26 = Z_to_bv 64 w /\ getr regs' 27 = Z_to_bv 64 top /\ getr regs' 23 = Z_to_bv 64 left /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 h /\
1 <= w /\ 0 <= left /\ left + w <= Wd /\ 1 <= h /\ 0 <= top /\ top + h <= Hd /\ wsc_scan w h top left /\
((getr regs' 10 = Z_to_bv 64 a184 /\ getr regs' 11 = Z_to_bv 64 a176) \/
 (getr regs' 10 = Z_to_bv 64 a176 /\ getr regs' 11 = Z_to_bv 64 a184 /\ (w, h, top, left) = (1, 1, 0, 0) /\ (forall p, 0 <= p < Wd * Hd -> ~ PDp p))).

Lemma fl_search_slowX : forall (regsE : bvmap 5 word) memE mdE,
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 25 = Z_to_bv 64 g -> getr regsE 24 = Z_to_bv 64 cfp ->
getr regsE 12 = Z_to_bv 64 0 -> getr regsE 21 = Z_to_bv 64 fimg -> getr regsE 19 = Z_to_bv 64 fimg ->
getr regsE 20 = Z_to_bv 64 bimg -> getr regsE 18 = Z_to_bv 64 bimg -> getr regsE 10 = Z_to_bv 64 Wd ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 192) 8 0 -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1ad4)) memE (seg_rom SEGS)) mdE) wsc_postX.
Proof.
intros regsE memE mdE HJE WK HKE E6 E25 E24 E12 E21 E19 E20 E18 E10 V192 V216.
pose proof HGEO as (RW & RH & HN & _).
eapply SRr_bind.
{ pose proof (fl_s1oX B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd a176 a184 sv2 sv4 HC HGEO HRES HSAV (Z.to_nat Hd)) as S1O. unfold s1o_stmtX in S1O.
eapply (S1O 0 regsE memE mdE); [ rewrite Z2Nat.id by lia; lia | lia | exact HJE | exact WK | exact HKE | exact E6 | exact E25 | exact E24 | exact E12
| rewrite E21; f_equal; lia | rewrite E19; f_equal; lia | rewrite E20; f_equal; lia | rewrite E18; f_equal; lia | exact E10 | exact V192 | exact V216 ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & pc5 & -> & HJ5 & WK5 & HK5 & H65 & H215 & H225 & V2165 & Hexit).
destruct Hexit as [(-> & top & c0 & HtopR & Hc0 & HPDw & H195 & H105 & H155 & H245 & V1845 & XN1) | (-> & H275 & H235 & H265 & V1605 & H105 & H115 & H185 & H205 & XNall)].
-
eapply SRr_bind.
{ eapply (fl_s2X B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO HFIMG top regs5 mem5 md5);
[ exact HtopR | exact HJ5 | exact WK5 | exact HK5 | exact H65 | exact H215 | exact H225 | exact H245 | exact H195 | exact H105 | exact H155 | exact V1845 | exact V2165 ]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & bot & -> & HJ6 & WK6 & HK6 & H66 & H216 & H226 & H276 & H196 & H156 & HbotR & V2166 & V1846 & XB2 & XN2).
eapply SRr_bind.
{ eapply (fl_s3X B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO HFIMG top bot c0 regs6 mem6 md6);
[ clear - HtopR HbotR; lia | clear - HbotR; lia | exact Hc0 | exact HPDw | exact HJ6 | exact WK6 | exact HK6 | exact H66 | exact H216 | exact H226 | exact H276
| exact H196 | exact H156 | exact V2166 | exact V1846 ]. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & left & -> & HJ7 & WK7 & HK7 & H217 & H227 & Hleft & H237 & H187 & H197 & H277 & H207 & H267 & H257 & H247 & H147
& V2167 & V1607 & XT3 & XN3).
eapply SRr_mono.
{ eapply (fl_s4X B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd a176 a184 sv2 sv4 HC HGEO HRES HFIMG HSAV c0 top bot left regs7 mem7 md7);
[ exact Hleft | clear - Hc0; lia | clear - HtopR HbotR; lia | clear - HbotR; lia | exact HPDw | exact HJ7 | exact WK7 | exact HK7 | exact H217 | exact H227
| exact H197 | exact H207 | exact H187 | exact H277 | exact H267 | exact H257 | exact H247 | exact H237 | exact H147 | exact V2167 | exact V1607 ]. }
cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & right & -> & HJ8 & WK8 & HK8 & H68 & H218 & H228 & Hright & H268 & V1608 & H278 & H238 & H108 & H118 & H188 & H208
& XT4 & XN4).
split; [reflexivity|]. exists regs8, mem8, md8, (right - left + 1), (bot + 1 - top), top, left.
split; [reflexivity|]. split; [exact HJ8|]. split; [exact WK8|]. split; [exact HK8|].
split; [exact H68|]. split; [exact H218|]. split; [exact H228|]. split; [exact H188|]. split; [exact H208|].
split; [exact H268|]. split; [exact H278|]. split; [exact H238|]. split; [exact V1608|].
do 6 (split; [clear - HtopR HbotR Hleft Hright Hc0; lia|]).
split.
+ left. exists bot, right, c0.
split; [reflexivity|]. split; [reflexivity|]. split; [clear - HtopR HbotR; lia|]. split; [clear - HbotR; lia|].
split; [clear - Hleft Hright Hc0; lia|]. split; [clear - Hright; lia|].
split; [exact Hc0|]. split; [exact HPDw|]. split; [exact XN1|]. split; [exact XB2|]. split; [exact XN2|].
destruct XT3 as (y3 & Hy3 & XT3). destruct XT4 as (y4 & Hy4 & XT4).
split; [exists y3; split; [clear - Hy3; lia | exact XT3]|].
split; [intros i x' Hi Hx'; apply XN3; [clear - Hi; lia | exact Hx']|].
split; [exists y4; split; [clear - Hy4; lia | exact XT4]|].
intros i x' Hi Hx'; apply XN4; [clear - Hi; lia | exact Hx'].
+ left. split; [exact H108 | exact H118].
-
apply SRr_ret. split; [reflexivity|]. exists regs5, mem5, md5, 1, 1, 0, 0.
split; [reflexivity|]. split; [exact HJ5|]. split; [exact WK5|]. split; [exact HK5|].
split; [exact H65|]. split; [exact H215|]. split; [exact H225|]. split; [exact H185|]. split; [exact H205|].
split; [exact H265|]. split; [exact H275|]. split; [exact H235|]. split; [exact V1605|].
do 6 (split; [clear - RW RH; lia|]).
split.
+ right. split; [reflexivity | exact XNall].
+ right. split; [exact H105|]. split; [exact H115|]. split; [reflexivity|]. intros p Hp; apply XNall; clear - Hp; lia.
Qed.
End d.
End c.
End b.
End a.
