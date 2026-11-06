(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YCfy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCe5 YCe9 YCfx YCex YCev YCf8 YCfp YCfa YCfb YCfc YCfd YCfe YCff.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_icpt.
Section c.
Variables (W : world trbsegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Definition wfc_post : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' w h top left,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x88250) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r ([2; 3; 4; 8; 9]%bv : list (bv 5)) -> getr regs' r = getr regs r) /\
getr regs' 21 = Z_to_bv 64 w /\ getr regs' 23 = Z_to_bv 64 h /\ getr regs' 22 = Z_to_bv 64 left /\ getr regs' 27 = Z_to_bv 64 Wd /\
val_mem trbsegs (mrestrict (w_H W) mem') (sp1 + 152) 8 top /\
1 <= w /\ 0 <= left /\ left + w <= Wd /\ 1 <= h /\ 0 <= top /\ top + h <= Hd.
Lemma fl_search_fast : forall (regsE : bvmap 5 word) memE mdE,
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r ([2; 3; 4; 8; 9]%bv : list (bv 5)) -> getr regsE r = getr regs r) ->
getr regsE 18 = Z_to_bv 64 0 -> getr regsE 26 = Z_to_bv 64 0 -> getr regsE 19 = Z_to_bv 64 1 -> getr regsE 20 = Z_to_bv 64 1 ->
getr regsE 25 = Z_to_bv 64 bimg -> getr regsE 27 = Z_to_bv 64 Wd ->
SRr trbsegs W (mkCfg (mkst regsE (Z_to_bv 64 0x87d38) memE (seg_rom trbsegs)) mdE) wfc_post.
Proof.
intros regsE memE mdE HJE WK HKE E18r E26r E19r E20r E25r E27r.
pose proof HGEO as (RW & RH & HN & _).
eapply SRr_bind.
{ pose proof (fl_f1 B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO (Z.to_nat Hd)) as S1. unfold f1_stmt in S1.
eapply (S1 0 regsE memE mdE); [ rewrite Z2Nat.id by lia; lia | lia | exact HJE | exact WK | exact HKE | rewrite E18r; f_equal; lia | exact E26r | exact E19r | exact E20r | exact E25r | exact E27r ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & pc5 & -> & HJ5 & WK5 & HK5 & H275 & Hexit).
destruct Hexit as [(-> & top & c0 & HtopR & Hc0 & HBDw & H265 & H255) | (-> & H215 & H235 & H225 & V1525)].
-
eapply SRr_bind.
{ eapply (fl_f2 B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO top regs5 mem5 md5); [ exact HtopR | exact HJ5 | exact WK5 | exact HK5 | exact H265 | exact H255 | exact H275 ]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & WK6 & HK6 & H276 & H256 & H266 & H186 & H296 & bot & HbotR & H196).
eapply SRr_bind.
{ eapply (fl_f3 B LAWS W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO c0 top bot regs6 mem6 md6);
[ exact Hc0 | lia | exact HbotR | exact HBDw | exact HJ6 | exact WK6 | exact HK6 | exact H276 | exact H256 | exact H266 | exact H186 | exact H296 | exact H196 ]. }
cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & left & -> & HJ7 & WK7 & HK7 & Hleft & H227 & H127 & H137 & H147 & H237 & H257 & H267 & H277 & H297).
eapply SRr_mono.
{ eapply (fl_f4 B LAWS W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO c0 top bot left regs7 mem7 md7);
[ exact Hleft | lia | lia | exact HbotR | exact HBDw | exact HJ7 | exact WK7 | exact HK7 | exact H227 | exact H127 | exact H137 | exact H147 | exact H237 | exact H257 | exact H267 | exact H277 | exact H297 ]. }
cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & w & -> & HJ8 & WK8 & HK8 & Hw1 & Hlw & H218 & H228 & H238 & H278 & V1528).
split; [reflexivity|]. exists regs8, mem8, md8, w, (bot + 1 - top), top, left.
split; [reflexivity|]. split; [exact HJ8|]. split; [exact WK8|]. split; [exact HK8|].
split; [exact H218|]. split; [exact H238|]. split; [exact H228|]. split; [exact H278|]. split; [exact V1528|]. lia.
-
apply SRr_ret. split; [reflexivity|]. exists regs5, mem5, md5, 1, 1, 0, 0.
split; [reflexivity|]. split; [exact HJ5|]. split; [exact WK5|]. split; [exact HK5|].
split; [exact H215|]. split; [exact H235|]. split; [exact H225|]. split; [exact H275|]. split; [exact V1525|]. lia.
Qed.
End c.
End b.
End a.
