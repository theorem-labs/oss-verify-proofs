(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: made from UZZ0: libtasn1's two builds (B.TopP, B.TopU) in place of cgif_rgb_fuzzer's, theorem names and module names. *)
(* libtasn1 / asn1_get_length_der_fuzzer: the plain and UBSan builds are strongly error-free
   equivalent under the shipped budgets, every allocation being allowed to fail (cgif_rgb_fuzzer's
   UZZ0, with libtasn1's two builds: OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.TopP and OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.TopU). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Plain.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YK15 YK18 YN09 YN05 YN0b YH04 UH04 YP07 YP01.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require Import TopP TopU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Lemma SRC_LIM_MIN_le_shipped_source : SRC_LIM_MIN <= ShippedBudgets.lim_source.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma SRC_LIM_MIN_le_shipped_target : SRC_LIM_MIN <= ShippedBudgets.lim_target.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Theorem asn1_get_length_der_fuzzer_ubsan_equiv_lim : forall ls lt : Z, SRC_LIM_MIN <= ls -> SRC_LIM_MIN <= lt ->
forall en_s en_t inp,
valid_entry (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) en_s inp ->
valid_entry (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) en_t inp ->
valid_input inp ->
strong_equiv_error_free_budgets ls lt
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) en_s en_t inp.
Proof.
intros ls lt Hls Hlt [sp brk mb rnd] [sp' brk' mb' rnd'] inp Hens Hent Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
destruct Hens as [Hsp [Hbrk [Hmb Hfit]]]. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
eapply (shape_strong_equiv_efs_budgets ls lt src2segs _ _ sp brk mb rnd ubs2segs _ _ sp' brk' mb' rnd' (SPEC inp) (SPEC inp) inp).
- apply tasn1_plain_realizes; assumption.
- apply srealizes_of_realizes. apply tasn1_ubsan_realizes; assumption.
- apply t_eq_refl.
Qed.
Theorem asn1_get_length_der_fuzzer_ubsan_equiv_shipped :
strong_universal_error_free_T_budgets ShippedBudgets.lim_source ShippedBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
intros en_s en_t inp Hs Ht Hv _.
exact (asn1_get_length_der_fuzzer_ubsan_equiv_lim _ _ SRC_LIM_MIN_le_shipped_source SRC_LIM_MIN_le_shipped_target en_s en_t inp Hs Ht Hv).
Qed.
