(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Require OSSVerify.openssl.punycode.images.Plain.
Require OSSVerify.openssl.punycode.images.Ubsan.
Require OSSVerify.openssl.punycode.images.Asan.
Require OSSVerify.openssl.punycode.images.AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Cls Require Import ClsAnchor ClsMain Rows ClsTotal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_sat_Src_punycode : image_brk_satisfiable (img_segments (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma brk_sat_Tgt_punycode_ubsan : image_brk_satisfiable (img_segments (mkImage OSSVerify.openssl.punycode.images.Ubsan.M.loaded_segments OSSVerify.openssl.punycode.images.Ubsan.M.init_pc OSSVerify.openssl.punycode.images.Ubsan.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma brk_sat_Tgt_punycode_asan : image_brk_satisfiable (img_segments (mkImage OSSVerify.openssl.punycode.images.Asan.M.loaded_segments OSSVerify.openssl.punycode.images.Asan.M.init_pc OSSVerify.openssl.punycode.images.Asan.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma brk_sat_Tgt_punycode_both : image_brk_satisfiable (img_segments (mkImage OSSVerify.openssl.punycode.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.punycode.images.AsanUbsan.M.init_pc OSSVerify.openssl.punycode.images.AsanUbsan.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem base_row_punycode_ubsan : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)
    (mkImage OSSVerify.openssl.punycode.images.Ubsan.M.loaded_segments OSSVerify.openssl.punycode.images.Ubsan.M.init_pc OSSVerify.openssl.punycode.images.Ubsan.M.phdrs) ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)
    (mkImage OSSVerify.openssl.punycode.images.Ubsan.M.loaded_segments OSSVerify.openssl.punycode.images.Ubsan.M.init_pc OSSVerify.openssl.punycode.images.Ubsan.M.phdrs).
Proof. intros cfg Hb. exact (issued_base_of_pinned cfg _ _ Hb). Qed.

Theorem base_row_punycode_asan : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)
    (mkImage OSSVerify.openssl.punycode.images.Asan.M.loaded_segments OSSVerify.openssl.punycode.images.Asan.M.init_pc OSSVerify.openssl.punycode.images.Asan.M.phdrs) ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)
    (mkImage OSSVerify.openssl.punycode.images.Asan.M.loaded_segments OSSVerify.openssl.punycode.images.Asan.M.init_pc OSSVerify.openssl.punycode.images.Asan.M.phdrs).
Proof. intros cfg Hb. exact (issued_base_of_pinned cfg _ _ Hb). Qed.

Theorem base_row_punycode_both : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)
    (mkImage OSSVerify.openssl.punycode.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.punycode.images.AsanUbsan.M.init_pc OSSVerify.openssl.punycode.images.AsanUbsan.M.phdrs) ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.openssl.punycode.images.Plain.M.loaded_segments OSSVerify.openssl.punycode.images.Plain.M.init_pc OSSVerify.openssl.punycode.images.Plain.M.phdrs)
    (mkImage OSSVerify.openssl.punycode.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.punycode.images.AsanUbsan.M.init_pc OSSVerify.openssl.punycode.images.AsanUbsan.M.phdrs).
Proof. intros cfg Hb. exact (issued_base_of_pinned cfg _ _ Hb). Qed.
