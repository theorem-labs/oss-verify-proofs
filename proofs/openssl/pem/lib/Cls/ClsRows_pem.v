(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Require OssFuzzTheorems.openssl.pem.images.Plain.

Require OssFuzzTheorems.openssl.pem.images.Ubsan.







Require OssFuzzTheorems.openssl.pem.images.AsanUbsan.



From OssFuzzTheorems.Proofs.openssl.pem.lib.Cls Require Import ClsMain Rows. 
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)







(* [comment removed for export] *)







(* [comment removed for export] *)







(* [comment removed for export] *)







(* [comment removed for export] *)







(* [comment removed for export] *)








(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_sat_Src_pem : image_brk_satisfiable (img_segments (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.





Lemma brk_sat_Tgt_pem_both : image_brk_satisfiable (img_segments (mkImage OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem base_row_pem_ubsan : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.openssl.pem.images.Ubsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Ubsan.M.init_pc OssFuzzTheorems.openssl.pem.images.Ubsan.M.phdrs) ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.openssl.pem.images.Ubsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Ubsan.M.init_pc OssFuzzTheorems.openssl.pem.images.Ubsan.M.phdrs).
Proof. intros cfg Hb. exact (issued_base_of_pinned cfg _ _ Hb). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)








(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)








Theorem base_row_pem_both : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.phdrs) ->
  strong_universal_error_free_T_scfg_budgets cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OssFuzzTheorems.openssl.pem.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.pem.images.Plain.M.init_pc OssFuzzTheorems.openssl.pem.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.pem.images.AsanUbsan.M.phdrs).
Proof. intros cfg Hb. exact (issued_base_of_pinned cfg _ _ Hb). Qed.
