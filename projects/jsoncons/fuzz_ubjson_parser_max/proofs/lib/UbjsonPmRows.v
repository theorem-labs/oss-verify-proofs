(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ClassifierRows UbjsonPmImgFacts UbjsonPmFinal UbjsonPmFinalA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__UbjsonPmRows () := ([""; "LinuxProcessSemantics.EquivalenceDefinition.Classifier."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.UbjsonPmFinal."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Cla_fuzz_ubjson_parser_max_ubsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Clb_fuzz_ubjson_parser_max_ubsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.TgtO_fuzz_ubjson_parser_max_ubsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.SrcO_jsoncons_fuzz_ubjson_parser_max_repro.M."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."], [["1classifier_total_T_fo"; "1classifies_good_inputs_T_s"; "1classifies_patch_diff_T_s"; "3lim_source"; "3lim_target"; "2strong_universal_error_free_T_scfg"; "2strong_universal_error_free_T_scfg_budgets_abort"; "4mkImage"; "5cfg0"; "6init_pc"; "6loaded_segments"; "6phdrs"; "7init_pc"; "7loaded_segments"; "7phdrs"; "8init_pc"]; ["8loaded_segments"; "8phdrs"; "9init_pc"; "9loaded_segments"; "9phdrs"; ":init_pc"; ":loaded_segments"; ":phdrs"; ";init_pc"; ";loaded_segments"; ";phdrs"]]).
Section Rows.
Hypothesis PK0 : PACKAGES_src.
Hypothesis PK1 : PACKAGES_ub.
Theorem ubjson_pm_ubsan_base : ltac2:(TCodec.tc2 tcn__UbjsonPmRows "<&5&8(7&I&H&J%43321&C&B&D%83321%;3:51").
Proof. exact (ubjson_pm_ubsan_modulo_packages PK0 PK1). Qed.
Theorem ubjson_pm_ubsan_base_abort : ltac2:(TCodec.tc2 tcn__UbjsonPmRows ">&6&8&3&4(7&I&H&J%43321&C&B&D%83321%=5<;:51").
Proof. exact (ubjson_pm_ubsan_abort_modulo_packages PK0 PK1). Qed.
End Rows.
