(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List QArith Lia.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg Spec HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import EchHalts.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require BaseUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require RefTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require UbTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_Iface MallocSR ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require ECH_Iface MallocSR ECH_LibTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module OpensslEchconfiglistParserHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslEchconfiglistParserHaltsPlainExits.

Module OpensslEchconfiglistParserHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslEchconfiglistParserHaltsUbsanExits.

(* [comment removed for export] *)
Definition FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
    @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC)
  := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_closed.

Theorem halts_allowed_openssl_echconfiglist_parser_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslEchconfiglistParserHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs).
Proof.
  apply (@halts_of_realizes_spec hunspell_scfg). unfold full_stmt. intros sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs.
  apply (RefTop.ref_realizes_spec_lim FZ_p); try assumption. unfold Equivalence.ShippedBudgets.lim_source, source_alloc_limit. lia.
Qed.

(* [comment removed for export] *)
Definition FZ_u : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
    @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.MallocSR.HS HCEIL HSEC)
  := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.ECH_LibTop.fuzz_closed.

Theorem strong_universal_error_free_echconfiglist_parser_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.phdrs).
Proof. exact (BaseUbsan.ubsan_base FZ_p FZ_u). Qed.

Theorem halts_allowed_openssl_echconfiglist_parser_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslEchconfiglistParserHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.phdrs).
Proof.
  apply (@halts_of_realizes_spec hunspell_scfg). unfold full_stmt. intros sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs.
  apply (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.UbTop.ub_realizes_spec_lim FZ_u); try assumption. unfold Equivalence.ShippedBudgets.lim_source, source_alloc_limit. lia.
Qed.
