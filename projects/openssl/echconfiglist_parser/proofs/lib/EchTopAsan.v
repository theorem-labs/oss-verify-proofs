(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List QArith Lia.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.Asan.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg Spec HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require BaseAsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require EchRowsAsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_Iface MallocSR ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require AsIface AsIfaceX ECH_Iface ECH_ALib F_time AInstFacts.
Require OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.ECH_ALibTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module OpensslEchconfiglistParserHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslEchconfiglistParserHaltsAsanExits.

(* [comment removed for export] *)
Definition FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
    @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC)
  := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_closed.

Section ThirdAsan.
  (* [comment removed for export] *)
  Definition FZ_a : forall (HCEIL : HeapCeil) (H : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.AsIface.asr),
      OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.AsIfaceX.asan_rt_hyps_x H -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.AInstFacts.ainst_facts H -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.ECH_Iface.fuzz_stmt H OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.ECH_ALib.ECHL
    := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As.ECH_ALibTop.fuzz_closed5.

Theorem strong_universal_error_free_echconfiglist_parser_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Asan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Asan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Asan.M.phdrs).
Proof. exact (BaseAsan.asan_base FZ_p FZ_a). Qed.

Theorem halts_allowed_openssl_echconfiglist_parser_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslEchconfiglistParserHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Asan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Asan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Asan.M.phdrs).
Proof. exact (EchRowsAsan.halts_asan FZ_a). Qed.
End ThirdAsan.
