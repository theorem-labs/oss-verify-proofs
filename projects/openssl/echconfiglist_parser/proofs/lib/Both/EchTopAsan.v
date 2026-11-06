(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added the HaltsCfgForcedOnly and allowed-exits modules and the halts theorem of the asan-ubsan build, copied from projects/openssl/echconfiglist_parser/proofs/lib/EchTopAsan.v at commit 874e3397a35 (its lines 23-31 and 53-59) with images.Asan replaced by images.AsanUbsan and lib.EchRowsAsan by lib.Both.EchRowsAsan. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List QArith Lia.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg Spec HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both Require BaseAsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both Require EchRowsAsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_Iface MallocSR ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require AsIface AsIfaceX ECH_Iface ECH_ALib F_time AInstFacts.
Require OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_ALibTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module OpensslEchconfiglistParserHaltsAsanUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslEchconfiglistParserHaltsAsanUbsanExits.

(* [comment removed for export] *)
Definition FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
    @OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC)
  := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_closed.

Section ThirdAsan.
  (* [comment removed for export] *)
  Definition FZ_a : forall (HCEIL : HeapCeil) (H : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.AsIface.asr),
      OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.AsIfaceX.asan_rt_hyps_x H -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.AInstFacts.ainst_facts H -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_Iface.fuzz_stmt H OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_ALib.ECHL
    := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_ALibTop.fuzz_closed5.

Theorem strong_universal_error_free_echconfiglist_parser_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.M.phdrs).
Proof. exact (BaseAsan.asan_base FZ_p FZ_a). Qed.

Theorem halts_allowed_openssl_echconfiglist_parser_halts_asan_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslEchconfiglistParserHaltsAsanUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.AsanUbsan.M.phdrs).
Proof. exact (EchRowsAsan.halts_asan FZ_a). Qed.

End ThirdAsan.
