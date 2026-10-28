(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List QArith Lia.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.
Require OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg Spec HeapCeil HeapSecret.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require BaseAsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_Iface MallocSR ECH_LibTop.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require AsIface AsIfaceX ECH_Iface ECH_ALib F_time AInstFacts.
Require OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_ALibTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

(* [comment removed for export] *)
Definition FZ_p : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
    @OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_Iface.fuzz_stmt HCEIL (@OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref.MallocSR.HS HCEIL HSEC)
  := OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_closed.

Section ThirdAsan.
  (* [comment removed for export] *)
  Definition FZ_a : forall (HCEIL : HeapCeil) (H : OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.AsIface.asr),
      OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.AsIfaceX.asan_rt_hyps_x H -> OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.AInstFacts.ainst_facts H -> OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_Iface.fuzz_stmt H OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_ALib.ECHL
    := OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As.ECH_ALibTop.fuzz_closed5.

Theorem strong_universal_error_free_echconfiglist_parser_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.M.init_pc OssFuzzTheorems.openssl.echconfiglist_parser.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.echconfiglist_parser.images.AsanUbsan.M.phdrs).
Proof. exact (BaseAsan.asan_base FZ_p FZ_a). Qed.

End ThirdAsan.
