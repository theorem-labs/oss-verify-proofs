(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/TopBndivHaltsA.v at commit 874e3397a35, its lemma lim_source_le_target and its halting theorem's lim_transfer_scfg step, with the module paths changed to libpcap/fuzz_pcap and the large-budget halting fact taken from this unit's ASan+UBSan equivalence proof (HaltsAsanKit.v) in place of bndiv's realizes_asan. *)
(** The ASan+UBSan build of fuzz_pcap halts within the 16 GiB budget.

    The equivalence proof of this build gives an srealizes fact for its run at
    the 512 GiB budget, under the configuration where an allocation is refused
    only when it must be; that fact realizes the plain build's trace set, whose
    exits are all 0 or 2 (HaltsAsanKit.v).  So every forced-only execution at
    512 GiB exits with 0 or 2, and lib/Lim/LimTransfer.v carries that down to
    16 GiB on the inputs where the run is never refused memory for exceeding
    16 GiB, which is the statement's own premise. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.libpcap.fuzz_pcap.images Require AsanUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Final_asan__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ImplTopA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import HaltsAsanKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lim Require LimTransfer.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.

Theorem fuzz_pcap_halts_both :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2]
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros en inp He Hi Hbud.
  apply (LimTransfer.lim_transfer_scfg forced_only_cfg _ _ en inp ShippedBudgets.lim_source target_alloc_limit
           lim_source_le_target); [| exact Hbud].
  destruct (plain_entry inp Hi) as [enS HvS].
  destruct UNodes__Equiv.EquivPlan.budgets_ok as [LIMS _].
  apply (must_exit_forced_of_srz _ _ _ _ en inp _
           (Final_asan__EquivA.Final_both.fuzz_pcap_both_srz ImplTopA.TwB.stkA_real ImplTopA.TwB.stkA_real_ok ImplTopA.TwB.IMPL_A_real
              source_alloc_limit LIMS enS en inp HvS He Hi)).
  exact (plain_traces_ok source_alloc_limit LIMS enS inp HvS Hi).
Qed.
