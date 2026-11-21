(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/TopHaltsA.v and its sibling
   TopHaltsB.v at commit theorem-labs/oss-verify-proofs@c5665593c2d8, lines 4-6 (the Stdlib/LPS import block), lines 14-15 (lim_source_le_target,
   verbatim) and lines 17-19 of each (the halts_allowed_T_scfg_budgets theorem statement), with from_chars's Asan and
   AsanUbsan images replaced by this harness's Plain and Ubsan, SpecHalts.HALT_CODES by this tree's HALT_CODES, and the
   theorem names by halts_skcms_iccprofile_info_plain and _ubsan.  The proof bodies are not copied: from_chars's single
   halts_allowed_lowered_of_realizes call is replaced here by HaltsBridge.halts_of_realizes_spec for the plain build and
   by must_exit_of_realizes_spec composed with Halts.Lim.LimTransfer.lim_transfer_scfg for the UBSan build. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the bridge onto the run's segment list takes vdso_none_plain and vdso_none_ubsan (neither binary image has a vDSO), and the cited source commit is named by its public id. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's lib/Halts/HaltsTops.v, its vdso_none lemmas and its halting theorem statements, for the ASan and ASan+UBSan images; the proofs take the ASan target facts InfoAsanTop.info_asan_tgt_C and InfoBothTop.info_both_tgt_C at this unit's certificates through HaltsAsanKit.halts_of_srealizes_tgt, after projects/libpcap/fuzz_pcap/proofs/lib/E2/Top/Halts_asan.v and Halts_both.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6; taken from projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsTops.v, lines 21-24, 29, 43-46, 49-51, 54-59 and 67, as in the LPS 727298f3 update. *)
(** The halting theorems of the two ASan builds, in the form [Statements.v]
    states them.

    The ASan target statement of each build is proved at 512 GiB, under the
    configuration where an allocation is refused only when it must be, for the
    plain build's trace set; [HaltsAsanKit] turns it into "must exit with 0
    or 2" at 512 GiB and carries that down to 16 GiB with
    [Halts.Lim.LimTransfer] on the inputs the statement's own premise names. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From OSSVerify.skcms.iccprofile_info.images Require Asan AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsLibFuzz BoLibFuzz.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require InfoAsanTop InfoBothTop InfoAsanFinal InfoBothFinal.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainForest AsanMainForestBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require Import SpecHalts HaltsAsanKit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsTops.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** [vdso_image … = None] is true of every binary image by computation, as in
    [HaltsTops.vdso_none_plain]. *)
Lemma vdso_none_asan : RiscvSemantics.vdso_image Asan.M.loaded_segments = None.
Proof. vm_compute. reflexivity. Qed.

Lemma vdso_none_both : RiscvSemantics.vdso_image AsanUbsan.M.loaded_segments = None.
Proof. vm_compute. reflexivity. Qed.

(** This unit's ASan certificates, as [InfoAsanClosed] and [InfoBothClosed]
    fill them: each CONFIG_RSEQ layout's forest ([TREE_rsb]) with its proof. *)
Definition asan_certs_closed : InfoAsanTop.asan_certs :=
  InfoAsanFinal.info_asan_certs AsanMainForest.TREE_rsb AsanMainForest.TREES_rsb.

Definition both_certs_closed : InfoBothTop.both_certs :=
  InfoBothFinal.info_both_certs AsanMainForestBoth.TREE_rsb AsanMainForestBoth.TREES_rsb.

Theorem halts_skcms_iccprofile_info_asan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  exact (halts_of_srealizes_tgt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs
           ShippedBudgets.lim_source target_alloc_limit HaltsTops.lim_source_le_target vdso_none_asan
           (InfoAsanTop.info_asan_tgt_C AsLibFuzz.as_fuzz_closed asan_certs_closed)).
Qed.

Theorem halts_skcms_iccprofile_info_asan_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  exact (halts_of_srealizes_tgt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
           ShippedBudgets.lim_source target_alloc_limit HaltsTops.lim_source_le_target vdso_none_both
           (InfoBothTop.info_both_tgt_C BoLibFuzz.as_fuzz_closed both_certs_closed)).
Qed.
