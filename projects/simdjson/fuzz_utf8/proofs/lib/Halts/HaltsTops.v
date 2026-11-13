(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/TopHaltsA.v and its sibling
   TopHaltsB.v at commit c395a1e0dfa, lines 4-6 (the Stdlib/LPS import block), lines 14-15 (lim_source_le_target,
   verbatim) and lines 17-19 of each (the halts_allowed_T_scfg_budgets theorem statement), with from_chars's Asan and
   AsanUbsan images replaced by this harness's Plain and Ubsan, SpecHalts.HALT_CODES by this tree's HALT_CODES, and the
   theorem names by halts_skcms_iccprofile_info_plain and _ubsan.  The proof bodies are not copied: from_chars's single
   halts_allowed_lowered_of_realizes call is replaced here by HaltsBridge.halts_of_realizes_spec for the plain build and
   by must_exit_of_realizes_spec composed with Halts.Lim.LimTransfer.lim_transfer_scfg for the UBSan build. *)
(* Modified by gabelogan195, 2026-11: made from projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsTops.v at commit f92feaf8b7 (the import block and the theorem statement of halts_skcms_iccprofile_info_plain), with skcms's Plain image replaced by simdjson/fuzz_utf8's and the theorem named halts_plain; the proof body is new: it takes the entry and the input apart as this harness's Thm_fuzz_utf8_ubsan.thm_either does, lowers the environment from Lib.Cfg.ACFG to forced_only_cfg, and walks Main_src13.realizes_spec_src13 with Halts.HaltsWalk.srealizes_must_exit_in, refuting its spinning leaf by SpinScan.exec_has_spin SEGS_src13 = false. *)
(** The halting theorem of the plain build, in the form [Statements.v] states
    it.

    The plain build's realization is proved at 16 GiB, the budget
    [Statements.plain_halts] names, so the walk of [HaltsWalk] needs no budget
    transfer and drops the statement's budget premise.  Its spinning leaf is
    ruled out by a scan of the image: the plain build's executable segment
    holds no [jal x0, 0]. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import ShapeAlg SpinAlg SpinScan Spec.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Img_src13 Main_src13.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Tree_src13.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Halts Require Import SpecHalts HaltsWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The plain build's executable segment holds no [jal x0, 0]. *)
Lemma no_spin_src13 : exec_has_spin SEGS_src13 = false.
Proof. vm_compute. reflexivity. Qed.

Theorem halts_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  intros [rsp rbrk rmb rdr] inp Hens Hv _.
  pose proof (valid_input_either_of_valid_input _ Hv) as Hve. clear Hv.
  assert (Hsv48 : in_va_size inp = Sv48)
    by (destruct Hve as (_ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]].
  destruct Hve as [Hargv [Henvp [Hfs [_ [[Huid Hgid] [Hnof [Hsig [Hhw _]]]]]]]].
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw abt va urnd tmp].
  cbn [in_va_size in_argv in_envp in_fs in_uid in_gid in_nofile in_hwcap] in *. subst va.
  cbn [must_exit_in_scfg].
  apply (must_exit_in_at_cfg_mono_classic forced_only_cfg ACFG _ HALT_CODES _ (forced_only_cfg_least ACFG)).
  refine (srealizes_must_exit_in SEGS_src13 HALT_CODES no_spin_src13 _ (spec argv (fs_seed_tmp fs tmp))
            (realizes_spec_src13 rsp rdr rbrk rmb argv envp (fs_seed_tmp fs tmp) stdin uid gid hw
               groups net nofile sigmask abt urnd Hrsp Hrbrk Hargv Henvp Hrfit Huid Hhw
               Tree_src13.CERTS_src13) _ _ _).
  - reflexivity.
  - exact (exits_in_spec argv (fs_seed_tmp fs tmp)).
  - exact (kill_free_spec argv (fs_seed_tmp fs tmp)).
Qed.
