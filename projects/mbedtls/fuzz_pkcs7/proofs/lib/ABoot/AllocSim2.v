(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim PropExec CatSim CatExec AllocSim MmapSim.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AllocSim2 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "OSSVerify.KrLib.ABoot.AllocSim.to_outcomes"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "two_outcomes"; "OSSVerify.KrLib.ABoot.MmapSim.tmw"; "OSSVerify.KrLib.ABoot.CatSim.bufs_modeled"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"; "LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"].


(* [comment removed for export] *)
Definition two_outcomes (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    : (list (list byte) * word) -> Prop :=
  fun o => o = (bf, cf) \/ o = (bs, cs).

(* [comment removed for export] *)
Lemma alloc_mmap_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_AllocSim2 ()) "Psource_segs,(0.$1.)Prpc,$2.Prph,$3.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5.Prlim,$6.Ptarget_segs,(0.$1.)Papc,$2.Paph,$3.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5.Palim,$6.Pbf,(0.(0.(4.&8.)))Pcf,(4.&40.)Pbs,(0.(0.(4.&8.)))Pcs,(4.&40.)Pinp,$7.P,(8.R15.(9.R15.R14.R13.R12.R?.(:.R1.)(;.R1.)(<.R1.)(=.R1.))(>.(?.R15.)R11.R10.R12.R>.R1.)(10.R5.R4.R3.R2.))P,(11.R>.(9.R>.R=.R<.R;.R8.(:.R2.)(;.R2.)(<.R2.)(=.R2.))(>.(?.R>.)R:.R9.R;.R7.R2.)R6.R5.R4.R3.)P,(12.R7.)P,(12.R6.)(13.(14.(15.(16.R19.R18.R17.)R12.(17.R16.R15.R14.R13.)R5.))(18.(15.(16.R19.R18.R17.)R12.(17.R16.R15.R14.R13.)R5.)(15.(16.R11.R10.R?.)R:.(17.R>.R=.R<.R;.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs
    inp Hsource Htarget Hbf Hbs.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp
             (two_outcomes bf cf bs cs) Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp
               (two_outcomes bf cf bs cs) Hsource tr).
    rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp
               bf cf bs cs Htarget Hbf Hbs tr).
    unfold two_traces, two_outcomes, outcome_trace.
    split.
    + intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
    + intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)];
        cbn [fst snd]; auto.
  - cbn.
    apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp
             bf cf bs cs Htarget Hbf Hbs).
Qed.

(* [comment removed for export] *)
Lemma alloc_mmap_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_AllocSim2 ()) "Psource_segs,(0.$1.)Prpc,$2.Prph,$3.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5.Ptarget_segs,(0.$1.)Papc,$2.Paph,$3.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5.Pbf,(0.(0.(4.&8.)))Pcf,(4.&40.)Pbs,(0.(0.(4.&8.)))Pcs,(4.&40.)Pinp,$7.P,(8.R13.(9.R13.R12.R11.R10.R=.(:.R1.)(;.R1.)(<.R1.)(=.R1.))(>.(?.R13.)R?.R>.R10.$19.R1.)(10.R5.R4.R3.R2.))P,(11.R=.(9.R=.R<.R;.R:.R7.(:.R2.)(;.R2.)(<.R2.)(=.R2.))(>.(?.R=.)R9.R8.R:.$1:.R2.)R6.R5.R4.R3.)P,(12.R7.)P,(12.R6.)(1;.(16.R17.R16.R15.)(16.R10.R?.R>.)(17.R14.R13.R12.R11.)(17.R=.R<.R;.R:.)R5.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs
    inp Hsource Htarget Hbf Hbs.
  apply strong_equiv_iff.
  apply (alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
           target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
           Hsource Htarget Hbf Hbs).
Qed.
