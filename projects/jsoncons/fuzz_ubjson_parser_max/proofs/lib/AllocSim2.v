(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim PropExec CatSim CatExec AllocSim MmapSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AllocSim2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "stdpp.bitvector.definitions."], [["1list"; "2and"; "3N"; "3Z"; "4equiv"; "4modeled"; "5omni_strong_equiv"; "6PhdrInfo"; "6Segment"; "6mkImage"; "7init_machine_state"; "7mkEntry"; "7run"; "7segments_reserved"; "8EntryDraw"; "9ProcInput"]; ["9in_argv"; "9in_envp"; "9in_hwcap"; "9in_uid"; "9init_model"; "9source_alloc_limit"; "9target_alloc_limit"; ":to_outcomes"; ";two_outcomes"; "<bufs_modeled"; "=tmw"; "0abrk"; "0alim"; "0amb"; "0apc"; "0aph"]; ["0arnd"; "0asp"; "0bf"; "0bs"; "0cf"; "0cs"; "0inp"; "0rbrk"; "0rlim"; "0rmb"; "0rpc"; "0rph"; "0rrnd"; "0rsp"; "0source_segs"; ">bv"]; ["0target_segs"]]).
Definition two_outcomes (bf : list (list byte)) (cf : word)
(bs : list (list byte)) (cs : word)
: (list (list byte) * word) -> Prop :=
fun o => o = (bf, cf) \/ o = (bs, cs).
Lemma alloc_mmap_strong_equiv : ltac2:(TCodec.tc2 tcn__AllocSim2 "S>'0'8%211'2'7'Q?yR0%211'>'3y8%611%<11%=11'?'GrE&:rDrCrBr?&@r1%211&A%113&C%115&B%117%>9?=<;:7531&D&=%11BrAr@r>%66432B1?&Hr5r4r3r2%544321%N4M>71'Jr=r<r;r8%M18%K19%J1:%I1;%Q69B87654321%G1Cr:r9r7%L6432;1Ar6%@7I721FED&I%115%214'1&5&<(9rIrHrG%43321(;rF%241QLQJQI%944QI1Q5%;11&4%;3Q=Q<QK%74Q<Q2Q1Q0%>42I1Q:%4261%B261p0D1p0F1p0I1p0Q;1pR>R;1pR<RC1pR8R>1pR:RE1pR6R@1pQJRE1pR2RG1pQLRI1pQHRJ1pR4RK1pR0RO1pQNS11pS2S31pRBRM1pRJRO1pRDS11pR@S21pRLS31pRHS71pRFS91pRNS;1").
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
Lemma alloc_mmap_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__AllocSim2 "S4'0'8%211'2'7'Q?yR0%211'>y8%511%;11%<11'?'GrC&:rBrAr@r=&@r1%211&A%113&C%115&B%117%>9?=<;:7531&D&=%11Br?r>&E%66432B1?&Hr5r4r3r2%544321%N4M>71'Jr<r;r:r7%M18%K19%J1:%I1;%Q69Q287654321%G1Q3r9r8&F%L6432;1Ar6%@7Q9721FED&I%11>%214&6(9rGrFrE%43321%53QDQ5Q4(;rD%241QKQIQH%34QGMLK%;56521Q5p0=1p0?1p0B1p0Q41pR>R41pR<R;1pR8R71pR:R=1pR6R91pR2R>1pQLR@1pQHRA1pR4RB1pR0RF1pQNRH1pS2RJ1pRJRE1pRDRG1pR@RH1pRLRI1pRHRM1pRFRO1pRNS11").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs
inp Hsource Htarget Hbf Hbs.
apply strong_equiv_iff.
apply (alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
Hsource Htarget Hbf Hbs).
Qed.
