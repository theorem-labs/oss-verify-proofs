(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v
   (ossv/recipes c8557374ad2) for fuzz_disco, in the form of fuzz_pcap's closing file lib/A/PcapClose.v
   (a working branch fe3d720b4c7): the closing of lib/A/DiscoAsanTop.v ASAN_T from named parts; module paths
   changed, shape DiscoAsanTop.disco_shape, fuzz_disco's asan image, ONE program part (LLVMFuzzerTestOneInput's
   contract) in place of cgif_file_fuzzer's three (TNEWGIFX / TADDFX / TCLOSEX and their wfn). *)
(* The closing side of fuzz_disco's two asan statements (rule 24: no function proved; this file is assembly).

   The split is fuzz_grant's (a working branch 7d31e8f3534: lib/A/AGrantT.v below lib/A/GrantTop.v). The lower file,
   lib/A/DiscoAsanT.v, applies lib/A/AD1q.v tfib_srealizesX over the landed core (a working branch f0d1f4eacff):
   the start-up (AB1n.v tfib_startup_T1 over AB01.v HS_tfib / AB12.v TFIB), the symbol table (AD2l.v TfibB /
   TfibB_syms), both allocator realizes (AF0w.v, AF0q.v), the memcpy interceptor and the read check (AD2m.v) and the
   driver's stdio sites (AD1k.v, AD1o.v, AD1l.v, AD1j.v), every one a proved lemma. Its TFIB_T_of_lib takes only the
   program contract and the read-only facts that contract's walks use. This file keeps exactly those two as Section
   hypotheses, each with the lane that supplies it (the obligation list is proofs/libreac/fuzz_disco/lib/A/OBLIGATIONS.md at a working branch 37e11e67676d), and
   closes the two statements. de_hroA (row P12) uses the base's lib/A/Prog/DiscoBase.v arodata_okP and
   lib/A/Prog/DiscoImg.v's PAImg instance PB_disco. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YC5d YCbp YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require ACfn AD2l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoList DiscoPa DiscoImg DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import DiscoAsanTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require DiscoAsanT.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := DiscoAsanTop.disco_shape.

Section asan.
(* B: the image's symbol and trace table, lib/A/AD2l.v TfibB (row A4), fixed as lib/A/DiscoAsanT.v fixes it (`Let B :=
   TfibB`, fuzz_grant's lib/A/AGrantT.v:35 `Let B := GrantB`). *)
Local Notation B := AD2l.TfibB.
(* H_RO (row A9): the read-only facts the part's walks take, a Theorem Labs lane's lib/A/Prog/DiscoEntBodyStmt.v:72 d_ro_hyps
   at B and the asan image (lib/A/DiscoAsanT.v H_RO_stmt: DiscoRo.disco_ro_unowned, globs_marked over
   DiscoRoList.disco_globs, img_shadow_vis). Closed at TfibB by a Theorem Labs lane's lib/A/Prog/DiscoRoClose.v
   (disco_ro_unowned_tfib, disco_globs_marked, disco_img_shadow_vis), by computation. It stays here until
   a Theorem Labs lane's part takes d_ro_hyps itself and discharges it, as fuzz_grant's GrantLibXClosed.grant_lib_x_all does. *)
Hypothesis H_RO : forall rc : YM05.RunCeil, DiscoAsanT.H_RO_stmt rc.
(* H_PROG_LIBX: THE PART, donor lib/A/AD1q.v:39 LIBX (lib/A/ACfn.v tfib_lib_contract_x_all, closed in the donor by
   lib/A/ACfi.v tfib_lib_x_all over three program parts), at fuzz_disco's one program part: the contract of
   LLVMFuzzerTestOneInput, with the donor's XL0 (ACfi.v:56, fun _ => 0), ameter_triv (Reusable/YCbp.v) and fuzz_disco's
   relro range (lib/A/Prog/DiscoImg.v). Owner: lib/A/Prog/DiscoLibX.v disco_lib_x_all (a Theorem Labs lane). Its premises
   other than H_RO (the runtime contracts per class, OBLIGATIONS.md) enter here when DiscoLibX states them. *)
Hypothesis H_PROG_LIBX :
  forall rc : YM05.RunCeil,
  DiscoAsanT.H_RO_stmt rc ->
  @ACfn.tfib_lib_contract_x_all rc LS B ameter_triv (fun _ => 0) (fun _ => 0)
    DiscoImg.disco_relro_lo DiscoImg.disco_relro_hi.

Section RC. Context {rc : YM05.RunCeil}.
(* Row P12 of OBLIGATIONS.md: the part's premise de_hro (S5's dentry_env field, lib/A/Prog/DiscoEntryShapes.v:57 at
   a working branch 01f9fabd121) at PI := DiscoImg.PB_disco and RLO / RHI := disco_relro_lo / hi. The two
   sides are one predicate: YE01.arodata_okS and DiscoBase.arodata_okP have the same body, and PB_disco's pa_segs /
   pa_relro_lo / pa_relro_hi are disco_segs (= the asan image's loaded segments) / disco_relro_lo / disco_relro_hi. *)
Lemma de_hroA : forall rd,
  YE01.arodata_okS (@DiscoPa.pa_segs rc DiscoList.disco_listing (@DiscoImg.PB_disco rc)) B
    DiscoImg.disco_relro_lo DiscoImg.disco_relro_hi rd ->
  DiscoBase.arodata_okP (@DiscoPa.pa_segs rc DiscoList.disco_listing (@DiscoImg.PB_disco rc))
    (@DiscoPa.pa_relro_lo rc DiscoList.disco_listing (@DiscoImg.PB_disco rc))
    (@DiscoPa.pa_relro_hi rc DiscoList.disco_listing (@DiscoImg.PB_disco rc)) B rd.
Proof. exact (fun rd H => H). Qed.
End RC.

(* donor lib/A/AD2o.v:75-84 tfib_srealizesX_top and TFIB_T_of_partsXF; ASAN_T is lib/A/AZ03.v TFIB_T, which
   lib/A/DiscoAsanT.v TFIB_T_of_lib proves from the two hypotheses above and the landed core. *)
Theorem ASAN_T_of_parts : DiscoAsanTop.ASAN_T.
Proof. exact (DiscoAsanT.TFIB_T_of_lib H_RO H_PROG_LIBX). Qed.

(* The two asan statements, given only the named parts above (donor lib/A/AZ05.v). *)
Theorem disco_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (DiscoAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem disco_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (DiscoAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.
End asan.
