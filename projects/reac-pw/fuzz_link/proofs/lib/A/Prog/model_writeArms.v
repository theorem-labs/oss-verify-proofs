(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 339 of its 386 lines of code are new or changed and 544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeArmsD.v, with its module names changed; 21 of its 58 lines of code are new or changed and 349 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: the MID obligation (cut interface lib/A/Prog/model_writeDefs.v)
   from the EXIT and SEND ones, by the case split the code makes at +0x124..+0x140 on the Pre's two strings:
     name NULL                          model_writeArmsB.v mw_arm_name_null    (-22)
     alias NULL                         model_writeArmsB.v mw_arm_alias_null   (-22)
     name empty                         model_writeArmsB.v mw_arm_name_empty   (-22)
     name non-empty, alias a C string   model_writeArmsC.v mw_to_len (wrapper_strlen) and model_writeArmsD.v mw_len
                                        (-36 if |alias| >= 256, index_of, -19 if the index is 0, else the SEND cut)

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeArmsB model_writeArmsC model_writeArmsD.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis LV : LinkVals.
(* wrapper_strlen (0x43044): lib/A/Rt/RtClosed.v cmd_strlen_closed *)
Hypothesis STRLEN : RtString.astrlen_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strlen).
(* index_of (0x86784): index_of_c.v, at every rlo rhi *)
Hypothesis IDX : forall rlo rhi, index_of_acontract SK SEGS rlo rhi B.

Theorem mw_mid : mw_exit_obl SK B -> mw_send_obl SK B -> mw_mid_obl SK B.
Proof.
  intros EXIT SEND cx fpos ly3 S3 W3 ms3 md3 HPX HMID.
  pose proof HPX as (_ & _ & HP).
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & HNM0 & HAL0 & _).
  destruct nm0 as [sn|].
  2: { cbn in HNM0. exact (mw_arm_name_null SK B LAWS TB HSEGS EXIT cx fpos ly3 S3 W3 ms3 md3 HPX HMID HNM0). }
  cbn in HNM0. destruct HNM0 as (Hn0 & Hcs).
  destruct al0 as [sa|].
  2: { cbn in HAL0.
       exact (mw_arm_alias_null SK B LAWS TB HSEGS EXIT cx fpos ly3 S3 W3 ms3 md3 sn HPX HMID Hn0 Hcs HAL0). }
  cbn in HAL0. destruct HAL0 as (Ha0 & Hca).
  destruct sn as [|b sn'].
  - exact (mw_arm_name_empty SK B LAWS TB HSEGS EXIT cx fpos ly3 S3 W3 ms3 md3 sa HPX HMID Hn0 Hcs Ha0 Hca).
  - exact (mw_to_len SK B LAWS TB HSEGS STRLEN (mw_len SK B LAWS TB HSEGS LV IDX EXIT SEND)
             cx fpos ly3 S3 W3 ms3 md3 (b :: sn') sa HPX HMID Hn0 Hcs ltac:(discriminate) Ha0 Hca).
Qed.

End b.
End a.
