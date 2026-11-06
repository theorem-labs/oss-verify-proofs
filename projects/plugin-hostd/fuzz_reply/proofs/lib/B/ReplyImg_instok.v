(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-instok-B of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: measurement; image rows, closed computations at reply's image B,
   fuzz_reply.asan-ubsan pin 10ffb5f9202a).

   The cf layer states this row as a Hypothesis (Hit, Sec) and a Definition (F2a) over its own Section context; reply
   has not taken those layer files yet.  So each Lemma below states the layer text VERBATIM at reply's instances (the
   image class ImgBase.AImg at image B's AImg_reply, B/AGif2reply.v:24; ImgBaseAG.AGImg at AGImg_reply,
   B/AGif0reply.v:117; ImgBaseDG.DImg at DImg_reply, B/DGif0reply.v:31), and a consumer closes the layer's row with
   `exact` once the layer is on reply.  No Definition of the layer is copied here.  The class fields ag_inst_ok and
   dg_inst_ok are on reply (B/ImgBaseAG.v:41, B/ImgBaseDG.v:35); at image B both are AGif0reply.inst_ok
   (B/AGif0reply.v:59: 0x9fdf8 <= inst /\ inst + 0xe60 <= 0xa3e60 /\ inst mod 8 = 0).
   - INST_AG, the Hit layer's YGcfInstHit.v:170 (commit ee95275bccbf; :161 at cc4fb1f2a13 / d2e17f315ba), in Section b
     (Variable B : asyms, :141; Hypothesis TS : im_syms B, :187), and the Sec layer's YGcfInstSec.v:1346 (commit
     8aea1d52068b; Section b, Variable B :353, Hypothesis TS :755), the same text in both:
       Hypothesis INST_AG : ag_inst_ok (as_inst B).
     (It replaced Sec's IOK_AG, YGcfInstSec.v:1281 at commit 4c2fd365d8e, the line CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row 49 cites:
       Hypothesis IOK_AG : forall inst, IOK inst -> ag_inst_ok inst.
     and the unit's IOK_ok, IOK i -> i = as_inst B, gives that form from INST_AG.)
     cgif's discharge: YGcfInstHitcgif.v:115-119 INST_AG_cgif (commit cc4fb1f2a13).
   - FM_INST_OK, the F2a layer's YGcfInstFreeModel.v:44 (commit 89caf2ed6834; Section a, Variable B : asyms, :39):
       Definition FM_INST_OK : Prop := dg_inst_ok (as_inst B).
     (:43 at commit 587da63d252, the line CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row 49 cites, was the IOK form
       Definition FM_INST_OK (IOK : Z -> Prop) : Prop := forall i, IOK i -> dg_inst_ok i.)
     cgif's discharge: DGif1.v:2159-2160 inst_cgif (commit ee95275bccbf), `unfold inst_ok, TFIB_INST; lia`.
   At image B the instance object is TFIB_INST = 0xa2fd8 (B/YF0m.v:16; ts_inst, B/YF0m.v:869): 0x9fdf8 <= 0xa2fd8,
   0xa2fd8 + 0xe60 = 0xa3e38 <= 0xa3e60, and 0xa2fd8 = 8 * 0x145fb. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply AGif0reply DGif0reply.
Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* INST_AG at image B (YGcfInstHit.v:170, YGcfInstSec.v:1346): AGImg_reply's instance window holds the symbol table's
   instance object TFIB_INST = 0xa2fd8 (B/YF0m.v:16). *)
Lemma inst_ag_B : forall B, @im_syms AImg_reply B -> @ag_inst_ok AImg_reply AGImg_reply (as_inst B).
Proof.
intros B TS. change (TfibSyms B) in TS. change (AGif0reply.inst_ok (as_inst B)).
rewrite (ts_inst B TS). unfold AGif0reply.inst_ok, TFIB_INST.
split; [lia | split; [lia | reflexivity]].
Qed.

(* FM_INST_OK at image B (YGcfInstFreeModel.v:44): DImg_reply accepts the symbol table's instance object
   TFIB_INST = 0xa2fd8 (B/YF0m.v:16).  dg_inst_ok's instance is DImg_reply (the one DImg instance in scope); the first
   `change` checks that it is AGif0reply.inst_ok, DImg_reply's field (B/DGif0reply.v:32). *)
Lemma fm_inst_ok_B : forall B, @im_syms AImg_reply B -> dg_inst_ok (as_inst B).
Proof.
intros B TS. change (TfibSyms B) in TS. change (AGif0reply.inst_ok (as_inst B)).
rewrite (ts_inst B TS). unfold AGif0reply.inst_ok, TFIB_INST.
split; [lia | split; [lia | reflexivity]].
Qed.

End rows.
