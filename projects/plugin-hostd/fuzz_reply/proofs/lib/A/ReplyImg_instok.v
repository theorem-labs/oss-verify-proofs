(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; image row img-instok-A).
   rule 24: no function proved (kind: measurement; an image row, a closed computation at reply's image A,
   fuzz_reply.asan, pin 42c58610e125).

   The cf layer states this row as a Hypothesis of the Hit and Sec layers and as a Definition of lane F2a, over their
   own Section contexts; reply has not taken those layer files yet.  So each Lemma below states the layer text
   VERBATIM at reply's instance (the image classes ImgBase.AImg at AImg_reply, A/AGif2reply.v:23; ImgBaseAG.AGImg at
   AGImg_reply, A/AGif0reply.v:116; ImgBaseDG.DImg at DImg_reply, A/DGif0reply.v:30), for a B with the image's symbol
   facts (each layer's Section has `Variable B : asyms` and the unit's B satisfies im_syms), and a consumer closes the
   layer's row with `exact` once the layer is on reply.  No Definition of the layer is copied here.

   The cf texts:
   - Hit, YGcfInstHit.v:169-170 (a working branch ee95275bccb; :161 at d2e17f315ba, the text a Theorem Labs lane's
     CF-UNIT-HYPS.md:49 (sha256 77b3f94c95d2; internal record) names in place of the Hit layer's earlier HIOK, `IOK inst -> ag_inst_ok inst`), in
     `Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}
     {AG : AGImg}. ... Section b. Variable B : asyms.`:
       (* the binary's allocator object is in AGImg's instance window *)
       Hypothesis INST_AG : ag_inst_ok (as_inst B).
   - Sec, YGcfInstSec.v:1345-1346 (a working branch 8aea1d52068; it replaced Sec's IOK_AG of :1281 at 4c2fd365d8e,
     `Hypothesis IOK_AG : forall inst, IOK inst -> ag_inst_ok inst.`, in b81e8b96881):
       (* The symbol table's instance object is in AGImg's instance window [cgif: AGif0cgif.inst_ok at TFIB_INST]. *)
       Hypothesis INST_AG : ag_inst_ok (as_inst B).
   - F2a, YGcfInstFreeModel.v:43-44 (a working branch 89caf2ed683), in `Section a. Context {fx : YK11.FPState}
     {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}. ... Variable B : asyms.`:
       (* DImg accepts the symbol table's instance object (cgif: DGif1.inst_cgif). *)
       Definition FM_INST_OK : Prop := dg_inst_ok (as_inst B).
   cgif's discharges: YGcfInstHitcgif.v:115-119 INST_AG_cgif (a working branch, file at cc4fb1f2a13); DGif1.v:2162-2163
   inst_cgif (a working branch 89caf2ed683), `unfold inst_ok, TFIB_INST. lia`.

   Proof at image A: both class fields are AGif0reply.inst_ok (A/AGif0reply.v:58, `0x9f878 <= inst /\ inst + 0xe60 <=
   0xa38e0 /\ inst mod 8 = 0`; AGImg_reply's ag_inst_ok, :116, and DImg_reply's dg_inst_ok, A/DGif0reply.v:31), and
   ts_inst (A/AF0m.v:870) gives as_inst B = TFIB_INST = 0xa2a58 (A/AF0m.v:17): 0x9f878 <= 0xa2a58, 0xa2a58 + 0xe60 =
   0xa38b8 <= 0xa38e0, and 0xa2a58 mod 8 = 0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
(* Qualified, as AGif0reply.v takes ImgBaseAG: importing them would hide AGis's geometry names behind the copies. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ImgBaseAG ImgBaseDG AGif0reply DGif0reply.
Open Scope Z_scope.

(* INST_AG at image A (the Hit / Sec layers' Hypothesis INST_AG): the instance object is in AGImg's instance window. *)
Lemma inst_ag_A : forall B, @im_syms AImg_reply B -> @ImgBaseAG.ag_inst_ok AImg_reply AGif0reply.AGImg_reply (as_inst B).
Proof.
intros B TS. change (TfibSyms B) in TS. change (AGif0reply.inst_ok (as_inst B)).
rewrite (ts_inst B TS). unfold AGif0reply.inst_ok, TFIB_INST.
split; [lia | split; [lia | reflexivity]].
Qed.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* FM_INST_OK at image A (the F2a layer's YGcfInstFreeModel.FM_INST_OK, unfolded): DImg accepts the instance object. *)
Lemma fm_inst_ok_A : forall B, @im_syms AImg_reply B -> ImgBaseDG.dg_inst_ok (DImg := DGif0reply.DImg_reply) (as_inst B).
Proof.
intros B TS. change (TfibSyms B) in TS. change (AGif0reply.inst_ok (as_inst B)).
rewrite (ts_inst B TS). unfold AGif0reply.inst_ok, TFIB_INST.
split; [lia | split; [lia | reflexivity]].
Qed.

End rows.
