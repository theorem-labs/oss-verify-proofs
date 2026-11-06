(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane W, ReallocPrimary.CfW.ReplyEnqReloc): field round 3 adds
   [pf_cells_img_reply], the twin of cgif's YGcfInstErrnocgif.pf_cells_img_cgif (cf-f1 af0289e23fe): Printf's two
   writable image cells (cf_toolname_cell / cf_pfcb_cell, A/CfImgA.v:73 / :77) lie in reply's image A when the static
   part of the unit row (YG0ncf.pf_cells_static_t, proj1 of its per-address conjunction) holds, by the same reading of
   Tfib_owned_static as errb_obj_img_reply. YFf1cf / YFf2cf (round 3) read it. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane W, ReallocPrimary.CfW.ReplyEnqReloc): reply's own twin, at image A
   (fuzz_reply.asan), of CfF1's cgif instance file proofs/cgif/cgif_file_fuzzer/lib/YGcfInstErrnocgif.v (commit
   a8ad57cefdcd, sha256 fd20dacf89b2; internal record), CUT to the one fact the relocated Enqueue room arm (A/YFg4cf.v) reads:
   [errb_obj_img_reply], the errbuf object lies in reply's image A when the unit's image row
   YG0ncf.errb_obj_owned_t holds (round 2: cf-f1 1223f55a2a51).  The cgif file's errno_seg / errno_nstatic witnesses are not taken: no file here
   uses them, and reply's rows img-errnoseg-A / img-errnonst-A are other hands' (REPLY-IMG-ROWS.md sha256 a33a582e3ffd; internal record).
   The proof is the cgif lemma's own script (YGcfInstErrnocgif.v:56-63 at a8ad57cefdcd) over reply's table:
   every range of A/AF0m.v:820 Tfib_owned_static (through the TfibSyms field ts_owned, A/AF0m.v:884) lies in
   [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x5fb000) (A/AF0x.v:37 / :25); lia decides each range of the computed list.
   rule 24: no function proved (kind: instance discharge at reply's image A). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The reply image instance first, as the cgif file takes cgif's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0ncf.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* The errbuf object lies in reply's image A when the unit's image row YG0ncf.errb_obj_owned_t holds (since field round 2
   it is ARmcf's amc_cells_owned; cgif's twin YGcfInstErrnocgif.v at cf-f1 1223f55a2a51): every owned static range of
   image A (Tfib_owned_static) is an image range.  The Enqueue arms' ARmcf builders keep the amc_errb_cells field
   through it (the walk writes nothing in the image). *)
Theorem errb_obj_img_reply : YG0ncf.errb_obj_owned_t B ->
forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> TFIB_IMG_LO <= a < TFIB_IMG_END.
Proof.
intros HEO a Ha. pose proof (HEO a Ha) as O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_IMG_LO, TFIB_IMG_END.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.

(* Printf's two writable image cells (field round 3: ARmcf's amc_pf_cells) lie in reply's image A when the static part
   of the unit's row (YG0ncf.pf_cells_static_t, the first conjunct of pf_cells_owned_t) holds, by the same reading of
   Tfib_owned_static; the Enqueue arms' ARmcf builders keep the amc_pf_cells field through it. The twin of cgif's
   YGcfInstErrnocgif.pf_cells_img_cgif (cf-f1 af0289e23fe), whose script this is. *)
Theorem pf_cells_img_reply : YG0ncf.pf_cells_static_t B ->
forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
TFIB_IMG_LO <= a < TFIB_IMG_END.
Proof.
intros HPO a Ha. pose proof (proj1 (HPO a Ha)) as O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_IMG_LO, TFIB_IMG_END.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.
End a.
