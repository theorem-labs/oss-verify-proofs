(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the three proofs are those of proofs/cgif/cgif_file_fuzzer/lib/ErrnoApartScgif.v
   (a working branch ad994c271653) at plugin-hostd/fuzz_reply's image A, with reply A's names. *)
(* Reply image row img-errnoimgs-A (a Theorem Labs lane pool 14): the secondary path's errno image facts at reply A, the three
   fields of the cf layer's [ErrnoImgSCf] beyond its base record (YGcfInstErrnoS.v: eis_dzone_s / eis_shadow_s /
   eis_zone3_s), each as a CLOSED lemma over reply A's TfibSyms and its image classes.
   rule 24: no function proved (kind: interface-instance discharge: errno's secondary image facts).

   The reply tree carries no ErrnoApartS.v, so each statement is the UNFOLDED text of the cf Definition it equals:
   - errno_apart_dzone_s_A  = ErrnoApartS.errno_apart_dzone_s  (ErrnoApartS.v, Definition errno_apart_dzone_s);
   - errno_apart_shadow_s_A = ErrnoApartS.errno_apart_shadow_s (ErrnoApartS.v, Definition errno_apart_shadow_s);
   - errno_apart_zone3_s_A  = ErrnoApartS.errno_apart_zone3_s  (ErrnoApartS.v, Definition errno_apart_zone3_s);
   each at IM := AImg_reply (AGif2reply) and IMS := AImgS_reply (AGif4reply).

   Reply A's values: errno is TFIB_ERRNO = 0x5d93cc (AF0m.v:22, ts_errno), 4 bytes;
   - ims_dzone = AGjm.DZONE (AGif4reply.v, AGjm.v:572-573): [0x177f88, 0x5c8710), which ends 0x10cbc below errno, then
     the nodes block and the store block, owned extents apart from errno by ErrnoApart.errno_apart_owned with
     ErrnoApartreply.errno_in_img_reply;
   - ims_shb = AGjm.SHBv = 0x7fff8000 (AGjm.v:164), above errno;
   - ims_zone3 = AF0x.zone3: off the image (AF0x.zone3_off_img, AF0x.v:73), while errno lies in
     [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x5fb000) (AF0x.v:37, :25).

   Require hazard (as ErrnoApartS.v's header): AGif4reply's closure reaches AGif4 and through it YA08 / YA09 / YA0e,
   whose non-local Zify flag setting escapes Require.  The proofs below use lia over linear facts only. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ErrnoApart ErrnoApartreply.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* = ErrnoApartS.errno_apart_dzone_s at AImg_reply / AImgS_reply: errno is apart from the secondary walk's depot zone. *)
Lemma errno_apart_dzone_s_A :
forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B ly a TS LY IMG Hd. destruct Hd as [Hd|[Hd|Hd]].
- rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia.
- exact (errno_apart_owned errno_in_img_reply B ly (ly_NB ly, kNodesBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; left; reflexivity) Hd).
- exact (errno_apart_owned errno_in_img_reply B ly (ly_SB ly, kStoreBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity) Hd).
Qed.

(* = ErrnoApartS.errno_apart_shadow_s at AImgS_reply: errno lies below the shadow offset. *)
Lemma errno_apart_shadow_s_A :
forall B a, im_syms B -> ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros B a TS Ha. change (0x7fff8000 <= a) in Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.

(* = ErrnoApartS.errno_apart_zone3_s at AImgS_reply: errno lies in no kernel-granted application zone. *)
Lemma errno_apart_zone3_s_A :
forall B x sz a, im_syms B -> ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B x sz a TS Hz Ha. pose proof (zone3_off_img x sz a Hz Ha) as O. rewrite (ts_errno B TS).
unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in *. lia.
Qed.

End a.
