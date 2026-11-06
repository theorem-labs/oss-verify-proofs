(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_errnoimgs.v (commit 4d286b2e618d, file sha256 7cc6de4868cd) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 3 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ErrnoApartScgif.v (commit cadcb4a0f83,
   ; file sha256 d5e52a0422bd) onto plugin-hostd/fuzz_reply's asan-ubsan image (image B;
   unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61): module paths lib.B / lib.Reusable, the cgif instances
   AImg_cgif / AImgS_cgif replaced by AImg_cgif (AGif2cgif.v) / AImgS_cgif (AGif4cgif.v) and the lemma
   errno_in_img_cgif by the unit's errno_in_img_cgif (ErrnoApartcgif.v:47); no other step changed.
   rule 24: no function proved (kind: image facts: errno's secondary-path image facts at reply image B).

   Row img-errnoimgs-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md (the internal file CF-UNIT-HYPS.md line 37): ErrnoImgSCf's three image facts
   at reply image B.  The reply tree does not carry ErrnoApartS.v (cgif: ErrnoApartS.v:52-59 @ cadcb4a0f83, sha256
   877cb362bcc5) nor the cf record YGcfInstErrnoS.ErrnoImgSCf (YGcfInstErrnoS.v:29-34 @ cadcb4a0f83), so each lemma
   below states the UNFOLDED text of the Prop it discharges, at the reply instances:
   - errno_apart_dzone_s_B  : ErrnoApartS.errno_apart_dzone_s  (ErrnoApartS.v:52-53);
   - errno_apart_shadow_s_B : ErrnoApartS.errno_apart_shadow_s (ErrnoApartS.v:55-56);
   - errno_apart_zone3_s_B  : ErrnoApartS.errno_apart_zone3_s  (ErrnoApartS.v:58-59).
   Each statement is that Definition's body token for token, with IM := AImg_cgif and IMS := AImgS_cgif filled by
   instance search, so once ErrnoApartS.v is in the tree `exact errno_apart_dzone_s_B` closes errno_apart_dzone_s
   (and the same for the other two) by delta.  ErrnoImgSCf's fourth field, eis_base : ErrnoImgCf (YGcfInstErrno.v:62-72),
   is a separate row (img-errnoimg-B); the record at B is {| eis_base := <that row's lemma>; eis_dzone_s :=
   errno_apart_dzone_s_B; eis_shadow_s := errno_apart_shadow_s_B; eis_zone3_s := errno_apart_zone3_s_B |}.

   The image facts used, at image B (all by delta through the reply instances):
   - errno is TFIB_ERRNO = 0x5d994c (YF0m.v:21; ts_errno, a TfibSyms field, YF0m.v:863), 4 bytes;
   - the depot zone ims_dzone = AGjm.DZONE (AGif4cgif.v:29; AGjm.v:573-574): [0x17d5c8, 0x5cdd50), which ends 0x10cbc
     below errno, and the depot's nodes and store blocks, the owned extents 4 and 5 of YG0f.owned_extents (YG0f.v:294-297),
     apart from errno by ErrnoApart.errno_apart_owned with ErrnoApartcgif.errno_in_img_cgif;
   - the shadow offset ImgBaseAGS.SHBv = ims_shb = AGjm.SHBv = 0x7fff8000 (AGif4cgif.v:27; AGjm.v:165), above errno;
   - the grant zones ims_zone3 = YF0x.zone3 (AGif4cgif.v:31; YF0x.v:65): off the image by YF0x.zone3_off_img (YF0x.v:73),
     while errno lies in [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x601000) (YF0x.v:37, :25). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import ErrnoApartcgif.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ErrnoApartS.errno_apart_dzone_s (ErrnoApartS.v:52-53), unfolded, at AImg_cgif / AImgS_cgif. *)
Lemma errno_apart_dzone_s_B :
forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B ly a TS LY IMG Hd. destruct Hd as [Hd|[Hd|Hd]].
- rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia.
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_NB ly, kNodesBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; left; reflexivity) Hd).
- exact (errno_apart_owned errno_in_img_cgif B ly (ly_SB ly, kStoreBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity) Hd).
Qed.

(* ErrnoApartS.errno_apart_shadow_s (ErrnoApartS.v:55-56), unfolded, at AImg_cgif / AImgS_cgif. *)
Lemma errno_apart_shadow_s_B :
forall B a, im_syms B -> ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros B a TS Ha. change (0x7fff8000 <= a) in Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.

(* ErrnoApartS.errno_apart_zone3_s (ErrnoApartS.v:58-59), unfolded, at AImg_cgif / AImgS_cgif. *)
Lemma errno_apart_zone3_s_B :
forall B x sz a, im_syms B -> ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B x sz a TS Hz Ha. pose proof (zone3_off_img x sz a Hz Ha) as O. rewrite (ts_errno B TS).
unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in *. lia.
Qed.

End a.
