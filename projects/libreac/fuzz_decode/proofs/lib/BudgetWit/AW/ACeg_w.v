(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the use-after-return flag at the address the target's GOT word holds, lib_const_addr empty (the target's program reads no GOT word of its own), and the image bounds from the unit's Reusable/YImgTop.v. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/ACeg.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/ACeg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.libreac.fuzz_decode.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v AF0l ACej.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
(* decode: YImgTop COMPUTES IMG_LO / IMG_TOP (the donor states numerals); the body here is the numeral vm_compute
   gives for YImgTop's term (no numeral written), so the donor's `unfold ...; lia` proofs see a number. *)
End c.
