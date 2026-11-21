(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE3m.v, with its module paths changed, names TfibSyms -> GrantSyms and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the decimal addresses FMT_d + 2 and + 3 are fuzz_decode.asan's 83953 and 83954, and BUFEND is 6244456 (stdout's buffer 0x5f4468 + 1024). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AE3m.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE3m.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0k YK0s YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w YA0m_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v AE34 AF0l AE3e.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import AE3f_w AE3g_w AE6g_w AE2p_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AE3i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import AE3h_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import AE22_w AF0x_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AE20.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import AE2y_w AE7f_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {rc : YM05.RunCeil}.
Lemma seg_rom_none_band : forall a, in_band_rw a -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha. apply AF0x_w.seg_rom_none_off. unfold AF0x_w.off_img, AF0x_w.TFIB_IMG_LO, AF0x_w.TFIB_IMG_END.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
Qed.
Definition F_STDOUT : Z := 0x9d400.
Definition STDOUT_BUFA : Z := 0x5f4468.
Definition STDOUT_BSZ : Z := 1024.
Definition stdout_fields0 : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x8dc1c); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x8e76c); (80, 8%N, 0x8dd60); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 10);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stdout_fields1 : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x8dc1c); (32, 8%N, STDOUT_BUFA + STDOUT_BSZ); (48, 8%N, 0);
(56, 8%N, STDOUT_BUFA); (64, 8%N, 0); (72, 8%N, 0x8dd68); (80, 8%N, 0x8dd60); (88, 8%N, STDOUT_BUFA); (96, 8%N, STDOUT_BSZ);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 1); (128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 4%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition ofile_is (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem tfibsegs m (F_STDOUT + o) (N.to_nat n) v end) flds.
Definition stdout_pristine : (word -> option byte) -> Prop := ofile_is stdout_fields0.
Definition stdout_mid (wp : Z) (m : word -> option byte) : Prop :=
ofile_is stdout_fields1 m /\ val_mem tfibsegs m (F_STDOUT + 40) 8 wp.
Definition fo_chunks (flds : list (Z * N * Z)) : list YP09.chunk :=
map (fun f => match f with (o, n, v) => YP09.mkChunk (F_STDOUT + o) (CVal n (SLit v)) end) flds.
Definition vo_file (a : Z) : Prop := F_STDOUT <= a < F_STDOUT + FILE_SZ.
Lemma stdout_img_bytes_ok : zallb (img_byte_ok tfibsegs) F_STDOUT (Z.to_nat FILE_SZ) = true.
Proof. vm_compute. reflexivity. Qed.
Section VO.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Variable mut : Z -> Prop.
Definition VO (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ mut a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
End VO.
End g.
