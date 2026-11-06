(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for plugin-hostd/fuzz_reply's ASan image (a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record) row
   img-vis-A): the three visibility facts the cf layer takes as Section hypotheses, YGcfInstSec.v:359-360 COMB_VIS,
   :736-737 ERRNO_VIS and :380-382 DEP_UNHID (cgif_file_fuzzer @ 4c2fd365d8e), proved as closed lemmas over the reply
   image's symbol table, in the pattern of cgif's discharge (rw_view, YB1h.tfib_rw_window; YFff.rw_unhidden). *)
(* Every address these facts name lies in the image's writable window [0x9d000, 0x5fb000): the combined stats words at
   TFIB_INST + o_comb_stats = 0xa2d08 (40 bytes), errno at TFIB_ERRNO = 0x5d93cc (4 bytes), the depot from TFIB_DEPOT =
   0x187f98 to 0x187f98 + d_map1 + 8 * 32768 = 0x5c7fa8, and the store at TFIB_STORE = 0x177f88 (64 bytes).  There the
   segment table has a byte at every address (AB13.tfib_rw_rom), so mbyte's fall-back to seg_rom makes every view Some
   whatever the hidden set and the memory; and no world hides such a byte (AFff.rw_unhidden). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB13 AFff.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
Import ListNotations.
Open Scope Z_scope.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the image's writable window: every view of an address there is a byte *)
Lemma reply_win_view : forall (H : word -> bool) (mem : word -> option byte) a,
  0x9d000 <= a < 0x5fb000 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. change im_segs with tfibsegs. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
pose proof (tfib_rw_rom a Ha) as R.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [discriminate|contradiction].
Qed.

Variable B : asyms.
Hypothesis TB : TfibSyms B.

(* YGcfInstSec.v:359-360 COMB_VIS: the combined allocator's stats words are image bytes no world hides *)
Lemma comb_vis_A : forall (H : word -> bool) (mem : word -> option byte) a,
  as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_inst B TB) in Ha. unfold TFIB_INST, o_comb_stats in Ha.
apply reply_win_view. lia.
Qed.

(* YGcfInstSec.v:736-737 ERRNO_VIS: errno's four bytes are visible *)
Lemma errno_vis_A : forall (H : word -> bool) (mem : word -> option byte) a,
  as_errno B <= a < as_errno B + 4 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_errno B TB) in Ha. unfold TFIB_ERRNO in Ha.
apply reply_win_view. lia.
Qed.

(* YGcfInstSec.v:380-382 DEP_UNHID: the depot's image bytes are never hidden *)
Lemma dep_unhid_A : forall (W : world im_segs) a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. rewrite (ts_depot B TB), (ts_store B TB) in Ha. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
apply (rw_unhidden W a). lia.
Qed.

End v.
