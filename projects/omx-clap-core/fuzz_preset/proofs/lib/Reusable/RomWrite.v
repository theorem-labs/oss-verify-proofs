(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK0i.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: written for LPS 727298f3; the premise lists of write1_rob and write_ch_rob restate those of write1_ok_n and write1_ok_inv in Reusable/YK0i.v. *)
(* Theorem Labs, 2026-11 (LPS 08b1429): a [write] node is robust to a larger read-only
   backing ([RomBase.sys_rob]) when the buffer it writes is readable.

   [YK0i]'s write lemmas characterise every outcome of a [write] on a channel from a
   buffer that [ms_read_bytes] reads in full: the [Ok] outcomes are the prefixes
   ([write1_ok_n], [write1_ok_inv]) and there is no [Unmodeled] ([write1_no_unmodeled]).
   A read that succeeds over a backing succeeds with the same bytes over every larger one
   ([RomBase.ms_read_bytes_wrom]), and the registers do not move, so the same
   characterisation holds there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import RomBase.
Import ListNotations.

Lemma write1_rob : forall segs ms model x8 buf,
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros segs ms model x8 buf Hfd Hsvc Hno Hg Hr Hok Hbm Hnb.
  apply (sys_rob_of_char segs ms model x8
    (fun o => syscall_spec (sys_input segs ms x8) model o) Hsvc).
  intros r Hrom o.
  assert (Hg' : ms_gpr (wrom ms r) 0 = Z_to_bv 64 1) by exact Hg.
  assert (Hr' : ms_read_bytes (wrom ms r) (ms_gpr (wrom ms r) 1) (ms_gpr (wrom ms r) 2) = Some buf)
    by exact (ms_read_bytes_wrom ms r _ _ buf Hrom Hr).
  assert (Hok' : access_okb (ms_gpr (wrom ms r) 1) (bv_unsigned (ms_gpr (wrom ms r) 2)) = true)
    by exact Hok.
  destruct o as [eff m' evs|]; split; intro H.
  - destruct (write1_ok_inv segs (wrom ms r) x8 model eff m' evs buf Hfd Hno Hg' Hr' Hok' Hnb H)
      as (n & Hn1 & Hn2 & -> & -> & ->).
    exact (write1_ok_n segs ms x8 model buf n Hfd Hno Hg Hr Hok Hbm Hn1 Hn2).
  - destruct (write1_ok_inv segs ms x8 model eff m' evs buf Hfd Hno Hg Hr Hok Hnb H)
      as (n & Hn1 & Hn2 & -> & -> & ->).
    exact (write1_ok_n segs (wrom ms r) x8 model buf n Hfd Hno Hg' Hr' Hok' Hbm Hn1 Hn2).
  - exfalso. exact (write1_no_unmodeled segs (wrom ms r) x8 model buf Hfd Hno Hg' Hr' Hbm Hnb H).
  - exfalso. exact (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hbm Hnb H).
Qed.

Lemma write_ch_rob : forall segs ms model fd ch x8 buf,
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sys_rob segs (mkCfg ms model).
Proof.
  intros segs ms model fd ch x8 buf Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb.
  apply (sys_rob_of_char segs ms model x8
    (fun o => syscall_spec (sys_input segs ms x8) model o) Hsvc).
  intros r Hrom o.
  assert (Hg' : ms_gpr (wrom ms r) 0 = fd) by exact Hg.
  assert (Hr' : ms_read_bytes (wrom ms r) (ms_gpr (wrom ms r) 1) (ms_gpr (wrom ms r) 2) = Some buf)
    by exact (ms_read_bytes_wrom ms r _ _ buf Hrom Hr).
  assert (Hok' : access_okb (ms_gpr (wrom ms r) 1) (bv_unsigned (ms_gpr (wrom ms r) 2)) = true)
    by exact Hok.
  destruct o as [eff m' evs|]; split; intro H.
  - destruct (write_ch_ok_inv segs (wrom ms r) x8 model fd ch eff m' evs buf Hfdc H32 Hno Hg' Hr' Hok' Hnb H)
      as (n & Hn1 & Hn2 & -> & -> & ->).
    exact (write_ch_ok_n segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hok Hbm Hn1 Hn2).
  - destruct (write_ch_ok_inv segs ms x8 model fd ch eff m' evs buf Hfdc H32 Hno Hg Hr Hok Hnb H)
      as (n & Hn1 & Hn2 & -> & -> & ->).
    exact (write_ch_ok_n segs (wrom ms r) x8 model fd ch buf n Hfdc H32 Hno Hg' Hr' Hok' Hbm Hn1 Hn2).
  - exfalso. exact (write_ch_no_unmodeled segs (wrom ms r) x8 model fd ch buf Hfdc H32 Hno Hg' Hr' Hbm Hnb H).
  - exfalso. exact (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc H32 Hno Hg Hr Hbm Hnb H).
Qed.
