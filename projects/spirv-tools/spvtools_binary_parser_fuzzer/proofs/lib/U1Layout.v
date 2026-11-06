(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SEGS := Ubsan.M.loaded_segments.

Definition L : Layout := {|
  ly_malloc      := 0xd3e38;
  ly_free        := 0xd3cf8;
  ly_new         := 0xe7b34;
  ly_new_arr     := 0xe7b34;
  ly_delete      := 0x6f8c8;
  ly_delete_arr  := 0x6f8d0;
  ly_new_handler := 0x100280;
  ly_oom_spin    := 0;
  ly_gp          := 0x10800;
  ly_tp          := 0x102418;
  ly_errno_off   := -164;
  ly_img         := [(0x10000, 0x124000)];
  ly_rw          := [(0xef000, 0x124000)];
  ly_relro       := [(0xe8000, 0xef000)];
  ly_rw_img      := ltac:(intros a (lo & hi & Hin & Hr); exists 0x10000, 0x124000; cbn in Hin; destruct Hin as [E|[]]; injection E as <- <-; split; [left; reflexivity|lia]);
  ly_errno_rw    := ltac:(intros a Ha; exists 0xef000, 0x124000; split; [left; reflexivity|cbn in Ha; lia])
|}.

Definition GET_NEW_HANDLER : Z := 0x6f9f0.
Definition GOT_NEW_HANDLER : Z := 0xeece0.
Definition MALLOC_IMPL : Z := 0xd4aa8.
Definition FREE_IMPL   : Z := 0xd411c.
