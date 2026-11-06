(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SEGS := Plain.M.loaded_segments.

Definition L : Layout := {|
  ly_malloc      := 0xd20e0;
  ly_free        := 0xd1fa0;
  ly_new         := 0xe5ddc;
  ly_new_arr     := 0xe5ddc;
  ly_delete      := 0x6db70;
  ly_delete_arr  := 0x6db78;
  ly_new_handler := 0xfe520;
  ly_oom_spin    := 0;
  ly_gp          := 0x10800;
  ly_tp          := 0x1006b8;
  ly_errno_off   := -164;
  ly_img         := [(0x10000, 0x122000)];
  ly_rw          := [(0xee000, 0x122000)];
  ly_relro       := [(0xe6000, 0xee000)];
  ly_rw_img      := ltac:(intros a (lo & hi & Hin & Hr); exists 0x10000, 0x122000; cbn in Hin; destruct Hin as [E|[]]; injection E as <- <-; split; [left; reflexivity|lia]);
  ly_errno_rw    := ltac:(intros a Ha; exists 0xee000, 0x122000; split; [left; reflexivity|cbn in Ha; lia])
|}.

Definition GET_NEW_HANDLER : Z := 0x6dc98.
Definition GOT_NEW_HANDLER : Z := 0xecf88.
Definition MALLOC_IMPL : Z := 0xd2d50.
Definition FREE_IMPL   : Z := 0xd23c4.
