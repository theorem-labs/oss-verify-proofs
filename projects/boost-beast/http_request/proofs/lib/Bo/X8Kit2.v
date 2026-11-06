(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr CellsX TacX Frame StoreDj.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 N8Kit N8Kit2 N8Kit3 X8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac slia ::= first [ exact I | dj_lia | split; [dj_lia| exact I] ].

Ltac dj_get A2 s2 A S k ::=
  lazymatch goal with
  | DJ : chunk_disj A2 s2 A S |- _ => k DJ
  | _ : chunk_nodj A2 s2 A S |- _ => fail
  | _ =>
      let DJ := fresh "DJc" in
      first [ assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; simpl_arr_sizes; simpl_sizes; dj_lia)
            | pose proof (I : chunk_nodj A2 s2 A S) as DJ; fail ];
      k DJ
  end.
Ltac dj_ensure A2 s2 A S ::=
  lazymatch goal with
  | _ : chunk_disj A2 s2 A S |- _ => idtac
  | _ : chunk_nodj A2 s2 A S |- _ => idtac
  | _ => let DJ := fresh "DJc" in
         first [ assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; simpl_arr_sizes; simpl_sizes; dj_lia)
               | pose proof (I : chunk_nodj A2 s2 A S) as DJ ]
  end.

Ltac tc1_orig_rw segs m a bs H A2 cs2 ::=
  first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a "(seed the pair with dj_seed, or provide/unhide the separation fact)" ].
Ltac tc1_orig_ro segs m a bs H A2 cs2 ::=
  first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a ].
Ltac tc1_orig_ba segs m a bs H A2 bs2 ::=
  first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a ].
Ltac tc1_orig_u8 segs m a bs H A2 xs ::=
  first [ apply (u8arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a ].
Ltac tc1_orig_u32 segs m a bs H A2 xs ::=
  first [ apply (u32arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a ].
Ltac tc1_orig_u64 segs m a bs H A2 xs ::=
  first [ apply (u64arr_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a ].
Ltac tc1_orig_u8ro segs m a bs H A2 xs ::=
  first [ apply (u8ro_frame segs m A2 xs a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
        | fail 100 "A8: chunk" H "not separable from the store at" a ].
