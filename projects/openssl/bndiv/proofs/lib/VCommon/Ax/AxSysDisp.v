(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxState AxSys AxOcc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Definition sys_fresh (A : AST) : bool := negb (state_occ (am_next (a_model A)) A).

Lemma sys_fresh_spec (A : AST) : sys_fresh A = true -> state_occ (am_next (a_model A)) A = false.
Proof. unfold sys_fresh. intros H. apply negb_true_iff in H. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition sys_disp (LIM : Z) (A : AST) : option (list AST) :=
  if pc_ok (npc A) then
    match xlit (aget (a_regs A) 17%uint63) with
    | Some 96 => if sys_fresh A then sys_set_tid A else None
    | Some 222 =>
        match null_shape A with
        | Some _ => if sys_fresh A then sys_mmap_null segs LIM A else None
        | None => sys_mmap_noreplace segs A
        end
    | _ => None
    end
  else None.

End WithSegs.
