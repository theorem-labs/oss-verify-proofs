(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad STree Malloc MallocCtrl Prog ProgDetIface ProgDetLogic ProgDetNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint oktree {R} (t : stree ev Z R) (P : R -> Prop) : Prop :=
  match t with
  | SRet r => P r
  | SVis e k =>
      match e with
      | EUndef _ | EPeek _ _ _ => True
      | EMmap _ _ _ flags =>
          if Z.land flags MAP_FIXED =? 0 then forall z, is_err z = false -> oktree (k z) P
          else forall z, oktree (k z) P
      | EMprotect _ _ _ => oktree (k 0) P
      | _ => forall z, oktree (k z) P
      end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Walk.
Context {R : Type}.
Variable P : R -> Prop.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section AllocGroup.
Variable lay : layout_hook.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis Hrec : forall st sc req k bail,
  (forall st' idx, 0 <= idx -> oktree (k st' idx) P) -> oktree (rec st sc req k bail) P.

(* [comment removed for export] *)
End AllocGroup.

(* [comment removed for export] *)

(* [comment removed for export] *)

End Walk.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fstable (K : assnE PState) : Prop :=
  forall s mo tr s' mo', K s mo tr -> ps_so s' = ps_so s -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> K s' mo' tr.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Embed.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

(* [comment removed for export] *)

(* [comment removed for export] *)

End Embed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Raw.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

(* [comment removed for export] *)

(* [comment removed for export] *)

End Raw.
