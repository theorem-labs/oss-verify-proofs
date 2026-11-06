(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec SymExec SymExecFP SymExecFPSound SymCallFP.
Unset Lia Cache.
Import ListNotations.
Import SXF. Import SXFS.

(* [comment removed for export] *)
Fixpoint kfind1_aux (segs : list Segment) (l : list kentry) (b : expr) (k : Z) (n : nat) (i : nat) : option nat :=
  match l with
  | [] => None
  | e :: t => match kread segs [e] b k n with
              | Some _ => Some i
              | None => kfind1_aux segs t b k n (S i)
              end
  end.
Definition kfind1 segs l b k n := kfind1_aux segs l b k n O.

(* [comment removed for export] *)
Ltac kread_rdn_fast segs E M kn b k n v HK H :=
  let oi := eval vm_compute in (kfind1 segs kn b k n) in
  first
    [ lazymatch oi with
      | Some ?i =>
        let oe := eval vm_compute in (nth_error kn i) in
        lazymatch oe with
        | Some ?e =>
          let r1 := eval vm_compute in (kread segs [e] b k n) in
          lazymatch r1 with
          | Some ?v1 =>
            constr_eq v v1;
            let HK1 := fresh "HK1" in let KR := fresh "KR" in
            pose proof (@Forall_cons _ _ e [] (know_nth segs E M kn i e HK eq_refl) (@Forall_nil _ _)
                        : know_ok segs E M [e]) as HK1;
            assert (KR : kread segs [e] b k n = Some v) by (vm_compute; reflexivity);
            pose proof (kread_rdn segs E M [e] b k n v HK1 KR ltac:(lia) ltac:(lia)) as H; clear KR HK1
          end
        end
      end
    | let KR := fresh "KR" in
      assert (KR : kread segs kn b k n = Some v) by (vm_compute; reflexivity);
      pose proof (kread_rdn segs E M kn b k n v HK KR ltac:(lia) ltac:(lia)) as H; clear KR ].
