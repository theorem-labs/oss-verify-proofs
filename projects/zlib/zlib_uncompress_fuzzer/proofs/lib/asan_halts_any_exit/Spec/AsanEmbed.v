(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree AsanCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition ASHOFF : Z := 0x7fff8000.
Definition shad (a : Z) : Z := ASHOFF + Z.shiftr a 3.
Definition shlen (L : Z) : Z := Z.shiftr L 3.

Definition adec_mmap (atop len prot : Z) (rsp : resp) : option Z :=
  match (if prot =? 0 then dec_mmap_none atop len [] rsp else dec_mmap atop len [] rsp) with
  | Some (MmOk x) => Some x
  | _ => None
  end.
Definition adec_munmap (addr len : Z) (rsp : resp) : option Z :=
  match dec_munmap addr len rsp with Some (RgDone _) => Some 0 | _ => None end.
Definition adec_mprotect (addr len : Z) (rsp : resp) : option Z :=
  match dec_mprotect addr len rsp with Some (RgDone _) => Some 0 | _ => None end.
Definition adec_raw (rsp : resp) : option Z := Some (bv_unsigned (eff_ret rsp)).

Definition aev_tree (atop : Z) (e : aev) : itree node (exc Z) :=
  match e with
  | AMmap a l p f => enode (NMmap a l p f) (adec_mmap atop l p)
  | AMunmap a l => enode (NMunmap a l) (adec_munmap a l)
  | AMprotect a l p => enode (NMprotect a l p) (adec_mprotect a l)
  | ABrk req => enode (NBrk req) adec_raw
  | ASetTid _ => enode NSetTid adec_raw
  | AUndef _ => Ret Unr
  end.

Fixpoint aembed (atop : Z) {R} (t : AM R) : itree node (exc R) :=
  match t with
  | SRet r => Ret (Ok r)
  | SVis e k => ebind (aev_tree atop e) (fun z => aembed atop (k z))
  end.

Lemma aembed_ret : forall atop {R} (r : R), aembed atop (SRet r) = Ret (Ok r).
Proof. reflexivity. Qed.
Lemma aembed_vis : forall atop {R} e (k : Z -> AM R), aembed atop (SVis e k) = ebind (aev_tree atop e) (fun z => aembed atop (k z)).
Proof. reflexivity. Qed.
Lemma aembed_undef : forall atop {R} w (k : Z -> AM R), aembed atop (SVis (AUndef w) k) = Ret Unr.
Proof. reflexivity. Qed.
Lemma aembed_aundef_ : forall atop {R} w (k : AM R), aembed atop (aundef_ w k) = Ret Unr.
Proof. reflexivity. Qed.

Lemma aembed_sbind_ret : forall atop {A B} (a : A) (f : A -> AM B), aembed atop (sbind (SRet a) f) = aembed atop (f a).
Proof. reflexivity. Qed.
Lemma aembed_sbind_vis : forall atop {A B} e (k : Z -> AM A) (f : A -> AM B),
  aembed atop (sbind (SVis e k) f) = ebind (aev_tree atop e) (fun z => aembed atop (sbind (k z) f)).
Proof. reflexivity. Qed.
