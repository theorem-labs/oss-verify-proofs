(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState NodesM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition vmaps (mo : Model) : list (word * word) := vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo).
Definition sizes_le (B : Z) (l : list (word * word)) : Prop := Forall (fun p => bv_unsigned (snd p) <= B) l.

Record room (mo : Model) (j : Z) : Prop := ROOM {
  rm_size  : sizes_le (2 ^ 30) (vmaps mo);
  rm_count : Z.of_nat (length (vmaps mo)) <= 100 + 64 * j;
  rm_live  : vm_live_bytes (m_vmmaps mo) <= (2 ^ 26 + 2 ^ 20) * (j + 1);
  rm_limit : 2 ^ 31 <= vm_limit (m_vmmaps mo) }.

Lemma room_frame : forall mo mo' j, m_vmmaps mo' = m_vmmaps mo -> room mo j -> room mo' j.
Proof. intros mo mo' j E [A B C D]; constructor; unfold vmaps in *; rewrite ?E; assumption. Qed.

Lemma room_mono : forall mo j j', 0 <= j <= j' -> room mo j -> room mo j'.
Proof. intros mo j j' Hj [A B C D]; constructor; try assumption; nia. Qed.
