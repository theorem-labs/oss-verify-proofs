(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ra X1qu X1ri X1r3.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation MP := (X1qx.M PState).

Definition raw_free_opt (p : option bptr) : MP unit :=
match p with Some q => raw_free q | None => mret tt end.

Definition raw_calloc (m n : Z) : MP (option bptr) :=
if negb (n =? 0) && ((2^64 - 1) / n <? m) then mret None
else raw_malloc (n * m).

Definition rtop_known (s : PState) (p : bptr) : Prop := 0 <= snd p.
Lemma rtop_known_ptop s p : rtop_known s p <-> ptop p = true.
Proof. unfold rtop_known, ptop. rewrite Z.leb_le. tauto. Qed.

Definition raw_realloc (p : bptr) (n : Z) : MP (option bptr) :=
if size_overflows n then mret None else
if negb (ptop p) then munr else
s <- mget ;;
let cs := ps_m s in
match (s_slots cs) !! (fst p) with
| None => munr
| Some (g, idx) =>
let mr := get_meta_rec cs g in
let avail := get_stride mr - IB - UNIT * snd p in
if (n <=? avail) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) then mret (Some p)
else if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n) then munr
else
q <- raw_malloc n ;;
match q with
| None => mret None
| Some q => raw_free p ;;; mret (Some q)
end
end.

Lemma raw_calloc_small m n : 0 <= m -> 0 <= n -> n * m < 2^64 -> raw_calloc m n = raw_malloc (n * m).
Proof.
intros Hm Hn Hp. unfold raw_calloc.
destruct (Z.eqb_spec n 0) as [->|NZ]; [reflexivity|]. cbn [negb andb].
destruct (Z.ltb_spec ((2^64 - 1) / n) m) as [LT|GE]; [|reflexivity].
exfalso. assert (Hn' : 0 < n) by lia.
pose proof (Z.mul_succ_div_gt (2^64 - 1) n Hn') as X.
assert (Y : n * (Z.succ ((2^64 - 1) / n)) <= n * m) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma raw_free_opt_none : raw_free_opt None = mret tt.
Proof. reflexivity. Qed.
Lemma raw_free_opt_some q : raw_free_opt (Some q) = raw_free q.
Proof. reflexivity. Qed.
