(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re X1od X1rk.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Record pst : Type := mkP { p_err : list Z }.
Definition p0 : pst := mkP [].
Definition p_app (bs : list Z) (q : pst) : pst := mkP (p_err q ++ bs).

Local Notation PM := (X1qy.M pst).

Definition p_overflows (n : Z) : bool := (2^63 - 1 - 4096 <=? n).

Definition p_malloc (n : Z) : PM (option unit) := mret (if p_overflows n then None else Some tt).

Definition p_calloc (m n : Z) : PM (option unit) :=
if negb (n =? 0) && ((2^64 - 1) / n <? m) then mret None else p_malloc (n * m).

Definition p_realloc (_ : unit) (n : Z) : PM (option unit) := mret (if p_overflows n then None else Some tt).
Definition p_free (_ : unit) : PM unit := mret tt.

Definition notify_bytes (msg : list Z) : list Z := concat (pieces_notify msg).
Definition warning_bytes (msg : list Z) : list Z := concat (pieces_warning msg).
Definition p_notify (msg : list Z) : PM unit := mupd (p_app (notify_bytes msg)).
Definition p_warning (msg : list Z) : PM unit := mupd (p_app (warning_bytes msg)).

Definition prun {A} (c : PM A) (q : pst) : option (A * pst) :=
match c q with Ret (Ok r) => Some r | _ => None end.

Lemma prun_ret {A} (a : A) q : prun (mret a) q = Some (a, q).
Proof. reflexivity. Qed.
Lemma prun_munr {A} q : prun (munr (A:=A)) q = None.
Proof. reflexivity. Qed.
Lemma prun_get q : prun mget q = Some (q, q).
Proof. reflexivity. Qed.
Lemma prun_put q1 q : prun (mput q1) q = Some (tt, q1).
Proof. reflexivity. Qed.
Lemma prun_upd f q : prun (mupd f) q = Some (tt, f q).
Proof. reflexivity. Qed.

Lemma prun_bind {A B} (c : PM A) (f : A -> PM B) q :
prun (mbind c f) q = match prun c q with Some (a, q') => prun (f a) q' | None => None end.
Proof.
unfold prun, mbind. destruct (c q) as [[|[a q']]|n k]; reflexivity.
Qed.

Lemma prun_bind_some {A B} (c : PM A) (f : A -> PM B) q r :
prun (mbind c f) q = Some r <-> exists a q', prun c q = Some (a, q') /\ prun (f a) q' = Some r.
Proof.
rewrite prun_bind. split.
- destruct (prun c q) as [[a q']|]; [|discriminate]. intros H. exists a, q'. split; [reflexivity| exact H].
- intros (a & q' & -> & H). exact H.
Qed.

Lemma prun_some_iff {A} (c : PM A) q r : prun c q = Some r <-> c q = Ret (Ok r).
Proof.
unfold prun. split.
- destruct (c q) as [[|r']|n k]; try discriminate. intros H. injection H as ->. reflexivity.
- intros ->. reflexivity.
Qed.

Lemma prun_malloc n q : prun (p_malloc n) q = Some ((if p_overflows n then None else Some tt), q).
Proof. reflexivity. Qed.
Lemma prun_malloc_ok n q : p_overflows n = false -> prun (p_malloc n) q = Some (Some tt, q).
Proof. intros H. rewrite prun_malloc, H. reflexivity. Qed.
Lemma prun_calloc_ok m n q : 0 <= m -> 0 <= n -> n * m < 2^63 - 1 - 4096 -> prun (p_calloc m n) q = Some (Some tt, q).
Proof.
intros Hm Hn Hp. unfold p_calloc.
assert (E : negb (n =? 0) && ((2^64 - 1) / n <? m) = false).
{ destruct (Z.eqb_spec n 0) as [->|NZ]; [reflexivity|]. cbn [negb andb]. apply Z.ltb_ge.
apply Z.div_le_lower_bound; [lia|]. nia. }
rewrite E. apply prun_malloc_ok. unfold p_overflows. apply Z.leb_gt. exact Hp.
Qed.
Lemma prun_realloc_ok p n q : p_overflows n = false -> prun (p_realloc p n) q = Some (Some tt, q).
Proof. intros H. unfold p_realloc, prun. cbn. rewrite H. reflexivity. Qed.
Lemma prun_free p q : prun (p_free p) q = Some (tt, q).
Proof. reflexivity. Qed.
Lemma prun_notify msg q : prun (p_notify msg) q = Some (tt, p_app (notify_bytes msg) q).
Proof. reflexivity. Qed.
Lemma prun_warning msg q : prun (p_warning msg) q = Some (tt, p_app (warning_bytes msg) q).
Proof. reflexivity. Qed.

Definition p_fuzz_one (payload : list Z) : PM Z :=
LLVMFuzzerTestOneInput p_malloc p_calloc p_realloc p_free p_notify p_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M payload.

Definition canon_fuzz (payload : list Z) : Z * list Z :=
match prun (p_fuzz_one payload) p0 with
| Some (rc, q) => (rc, p_err q)
| None => (0, [])
end.

Lemma canon_fuzz_big payload : MAX_FUZZ_SIZE < zlength payload -> canon_fuzz payload = (0, []).
Proof.
intros H. unfold canon_fuzz, p_fuzz_one, LLVMFuzzerTestOneInput.
replace (MAX_FUZZ_SIZE <? zlength payload) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.
