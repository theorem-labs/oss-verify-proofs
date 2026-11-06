(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Module DFact.
  Definition dfact_pack : { f : Prop -> Prop | (forall P : Prop, P -> f P) /\ (forall P : Prop, f P -> P) }.
  Proof. exists (fun P => P). split; intros P H; exact H. Qed.
  Definition dfact : Prop -> Prop := proj1_sig dfact_pack.
  Lemma dfact_in : forall P : Prop, P -> dfact P.
  Proof. exact (proj1 (proj2_sig dfact_pack)). Qed.
  Lemma dfact_out : forall P : Prop, dfact P -> P.
  Proof. exact (proj2 (proj2_sig dfact_pack)). Qed.
  Definition dno_pack : { f : Prop -> Prop | forall P : Prop, f P }.
  Proof. exists (fun _ => True). intros P. exact I. Qed.
  Definition dno : Prop -> Prop := proj1_sig dno_pack.
  Lemma dno_in : forall P : Prop, dno P.
  Proof. exact (proj2_sig dno_pack). Qed.
  Global Opaque dfact dno.
  Global Arguments dfact : simpl never.
  Global Arguments dno : simpl never.
End DFact.
Export DFact.

(* [comment removed for export] *)
Definition dchk (k n SZ : Z) : bool := andb (Z.leb 0 k) (Z.leb (k + n) SZ).
(* [comment removed for export] *)
Definition dchk_sb (c2 s2 c SZ : Z) : bool := orb (Z.leb (c2 + s2) c) (Z.leb (c + SZ) c2).

Lemma dchk_spec : forall k n SZ, dchk k n SZ = true -> 0 <= k /\ k + n <= SZ.
Proof. intros k n SZ H. unfold dchk in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption. Qed.

(* [comment removed for export] *)
Lemma d_lb : forall A S k n, 0 <= A /\ A + S <= 2^64 -> dchk k n S = true -> 0 <= A + k.
Proof. intros A S k n [H1 H2] C. apply dchk_spec in C. lia. Qed.
Lemma d_ub : forall A S k n len, 0 <= A /\ A + S <= 2^64 -> len = n -> dchk k n S = true -> A + k + len <= 2^64.
Proof. intros A S k n len [H1 H2] -> C. apply dchk_spec in C. lia. Qed.

(* [comment removed for export] *)
Lemma d_apart_use : forall A2 sz2 s2 A SZ k n,
  dfact (A2 + s2 <= A \/ A + SZ <= A2) -> sz2 = s2 -> dchk k n SZ = true ->
  A2 + sz2 <= A + k \/ A + k + n <= A2.
Proof. intros A2 sz2 s2 A SZ k n AP -> C. apply dfact_out in AP. apply dchk_spec in C. lia. Qed.
(* [comment removed for export] *)
Lemma d_apart_sb : forall A2 sz2 s2 A SZ X c2 c k n,
  A2 = X + c2 -> A = X + c -> sz2 = s2 -> dchk_sb c2 s2 c SZ = true -> dchk k n SZ = true ->
  A2 + sz2 <= A + k \/ A + k + n <= A2.
Proof.
  intros A2 sz2 s2 A SZ X c2 c k n -> -> -> B C. apply dchk_spec in C. unfold dchk_sb in B.
  apply orb_true_iff in B as [B|B]; apply Z.leb_le in B; lia.
Qed.
(* [comment removed for export] *)
Lemma d_inside_sub : forall W A SZ k n, dfact (inside W A SZ) -> dchk k n SZ = true -> inside W (A + k) n.
Proof.
  intros W A SZ k n IN C. apply dfact_out in IN. apply dchk_spec in C.
  induction W as [|[lo hi] W IH]; cbn [inside] in *; [exact IN|].
  destruct IN as [IN|IN]; [left; lia| right; exact (IH IN)].
Qed.

(* [comment removed for export] *)
Definition dchk_ivl (c2 s2 l h : Z) : bool := orb (Z.leb (c2 + s2) l) (Z.leb h c2).
Lemma d_ivl_use : forall A2 sz2 s2 lo hi,
  dfact (A2 + s2 <= lo \/ hi <= A2) -> sz2 = s2 -> A2 + sz2 <= lo \/ hi <= A2.
Proof. intros A2 sz2 s2 lo hi AP ->. exact (dfact_out _ AP). Qed.
Lemma d_ivl_sb : forall A2 sz2 s2 lo hi X c2 l h,
  A2 = X + c2 -> lo = X + l -> hi = X + h -> sz2 = s2 -> dchk_ivl c2 s2 l h = true -> A2 + sz2 <= lo \/ hi <= A2.
Proof.
  intros A2 sz2 s2 lo hi X c2 l h -> -> -> -> B. unfold dchk_ivl in B.
  apply orb_true_iff in B as [B|B]; apply Z.leb_le in B; lia.
Qed.

(* [comment removed for export] *)
Lemma d_band_sub : forall A SZ k n L U, dfact (A + SZ <= L \/ U <= A) -> dchk k n SZ = true -> A + k + n <= L \/ U <= A + k.
Proof. intros A SZ k n L U B C. apply dfact_out in B. apply dchk_spec in C. lia. Qed.


(* [comment removed for export] *)
Definition dchk_in (l h c n : Z) : bool := andb (Z.leb l c) (Z.leb (c + n) h).
Lemma d_in_sb1 : forall X k n l h lo hi, lo = X + l -> hi = X + h -> dchk_in l h k n = true -> lo <= X + k /\ X + k + n <= hi.
Proof. intros X k n l h lo hi -> -> C. unfold dchk_in in C. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia. Qed.
Lemma d_in_sb2 : forall X c0 k n l h lo hi, lo = X + l -> hi = X + h -> dchk_in l h (c0 + k) n = true -> lo <= X + c0 + k /\ X + c0 + k + n <= hi.
Proof. intros X c0 k n l h lo hi -> -> C. unfold dchk_in in C. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia. Qed.
