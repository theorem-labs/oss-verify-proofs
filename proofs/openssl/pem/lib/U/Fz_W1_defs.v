(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition bufmem_cells (len data max : Z) (flw : word) : list cell := [C8 (wz len); C8 (wz data); C8 (wz max); C8 flw].

(* [comment removed for export] *)
Definition bio_w1_cells (isw : word) (fl : Z) (rrw numw padw ptrw : word) : list cell := [C8 isw; C4 (wz fl); C4 rrw; C4 numw; C4 padw; C8 ptrw].

(* [comment removed for export] *)
Definition fl_ok (fl : Z) : Prop := 0 <= fl < 2 ^ 31 /\ Z.land fl 512 = 0.

Lemma fl_ok_0 : fl_ok 0.
Proof. split; [lia | reflexivity]. Qed.

Lemma t_lor_bound : forall a b n, 0 < n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)); lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [exact Hn| apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [->|]; [exact Hn| apply Z.log2_lt_pow2; lia].
Qed.

Lemma fl_ok_lor : forall fl c, fl_ok fl -> 0 <= c < 2 ^ 31 -> Z.land c 512 = 0 -> fl_ok (Z.lor fl c).
Proof.
  intros fl c [R H] Rc Hc. split; [apply t_lor_bound; lia|].
  rewrite Z.land_lor_distr_l, H, Hc. reflexivity.
Qed.

Lemma fl_ok_land : forall fl c, fl_ok fl -> 0 <= c -> fl_ok (Z.land fl c).
Proof.
  intros fl c [R H] Rc. split.
  - split; [apply Z.land_nonneg; lia|].
    destruct (Z.eq_dec (Z.land fl c) 0) as [E|NE]; [rewrite E; lia|].
    apply Z.log2_lt_pow2; [pose proof (proj2 (Z.land_nonneg fl c) ltac:(lia)); lia|].
    pose proof (Z.log2_land fl c ltac:(lia) Rc) as LL.
    destruct (Z.eq_dec fl 0) as [->|NF]; [rewrite Z.land_0_l in NE; lia|].
    pose proof (proj1 (Z.log2_lt_pow2 fl 31 ltac:(lia)) ltac:(lia)). lia.
  - rewrite <- Z.land_assoc, (Z.land_comm c 512), Z.land_assoc, H. reflexivity.
Qed.

Section Reps.
Context (m : mem) (LBall : list block) (L : @clist bptr).

(* [comment removed for export] *)
Definition bufmem_rep (pb : bptr) (bm len max : Z) (flw : word) (dopt : option (bptr * Z)) : Prop :=
  cown LBall L pb bm 32 32 /\ 0 <= len <= max /\ max < 2 ^ 31 /\
  match dopt with
  | None => max = 0 /\ rw_cells usegs m bm (bufmem_cells 0 0 0 flw)
  | Some (pd, D) => exists nm junk, cown LBall L pd D max nm /\ rw_cells usegs m bm (bufmem_cells len D max flw) /\ rw_cells usegs m D [CB (Z.to_nat max) junk]
  end.

(* [comment removed for export] *)
Definition membio_rep (pbb : bptr) (bb : Z) (pb : bptr) (bm : Z) (pr : bptr) (rp len max : Z) (flw : word) (dopt : option (bptr * Z)) (off : Z) : Prop :=
  cown LBall L pbb bb 16 16 /\ rw_cells usegs m bb [C8 (wz bm); C8 (wz rp)] /\ bufmem_rep pb bm len max flw dopt /\ cown LBall L pr rp 32 32 /\ 0 <= off <= len /\
  rw_cells usegs m rp (match dopt with None => bufmem_cells 0 0 0 flw | Some (_, D) => bufmem_cells (len - off) (D + off) (max - off) flw end).
End Reps.
