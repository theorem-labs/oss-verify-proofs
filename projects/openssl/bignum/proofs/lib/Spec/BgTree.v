(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BgState BgWords BgLib BgArith BgMont BgExp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Fuzz.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : bn_ops M ptr.

Local Notation BM := (BM (M:=M) (ptr:=ptr)) (only parsing).
Local Notation "x <- m ;; k" := (bbind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).

Definition pool_fl0 (s : bstate ptr) : bool := forallb (fun b => bn_flags b =? 0) (skipn NFIX (st_bns s)).

Definition BN_CTX_free_g (pc : ptr) : BM unit :=
  fun s => if pool_fl0 s then BN_CTX_free ops pc s else bunr ops s.

Definition fuzz_one_g (data : list Z) : BM Z :=
  p1 <- BN_new ops RB1 ;;
  p2 <- BN_new ops RB2 ;;
  p3 <- BN_new ops RB3 ;;
  p4 <- BN_new ops RB4 ;;
  p5 <- BN_new ops RB5 ;;
  pc <- BN_CTX_new ops ;;
  let '(n1, n2, n3, s1, s3) := bg_split data in
  BN_bin2bn ops n1 RB1 ;;;
  BN_set_negative ops RB1 s1 ;;;
  BN_bin2bn ops n2 RB2 ;;;
  BN_bin2bn ops n3 RB3 ;;;
  BN_set_negative ops RB3 s3 ;;;
  b3 <- bget ops RB3 ;;
  (if is_zero_pure b3 then bret ops tt
   else
     BN_mod_exp ops RB4 RB1 RB2 RB3 ;;;
     BN_mod_exp_simple ops RB5 RB1 RB2 RB3 ;;;
     b4 <- bget ops RB4 ;;
     b5 <- bget ops RB5 ;;
     if cmp_pure b4 b5 =? 0 then bret ops tt
     else bunr ops) ;;;

  BN_free ops RB1 (Some p1) ;;;
  BN_free ops RB2 (Some p2) ;;;
  BN_free ops RB3 (Some p3) ;;;
  BN_free ops RB4 (Some p4) ;;;
  BN_free ops RB5 (Some p5) ;;;
  BN_CTX_free_g pc ;;;

  bret ops 0.

End Fuzz.

Definition bg_one {ptr} (d : list Z) : btree ptr Z :=
  tbind (fuzz_one_g (tree_ops ptr) d st_init) (fun p => TRet (fst p)).

Definition bg_run (d : list Z) : list bevent * nat * option Z := run_tree (bg_one d) 0 [].
