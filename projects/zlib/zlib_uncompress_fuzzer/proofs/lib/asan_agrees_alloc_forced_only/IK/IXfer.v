(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import ZStep ZMem ZPrune ZTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
Definition zrng (a n : Z) : Prop := 0 <= a < two64 /\ a + n <= two64.

Lemma zdisj_of_rng : forall a n a' n',
  zrng a n -> zrng a' n' -> (a + n <= a' \/ a' + n' <= a) -> zdisj a n a' n'.
Proof. intros a n a' n' [H1 H2] [H3 H4] H5. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))). Qed.

Lemma zsep_sb : forall b o n o' n',
  ((o + n <=? o') || (o' + n' <=? o))%bool = true -> b + o + n <= b + o' \/ b + o' + n' <= b + o.
Proof. intros b o n o' n' H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left | right]; lia. Qed.
Lemma zsep_sb_l : forall b n o' n',
  ((n <=? o') || (o' + n' <=? 0))%bool = true -> b + n <= b + o' \/ b + o' + n' <= b.
Proof. intros b n o' n' H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left | right]; lia. Qed.
Lemma zsep_sb_r : forall b o n n',
  ((o + n <=? 0) || (n' <=? o))%bool = true -> b + o + n <= b \/ b + n' <= b + o.
Proof. intros b o n n' H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left | right]; lia. Qed.

End FXG.
Ltac zsep_fast :=
  lazymatch goal with
  | |- ?a + ?n <= ?a' \/ ?a' + ?n' <= ?a =>
      lazymatch is_zlit_b n with true =>
      lazymatch is_zlit_b n' with true =>
      lazymatch zbase_off a with (?b, ?o) =>
      lazymatch zbase_off a' with (?b', ?o') =>
        constr_eq b b';
        lazymatch eval cbv in (orb (Z.leb (o + n) o') (Z.leb (o' + n') o)) with
        | true => first [ exact (zsep_sb b o n o' n' eq_refl) | exact (zsep_sb_l b n o' n' eq_refl) | exact (zsep_sb_r b o n n' eq_refl) ]
        end
      end end end end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zsep_overlap :=
  lazymatch goal with
  | |- ?a + ?n <= ?a' \/ ?a' + ?n' <= ?a =>
      lazymatch is_zlit_b n with true =>
      lazymatch is_zlit_b n' with true =>
      lazymatch zbase_off a with (?b, ?o) =>
      lazymatch zbase_off a' with (?b', ?o') =>
        constr_eq b b';
        lazymatch eval cbv in (orb (Z.leb (o + n) o') (Z.leb (o' + n') o)) with false => idtac end
      end end end end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zrng_ensure a' n' :=
  lazymatch goal with
  | _ : zrng a' n' |- _ => idtac
  | _ => try (let Z := fresh "ZRg" in assert (Z : zrng a' n') by (unfold zrng; zlia))
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zxfer_pre a bs :=
  try (let R := fresh "ZRs" in assert (R : zrng a (Z.of_nat (length bs))) by (unfold zrng; zlen_norm; zlia)).
Ltac zxfer_post a :=
  repeat match goal with H : zrng a (Z.of_nat (length _)) |- _ => clear H end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zdisj_x stock :=
  lazymatch goal with
  | |- zdisj ?a ?n ?a' ?n' =>
      lazymatch goal with
      | Ra : zrng a n, Ra' : zrng a' n' |- _ =>
          refine (zdisj_of_rng a n a' n' Ra Ra' _);
          repeat match goal with
          | |- context [Z.of_nat (@length ?A (Z_to_le_bytes ?k ?v))] =>
              let m := eval cbv in (Z.of_nat k) in
              change_no_check (Z.of_nat (@length A (Z_to_le_bytes k v))) with m
          end;
          first [ zsep_fast | (tryif zsep_overlap then fail else first [ zlia | zlen_norm; zlia ]) ]
      | |- _ => stock
      end
  | |- _ => stock
  end.
