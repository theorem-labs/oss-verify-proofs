(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA LibIface LibIfaceAB L5Defs L5Core PnTopS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64.
Proof. unfold U. pose proof (bv_unsigned_in_range 64 (getr R (reg k))) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Definition STK : Z := 36864.                          (* [comment removed for export] *)
Definition FRAMES (k : Z) : Z := 14.                  (* [comment removed for export] *)
Definition LEAK (k : Z) : Z := 0.
Definition CREDIT (n : Z) : credit := (PNTS.TOPK, 3 * 2 ^ 30 + 8 * n).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition tfrk (S : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U R 1) /\ L5.u64_at RSEGS M (S - 16) (U R 8) /\ L5.u64_at RSEGS M (S - 24) (U R 9) /\ L5.u64_at RSEGS M (S - 32) (U R 18) /\
  L5.u64_at RSEGS M (S - 40) (U R 19) /\ L5.u64_at RSEGS M (S - 48) (U R 20) /\ L5.u64_at RSEGS M (S - 56) (U R 21) /\ L5.u64_at RSEGS M (S - 64) (U R 22) /\
  L5.u64_at RSEGS M (S - 72) (U R 23) /\ L5.u64_at RSEGS M (S - 80) (U R 24) /\ L5.u64_at RSEGS M (S - 88) (U R 25) /\ L5.u64_at RSEGS M (S - 96) (U R 26).
Definition tocell (S : Z) (a : Z) : Prop := S - 96 <= a < S.
Lemma tfrk_agree S R M1 M1' : 4096 <= S - 96 -> S <= 2 ^ 47 -> tfrk S R M1 -> (forall a, tocell S a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> tfrk S R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold tfrk, tocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

(* [comment removed for export] *)
Definition rinvH (R0 Rc : bvmap 5 word) (V2 cls F : Z) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (V2 - 128) /\ getr Rc (reg 8) = Z_to_bv 64 (V2 + cls) /\ getr Rc (reg 9) = Z_to_bv 64 (V2 - 128) /\
  getr Rc (reg 18) = Z_to_bv 64 F /\ getr Rc (reg 19) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 20) = Z_to_bv 64 (F + 32) /\
  getr Rc (reg 24) = Z_to_bv 64 F /\ getr Rc (reg 25) = Z_to_bv 64 2147450880 /\
  getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4) /\ getr Rc (reg 27) = getr R0 (reg 27).
Definition HIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 27]%nat.
Lemma rinvH_keep R0 Ra Rb V2 cls F : rinvH R0 Ra V2 cls F -> (forall k, In k HIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvH R0 Rb V2 cls F.
Proof.
  intros (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27) KS. unfold rinvH.
  rewrite !KS by (cbn; tauto). repeat split; assumption.
Qed.
Lemma rinvH_ks R0 Ra Rb V2 cls F (KSL : list nat) : rinvH R0 Ra V2 cls F -> (forall k, In k KSL -> getr Rb (reg k) = getr Ra (reg k)) ->
  forallb (fun k => existsb (Nat.eqb k) KSL) HIDX = true -> rinvH R0 Rb V2 cls F.
Proof.
  intros RI KS HB. apply (rinvH_keep R0 Ra Rb V2 cls F RI). intros k Hk. apply KS.
  rewrite forallb_forall in HB. specialize (HB k Hk). apply existsb_exists in HB. destruct HB as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma rinvH_pres R0 Ra Rb V2 cls F : rinvH R0 Ra V2 cls F -> regs_preserved Ra Rb -> rinvH R0 Rb V2 cls F.
Proof.
  intros RI RP. apply (rinvH_keep R0 Ra Rb V2 cls F RI). intros k Hk. apply RP. unfold callee_saved_idx.
  unfold HIDX in Hk. repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.
End PNHAS.
