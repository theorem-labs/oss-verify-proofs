(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit Bs0PlanKit PmKeep PnDecFacts PnMemW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDD.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
Definition saves (R0 : bvmap 5 word) (S r : Z) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) r /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19)))
  /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21)))
  /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))).
(* [comment removed for export] *)
Definition MI (R0 : bvmap 5 word) (S first r : Z) (M : word -> option byte) : Prop :=
  L5.writable RSEGS M (S - 240) 240 /\ L5.writable RSEGS M first 42 /\ L5.img_clear M 65536 749064 /\ saves R0 S r M.
(* [comment removed for export] *)
Definition cell (S : Z) (M : word -> option byte) (i v : Z) : Prop := L5.u32_at RSEGS M (S - 216 + 4 * i) v.
Definition digs (S V : Z) (M : word -> option byte) (k : Z) : Prop := forall i, 9 * k <= i < 36 -> cell S M i (PNDF.dg V i).
Definition zers (S : Z) (M : word -> option byte) (k : Z) : Prop := forall i, 0 <= i < 9 * k -> cell S M i 0.
(* [comment removed for export] *)
Definition sdigs (S : Z) (M : word -> option byte) (z sd : Z) : Prop := forall i, z <= i < z + sd -> exists v, cell S M i v /\ 0 <= v <= 9.

(* [comment removed for export] *)
Definition RB (R0 : bvmap 5 word) (S first sigma : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 240) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 9) = Z_to_bv 64 first /\ getr R (reg 8) = Z_to_bv 64 (first + 42) /\ getr R (reg 18) = Z_to_bv 64 (first + sigma)
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).

(* [comment removed for export] *)
Definition stJ (R0 : bvmap 5 word) (S first sigma vp hi : Z) (R : bvmap 5 word) : Prop :=
  RB R0 S first sigma R /\ getr R (reg 19) = Z_to_bv 64 vp /\ getr R (reg 12) = Z_to_bv 64 hi.
Definition stX (R0 : bvmap 5 word) (S first sigma vp hi lo : Z) (R : bvmap 5 word) : Prop :=
  RB R0 S first sigma R /\ getr R (reg 19) = Z_to_bv 64 vp /\ getr R (reg 12) = Z_to_bv 64 hi /\ getr R (reg 14) = Z_to_bv 64 lo
  /\ getr R (reg 13) = Z_to_bv 64 (hi / 2 ^ 32).
Definition vp_at (M : word -> option byte) (vp lo hi : Z) : Prop := L5.u64_at RSEGS M vp lo /\ L5.u64_at RSEGS M (vp + 8) hi.

(* [comment removed for export] *)
Definition stP (R0 : bvmap 5 word) (S first sigma e z sd d : Z) (R : bvmap 5 word) : Prop :=
  RB R0 S first sigma R /\ bv_unsigned (getr R (reg 10)) = e /\ getr R (reg 11) = Z_to_bv 64 (e - 6176)
  /\ getr R (reg 20) = Z_to_bv 64 (S - 216 + 4 * z) /\ getr R (reg 21) = Z_to_bv 64 sd /\ getr R (reg 12) = Z_to_bv 64 d.
(* [comment removed for export] *)
Definition stQ (R0 : bvmap 5 word) (S first sigma e z sd : Z) (R : bvmap 5 word) : Prop :=
  RB R0 S first sigma R /\ bv_unsigned (getr R (reg 10)) = e /\ getr R (reg 11) = Z_to_bv 64 (e - 6176)
  /\ getr R (reg 20) = Z_to_bv 64 (S - 216 + 4 * z) /\ getr R (reg 21) = Z_to_bv 64 sd.
(* [comment removed for export] *)
Definition stE (R0 : bvmap 5 word) (S ptr : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 240) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4) /\ getr R (reg 9) = Z_to_bv 64 ptr
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).
(* [comment removed for export] *)
Definition stZ (R0 : bvmap 5 word) (S first sigma e : Z) (R : bvmap 5 word) : Prop :=
  RB R0 S first sigma R /\ bv_unsigned (getr R (reg 10)) = e /\ getr R (reg 11) = Z_to_bv 64 (e - 6176).

(* [comment removed for export] *)
Definition CS : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition stR (R0 : bvmap 5 word) (S ptr : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 S /\ getr R (reg 10) = Z_to_bv 64 ptr /\ (forall k, In k CS -> getr R (reg k) = getr R0 (reg k)).

(* [comment removed for export] *)
Definition agree_but (P : Z -> Prop) (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition in_frame (S a : Z) : Prop := S - 240 <= a < S.
Definition in_out (first a : Z) : Prop := first <= a < first + 42.

Lemma agree_but_trans (P Q : Z -> Prop) M1 M2 M3 :
  agree_but P M1 M2 -> agree_but Q M2 M3 -> agree_but (fun a => P a \/ Q a) M1 M3.
Proof. intros A B a Ha Hn. rewrite (B a Ha) by tauto. apply A; tauto. Qed.
Lemma agree_but_weaken (P Q : Z -> Prop) M1 M2 : agree_but P M1 M2 -> (forall a, P a -> Q a) -> agree_but Q M1 M2.
Proof. intros A PQ a Ha Hn. apply A; [exact Ha|]. intros HP. exact (Hn (PQ a HP)). Qed.

Section Facts.
Variables (R0 : bvmap 5 word) (S first r : Z).
Hypothesis FS : 140735332483312 <= S <= 140737488355328.

Lemma MI_xfer M M' : MI R0 S first r M -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> MI R0 S first r M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  split. { apply (PMKP.clear_agree M M' 65536 749064); [|exact IC]. intros i Hi. apply FZ; clear -Hi FS; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; clear -Hi FS; lia| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.

Lemma cell_xfer M M' (P : Z -> Prop) i v : (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, S - 216 + 4 * i <= a < S - 216 + 4 * i + 4 -> ~ P a) -> 0 <= i < 36 -> cell S M i v -> cell S M' i v.
Proof.
  intros FZ NP Hi C. unfold cell in *. apply (PNMW.u32_at_agree RSEGS M M'); [| clear -Hi FS; lia| clear -Hi FS; lia| exact C].
  intros a Ha. apply FZ; [clear -Ha Hi FS; lia| apply NP; exact Ha].
Qed.
End Facts.
End PNSDD.
