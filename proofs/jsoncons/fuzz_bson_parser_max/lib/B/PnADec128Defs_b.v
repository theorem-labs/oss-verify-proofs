(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5CoreKit L5KnA PnDecFacts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNADD.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition SBv : Z := 2147450880.                      (* [comment removed for export] *)
Definition SH (a : Z) : Z := a / 8 + SBv.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition geom (S first vp F fl : Z) : Prop :=
  140735332483456 <= S <= 140737488355328 /\ S mod 32 = 0
  /\ 4096 <= first <= 140737488355280 /\ first mod 8 = 0 /\ (2147446784 + 17592186048512 <= first \/ first + 48 <= 2147446784)
  /\ (S - 256 + 256 <= first \/ first + 48 <= S - 256) /\ (65536 + 6840320 <= first \/ first + 48 <= 65536)
  /\ 6905856 <= vp <= 140737488355312 /\ vp mod 8 = 0 /\ (2147446784 + 17592186048512 <= vp \/ vp + 16 <= 2147446784)
  /\ (S - 256 + 256 <= vp \/ vp + 16 <= S - 256) /\ (first + 48 <= vp \/ vp + 16 <= first)
  /\ 4096 <= F <= 140737488354816 /\ F mod 32 = 0 /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784)
  /\ (S - 256 + 256 <= F \/ F + 512 <= S - 256) /\ (65536 + 6840320 <= F \/ F + 512 <= 65536)
  /\ (first + 48 <= F \/ F + 512 <= first) /\ (vp + 16 <= F \/ F + 512 <= vp)
  /\ 4096 <= fl <= 140737488355327 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 512 <= fl \/ fl + 1 <= F) /\ (S - 256 + 256 <= fl \/ fl + 1 <= S - 256)
  /\ (first + 42 <= fl \/ fl + 1 <= first) /\ (vp + 16 <= fl \/ fl + 1 <= vp).

(* [comment removed for export] *)
Definition saves (R0 : bvmap 5 word) (S r : Z) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) r /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19)))
  /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21)))
  /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23)))
  /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))) /\ L5.u64_at RSEGS M (S - 88) (bv_unsigned (getr R0 (reg 25)))
  /\ L5.u64_at RSEGS M (S - 96) (bv_unsigned (getr R0 (reg 26))) /\ L5.u64_at RSEGS M (S - 104) (bv_unsigned (getr R0 (reg 27))).

(* [comment removed for export] *)
Definition MIA (R0 : bvmap 5 word) (S first r F fl : Z) (M : word -> option byte) : Prop :=
  L5.writable RSEGS M (S - 256) 256 /\ L5.writable RSEGS M first 42 /\ L5.writable RSEGS M F 512 /\ L5.writable RSEGS M (SH F) 64
  /\ L5.writable RSEGS M fl 1
  /\ L5.img_clear M 1249280 1282048 /\ L5.u64_at RSEGS M 1309752 2147450880 /\ L5.u32_at RSEGS M 1309760 1
  /\ saves R0 S r M /\ L5.u64_at RSEGS M (S - 144) F /\ L5.u64_at RSEGS M (F + 504) fl
  /\ L5KA.zeros_at M (SH first) 6 /\ L5KA.zeros_at M (SH F + 4) 18.

(* [comment removed for export] *)
Definition cell (F : Z) (M : word -> option byte) (i v : Z) : Prop := L5.u32_at RSEGS M (F + 32 + 4 * i) v.
Definition digs (F V : Z) (M : word -> option byte) (k : Z) : Prop := forall i, 9 * k <= i < 36 -> cell F M i (PNDF.dg V i).
Definition zers (F : Z) (M : word -> option byte) (k : Z) : Prop := forall i, 0 <= i < 9 * k -> cell F M i 0.
Definition sdigs (F : Z) (M : word -> option byte) (z sd : Z) : Prop := forall i, z <= i < z + sd -> exists v, cell F M i v /\ 0 <= v <= 9.
Definition vp_at (M : word -> option byte) (vp lo hi : Z) : Prop :=
  L5.u64_at RSEGS M vp lo /\ L5.u64_at RSEGS M (vp + 8) hi /\ L5KA.zeros_at M (SH vp) 2.

(* [comment removed for export] *)
Definition RBA (R0 : bvmap 5 word) (S F : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 256) /\ getr R (reg 23) = Z_to_bv 64 (SH F)
  /\ getr R (reg 26) = Z_to_bv 64 F /\ getr R (reg 27) = Z_to_bv 64 F.
(* [comment removed for export] *)
Definition RBO (R0 : bvmap 5 word) (S F first sigma : Z) (R : bvmap 5 word) : Prop :=
  RBA R0 S F R /\ getr R (reg 19) = Z_to_bv 64 SBv /\ getr R (reg 20) = Z_to_bv 64 first /\ getr R (reg 30) = Z_to_bv 64 (first + sigma).

(* [comment removed for export] *)
Definition stJ (R0 : bvmap 5 word) (S F first sigma vp : Z) (R : bvmap 5 word) : Prop :=
  RBO R0 S F first sigma R /\ getr R (reg 18) = Z_to_bv 64 (F + 32) /\ getr R (reg 24) = Z_to_bv 64 vp
  /\ getr R (reg 10) = Z_to_bv 64 (vp + 8) /\ getr R (reg 11) = Z_to_bv 64 (SH (vp + 8)).
(* [comment removed for export] *)
Definition stX (R0 : bvmap 5 word) (S F first sigma hi lo : Z) (R : bvmap 5 word) : Prop :=
  RBO R0 S F first sigma R /\ getr R (reg 18) = Z_to_bv 64 (F + 32) /\ getr R (reg 11) = Z_to_bv 64 hi /\ getr R (reg 10) = Z_to_bv 64 lo
  /\ getr R (reg 13) = Z_to_bv 64 (hi / 2 ^ 32).
(* [comment removed for export] *)
Definition stZ (R0 : bvmap 5 word) (S F first sigma e : Z) (R : bvmap 5 word) : Prop :=
  RBO R0 S F first sigma R /\ getr R (reg 18) = Z_to_bv 64 (F + 32) /\ Z.land (bv_unsigned (getr R (reg 17))) 16383 = e
  /\ getr R (reg 5) = Z_to_bv 64 16383.
Definition stP (R0 : bvmap 5 word) (S F first sigma e z sd : Z) (R : bvmap 5 word) : Prop :=
  RBO R0 S F first sigma R /\ getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) /\ getr R (reg 13) = Z_to_bv 64 sd
  /\ Z.land (bv_unsigned (getr R (reg 17))) 16383 = e /\ getr R (reg 5) = Z_to_bv 64 16383.
(* [comment removed for export] *)
Definition stE (R0 : bvmap 5 word) (S F ptr ec : Z) (R : bvmap 5 word) : Prop :=
  RBA R0 S F R /\ getr R (reg 24) = Z_to_bv 64 ptr /\ getr R (reg 25) = Z_to_bv 64 ec.
(* [comment removed for export] *)
Definition CS : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition stR (R0 : bvmap 5 word) (S ptr : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 S /\ getr R (reg 10) = Z_to_bv 64 ptr /\ (forall k, In k CS -> getr R (reg k) = getr R0 (reg k)).

(* [comment removed for export] *)
Definition agree_but (P : Z -> Prop) (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition in_out (first a : Z) : Prop := first <= a < first + 42.
Definition in_frame (F a : Z) : Prop := F <= a < F + 512 \/ SH F <= a < SH F + 64.       (* [comment removed for export] *)
Definition in_parts (S a : Z) : Prop := S - 256 <= a < S - 104.                           (* [comment removed for export] *)
Lemma agree_but_trans (P Q : Z -> Prop) M1 M2 M3 :
  agree_but P M1 M2 -> agree_but Q M2 M3 -> agree_but (fun a => P a \/ Q a) M1 M3.
Proof. intros A B a Ha Hn. rewrite (B a Ha) by tauto. apply A; tauto. Qed.
Lemma agree_but_weaken (P Q : Z -> Prop) M1 M2 : agree_but P M1 M2 -> (forall a, P a -> Q a) -> agree_but Q M1 M2.
Proof. intros A PQ a Ha Hn. apply A; [exact Ha|]. intros HP. exact (Hn (PQ a HP)). Qed.

(* [comment removed for export] *)
Definition out_pre (R0 : bvmap 5 word) (S F fl first sigma e z sd r : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  stP R0 S F first sigma e z sd R /\ MIA R0 S first r F fl M /\ sdigs F M z sd
  /\ 0 <= sigma <= 1 /\ 0 <= e <= 16383 /\ 0 <= z /\ 1 <= sd /\ z + sd <= 36.
Definition out_post (R0 : bvmap 5 word) (S F fl first r ptr ec : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  stE R0 S F ptr ec R /\ MIA R0 S first r F fl M /\ first <= ptr <= first + 42 /\ (ec = 0 \/ ec = 75).
End PNADD.
