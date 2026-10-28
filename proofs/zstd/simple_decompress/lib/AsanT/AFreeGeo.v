(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ARep ARepQ ARepFrame ALayout AHeapP AModelFacts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Slot.
Variables (L : alayout) (st : astate) (X : aconc) (c k : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.

Let S := size_of_class c.
Let AB := aslot_addr L c k.

Lemma slot_geo :
     16 <= S <= 65536 /\ S mod 16 = 0 /\ AB mod 16 = 0
  /\ aregion L c <= AB /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)
  /\ c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) /\ c_mapped_user (get_cls st c) <= K_FREEARR_OFF
  /\ al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE
  /\ 0x10007fff8000 <= AB /\ AB + S <= ATOP
  /\ aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0.
Proof.
  pose proof (size_of_class_facts c HC) as [S1 S2].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & _).
  pose proof (slot_in_region L st c k ltac:(fold S; lia) ltac:(lia) KR) as (G1 & G2 & G3).
  pose proof (slot_aligned L c k SAL HC) as AL16.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  assert (R8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0).
  { generalize SAL A4. clear. unfold aregion, K_REGION, K_USER_MAP, K_ALIGN. intros. Z.div_mod_to_equations. lia. }
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_FREEARR_OFF <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  subst S AB. generalize S1 S2 A1 A2 G1 G2 G3 AL16 SP1 SP2 R8 RS. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. intros. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma slot_sep_objects :
     (al_t L + 4096 <= AB \/ AB + S <= al_t L) /\ (al_ctx L + 65536 <= AB \/ AB + S <= al_ctx L)
  /\ (al_nodes L + 1048576 <= AB \/ AB + S <= al_nodes L) /\ (al_store L + 8388608 <= AB \/ AB + S <= al_store L)
  /\ (al_fake L + 11571200 <= AB \/ AB + S <= al_fake L).
Proof.
  pose proof slot_geo as (S1 & _ & _ & _ & _ & _ & _ & G7 & G8 & _).
  exact (alayout_slot_disj L AB S ALO G7 G8 ltac:(lia)).
Qed.

Lemma slot_rng : forall RNG, arng L RNG st -> rng RNG AB S /\ rng RNG (shad AB) (shlen S).
Proof.
  intros RNG (_ & _ & _ & _ & _ & _ & _ & _ & _ & RC & _). destruct (RC c HC) as (R1 & R2 & _).
  pose proof slot_geo as (S1 & S2 & AL & G1 & G2 & G3 & G4 & _ & _ & _ & _ & R8 & M8).
  split.
  - eapply rng_sub; [exact R1| lia| lia].
  - eapply rng_sub; [exact R2| |].
    + rewrite !shad_div. generalize G1 R8. clear. intros. Z.div_mod_to_equations. lia.
    + rewrite !shad_div, !shlen_div. generalize G1 G2 G3 R8 M8 S1. clear. intros. Z.div_mod_to_equations. lia.
Qed.
End Slot.

(* [comment removed for export] *)
Lemma slots_sep_any : forall L st X c1 k1 c2 k2,
  alayout_ok L -> awf L st X -> 1 <= c1 < K_NUM_CLASSES -> 1 <= c2 < K_NUM_CLASSES ->
  0 <= k1 < ndist st c1 -> 0 <= k2 < ndist st c2 -> (c1 <> c2 \/ k1 <> k2) ->
  aslot_addr L c1 k1 + size_of_class c1 <= aslot_addr L c2 k2 \/ aslot_addr L c2 k2 + size_of_class c2 <= aslot_addr L c1 k1.
Proof.
  intros L st X c1 k1 c2 k2 ALO WF H1 H2 K1 K2 NE.
  pose proof (slot_geo L st X c1 k1 ALO WF H1 K1) as (S1 & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (slot_geo L st X c2 k2 ALO WF H2 K2) as (T1 & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - apply (slots_disjoint L c1 k1 k2); lia.
  - generalize S1 G1 G2 G3 G4 T1 F1 F2 F3 F4 NC. clear. unfold aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    intros. destruct (Z.lt_ge_cases c1 c2); [left| right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
Lemma rz_size_facts : forall n, 0 <= n -> 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
  intros n Hn. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : exists i, (i <= 7)%nat /\ rz_log n = Z.of_nat i) by (exists (Z.to_nat (rz_log n)); split; lia).
  destruct E as (i & Hi & ->). do 8 (destruct i as [|i]; [cbn; lia|]). lia.
Qed.

Lemma rounded_size_facts : forall n, 0 <= n -> n <= rounded_size n /\ 8 <= rounded_size n /\ rounded_size n mod 8 = 0 /\ rup n 8 <= rounded_size n
  /\ rounded_size n <= n + 15.
Proof.
  intros n Hn. unfold rounded_size, rup. Z.div_mod_to_equations. nia.
Qed.

Section Chunk.
Variables (L : alayout) (st : astate) (X : aconc) (c k n : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : rounded_size n + rz_size n <= size_of_class c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let hm := UB - 16.

Lemma chunk_geo :
     hm mod 16 = 0 /\ UB mod 16 = 0 /\ AB + 16 <= UB /\ AB <= hm
  /\ 0x10007fff8000 <= hm /\ UB + rup n 8 <= AB + S /\ AB + S <= ATOP /\ hm + 16 + rup n 8 <= ATOP /\ n <= 65536 /\ n <= Q_MAX
  /\ 0x10007fff8000 <= AB /\ n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ 8 <= S - rz_size n.
Proof.
  pose proof (slot_geo L st X c k ALO WF HC KR) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. pose proof (rounded_size_facts n N0) as (RS1 & RS2 & RS3 & RS4 & RS5).
  subst S AB UB hm. generalize S1 S2 AL G1 G2 G7 G8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold Q_MAX, rup. intros. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_shadow_geo :
     shad UB = shad AB + shlen (rz_size n) /\ 2 <= shlen (rz_size n)
  /\ shlen (rup n 8) = granules n /\ 0 <= shlen (rup n 8)
  /\ shlen (rz_size n) + granules n <= shlen S
  /\ 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fff8000
  /\ shad (aregion L c) <= shad AB /\ shad AB + shlen S <= shad (aregion L c) + shlen (c_mapped_user (get_cls st c)).
Proof.
  pose proof (slot_geo L st X c k ALO WF HC KR) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. pose proof (rounded_size_facts n N0) as (RS1 & RS2 & RS3 & RS4 & RS5).
  subst S AB UB hm. unfold granules. rewrite !shad_div, !shlen_div.
  generalize S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold ASHOFF, rup, K_FREEARR_OFF, K_SPACE_SIZE. intros.
  Z.div_mod_to_equations. lia.
Qed.
End Chunk.
End CANSEC1.
