(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec SeqExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptRecs LeptStructs DitherLib DitherLoop.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CmapArr.
Context {fx : FPState}.
Variable segs : list Segment.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition arr255 (M : word -> option byte) (p n : Z) : Prop :=
  forall i, 0 <= i < n -> exists v, 0 <= v <= 255 /\ rdn segs M (Z_to_bv 64 (p + 4 * i)) 4 = Some (Z_to_le_bytes 4 v).

(* [comment removed for export] *)
Lemma arr255_zero : forall M p n, 0 <= p -> p + 4 * n <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 * n -> M (at_ (Z_to_bv 64 p) i) = Some (Z_to_bv 8 0)) -> arr255 M p n.
Proof.
  intros M p n Hp Hn Z i Hi. exists 0. split; [lia|]. rewrite Z_to_le_bytes_0.
  apply rdn_const; rewrite u_Z2bv by lia; [cbn; lia|].
  intros x Hx. cbn in Hx. specialize (Z (u x - p) ltac:(lia)). unfold at_ in Z. rewrite u_Z2bv in Z by lia.
  replace (Z_to_bv 64 (p + (u x - p))) with x in Z; [exact Z|]. apply bv_eq. rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.

(* [comment removed for export] *)
Lemma arr255_ext : forall M M' p n, 0 <= p -> p + 4 * n <= 2 ^ 64 ->
  (forall x : word, p <= u x < p + 4 * n -> M' x = M x) -> arr255 M p n -> arr255 M' p n.
Proof.
  intros M M' p n Hp Hn E A i Hi. destruct (A i Hi) as (v & Hv & R). exists v. split; [exact Hv|]. rewrite <- R.
  apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply E. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma arr255_wbytes_out : forall M p n (a : Z) bs, 0 <= p -> p + 4 * n <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (a + Z.of_nat (length bs) <= p \/ p + 4 * n <= a) -> arr255 M p n -> arr255 (wbytes M (Z_to_bv 64 a) bs) p n.
Proof.
  intros M p n a bs Hp Hn Ha Hab D. apply arr255_ext; [exact Hp | exact Hn|]. intros x Hx.
  apply wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma arr255_wbytes_cell : forall M p n j v, 0 <= p -> p + 4 * n <= 2 ^ 64 -> 0 <= j < n -> 0 <= v <= 255 ->
  arr255 M p n -> arr255 (wbytes M (Z_to_bv 64 (p + 4 * j)) (word_to_le_bytes 4 (Z_to_bv 64 v))) p n.
Proof.
  intros M p n j v Hp Hn Hj Hv A i Hi. destruct (Z.eq_dec i j) as [->|NE].
  - exists v. split; [exact Hv|]. rewrite <- (w2b_Z 4 v) by lia.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 (Z_to_bv 64 v)) M (Z_to_bv 64 (p + 4 * j))) as H.
    rewrite length_N_to_le_bytes in H. apply H. rewrite u_Z2bv by lia. cbn. lia.
  - destruct (A i Hi) as (v' & Hv' & R). exists v'. split; [exact Hv'|]. rewrite <- R.
    apply rdn_wbytes_out; rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma arr255_cell : forall M p n i, arr255 M p n -> 0 <= i < n ->
  exists v, 0 <= v <= 255 /\ rdn segs M (Z_to_bv 64 (p + 4 * i)) 4 = Some (Z_to_le_bytes 4 v).
Proof. intros M p n i A Hi. exact (A i Hi). Qed.

(* [comment removed for export] *)
Definition PTAL (m : word -> option byte) (r1 g1 b1 a1 vr vg vb va : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 r1) (word_to_le_bytes 4 (Z_to_bv 64 vr))) (Z_to_bv 64 g1) (word_to_le_bytes 4 (Z_to_bv 64 vg)))
    (Z_to_bv 64 b1) (word_to_le_bytes 4 (Z_to_bv 64 vb))) (Z_to_bv 64 a1) (word_to_le_bytes 4 (Z_to_bv 64 va)).

(* [comment removed for export] *)
Definition arrs4 (rm gm bm am n : Z) : Prop :=
  0 <= rm /\ rm + 4 * n < 2 ^ 63 /\ 0 <= gm /\ gm + 4 * n < 2 ^ 63 /\ 0 <= bm /\ bm + 4 * n < 2 ^ 63 /\ 0 <= am /\ am + 4 * n < 2 ^ 63 /\
  (rm + 4 * n <= gm \/ gm + 4 * n <= rm) /\ (rm + 4 * n <= bm \/ bm + 4 * n <= rm) /\ (rm + 4 * n <= am \/ am + 4 * n <= rm) /\
  (gm + 4 * n <= bm \/ bm + 4 * n <= gm) /\ (gm + 4 * n <= am \/ am + 4 * n <= gm) /\ (bm + 4 * n <= am \/ am + 4 * n <= bm).

Definition R4 (rm gm bm am n : Z) : list (Z * Z) := [(rm, 4 * n); (gm, 4 * n); (bm, 4 * n); (am, 4 * n)].

Lemma PTAL_inv : forall M0 M rm gm bm am n j vr vg vb va, arrs4 rm gm bm am n -> 0 <= j < n ->
  0 <= vr <= 255 -> 0 <= vg <= 255 -> 0 <= vb <= 255 -> 0 <= va <= 255 ->
  rinv (R4 rm gm bm am n) M0 M -> arr255 M rm n -> arr255 M gm n -> arr255 M bm n ->
  let M' := PTAL M (rm + 4 * j) (gm + 4 * j) (bm + 4 * j) (am + 4 * j) vr vg vb va in
  rinv (R4 rm gm bm am n) M0 M' /\ arr255 M' rm n /\ arr255 M' gm n /\ arr255 M' bm n.
Proof.
  intros M0 M rm gm bm am n j vr vg vb va G Hj Hvr Hvg Hvb Hva RI Ar Ag Ab M'.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & D1 & D2 & D3 & D4 & D5 & D6).
  subst M'. unfold PTAL. split; [|split; [|split]].
  - unfold R4. repeat (apply (rinv_wbytes _ M0 _ _ 4); [ | rewrite length_N_to_le_bytes; reflexivity | lia | lia | ]).
    + exact RI.
    + exists (rm, 4 * n). split; [left; reflexivity | cbn [fst snd]; lia].
    + exists (gm, 4 * n). split; [right; left; reflexivity | cbn [fst snd]; lia].
    + exists (bm, 4 * n). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
    + exists (am, 4 * n). split; [right; right; right; left; reflexivity | cbn [fst snd]; lia].
  - do 3 (apply arr255_wbytes_out; [lia | lia | lia | rewrite length_N_to_le_bytes; cbn; lia | rewrite length_N_to_le_bytes; cbn; lia |]).
    apply arr255_wbytes_cell; [lia | lia | exact Hj | exact Hvr | exact Ar].
  - do 2 (apply arr255_wbytes_out; [lia | lia | lia | rewrite length_N_to_le_bytes; cbn; lia | rewrite length_N_to_le_bytes; cbn; lia |]).
    apply arr255_wbytes_cell; [lia | lia | exact Hj | exact Hvg|].
    apply arr255_wbytes_out; [lia | lia | lia | rewrite length_N_to_le_bytes; cbn; lia | rewrite length_N_to_le_bytes; cbn; lia | exact Ag].
  - apply arr255_wbytes_out; [lia | lia | lia | rewrite length_N_to_le_bytes; cbn; lia | rewrite length_N_to_le_bytes; cbn; lia |].
    apply arr255_wbytes_cell; [lia | lia | exact Hj | exact Hvb|].
    do 2 (apply arr255_wbytes_out; [lia | lia | lia | rewrite length_N_to_le_bytes; cbn; lia | rewrite length_N_to_le_bytes; cbn; lia |]).
    exact Ab.
Qed.

(* [comment removed for export] *)
Lemma rdn_byte_val : forall M (a : Z) (N : nat) bs k, 0 <= a -> a + Z.of_nat N <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) N = Some bs -> 0 <= k < Z.of_nat N ->
  exists v, 0 <= v <= 255 /\ rdn segs M (Z_to_bv 64 (a + k)) 1 = Some (Z_to_le_bytes 1 v).
Proof.
  intros M a N bs k Ha Hhi R Hk.
  assert (S1 : exists b : byte, rdn segs M (Z_to_bv 64 (a + k)) 1 = Some [b]).
  { pose proof (rdn_sub segs M N (Z_to_bv 64 a) bs (Z.to_nat k) 1 R ltac:(lia)) as S.
    unfold at_ in S. rewrite u_Z2bv in S by lia. rewrite Z2Nat.id in S by lia.
    pose proof (rdn_length _ _ _ _ _ S) as L. destruct (sub bs (Z.to_nat k) 1) as [|b [|? ?]] eqn:E; cbn in L; try lia. exists b. exact S. }
  destruct S1 as (b & S1). exists (u b). split; [pose proof (bv_unsigned_in_range _ b) as B; change (bv_modulus 8) with 256 in B; lia|].
  rewrite S1. cbn [Z_to_le_bytes]. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

End CmapArr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CmapArrW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rinv_changed : forall R (M M' : word -> option byte), rinv R M M' ->
  forall a : word, M' a <> M a -> Exists (fun r => fst r <= u a < fst r + snd r) R.
Proof.
  intros R M M' [_ F] a NE.
  assert (D : forall L : list (Z * Z), Exists (fun r => fst r <= u a < fst r + snd r) L \/ (forall r, In r L -> ~ inreg (fst r) (snd r) a)).
  { induction L as [|r t IH]; [right; intros r []|].
    destruct (Z_le_gt_dec (fst r) (u a)) as [H1|H1]; [destruct (Z_lt_ge_dec (u a) (fst r + snd r)) as [H2|H2]|].
    - left. constructor. lia.
    - destruct IH as [IH|IH]; [left; constructor 2; exact IH | right]. intros r' [<-|Hr']; [unfold inreg; lia | exact (IH r' Hr')].
    - destruct IH as [IH|IH]; [left; constructor 2; exact IH | right]. intros r' [<-|Hr']; [unfold inreg; lia | exact (IH r' Hr')]. }
  destruct (D R) as [X|X]; [exact X|]. exfalso. apply NE. apply F. exact X.
Qed.

(* [comment removed for export] *)
Definition fresh_regions (C : lctx) (A Ar : AS) (R : list (Z * Z)) : Prop :=
  Forall (fun r => exists (p : word) n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ u p <= fst r /\ fst r + snd r <= u p + n) R.

Lemma rinv_WP : forall C Ar A m md M' R s, Cok C -> W C A m md -> sub_live Ar A -> s <= c_top C ->
  rinv R m M' -> fresh_regions C A Ar R -> W C A M' md /\ POSTM C Ar s m M'.
Proof.
  intros C Ar A m md M' R s CK HW SUB Hs RI FR.
  assert (CH : forall a : word, M' a <> m a -> exists p n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ u p <= u a < u p + n).
  { intros a NE. pose proof (rinv_changed R m M' RI a NE) as X. apply Exists_exists in X. destruct X as (r & Hr & Hin).
    unfold fresh_regions in FR. rewrite Forall_forall in FR. destruct (FR r Hr) as (p & n & L & LR & L0 & H1 & H2).
    exists p, n. split; [exact L | split; [exact LR | split; [exact L0 | lia]]]. }
  split.
  - apply (W_local C A m md M' s CK HW Hs); [|exact (proj1 RI)].
    intros a NE. right. destruct (CH a NE) as (p & n & L & _ & L0 & Rg). exists p, n. split; [exact L | split; [exact L0 | exact Rg]].
  - apply (POSTM_local C Ar A m md M' s CK HW SUB).
    intros a NE. right. destruct (CH a NE) as (p & n & L & LR & _ & Rg). exists p, n. split; [exact L | split; [exact LR | exact Rg]].
Qed.

(* [comment removed for export] *)
Definition local_regions (C : lctx) (A Ar : AS) (s : Z) (R : list (Z * Z)) : Prop :=
  Forall (fun r => (c_top C - LSTK <= fst r /\ fst r + snd r <= s)
                   \/ exists (p : word) n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ u p <= fst r /\ fst r + snd r <= u p + n) R.

Lemma rinv_WP2 : forall C Ar A m md M' R s, Cok C -> W C A m md -> sub_live Ar A -> s <= c_top C ->
  rinv R m M' -> local_regions C A Ar s R -> W C A M' md /\ POSTM C Ar s m M'.
Proof.
  intros C Ar A m md M' R s CK HW SUB Hs RI FR.
  assert (CH : forall a : word, M' a <> m a -> scratch C s a \/ exists p n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ u p <= u a < u p + n).
  { intros a NE. pose proof (rinv_changed R m M' RI a NE) as X. apply Exists_exists in X. destruct X as (r & Hr & Hin).
    unfold local_regions in FR. rewrite Forall_forall in FR. destruct (FR r Hr) as [[H1 H2] | (p & n & L & LR & L0 & H1 & H2)].
    - left. unfold scratch. lia.
    - right. exists p, n. split; [exact L | split; [exact LR | split; [exact L0 | lia]]]. }
  split.
  - apply (W_local C A m md M' s CK HW Hs); [|exact (proj1 RI)].
    intros a NE. destruct (CH a NE) as [X | (p & n & L & _ & L0 & Rg)]; [left; exact X | right; exists p, n; split; [exact L | split; [exact L0 | exact Rg]]].
  - apply (POSTM_local C Ar A m md M' s CK HW SUB).
    intros a NE. destruct (CH a NE) as [X | (p & n & L & LR & _ & Rg)]; [left; exact X | right; exists p, n; split; [exact L | split; [exact LR | exact Rg]]].
Qed.

(* [comment removed for export] *)
Definition blk_new (C : lctx) (A A' : AS) (p n : Z) : Prop :=
  4096 <= p /\ p + n <= alloc_top (c_vm C) /\ p mod 16 = 0 /\
  live A (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 p) = None /\ live A' (Z_to_bv 64 p) = Some n.

Definition pta_new (segs : list Segment) (C : lctx) (A A' : AS) (m' : word -> option byte) (q rm gm bm am n : Z) : Prop :=
  blk_new C A A' rm (4 * n) /\ blk_new C A A' gm (4 * n) /\ blk_new C A A' bm (4 * n) /\ blk_new C A A' am (4 * n) /\
  rm <> gm /\ rm <> bm /\ rm <> am /\ gm <> bm /\ gm <> am /\ bm <> am /\
  (forall p : word, p <> Z_to_bv 64 rm -> p <> Z_to_bv 64 gm -> p <> Z_to_bv 64 bm -> p <> Z_to_bv 64 am -> live A' p = live A p) /\
  rdn segs m' (Z_to_bv 64 (q + 24)) 8 = Some (Z_to_le_bytes 8 rm) /\ rdn segs m' (Z_to_bv 64 (q + 16)) 8 = Some (Z_to_le_bytes 8 gm) /\
  rdn segs m' (Z_to_bv 64 (q + 8)) 8 = Some (Z_to_le_bytes 8 bm) /\ rdn segs m' (Z_to_bv 64 q) 8 = Some (Z_to_le_bytes 8 am) /\
  arr255 segs m' rm n /\ arr255 segs m' gm n /\ arr255 segs m' bm n.

End CmapArrW.

(* [comment removed for export] *)
Definition PTA_STACK : Z := 96 + CALLOC_STACK.
Definition RK_pta : Z := 4.
Definition RB_pta : Z := 4 * 2 ^ 17.
