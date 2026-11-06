(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptDefs LeptRecs.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Slots.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma W_free0 : forall C A m md regs (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  getr regs 10 = Z_to_bv 64 0 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs',
      W C A' m' (with_vmmaps vm' md) ->
      (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      live A' (Z_to_bv 64 0) = None -> (forall q, q <> Z_to_bv 64 0 -> live A' q = live A q) ->
      POSTM C A s m m' ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S.
Proof.
  intros C A m md regs ret s S CK HW Z0 H10 H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_free fx A m md regs (Z_to_bv 64 0) ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 (or_introl eq_refl) H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' Hinv' Hcs Lp' EQ Hfr Hlive Hdef E1 E2 E3 E4 _.
    rewrite H2, u_Z2bv in Hfr by lia.
    assert (Hkeep' : forall q k, live (c_A0 C) q = Some k -> live A' q = Some k).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [congruence|].
      rewrite (EQ q NE). exact (w_keep _ _ _ _ HW q k L). }
    assert (Hdef' : forall a, m a <> None -> u a < al_image_hi \/ owned A a \/ m' a <> None).
    { intros a Ha. destruct (Hdef a Ha) as [X|X]; [right; left; exact X | right; right; exact X]. }
    assert (Hlive2 : forall q k i, live (c_A0 C) q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)).
    { intros q k i L Hi. exact (Hlive q k i (Hkeep' q k L) Hi). }
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi Hinv' Hkeep' Hfr Hlive2 Hdef' E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' HW' Hcs Lp' EQ). split; [exact F|].
    intros q k i L Hi. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE].
    + (* [comment removed for export] *)
      exfalso. destruct (Z_lt_ge_dec 0 k) as [Hk|Hk]; [| lia].
      pose proof (blk_range C A m md (Z_to_bv 64 0) k CK HW L Hk) as [B _]. rewrite u_Z2bv in B by lia. lia.
    + exact (Hlive q k i ltac:(rewrite (EQ q NE); exact L) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inslot (pp : Z) (a : word) : Prop := pp <= u a < pp + 8.

Definition slotok (C : lctx) (A : AS) (s pp : Z) (sb : option (word * Z)) : Prop :=
  match sb with
  | None => s <= pp /\ pp + 8 <= c_top C
  | Some (p, n) => live A p = Some n /\ live (c_A0 C) p = None /\ u p <= pp /\ pp + 8 <= u p + n
  end.

Definition FRMx (C : lctx) (s pp : Z) (m m' : word -> option byte) : Prop :=
  forall a : word, ~ heap_gap C a -> ~ al_globals a -> ~ al_errno_slot a -> ~ hcell a -> ~ scratch C s a ->
                   ~ inslot pp a -> m' a = m a.
Definition LIVKx (A : AS) (pp : Z) (m m' : word -> option byte) : Prop :=
  forall q k i, live A q = Some k -> 0 <= i < k -> ~ inslot pp (at_ q i) -> m' (at_ q i) = m (at_ q i).
Definition POSTD (C : lctx) (A : AS) (s pp : Z) (m m' : word -> option byte) : Prop :=
  FRMx C s pp m m' /\ LIVKx A pp m m'.

Lemma POSTD_of_POSTM : forall C A A' s pp m m', POSTM C A s m m' -> sub_live A' A -> POSTD C A' s pp m m'.
Proof.
  intros C A A' s pp m m' [F L] SUB. split.
  - intros a H1 H2 H3 H4 H5 _. exact (F a H1 H2 H3 H4 H5).
  - intros q k i Lq Hi _. exact (L q k i (SUB q k Lq) Hi).
Qed.

Lemma POSTD_refl : forall C A s pp m, POSTD C A s pp m m.
Proof. intros. split; [intros a _ _ _ _ _ _ | intros q k i _ _ _]; reflexivity. Qed.

Lemma POSTD_trans : forall C A s pp m1 m2 m3, POSTD C A s pp m1 m2 -> POSTD C A s pp m2 m3 -> POSTD C A s pp m1 m3.
Proof.
  intros C A s pp m1 m2 m3 [F1 L1] [F2 L2]. split.
  - intros a H1 H2 H3 H4 H5 H6. rewrite (F2 a H1 H2 H3 H4 H5 H6). exact (F1 a H1 H2 H3 H4 H5 H6).
  - intros q k i Lq Hi Hs. rewrite (L2 q k i Lq Hi Hs). exact (L1 q k i Lq Hi Hs).
Qed.

Lemma POSTD_sub : forall C A A' s pp m m', sub_live A' A -> POSTD C A s pp m m' -> POSTD C A' s pp m m'.
Proof.
  intros C A A' s pp m m' SUB [F L]. split; [exact F|]. intros q k i Lq Hi Hs. exact (L q k i (SUB q k Lq) Hi Hs).
Qed.

Lemma POSTD_mono : forall C A s s' pp m m', s <= s' -> POSTD C A s pp m m' -> POSTD C A s' pp m m'.
Proof.
  intros C A s s' pp m m' Hs [F L]. split; [|exact L]. intros a H1 H2 H3 H4 H5 H6. apply F; try assumption.
  unfold scratch in *. lia.
Qed.

(* [comment removed for export] *)
Lemma POSTD_slotw : forall C A s pp m bs, length bs = 8%nat -> 0 <= pp -> pp + 8 <= 2 ^ 64 ->
  POSTD C A s pp m (wbytes m (Z_to_bv 64 pp) bs).
Proof.
  intros C A s pp m bs Hl Hp Hp64. split.
  - intros a _ _ _ _ _ H6. unfold inslot in H6. apply wbytes_outside; rewrite u_Z2bv by lia; rewrite Hl; cbn; lia.
  - intros q k i _ _ H6. unfold inslot in H6. apply wbytes_outside; rewrite u_Z2bv by lia; rewrite Hl; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma POSTD_deadw : forall C A A' m md (q a : word) (n : Z) bs (s pp : Z), Cok C -> W C A m md ->
  live A q = Some n -> live A' q = None -> sub_live A' A ->
  u q <= u a -> u a + Z.of_nat (length bs) <= u q + n ->
  POSTD C A' s pp m (wbytes m a bs).
Proof.
  intros C A A' m md q a n bs s pp CK HW L L' SUB Hlo Hhi.
  pose proof (ai_live_hull A m (m_vmmaps md) q n (w_inv _ _ _ _ HW) L) as (Hn0 & _ & TOP & _). pose proof (round16_ge n Hn0).
  pose proof (alloc_top_lt (m_vmmaps md)) as T. unfold two_pow_64 in T.
  split.
  - intros x H1 _ _ _ _ _. destruct (Z_lt_ge_dec (u x) (u a)); [apply wbytes_outside; lia|].
    destruct (Z_lt_ge_dec (u x) (u a + Z.of_nat (length bs))); [|apply wbytes_outside; lia].
    exfalso. apply H1. destruct (blk_byte C A m md q n x CK HW L ltac:(lia)) as (G & _). exact G.
  - intros q' k i Lq' Hi _. pose proof (SUB q' k Lq') as LqA.
    assert (NE : q <> q') by (intros ->; congruence).
    pose proof (ai_live_disjoint A m (m_vmmaps md) q n q' k (w_inv _ _ _ _ HW) L LqA NE) as D.
    pose proof (ai_live_hull A m (m_vmmaps md) q' k (w_inv _ _ _ _ HW) LqA) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
    apply wbytes_outside; [lia|]. unfold at_. rewrite u_Z2bv by (pose proof (u64_range q'); lia). lia.
Qed.

(* [comment removed for export] *)
Lemma POSTD_win : forall C A A' m md (a : word) bs (s pp : Z), Cok C -> W C A m md -> sub_live A' A ->
  c_top C - LSTK <= u a -> u a + Z.of_nat (length bs) <= s -> s <= c_top C ->
  POSTD C A' s pp m (wbytes m a bs).
Proof.
  intros C A A' m md a bs s pp CK HW SUB Hlo Hhi Hs.
  apply (POSTD_of_POSTM C A A'); [| exact SUB]. eapply POSTM_wbytes_win; eassumption.
Qed.

(* [comment removed for export] *)
Lemma slot_where : forall C A m md s pp sb, Cok C -> W C A m md -> slotok C A s pp sb -> c_top C - LSTK <= s ->
  (s <= pp /\ pp + 8 <= c_top C) \/ (4096 <= pp /\ pp + 8 <= alloc_top (c_vm C) /\ alloc_top (c_vm C) + 8192 + LSTK <= c_top C).
Proof.
  intros C A m md s pp sb CK HW SL Hs. destruct sb as [[p n]|]; cbn in SL.
  - destruct SL as (L & L0 & R1 & R2). right.
    destruct (blk_range C A m md p n CK HW L ltac:(lia)) as [G TOP]. pose proof (ck_top C CK). lia.
  - left. exact SL.
Qed.

Lemma slot_range : forall C A m md s pp sb, Cok C -> W C A m md -> slotok C A s pp sb -> c_top C - LSTK <= s ->
  4096 <= pp /\ pp + 8 <= c_top C.
Proof.
  intros C A m md s pp sb CK HW SL Hs. pose proof (ck_top C CK). pose proof LSTK_val.
  pose proof (alloc_top_lt (c_vm C)) as T. unfold two_pow_64 in T.
  destruct (slot_where C A m md s pp sb CK HW SL Hs) as [X|X]; [|lia].
  (* [comment removed for export] *)
  pose proof (ck_img C CK). laypins. lia.
Qed.

(* [comment removed for export] *)
Lemma slot_sok : forall C A m md s pp sb, Cok C -> W C A m md -> slotok C A s pp sb -> c_top C - LSTK <= s ->
  store_ok al_segs m (Z_to_bv 64 pp) 8 = true.
Proof.
  intros C A m md s pp sb CK HW SL Hs. pose proof (slot_range C A m md s pp sb CK HW SL Hs) as [R1 R2].
  pose proof CK as [T1 T2 T3 T4 T5].
  apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
  unfold wview. destruct (m x) as [b|] eqn:E; [discriminate|]. exfalso.
  destruct sb as [[p n]|]; cbn in SL.
  - destruct SL as (L & L0 & Q1 & Q2). destruct (blk_byte C A m md p n x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
  - apply (w_win _ _ _ _ HW x); [unfold win; lia | exact E].
Qed.

(* [comment removed for export] *)
Lemma slot_W : forall C A m md s pp sb bs, Cok C -> W C A m md -> slotok C A s pp sb -> c_top C - LSTK <= s ->
  length bs = 8%nat -> W C A (wbytes m (Z_to_bv 64 pp) bs) md.
Proof.
  intros C A m md s pp sb bs CK HW SL Hs Hl. pose proof (slot_range C A m md s pp sb CK HW SL Hs) as [R1 R2].
  pose proof CK as [T1 T2 T3 T4 T5].
  destruct sb as [[p n]|]; cbn in SL.
  - destruct SL as (L & L0 & Q1 & Q2). apply (W_store_blk C A m md p _ n bs CK HW L L0); rewrite ?Hl, u_Z2bv by lia; [lia | cbn; lia].
  - apply (W_store_win C A m md _ bs CK HW); rewrite ?Hl, u_Z2bv by lia; [lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma slot_keep : forall C A A' s pp sb, slotok C A s pp sb ->
  (forall p n, sb = Some (p, n) -> live A' p = live A p) -> slotok C A' s pp sb.
Proof.
  intros C A A' s pp sb SL K. destruct sb as [[p n]|]; cbn in *; [|exact SL].
  destruct SL as (L & rest). split; [rewrite (K p n eq_refl); exact L | exact rest].
Qed.

(* [comment removed for export] *)
Lemma slot_blk_neq : forall C A s pp p n (q : word) k, slotok C A s pp (Some (p, n)) -> live A q = Some k ->
  (n <> k \/ ~ (u q <= pp /\ pp + 8 <= u q + k)) -> p <> q.
Proof.
  intros C A s pp p n q k (L & _ & R1 & R2) Lq H ->. rewrite Lq in L. injection L as ->. destruct H as [H|H]; [exact (H eq_refl) | exact (H (conj R1 R2))].
Qed.

(* [comment removed for export] *)
Lemma POSTD_POSTM_win : forall C A m' md' (s s' pp : Z) m, Cok C -> W C A m' md' ->
  c_top C - LSTK <= pp -> pp + 8 <= s' -> s <= s' -> s' <= c_top C -> POSTD C A s pp m m' -> POSTM C A s' m m'.
Proof.
  intros C A m' md' s s' pp m CK HW Hlo Hhi Hs Hs' [F L]. split.
  - intros a H1 H2 H3 H4 H5. apply F; try assumption; unfold scratch, inslot in *; lia.
  - intros q k i Lq Hi. apply (L q k i Lq Hi). intros IN. unfold inslot in IN.
    pose proof (ai_live_hull A m' (m_vmmaps md') q k (w_inv _ _ _ _ HW) Lq) as (Hk0 & _ & TOP & _). pose proof (round16_ge k Hk0).
    pose proof (alloc_top_lt (m_vmmaps md')) as T. unfold two_pow_64 in T.
    assert (R : u q <= u (at_ q i) < u q + k) by (unfold at_; rewrite u_Z2bv by (pose proof (u64_range q); lia); lia).
    destruct (blk_byte C A m' md' q k (at_ q i) CK HW Lq R) as (_ & _ & _ & NW & _). apply NW. unfold win.
    pose proof (ck_top C CK). lia.
Qed.

(* [comment removed for export] *)
Lemma POSTD_POSTM_blk : forall C Ar A1 m1 md1 (q : word) (n s pp : Z) m m', Cok C -> W C A1 m1 md1 ->
  live A1 q = Some n -> u q <= pp -> pp + 8 <= u q + n -> live Ar q = None -> sub_live Ar A1 ->
  POSTD C Ar s pp m m' -> POSTM C Ar s m m'.
Proof.
  intros C Ar A1 m1 md1 q n s pp m m' CK HW Lq Q1 Q2 Lr SUB [F L]. split.
  - intros a H1 H2 H3 H4 H5. apply F; try assumption. intros IN. unfold inslot in IN. apply H1.
    destruct (blk_byte C A1 m1 md1 q n a CK HW Lq ltac:(lia)) as (G & _). exact G.
  - intros q' k i Lq' Hi. apply (L q' k i Lq' Hi). intros IN. unfold inslot in IN.
    pose proof (SUB q' k Lq') as L1. assert (NE : q <> q') by (intros ->; congruence).
    pose proof (ai_live_disjoint A1 m1 (m_vmmaps md1) q n q' k (w_inv _ _ _ _ HW) Lq L1 NE) as D.
    pose proof (ai_live_hull A1 m1 (m_vmmaps md1) q' k (w_inv _ _ _ _ HW) L1) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
    pose proof (ai_live_hull A1 m1 (m_vmmaps md1) q n (w_inv _ _ _ _ HW) Lq) as (Hn0 & _ & TOPn & _). pose proof (round16_ge n Hn0).
    pose proof (alloc_top_lt (m_vmmaps md1)) as T. unfold two_pow_64 in T.
    assert (R : u q' <= u (at_ q' i) < u q' + k) by (unfold at_; rewrite u_Z2bv by (pose proof (u64_range q'); lia); lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma POSTD_blk_byte : forall C A s pp m m' (q : word) k (x : word), POSTD C A s pp m m' -> live A q = Some k ->
  u q <= u x < u q + k -> ~ inslot pp x -> m' x = m x.
Proof.
  intros C A s pp m m' q k x [_ L] Lq R NS.
  assert (E : at_ q (u x - u q) = x) by (unfold at_; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range x); pose proof (u64_range q); lia); lia).
  rewrite <- E. rewrite <- E in NS. exact (L q k (u x - u q) Lq ltac:(lia) NS).
Qed.

(* [comment removed for export] *)
Lemma LIVK_byte : forall A m m' (q : word) k (x : word), LIVK A m m' -> live A q = Some k ->
  u q <= u x < u q + k -> m' x = m x.
Proof.
  intros A m m' q k x L Lq R.
  assert (E : at_ q (u x - u q) = x) by (unfold at_; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range x); pose proof (u64_range q); lia); lia).
  rewrite <- E. exact (L q k (u x - u q) Lq ltac:(lia)).
Qed.

Lemma RECat_LIVK : forall A m m' (q : word) k p fs, RECat m p fs -> LIVK A m m' -> live A q = Some k ->
  u q <= p -> p + Z.of_nat (flds_len fs) <= u q + k -> RECat m' p fs.
Proof.
  intros A m m' q k p fs R L Lq H1 H2. apply (RECat_frame m m' p fs R). intros x Hx. exact (LIVK_byte A m m' q k x L Lq ltac:(lia)).
Qed.

Lemma RECat_POSTM : forall C A s m m' (q : word) k p fs, RECat m p fs -> POSTM C A s m m' -> live A q = Some k ->
  u q <= p -> p + Z.of_nat (flds_len fs) <= u q + k -> RECat m' p fs.
Proof. intros C A s m m' q k p fs R [_ L] Lq H1 H2. exact (RECat_LIVK A m m' q k p fs R L Lq H1 H2). Qed.

Lemma RECat_POSTD : forall C A s pp m m' (q : word) k p fs, RECat m p fs -> POSTD C A s pp m m' -> live A q = Some k ->
  u q <= p -> p + Z.of_nat (flds_len fs) <= u q + k -> (pp + 8 <= p \/ p + Z.of_nat (flds_len fs) <= pp) -> RECat m' p fs.
Proof.
  intros C A s pp m m' q k p fs R PD Lq H1 H2 OFF. apply (RECat_frame m m' p fs R). intros x Hx.
  apply (POSTD_blk_byte C A s pp m m' q k x PD Lq ltac:(lia)). unfold inslot. lia.
Qed.

(* [comment removed for export] *)
Lemma POSTD_rdn_above : forall C A s pp m m' (a : Z) (n : nat), Cok C -> POSTD C A s pp m m' ->
  s <= a -> a + Z.of_nat n <= 2 ^ 64 -> c_top C - LSTK <= s -> (pp + 8 <= a \/ a + Z.of_nat n <= pp) ->
  rdn al_segs m' (Z_to_bv 64 a) n = rdn al_segs m (Z_to_bv 64 a) n.
Proof.
  intros C A s pp m m' a n CK [F _] Hs Hn Hlo OFF. destruct CK. laypins. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply F.
  - apply above_not_gap. lia.
  - intros G; apply pin_glob in G; unfold inZ in G; lia.
  - intros G; apply pin_errno in G; unfold inZ in G; lia.
  - unfold hcell; lia.
  - unfold scratch; lia.
  - unfold inslot; lia.
Qed.

End Slots.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
