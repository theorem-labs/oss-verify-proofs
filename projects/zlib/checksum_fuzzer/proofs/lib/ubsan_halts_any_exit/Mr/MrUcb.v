(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition ev_ok (e : ev) (kb : option Z) : Prop :=
  match e with
  (* port727 (): brk grants whole pages (Run.brk_page_range), so a grow may back up to one page
     more than asked; the request bound leaves room for it (MrAccSpec.accs_brk). *)
  | EBrk req => match kb with Some b => req = 0 \/ (b <= req /\ req - b <= 2 ^ 30 - 4096) | None => req = 0 end
  | EMmap _ len _ _ => 0 <= len <= 2 ^ 30 - 4096
  | _ => True
  end.
Definition ev_ans (e : ev) (kb : option Z) (z : Z) : Prop :=
  match e, kb with EBrk req, Some b => req = 0 -> z = b | _, _ => True end.
Definition ev_kb (e : ev) (kb : option Z) : option Z :=
  match e with EBrk req => if req =? 0 then kb else None | _ => None end.
Definition ev_dc (e : ev) : Z :=
  (* port727 (): munmap removes a RANGE and can split an entry: two more entries. *)
  match e with EBrk req => if req =? 0 then 0 else 1 | EMmap _ _ _ _ => 2 | EMunmap _ _ => 2 | _ => 0 end.
Definition ev_du (e : ev) (kb : option Z) : Z :=
  match e with
  (* port727 (): plus the page a brk grow may round up to. *)
  | EBrk req => if req =? 0 then 0 else match kb with Some b => req - b + 4096 | None => 0 end
  | EMmap _ len _ _ => len + 4096
  | _ => 0
  end.

Fixpoint ucb {R} (t : stree ev Z R) (kb : option Z) (C U : Z) (Post : R -> Z -> Z -> Prop) : Prop :=
  match t with
  | SRet r => Post r C U
  | SVis e k =>
      match e with
      | EUndef _ | EPeek _ _ _ => True
      | _ => ev_ok e kb /\ forall z, ev_ans e kb z -> ucb (k z) (ev_kb e kb) (C + ev_dc e) (U + ev_du e kb) Post
      end
  end.

Lemma ucb_mono : forall {R} (t : stree ev Z R) kb C U (P Q : R -> Z -> Z -> Prop),
  (forall r c u, P r c u -> Q r c u) -> ucb t kb C U P -> ucb t kb C U Q.
Proof.
  intros R t. induction t as [r | e k IH]; intros kb C U P Q HPQ; cbn [ucb]; [apply HPQ|].
  destruct e; try exact (fun H => H); intros [H0 H]; (split; [exact H0|]); intros z Hz; (eapply IH; [exact HPQ | apply H; exact Hz]).
Qed.

Lemma ucb_sbind : forall {R S} (t : stree ev Z R) (f : R -> stree ev Z S) kb C U (P : R -> Z -> Z -> Prop) (Q : S -> Z -> Z -> Prop),
  ucb t kb C U P -> (forall r kb' c u, P r c u -> ucb (f r) kb' c u Q) -> ucb (sbind t f) kb C U Q.
Proof.
  intros R S t f. induction t as [r | e k IH]; intros kb C U P Q Ht Hf; cbn [sbind ucb] in *; [apply Hf; exact Ht|].
  destruct e; try exact I; destruct Ht as [H0 H]; (split; [exact H0|]); intros z Hz; (eapply IH; [apply H; exact Hz | exact Hf]).
Qed.


Fixpoint ucbg {R} (Bud : Z -> Z -> Prop) (t : stree ev Z R) (kb : option Z) (C U : Z) (Post : R -> Z -> Z -> Prop) : Prop :=
  match t with
  | SRet r => Post r C U
  | SVis e k =>
      match e with
      | EUndef _ | EPeek _ _ _ => True
      | _ => ev_ok e kb /\ Bud (C + ev_dc e) (U + ev_du e kb) /\
             forall z, ev_ans e kb z -> ucbg Bud (k z) (ev_kb e kb) (C + ev_dc e) (U + ev_du e kb) Post
      end
  end.

Lemma ucbg_ucb : forall {R} (Bud : Z -> Z -> Prop) (t : stree ev Z R) kb C U (P : R -> Z -> Z -> Prop),
  ucbg Bud t kb C U P -> ucb t kb C U P.
Proof.
  intros R Bud t. induction t as [r | e k IH]; intros kb C U P; cbn [ucbg ucb]; [exact (fun H => H)|].
  destruct e; try exact (fun H => H); intros (H0 & _ & H); (split; [exact H0|]); intros z Hz; apply IH, H, Hz.
Qed.

Lemma ucbg_mono : forall {R} (Bud : Z -> Z -> Prop) (t : stree ev Z R) kb C U (P Q : R -> Z -> Z -> Prop),
  (forall r c u, P r c u -> Q r c u) -> ucbg Bud t kb C U P -> ucbg Bud t kb C U Q.
Proof.
  intros R Bud t. induction t as [r | e k IH]; intros kb C U P Q HPQ; cbn [ucbg]; [apply HPQ|].
  destruct e; try exact (fun H => H); intros (H0 & HB & H); (split; [exact H0|]); (split; [exact HB|]); intros z Hz;
    (eapply IH; [exact HPQ | apply H; exact Hz]).
Qed.

Lemma ucbg_sbind : forall {R S} (Bud : Z -> Z -> Prop) (t : stree ev Z R) (f : R -> stree ev Z S) kb C U
    (P : R -> Z -> Z -> Prop) (Q : S -> Z -> Z -> Prop),
  ucbg Bud t kb C U P -> (forall r kb' c u, P r c u -> ucbg Bud (f r) kb' c u Q) -> ucbg Bud (sbind t f) kb C U Q.
Proof.
  intros R S Bud t f. induction t as [r | e k IH]; intros kb C U P Q Ht Hf; cbn [sbind ucbg] in *; [apply Hf; exact Ht|].
  destruct e; try exact I; destruct Ht as (H0 & HB & H); (split; [exact H0|]); (split; [exact HB|]); intros z Hz;
    (eapply IH; [apply H; exact Hz | exact Hf]).
Qed.
