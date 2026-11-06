(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition pfact_eqb' (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb'_eq : forall f g, pfact_eqb' f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma pfact_find' : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb' f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb'_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (pfact_find' V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.
Ltac mimg V m HM lo hi H := pose proof (mimg_cover asegs V m _ lo hi HM ltac:(vm_compute; reflexivity)) as H.

Fixpoint img_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom asegs (wa A) with Some b' => bv_eqb b b' && img_bytes_b (A + 1) bs' | None => false end
  end.
Lemma img_bytes_b_sound : forall bs A i, img_bytes_b A bs = true -> (i < length bs)%nat ->
  seg_rom asegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b bs IH]; intros A i H Hi; [cbn in Hi; lia|].
  cbn [img_bytes_b] in H. destruct (seg_rom asegs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  destruct i as [|i]; [rewrite Z.add_0_r; exact E|].
  cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact H2| cbn in Hi; lia].
Qed.
Lemma img_bytes_at : forall (m : mem) A bs,
  (forall i, A <= i < A + Z.of_nat (length bs) -> m (wa i) = None) -> img_bytes_b A bs = true ->
  0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at asegs m A bs.
Proof.
  intros m A bs HN HB H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (HN (A + Z.of_nat i)) by lia. apply img_bytes_b_sound; assumption.
Qed.

Lemma aimg_chunk : forall V (m : mem) (l : list mfact) A cs,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> img_bytes_b A (cells_bytes cs) = true -> 0xa9000 <= A -> A + Z.of_nat (cells_size cs) <= 0x609000 ->
  rw_cells asegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  split; [split; [exact WF|]| apply a0_rw_image_wr_at; lia].
  apply img_bytes_at; [rewrite LEN; exact R| exact HB| lia| rewrite LEN; lia].
Qed.
Ltac aimg V m HM A cs H :=
  pose proof (aimg_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

Lemma aimg_bytes : forall V (m : mem) (l : list mfact) A bs,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (length bs) <=? hi') | _ => false end) l = true ->
  img_bytes_b A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at asegs m A bs.
Proof.
  intros V m l A bs HM HE HB HA HHI. apply img_bytes_at; [| exact HB| exact HA| exact HHI].
  eapply mimg_cover; [exact HM| exact HE].
Qed.

Lemma rw_cell_of_bytes : forall (m : mem) A cs, cells_wf cs -> bytes_at asegs m A (cells_bytes cs) ->
  0xa9000 <= A -> A + Z.of_nat (cells_size cs) <= 0x609000 -> rw_cells asegs m A cs.
Proof. intros m A cs WF B H1 H2. split; [split; [exact WF| exact B]|]. apply a0_rw_image_wr_at; lia. Qed.

Definition fact_iv (f : mfact) : option (Z * Z * bool) :=
  match f with
  | MZero (ZLit a) n => Some (a, n, true)
  | MZeroC (ZLit a) n => Some (a, n, true)
  | MFill (ZLit a) n c => Some (a, n, Z.eqb c 0)
  | MCell (ZLit a) w _ => if is_cellw w then Some (a, Z.of_nat w, false) else None
  | _ => None
  end.

Lemma zeros_nth : forall n i, (i < Z.to_nat n)%nat -> nth_error (zeros n) i = Some (Z_to_bv 8 0).
Proof. intros n i Hi. unfold zeros. apply nth_error_repeat. exact Hi. Qed.

Lemma fact_iv_sound : forall V (m : mem) f a n z, mfact_ok asegs V m f -> fact_iv f = Some (a, n, z) ->
  forall x, a <= x < a + n -> (exists v, mrd asegs m (wa x) = Some v) /\ (z = true -> mrd asegs m (wa x) = Some (Z_to_bv 8 0)).
Proof.
  intros V m f a n z OK E x Hx. destruct f as [e w v|e k|e w v|e k|e k c|lo hi|e k|e k|e k]; cbn [fact_iv] in E; try discriminate.
  -   destruct e; try discriminate. destruct (is_cellw w) eqn:W; [|discriminate]. injection E as <- <- <-.
    cbn [mfact_ok zv] in OK. destruct OK as [[WF (B0 & B1 & BB)] _].
    pose proof (cellw_bytes w (zv V v) W) as (Cb & Cs & _).
    cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
    assert (L : length (cbytes (cellw w (zv V v))) = w).
    { destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try discriminate; reflexivity. }
    specialize (BB (Z.to_nat (x - z0)) ltac:(rewrite L; lia)). rewrite Z2Nat.id in BB by lia.
    replace (z0 + (x - z0)) with x in BB by lia. split; [| intros; discriminate].
    destruct (nth_error (cbytes (cellw w (zv V v))) (Z.to_nat (x - z0))) as [b|] eqn:N; [exists b; exact BB|].
    apply nth_error_None in N. rewrite L in N. lia.
  -   destruct e; try discriminate. injection E as <- <- <-.
    cbn [mfact_ok zv] in OK. destruct OK as [[WF (B0 & B1 & BB)] _].
    cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
    assert (L : length (zeros k) = Z.to_nat k) by (unfold zeros; apply repeat_length).
    specialize (BB (Z.to_nat (x - z0)) ltac:(rewrite L; lia)). rewrite Z2Nat.id in BB by lia.
    replace (z0 + (x - z0)) with x in BB by lia. rewrite zeros_nth in BB by lia.
    split; [exists (Z_to_bv 8 0); exact BB| intros _; exact BB].
  -   destruct e; try discriminate. injection E as <- <- <-.
    cbn [mfact_ok zv] in OK. specialize (OK (x - z0) ltac:(lia)). replace (z0 + (x - z0)) with x in OK by lia.
    unfold mrd. rewrite OK. split; [eexists; reflexivity| intros _; reflexivity].
  -   destruct e; try discriminate. injection E as <- <- <-.
    cbn [mfact_ok zv] in OK. specialize (OK (x - z0) ltac:(lia)). replace (z0 + (x - z0)) with x in OK by lia.
    unfold mrd. rewrite OK. split; [eexists; reflexivity| intros Hc; apply Z.eqb_eq in Hc; subst c; reflexivity].
Qed.

Fixpoint find_next (z : bool) (l : list mfact) (x : Z) : option Z :=
  match l with
  | [] => None
  | f :: l' => match fact_iv f with
               | Some (a, n, zf) => if (a <=? x) && (x <? a + n) && (implb z zf) then Some (a + n) else find_next z l' x
               | None => find_next z l' x
               end
  end.
Lemma find_next_sound : forall V (m : mem) z l x e, Forall (mfact_ok asegs V m) l -> find_next z l x = Some e ->
  x < e /\ forall y, x <= y < e -> (exists v, mrd asegs m (wa y) = Some v) /\ (z = true -> mrd asegs m (wa y) = Some (Z_to_bv 8 0)).
Proof.
  intros V m z l. induction l as [|f l IH]; intros x e HF H; [discriminate|]. inversion HF as [|? ? Hf Hl]; subst.
  cbn [find_next] in H. destruct (fact_iv f) as [[[a n] zf]|] eqn:E; [| exact (IH x e Hl H)].
  destruct ((a <=? x) && (x <? a + n) && implb z zf) eqn:C; [| exact (IH x e Hl H)].
  injection H as <-. apply andb_prop in C as [C Cz]. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  split; [lia|]. intros y Hy. destruct (fact_iv_sound V m f a n zf Hf E y ltac:(lia)) as [R Z0]. split; [exact R|].
  intros ->. apply Z0. destruct zf; [reflexivity| discriminate].
Qed.
Fixpoint cover (z : bool) (l : list mfact) (fuel : nat) (lo hi : Z) : bool :=
  if hi <=? lo then true else
  match fuel with
  | O => false
  | S fuel' => match find_next z l lo with Some e => cover z l fuel' e hi | None => false end
  end.
Lemma cover_sound : forall V (m : mem) z l fuel lo hi, Forall (mfact_ok asegs V m) l -> cover z l fuel lo hi = true ->
  forall y, lo <= y < hi -> (exists v, mrd asegs m (wa y) = Some v) /\ (z = true -> mrd asegs m (wa y) = Some (Z_to_bv 8 0)).
Proof.
  intros V m z l fuel. induction fuel as [|fuel IH]; intros lo hi HF H y Hy; cbn [cover] in H;
    (destruct (Z.leb_spec0 hi lo); [lia|]); [discriminate|].
  destruct (find_next z l lo) as [e|] eqn:E; [|discriminate].
  destruct (find_next_sound V m z l lo e HF E) as [Lt S]. destruct (Z.lt_ge_cases y e); [apply S; lia| apply (IH e hi HF H); lia].
Qed.

Lemma readable_bytes : forall (m : mem) n A, (forall y, A <= y < A + Z.of_nat n -> exists v, mrd asegs m (wa y) = Some v) ->
  0 <= A -> A + Z.of_nat n <= 2^64 -> exists bs, length bs = n /\ bytes_at asegs m A bs.
Proof.
  intros m n. induction n as [|n IH]; intros A R H0 H1.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (R A ltac:(lia)) as [v Hv]. destruct (IH (A + 1) ltac:(intros y Hy; apply R; lia) ltac:(lia) ltac:(lia)) as (bs & L & (_ & _ & B)).
    exists (v :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + rewrite Z.add_0_r. exact Hv.
    + cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.
