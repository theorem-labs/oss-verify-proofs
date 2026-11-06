(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Read.
Variable segs : list Segment.

Definition in_rng (a0 n a : Z) : bool := (a0 <=? a) && (a <? a0 + n).

(* [comment removed for export] *)
Definition frel (A n : Z) (f : mfact) : bool :=
  match f with
  | MCell (ZLit a0) w (ZLit _) => (a0 <? A + n) && (A <? a0 + Z.of_nat w)
  | MZeroC (ZLit a0) k => (a0 <? A + n) && (A <? a0 + k)
  | MImg lo hi => (lo <? A + n) && (A <? hi)
  | _ => false
  end.

Fixpoint fread (MF : list mfact) (a : Z) : option byte :=
  match MF with
  | [] => None
  | MCell (ZLit a0) w (ZLit v) :: r =>
      if in_rng a0 (Z.of_nat w) a then nth_error (cbytes (cellw w v)) (Z.to_nat (a - a0)) else fread r a
  | MZeroC (ZLit a0) k :: r => if in_rng a0 k a then Some (Z_to_bv 8 0) else fread r a
  | MImg lo hi :: r =>
      if (lo <=? a) && (a <? hi)
      then match seg_rom segs (wa a), wview segs (fun _ => None) (wa a) with Some b, Some _ => Some b | _, _ => None end
      else fread r a
  | _ :: r => fread r a
  end.

Fixpoint fchk_go (F : list mfact) (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => match fread F a with Some b' => bv_eqb b b' && fchk_go F (a + 1) r | None => false end
  end.

Definition fchk (MF : list mfact) (A : Z) (bs : list byte) : bool :=
  fchk_go (List.filter (frel A (Z.of_nat (length bs))) MF) A bs.

Lemma nth_error_zeros : forall n i b, nth_error (zeros n) i = Some b -> b = Z_to_bv 8 0.
Proof. intros n i b H. unfold zeros in H. apply nth_error_In in H. apply repeat_spec in H. exact H. Qed.

Lemma fread_sound : forall V m MF a b, Forall (mfact_ok segs V m) MF -> 0 <= a < 2 ^ 64 -> fread MF a = Some b ->
  mrd segs m (wa a) = Some b /\ wview segs m (wa a) <> None.
Proof.
  intros V m MF a b HF Ha. induction MF as [|f r IH]; intros H; cbn [fread] in H; [discriminate|].
  apply Forall_cons_iff in HF as [Hf HF]. specialize (IH HF).
  destruct f as [a0 w v|a0 k| | | |lo hi| | |]; try (apply IH; exact H).
  - (* [comment removed for export] *) destruct a0 as [a0| | | | |]; try (apply IH; exact H). destruct v as [v| | | | |]; try (apply IH; exact H).
    destruct (in_rng a0 (Z.of_nat w) a) eqn:Er; [| apply IH; exact H].
    unfold in_rng in Er. apply andb_prop in Er as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    cbn [mfact_ok zv] in Hf. destruct Hf as [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)].
    assert (Hlen : (Z.to_nat (a - a0) < length (cells_bytes [cellw w v]))%nat).
    { apply nth_error_Some. cbn [cells_bytes]. rewrite app_nil_r. rewrite H. discriminate. }
    pose proof (HB _ Hlen) as Hb. cbn [cells_bytes] in Hb. rewrite app_nil_r in Hb. rewrite H in Hb.
    replace (a0 + Z.of_nat (Z.to_nat (a - a0))) with a in Hb by lia. split; [exact Hb|].
    assert (Hs : Z.of_nat (cells_size [cellw w v]) = Z.of_nat (length (cells_bytes [cellw w v]))) by (rewrite cells_bytes_length; [reflexivity| exact Hwf]).
    specialize (HW (a - a0) ltac:(lia)). replace (a0 + (a - a0)) with a in HW by lia. exact HW.
  - (* [comment removed for export] *) destruct a0 as [a0| | | | |]; try (apply IH; exact H).
    destruct (in_rng a0 k a) eqn:Er; [| apply IH; exact H]. injection H as <-.
    unfold in_rng in Er. apply andb_prop in Er as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    cbn [mfact_ok zv] in Hf. destruct Hf as [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)].
    cbn [cells_bytes cbytes] in HB, B1. rewrite app_nil_r in HB, B1. cbn [cells_size csize] in HW, W1. rewrite Nat.add_0_r in HW, W1.
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
    assert (Hi : (Z.to_nat (a - a0) < length (zeros k))%nat) by (rewrite Hl; lia).
    pose proof (HB _ Hi) as Hb. replace (a0 + Z.of_nat (Z.to_nat (a - a0))) with a in Hb by lia.
    destruct (nth_error (zeros k) (Z.to_nat (a - a0))) as [z|] eqn:Ez; [| apply nth_error_None in Ez; lia].
    rewrite (nth_error_zeros _ _ _ Ez) in Hb. split; [exact Hb|].
    specialize (HW (a - a0) ltac:(lia)). replace (a0 + (a - a0)) with a in HW by lia. exact HW.
  - (* [comment removed for export] *) destruct ((lo <=? a) && (a <? hi))%bool eqn:Er; [| apply IH; exact H].
    apply andb_prop in Er as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    cbn [mfact_ok] in Hf. specialize (Hf a ltac:(lia)).
    destruct (seg_rom segs (wa a)) as [b'|] eqn:Es; [|discriminate].
    destruct (wview segs (fun _ => None) (wa a)) as [bw|] eqn:Ew; [|discriminate]. injection H as <-.
    split; [unfold mrd; rewrite Hf; exact Es|]. unfold wview in *. rewrite Hf. rewrite Ew. discriminate.
Qed.

Lemma fchk_go_sound : forall V m F bs a, Forall (mfact_ok segs V m) F -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  fchk_go F a bs = true ->
  forall i b, nth_error bs i = Some b -> mrd segs m (wa (a + Z.of_nat i)) = Some b /\ wview segs m (wa (a + Z.of_nat i)) <> None.
Proof.
  intros V m F bs. induction bs as [|b0 r IH]; intros a HF H0 H1 H i b Hn; [destruct i; discriminate|].
  cbn [fchk_go] in H. destruct (fread F a) as [b'|] eqn:Ef; [|discriminate]. apply andb_prop in H as [Hb H].
  unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq in Hb. subst b'. cbn [length] in H1.
  destruct i as [|i].
  - cbn in Hn. injection Hn as <-. rewrite Z.add_0_r. apply (fread_sound V m F a b0 HF); [lia | exact Ef].
  - cbn in Hn. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    apply (IH (a + 1) HF); [lia | lia | exact H | exact Hn].
Qed.

Theorem chunk_of_facts : forall V m MF A cs,
  Forall (mfact_ok segs V m) MF -> cells_wf cs -> fchk MF A (cells_bytes cs) = true ->
  0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 -> rw_cells segs m A cs.
Proof.
  intros V m MF A cs HF Hwf Hc H0 H1. unfold fchk in Hc.
  assert (HF' : Forall (mfact_ok segs V m) (List.filter (frel A (Z.of_nat (length (cells_bytes cs)))) MF)).
  { apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _]. exact (proj1 (Forall_forall _ _) HF f Hf). }
  assert (El : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact Hwf).
  pose proof (fchk_go_sound V m _ (cells_bytes cs) A HF' H0 ltac:(rewrite El; exact H1) Hc) as G.
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [rewrite El; exact H1|]. intros i Hi.
    destruct (nth_error (cells_bytes cs) i) as [b|] eqn:E; [exact (proj1 (G i b E)) | apply nth_error_None in E; lia].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E; [exact (proj2 (G _ b E)) | apply nth_error_None in E; lia].
Qed.

End Read.
