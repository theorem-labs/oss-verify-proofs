(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition pin_of (s : store) (x : int) : option Z :=
  match vbound s x with
  | Some (lo, hi) => if lo =? hi then Some lo else None
  | None => None
  end.

Lemma pin_of_sound (ρ : valuation) (s : store) (x : int) (z : Z) : sat ρ s -> pin_of s x = Some z -> ρ x = z.
Proof.
  intros Hs H. unfold pin_of in H. destruct (vbound s x) as [[lo hi]|] eqn:E; [|discriminate].
  destruct (Z.eqb_spec lo hi) as [->|]; [|discriminate]. injection H as <-.
  pose proof (vbound_sound ρ s x Hs _ E) as Hb. cbn [fst snd] in Hb. lia.
Qed.

(* [comment removed for export] *)
Fixpoint canon_ts (s : store) (ts : terms) : Z * terms :=
  match ts with
  | [] => (0, [])
  | (x, a) :: r =>
      let cr := canon_ts s r in
      match pin_of s x with
      | Some z => (fst cr + a * z, snd cr)
      | None => (fst cr, (x, a) :: snd cr)
      end
  end.

Lemma canon_ts_sound (ρ : valuation) (s : store) (ts : terms) :
  sat ρ s -> teval ρ ts = fst (canon_ts s ts) + teval ρ (snd (canon_ts s ts)).
Proof.
  intros Hs. induction ts as [|[x a] r IH]; [reflexivity|]. cbn [canon_ts teval].
  destruct (pin_of s x) as [z|] eqn:E; cbn [fst snd teval].
  - rewrite (pin_of_sound ρ s x z Hs E). lia.
  - lia.
Qed.

Definition canon_form (s : store) (ts : terms) (o : w64) : terms * w64 :=
  let cr := canon_ts s ts in (snd cr, w_add o (wofZ (fst cr))).

Lemma canon_form_sound (ρ : valuation) (s : store) (ts : terms) (o : w64) :
  sat ρ s -> smod ρ (fst (canon_form s ts o)) (snd (canon_form s ts o)) = smod ρ ts o.
Proof.
  intros Hs. unfold canon_form, smod. cbn [fst snd]. rewrite wZ_add, wZ_wofZ.
  rewrite (canon_ts_sound ρ s ts Hs). set (c := fst (canon_ts s ts)). set (t := teval ρ (snd (canon_ts s ts))).
  rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc, Zplus_mod_idemp_r. f_equal. ring.
Qed.

Definition canon_region (s : store) (R : region) : region :=
  let f := canon_form s (rg_ts R) (rg_bo R) in
  Rg (fst f) (snd f) (rg_n R) (rg_kind R) (rg_d R) (rg_cells R).

Definition canon_v (s : store) (v : xv) : xv :=
  match v with
  | XS ts o => let f := canon_form s ts o in mk_xs (fst f) (snd f)
  | _ => v
  end.

(* [comment removed for export] *)
Definition restore1 (R R'' : region) : region :=
  Rg (rg_ts R) (rg_bo R) (rg_n R'') (rg_kind R'') (rg_d R'') (rg_cells R'').

Fixpoint restore_bases (A A'' : list region) : list region :=
  match A, A'' with
  | R :: A1, R'' :: A2 => restore1 R R'' :: restore_bases A1 A2
  | _, _ => []
  end.

Lemma rbase_canon (ρ : valuation) (s : store) (R : region) : sat ρ s -> rbase ρ (canon_region s R) = rbase ρ R.
Proof. intros Hs. unfold rbase, canon_region. cbn [rg_ts rg_bo]. apply canon_form_sound. exact Hs. Qed.

Lemma canon_v_sound (ρ : valuation) (s : store) (v : xv) (a : bv 64) : sat ρ s -> xv_val ρ v a -> xv_val ρ (canon_v s v) a.
Proof.
  intros Hs Hv. destruct v as [x|ts o| | | |]; try exact Hv. cbn [canon_v]. apply mk_xs_sound.
  rewrite canon_form_sound by exact Hs. exact Hv.
Qed.

Lemma canon_ts_nil (s : store) : snd (canon_ts s []) = [].
Proof. reflexivity. Qed.

Lemma region_wf_canon (ρ : valuation) (s : store) (R : region) : sat ρ s -> region_wf ρ R -> region_wf ρ (canon_region s R).
Proof.
  intros Hs [W1 [W2 [W3 [W4 W5]]]]. unfold region_wf. rewrite (rbase_canon ρ s R Hs).
  unfold canon_region at 1 2 3 4 5. cbn [rg_n rg_d rg_kind]. repeat split; try assumption.
  intros w i Hk. unfold canon_region, canon_form. cbn [rg_ts fst]. rewrite (W5 w i Hk). reflexivity.
Qed.

Lemma regions_ok_canon (ρ : valuation) (s : store) (A : list region) : sat ρ s -> regions_ok ρ A -> regions_ok ρ (map (canon_region s) A).
Proof.
  intros Hs. induction A as [|R A IH]; intros Hok; [exact I|]. destruct Hok as [Hw [Hd Hok]]. cbn [map regions_ok].
  split; [exact (region_wf_canon ρ s R Hs Hw)|]. split; [|exact (IH Hok)].
  apply Forall_map. eapply Forall_impl; [|exact Hd]. intros Q HQ. unfold rdisj in *. rewrite !rbase_canon by exact Hs. exact HQ.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma RRegion_shape (ρ : valuation) (m : word -> option byte) (R R' : region) :
  rbase ρ R' = rbase ρ R -> rg_n R' = rg_n R -> rg_kind R' = rg_kind R -> rg_d R' = rg_d R -> rg_cells R' = rg_cells R ->
  RRegion segs ρ m R -> RRegion segs ρ m R'.
Proof.
  intros Eb En Ek Ed Ec H.
  assert (H0 : RRegion0 segs ρ m R -> RRegion0 segs ρ m R').
  { intros H0 y Hy. rewrite En in Hy. rewrite Eb, Ek.
    replace (rbyte segs R' y) with (rbyte segs R y) by (unfold rbyte, get_cell_opt; rewrite Ed, Ec, Ek; reflexivity).
    exact (H0 y Hy). }
  unfold RRegion in *. rewrite Ek. destruct (rg_kind R); try (apply H0; exact H).
  rewrite Eb, En. exact H.
Qed.

Lemma RRegion_canon (ρ : valuation) (s : store) (m : word -> option byte) (R : region) :
  sat ρ s -> RRegion segs ρ m R -> RRegion segs ρ m (canon_region s R).
Proof. intros Hs. apply RRegion_shape; try reflexivity. exact (rbase_canon ρ s R Hs). Qed.

Lemma RMem_canon (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) :
  sat ρ s -> RMem segs ρ A m -> RMem segs ρ (map (canon_region s) A) m.
Proof.
  intros Hs [Hok HR]. split; [exact (regions_ok_canon ρ s A Hs Hok)|].
  apply Forall_map. eapply Forall_impl; [|exact HR]. intros R. apply RRegion_canon. exact Hs.
Qed.

Definition a_load2 (s : store) (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match a_load segs A v n with
  | Some l => Some l
  | None => a_load segs (map (canon_region s) A) (canon_v s v) n
  end.

Definition a_store2 (s : store) (A : list region) (v : xv) (nb : list xb) : option (list region) :=
  match a_store segs A v nb with
  | Some A' => Some A'
  | None => match a_store segs (map (canon_region s) A) (canon_v s v) nb with
            | Some A'' => Some (restore_bases A A'')
            | None => None
            end
  end.

Lemma a_load2_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> (1 <= n < 1000)%nat -> a_load2 s A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs HM Hv Hn H. unfold a_load2 in H. destruct (a_load segs A v n) as [l0|] eqn:E.
  - injection H as <-. exact (a_load_sound segs ρ A m v a n l0 HM Hv Hn E).
  - exact (a_load_sound segs ρ _ m _ a n l (RMem_canon ρ s A m Hs HM) (canon_v_sound ρ s v a Hs Hv) Hn H).
Qed.

Lemma a_load2_length (s : store) (A : list region) (v : xv) (n : nat) (l : list xb) : a_load2 s A v n = Some l -> length l = n.
Proof.
  intros H. unfold a_load2 in H. destruct (a_load segs A v n) as [l0|] eqn:E.
  - injection H as <-. exact (a_load_length segs A v n l0 E).
  - exact (a_load_length segs _ _ n l H).
Qed.

(* [comment removed for export] *)
Lemma restore_sound (ρ : valuation) (s : store) (m : word -> option byte) : forall (A A'' : list region),
  sat ρ s -> Forall2 same_fields (map (canon_region s) A) A'' -> regions_ok ρ A -> RMem segs ρ A'' m -> RMem segs ρ (restore_bases A A'') m.
Proof.
  intros A A'' Hs HF Hok0 [Hok HR].
  assert (Hb : forall R R'', same_fields (canon_region s R) R'' -> rbase ρ (restore1 R R'') = rbase ρ R'').
  { intros R R'' [F1 [F2 _]]. unfold rbase, restore1. cbn [rg_ts rg_bo]. rewrite F1, F2. symmetry. apply (rbase_canon ρ s R Hs). }
  assert (Hwf : forall R R'', same_fields (canon_region s R) R'' -> region_wf ρ R -> region_wf ρ R'' -> region_wf ρ (restore1 R R'')).
  { intros R R'' HS [_ [_ [_ [_ V5]]]] [W1 [W2 [W3 [W4 W5]]]]. unfold region_wf. rewrite (Hb R R'' HS).
    unfold restore1 at 1 2 3 4. cbn [rg_n rg_d rg_kind]. repeat split; try assumption.
    intros w i Hk. unfold restore1 in Hk |- *. cbn [rg_ts rg_kind] in Hk |- *. destruct HS as [_ [_ [_ [F4 _]]]]. unfold canon_region in F4. cbn [rg_kind] in F4.
    rewrite F4 in Hk. exact (V5 w i Hk). }
  revert A'' HF Hok HR Hok0. induction A as [|R A IH]; intros A'' HF Hok HR Hok0; inversion HF as [|? R'' ? B HS HF']; subst; cbn [restore_bases].
  - split; [exact I | constructor].
  - destruct Hok as [W [Hd Hok']]. destruct Hok0 as [W0 [_ Hok0']]. apply Forall_cons_iff in HR as [HR1 HR2].
    destruct (IH B HF' Hok' HR2 Hok0') as [IH1 IH2]. split.
    + split; [exact (Hwf R R'' HS W0 W)|]. split; [|exact IH1].
      clear -Hd HF' Hb HS. revert B HF' Hd. induction A as [|Q A IHA]; intros B HF' Hd; inversion HF' as [|? Q'' ? B' HQ HF'']; subst; cbn [restore_bases]; constructor.
      * inversion Hd as [|? ? Hd1 _]; subst. unfold rdisj in *. rewrite (Hb R R'' HS), (Hb Q Q'' HQ). exact Hd1.
      * inversion Hd; subst. apply IHA; assumption.
    + constructor; [|exact IH2]. apply (RRegion_shape ρ m R''); try reflexivity; [exact (Hb R R'' HS) | exact HR1].
Qed.

Lemma a_store2_sound (ρ : valuation) (s : store) (A A' : list region) (m : word -> option byte) (v : xv) (a : bv 64) (nb : list xb) (bs : list byte) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> Forall2 (xb_bv ρ) nb bs ->
  a_store2 s A v nb = Some A' ->
  store_ok segs m a (length nb) = true /\ RMem segs ρ A' (write_to_mem m a bs).
Proof.
  intros Hs HM Hv Hn Hf H. unfold a_store2 in H. destruct (a_store segs A v nb) as [A0|] eqn:E.
  - injection H as <-. exact (a_store_sound segs ρ A A0 m v a nb bs HM Hv Hn Hf E).
  - destruct (a_store segs (map (canon_region s) A) (canon_v s v) nb) as [A''|] eqn:E2; [|discriminate]. injection H as <-.
    destruct (a_store_sound segs ρ _ A'' m _ a nb bs (RMem_canon ρ s A m Hs HM) (canon_v_sound ρ s v a Hs Hv) Hn Hf E2) as [Hok HM''].
    split; [exact Hok|]. apply (restore_sound ρ s); [exact Hs | exact (a_store_fields segs _ _ _ _ E2) | exact (proj1 HM) | exact HM''].
Qed.

End WithSegs.
