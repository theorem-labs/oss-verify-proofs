(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChFix FxChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition B17 : Z := 0x7fff7000.      Definition S17 : Z := 0x10000000.
Definition B16 : Z := 0x8fff7000.      Definition S16 : Z := 0x20000000000.
Definition B15 : Z := 0x2008fff7000.   Definition S15 : Z := 0xdfff0001000.
Definition KHIZ : Z := 0x10007fff8000.

Fixpoint gidx (gs : list (lin * lin * gkind)) (b : lin) (k : nat) : option nat :=
  match gs with [] => None | g :: r => if lin_eqb (fst (fst g)) b then Some k else gidx r b (Datatypes.S k) end.
Definition is_cg (g : lin * lin * gkind) (b s : Z) : bool := (lin_eqb (fst (fst g)) (lconst b) && lin_eqb (snd (fst g)) (lconst s))%bool.

Definition lowb_chk (S : sst) (M : smodel) (j i17 i16 i15 : nat) : option fact :=
  match nth_error (sm_maps M) j, nth_error (sm_maps M) i17, nth_error (sm_maps M) i16, nth_error (sm_maps M) i15 with
  | Some gj, Some g17, Some g16, Some g15 =>
      if (negb (Nat.eqb j i17) && negb (Nat.eqb j i16) && negb (Nat.eqb j i15) && is_cg g17 B17 S17 && is_cg g16 B16 S16 && is_cg g15 B15 S15 &&
          lwf (s_next S) (fst (fst gj)) && Z.ltb (snd (irange (s_facts S) (fst (fst gj)))) KHIZ && Z.leb 0 (B17 - gsz_lo (s_facts S) gj) && negb (is_mark gj))%bool
      then Some (FRange (fst (fst gj)) 0 (B17 - gsz_lo (s_facts S) gj)) else None
  | _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition lowb_post (S : sst) (M : smodel) (b : lin) : option sst :=
  match gidx (sm_maps M) b 0, gidx (sm_maps M) (lconst B17) 0, gidx (sm_maps M) (lconst B16) 0, gidx (sm_maps M) (lconst B15) 0 with
  | Some j, Some i17, Some i16, Some i15 =>
      match lowb_chk S M j i17 i16 i15 with Some f => Some (add_fact S f) | None => Some S end
  | _, _, _, _ => Some S
  end.

Section Low.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma uE_lconst : forall E c, 0 <= c < two64 -> uE E (lconst c) = c.
Proof. LiaFast.lf_pins LiaFast.u0. intros E c Hc. unfold uE. rewrite lden_lconst, u_Z_to_bv. apply Z.mod_small. exact Hc. Qed.

#[using="Type"] Lemma den_lowb : forall E S M ms model b S', DEN segs LIMIT model0 mem0 E S M ms model -> lowb_post S M b = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model b S' Hd Hp. unfold lowb_post in Hp.
  destruct (gidx (sm_maps M) b 0) as [j|]; [|injection Hp as <-; exact Hd].
  destruct (gidx (sm_maps M) (lconst B17) 0) as [i17|]; [|injection Hp as <-; exact Hd].
  destruct (gidx (sm_maps M) (lconst B16) 0) as [i16|]; [|injection Hp as <-; exact Hd].
  destruct (gidx (sm_maps M) (lconst B15) 0) as [i15|]; [|injection Hp as <-; exact Hd].
  destruct (lowb_chk S M j i17 i16 i15) as [f|] eqn:Hc; [|injection Hp as <-; exact Hd]. injection Hp as <-.
  unfold lowb_chk in Hc.
  destruct (nth_error (sm_maps M) j) as [gj|] eqn:Hj; [|discriminate]. destruct (nth_error (sm_maps M) i17) as [g17|] eqn:H17; [|discriminate].
  destruct (nth_error (sm_maps M) i16) as [g16|] eqn:H16; [|discriminate]. destruct (nth_error (sm_maps M) i15) as [g15|] eqn:H15; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end. injection Hc as <-.
  repeat match type of Hb with (_ && _)%bool = true => let X := fresh "X" in apply andb_prop in Hb as [Hb X] end.
  rename X into Hnm, X0 into Hnn, X1 into Hlt, X2 into Hwj, X3 into C15, X4 into C16, X5 into C17, X6 into N15, X7 into N16.
  apply negb_true_iff in Hnm. apply negb_true_iff, Nat.eqb_neq in Hb, N16, N15. apply Z.ltb_lt in Hlt. apply Z.leb_le in Hnn.
  unfold is_cg in C15, C16, C17. apply andb_prop in C15 as [C15b C15s]. apply andb_prop in C16 as [C16b C16s]. apply andb_prop in C17 as [C17b C17s].
  apply lin_eqb_eq in C15b, C15s, C16b, C16s, C17b, C17s.
  pose proof (dn_sden segs LIMIT model0 mem0 E S M ms model Hd) as Hsd. destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HF & _).
  apply den_addfact; [exact Hd|]. intros E' Ha'. cbn [fact_ok].
  rewrite <- (lden_agree (s_next S) E E' _ Hwj Ha').
  pose proof (dn_pd segs LIMIT model0 mem0 E S M ms model Hd) as Hpd. rewrite (dn_maps segs LIMIT model0 mem0 E S M ms model Hd) in Hpd.
  assert (M17 : is_mark g17 = false) by (destruct g17 as [[b17 s17] k17]; cbn [fst snd] in C17s; rewrite C17s; apply is_mark_csize).
  assert (M16 : is_mark g16 = false) by (destruct g16 as [[b16 s16] k16]; cbn [fst snd] in C16s; rewrite C16s; apply is_mark_csize).
  assert (M15 : is_mark g15 = false) by (destruct g15 as [[b15 s15] k15]; cbn [fst snd] in C15s; rewrite C15s; apply is_mark_csize).
  pose proof (pdisj_lden_nth _ _ _ j i17 _ _ Hpd Hj H17 Hb Hnm M17) as D17. pose proof (pdisj_lden_nth _ _ _ j i16 _ _ Hpd Hj H16 N16 Hnm M16) as D16.
  pose proof (pdisj_lden_nth _ _ _ j i15 _ _ Hpd Hj H15 N15 Hnm M15) as D15.
  pose proof (dn_gsh segs LIMIT model0 mem0 E S M ms model Hd) as Hgsh. rewrite Forall_forall in Hgsh.
  destruct (Hgsh gj (nth_error_In _ _ Hj)) as (S1 & _ & _ & S4 & _).
  unfold iv_disj, FxBacking.B, FxBacking.S, gden in D17, D16, D15. cbn [fst snd] in D17, D16, D15.
  rewrite C17b, C17s in D17. rewrite C16b, C16s in D16. rewrite C15b, C15s in D15.
  change (bv_unsigned (lden E (lconst B17))) with (uE E (lconst B17)) in D17. change (bv_unsigned (lden E (lconst S17))) with (uE E (lconst S17)) in D17.
  change (bv_unsigned (lden E (lconst B16))) with (uE E (lconst B16)) in D16. change (bv_unsigned (lden E (lconst S16))) with (uE E (lconst S16)) in D16.
  change (bv_unsigned (lden E (lconst B15))) with (uE E (lconst B15)) in D15. change (bv_unsigned (lden E (lconst S15))) with (uE E (lconst S15)) in D15.
  rewrite !uE_lconst in D17, D16, D15 by (unfold B17, S17, B16, S16, B15, S15, two64; lia).
  pose proof (irange_sound E (s_facts S) (fst (fst gj)) HF) as Ir.
  pose proof (gsz_bounds E (s_facts S) gj HF) as Bj. pose proof (gsz_lo_nonneg (s_facts S) gj) as Bj0.
  pose proof (u_range E (fst (fst gj))) as Rj.
  unfold gsz, uE in Bj, S1, S4.
  set (bj := bv_unsigned (lden E (fst (fst gj)))) in *. set (sj := bv_unsigned (lden E (snd (fst gj)))) in *.
  unfold B17, S17, B16, S16, B15, S15, KHIZ in *. lia.
Qed.
End Low.
(* [comment removed for export] *)
