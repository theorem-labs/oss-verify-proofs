(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxSys AxAcct.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Sound.
Variable ρ' : valuation.
Variable g : int.
Variables a nZ : Z.
Hypothesis Hg : 4096 * ρ' g = a.

Lemma leval_gform : leval ρ' (gform g) = a.
Proof. unfold gform. rewrite leval_lvar. exact Hg. Qed.

Lemma hole_ents_sat (ents : list aent) (s : store) :
  sat ρ' s -> (forall e, In e ents -> a + nZ <= leval ρ' (ae_base e) \/ leval ρ' (ae_base e) + ae_size e <= a) ->
  sat ρ' (hole_ents g nZ ents s).
Proof.
  unfold hole_ents. revert s. induction ents as [|e r IH]; intros s Hs H; [exact Hs|]. cbn [fold_left].
  apply IH; [|intros e' He'; apply H; right; exact He'].
  apply sat_shole; [exact Hs|]. rewrite leval_lsub, leval_gform. destruct (H e (or_introl eq_refl)); lia.
Qed.

Lemma hole_res_sat (res : list (Z * Z)) (s : store) :
  sat ρ' s -> (forall q, In q res -> a + nZ <= fst q \/ fst q + snd q <= a) -> sat ρ' (hole_res g nZ res s).
Proof.
  unfold hole_res. revert s. induction res as [|q r IH]; intros s Hs H; [exact Hs|]. cbn [fold_left].
  apply IH; [|intros q' Hq'; apply H; right; exact Hq'].
  apply sat_shole; [exact Hs|]. rewrite leval_gform. destruct (H q (or_introl eq_refl)); lia.
Qed.

Lemma hole_span_sat (on : bool) (s : store) :
  sat ρ' s -> (on = true -> a + nZ <= sh_lo \/ sh_hi <= a) -> sat ρ' (hole_span g nZ on s).
Proof.
  intros Hs H. unfold hole_span. destruct on; [|exact Hs]. apply sat_shole; [exact Hs|]. rewrite leval_gform. destruct (H eq_refl); lia.
Qed.

Lemma grant_rng_sat (atop : lin) (ghi : Z) (s : store) :
  sat ρ' s -> 0 < a -> 0 < nZ -> a + nZ <= leval ρ' atop -> leval ρ' atop <= 18446744073709551616 -> ρ' g <= ghi ->
  sat ρ' (grant_rng g nZ atop ghi s).
Proof.
  intros Hs Ha Hn Ht Ht2 Hgh. unfold grant_rng. apply sat_sadd; [apply sat_sadd; [exact Hs|]|].
  - rewrite leval_lvar. lia.
  - rewrite leval_lsub, leval_gform. lia.
Qed.

Lemma res_top_disj (res : list (Z * Z)) : forall top t, res_top top res = Some t -> 0 < nZ ->
  (forall q, In q res -> a + nZ <= fst q \/ fst q + snd q <= a) -> top <= a -> t <= a.
Proof.
  induction res as [|q r IH]; intros top t H Hn Hd Ha; cbn [res_top] in H; [injection H as <-; exact Ha|].
  destruct ((fst q =? top) &&& (0 <? snd q)) eqn:E; [|discriminate H]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.ltb_lt in E2.
  apply (IH _ t H Hn (fun q' Hq' => Hd q' (or_intror Hq'))). destruct (Hd q (or_introl eq_refl)); lia.
Qed.

Lemma hole_img_sat (res : list (Z * Z)) (s : store) :
  sat ρ' s -> 0 < nZ -> (forall q, In q res -> a + nZ <= fst q \/ fst q + snd q <= a) -> sat ρ' (hole_img g nZ res s).
Proof.
  intros Hs Hn Hd. unfold hole_img. destruct (res_span res) as [[lo hi]|] eqn:E; [|exact (hole_res_sat res s Hs Hd)]. apply sat_shole; [exact Hs|]. rewrite leval_gform.
  unfold res_span in E. destruct res as [|q r]; [discriminate E|]. destruct (0 <? snd q) eqn:Ep; [|discriminate E]. apply Z.ltb_lt in Ep.
  destruct (res_top (fst q + snd q) r) as [t|] eqn:Et; [|discriminate E]. injection E as <- <-.
  destruct (Hd q (or_introl eq_refl)) as [H|H]; [left; lia | right].
  exact (res_top_disj r _ t Et Hn (fun q' Hq' => Hd q' (or_intror Hq')) H).
Qed.

Theorem grant_facts_sat (atop : lin) (ghi : Z) (on : bool) (ents : list aent) (res : list (Z * Z)) (s : store) :
  sat ρ' s -> 0 < a -> 0 < nZ -> a + nZ <= leval ρ' atop -> leval ρ' atop <= 18446744073709551616 -> ρ' g <= ghi ->
  (forall e, In e ents -> a + nZ <= leval ρ' (ae_base e) \/ leval ρ' (ae_base e) + ae_size e <= a) ->
  (forall q, In q res -> a + nZ <= fst q \/ fst q + snd q <= a) ->
  (on = true -> a + nZ <= sh_lo \/ sh_hi <= a) ->
  sat ρ' (grant_facts g nZ atop ghi on ents res s).
Proof.
  intros Hs Ha Hn Ht Ht2 Hgh He Hr Ho. unfold grant_facts. apply hole_img_sat; [|exact Hn | exact Hr].
  apply hole_span_sat; [|exact Ho]. apply hole_ents_sat; [|intros e0 He0; apply filter_In in He0 as [He0 _]; exact (He e0 He0)].
  apply grant_rng_sat; assumption.
Qed.

End Sound.

Lemma res_lits_disj (res : list (word * word)) (a nZ : Z) :
  (forall q, In q res -> iv_disj a (a + nZ) q) -> forall q, In q (res_lits res) -> a + nZ <= fst q \/ fst q + snd q <= a.
Proof.
  intros H q Hq. unfold res_lits in Hq. apply in_map_iff in Hq as [q0 [<- Hq0]]. cbn [fst snd]. exact (H q0 Hq0).
Qed.
