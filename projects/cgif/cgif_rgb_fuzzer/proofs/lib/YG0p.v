(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0d YG0n YG0o YG0t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition dev (s : astate) : Z :=
Z.max (st_nev s) (Z.max (nrec s) (Z.max (cdivZ (wpot s) (2 ^ 17)) (cdivZ (sec_hulls s) HULL_UNIT))).
Lemma dev_init : dev init_state = 0.
Proof. reflexivity. Qed.
Lemma vev_init : vev init_state <= 0.
Proof. vm_compute. discriminate. Qed.
Lemma vev_le_dev : forall s, vev s <= dev s.
Proof.
intros s. unfold vev, dev. unfold EV_BIG, VEV_MAX, NREC_MAX, WPOT_MAX, HPOT_MAX, HULL_UNIT.
change ((2 ^ 31 - 2 ^ 23) / 2 ^ 17) with 16320. change (3 * 2 ^ 36 / (2 ^ 25 + 2 ^ 14)) with 6141. lia.
Qed.
Lemma dev_le : forall s s' k, 0 <= k -> bud_le s s' k k (2 ^ 17 * k) (HULL_UNIT * k) -> dev s' <= dev s + k.
Proof.
intros s s' k Hk (A1 & A2 & A3 & A4). unfold dev.
pose proof (cdivZ_step (wpot s) (wpot s') (2 ^ 17) k ltac:(lia) A3) as B3.
pose proof (cdivZ_step (sec_hulls s) (sec_hulls s') HULL_UNIT k ltac:(unfold HULL_UNIT; lia) A4) as B4. lia.
Qed.
Lemma dev_jbud : forall s s' k, 0 <= k -> jbud s s' k -> dev s' <= dev s + k.
Proof. intros s s' k Hk (_ & D). exact (dev_le s s' k Hk D). Qed.
Lemma dev_bud : forall s d, dev s <= d -> st_nev s <= d /\ nrec s <= d /\ wpot s <= 2 ^ 17 * d /\ sec_hulls s <= HULL_UNIT * d.
Proof.
intros s d H. unfold dev in H.
assert (H3 : cdivZ (wpot s) (2 ^ 17) <= d) by lia. assert (H4 : cdivZ (sec_hulls s) HULL_UNIT <= d) by lia.
apply cdivZ_le in H3; [|lia]. apply cdivZ_le in H4; [|unfold HULL_UNIT; lia]. lia.
Qed.
Definition dbud (E C W H : Z) (s : astate) (r d : Z) : Prop :=
bud_ok s (E * r + d) (C * r + d) (W * r + 2 ^ 17 * d) (H * r + HULL_UNIT * d + 2 ^ 24).
Lemma dbud_of_dev : forall E C W H s r d d0,
dev s <= d0 ->
d0 + E * r + d <= EV_BIG -> d0 + C * r + d <= NREC_MAX -> 2 ^ 17 * (d0 + d) + W * r <= WPOT_MAX ->
HULL_UNIT * (d0 + d) + H * r + 2 ^ 24 <= HPOT_MAX ->
dbud E C W H s r d.
Proof. intros E C W H s r d d0 Hd F1 F2 F3 F4. destruct (dev_bud s d0 Hd) as (D1 & D2 & D3 & D4). unfold dbud, bud_ok. lia. Qed.
Lemma dbud_lib_pre : forall E C W H s r d, 0 <= E -> 0 <= C -> 0 <= W -> 0 <= H -> 1 <= r -> 0 <= d -> dbud E C W H s r d -> bud_ok s E C W H.
Proof.
intros E C W H s r d HE HC HW HH Hr Hd B. unfold dbud in B. eapply bud_ok_mono; [exact B | nia | nia | nia | unfold HULL_UNIT; nia].
Qed.
Lemma dbud_lib_post : forall E C W H s s' r d, dbud E C W H s (r + 1) d -> bud_le s s' E C W H -> dbud E C W H s' r d.
Proof.
intros E C W H s s' r d B D. unfold dbud in *. apply (bud_ok_le s s' E C W H); [|exact D].
eapply bud_ok_mono; [exact B | lia | lia | lia | lia].
Qed.


Lemma dbud_vev : forall E C W H s r d, 0 <= E -> 0 <= C -> 0 <= W -> 0 <= H -> 0 <= r -> dbud E C W H s r d -> vev s + d <= VEV_MAX.
Proof.
intros E C W H s r d HE HC HW HH Hr B. apply vev_of_bud. unfold dbud in B. eapply bud_ok_mono; [exact B | nia | nia | nia | nia].
Qed.
Lemma qtightB_init : qtightB init_state.
Proof. split; [exact qtight_init | exact BigInv_init]. Qed.
Section a.
Variable U : list (list Z).
Hypothesis ML : model_laws U.
Lemma drv_malloc_big : forall s n tr, Wf U s -> qtightB s -> vev s < VEV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr s) (fun ns r => malloc_post U s n ns r /\ (qtightB s -> qtightB (snd r)) /\ jbud s (snd r) 1).
Proof.
intros s n tr HW HQ HV Hn Hl Htr. destruct (regime_big_vev U s HW HQ HV) as [RB _].
eapply atok_mono; [| exact (ml_malloc_big U ML s n tr HW RB Hn Hl Htr)].
intros ns [p s'] (MP & BI & MG). split; [exact MP|]. cbn [snd] in *.
pose proof MP as MP'. cbn [malloc_post] in MP'. destruct MP' as (_ & NE & _ & _ & _ & QT).
split; [intros (Q & _); split; [exact (QT Q) | exact BI] | exact (jbud_malloc1 s n s' Hn MG NE)].
Qed.
Lemma drv_free_big : forall s p n tr, Wf U s -> qtightB s -> vev s < VEV_MAX -> (p = PNull \/ In (p, n) (blocks s)) -> In tr U ->
atok true (free p tr s) (fun ns r => free_post U s p n ns r /\ (qtightB s -> qtightB (snd r)) /\ jbud s (snd r) 1).
Proof.
intros s p n tr HW HQ HV Hp Htr. destruct (regime_big_vev U s HW HQ HV) as [RB _].
eapply atok_mono; [| exact (ml_free_big U ML s p n tr HW RB Hp Htr)].
intros ns r (FP & BI & FG). split; [exact FP|].
pose proof FP as FP'. unfold free_post in FP'. cbn zeta in FP'. destruct FP' as (_ & _ & _ & _ & _ & QT).
split; [intros (Q & _); split; [exact (QT Q) | exact BI] | exact (jbud_free1 U s p n ns r FG FP)].
Qed.
End a.
Ltac drv_facts :=
pose proof vev_init; pose proof dev_init;
repeat match goal with
| H : jbud ?s ?s' ?k |- _ =>
lazymatch goal with
| _ : dev s' <= dev s + k |- _ => fail
| _ => pose proof (proj1 H : vev s' <= vev s + k); pose proof (dev_jbud s s' k ltac:(lia) H)
end
end;
repeat match goal with
| H : dev ?s <= _ |- _ => lazymatch goal with _ : vev s <= dev s |- _ => fail | _ => pose proof (vev_le_dev s) end
| H : dev ?s + _ <= _ |- _ => lazymatch goal with _ : vev s <= dev s |- _ => fail | _ => pose proof (vev_le_dev s) end
| H : _ <= dev ?s + _ |- _ => lazymatch goal with _ : vev s <= dev s |- _ => fail | _ => pose proof (vev_le_dev s) end
end.
Ltac drv_lia := drv_facts; unfold VEV_MAX in *; lia.
Goal forall s s1 s2, dev s <= 64 -> jbud s s1 1 -> jbud s1 s2 1 -> vev s2 < VEV_MAX /\ dev s2 <= dev s + 2 /\ vev s1 + 2 <= VEV_MAX.
Proof. intros s s1 s2 H J1 J2. repeat split; drv_lia. Qed.
Goal forall s', jbud init_state s' 1 -> vev s' < VEV_MAX /\ dev s' <= 1 /\ vev init_state < VEV_MAX.
Proof. intros s' J. repeat split; drv_lia. Qed.
Goal forall s s' f, dev s + 2 * Z.of_nat (S f) <= 64 -> dev s' <= dev s + 2 -> dev s' + 2 * Z.of_nat f <= 64 /\ vev s + 2 <= VEV_MAX.
Proof. intros s s' f H J. split; drv_lia. Qed.
