(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
Import ListNotations.
Open Scope Z_scope.

Definition with_v (e : lent) (v : Z) : lent := LE (le_ix e) (le_k e) (le_kn e) (le_ks e) v.
Definition sv_with_v (s : slotv) (v : Z) : slotv := SV (sv_k s) (sv_kc s) (sv_pad s) v (sv_nx s) (sv_pv s).

Lemma map_ix_upd_with_v : forall es j e v, nth_error es j = Some e -> map le_ix (upd es j (with_v e v)) = map le_ix es.
Proof.
intros es. induction es as [|x es IH]; intros [|j] e v E; cbn in *; try discriminate.
- injection E as ->. reflexivity.
- rewrite (IH j e v E). reflexivity.
Qed.

Lemma nth_error_upd_with_v : forall es j e v i, nth_error es j = Some e ->
nth_error (upd es j (with_v e v)) i = if Nat.eqb i j then Some (with_v e v) else nth_error es i.
Proof.
intros es j e v i E. destruct (Nat.eqb_spec i j) as [->|NE].
- apply nth_error_upd_same. apply (proj1 (nth_error_Some es j)). rewrite E; discriminate.
- rewrite nth_error_upd_other by (intros X; apply NE; symmetry; exact X). reflexivity.
Qed.

Lemma nx_of_ix : forall tbl es es' j, map le_ix es' = map le_ix es -> nx_of tbl es' j = nx_of tbl es j.
Proof.
intros tbl es es' j H. unfold nx_of.
pose proof (f_equal (fun l => nth_error l (S j)) H) as X. cbn beta in X. rewrite !nth_error_map in X.
destruct (nth_error es' (S j)), (nth_error es (S j)); cbn in X; try discriminate; [injection X as X; rewrite X|]; reflexivity.
Qed.
Lemma pv_of_ix : forall tbl es es' j, map le_ix es' = map le_ix es -> pv_of tbl es' j = pv_of tbl es j.
Proof.
intros tbl es es' j H. unfold pv_of. destruct j as [|j']; [reflexivity|].
pose proof (f_equal (fun l => nth_error l j') H) as X. cbn beta in X. rewrite !nth_error_map in X.
destruct (nth_error es' j'), (nth_error es j'); cbn in X; try discriminate; [injection X as X; rewrite X|]; reflexivity.
Qed.
Lemma hd_of_ix : forall tbl es es', map le_ix es' = map le_ix es -> hd_of tbl es' = hd_of tbl es.
Proof.
intros tbl es es' H. rewrite !hd_of_nth.
pose proof (f_equal (fun l => nth_error l 0) H) as X. cbn beta in X. rewrite !nth_error_map in X.
destruct (nth_error es' 0), (nth_error es 0); cbn in X; try discriminate; [injection X as X; rewrite X|]; reflexivity.
Qed.
Lemma last_map_ix : forall (l : list lent) d, le_ix (last l d) = last (map le_ix l) (le_ix d).
Proof.
induction l as [|x l IH]; intros d; [reflexivity|]. cbn [map last]. destruct l as [|y l']; [reflexivity|]. exact (IH d).
Qed.
Lemma tl_of_ix : forall tbl es es', map le_ix es' = map le_ix es -> tl_of tbl es' = tl_of tbl es.
Proof.
intros tbl es es' H. unfold tl_of.
assert (L : length es' = length es) by (rewrite <- (length_map le_ix es'), <- (length_map le_ix es), H; reflexivity).
destruct es' as [|x es1]; destruct es as [|y es2]; cbn in L; try discriminate; [reflexivity|].
f_equal. change (le_ix (last (x :: es1) (LE 0 0 0 [] 0)) = le_ix (last (y :: es2) (LE 0 0 0 [] 0))).
rewrite !last_map_ix, H. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

#[using="Type"] Lemma lh_open_slot : forall ffn m t tbl size es svs j e,
lh_openf segs fn ffn m t tbl size es svs -> nth_error es j = Some e ->
exists s, nth_error svs (le_ix e) = Some s /\ (le_ix e < length svs)%nat /\
rw_cells segs m (ent_addr tbl (le_ix e))
[C8 (Z_to_bv 64 (le_k e)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (sv_pad s)); C8 (Z_to_bv 64 (le_v e));
C8 (Z_to_bv 64 (nx_of tbl es j)); C8 (Z_to_bv 64 (pv_of tbl es j))].
Proof.
intros ffn m t tbl size es svs j e (HDR & SL & (LK1 & _) & _) Hj.
destruct (LK1 j e Hj) as (s & Es & Ek & Ekc & Ev & Enx & Epv).
exists s. split; [exact Es|]. split; [apply (proj1 (nth_error_Some svs (le_ix e))); rewrite Es; discriminate|].
pose proof (SL (le_ix e) s Es) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C. exact C.
Qed.

#[using="Type"] Lemma pv_of_spec : forall tbl es j,
pv_of tbl es j = match j with O => 0 | S j' => match nth_error es j' with Some e' => ent_addr tbl (le_ix e') | None => 0 end end.
Proof. reflexivity. Qed.

#[using="Type"] Lemma lh_open_set_val : forall ffn m m' t tbl size es svs j e s v' W,
lh_openf segs fn ffn m t tbl size es svs -> nth_error es j = Some e -> nth_error svs (le_ix e) = Some s ->
0 <= v' < 2^64 ->
munch W m m' -> wmono segs m m' ->
Forall (fun iv => ent_addr tbl (le_ix e) + 16 <= fst iv /\ snd iv <= ent_addr tbl (le_ix e) + 24) W ->
(t + 56 <= tbl \/ tbl + 40 * size <= t) ->
(forall x, In x es -> tbl + 40 * size <= le_k x \/ le_k x + le_kn x <= tbl) ->
rw_cells segs m' (ent_addr tbl (le_ix e))
[C8 (Z_to_bv 64 (le_k e)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (sv_pad s)); C8 (Z_to_bv 64 v');
C8 (Z_to_bv 64 (nx_of tbl es j)); C8 (Z_to_bv 64 (pv_of tbl es j))] ->
lh_openf segs fn ffn m' t tbl size (upd es j (with_v e v')) (upd svs (le_ix e) (sv_with_v s v')).
Proof.
intros ffn m m' t tbl size es svs j e s v' W (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen) Hj Es Hv MU WM HW SEP KSEP NEW.
pose proof LINK as (LK1 & LK2 & LK3 & LK4).
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Es; discriminate)) as Hix.
pose proof (map_ix_upd_with_v es j e v' Hj) as MIX.
assert (LEN' : length (upd es j (with_v e v')) = length es) by apply upd_length.
destruct (LK1 j e Hj) as (s0 & Es0 & Ek & Ekc & Ev & Enx & Epv). rewrite Es in Es0. injection Es0 as <-.
split; [| split; [| split; [| split; [| split; [exact Hsz | split; [rewrite LEN'; exact Hcnt | rewrite upd_length; exact Hlen]]]]]].
-
unfold lh_hdrf in *. rewrite LEN', (hd_of_ix tbl es _ MIX), (tl_of_ix tbl es _ MIX).
eapply (rw_cells_transport segs W m m'); [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
rewrite <- Hlen in SEP. clear -HW SEP Hix. induction W as [|[a b] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2. split; [unfold ent_addr in *; nia | apply IH; exact HW].
-
eapply lh_slots_write1; [exact SL | exact Hix | exact MU | exact WM | | ].
+ intros i NE Hi. unfold ivs_miss_slot. clear -HW NE Hi Hix. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2. apply Forall_cons; [cbn | apply IH; exact HW].
unfold ent_addr in *. assert (Z.of_nat i + 1 <= Z.of_nat (le_ix e) \/ Z.of_nat (le_ix e) + 1 <= Z.of_nat i) by lia. lia.
+ unfold slot_cells, sv_with_v. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Ek, Ekc, Enx, Epv. exact NEW.
-
split; [| split; [| split; [rewrite MIX; exact LK3 |]]].
+ intros j' x E. rewrite (nth_error_upd_with_v es j e v' j' Hj) in E.
destruct (Nat.eqb_spec j' j) as [->|NE].
* injection E as <-. cbn [le_ix le_k le_v with_v]. exists (sv_with_v s v').
rewrite nth_error_upd_same by exact Hix. split; [reflexivity|]. cbn [sv_with_v sv_k sv_kc sv_v sv_nx sv_pv].
rewrite (nx_of_ix tbl es _ j MIX), (pv_of_ix tbl es _ j MIX). repeat split; assumption.
* destruct (LK1 j' x E) as (sx & Esx & A1 & A2 & A3 & A4 & A5).
assert (NEix : le_ix x <> le_ix e).
{ intros X. apply NE. eapply (proj1 (NoDup_nth_error _) LK3 j' j).
- rewrite length_map. apply (proj1 (nth_error_Some es j')). rewrite E; discriminate.
- erewrite nth_error_map, E, nth_error_map, Hj. cbn. rewrite X. reflexivity. }
exists sx. rewrite nth_error_upd_other by (intros X; apply NEix; symmetry; exact X).
rewrite (nx_of_ix tbl es _ j' MIX), (pv_of_ix tbl es _ j' MIX). repeat split; assumption.
+ intros i sx E NI. rewrite MIX in NI.
assert (NEi : i <> le_ix e) by (intros ->; apply NI; apply in_map_iff; exists e; split; [reflexivity | eapply nth_error_In; exact Hj]).
rewrite nth_error_upd_other in E by (intros X; apply NEi; symmetry; exact X). exact (LK2 i sx E NI).
+ intros x Hx. apply In_nth_error in Hx as [j' E]. rewrite (nth_error_upd_with_v es j e v' j' Hj) in E.
destruct (Nat.eqb j' j); [injection E as <-; cbn; destruct (LK4 e (nth_error_In _ _ Hj)); split; [| split]; try lia | exact (LK4 x (nth_error_In _ _ E))].
-
unfold lh_keys in *. apply Forall_forall. intros x Hx.
apply In_nth_error in Hx as [j' E]. rewrite (nth_error_upd_with_v es j e v' j' Hj) in E.
assert (HK : exists y, In y es /\ le_k y = le_k x /\ le_kn y = le_kn x /\ le_ks y = le_ks x).
{ destruct (Nat.eqb j' j); [injection E as <-; exists e; split; [eapply nth_error_In; exact Hj | repeat split; reflexivity]
| exists x; split; [eapply nth_error_In; exact E | repeat split; reflexivity]]. }
destruct HK as (y & Hy & <- & <- & <-).
destruct (proj1 (Forall_forall _ _) KEYS y Hy) as (Hl & Hnz & junk & C). split; [exact Hl|]. split; [exact Hnz|]. exists junk.
assert (LJ : length ((le_ks y ++ [Z_to_bv 8 0]) ++ junk) = Z.to_nat (le_kn y)) by (destruct C as [[[Wf _] _] _]; rewrite <- app_assoc; exact Wf).
rewrite length_app in LJ. cbn in LJ.
eapply (rw_cells_transport segs W m m'); [exact C | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
specialize (KSEP y Hy). rewrite <- Hlen in KSEP. clear -HW KSEP Hix Hl LJ.
induction W as [|[a b] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2. split; [unfold ent_addr in *; nia | apply IH; exact HW].
Qed.
End WithSegs.
