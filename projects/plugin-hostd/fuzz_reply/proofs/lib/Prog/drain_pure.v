(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v; 12442 of its 12533 lines of code are new or changed and 1138 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/drain_b.v, with its module paths and module names changed; 3 of its 250 lines of code are new or changed and 12286 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF ListTr RelayModel
  RelayKeys RelayRep HarnessRep drain_b_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------
   The round model: the bytes still pending, the rounds a state needs, and one round's equations. *)

(* The pending bytes: the rest of the head text from off, then the other texts. *)
Definition prest (pend : list (list Z)) (off : Z) : list Z :=
  match pend with [] => [] | r :: rs => skipn (Z.to_nat off) r ++ concat rs end.

Definition pstream (s : dstate) : list Z := prest (ds_pend s) (ds_off s).

(* The rounds drain_run needs from s: one per pending byte at most, one for an EINTR, one for the last. *)
Definition dneed (s : dstate) : nat := S (length (pstream s) + Nat.b2n (ds_eintr s)).

Definition dwf (s : dstate) : Prop :=
  0 <= ds_off s /\ forall r rs, ds_pend s = r :: rs -> ds_off s <= Z.of_nat (length r).

(* The head text is not used up (fuzz_recv keeps pending_off below the head text's length). *)
Definition dstrict (s : dstate) : Prop := forall r rs, ds_pend s = r :: rs -> ds_off s < Z.of_nat (length r).

Definition ulen (s : dstate) : Z := Z.of_nat (length (ds_u s)).

(* The capacity after the round's growth; grow_tr's capacity does not depend on the addresses. *)
Definition gcap (cap used : Z) : Z := fst (snd (grow_tr cap used 0 adr0)).

(* The state after the round's growth (the EINTR flag kept), and with the EINTR flag cleared. *)
Definition dgrow (s : dstate) : dstate :=
  DS (gcap (ds_cap s) (ulen s)) (ds_u s) (ds_skip s) (ds_H s) (ds_ka s) (ds_eintr s) (ds_pend s) (ds_off s)
     (ds_ref s) (ds_en s) (ds_ecap s) (ds_no s) (ds_ocap s).

Definition dclr (s : dstate) : dstate :=
  DS (ds_cap s) (ds_u s) (ds_skip s) (ds_H s) (ds_ka s) false (ds_pend s) (ds_off s)
     (ds_ref s) (ds_en s) (ds_ecap s) (ds_no s) (ds_ocap s).

(* A data round of a grown state (relay.c:193-222 with fuzz_recv): the head text, the bytes n it hands over, the
   bytes d, whether the head text is used up, the reference lines, and the relay's chunk. *)
Definition dhead (s : dstate) : list Z := match ds_pend s with [] => [] | r :: _ => r end.
Definition dtail (s : dstate) : list (list Z) := match ds_pend s with [] => [] | _ :: rs => rs end.
Definition dnum (s : dstate) : Z := Z.min (Z.of_nat (length (dhead s)) - ds_off s) (ds_cap s - ulen s).
Definition ddata (s : dstate) : list Z := firstn (Z.to_nat (dnum s)) (skipn (Z.to_nat (ds_off s)) (dhead s)).
Definition dwhole (s : dstate) : bool := ds_off s + dnum s =? Z.of_nat (length (dhead s)).
Definition dref (s : dstate) : list (list Z) := lines (ds_ref s) (ddata s).
Definition dchunk (s : dstate) : list Z * bool * list (list Z) := chunk (ds_u s) (ds_skip s) (ddata s).
Definition drl (s : dstate) : list (list Z) := snd (dchunk s).

Lemma gcap_eq : forall cap used j b, fst (snd (grow_tr cap used j b)) = gcap cap used.
Proof. intros cap used j b. unfold gcap, grow_tr. destruct (cap - used <? 4096); reflexivity. Qed.

Lemma grow_none : forall cap used j b, 4096 <= cap - used -> grow_tr cap used j b = ([], (cap, b)).
Proof. intros cap used j b H. unfold grow_tr. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

(* From cap in {0, 8192, 16384} and used <= min (cap, 6000), one growth leaves at least 4096 bytes free. *)
Lemma grow_room : forall cap used, (cap = 0 \/ cap = 8192 \/ cap = 16384) -> 0 <= used <= 6000 -> used <= cap ->
  4096 <= gcap cap used - used /\ (gcap cap used = 8192 \/ gcap cap used = 16384).
Proof.
  intros cap used Hc Hu Huc. unfold gcap, grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096) as [Lt|Ge]; cbn [fst snd].
  - destruct (Z.eqb_spec cap 0); lia.
  - lia.
Qed.

Lemma prest_data : forall r0 rs off n, 0 <= off -> 0 < n -> off + n <= Z.of_nat (length r0) ->
  Nat.add (length (prest (if off + n =? Z.of_nat (length r0) then rs else r0 :: rs)
                         (if off + n =? Z.of_nat (length r0) then 0 else off + n))) (Z.to_nat n) =
  length (prest (r0 :: rs) off).
Proof.
  intros r0 rs off n H0 Hn Hle. cbn [prest]. rewrite length_app, length_skipn.
  destruct (Z.eqb_spec (off + n) (Z.of_nat (length r0))) as [W|W].
  - destruct rs as [|r1 rs']; cbn [prest concat length app]; [lia|].
    rewrite skipn_O, length_app. lia.
  - cbn [prest]. rewrite length_app, length_skipn. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The model parts of the trace functions (g_capout, keys, array sizes): they do not depend on the addresses. *)

Lemma nret_nil : nretF [] = 0%nat.
Proof. reflexivity. Qed.

(* gesture_seen's array size after the line l. *)
Definition seen_ka (H : list (list Z)) (ka : Z) (l : list Z) : Z := snd (fst (seen_tr H ka l 0 adr0 [])).

Lemma seen_tr_m : forall H ka l j ha ks, snd (fst (seen_tr H ka l j ha ks)) = seen_ka H ka l.
Proof.
  intros H ka l j ha ks. unfold seen_ka, seen_tr.
  destruct (gesture l) as [[k x]|]; [|reflexivity].
  destruct k; cbv iota; destruct (index_of x H); reflexivity.
Qed.

(* lines_run's model part: g_capout, the held keys and the array size after the lines ls. *)
Definition lrun (live : bool) (mx no cap : Z) (H : list (list Z)) (ka : Z) (ls : list (list Z)) : Z * list (list Z) * Z :=
  snd (fst (lines_run live mx no cap H ka ls 0 adr0 adr0 [])).

Lemma lines_run_mm : forall live mx ls no cap H ka j o ha ks j' o' ha' ks',
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = snd (fst (lines_run live mx no cap H ka ls j' o' ha' ks')).
Proof.
  intros live mx ls. induction ls as [|l r IH]; intros no cap H ka j o ha ks j' o' ha' ks'; [reflexivity|].
  cbn [lines_run fst snd]. rewrite !seen_tr_m. apply IH.
Qed.

Lemma lines_run_m : forall live mx no cap H ka ls j o ha ks,
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = lrun live mx no cap H ka ls.
Proof. intros live mx no cap H ka ls j o ha ks. unfold lrun. apply lines_run_mm. Qed.

(* pushes_run's model part: the expected list's capacity after pushing the lines ls. *)
Definition pcapm (n cap : Z) (ls : list (list Z)) : Z := snd (fst (pushes_run n cap ls 0 adr0 [])).

Lemma pushes_run_mm : forall ls n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs j' v' rs'; [reflexivity|]. cbn [pushes_run fst snd]. apply IH.
Qed.

Lemma pushes_run_m : forall n cap ls j v rs, snd (fst (pushes_run n cap ls j v rs)) = pcapm n cap ls.
Proof. intros n cap ls j v rs. unfold pcapm. apply pushes_run_mm. Qed.

(* The model state after a data round of a grown state (drain_run's data branch). *)
Definition dnext (live : bool) (mx : Z) (s : dstate) : dstate :=
  DS (ds_cap s) (fst (fst (dchunk s))) (snd (fst (dchunk s)))
     (snd (fst (lrun live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s))))
     (snd (lrun live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s))) false
     (if dwhole s then dtail s else ds_pend s) (if dwhole s then 0 else ds_off s + dnum s) (feed (ds_ref s) (ddata s))
     (ds_en s + Z.of_nat (length (dref s))) (pcapm (ds_en s) (ds_ecap s) (dref s))
     (ds_no s + Z.of_nat (length (with_nul (drl s))))
     (fst (fst (lrun live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)))).

(* A data round's requests from base j with the addresses a: reference_feed's pushes, list_drop of a used-up head
   text, the relay's lines; and the addresses after. *)
Definition dpush (s : dstate) (j : nat) (a : dadr) : trF * Z * (adrF * list adrF) :=
  pushes_run (ds_en s) (ds_ecap s) (dref s) j (da_ev a) (da_erecs a).

Definition ddrop (s : dstate) (a : dadr) : trF :=
  if dwhole s then list_drop_tra (nth 0 (da_pend a) adr0) (Z.of_nat (length (dhead s))) else [].

Definition dlines (live : bool) (mx : Z) (s : dstate) (j : nat) (a : dadr)
    : trF * (Z * list (list Z) * Z) * (adrF * adrF * list adrF) :=
  lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
    (j + nretF (fst (fst (dpush s j a))) + nretF (ddrop s a)) (da_out a) (da_hp a) (da_keys a).

Definition dround_tr (live : bool) (mx : Z) (s : dstate) (j : nat) (a : dadr) : trF :=
  fst (fst (dpush s j a)) ++ ddrop s a ++ fst (fst (dlines live mx s j a)).

Definition dnext_a (live : bool) (mx : Z) (s : dstate) (j : nat) (a : dadr) : dadr :=
  DA (fst (fst (snd (dlines live mx s j a)))) (da_buf a) (snd (fst (snd (dlines live mx s j a))))
     (snd (snd (dlines live mx s j a))) (if dwhole s then skipn 1 (da_pend a) else da_pend a)
     (fst (snd (dpush s j a))) (snd (snd (dpush s j a))).

(* dnext with the model values read off the address-carrying runs. *)
Definition dnext_j (live : bool) (mx : Z) (s : dstate) (j : nat) (a : dadr) : dstate :=
  DS (ds_cap s) (fst (fst (dchunk s))) (snd (fst (dchunk s))) (snd (fst (snd (fst (dlines live mx s j a)))))
     (snd (snd (fst (dlines live mx s j a)))) false
     (if dwhole s then dtail s else ds_pend s) (if dwhole s then 0 else ds_off s + dnum s) (feed (ds_ref s) (ddata s))
     (ds_en s + Z.of_nat (length (dref s))) (snd (fst (dpush s j a)))
     (ds_no s + Z.of_nat (length (with_nul (drl s)))) (fst (fst (snd (fst (dlines live mx s j a))))).

Lemma dnext_j_eq : forall live mx s j a, dnext_j live mx s j a = dnext live mx s.
Proof. intros live mx s j a. unfold dnext_j, dnext, dlines, dpush. rewrite lines_run_m, pushes_run_m. reflexivity. Qed.

Lemma nret_dround : forall live mx s j a, nretF (dround_tr live mx s j a) =
  (nretF (fst (fst (dpush s j a))) + nretF (ddrop s a) + nretF (fst (fst (dlines live mx s j a))))%nat.
Proof. intros live mx s j a. unfold dround_tr. rewrite !nret_app. lia. Qed.

(* The addresses after the round's growth. *)
Definition agrow (s : dstate) (j : nat) (a : dadr) : dadr :=
  DA (da_out a) (snd (snd (grow_tr (ds_cap s) (ulen s) j (da_buf a)))) (da_hp a) (da_keys a) (da_pend a) (da_ev a)
     (da_erecs a).

Lemma drain_run_fuel : forall f1 f2 live mx s j a, dwf s -> (dneed s <= f1)%nat -> (dneed s <= f2)%nat ->
  drain_run f1 live mx s j a = drain_run f2 live mx s j a.
Proof.
  induction f1 as [|f1 IH]; intros f2 live mx s j a W N1 N2; [unfold dneed in N1; lia|].
  destruct f2 as [|f2]; [unfold dneed in N2; lia|].
  pose proof W as (W0 & W1).
  unfold dneed, pstream in N1, N2.
  cbn [drain_run].
  destruct (ds_eintr s) eqn:EI; cbn [Nat.b2n] in N1, N2.
  - match goal with |- context [drain_run f1 ?l ?m ?s2 ?j2 ?a2] => rewrite (IH f2 l m s2 j2 a2) end;
      [reflexivity | | |].
    + unfold dwf; cbn [ds_off ds_pend]. split; [exact W0 | exact W1].
    + unfold dneed, pstream; cbn [ds_eintr ds_pend ds_off Nat.b2n]; lia.
    + unfold dneed, pstream; cbn [ds_eintr ds_pend ds_off Nat.b2n]; lia.
  - destruct (ds_pend s) as [|r0 rs] eqn:PE; [reflexivity|].
    specialize (W1 r0 rs eq_refl).
    match goal with |- context [Z.leb ?nn 0] => set (n := nn) end.
    destruct (Z.leb_spec n 0) as [Hn|Hn]; [reflexivity|].
    destruct (chunk _ _ _) as [[u' sk'] rl].
    destruct (snd (fst (lines_run _ _ _ _ _ _ rl _ _ _ _))) as [[oc' H'] ka'].
    destruct (snd (lines_run _ _ _ _ _ _ rl _ _ _ _)) as [[o' ha'] ks'].
    assert (LE : ds_off s + n <= Z.of_nat (length r0)) by (subst n; lia).
    pose proof (prest_data r0 rs (ds_off s) n W0 Hn LE) as PL.
    match goal with |- context [drain_run f1 ?l ?m ?s2 ?j2 ?a2] => rewrite (IH f2 l m s2 j2 a2) end;
      [reflexivity | | |].
    + unfold dwf. cbn [ds_off ds_pend].
      destruct (Z.eqb_spec (ds_off s + n) (Z.of_nat (length r0))) as [E|E].
      * split; [lia|]. intros r rs' Er. subst rs. lia.
      * split; [lia|]. intros r rs' Er. injection Er as <- <-. lia.
    + unfold dneed, pstream; cbn [ds_eintr ds_pend ds_off Nat.b2n]. lia.
    + unfold dneed, pstream; cbn [ds_eintr ds_pend ds_off Nat.b2n]. lia.
Qed.

(* The state drain_run leaves does not depend on the base or the addresses. *)
Lemma drun_state : forall f live mx s j a j' a',
  fst (snd (drain_run f live mx s j a)) = fst (snd (drain_run f live mx s j' a')).
Proof.
  induction f as [|f IH]; intros live mx s j a j' a'; [reflexivity|].
  cbn [drain_run]. rewrite !gcap_eq.
  destruct (ds_eintr s); cbn [fst snd]; [apply IH|].
  destruct (ds_pend s) as [|r0 rs]; cbn [fst snd]; [reflexivity|].
  destruct (_ <=? 0); cbn [fst snd]; [reflexivity|].
  destruct (chunk _ _ _) as [[u' sk'] rl]. cbn [fst snd].
  rewrite !lines_run_m, !pushes_run_m.
  destruct (lrun _ _ _ _ _ _ rl) as [[oc' H'] ka']. cbn [fst snd].
  destruct (snd (lines_run _ _ _ _ _ _ rl _ _ _ _)) as [[o1 ha1] ks1].
  destruct (snd (lines_run _ _ _ _ _ _ rl _ _ _ _)) as [[o2 ha2] ks2].
  cbn [fst snd]. apply IH.
Qed.

(* A state with at least 4096 free bytes does not grow. *)
Lemma dgrow_id : forall s, 4096 <= ds_cap s - ulen s -> dgrow s = s.
Proof. intros s H. unfold dgrow, gcap, ulen in *. rewrite grow_none by exact H. destruct s; reflexivity. Qed.

(* The round's growth comes first; the rest of the round runs on the grown state. *)
Lemma drun_grow : forall f live mx s j a, 4096 <= ds_cap (dgrow s) - ulen (dgrow s) ->
  drain_run (S f) live mx s j a =
  (fst (grow_tr (ds_cap s) (ulen s) j (da_buf a)) ++
     fst (drain_run (S f) live mx (dgrow s) (j + nretF (fst (grow_tr (ds_cap s) (ulen s) j (da_buf a)))) (agrow s j a)),
   snd (drain_run (S f) live mx (dgrow s) (j + nretF (fst (grow_tr (ds_cap s) (ulen s) j (da_buf a)))) (agrow s j a))).
Proof.
  intros f live mx s j a H. unfold dgrow, agrow, ulen in *. cbn [ds_cap ds_u] in H.
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap
       da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  rewrite (grow_none (gcap (ds_cap s) (Z.of_nat (length (ds_u s)))) _ _ _ H). cbn [fst snd app].
  rewrite nret_nil, Nat.add_0_r, gcap_eq.
  destruct (ds_eintr s); [reflexivity|].
  destruct (ds_pend s) as [|r0 rs]; cbn [fst snd app]; [rewrite app_nil_r; reflexivity|].
  destruct (_ <=? 0); cbn [fst snd app]; [rewrite app_nil_r; reflexivity|].
  destruct (chunk _ _ _) as [[u' sk'] rl]. cbn [fst snd].
  destruct (snd (fst (lines_run _ _ _ _ _ _ rl _ _ _ _))) as [[oc' H'] ka']. cbn [fst snd].
  destruct (snd (lines_run _ _ _ _ _ _ rl _ _ _ _)) as [[o' ha'] ks']. cbn [fst snd].
  reflexivity.
Qed.

(* An EINTR round of a grown state: nothing requested, the flag cleared. *)
Lemma drun_eintr : forall f live mx s j a, 4096 <= ds_cap s - ulen s -> ds_eintr s = true ->
  drain_run (S f) live mx s j a = drain_run f live mx (dclr s) j a.
Proof.
  intros f live mx s j [ao ab ah ak ap av ar] H E. unfold ulen in H.
  cbn [drain_run da_out da_buf da_hp da_keys da_pend da_ev da_erecs]. rewrite E, (grow_none _ _ _ _ H).
  cbn [fst snd app]. rewrite nret_nil, Nat.add_0_r. unfold dclr. rewrite <- surjective_pairing. reflexivity.
Qed.

(* The last round of a grown state: no pending text, nothing requested, the state and the addresses final. *)
Lemma drun_end : forall f live mx s j a, 4096 <= ds_cap s - ulen s -> ds_eintr s = false -> ds_pend s = [] ->
  drain_run (S f) live mx s j a = ([], (s, a)).
Proof.
  intros f live mx [cap u sk hh ka ei pend off rf en ec no oc] j [ao ab ah ak ap av ar] Hg E P.
  cbn [ds_eintr ds_pend] in E, P. subst ei pend. unfold ulen in Hg. cbn [ds_cap ds_u] in Hg.
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap
       da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  rewrite (grow_none _ _ _ _ Hg). reflexivity.
Qed.

(* A data round of a grown state hands over n > 0 bytes. *)
Lemma dnum_pos : forall s, dstrict s -> 4096 <= ds_cap s - ulen s -> ds_pend s <> [] -> 0 < dnum s.
Proof.
  intros s W1 H P. unfold dnum, dhead. destruct (ds_pend s) as [|r0 rs] eqn:E; [congruence|].
  specialize (W1 r0 rs E). lia.
Qed.

Lemma drun_data : forall f live mx s j a, 4096 <= ds_cap s - ulen s -> ds_eintr s = false -> ds_pend s <> [] ->
  dstrict s ->
  drain_run (S f) live mx s j a =
  (fst (fst (dpush s j a)) ++ ddrop s a ++ fst (fst (dlines live mx s j a)) ++
     fst (drain_run f live mx (dnext live mx s)
            (j + nretF (fst (fst (dpush s j a))) + nretF (ddrop s a) + nretF (fst (fst (dlines live mx s j a))))
            (dnext_a live mx s j a)),
   snd (drain_run f live mx (dnext live mx s)
          (j + nretF (fst (fst (dpush s j a))) + nretF (ddrop s a) + nretF (fst (fst (dlines live mx s j a))))
          (dnext_a live mx s j a))).
Proof.
  intros f live mx s j a Hg E P W. pose proof (dnum_pos s W Hg P) as NP.
  rewrite <- (dnext_j_eq live mx s j a).
  unfold ulen in Hg. cbn [drain_run]. rewrite E, (grow_none _ _ _ _ Hg). cbn [fst snd app].
  rewrite nret_nil, Nat.add_0_r.
  unfold dnext_j, dnext_a, dlines, dpush, ddrop, drl, dref, dchunk, dwhole, ddata, dnum, dhead, dtail, ulen in *.
  destruct (ds_pend s) as [|r0 rs]; [congruence|]. cbv beta iota in *.
  rewrite (proj2 (Z.leb_gt _ _) NP).
  destruct (chunk _ _ _) as [[u' sk'] rl]. cbn [fst snd].
  destruct a as [ao ab ah ak ap av ar]. cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  destruct (pushes_run _ _ _ _ _ _) as [[tp cp] [v rs']]. cbn [fst snd].
  destruct (lines_run _ _ _ _ _ _ rl _ _ _ _) as [[tl [[oc' H'] ka']] [[o' ha'] ks']]. cbn [fst snd].
  reflexivity.
Qed.

Lemma dneed_dclr : forall s, ds_eintr s = true -> dneed s = S (dneed (dclr s)).
Proof. intros s E. unfold dneed, dclr, pstream. cbn [ds_eintr ds_pend ds_off]. rewrite E. cbn [Nat.b2n]. lia. Qed.

Lemma dneed_dnext : forall live mx s, 4096 <= ds_cap s - ulen s -> ds_pend s <> [] -> dwf s -> dstrict s ->
  ds_eintr s = false -> (S (dneed (dnext live mx s)) <= dneed s)%nat /\ dwf (dnext live mx s).
Proof.
  intros live mx s H P W ST E. pose proof (dnum_pos s ST H P) as NP. pose proof W as (W0 & W1).
  unfold dneed, pstream, dnext, dwhole, dtail, dhead in *. cbn [ds_eintr ds_pend ds_off]. rewrite E. cbn [Nat.b2n].
  destruct (ds_pend s) as [|r0 rs] eqn:PE; [congruence|]. cbv beta iota in *.
  specialize (W1 r0 rs eq_refl). specialize (ST r0 rs PE).
  assert (LE : ds_off s + dnum s <= Z.of_nat (length r0)) by (unfold dnum, dhead; rewrite PE; lia).
  pose proof (prest_data r0 rs (ds_off s) (dnum s) W0 NP LE) as PL.
  split; [lia|].
  unfold dwf. cbn [ds_off ds_pend].
  destruct (Z.eqb_spec (ds_off s + dnum s) (Z.of_nat (length r0))) as [E2|E2].
  - split; [lia|]. intros r rs' Er. subst rs. lia.
  - split; [lia|]. intros r rs' Er. injection Er as <- <-. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The machine side. *)
