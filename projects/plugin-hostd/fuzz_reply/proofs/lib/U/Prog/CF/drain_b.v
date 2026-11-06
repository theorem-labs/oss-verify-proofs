(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 12453 of its 12546 lines of code are new or changed and 1136 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO10 YK14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import drain_b_seg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memchr_c memmove_c memcpy_c strrchr_c strcmp_c strncmp_c strlen_c __errno_location_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import strndup_c strndup_rt list_push_c list_drop_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require gestures_end_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dr_cut : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[W Bs] (H0 & H1 & H)] ->.
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in Bs. apply bytes_at_app in Bs. destruct Bs as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma dr_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma dr_c8_cb : forall m A v, rw_cells rsegs m A [C8 v] -> rw_cells rsegs m A [CB 8 (le8 v)].
Proof.
  intros m A v [[_ Bs] W]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_le8|exact I].
  - exact Bs.
  - exact W.
Qed.

Definition prest (pend : list (list Z)) (off : Z) : list Z :=
  match pend with [] => [] | r :: rs => skipn (Z.to_nat off) r ++ concat rs end.

Definition pstream (s : dstate) : list Z := prest (ds_pend s) (ds_off s).

Definition dneed (s : dstate) : nat := S (length (pstream s) + Nat.b2n (ds_eintr s)).

Definition dwf (s : dstate) : Prop :=
  0 <= ds_off s /\ forall r rs, ds_pend s = r :: rs -> ds_off s <= Z.of_nat (length r).

Definition dstrict (s : dstate) : Prop := forall r rs, ds_pend s = r :: rs -> ds_off s < Z.of_nat (length r).

Definition ulen (s : dstate) : Z := Z.of_nat (length (ds_u s)).

Definition gcap (cap used : Z) : Z := fst (snd (grow_tr cap used 0 adr0)).

Definition dgrow (s : dstate) : dstate :=
  DS (gcap (ds_cap s) (ulen s)) (ds_u s) (ds_skip s) (ds_H s) (ds_ka s) (ds_eintr s) (ds_pend s) (ds_off s)
     (ds_ref s) (ds_en s) (ds_ecap s) (ds_no s) (ds_ocap s).

Definition dclr (s : dstate) : dstate :=
  DS (ds_cap s) (ds_u s) (ds_skip s) (ds_H s) (ds_ka s) false (ds_pend s) (ds_off s)
     (ds_ref s) (ds_en s) (ds_ecap s) (ds_no s) (ds_ocap s).

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

Lemma nret_nil : nretF [] = 0%nat.
Proof. reflexivity. Qed.

Definition seen_ka (H : list (list Z)) (ka : Z) (l : list Z) : Z := snd (fst (seen_tr H ka l 0 adr0 [])).

Lemma seen_tr_m : forall H ka l j ha ks, snd (fst (seen_tr H ka l j ha ks)) = seen_ka H ka l.
Proof.
  intros H ka l j ha ks. unfold seen_ka, seen_tr.
  destruct (gesture l) as [[k x]|]; [|reflexivity].
  destruct k; cbv iota; destruct (index_of x H); reflexivity.
Qed.

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

Definition pcapm (n cap : Z) (ls : list (list Z)) : Z := snd (fst (pushes_run n cap ls 0 adr0 [])).

Lemma pushes_run_mm : forall ls n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs j' v' rs'; [reflexivity|]. cbn [pushes_run fst snd]. apply IH.
Qed.

Lemma pushes_run_m : forall n cap ls j v rs, snd (fst (pushes_run n cap ls j v rs)) = pcapm n cap ls.
Proof. intros n cap ls j v rs. unfold pcapm. apply pushes_run_mm. Qed.

Definition dnext (live : bool) (mx : Z) (s : dstate) : dstate :=
  DS (ds_cap s) (fst (fst (dchunk s))) (snd (fst (dchunk s)))
     (snd (fst (lrun live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s))))
     (snd (lrun live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s))) false
     (if dwhole s then dtail s else ds_pend s) (if dwhole s then 0 else ds_off s + dnum s) (feed (ds_ref s) (ddata s))
     (ds_en s + Z.of_nat (length (dref s))) (pcapm (ds_en s) (ds_ecap s) (dref s))
     (ds_no s + Z.of_nat (length (with_nul (drl s))))
     (fst (fst (lrun live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)))).

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

Lemma dgrow_id : forall s, 4096 <= ds_cap s - ulen s -> dgrow s = s.
Proof. intros s H. unfold dgrow, gcap, ulen in *. rewrite grow_none by exact H. destruct s; reflexivity. Qed.

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

Lemma drun_eintr : forall f live mx s j a, 4096 <= ds_cap s - ulen s -> ds_eintr s = true ->
  drain_run (S f) live mx s j a = drain_run f live mx (dclr s) j a.
Proof.
  intros f live mx s j [ao ab ah ak ap av ar] H E. unfold ulen in H.
  cbn [drain_run da_out da_buf da_hp da_keys da_pend da_ev da_erecs]. rewrite E, (grow_none _ _ _ _ H).
  cbn [fst snd app]. rewrite nret_nil, Nat.add_0_r. unfold dclr. rewrite <- surjective_pairing. reflexivity.
Qed.

Lemma drun_end : forall f live mx s j a, 4096 <= ds_cap s - ulen s -> ds_eintr s = false -> ds_pend s = [] ->
  drain_run (S f) live mx s j a = ([], (s, a)).
Proof.
  intros f live mx [cap u sk hh ka ei pend off rf en ec no oc] j [ao ab ah ak ap av ar] Hg E P.
  cbn [ds_eintr ds_pend] in E, P. subst ei pend. unfold ulen in Hg. cbn [ds_cap ds_u] in Hg.
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap
       da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  rewrite (grow_none _ _ _ _ Hg). reflexivity.
Qed.

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

Section DH.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Local Abbreviation segs := (ms_segs Bm).
Local Abbreviation MR := (aa_MR API).
Hypothesis AX : AllocExtra Bm MR.
Hypothesis CTX : ctx_owned Bm API.
Hypothesis SLACK : block_slack_present Bm API.
Hypothesis BW : blocks_writable Bm API.
Hypothesis EU : errno_unowned Bm API.
Hypothesis FREEPC : ms_free Bm = 0x15f4c.
Hypothesis NODUP : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).
Hypothesis RAC : realloc_contract_rt Bm API F 0x178f8.
Hypothesis RNC : realloc_null_contract_rt Bm API F 0x178f8.
Hypothesis MALPC : ms_malloc Bm = 0x1608c.
Hypothesis ELC : __errno_location_contract.
Hypothesis SLC : send_line_contract Bm API F.
Hypothesis LPC : list_push_contract Bm API F.
Hypothesis SDC : strndup_contract_rt Bm API F.
Hypothesis FRC : free_contract_rt Bm API F.
Hypothesis MCH : memchr_contract.
Hypothesis MMV : memmove_contract.
Hypothesis MCP : memcpy_contract.
Hypothesis SRR : strrchr_contract.
Hypothesis SCM : strcmp_contract.
Hypothesis SNC : strncmp_contract.
Hypothesis SLN : strlen_contract.
Hypothesis LDC : list_drop_contract Bm API F.

Definition key_okw (L : layout) (A : astate) (m : word -> option byte) (k : Z * list byte * list byte) : Prop :=
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
  fresh_block Bm (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
  bytes_at segs m (key_addr k) (key_text k ++ [Z_to_bv 8 0]) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= 6000.

Definition entry_okw (L : layout) (A : astate) (m : word -> option byte) (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
  0 <= re_fd e < 2 ^ 31 /\
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) = re_used e /\ re_used e <= 6000 /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  ((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
   (0 < re_cap e /\ In (re_buf e, re_cap e) (blocks L A) /\ fresh_block Bm (re_buf e) (re_cap e) /\
    Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
    rw_cells segs m (re_buf e) [CB (Z.to_nat (re_cap e)) (re_U e ++ re_junk e)])) /\
  re_nheld e < 2 ^ 26 /\
  ((re_hp e = 0 /\ re_keys e = []) \/
   (In (re_hp e, re_kh e) (blocks L A) /\ fresh_block Bm (re_hp e) (re_kh e) /\ 8 * re_nheld e <= re_kh e /\
    8 <= re_kh e /\ bytes_at segs m (re_hp e) (key_ptrs (re_keys e)))) /\
  NoDup (map key_addr (re_keys e)) /\
  NoDup (map key_text (re_keys e)) /\
  Forall (key_okw L A m) (re_keys e).

Definition msame (Pa : Z -> Prop) (m1 m2 : word -> option byte) : Prop :=
  forall a, Pa a -> mbyte segs m2 a = mbyte segs m1 a /\ (writable_at segs m1 a -> writable_at segs m2 a).

Lemma msame_munch : forall W m1 m2, munch W m1 m2 -> wmono segs m1 m2 ->
  msame (fun a => 0 <= a < 2 ^ 64 /\ outside W a) m1 m2.
Proof using.
  intros W m1 m2 MU WM a [Ha Ho]. unfold mbyte, writable_at.
  rewrite (MU (Z_to_bv 64 a)) by (rewrite unsigned_lit by lia; exact Ho).
  split; [reflexivity|]. intros Hw. exact (WM _ Hw).
Qed.

Lemma msame_mono : forall (Pa Qa : Z -> Prop) m1 m2, msame Qa m1 m2 -> (forall a, Pa a -> Qa a) -> msame Pa m1 m2.
Proof using. intros Pa Qa m1 m2 H I a Ha. exact (H a (I a Ha)). Qed.

Lemma rw_tr : forall Pa m1 m2 c cs, msame Pa m1 m2 -> rw_cells segs m1 c cs ->
  (forall a, c <= a < c + Z.of_nat (cells_size cs) -> Pa a) -> rw_cells segs m2 c cs.
Proof using.
  intros Pa m1 m2 c cs MS H HP. apply (CF.gestures_end_b.rw_cells_transfer2 segs m1 m2 c cs H).
  intros i Hi. apply MS. apply HP. lia.
Qed.

Lemma by_tr : forall Pa m1 m2 c bs, msame Pa m1 m2 -> bytes_at segs m1 c bs ->
  (forall a, c <= a < c + Z.of_nat (length bs) -> Pa a) -> bytes_at segs m2 c bs.
Proof using.
  intros Pa m1 m2 c bs MS H HP. apply (CF.gestures_end_b.bytes_at_transfer2 segs m1 m2 c bs H).
  intros i Hi. apply MS. apply HP. lia.
Qed.

Lemma entry_okw_of : forall L1 A1 m1 e1, entry_ok Bm L1 A1 m1 e1 -> entry_okw L1 A1 m1 e1.
Proof using.
  intros L1 A1 m1 e1 (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15).
  do 14 (split; [assumption|]).
  eapply Forall_impl; [|exact E15]. intros k (K1 & K2 & K3 & K4 & K5 & K6).
  split; [exact K1|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  change (key_text k ++ Z_to_bv 8 0 :: key_slack k) with (key_text k ++ [Z_to_bv 8 0] ++ key_slack k) in K3.
  rewrite app_assoc in K3. apply bytes_at_app in K3 as [K3 _]. exact K3.
Qed.

Lemma entry_okw_tr : forall L1 A1 L2 A2 m1 m2 e1 Pa, msame Pa m1 m2 -> entry_okw L1 A1 m1 e1 ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1) -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1) -> q <= a < q + k -> Pa a) ->
  entry_okw L2 A2 m2 e1.
Proof using.
  intros L1 A1 L2 A2 m1 m2 e1 Pa MS (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15) SV HP.
  assert (IB : re_cap e1 <> 0 -> In (re_buf e1) (entry_blocks e1)).
  { intros C. unfold entry_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
  assert (IH : re_hp e1 <> 0 -> In (re_hp e1) (entry_blocks e1)).
  { intros C. unfold entry_blocks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
  assert (IK : forall k, In k (re_keys e1) -> In (key_addr k) (entry_blocks e1)).
  { intros k Hk. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
  unfold entry_okw. do 9 (split; [assumption|]).
  split.
  { destruct E10 as [Z0|(C0 & BI & BF & BJ & BC)]; [left; exact Z0 | right].
    assert (CN : re_cap e1 <> 0) by (clear - C0; lia).
    split; [exact C0|]. split; [exact (SV _ _ BI (IB CN))|]. split; [exact BF|]. split; [exact BJ|].
    eapply rw_tr; [exact MS | exact BC |]. intros a Ha. apply (HP _ _ a BI (IB CN)).
    cbn [cells_size csize] in Ha. clear - Ha C0. lia. }
  split; [exact E11|].
  split.
  { destruct E12 as [Z0|(HI & HF & H8 & H8' & HB)]; [left; exact Z0 | right].
    assert (HN : re_hp e1 <> 0) by (destruct HF as (HF1 & _); clear - HF1; lia).
    split; [exact (SV _ _ HI (IH HN))|]. split; [exact HF|]. split; [exact H8|]. split; [exact H8'|].
    eapply by_tr; [exact MS | exact HB |]. intros a Ha. apply (HP _ _ a HI (IH HN)).
    rewrite CF.gestures_end_b.key_ptrs_length in Ha. unfold re_nheld in H8. clear - Ha H8. lia. }
  split; [exact E13|]. split; [exact E14|].
  apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) E15 k Hk) as (K1 & K2 & K3 & K4 & K5).
  split; [exact (SV _ _ K1 (IK k Hk))|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  eapply by_tr; [exact MS | exact K3 |]. intros a Ha. apply (HP _ _ a K1 (IK k Hk)).
  rewrite length_app in Ha. cbn [length] in Ha. clear - Ha. lia.
Qed.

Lemma list_at_tr : forall L1 A1 L2 A2 m1 m2 LA l ln Pa, msame Pa m1 m2 -> list_at Bm L1 A1 m1 LA l ln ->
  (forall a, LA <= a < LA + 16 -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (list_blocks l) -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (list_blocks l) -> q <= a < q + k -> Pa a) ->
  list_at Bm L2 A2 m2 LA l ln.
Proof using.
  intros L1 A1 L2 A2 m1 m2 LA l ln Pa MS (C1 & C2 & C3 & C4 & C5 & C6) HC SV HB.
  split; [eapply rw_tr; [exact MS | exact C1 | intros a Ha; apply HC; cbn [cells_size csize] in Ha; clear - Ha; lia]|].
  split; [exact C2|].
  split.
  { destruct C3 as [Z0|(V0 & VI & VF & VJ & VC)]; [left; exact Z0 | right].
    assert (IV : In (hl_v l) (list_blocks l)).
    { unfold list_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - V0; lia). left. reflexivity. }
    split; [exact V0|]. split; [exact (SV _ _ VI IV)|]. split; [exact VF|]. split; [exact VJ|].
    eapply rw_tr; [exact MS | exact VC |]. intros a Ha. apply (HB _ _ a VI IV).
    cbn [cells_size csize] in Ha. clear - Ha V0. lia. }
  split; [exact C4|]. split; [exact C5|].
  apply Forall_forall. intros r Hr. destruct (proj1 (Forall_forall _ _) C6 r Hr) as (R1 & R2 & R3 & R4 & R5).
  assert (IR : In (fst r) (list_blocks l)) by (unfold list_blocks; apply in_or_app; right; apply in_map; exact Hr).
  split; [exact (SV _ _ R1 IR)|]. split; [exact R2|]. split; [|split; [exact R4 | exact R5]].
  eapply rw_tr; [exact MS | exact R3 |]. intros a Ha. apply (HB _ _ a R1 IR).
  cbn [cells_size csize] in Ha. clear - Ha. lia.
Qed.

Definition hs_eset (h1 : hsrc) (v : Z) : hsrc :=
  HS (hs_fd h1) (hs_open h1) (hs_closed h1) v (hs_pending h1) (hs_off h1) (hs_partial h1) (hs_pjunk h1)
     (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1).

Lemma hs_eset_id : forall h1, hs_eset h1 (hs_eintr h1) = h1.
Proof using. intros []. reflexivity. Qed.

Lemma hb_pend : forall h1 q, In q (list_blocks (hs_pending h1)) -> In q (hs_blocks h1).
Proof using. intros h1 q H. unfold hs_blocks. apply in_or_app. left. exact H. Qed.

Lemma hb_part : forall h1, In (hs_partial h1) (hs_blocks h1).
Proof using. intros h1. unfold hs_blocks. apply in_or_app. right. left. reflexivity. Qed.

Lemma hb_exp : forall h1 q, In q (list_blocks (hs_expected h1)) -> In q (hs_blocks h1).
Proof using.
  intros h1 q H. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H.
Qed.

Lemma hb_held : forall h1 q, In q (list_blocks (hs_held h1)) -> In q (hs_blocks h1).
Proof using.
  intros h1 q H. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

Lemma src_at_tr : forall L1 A1 L2 A2 m1 m2 HA1 h1 v Pa, msame Pa m1 m2 -> src_at Bm L1 A1 m1 HA1 h1 ->
  rw_cells segs m2 HA1 [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                        C4 (Z_to_bv 64 (hs_closed h1)); C4 (Z_to_bv 64 v)] ->
  (v = 0 \/ v = 1) ->
  (forall a, HA1 + 16 <= a < HA1 + 96 -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> q <= a < q + k -> Pa a) ->
  src_at Bm L2 A2 m2 HA1 (hs_eset h1 v).
Proof using.
  intros L1 A1 L2 A2 m1 m2 HA1 h1 v Pa MS
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) C V HC SV HB.
  unfold src_at. split; [exact C|]. split; [exact S2|]. split; [exact V|]. split; [exact S4|]. split; [exact S5|].
  split.
  { eapply list_at_tr; [exact MS | exact S6 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. exact (SV q k Hq (hb_pend h1 q Hl)).
    - intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_pend h1 q Hl) Ha). }
  split; [eapply rw_tr; [exact MS | exact S7 | intros a Ha; apply HC; cbn [cells_size csize] in Ha; clear - Ha; lia]|].
  split; [exact S8|]. split; [exact S9|]. split; [exact S10|].
  split; [exact (SV _ _ S11 (hb_part h1))|]. split; [exact S12|]. split; [exact S13|].
  split.
  { eapply rw_tr; [exact MS | exact S14 |]. intros a Ha. apply (HB _ _ a S11 (hb_part h1)).
    cbn [cells_size csize hs_partial hs_eset] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. clear - Ha. lia. }
  split; [exact S15|].
  split.
  { eapply list_at_tr; [exact MS | exact S16 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. exact (SV q k Hq (hb_exp h1 q Hl)).
    - intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_exp h1 q Hl) Ha). }
  split.
  { eapply list_at_tr; [exact MS | exact S17 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. exact (SV q k Hq (hb_held h1 q Hl)).
    - intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_held h1 q Hl) Ha). }
  exact S18.
Qed.

Lemma src_at_tr0 : forall L1 A1 L2 A2 m1 m2 HA1 h1 Pa, msame Pa m1 m2 -> src_at Bm L1 A1 m1 HA1 h1 ->
  (forall a, HA1 <= a < HA1 + 96 -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> q <= a < q + k -> Pa a) ->
  src_at Bm L2 A2 m2 HA1 h1.
Proof using.
  intros L1 A1 L2 A2 m1 m2 HA1 h1 Pa MS SR0 HC SV HB. rewrite <- (hs_eset_id h1).
  pose proof SR0 as (S1 & S2 & S3 & _).
  apply (src_at_tr L1 A1 L2 A2 m1 m2 HA1 h1 (hs_eintr h1) Pa MS SR0);
    [| exact S3 | intros a Ha; apply HC; clear - Ha; lia | exact SV | exact HB].
  eapply rw_tr; [exact MS | exact S1 |]. intros a Ha. apply HC. cbn [cells_size csize] in Ha. clear - Ha. lia.
Qed.

Lemma others_at_tr : forall m1 m2 j1 fd fs1 os1 Pa, msame Pa m1 m2 -> others_at Bm m1 j1 fd fs1 os1 ->
  (forall i a, (i < 4)%nat -> i <> j1 -> G_S + SRC_SIZE * Z.of_nat i <= a < G_S + SRC_SIZE * Z.of_nat i + 8 -> Pa a) ->
  others_at Bm m2 j1 fd fs1 os1.
Proof using.
  intros m1 m2 j1 fd fs1 os1 Pa MS (O1 & O2 & O3) HP. split; [exact O1|]. split; [exact O2|].
  intros i Hi Hij. destruct (O3 i Hi Hij) as (C & D & E). split; [|split; [exact D | exact E]].
  eapply rw_tr; [exact MS | exact C |]. intros a Ha. apply (HP i a Hi Hij). cbn [cells_size csize] in Ha. lia.
Qed.

Lemma blk_rng : forall L1 A1 m1 md1 q k, MR L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) ->
  4096 <= q /\ q + k <= YM05.alloc_ceiling.
Proof using.
  intros L1 A1 m1 md1 q k HM H. apply CF.gestures_end_b.blocks_In2 in H as (p & <- & Hp).
  exact (mr_blocks_range Bm MR (aa_laws API) L1 A1 m1 md1 p k HM Hp).
Qed.

Lemma blk_align : forall L1 A1 m1 md1 q k, MR L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) -> q mod 16 = 0.
Proof using.
  intros L1 A1 m1 md1 q k HM H. apply CF.gestures_end_b.blocks_In2 in H as (p & <- & Hp).
  exact (mr_blocks_aligned Bm MR (aa_laws API) L1 A1 m1 md1 p k HM Hp).
Qed.

Lemma blk_noimg : forall L1 A1 m1 md1 q k i, MR L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) -> 0 <= i < k ->
  ~ in_img Bm (q + i).
Proof using AX.
  intros L1 A1 m1 md1 q k i HM H Hi. apply CF.gestures_end_b.blocks_In2 in H as (p & <- & Hp).
  exact (ax_blocks_img AX L1 A1 m1 md1 p k i HM Hp Hi).
Qed.

Lemma bzs_inj : forall a b, bzs a = bzs b -> a = b.
Proof using.
  induction a as [|x a IH]; intros [|y b] E; cbn in E; try discriminate; [reflexivity|].
  injection E as Exy Eab. f_equal; [apply bv_eq; exact Exy | apply IH; exact Eab].
Qed.

Lemma nodup_kt : forall ks, NoDup (map key_text ks) -> NoDup (keys_texts ks).
Proof using.
  intros ks H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  unfold keys_texts. replace (map (fun k => bzs (key_text k)) ks) with (map bzs (map key_text ks))
    by (rewrite map_map; reflexivity).
  induction H as [|x l Hx Hl IH]; cbn [map]; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Ey & Hy). apply bzs_inj in Ey. subst. exact (Hx Hy).
Qed.

Lemma nozero_of : forall U, ~ In (Z_to_bv 8 0) U -> nozero (bzs U).
Proof using.
  intros U H. unfold nozero, bzs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (x & <- & Hx).
  intros E. apply H. replace (Z_to_bv 8 0) with x; [exact Hx|]. apply bv_eq. unfold bz in E. rewrite E. reflexivity.
Qed.

Lemma skipn_bzs : forall n l, skipn n (bzs l) = bzs (skipn n l).
Proof using. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma pstream_init : forall NO1 CAP1 e1 h1, pstream (drain_init NO1 CAP1 e1 h1) = bzs (pending_stream h1).
Proof using.
  intros NO1 CAP1 e1 h1. unfold pstream, prest, pending_stream, drain_init. cbn [ds_pend ds_off].
  destruct (hl_recs (hs_pending h1)) as [|r rs]; cbn [map]; [reflexivity|].
  unfold bzs at 3. rewrite map_app. f_equal; [apply skipn_bzs|].
  induction rs as [|r1 rs IH]; cbn [map concat]; [reflexivity|]. rewrite map_app, IH. reflexivity.
Qed.

Lemma msame_trans : forall (Pa Qa : Z -> Prop) m1 m2 m3, msame Pa m1 m2 -> msame Qa m2 m3 ->
  msame (fun a => Pa a /\ Qa a) m1 m3.
Proof using.
  intros Pa Qa m1 m2 m3 H1 H2 a [HP HQ]. destruct (H1 a HP) as [E1 W1]. destruct (H2 a HQ) as [E2 W2].
  split; [congruence | intros W; apply W2, W1, W].
Qed.

Lemma rp_msame : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2,
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  msame (fun a => ((YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) /\ ~ owned Bm L1 A1 a /\ ~ owned Bm L2 A2 a /\
                   ~ scratch_k Bm K R1 a /\ ~ E a) \/
                  (exists q k, In (q, k) (blocks L1 A1) /\ 0 < k /\ ~ F0 q /\ q <= a < q + k /\ ~ E a)) m1 m2.
Proof using BW.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2
    (M2 & W2 & B2 & LL & LN & AD & SV & Z0 & OW & RP & MD & FR & BY & SC) a
    [(Ha & N1 & N2 & NS & NE)|(q & k & Hq & Hk & NF & Hqa & NE)].
  - destruct (FR a Ha N1 N2 NS NE) as [E1 W1]. split; [exact E1 | intros W; apply W1; exact W].
  - apply CF.gestures_end_b.blocks_In2 in Hq as (p & Ep & Hp). subst q.
    pose proof (SV p k Hp Hk NF) as Hp2.
    pose proof (AD p k Hp Hp2 NF) as EA.
    replace a with (ptr_addr L1 p + (a - ptr_addr L1 p)) by lia.
    split.
    + apply (BY p k (a - ptr_addr L1 p) Hp Hp2 NF); [lia|].
      replace (ptr_addr L1 p + (a - ptr_addr L1 p)) with a by lia. exact NE.
    + intros _. rewrite <- EA.
      apply (BW L2 A2 m2 md2 (ptr_addr L2 p) k (a - ptr_addr L2 p) M2); [|lia].
      unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hp2].
Qed.

Lemma rp_mono : forall K (E E' F0 F' : Z -> Prop) L1 A1 R1 m1 md1 L2 A2 R2 m2 md2,
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> (forall a, E a -> E' a) -> (forall q, F0 q -> F' q) ->
  relay_post Bm API K E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2.
Proof using.
  intros K E E' F0 F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 Pr HE HF.
  destruct Pr as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FR1 & BY1 & SC1).
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact LL1|]. split; [exact LN1|].
  split; [intros p n H1 H2 NF; apply (AD1 p n H1 H2); intros X; apply NF, HF, X|].
  split; [intros p n H1 Hn NF; apply (SV1 p n H1 Hn); intros X; apply NF, HF, X|].
  split; [exact Z1|]. split; [exact OW1|]. split; [exact RP1|]. split; [exact MD1|].
  split; [intros a Ha N1 N2 NS NE; apply FR1; [exact Ha | exact N1 | exact N2 | exact NS | intros X; apply NE, HE, X]|].
  split; [intros p n i H1 H2 NF Hi NE; apply (BY1 p n i H1 H2);
          [intros X; apply NF, HF, X | exact Hi | intros X; apply NE, HE, X]|].
  exact SC1.
Qed.

Lemma img_unowned : forall L1 A1 m1 md1 a, MR L1 A1 m1 md1 -> img_plain Bm a -> ~ owned Bm L1 A1 a.
Proof using AX.
  intros L1 A1 m1 md1 a HM (Hi & Hs & Hc & He) [Ho|Ho];
    [exact (Hc (ax_img AX L1 A1 m1 md1 a HM Hi Ho)) | exact (Hs Ho)].
Qed.

Lemma owned_lo2 : forall L1 A1 m1 md1 a, MR L1 A1 m1 md1 -> owned Bm L1 A1 a -> 0 <= a < YM05.alloc_ceiling.
Proof using. intros L1 A1 m1 md1 a HM Ho. exact (mr_owned_low Bm MR (aa_laws API) L1 A1 m1 md1 a HM Ho). Qed.

Lemma ent_cells : forall m SA1 e1, rw_cells rsegs m SA1 [CB 56 (entry_bytes e1)] ->
  length (re_pad1 e1) = 4%nat -> length (re_pad2 e1) = 4%nat ->
  rw_cells rsegs m SA1 [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1)); C4 (Z_to_bv 64 (re_skip e1));
                        CB 4 (re_pad1 e1)] /\
  rw_cells rsegs m (SA1 + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1)); C8 (Z_to_bv 64 (re_cap e1))] /\
  rw_cells rsegs m (SA1 + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1)); CB 4 (re_pad2 e1)].
Proof using.
  intros m SA1 e1 [[W B] Wr] P1 P2.
  assert (H : rw_cells rsegs m SA1
    ([C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1)); C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)] ++
     [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1)); C8 (Z_to_bv 64 (re_cap e1))] ++
     [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1)); CB 4 (re_pad2 e1)])).
  { split; [split|].
    - cbn [app cells_wf cell_wf]. repeat split; assumption.
    - cbn [app cells_bytes cbytes]. rewrite app_nil_r. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      exact B.
    - exact Wr. }
  destruct (dr_cut m SA1 (SA1 + 16) _ _ H eq_refl) as [H1 H23].
  destruct (dr_cut m (SA1 + 16) (SA1 + 40) _ _ H23 ltac:(cbn [cells_size csize]; lia)) as [H2 H3].
  exact (conj H1 (conj H2 H3)).
Qed.

Lemma ent_join : forall m SA1 e1, length (re_pad1 e1) = 4%nat -> length (re_pad2 e1) = 4%nat ->
  rw_cells rsegs m SA1 [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1)); C4 (Z_to_bv 64 (re_skip e1));
                        CB 4 (re_pad1 e1)] ->
  rw_cells rsegs m (SA1 + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1)); C8 (Z_to_bv 64 (re_cap e1))] ->
  rw_cells rsegs m (SA1 + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1)); CB 4 (re_pad2 e1)] ->
  rw_cells rsegs m SA1 [CB 56 (entry_bytes e1)].
Proof using.
  intros m SA1 e1 P1 P2 H1 H2 H3.
  pose proof (dr_join m (SA1 + 16) (SA1 + 40) _ _ H2 H3 ltac:(cbn [cells_size csize]; lia)) as H23.
  pose proof (dr_join m SA1 (SA1 + 16) _ _ H1 H23 eq_refl) as [[W B] Wr].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. unfold entry_bytes.
    rewrite !length_app, !length_le4, !length_le8, P1, P2. reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. cbn [app cells_bytes cbytes] in B. rewrite app_nil_r in B.
    exact B.
  - exact Wr.
Qed.

Lemma entry_okw_buf : forall L1 A1 L2 A2 m1 m2 e1 Pa res n junk2,
  msame Pa m1 m2 -> entry_okw L1 A1 m1 e1 ->
  (forall q k, In (q, k) (blocks L1 A1) -> (q = re_hp e1 \/ In q (map key_addr (re_keys e1))) ->
     In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> (q = re_hp e1 \/ In q (map key_addr (re_keys e1))) -> q <= a < q + k ->
     Pa a) ->
  (n = 8192 \/ n = 16384) -> re_used e1 <= n -> In (res, n) (blocks L2 A2) -> fresh_block Bm res n ->
  Z.of_nat (length junk2) = n - re_used e1 -> rw_cells segs m2 res [CB (Z.to_nat n) (re_U e1 ++ junk2)] ->
  entry_okw L2 A2 m2 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) res (re_used e1) n (re_hp e1) (re_kh e1)
                        (re_pad2 e1) (re_keys e1) (re_U e1) junk2).
Proof using.
  intros L1 A1 L2 A2 m1 m2 e1 Pa res n junk2 MS
    (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15) SV HP Hn Hu RI RF RJ RC.
  unfold entry_okw, re_nheld.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys].
  unfold re_nheld in E11, E12.
  do 5 (split; [assumption|]).
  split; [clear - Hn; lia|].
  do 3 (split; [assumption|]).
  split; [right; split; [clear - Hn; lia|]; split; [exact RI|]; split; [exact RF|]; split; [exact RJ | exact RC]|].
  split; [exact E11|].
  split.
  { destruct E12 as [Z0|(HI & HF & H8 & H8' & HB)]; [left; exact Z0 | right].
    split; [apply SV; [exact HI | left; reflexivity]|]. split; [exact HF|]. split; [exact H8|]. split; [exact H8'|].
    eapply by_tr; [exact MS | exact HB |]. intros a Ha. apply (HP _ _ a HI); [left; reflexivity|].
    rewrite CF.gestures_end_b.key_ptrs_length in Ha. clear - Ha H8. lia. }
  split; [exact E13|]. split; [exact E14|].
  apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) E15 k Hk) as (K1 & K2 & K3 & K4 & K5).
  split; [apply SV; [exact K1 | right; apply in_map; exact Hk]|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  eapply by_tr; [exact MS | exact K3 |]. intros a Ha. apply (HP _ _ a K1); [right; apply in_map; exact Hk|].
  rewrite length_app in Ha. cbn [length] in Ha. clear - Ha. lia.
Qed.

Lemma eb_live : forall L1 A1 m1 e1 q, entry_okw L1 A1 m1 e1 -> In q (entry_blocks e1) ->
  exists k, In (q, k) (blocks L1 A1).
Proof using.
  intros L1 A1 m1 e1 q (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & _ & E12 & _ & _ & E15) Hq.
  unfold entry_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [|apply in_app_or in Hq as [Hq|Hq]].
  - revert Hq. destruct (Z.eqb_spec (re_cap e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E10 as [(C0 & _)|(_ & BI & _)]; [lia | exists (re_cap e1); exact BI].
  - revert Hq. destruct (Z.eqb_spec (re_hp e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E12 as [(H0 & _)|(HI & _)]; [lia | exists (re_kh e1); exact HI].
  - apply in_map_iff in Hq as (k & <- & Hk). destruct (proj1 (Forall_forall _ _) E15 k Hk) as (K1 & _).
    eexists; exact K1.
Qed.

Lemma lb_live : forall L1 A1 m1 LA l ln q, list_at Bm L1 A1 m1 LA l ln -> In q (list_blocks l) ->
  exists k, In (q, k) (blocks L1 A1).
Proof using.
  intros L1 A1 m1 LA l ln q (_ & _ & C3 & _ & _ & C6) Hq.
  unfold list_blocks in Hq. apply in_app_or in Hq as [Hq|Hq].
  - revert Hq. destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct C3 as [(C0 & _)|(_ & VI & _)]; [lia | eexists; exact VI].
  - apply in_map_iff in Hq as (r & <- & Hr). destruct (proj1 (Forall_forall _ _) C6 r Hr) as (R1 & _).
    eexists; exact R1.
Qed.

Lemma hb_live : forall L1 A1 m1 HA1 h1 q, src_at Bm L1 A1 m1 HA1 h1 -> In q (hs_blocks h1) ->
  exists k, In (q, k) (blocks L1 A1).
Proof using.
  intros L1 A1 m1 HA1 h1 q (_ & _ & _ & _ & _ & S6 & _ & _ & _ & _ & S11 & _ & _ & _ & _ & S16 & S17 & _) Hq.
  unfold hs_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [exact (lb_live _ _ _ _ _ _ _ S6 Hq)|].
  apply in_app_or in Hq as [Hq|Hq]; [destruct Hq as [<-|[]]; eexists; exact S11|].
  apply in_app_or in Hq as [Hq|Hq]; [exact (lb_live _ _ _ _ _ _ _ S16 Hq) | exact (lb_live _ _ _ _ _ _ _ S17 Hq)].
Qed.

Lemma nodup_mid_drop : forall (pre x post : list Z), List.NoDup (pre ++ x ++ post) -> List.NoDup (pre ++ post).
Proof using.
  induction pre as [|y pre IH]; intros x post H; cbn in *.
  - induction x as [|z x IHx]; cbn in H; [exact H|]. apply IHx. inversion H; assumption.
  - inversion H as [|? ? Hy Hn]; subst. constructor; [|exact (IH x post Hn)].
    intros Hin. apply Hy. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
      [left; exact Hin | right; apply in_or_app; right; exact Hin].
Qed.

Lemma nodup_mid_add : forall (pre post : list Z) r, List.NoDup (pre ++ post) -> ~ In r (pre ++ post) ->
  List.NoDup (pre ++ r :: post).
Proof using.
  induction pre as [|y pre IH]; intros post r H Hr; cbn in *.
  - constructor; assumption.
  - inversion H as [|? ? Hy Hn]; subst. constructor.
    + intros Hin. apply in_app_or in Hin as [Hin|[Hin|Hin]];
        [apply Hy; apply in_or_app; left; exact Hin | apply Hr; left; symmetry; exact Hin |
         apply Hy; apply in_or_app; right; exact Hin].
    + apply IH; [exact Hn | intros Hin; apply Hr; right; exact Hin].
Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (bnd : rt_R F)
  (e : rentry) (h : hsrc) (j : nat) (fs os : list Z) (G : Z) (O junk : list byte) (cl br dd ei : Z)
  (mx nout cap out : word).
Local Abbreviation S0 := (bv_unsigned (getr regs 2)).
Local Abbreviation SA := (bv_unsigned (getr regs 10)).
Local Abbreviation HA := (G_S + SRC_SIZE * Z.of_nat j).
Local Abbreviation XH := (DR_TU + 96 * Z.of_nat j).
Local Abbreviation PS := (pending_stream h).
Local Abbreviation ST0 := (hs_state h).
Local Abbreviation LS0 := (lines (hs_state h) (bzs (pending_stream h))).
Local Abbreviation TOT := (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h)))))).
Local Abbreviation PL := (Z.of_nat (length (pending_stream h))).
Local Abbreviation ERR := (errno_addr Bm).
Local Abbreviation NO := (bv_unsigned nout).
Local Abbreviation CAP := (bv_unsigned cap).
Local Abbreviation OUT := (bv_unsigned out).
Local Abbreviation LIVE := (send_live cl br dd (Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))))).
Local Abbreviation MX := (bv_unsigned mx).
Local Abbreviation AD0 := (drain_start (known_at L A) (known_at L A (bv_unsigned out)) e h).
Local Abbreviation TR := (drain_tr LIVE MX NO CAP e h 0 AD0).
Local Abbreviation FIN := (drain_fin LIVE MX NO CAP e h).
Local Abbreviation FAD := (drain_adr LIVE MX NO CAP e h 0 AD0).
Local Abbreviation EE := (fun a => send_writes LIVE OUT CAP a \/ SA <= a < SA + SRC_ENTRY \/ HA + 12 <= a < HA + SRC_SIZE \/
  (exists q m, In q (entry_blocks e ++ hs_blocks h) /\ In (q, m) (blocks L A) /\ q <= a < q + m)).
Local Abbreviation FF := (fun q => (LIVE = true /\ q = OUT) \/ In q (entry_blocks e ++ hs_blocks h)).
Local Abbreviation drun := (drain_run).
Local Abbreviation SAVED := (dr_saved (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
  (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
  (getr regs 27)).

Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis PRE : call_pre_k Bm MR DRAIN_K L A regs mem md.
Hypothesis INIT : st_init_done A = true.
Hypothesis TPE : ms_tp Bm + ERRNO_OFF = ERR.
Hypothesis ERR4 : ERR mod 4 = 0.

Hypothesis EHI : G_LOCK_HI <= ERR.
Hypothesis RO0 : ro_agree segs mem.
Hypothesis GRP : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a.
Hypothesis GCP : forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a.
Hypothesis GEI : forall a, ERR <= a < ERR + 4 -> in_img Bm a.
Hypothesis HJ : (j < 4)%nat.
Hypothesis HG : In (G, SRC_TABLE) (blocks L A) /\ fresh_block Bm G SRC_TABLE /\ G <= SA /\ SA + SRC_ENTRY <= G + SRC_TABLE /\
  (SA - G) mod SRC_ENTRY = 0.
Hypothesis HE0 : rw_cells segs mem SA [CB 56%nat (entry_bytes e)].
Hypothesis EOK : entry_ok Bm L A mem e.
Hypothesis SRC0 : src_at Bm L A mem HA h.
Hypothesis OTH : others_at Bm mem j (re_fd e) fs os.
Hypothesis HFD : hs_fd h = re_fd e.
Hypothesis HSK : re_skip e = hs_overlong h.
Hypothesis HSW : re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h).
Hypothesis HND : NoDup (G :: OUT :: entry_blocks e ++ hs_blocks h).
Hypothesis HPL : PL < 2 ^ 26.
Hypothesis HEC : hl_cap (hs_expected h) < 2 ^ 26.
Hypothesis HNH : re_nheld e + PL < 2 ^ 26.
Hypothesis Hcl : cl = 3 \/ cl = -1.
Hypothesis Hbr : br = 0 \/ br = 1.
Hypothesis Hdd : dd = 0 \/ dd = 1.
Hypothesis Hei : ei = 0 \/ ei = 1.
Hypothesis CCL : rw_cells segs mem G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis CBR : rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis CDD : rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis CEI : rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis COUT : rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis CERR : exists ev, rw_cells segs mem ERR [C4 ev].
Hypothesis OUTD : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
  (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
   bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO).
Hypothesis RES0 : rt_ok F A bnd.
Hypothesis ROOM : forall qs, length qs = nretF TR -> roomF F qs bnd TR.

Definition DPOST (c' : config) : Prop :=
  exists L' A' regs' mem' md' (e' : rentry) (h' : hsrc) (OUT' CAP' : Z) (junk' LB : list byte),
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    relay_post Bm API DRAIN_K EE FF L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF TR /\ rt_ok F A' (runF F qs bnd TR) /\
       (LIVE = true -> live_at L' A' (resolveF qs (da_out FAD)) OUT' CAP') /\
       entry_links L' A' qs FAD e' /\ src_links L' A' qs (known_at L A) FAD h') /\
    ro_agree segs mem' /\
    rw_cells segs mem' SA [CB 56%nat (entry_bytes e')] /\
    entry_ok Bm L' A' mem' e' /\
    src_at Bm L' A' mem' HA h' /\
    others_at Bm mem' j (re_fd e) fs os /\
    re_fd e' = re_fd e /\
    re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\
    0 < re_cap e' /\
    re_cap e' = ds_cap FIN /\ bzs (re_U e') = ds_u FIN /\ re_skip e' = (if ds_skip FIN then 1 else 0) /\
    keys_texts (re_keys e') = ds_H FIN /\ ent_ka e' = ds_ka FIN /\ hl_cap (hs_expected h') = ds_ecap FIN /\
    ((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
    hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
    hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
    hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
    hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
    hs_partial h' = hs_partial h /\
    hs_state h' = feed ST0 (bzs PS) /\
    map snd (hl_recs (hs_expected h')) =
      map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) LS0 /\
    firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
    hs_held h' = hs_held h /\
    re_skip e' = hs_overlong h' /\
    (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
    NoDup (keys_texts (re_keys e')) /\
    same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys e)) LS0) /\
    NoDup (G :: OUT' :: entry_blocks e' ++ hs_blocks h') /\
    In (G, SRC_TABLE) (blocks L' A') /\
    (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
       In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L' A') ->
       (In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (entry_blocks e) /\ ~ In q (hs_blocks h)) \/
       In q (entry_blocks e' ++ hs_blocks h') \/ q = OUT') /\
    (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
       q <> OUT' /\ ~ In q (entry_blocks e') /\ ~ In q (hs_blocks h')) /\
    rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
    rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if send_off cl br TOT then br else dd))] /\
    rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if send_off cl br TOT then ei else 0))] /\
    (exists ev', rw_cells segs mem' ERR [C4 ev']) /\
    bzs LB = with_nul LS0 /\
    (LIVE = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
       (0 < CAP -> In (OUT, CAP) (blocks L' A') /\ bytes_at segs mem' OUT (O ++ junk)) /\ OUT' = OUT) /\
    (LIVE = true ->
       NO + TOT <= CAP' /\ CAP' = ds_ocap FIN /\ In (OUT', CAP') (blocks L' A') /\ fresh_block Bm OUT' CAP' /\
       bytes_at segs mem' OUT' (O ++ LB ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
       rw_cells segs mem' G_OUTV
         [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]).

Definition dtot (D : list Z) : Z := Z.of_nat (length (with_nul (lines ST0 D))).
Definition brf (D : list Z) : Z := if send_off cl br (dtot D) then br else dd.
Definition eif (D : list Z) : Z := if send_off cl br (dtot D) then ei else 0.

Definition DKH (e1 : rentry) : Prop := (re_hp e1 = re_hp e /\ re_kh e1 = re_kh e) \/ re_kh e1 <= 2 ^ 30.

Definition dadr_ok (n : nat) (a : dadr) : Prop :=
  p3a_ok (da_out a) n /\ p3a_ok (da_buf a) n /\ p3a_ok (da_hp a) n /\ Forall (fun x => p3a_ok x n) (da_keys a) /\
  Forall (fun x => p3a_ok x n) (da_pend a) /\ p3a_ok (da_ev a) n /\ Forall (fun x => p3a_ok x n) (da_erecs a).

Definition DLNK (L1 : layout) (A1 : astate) (qd : list sptr) (a : dadr) (oc : Z) (e1 : rentry) (h1 : hsrc) (OUT1 : Z)
    : Prop :=
  (LIVE = true -> 0 < oc -> live_at L1 A1 (resolveF qd (da_out a)) OUT1 oc) /\
  entry_links L1 A1 qd a e1 /\ src_links L1 A1 qd (known_at L A) a h1.

Definition RCORE (L1 : layout) (A1 : astate) (oc : Z) (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (tp : trF) (qd : list sptr)
    (a : dadr) : Prop :=
  length qd = nretF tp /\ wf_from sptr 0 tp /\ dadr_ok (nretF tp) a /\ rt_ok F A1 (runF F qd bnd tp) /\
  DLNK L1 A1 qd a oc e1 h1 OUT1 /\ DKH e1.

Definition RFUT (done : trF) (r : trF * (dstate * dadr)) : Prop :=
  done ++ fst r = TR /\ fst (snd r) = FIN /\ snd (snd r) = FAD.

Definition DTR (L1 : layout) (A1 : astate) (s : dstate) (e1 : rentry) (h1 : hsrc) (OUT1 : Z) : Prop :=
  exists tp qd a, RCORE L1 A1 (ds_ocap s) e1 h1 OUT1 tp qd a /\ RFUT tp (drun (dneed s) LIVE MX s (nretF tp) a).

Definition apush (a : dadr) (vr : adrF * list adrF) : dadr :=
  DA (da_out a) (da_buf a) (da_hp a) (da_keys a) (da_pend a) (fst vr) (snd vr).

Definition DPU (L1 : layout) (A1 : astate) (s : dstate) (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (ls : list (list Z))
    : Prop :=
  exists tp qd a,
    RCORE L1 A1 (ds_ocap s) e1 h1 OUT1
      (tp ++ fst (fst (pushes_run (ds_en s) (ds_ecap s) ls (nretF tp) (da_ev a) (da_erecs a)))) qd
      (apush a (snd (pushes_run (ds_en s) (ds_ecap s) ls (nretF tp) (da_ev a) (da_erecs a)))) /\
    RFUT tp (drun (dneed s) LIVE MX s (nretF tp) a).

Definition DSAME (e1 : rentry) (h1 : hsrc) : Prop :=
  re_fd e1 = re_fd e /\ re_eof e1 = re_eof e /\ hs_fd h1 = hs_fd h /\ hs_open h1 = hs_open h /\
  hs_closed h1 = hs_closed h /\ hl_v (hs_pending h1) = hl_v (hs_pending h) /\
  hl_cap (hs_pending h1) = hl_cap (hs_pending h) /\ hs_partial h1 = hs_partial h /\ hs_held h1 = hs_held h.

Definition DLINK (s : dstate) (e1 : rentry) (h1 : hsrc) : Prop :=
  re_cap e1 = ds_cap s /\ bzs (re_U e1) = ds_u s /\ re_skip e1 = (if ds_skip s then 1 else 0) /\
  keys_texts (re_keys e1) = ds_H s /\ ent_ka e1 = ds_ka s /\ hs_eintr h1 = (if ds_eintr s then 1 else 0) /\
  map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = ds_pend s /\ hs_off h1 = ds_off s /\
  hs_state h1 = ds_ref s /\ hl_n (hs_expected h1) = ds_en s /\ hl_cap (hs_expected h1) = ds_ecap s /\ dwf s.

Definition DHIST (s : dstate) (D : list Z) (h1 : hsrc) (LB1 : list byte) : Prop :=
  bzs PS = D ++ pstream s /\ ds_ref s = feed ST0 D /\ J1 (ds_u s) (ds_skip s) (ds_ref s) /\
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines ST0 D) /\
  firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
  hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
  ds_no s = NO + dtot D /\ bzs LB1 = with_nul (lines ST0 D) /\
  NoDup (ds_H s) /\ same_set (ds_H s) (upds (keys_texts (re_keys e)) (lines ST0 D)) /\
  Z.of_nat (length (ds_H s)) + Z.of_nat (length (pstream s)) < 2 ^ 26 /\
  ds_en s + Z.of_nat (length (pstream s)) < 2 ^ 27.

Definition DBLK (L1 : layout) (A1 : astate) (e1 : rentry) (h1 : hsrc) (OUT1 : Z) : Prop :=
  NoDup (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) /\
  In (G, SRC_TABLE) (blocks L1 A1) /\
  (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
     In (q, m) (blocks L1 A1)) /\
  (forall q m, In (q, m) (blocks L1 A1) ->
     (In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (entry_blocks e) /\ ~ In q (hs_blocks h)) \/
     In q (entry_blocks e1 ++ hs_blocks h1) \/ q = OUT1) /\
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
     q <> OUT1 /\ ~ In q (entry_blocks e1) /\ ~ In q (hs_blocks h1)).

Definition DGLB (D : list Z) (m1 : word -> option byte) : Prop :=
  rw_cells segs m1 G_CLIENT [C4 (Z_to_bv 64 cl)] /\ rw_cells segs m1 G_BROKEN [C1 (Z_to_bv 8 (brf D))] /\
  rw_cells segs m1 G_DEAD [C1 (Z_to_bv 8 dd)] /\ rw_cells segs m1 G_EINTR [C1 (Z_to_bv 8 (eif D))] /\
  (exists ev1, rw_cells segs m1 ERR [C4 ev1]).

Definition DOUT (s : dstate) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (OUT1 : Z) (junk1 LB1 : list byte)
    : Prop :=
  (LIVE = false -> rw_cells segs m1 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\ OUT1 = OUT /\ ds_ocap s = CAP /\
     (0 < CAP -> In (OUT, CAP) (blocks L1 A1) /\ bytes_at segs m1 OUT (O ++ junk))) /\
  (LIVE = true ->
     rw_cells segs m1 G_OUTV [C8 mx; C8 (Z_to_bv 64 (ds_no s)); C8 (Z_to_bv 64 (ds_ocap s)); C8 (Z_to_bv 64 OUT1)] /\
     ((ds_ocap s = 0 /\ OUT1 = 0 /\ ds_no s = 0 /\ O = [] /\ LB1 = []) \/
      (0 < ds_ocap s /\ ds_no s <= ds_ocap s /\ In (OUT1, ds_ocap s) (blocks L1 A1) /\
       fresh_block Bm OUT1 (ds_ocap s) /\ bytes_at segs m1 OUT1 (O ++ LB1 ++ junk1) /\
       Z.of_nat (length junk1) = ds_ocap s - ds_no s))).

Definition DC (s : dstate) (D : list Z) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (junk1 LB1 : list byte) : Prop :=
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 /\
  st_init_done A1 = true /\
  DTR L1 A1 s e1 h1 OUT1 /\
  ro_agree segs m1 /\
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] /\
  entry_okw L1 A1 m1 e1 /\
  src_at Bm L1 A1 m1 HA h1 /\
  others_at Bm m1 j (re_fd e) fs os /\
  DSAME e1 h1 /\
  DLINK s e1 h1 /\
  DHIST s D h1 LB1 /\
  DBLK L1 A1 e1 h1 OUT1 /\
  DGLB D m1 /\
  DOUT s L1 A1 m1 OUT1 junk1 LB1.

Definition RT (R : bvmap 5 word) : Prop :=
  getr R 2 = Z_to_bv 64 (S0 - 144) /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  getr R 8 = Z_to_bv 64 SA /\ getr R 22 = Z_to_bv 64 384 /\ getr R 25 = Z_to_bv 64 DR_TU.

Definition RTK (R : bvmap 5 word) : Prop := RT R /\ getr R 23 = Z_to_bv 64 9 /\ getr R 26 = Z_to_bv 64 4.

Definition RTL (R : bvmap 5 word) : Prop := RTK R /\ getr R 27 = Z_to_bv 64 (-1).

Definition DI (s : dstate) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13924) m1 (seg_rom segs)) md1 /\ RTK R1 /\
    DC s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DF (s : dstate) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x139c0) m1 (seg_rom segs)) md1 /\ RTK R1 /\
    getr R1 10 = Z_to_bv 64 (re_buf e1 + re_used e1) /\ getr R1 11 = Z_to_bv 64 (re_cap e1 - re_used e1) /\
    getr R1 20 = Z_to_bv 64 XH /\ 4096 <= ds_cap s - ulen s /\
    DC s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Lemma pre_facts : MR L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\ S0 mod 16 = 0 /\
  YM05.alloc_ceiling + 8512 <= S0 /\ S0 < 2 ^ 63 /\ (forall a, S0 - 8512 <= a < S0 -> writable_at segs mem a) /\
  getr regs 4 = Z_to_bv 64 (ms_tp Bm) /\ (forall a, ERR <= a < ERR + 4 -> writable_at segs mem a).
Proof using PRE.
  destruct PRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _).
  assert (K : DRAIN_K = 8512) by reflexivity. unfold spZ in *. rewrite K in H6, H8.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. exact H10.
Qed.

Lemma img_lo : forall a, in_img Bm a -> 0 <= a < 2 ^ 21.
Proof using HG HJ O SEGS h junk.
  intros a (_ & s & Hin & H1 & H2). rewrite SEGS in Hin.
  pose proof (proj1 (forallb_forall _ _) CF.gestures_end_b.rsegs_res_top2 s Hin) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma gfacts : YM05.alloc_ceiling + 8512 <= S0 /\ S0 < 2 ^ 63 /\ 2 ^ 46 <= YM05.alloc_ceiling /\
  YM05.alloc_ceiling < 2 ^ 47 /\ 4096 <= G /\ G <= SA /\ SA + 56 <= G + 896 /\ G + 896 <= YM05.alloc_ceiling /\
  G_LOCK_HI <= ERR /\ ERR + 4 <= 2 ^ 21 /\ Z.of_nat j < 4.
Proof using EHI GEI HG HJ O PRE SEGS h junk.
  pose proof pre_facts as (HM0 & _ & _ & _ & _ & HCEIL & H63 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof HG as (GI & _ & GL1 & GL2 & _).
  pose proof (blk_rng L A mem md G SRC_TABLE HM0 GI) as GR. unfold SRC_TABLE, SRC_ENTRY in *.
  pose proof (img_lo _ (GEI (ERR + 3) ltac:(lia))) as EL.
  repeat split; lia.
Qed.

Lemma rp_refl : relay_post Bm API DRAIN_K EE FF L A regs mem md L A regs mem md.
Proof using HG HJ Hbr Hcl Hdd Hei OUTD PRE.
  pose proof PRE as (HM & HWF & HBD & _ & _ & _ & _ & HWS & _ & HWE & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|]. split; [lia|].
  split; [intros; reflexivity|]. split; [intros p n H _ _; exact H|].
  split; [intros p H; split; [exact H | reflexivity]|].
  split; [intros a _ H; exact H|].
  split; [intros r _; reflexivity|].
  split; [exists (m_vmmaps md); symmetry; apply sb_vm_id|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HWS; exact Ha | apply HWE; exact Ha].
Qed.

Lemma ro_low : forall x : word, Mem.ro_addr rsegs x = true -> bv_unsigned x < 0x21624.
Proof using Bm G HJ O h junk regs.
  intros x H. destruct (Z_lt_ge_dec (bv_unsigned x) 0x21624) as [Lt|Ge]; [exact Lt|]. exfalso.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  pose proof (sb_ro_ge (bv_unsigned x) ltac:(lia)) as R2. unfold wa in R2. rewrite Z_to_bv_bv_unsigned in R2.
  congruence.
Qed.

Lemma ro_munch : forall m m' W, ro_agree rsegs m -> munch W m m' ->
  (forall x : word, bv_unsigned x < 0x21624 -> outside W (bv_unsigned x)) -> ro_agree rsegs m'.
Proof using Bm G HJ O h junk regs. intros m m' W H MU HW a Hro. unfold mrd. rewrite (MU a (HW a (ro_low a Hro))). exact (H a Hro). Qed.

Lemma frame_cb : forall m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> writable_at rsegs m (a + i)) -> exists bs, rw_cells rsegs m a [CB n bs].
Proof using Bm G HJ O h junk regs.
  intros m a n H0 H1 W.
  destruct (CF.gestures_end_b.bytes_of_mbytes rsegs m a n H0 H1) as (bs & Lb & Hb).
  { intros i Hi. apply CF.gestures_end_b.writable_mbyte. apply W. exact Hi. }
  exists bs. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Lb | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - split; [exact H0|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. cbn [cells_size csize] in Hi.
    exact (W i ltac:(lia)).
Qed.

Lemma dtot_nil : dtot [] = 0.
Proof using. reflexivity. Qed.

Lemma brf_nil : brf [] = br.
Proof using. unfold brf. rewrite dtot_nil. unfold send_off. rewrite Z.eqb_refl, orb_true_r. reflexivity. Qed.

Lemma eif_nil : eif [] = ei.
Proof using. unfold eif. rewrite dtot_nil. unfold send_off. rewrite Z.eqb_refl, orb_true_r. reflexivity. Qed.

Ltac rgv X := rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X) by reflexivity; simp_regs;
  first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned | apply Z_to_bv_bv_unsigned].

Lemma dwf_init : dwf (drain_init NO CAP e h).
Proof using G HJ O SRC0 junk regs.
  pose proof SRC0 as (_ & _ & _ & _ & _ & _ & _ & PC & _).
  unfold dwf, drain_init. cbn [ds_off ds_pend].
  destruct PC as [(RN & O0)|(r & rs & RE & RO)].
  - rewrite RN, O0. split; [lia|]. intros r rs E. discriminate.
  - rewrite RE. cbn [map]. split; [lia|]. intros r1 rs1 E. injection E as <- <-. unfold bzs. rewrite length_map. lia.
Qed.

Lemma dtr_init : DTR L A (drain_init NO CAP e h) e h OUT.
Proof using EOK G HJ NODUP OUTD PRE RES0 SRC0.
  assert (LK : forall a n, In (a, n) (blocks L A) -> live_at L A (resolveF [] (known_at L A a)) a n).
  { intros a n Hin. pose proof pre_facts as (HM0 & _). exact (sptr_of_spec L A a n (NODUP L A mem md HM0) Hin). }
  assert (LA1 : forall LA0 l ln m0, list_at Bm L A m0 LA0 l ln ->
            (0 < hl_cap l -> live_at L A (resolveF [] (known_at L A (hl_v l))) (hl_v l) (16 * hl_cap l)) /\
            Forall2 (fun r a => live_at L A (resolveF [] a) (fst r) (Z.of_nat (length (snd r)) + 1))
              (hl_recs l) (map (fun r => known_at L A (fst r)) (hl_recs l)) /\
            Forall (fun r => live_at L A (resolveF [] (known_at L A (fst r))) (fst r) (Z.of_nat (length (snd r)) + 1))
              (hl_recs l)).
  { intros LA0 l ln m0 (_ & _ & C3 & _ & _ & C6).
    split; [intros CP; destruct C3 as [(C0 & _)|(_ & IN & _)]; [lia | exact (LK _ _ IN)]|].
    clear - C6 LK. revert C6. generalize (hl_recs l) as rs. induction rs as [|r rs IH]; intros F6.
    - split; constructor.
    - destruct (IH (Forall_inv_tail F6)) as [IH1 IH2]. pose proof (LK _ _ (proj1 (Forall_inv F6))) as L1r.
      cbn [map]. split; constructor; [exact L1r | exact IH1 | exact L1r | exact IH2]. }
  assert (FK : forall (T : Type) (n : nat) (f : T -> Z) (l : list T),
            Forall (fun x => p3a_ok x n) (map (fun y => known_at L A (f y)) l)).
  { intros T n f l. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (y & <- & _). exact I. }
  assert (FU : forall jn an, drun (dneed (drain_init NO CAP e h)) LIVE MX (drain_init NO CAP e h) jn an =
                             drun (S (S (length PS))) LIVE MX (drain_init NO CAP e h) jn an).
  { intros jn an. apply drain_run_fuel; [exact dwf_init | lia |].
    unfold dneed. rewrite pstream_init. unfold bzs. rewrite length_map.
    destruct (ds_eintr _); cbn [Nat.b2n]; lia. }
  pose proof EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EB & _ & EH & _ & _ & EK).
  pose proof SRC0 as (_ & _ & _ & _ & _ & SP & _ & _ & _ & _ & SPt & _ & _ & _ & _ & SE & SH & _).
  exists [], [], AD0. split.
  - split; [reflexivity|]. split; [exact I|].
    split.
    { unfold dadr_ok, drain_start. cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
      split; [exact I|]. split; [exact I|]. split; [exact I|]. split; [apply FK|]. split; [apply FK|].
      split; [exact I | apply FK]. }
    split; [exact RES0|].
    split; [|left; split; reflexivity].
    split.
    { intros _ CP. cbn [drain_init ds_ocap] in CP |- *. unfold drain_start. cbn [da_out].
      destruct OUTD as [(C0 & _)|(_ & _ & IN & _)]; [lia | exact (LK _ _ IN)]. }
    split.
    { unfold entry_links, drain_start. cbn [da_buf da_hp da_keys].
      split; [intros CP; destruct EB as [(C0 & _)|(_ & IN & _)]; [lia | exact (LK _ _ IN)]|].
      split; [intros HP; destruct EH as [(H0 & _)|(IN & _)]; [contradiction | exact (LK _ _ IN)]|].
      clear - EK LK. revert EK. generalize (re_keys e) as ks. induction ks as [|k ks IH]; intros FKs.
      - constructor.
      - cbn [map]. constructor; [exact (LK _ _ (proj1 (Forall_inv FKs))) | exact (IH (Forall_inv_tail FKs))]. }
    unfold src_links, expected_links, drain_start. cbn [da_pend da_ev da_erecs].
    destruct (LA1 _ _ _ _ SP) as (P1 & P2 & _). destruct (LA1 _ _ _ _ SE) as (E1 & E2 & _).
    destruct (LA1 _ _ _ _ SH) as (H1 & _ & H3).
    split; [exact P1|]. split; [exact P2|]. split; [exact (LK _ _ SPt)|].
    split; [split; [exact E1 | exact E2]|]. split; [exact H1 | exact H3].
  - unfold RFUT. rewrite FU. split; [reflexivity|]. split; [|reflexivity].
    unfold drain_fin, drain_go. apply drun_state.
Qed.

Lemma entry_step : SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 DRAIN) mem (seg_rom segs)) md)
  (DI (drain_init NO CAP e h)).
Proof using All.
  pose proof pre_facts as (HM0 & HW0 & HB0 & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ HM0) as (Hh & Hl & _).
  destruct (frame_cb mem (S0 - 144) 144) as (junk0 & FR0); [lia | lia | |].
  { intros i Hi. rewrite <- SEGS. apply HWS. lia. }
  assert (SA8 : SA mod 8 = 0).
  { pose proof HG as (GI & _ & _ & _ & GM). pose proof (blk_align L A mem md G SRC_TABLE HM0 GI) as GA.
    unfold SRC_ENTRY in GM. clear - GM GA. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 (getr regs 10)) as SAR. change (bv_modulus 64) with (2 ^ 64) in SAR.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr. rewrite SEGS. unfold DRAIN.
    rewrite <- (Z_to_bv_bv_unsigned (getr regs 10)).
    eapply dr_prologue; [exact FR0 | lia | exact SAR | exact SA8]. }
  intros ms1 (can1 & (m1 & j0 & j1 & j2 & j4 & HC & MU & WM & LJ0 & LJ1 & LJ2 & LJ4 & FR1) & EQ1). subst can1.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  apply SR_ret.
  assert (WM' : wmono segs mem m1) by (rewrite SEGS; exact WM).
  pose proof (msame_munch _ _ _ MU WM') as MS1.
  assert (LOW : forall a, 0 <= a < S0 - 144 -> 0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0)] a).
  { intros a Ha. split; [clear - Ha F1 F2 F3; lia|]. cbn [outside]. split; [clear - Ha; lia | exact I]. }
  assert (BLK : forall q k a, In (q, k) (blocks L A) -> q <= a < q + k -> 0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0)] a).
  { intros q k a Hq Ha. apply LOW. pose proof (blk_rng L A mem md q k HM0 Hq) as BR. clear - Ha BR F1 F3. lia. }
  pose proof SRC0 as (SC1 & SC2 & SC3 & SC4 & SC5 & SC6 & SC7 & SC8 & SC9 & SC10 & SC11 & SC12 & SC13 & SC14 & SC15 &
    SC16 & SC17 & SC18).
  pose proof EOK as (EO1 & EO2 & EO3 & EO4 & EO5 & EO6 & EO7 & EO8 & EO9 & EO10 & EO11 & EO12 & EO13 & EO14 & EO15).
  pose proof SC16 as (_ & (EXN & _) & _).
  exists R1, L, A, m1, md, e, h, OUT, junk, [], [].
  split; [reflexivity|].
  split.
  { unfold RTK, RT. repeat match goal with |- _ /\ _ => split end; rgv X1. }
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ rp_refl MU); [exact WM' | exact GEI |].
    intros a Ha. destruct (Z_lt_le_dec a (S0 - 144)) as [D|D]; [left; cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec a S0) as [D2|D2].
    - right. left. change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. lia.
    - left. cbn [outside]. split; [lia | exact I]. }
  split; [exact INIT|].
  split; [exact dtr_init|].
  split.
  { rewrite SEGS. apply (ro_munch mem m1 [(S0 - 144, S0)]); [rewrite <- SEGS; exact RO0 | exact MU |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  split; [exists j0, j1, j2, j4; rewrite SEGS; exact FR1|].
  split; [eapply rw_tr; [exact MS1 | exact HE0 | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                         clear - Ha F1 F3 F5 F6 F7 F8; lia]|].
  split; [eapply entry_okw_tr; [exact MS1 | exact (entry_okw_of _ _ _ _ EOK) | intros q k Hq _; exact Hq |
           intros q k a Hq _ Ha; exact (BLK q k a Hq Ha)]|].
  split.
  { eapply src_at_tr0; [exact MS1 | exact SRC0 | | intros q k Hq _; exact Hq | intros q k a Hq _ Ha; exact (BLK q k a Hq Ha)].
    intros a Ha. apply LOW. unfold G_S, SRC_SIZE in Ha. clear - Ha F1 F3 F11. lia. }
  split.
  { eapply others_at_tr; [exact MS1 | exact OTH |]. intros i a Hi _ Ha. apply LOW. unfold G_S, SRC_SIZE in Ha.
    clear - Ha Hi F1 F3. lia. }
  split; [repeat split; reflexivity|].
  split.
  { unfold DLINK, drain_init. cbn [ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap].
    split; [reflexivity|]. split; [reflexivity|].
    split; [destruct EO2 as [E|E]; rewrite E; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [destruct SC3 as [E|E]; rewrite E; reflexivity|].
    do 5 (split; [reflexivity|]). exact dwf_init. }
  split.
  { unfold DHIST. rewrite (pstream_init NO CAP e h). unfold drain_init.
    cbn [ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { split; [rewrite HSK; reflexivity|].
      split; [intros E; destruct EO2 as [E2|E2]; [exact (HSW E2) | rewrite E2 in E; discriminate]|].
      split; [unfold bzs; rewrite length_map; apply Nat2Z.inj_le; rewrite EO7; unfold LINE_LIMIT;
              change (Z.of_nat 6000) with 6000; clear - EO8; lia|].
      apply nozero_of. exact EO9. }
    rewrite lines_nil. cbn [map]. rewrite app_nil_r.
    split; [reflexivity|]. split; [apply firstn_all|].
    split; [clear; lia|].
    split; [rewrite dtot_nil; clear; lia|].
    split; [reflexivity|].
    split; [apply nodup_kt; exact EO14|].
    split; [intros y; split; intros Hy; exact Hy|].
    unfold keys_texts, bzs. rewrite !length_map. unfold re_nheld in HNH. unfold hl_n in EXN |- *. clear - HNH EXN HEC HPL. split; lia. }
  split.
  { unfold DBLK. split; [exact HND|]. split; [exact (proj1 HG)|].
    split; [intros q m Hq _ _; exact Hq|].
    split.
    { intros q m Hq. destruct (Z.eq_dec q OUT) as [->|NE]; [right; right; reflexivity|].
      destruct (in_dec Z.eq_dec q (entry_blocks e ++ hs_blocks h)) as [I|I]; [right; left; exact I|].
      left. split; [exact Hq|]. split; [exact NE|].
      split; intros I2; apply I; apply in_or_app; [left|right]; exact I2. }
    intros q m _ _ NE NI. split; [exact NE|]. split; intros I2; apply NI; apply in_or_app; [left|right]; exact I2. }
  split.
  { unfold DGLB. rewrite brf_nil, eif_nil.
    split; [eapply rw_tr; [exact MS1 | exact CCL | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                           unfold G_CLIENT in Ha; clear - Ha F1 F3; lia]|].
    split; [eapply rw_tr; [exact MS1 | exact CBR | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                           unfold G_BROKEN in Ha; clear - Ha F1 F3; lia]|].
    split; [eapply rw_tr; [exact MS1 | exact CDD | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                           unfold G_DEAD in Ha; clear - Ha F1 F3; lia]|].
    split; [eapply rw_tr; [exact MS1 | exact CEI | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                           unfold G_EINTR in Ha; clear - Ha F1 F3; lia]|].
    destruct CERR as (ev & CE). exists ev.
    eapply rw_tr; [exact MS1 | exact CE | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                   unfold G_LOCK_HI in F9; clear - Ha F1 F3 F9 F10; lia]. }
  unfold DOUT, drain_init. cbn [ds_no ds_ocap]. split.
  - intros LV. split; [eapply rw_tr; [exact MS1 | exact COUT | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                                      unfold G_OUTV in Ha; clear - Ha F1 F3; lia]|].
    split; [reflexivity|]. split; [reflexivity|].
    intros Cp. destruct OUTD as [(C0 & _)|(_ & _ & OI & _ & OB & LO & LJ)]; [clear - Cp C0; lia|].
    split; [exact OI|]. eapply by_tr; [exact MS1 | exact OB |]. intros a Ha. apply (BLK OUT CAP a OI).
    rewrite length_app in Ha. clear - Ha LO LJ. lia.
  - intros LV. split.
    + rewrite !Z_to_bv_bv_unsigned.
      eapply rw_tr; [exact MS1 | exact COUT | intros a Ha; apply LOW; cbn [cells_size csize] in Ha;
                     unfold G_OUTV in Ha; clear - Ha F1 F3; lia].
    + destruct OUTD as [(C0 & O0 & N0 & OE)|(Cp & NL & OI & OF & OB & LO & LJ)].
      * left. split; [exact C0|]. split; [exact O0|]. split; [exact N0|]. split; [exact OE | reflexivity].
      * right. split; [exact Cp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OF|].
        split; [|clear - LJ; lia]. cbn [app]. eapply by_tr; [exact MS1 | exact OB |]. intros a Ha.
        apply (BLK OUT CAP a OI). rewrite length_app in Ha. clear - Ha LO LJ. lia.
Qed.

Ltac rgw X := rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X) by reflexivity; simp_regs;
  first [reflexivity | assumption | symmetry; apply Z_to_bv_bv_unsigned | apply Z_to_bv_bv_unsigned].

Lemma ret_ok_13954 : YK0s.ret_ok (Z_to_bv 64 0x13954).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ro_munch2 : forall m m' W, ro_agree rsegs m -> munch W m m' ->
  (forall x : word, in_img Bm (bv_unsigned x) -> outside W (bv_unsigned x)) -> ro_agree rsegs m'.
Proof using G HJ O SEGS h junk regs.
  intros m m' W H MU HW a Hro. unfold mrd. rewrite (MU a); [exact (H a Hro)|]. apply HW.
  pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  apply (ro_in_img Bm SEGS (bv_unsigned a)); [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hro.
Qed.

Lemma pre_realloc : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre_k Bm MR REALLOC_STACK L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold REALLOC_STACK, ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold REALLOC_STACK, ALLOC_STACK in Ha. apply SC1. left.
    change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma untouched : forall s L1 A1 m1 e1 h1 OUT1 junk1 LB1 q m,
  DBLK L1 A1 e1 h1 OUT1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  In (q, m) (blocks L A) -> 0 < m -> ~ FF q -> ~ In q (entry_blocks e1) /\ ~ In q (hs_blocks h1).
Proof using ROOM.
  intros s L1 A1 m1 e1 h1 OUT1 junk1 LB1 q m (ND & _ & _ & _ & BV) (OF & _) Hq Hm NF.
  destruct (Z.eq_dec q OUT) as [->|NE].
  - destruct (send_live cl br dd TOT) eqn:LV; [exfalso; apply NF; left; split; reflexivity|].
    destruct (OF eq_refl) as (_ & EO & _). rewrite EO in ND.
    apply NoDup_ListNoDup, List.NoDup_cons_iff in ND as [_ ND]. apply List.NoDup_cons_iff in ND as [NI _].
    split; intros I; apply NI; apply in_or_app; [left|right]; exact I.
  - assert (NI : ~ In q (entry_blocks e ++ hs_blocks h)) by (intros I; apply NF; right; exact I).
    destruct (BV q m Hq Hm NE NI) as (_ & U1 & U2). split; assumption.
Qed.

Lemma dx_odec : forall W a, outside W a \/ exists lo hi, In (lo, hi) W /\ lo <= a < hi.
Proof using Bm G HJ O h junk regs.
  induction W as [|[lo hi] W IH]; intros a; cbn [outside]; [left; exact I|].
  destruct (IH a) as [Ox|(lo' & hi' & I' & R')]; [|right; exists lo', hi'; split; [right; exact I' | exact R']].
  destruct (Z_le_gt_dec lo a) as [D1|D1]; [destruct (Z_lt_ge_dec a hi) as [D2|D2]|].
  - right. exists lo, hi. split; [left; reflexivity | lia].
  - left. split; [lia | exact Ox].
  - left. split; [lia | exact Ox].
Qed.

Lemma grp_img : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> in_img Bm a.
Proof using GRP. intros a Ha. exact (proj1 (GRP a Ha)). Qed.

Lemma err_hi : G_S + SRC_SIZE * SOURCES_MAX <= ERR.
Proof using EHI G GRP HJ O h junk regs.
  destruct (Z_lt_le_dec ERR (G_S + SRC_SIZE * SOURCES_MAX)) as [Lt|Ge]; [exfalso|exact Ge].
  destruct (GRP ERR) as (_ & _ & _ & NE); [unfold G_RELAY_LO, G_S, G_LOCK_HI in *; lia | apply NE; lia].
Qed.

Lemma g_noimg : forall a, SA <= a < SA + 56 -> ~ in_img Bm a.
Proof using HG HJ O h junk.
  intros a Ha Im. pose proof HG as (_ & (_ & _ & FI) & GL1 & GL2 & _).
  apply (FI (a - G)); [unfold SRC_TABLE, SRC_ENTRY in *; lia|]. replace (G + (a - G)) with a by lia. exact Im.
Qed.

Definition WOK (W : list ivl) : Prop := forall lo hi, In (lo, hi) W ->
  (HA + 12 <= lo /\ hi <= HA + 16) \/ (ERR <= lo /\ hi <= ERR + 4) \/ (SA <= lo /\ hi <= SA + 56).

Lemma dx_pa : forall W a, WOK W -> 0 <= a < 2 ^ 64 -> ~ (HA + 12 <= a < HA + 16) -> ~ (ERR <= a < ERR + 4) ->
  (in_img Bm a \/ ~ (SA <= a < SA + 56)) -> 0 <= a < 2 ^ 64 /\ outside W a.
Proof using ERR4 HG HJ O h junk.
  intros W a HW Ha N1 N2 N3. split; [exact Ha|].
  destruct (dx_odec W a) as [Ox|(lo & hi & Iw & R)]; [exact Ox|exfalso].
  destruct (HW lo hi Iw) as [B|[B|B]]; [lia | lia |].
  destruct N3 as [Im|N3]; [exact (g_noimg a ltac:(lia) Im) | lia].
Qed.

Lemma dx_pa_blk : forall W L1 A1 m1 md1 q k a, WOK W -> MR L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) ->
  In (G, SRC_TABLE) (blocks L1 A1) -> q <> G -> q <= a < q + k -> 0 <= a < 2 ^ 64 /\ outside W a.
Proof using AX EHI ERR4 GEI GRP HG HJ O PRE SEGS h junk.
  intros W L1 A1 m1 md1 q k a HW HM Hq HG1 NE Ha.
  pose proof (blk_rng L1 A1 m1 md1 q k HM Hq) as BR.
  pose proof (blk_noimg L1 A1 m1 md1 q k (a - q) HM Hq ltac:(lia)) as NI. replace (q + (a - q)) with a in NI by lia.
  pose proof (blocks_disjoint Bm API L1 A1 m1 md1 q k G SRC_TABLE HM Hq HG1 NE) as DJ.
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  apply (dx_pa W a HW); [lia | intros R; apply NI, grp_img; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia
    | intros R; exact (NI (GEI a R)) | right; unfold SRC_TABLE, SRC_ENTRY in *; lia].
Qed.

Lemma dx_pa_img : forall W a, WOK W -> img_plain Bm a -> ~ (HA + 12 <= a < HA + 16) -> 0 <= a < 2 ^ 64 /\ outside W a.
Proof using ERR4 HG HJ O SEGS h junk.
  intros W a HW (Im & _ & _ & NE) N1. pose proof (img_lo a Im) as IL.
  apply (dx_pa W a HW); [lia | exact N1 | exact NE | left; exact Im].
Qed.

Lemma dx_pa_stk : forall W a, WOK W -> S0 - 144 <= a < S0 -> 0 <= a < 2 ^ 64 /\ outside W a.
Proof using EHI ERR4 GEI HG HJ O PRE SEGS h junk.
  intros W a HW Ha. pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  apply (dx_pa W a HW); [lia | unfold G_S, SRC_SIZE in *; lia | lia | right; lia].
Qed.

Lemma dx_ng : forall OUT1 l q, NoDup (G :: OUT1 :: l) -> (q = OUT1 \/ In q l) -> q <> G.
Proof using.
  intros OUT1 l q ND H E. subst q. apply NoDup_ListNoDup, List.NoDup_cons_iff in ND as [NI _]. apply NI.
  destruct H as [H|H]; [left; symmetry; exact H | right; exact H].
Qed.

Lemma dc_munch : forall s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 W,
  DC s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 -> munch W m1 m2 -> wmono segs m1 m2 -> WOK W ->
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m2 md1 /\ ro_agree segs m2 /\
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  entry_okw L1 A1 m2 e1 /\
  (forall v, rw_cells segs m2 HA [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                                 C4 (Z_to_bv 64 (hs_closed h1)); C4 (Z_to_bv 64 v)] -> (v = 0 \/ v = 1) ->
     src_at Bm L1 A1 m2 HA (hs_eset h1 v)) /\
  others_at Bm m2 j (re_fd e) fs os /\ DGLB D m2 /\ DOUT s L1 A1 m2 OUT1 junk1 LB1.
Proof using AX BW EHI ERR4 EU GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 W DC1 MU WM HW.
  pose proof DC1 as (RP1 & _ & _ & RO1 & FR1 & _ & EK1 & SR1 & OT1 & _ & _ & HI1 & BK1 & GL1 & OU1).
  pose proof BK1 as (ND1 & GI1 & _).
  pose proof HI1 as (_ & _ & _ & _ & _ & _ & H7 & H8 & _).
  pose proof RP1 as (M1 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof err_hi as EH. unfold G_LOCK_HI in F9.
  pose proof (msame_munch W m1 m2 MU WM) as MS.
  assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> (q = OUT1 \/ In q (entry_blocks e1 ++ hs_blocks h1)) ->
            q <= a < q + k -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros q k a Hq Hn Ha. exact (dx_pa_blk W L1 A1 m1 md1 q k a HW M1 Hq GI1 (dx_ng OUT1 _ q ND1 Hn) Ha). }
  assert (PI : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX \/ G_CLIENT <= a < G_CLIENT + 4 ->
            ~ (HA + 12 <= a < HA + 16) -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a [Ha|Ha] N; [exact (dx_pa_img W a HW (GRP a Ha) N) | exact (dx_pa_img W a HW (GCP a Ha) N)]. }
  assert (LO : Z.of_nat (length O) = NO)
    by (destruct OUTD as [(_ & _ & N0 & ->)|(_ & _ & _ & _ & _ & LO & _)]; [cbn; lia | exact LO]).
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU WM GEI).
    intros a Ha. destruct (dx_odec W a) as [Ox|(lo & hi & Iw & R)]; [left; exact Ox|right].
    destruct (HW lo hi Iw) as [B|[B|B]].
    - right. left. split; [apply GRP; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
      cbv beta. right. right. left. unfold SRC_SIZE in *. lia.
    - right. right. left. lia.
    - right. right. right. split; [exact (g_noimg a ltac:(lia))|].
      split; [exists G, SRC_TABLE; split; [exact GI1 | unfold SRC_TABLE, SRC_ENTRY in *; lia]|].
      intros p n i _ _ _ _ NE E. apply NE. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. lia. }
  split.
  { intros x Hro. unfold mrd. rewrite (MU x); [exact (RO1 x Hro)|].
    rewrite SEGS in Hro. pose proof (ro_low x Hro) as XL. pose proof (bv_unsigned_in_range 64 x) as XR.
    change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (XI : in_img Bm (bv_unsigned x)).
    { apply (ro_in_img Bm SEGS (bv_unsigned x)); [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hro. }
    refine (proj2 (dx_pa W _ HW _ _ _ _)); [lia | unfold G_S, SRC_SIZE in *; lia | lia | left; exact XI]. }
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FR). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FR |].
    intros a Ha. cbn [cells_size csize app dr_saved] in Ha. exact (dx_pa_stk W a HW ltac:(lia)). }
  split.
  { eapply entry_okw_tr; [exact MS | exact EK1 | intros q k Hq _; exact Hq |].
    intros q k a Hq Hb Ha. exact (PB q k a Hq (or_intror (in_or_app _ _ _ (or_introl Hb))) Ha). }
  split.
  { intros v C V. eapply src_at_tr; [exact MS | exact SR1 | exact C | exact V | | intros q k Hq _; exact Hq |].
    - intros a Ha. cbv beta. apply PI; [left|]; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    - intros q k a Hq Hb Ha. exact (PB q k a Hq (or_intror (in_or_app _ _ _ (or_intror Hb))) Ha). }
  split.
  { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi _ Ha. cbv beta.
    apply PI; [left|]; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
  split.
  { destruct GL1 as (C1 & C2 & C3 & CC4 & (ev1 & C5)).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; cbn [cells_size csize] in Ha; cbv beta;
            apply PI; [right|]; unfold G_CLIENT, G_S, SRC_SIZE in *; lia|].
    split; [eapply rw_tr; [exact MS | exact C2 |]; intros a Ha; cbn [cells_size csize] in Ha; cbv beta;
            apply PI; [left|]; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact C3 |]; intros a Ha; cbn [cells_size csize] in Ha; cbv beta;
            apply PI; [left|]; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact CC4 |]; intros a Ha; cbn [cells_size csize] in Ha; cbv beta;
            apply PI; [left|]; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    destruct C5 as [_ (_ & _ & CW)].
    destruct (sb_c4 m2 ERR) as (v & HV); [lia | lia | |exists v; rewrite SEGS; exact HV].
    intros i Hi. rewrite <- SEGS. exact (WM _ (CW i ltac:(cbn [cells_size csize]; lia))). }
  destruct OU1 as (OF & OT). split.
  - intros LV. destruct (OF LV) as (C & EO & EC & OB).
    split; [eapply rw_tr; [exact MS | exact C |]; intros a Ha; cbn [cells_size csize] in Ha; cbv beta;
            apply PI; [left|]; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [exact EO|]. split; [exact EC|]. intros Cp. destruct (OB Cp) as (OI & OBy). split; [exact OI|].
    eapply by_tr; [exact MS | exact OBy |]. intros a Ha. cbv beta.
    apply (PB OUT CAP a OI); [left; symmetry; exact EO|].
    destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & _ & LJ)]; [lia|]. rewrite length_app in Ha. lia.
  - intros LV. destruct (OT LV) as (C & OB).
    split; [eapply rw_tr; [exact MS | exact C |]; intros a Ha; cbn [cells_size csize] in Ha; cbv beta;
            apply PI; [left|]; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    destruct OB as [Z0|(Cp & NL & OI & OFr & OBy & LJ)]; [left; exact Z0|right].
    split; [exact Cp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OFr|]. split; [|exact LJ].
    eapply by_tr; [exact MS | exact OBy |]. intros a Ha. cbv beta.
    apply (PB OUT1 (ds_ocap s) a OI); [left; reflexivity|].
    assert (LL : Z.of_nat (length LB1) = dtot D)
      by (unfold dtot; rewrite <- H8; unfold bzs; rewrite length_map; reflexivity).
    rewrite !length_app in Ha. lia.
Qed.

Lemma dx_slack : forall L1 A1 m1 md1 a XL, MR L1 A1 m1 md1 -> In (a, XL + 1) (blocks L1 A1) -> 0 <= a -> 0 <= XL ->
  a + XL + 1 + 8 <= 2 ^ 64 -> exists sl, Z.of_nat (length sl) = (- (a + XL + 1)) mod 8 /\ bytes_at segs m1 (a + XL + 1) sl.
Proof using HG HJ O SLACK h junk.
  intros L1 A1 m1 md1 a XL HM Hin Ha HX Hb.
  pose proof (Z.mod_pos_bound (- (a + XL + 1)) 8 ltac:(lia)) as R8.
  destruct (CF.gestures_end_b.bytes_of_mbytes segs m1 (a + XL + 1) (Z.to_nat ((- (a + XL + 1)) mod 8)))
    as (sl & Ls & Hs).
  - lia.
  - lia.
  - intros i Hi. apply CF.gestures_end_b.present_mbyte. apply (SLACK L1 A1 m1 md1 a (XL + 1) _ HM Hin).
    assert (E : 8 * ((a + (XL + 1) + 7) / 8) = a + XL + 1 + (- (a + XL + 1)) mod 8)
      by (Z.div_mod_to_equations; lia).
    lia.
  - exists sl. split; [lia | exact Hs].
Qed.

Lemma keys_slack : forall L1 A1 m1 md1 ks, MR L1 A1 m1 md1 -> Forall (key_okw L1 A1 m1) ks ->
  exists ks', map key_addr ks' = map key_addr ks /\ map key_text ks' = map key_text ks /\
    keys_texts ks' = keys_texts ks /\ key_ptrs ks' = key_ptrs ks /\ length ks' = length ks /\
    Forall (fun k =>
      In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L1 A1) /\
      fresh_block Bm (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
      bytes_at segs m1 (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
      ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= 6000 /\
      (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k))) ks'.
Proof using HG HJ O SLACK h junk.
  intros L1 A1 m1 md1 ks HM. induction ks as [|k ks IH]; intros H.
  - exists []. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity | constructor].
  - inversion H as [|k0 ks0 HK HF]; subst.
    destruct HK as (K1 & K2 & K3 & K4 & K5).
    destruct (IH HF) as (ks' & E1 & E2 & E3 & E4 & E5 & F').
    pose proof K2 as (B1 & B2 & _). pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    destruct (dx_slack L1 A1 m1 md1 (key_addr k) (Z.of_nat (length (key_text k))) HM K1) as (sl & Ls & Hs);
      [lia | lia | lia |].
    exists ((fst k, sl) :: ks').
    split; [cbn [map]; rewrite E1; reflexivity|].
    split; [cbn [map]; rewrite E2; reflexivity|].
    split; [unfold keys_texts in *; cbn [map]; rewrite E3; reflexivity|].
    split; [rewrite !CF.gestures_end_b.key_ptrs_cons, E4; reflexivity|].
    split; [cbn [length]; rewrite E5; reflexivity|].
    constructor; [|exact F'].
    change (key_addr (fst k, sl)) with (key_addr k). change (key_text (fst k, sl)) with (key_text k).
    change (key_slack (fst k, sl)) with sl.
    split; [exact K1|]. split; [exact K2|]. split; [|split; [exact K4 | split; [exact K5 | lia]]].
    change (key_text k ++ Z_to_bv 8 0 :: sl) with (key_text k ++ [Z_to_bv 8 0] ++ sl). rewrite app_assoc.
    apply bytes_at_app. split; [exact K3|]. rewrite length_app. cbn [length].
    replace (key_addr k + Z.of_nat (length (key_text k) + 1)) with (key_addr k + Z.of_nat (length (key_text k)) + 1)
      by lia.
    exact Hs.
Qed.

Lemma exit_post : forall s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 W R2 EOF,
  DC s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 -> 4096 <= ds_cap s - ulen s -> ds_eintr s = false -> ds_pend s = [] ->
  munch W m1 m2 -> wmono segs m1 m2 -> WOK W -> (forall a, HA <= a < HA + 16 -> outside W a) ->
  regs_preserved regs R2 -> EOF = (if hs_closed h =? 1 then 1 else re_eof e) -> (EOF = 0 \/ EOF = 1) ->
  rw_cells segs m2 SA [CB 56 (entry_bytes (RE (re_fd e1) EOF (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1)
    (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1) (re_U e1) (re_junk e1)))] ->
  DPOST (mkCfg (YK11.mkst R2 (getr regs 1) m2 (seg_rom segs)) md1).
Proof using AX BW EHI ERR4 EU GCP GEI GRP HG HJ OUTD PRE SEGS SLACK.
  intros s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 W R2 EOF DC1 GR EI PE MU WM HW HAW PRS HEOF HE01 SAC2.
  pose proof DC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof SM1 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _).
  pose proof BK1 as (ND1 & GI1 & SV1 & CL1 & FB1).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  destruct (dc_munch s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 W DC1 MU WM HW)
    as (RP2 & RO2 & _ & EK2 & SRC2 & OT2 & GL2 & OU2).
  pose proof RP2 as (M2 & _).
  pose proof EK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E15).
  destruct (keys_slack L1 A1 m2 md1 (re_keys e1) M2 E15) as (ks' & KA & KT & KX & KP & KL & KF).
  assert (DN : forall jn an, drun (dneed s) LIVE MX s jn an = ([], (s, an)))
    by (intros jn an; unfold dneed; exact (drun_end _ LIVE MX s jn an GR EI PE)).
  destruct TR1 as (tp & qd & ad & (RQ & _ & _ & RS & (LO & LE & LS) & KH) & TE & TF & TA).
  rewrite DN in TE, TF, TA. cbn [fst snd] in TE, TF, TA. rewrite app_nil_r in TE.
  assert (FT : forall (ks1 ks2 : list (Z * list byte * list byte)) (xs : list adrF),
            map key_addr ks1 = map key_addr ks2 -> map key_text ks1 = map key_text ks2 ->
            Forall2 (fun k x => live_at L1 A1 (resolveF qd x) (key_addr k) (Z.of_nat (length (key_text k)) + 1)) ks2 xs ->
            Forall2 (fun k x => live_at L1 A1 (resolveF qd x) (key_addr k) (Z.of_nat (length (key_text k)) + 1)) ks1 xs).
  { induction ks1 as [|k1 ks1 IH]; intros ks2 xs EA ET FKS.
    - destruct ks2 as [|k2 ks2]; [exact FKS | discriminate EA].
    - destruct ks2 as [|k2 ks2]; [discriminate EA|].
      cbn [map] in EA, ET. injection EA as EA1 EA2. injection ET as ET1 ET2.
      destruct xs as [|x xs]; [inversion FKS|].
      assert (Q12 : live_at L1 A1 (resolveF qd x) (key_addr k2) (Z.of_nat (length (key_text k2)) + 1) /\
                    Forall2 (fun k y => live_at L1 A1 (resolveF qd y) (key_addr k) (Z.of_nat (length (key_text k)) + 1))
                      ks2 xs)
        by (inversion FKS; split; assumption).
      destruct Q12 as [Q1 Q2].
      constructor; [cbv beta; rewrite EA1, ET1; exact Q1 | exact (IH ks2 xs EA2 ET2 Q2)]. }
  pose proof HI1 as (H1 & H2 & J & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _).
  assert (PS0 : pstream s = []) by (unfold pstream; rewrite PE; reflexivity).
  rewrite PS0, app_nil_r in H1. subst D.
  rewrite PE in L7c. pose proof (map_eq_nil _ _ L7c) as RN.
  assert (OF0 : hs_off h1 = 0)
    by (destruct S8 as [(_ & O0)|(r & rs & RE & _)]; [exact O0 | rewrite RN in RE; discriminate]).
  assert (SKP : re_skip e1 = hs_overlong h1).
  { destruct J as (JK & _). rewrite L3c, JK, <- L9c. unfold hs_state. cbn [ls_k].
    destruct S10 as [E|E]; rewrite E; reflexivity. }
  pose (e2 := RE (re_fd e1) EOF (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1)
                 (re_pad2 e1) ks' (re_U e1) (re_junk e1)).
  assert (EBk : entry_blocks e2 = entry_blocks e1)
    by (unfold e2, entry_blocks; cbn [re_cap re_buf re_hp re_keys]; rewrite KA; reflexivity).
  assert (EB : entry_bytes e2 = entry_bytes (RE (re_fd e1) EOF (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1)
    (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1) (re_U e1) (re_junk e1))).
  { unfold e2, entry_bytes, re_nheld. cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 re_keys].
    rewrite KL. reflexivity. }
  assert (OC : LIVE = true -> 0 < ds_ocap s).
  { intros LV. destruct OU1 as (_ & OT). destruct (OT LV) as (_ & [(Z0 & _ & N0 & _)|(Cp & _)]); [|exact Cp].
    exfalso. pose proof (bv_unsigned_in_range 64 nout) as NR.
    assert (TP : 0 < TOT).
    { destruct (Z.eq_dec TOT 0) as [Z1|Z1]; [|lia]. unfold send_live, send_off in LV.
      rewrite Z1, Z.eqb_refl, orb_true_r in LV. discriminate. }
    unfold dtot in H7. lia. }
  unfold DPOST. rewrite <- TA, <- TF, <- TE.
  exists L1, A1, R2, m2, md1, e2, h1, OUT1, (ds_ocap s), junk1, LB1.
  split; [reflexivity|].
  split.
  { destruct RP2 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _ & P11 & P12 & P13 & P14).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact PRS|].
    split; [exact P11|]. split; [exact P12|]. split; [exact P13 | exact P14]. }
  split; [exact IN1|].
  split.
  { exists qd. split; [exact RQ|]. split; [exact RS|].
    split; [intros LV; exact (LO LV (OC LV))|].
    split; [|exact LS].
    destruct LE as (LB0 & LH0 & LK0). split; [exact LB0|]. split; [exact LH0|].
    exact (FT ks' (re_keys e1) (da_keys ad) KA KT LK0). }
  split; [exact RO2|].
  split; [rewrite EB; exact SAC2|].
  split.
  { pose proof EK2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _).
    unfold e2, entry_ok, re_nheld in *.
    cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
    split; [exact HE01|]. do 9 (split; [assumption|]).
    split; [rewrite KL; exact E11|].
    split.
    { destruct E12 as [(H0 & K0)|(HI & HF & H8a & H8b & HB)].
      - left. split; [exact H0|]. apply length_zero_iff_nil. rewrite KL, K0. reflexivity.
      - right. rewrite KL, KP. split; [exact HI|]. split; [exact HF|]. split; [exact H8a|].
        split; [exact H8b | exact HB]. }
    split; [rewrite KA; exact E13|]. split; [rewrite KT; exact E14 | exact KF]. }
  split.
  { rewrite <- (hs_eset_id h1). apply SRC2; [|exact S3].
    eapply rw_tr; [exact (msame_munch _ _ _ MU WM) | exact S1 |]. intros a Ha. cbn [cells_size csize] in Ha.
    cbv beta. split; [unfold G_S, SRC_SIZE in *; lia | apply HAW; lia]. }
  split; [exact OT2|].
  split; [exact D1|].
  split; [exact HEOF|].
  split; [change (0 < re_cap e1); rewrite L1c; unfold ulen in GR; lia|].
  split; [exact L1c|]. split; [exact L2c|]. split; [exact L3c|].
  split; [change (keys_texts ks' = ds_H s); rewrite KX; exact L4c|].
  split; [exact L5c|]. split; [exact L11c|]. split; [exact KH|]. split; [exact H6|].
  split; [exact D3|]. split; [exact D5|]. split; [rewrite L6c, EI; reflexivity|].
  split; [exact RN|]. split; [exact OF0|]. split; [exact D6|]. split; [exact D7|]. split; [exact D8|].
  split; [rewrite L9c; exact H2|]. split; [exact H4|]. split; [exact H5|]. split; [exact D9|].
  split; [exact SKP|].
  split.
  { change (re_skip e1 = 0 -> bzs (re_U e1) = bzs (hs_W h1)). intros Z0. destruct J as (_ & JW & _).
    rewrite L2c, JW; [rewrite <- L9c; reflexivity|].
    destruct (ds_skip s) eqn:SK; [try rewrite SK in L3c; rewrite L3c in Z0; discriminate | reflexivity]. }
  split; [change (NoDup (keys_texts ks')); rewrite KX, L4c; exact H9|].
  split; [change (same_set (keys_texts ks') (upds (keys_texts (re_keys e)) LS0)); rewrite KX, L4c; exact H10|].
  split; [rewrite EBk; exact ND1|].
  split; [exact GI1|].
  split; [exact SV1|].
  split; [rewrite EBk; exact CL1|].
  split; [rewrite EBk; exact FB1|].
  destruct GL2 as (C1 & C2 & C3 & C4' & C5).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4'|]. split; [exact C5|].
  split; [exact H8|].
  split.
  { intros LV. destruct OU2 as (OF & _). destruct (OF LV) as (C & EO & _ & OB). split; [exact C|].
    split; [exact OB | exact EO]. }
  intros LV. destruct OU2 as (_ & OT). destruct (OT LV) as (C & [(Z0 & _ & N0 & _)|(Cp & NL & OI & OFr & OBy & LJ)]).
  - exfalso. pose proof (bv_unsigned_in_range 64 nout) as NR.
    assert (TP : 0 < TOT).
    { destruct (Z.eq_dec TOT 0) as [Z1|Z1]; [|lia]. unfold send_live, send_off in LV.
      rewrite Z1, Z.eqb_refl, orb_true_r in LV. discriminate. }
    unfold dtot in H7. lia.
  - rewrite H7 in C. unfold dtot in H7.
    split; [lia|]. split; [reflexivity|]. split; [exact OI|]. split; [exact OFr|].
    split; [exact OBy|]. split; [lia | exact C].
Qed.

Lemma nb_of : forall OUT1 e1 h1 q, NoDup (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) ->
  (q = G \/ q = OUT1 \/ In q (hs_blocks h1) \/ q = re_hp e1 \/ In q (map key_addr (re_keys e1))) -> q <> 0 ->
  re_cap e1 = 0 \/ q <> re_buf e1.
Proof using.
  intros OUT1 e1 h1 q ND Hq Q0. destruct (Z.eq_dec (re_cap e1) 0) as [C|C]; [left; exact C|right]. intros E. subst q.
  unfold entry_blocks in ND. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) C) in ND.
  apply NoDup_ListNoDup in ND. cbn [app] in ND.
  apply List.NoDup_cons_iff in ND as [NG ND]. apply List.NoDup_cons_iff in ND as [NO ND].
  apply List.NoDup_cons_iff in ND as [NB _].
  destruct Hq as [E|[E|[E|[E|E]]]].
  - apply NG. right. left. exact E.
  - apply NO. left. exact E.
  - apply NB. apply in_or_app. right. exact E.
  - apply NB. apply in_or_app. left. apply in_or_app. left.
    rewrite <- E, (proj2 (Z.eqb_neq (re_buf e1) 0) Q0). left. reflexivity.
  - apply NB. apply in_or_app. left. apply in_or_app. right. exact E.
Qed.

Ltac glia :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?P -> ?Q |- _ =>
             lazymatch type of P with
             | Prop => lazymatch Q with False => fail | _ => clear H end
             end
         end;
  lia.

Definition RLT (b : rt_R F) (cap0 buf0 n : Z) (p0 : sptr) (old : list byte) (L1 : layout) (A1 : astate)
    (R1 : bvmap 5 word) (m1 : word -> option byte) (md1 : Model) (c' : config) : Prop :=
  exists L2 A2 regs2 mem2 md2 res q,
    c' = mkCfg (YK11.mkst regs2 (getr R1 1) mem2 (seg_rom segs)) md2 /\
    relay_post Bm API REALLOC_STACK (fun a => buf0 <= a < buf0 + cap0) (fun z => z = buf0)
      L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 /\
    getr regs2 10 = Z_to_bv 64 res /\ res <> 0 /\ fresh_block Bm res n /\
    (exists b1 b2 c1 c2, blocks L2 A2 = c1 ++ (res, n) :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
       ((cap0 = 0 /\ blocks L1 A1 = b1 ++ b2) \/ (0 < cap0 /\ blocks L1 A1 = b1 ++ (buf0, cap0) :: b2))) /\
    ro_agree segs mem2 /\ bytes_at segs mem2 res old /\ st_init_done A2 = true /\
    live_at L2 A2 q res n /\
    (forall p x k, live_at L1 A1 p x k -> (cap0 = 0 \/ x <> buf0) -> live_at L2 A2 p x k) /\
    rt_ok F A2 (if cap0 =? 0 then rt_malloc F b n else rt_realloc F b cap0 n p0 q).

Lemma UG_rlt_ra : forall L1 A1 R1 m1 md1 b cap0 buf0 n old p0,
  call_pre_k Bm MR REALLOC_STACK L1 A1 R1 m1 md1 -> ro_agree segs m1 ->
  0 < cap0 -> live_at L1 A1 p0 buf0 cap0 ->
  getr R1 10 = Z_to_bv 64 buf0 -> getr R1 11 = Z_to_bv 64 n -> cap0 <= n ->
  bytes_at segs m1 buf0 old -> Z.of_nat (length old) = cap0 ->
  rt_ok F A1 b -> rt_room F b n ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x178f8) m1 (seg_rom segs)) md1)
    (RLT b cap0 buf0 n p0 old L1 A1 R1 m1 md1).
Proof using All.
  intros L1 A1 R1 m1 md1 b cap0 buf0 n old p0 PRE1 RO1 Cp [Hp Ep] E10 E11 LE OB LOLD RES ROOMn.
  pose proof PRE1 as (HM1 & HW1 & _).
  assert (A10 : getr R1 10 = Z_to_bv 64 (ptr_addr L1 p0)) by (rewrite Ep; exact E10).
  assert (AOLD : forall i, 0 <= i < cap0 -> mbyte segs m1 (ptr_addr L1 p0 + i) = nth_error old (Z.to_nat i)).
  { intros i Hi. rewrite Ep. pose proof (mbyte_of_bytes_at segs m1 _ _ (Z.to_nat i) OB ltac:(lia)) as X.
    rewrite Z2Nat.id in X by lia. exact X. }
  eapply SR_mono; [exact (RAC L1 A1 R1 m1 md1 p0 cap0 n old b PRE1 RO1 Hp A10 E11 AOLD LOLD RES ROOMn)|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & A0 & NZ & AL & FR & BLK & KEPT & RO2 & GK & SURV & CPY
             & INI2 & LN & q & Hq & Eq & RES2).
  exists L2, A2, regs2, mem2, md2, res, q. split; [reflexivity|].
  split.
  { pose proof (sb_realloc_rp Bm API AX CTX L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 p0 cap0 HW1 Hp Cp HM1 CP SURV LN)
      as RP. rewrite Ep in RP. exact RP. }
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split.
  { destruct BLK as (b1 & b2 & c1 & c2 & E1 & E2 & E3). rewrite Ep in E1.
    exists b1, b2, c1, c2. split; [exact E2|]. split; [exact E3|]. right. split; [exact Cp | exact E1]. }
  split; [exact RO2|].
  split.
  { pose proof FR as (FR1 & FR2 & _). pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    apply bytes_at_of_mbyte; [clear - FR1; lia | clear - FR1 FR2 ACL LOLD LE; lia |].
    intros i Hi. rewrite (CPY (Z.of_nat i) ltac:(clear - Hi LOLD LE; lia)). rewrite Nat2Z.id. reflexivity. }
  split; [exact INI2|].
  split; [split; [exact Hq | exact Eq]|].
  split.
  { intros p x k [Hpk Epx] Hx.
    assert (NP : p <> p0).
    { intros E. subst p. destruct Hx as [Hx|Hx]; [clear - Hx Cp; lia|]. apply Hx. rewrite <- Epx. exact Ep. }
    pose proof (SURV p k Hpk NP) as Hpk2. split; [exact Hpk2|].
    pose proof CP as (_ & _ & _ & _ & AD & _). rewrite (AD p k Hpk Hpk2). exact Epx. }
  rewrite (proj2 (Z.eqb_neq cap0 0)) by lia. exact RES2.
Qed.

Lemma UG_rlt_rn : forall L1 A1 R1 m1 md1 b n p0,
  call_pre_k Bm MR REALLOC_STACK L1 A1 R1 m1 md1 -> ro_agree segs m1 ->
  getr R1 10 = Z_to_bv 64 0 -> getr R1 11 = Z_to_bv 64 n -> 0 <= n ->
  getr R1 1 <> Z_to_bv 64 (ms_malloc Bm) ->
  rt_ok F A1 b -> rt_room F b n ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x178f8) m1 (seg_rom segs)) md1) (RLT b 0 0 n p0 [] L1 A1 R1 m1 md1).
Proof using All.
  intros L1 A1 R1 m1 md1 b n p0 PRE1 RO1 E10 E11 N0 RNM RES ROOMn.
  pose proof PRE1 as (HM1 & _).
  eapply SR_mono; [exact (RNC L1 A1 R1 m1 md1 n b PRE1 RO1 E10 E11 RNM RES ROOMn)|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & A0 & NZ & AL & FR & (b1 & b2 & E1 & E2) & KEPT & RO2
             & GK & SURV & INI2 & LN & RES2).
  pose proof CP as (M2 & _).
  assert (IN2 : In (res, n) (blocks L2 A2)) by (rewrite E1; apply in_or_app; right; left; reflexivity).
  destruct (sptr_of_spec L2 A2 res n (NODUP _ _ _ _ M2) IN2) as (Hq & Eq).
  exists L2, A2, regs2, mem2, md2, res, (sptr_of L2 A2 res). split; [reflexivity|].
  split.
  { apply (rp_mono _ (fun _ => False) _ (fun _ => False));
      [exact (sb_null_rp Bm API AX CTX L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 HM1 CP SURV LN)
      | intros a [] | intros z []]. }
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split; [exists b1, b2, b1, b2; split; [exact E1|]; split; [reflexivity|]; left; split; [reflexivity | exact E2]|].
  split; [exact RO2|].
  pose proof FR as (FR1 & FR2 & _). pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  split; [split; [clear - FR1; lia|]; split; [cbn; clear - FR1 FR2 ACL N0; lia|]; intros i Hi; cbn in Hi; lia|].
  split; [exact INI2|].
  split; [split; [exact Hq | exact Eq]|].
  split.
  { intros p x k [Hpk Epx] _. pose proof (SURV p k Hpk) as Hpk2. split; [exact Hpk2|].
    pose proof CP as (_ & _ & _ & _ & AD & _). rewrite (AD p k Hpk Hpk2). exact Epx. }
  exact RES2.
Qed.

Lemma gr_lv : forall L1 A1 p x n, live_at L1 A1 p x n -> In (x, n) (blocks L1 A1).
Proof using All.
  intros L1 A1 p x n [Hp <-]. unfold blocks. exact (in_map (fun b => (ptr_addr L1 (fst b), snd b)) _ (p, n) Hp).
Qed.

Lemma gr_f2 : forall {X : Type} (P Q : X -> adrF -> Prop) (Sa : adrF -> Prop) (xs : list X) (ys : list adrF),
  Forall Sa ys -> Forall2 P xs ys -> (forall x y, In x xs -> Sa y -> P x y -> Q x y) -> Forall2 Q xs ys.
Proof using All.
  intros X P Q Sa xs ys HS HP. revert HS. induction HP as [|x y xs' ys' Hxy HP' IH]; intros HS H; constructor.
  - apply H; [left; reflexivity | exact (Forall_inv HS) | exact Hxy].
  - apply IH; [exact (Forall_inv_tail HS)|]. intros x' y' Hx' Hy' Hp'. apply H; [right; exact Hx' | exact Hy' | exact Hp'].
Qed.

Lemma gr_src : forall L1 A1 L2 A2 (qd post : list sptr) a h1,
  (forall p x n, In x (hs_blocks h1) -> live_at L1 A1 p x n -> live_at L2 A2 p x n) ->
  p3a_ok (da_ev a) (length qd) -> Forall (fun x => p3a_ok x (length qd)) (da_pend a) ->
  Forall (fun x => p3a_ok x (length qd)) (da_erecs a) ->
  src_links L1 A1 qd (known_at L A) a h1 -> src_links L2 A2 (qd ++ post) (known_at L A) a h1.
Proof using All.
  intros L1 A1 L2 A2 qd post a h1 T Dev Dpend Derecs (S1 & S2 & S3 & (X1 & X2) & S5 & S6).
  assert (LV : forall l, (forall z, In z (list_blocks l) -> In z (hs_blocks h1)) -> 0 < hl_cap l ->
            In (hl_v l) (hs_blocks h1)).
  { intros l Hl Cp. apply Hl. unfold list_blocks. rewrite (proj2 (Z.eqb_neq (hl_cap l) 0)) by lia.
    left. reflexivity. }
  assert (LR : forall l r, (forall z, In z (list_blocks l) -> In z (hs_blocks h1)) -> In r (hl_recs l) ->
            In (fst r) (hs_blocks h1)).
  { intros l r Hl Hr. apply Hl. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr. }
  unfold src_links, expected_links.
  split; [intros Cp; exact (T _ _ _ (LV _ (hb_pend h1) Cp) (S1 Cp))|].
  split.
  { apply (gr_f2 _ _ _ _ _ Dpend S2). intros r y Hr Hy Hl. cbv beta in Hy, Hl |- *.
    rewrite (p3a_resolve_app qd post y Hy). exact (T _ _ _ (LR _ _ (hb_pend h1) Hr) Hl). }
  split; [exact (T _ _ _ (hb_part h1) S3)|].
  split.
  { split.
    - intros Cp. rewrite (p3a_resolve_app qd post _ Dev). exact (T _ _ _ (LV _ (hb_exp h1) Cp) (X1 Cp)).
    - apply (gr_f2 _ _ _ _ _ Derecs X2). intros r y Hr Hy Hl. cbv beta in Hy, Hl |- *.
      rewrite (p3a_resolve_app qd post y Hy). exact (T _ _ _ (LR _ _ (hb_exp h1) Hr) Hl). }
  split; [intros Cp; exact (T _ _ _ (LV _ (hb_held h1) Cp) (S5 Cp))|].
  apply Forall_forall. intros r Hr. exact (T _ _ _ (LR _ _ (hb_held h1) Hr) (proj1 (Forall_forall _ _) S6 r Hr)).
Qed.

Lemma UG_find_step : forall s R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
  RTK R1 -> getr R1 9 = Z_to_bv 64 (re_cap e1) -> 4096 <= ds_cap s - ulen s ->
  DC s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13960) m1 (seg_rom segs)) md1) (DF s).
Proof using EHI GEI HFD HG HJ PRE SEGS.
  intros s R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D RT1 G9 GR DC1.
  pose proof DC1 as (RP1 & _ & _ & _ & _ & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & _).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _).
  pose proof LK1 as (L1c & _).
  pose proof SR1 as (S1 & _ & _ & S4 & _).
  pose proof SM1 as (D1 & _ & D3 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & _).
  destruct (dr_cut m1 SA (SA + 4) [C4 (Z_to_bv 64 (re_fd e1))]
              [C4 (Z_to_bv 64 (re_eof e1)); C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)] EC1
              ltac:(cbn [cells_size csize]; lia)) as [EC0 _].
  destruct (dr_cut m1 (SA + 16) (SA + 32) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]
              [C8 (Z_to_bv 64 (re_cap e1))] EC2 ltac:(cbn [cells_size csize]; lia)) as [EB _].
  assert (HC : rw_cells rsegs m1 HA [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                                     C4 (Z_to_bv 64 (hs_closed h1)); C4 (Z_to_bv 64 (hs_eintr h1))])
    by (rewrite <- SEGS; exact S1).
  destruct (dr_cut m1 HA (HA + 8) [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1))]
              [C4 (Z_to_bv 64 (hs_closed h1)); C4 (Z_to_bv 64 (hs_eintr h1))] HC eq_refl) as [HC0 _].
  rewrite D3, HFD, <- D1, S4 in HC0.
  assert (UB : 0 < re_buf e1 /\ 0 <= re_used e1 /\ re_buf e1 + re_used e1 < 2 ^ 64 /\ 0 <= re_cap e1 < 2 ^ 64).
  { assert (CP : 4096 <= re_cap e1) by (rewrite L1c; unfold ulen in GR; clear - GR; lia).
    destruct K10 as [(C0 & _)|(Cp & BI & BF & BJ & BC)]; [clear - C0 CP; lia|].
    pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR. clear - K7 BJ BR F4 Cp. lia. }
  assert (OTH1 : forall i', 0 <= i' < Z.of_nat j -> exists f o,
            rw_cells rsegs m1 (DR_TU + 96 * i' + 128) [C4 (Z_to_bv 64 f); C4 (Z_to_bv 64 o)] /\
            (o = 0 \/ (0 <= f < 2 ^ 31 /\ f <> re_fd e1))).
  { intros i' Hi'. destruct OT1 as (_ & _ & O3).
    destruct (O3 (Z.to_nat i') ltac:(clear - Hi' F11; lia) ltac:(clear - Hi'; lia)) as (OC & OD & OE).
    exists (nth (Z.to_nat i') fs 0), (nth (Z.to_nat i') os 0). split.
    - rewrite <- SEGS. replace (DR_TU + 96 * i' + 128) with (G_S + SRC_SIZE * Z.of_nat (Z.to_nat i'))
        by (rewrite Z2Nat.id by lia; unfold DR_TU, G_S, SRC_SIZE; lia). exact OC.
    - rewrite D1. destruct OD as [OD|OD]; [left; exact OD | right; split; [exact OE | exact OD]]. }
  destruct RT1 as ((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G8, G9, G22, G25. rewrite SEGS.
    eapply dr_find with (j := Z.of_nat j); [exact EC0 | exact EB | clear - F11; lia | exact K5 | clear - UB; lia |
      clear - UB; lia | clear - UB; lia | clear - UB; lia | exact OTH1 |].
    replace (DR_TU + 96 * Z.of_nat j + 128) with HA by (unfold DR_TU, G_S, SRC_SIZE; lia). exact HC0. }
  intros ms (can & (x14' & ->) & EQ).
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  apply SR_ret. exists R2, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D.
  split; [reflexivity|].
  split; [unfold RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
  split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|]. split; [exact GR | exact DC1].
Qed.

Lemma grow_step : forall s c, DI s c -> SR segs c (DF (dgrow s)).
Proof using All.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RT1 & DC1).
  pose proof DC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & W1 & B1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
  assert (ULEN : ulen s = re_used e1) by (unfold ulen; rewrite <- L2c; unfold bzs; rewrite length_map; exact K7).
  assert (UC : 0 <= re_used e1 <= re_cap e1 /\ 0 <= re_buf e1 < 2 ^ 64).
  { destruct K10 as [(C0 & B0 & U0)|(Cp & BI & BF & BJ & BC)]; [clear - C0 B0 U0; lia|].
    pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR. clear - K7 BJ BR F4 Cp. lia. }
  destruct RT1 as ((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G8. rewrite SEGS.
    eapply dr_top; [exact EC2 | clear - UC; lia | clear - K6; lia]. }
  intros ms (can & (x10' & [(GE & ->)|(LT & ->)]) & EQ);
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  - assert (GR : 4096 <= ds_cap s - ulen s) by (rewrite <- L1c, ULEN; exact GE).
    rewrite (dgrow_id s GR).
    apply (UG_find_step s R2 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D); [ | rgw X2 | exact GR | exact DC1].
    unfold RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X2.
  - assert (CC : re_cap e1 = 0 \/ re_cap e1 = 8192) by (clear - K6 LT UC K8; lia).
    assert (NV : dr_grow (re_cap e1) = 8192 \/ dr_grow (re_cap e1) = 16384)
      by (unfold dr_grow; destruct CC as [C|C]; rewrite C; cbn; auto).
    assert (NL : re_cap e1 <= dr_grow (re_cap e1) /\ re_used e1 <= dr_grow (re_cap e1) /\
                 (re_cap e1 = 0 -> re_used e1 = 0))
      by (unfold dr_grow; destruct CC as [C|C]; rewrite C; cbn; clear - C UC K8; lia).
    assert (GT : forall jj bb, grow_tr (ds_cap s) (ulen s) jj bb =
                 ([if re_cap e1 =? 0 then RMalloc (dr_grow (re_cap e1))
                   else RRealloc (re_cap e1) (dr_grow (re_cap e1)) bb], (dr_grow (re_cap e1), Ret jj))).
    { intros jj bb. rewrite <- L1c, ULEN. unfold grow_tr, dr_grow. rewrite (proj2 (Z.ltb_lt _ _) LT). reflexivity. }
    destruct TR1 as (tp & qd & ad & (RQ & WF0 & DOK & RS1 & (LKo & (LKb & LKh & LKk) & LKs) & KH) & TE1 & TF1 & TA1).
    destruct DOK as (Dout & Dbuf & Dhp & Dkeys & Dpend & Dev & Derecs).
    rewrite <- RQ in Dout, Dbuf, Dhp, Dkeys, Dpend, Dev, Derecs.
    remember (if re_cap e1 =? 0 then RMalloc (dr_grow (re_cap e1))
              else RRealloc (re_cap e1) (dr_grow (re_cap e1)) (da_buf ad)) as ev eqn:Hev.
    assert (GTa : grow_tr (ds_cap s) (ulen s) (nretF tp) (da_buf ad) = ([ev], (dr_grow (re_cap e1), Ret (nretF tp))))
      by (rewrite GT, Hev; reflexivity).
    assert (NE1 : nretF [ev] = 1%nat) by (rewrite Hev; destruct (re_cap e1 =? 0); reflexivity).
    assert (GR2 : 4096 <= ds_cap (dgrow s) - ulen (dgrow s)).
    { change (4096 <= gcap (ds_cap s) (ulen s) - ulen s). unfold gcap. rewrite GT. cbn [fst snd]. rewrite ULEN.
      unfold dr_grow. destruct CC as [C|C]; rewrite C; cbn; clear - C K8 UC; lia. }
    pose proof (drun_grow (length (pstream s) + Nat.b2n (ds_eintr s)) LIVE MX s (nretF tp) ad GR2) as DN.
    change (S (length (pstream s) + Nat.b2n (ds_eintr s))) with (dneed s) in DN.
    rewrite DN, GTa in TE1, TF1, TA1. cbn [fst snd] in TE1, TF1, TA1. rewrite NE1 in TE1, TF1, TA1.
    assert (TE2 : tp ++ ev :: fst (drun (dneed s) LIVE MX (dgrow s) (nretF tp + 1)%nat (agrow s (nretF tp) ad)) = TR)
      by exact TE1.
    assert (RMn : rt_room F (runF F qd bnd tp) (dr_grow (re_cap e1))).
    { apply (p3a_room_next F qd bnd tp ev (fst (drun (dneed s) LIVE MX (dgrow s) (nretF tp + 1)%nat (agrow s (nretF tp) ad))));
        [exact WF0 | symmetry; exact RQ | rewrite TE2; exact ROOM |].
      rewrite Hev. destruct (re_cap e1 =? 0); [left; reflexivity | right; exists (re_cap e1), (da_buf ad); reflexivity]. }
    assert (PRE2 : call_pre_k Bm MR REALLOC_STACK L1 A1 R2 m1 md1).
    { apply (pre_realloc L1 A1 m1 md1 R2 RP1 IN1); [rgw X2 | rgw X2 |].
      rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. exact ret_ok_13954. }
    assert (RLc : SR segs (mkCfg (YK11.mkst R2 (Z_to_bv 64 0x178f8) m1 (seg_rom segs)) md1)
              (RLT (runF F qd bnd tp) (re_cap e1) (re_buf e1) (dr_grow (re_cap e1)) (resolveF qd (da_buf ad))
                  (if re_cap e1 =? 0 then [] else re_U e1 ++ re_junk e1) L1 A1 R2 m1 md1)).
    { destruct K10 as [(C0 & B0 & U0)|(Cp & BI & BF & BJ & BC)].
      - rewrite C0, B0 in *. cbn [Z.eqb].
        apply UG_rlt_rn; [exact PRE2 | exact RO1 | rgw X2 | rgw X2 | clear - NV; lia | | exact RS1 | exact RMn].
        rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. rewrite MALPC.
        intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate.
      - rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by (clear - Cp; lia). cbv iota.
        apply UG_rlt_ra; [exact PRE2 | exact RO1 | exact Cp | exact (LKb Cp) | rgw X2 | rgw X2 | clear - NL; lia | |
                       | exact RS1 | exact RMn].
        + destruct BC as [[_ BB] _]. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB. exact BB.
        + rewrite length_app, Nat2Z.inj_add, K7, BJ. ring. }
    eapply SR_bind; [exact RLc|].
    intros c' (L2 & A2 & regs2 & mem2 & md2 & res & qn & -> & RP2 & G10' & NZ & FRES & BLK & RO2 & OB2 & IN2 & LQn
               & KEEP & RS2).
    pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & PR2 & _ & _ & _ & SC2).
    destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
    destruct BLK as (b1 & b2 & c1 & c2 & EB2 & EC12 & EB1).
    pose proof BK1 as (ND1 & GI1 & SV1 & CL1 & FB1).
    pose proof HI1 as (_ & _ & _ & _ & _ & _ & H7 & H8 & _).
    pose proof pre_facts as (HM0 & _ & _ & _ & _ & HCEIL & H63 & _ & _ & _).
    pose proof err_hi as EH. unfold G_LOCK_HI in F9.
    pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    pose proof FRES as (FR1r & FR2r & FR3r).
    assert (SPR2 : spZ R2 = S0 - 144).
    { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity.
      simp_regs. rewrite G2. apply unsigned_lit. glia. }
    assert (NDB1 : List.NoDup (map fst (blocks L1 A1))) by (apply NoDup_ListNoDup; exact (NODUP _ _ _ _ M1)).
    assert (NDB2 : List.NoDup (map fst (blocks L2 A2))) by (apply NoDup_ListNoDup; exact (NODUP _ _ _ _ M2)).
    assert (ENI : forall a, re_buf e1 <= a < re_buf e1 + re_cap e1 ->
              a < YM05.alloc_ceiling /\ ~ in_img Bm a /\ 0 < re_cap e1).
    { intros a Ha. destruct K10 as [(C0 & B0 & U0)|(Cp & BI & (BF1 & BF2 & BF3) & BJ & BC)]; [exfalso; glia|].
      split; [glia|]. split; [|exact Cp]. replace a with (re_buf e1 + (a - re_buf e1)) by ring. apply BF3. glia. }
    assert (EDJ : forall q k a, In (q, k) (blocks L1 A1) -> (re_cap e1 = 0 \/ q <> re_buf e1) -> q <= a < q + k ->
              ~ (re_buf e1 <= a < re_buf e1 + re_cap e1)).
    { intros q k a Hq Hn Ha. destruct Hn as [C|C]; [glia|].
      destruct K10 as [(C0 & _)|(Cp & BI & _)]; [glia|].
      pose proof (blocks_disjoint Bm API _ _ _ _ q k (re_buf e1) (re_cap e1) M1 Hq BI C) as DJ. clear - DJ Ha. lia. }
    assert (NBNE : forall q k, In (q, k) (blocks L1 A1) -> (re_cap e1 = 0 \/ q <> re_buf e1) -> q <> re_buf e1).
    { intros q k Hq Hn E. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR. destruct Hn as [Hn|Hn]; [|exact (Hn E)].
      destruct K10 as [(_ & B0 & _)|(Cp & _)]; glia. }
    assert (NBG : re_cap e1 = 0 \/ G <> re_buf e1) by (apply (nb_of OUT1 e1 h1 G ND1); [left; reflexivity | clear - F5; lia]).
    assert (SURV : forall q k, In (q, k) (blocks L1 A1) -> (re_cap e1 = 0 \/ q <> re_buf e1) ->
              In (q, k) (blocks L2 A2) /\ q <> res).
    { intros q k Hq Hn. assert (Hc : In (q, k) (c1 ++ c2)).
      { rewrite EC12. destruct EB1 as [(_ & E)|(Cp0 & E)]; rewrite E in Hq; [exact Hq|].
        apply in_app_or in Hq as [Hq|[Hq|Hq]]; [apply in_or_app; left; exact Hq | | apply in_or_app; right; exact Hq].
        injection Hq as <- <-. destruct Hn as [Hn|Hn]; [exfalso; glia | congruence]. }
      split; [rewrite EB2; apply in_app_or in Hc as [Hc|Hc]; apply in_or_app; [left; exact Hc | right; right; exact Hc]|].
      intros ->. rewrite EB2, map_app in NDB2. cbn [map fst] in NDB2. apply NoDup_remove_2 in NDB2. apply NDB2.
      rewrite <- map_app. change res with (fst (res, k)). apply in_map. exact Hc. }
    assert (BACK : forall q k, In (q, k) (blocks L2 A2) -> (q = res /\ k = dr_grow (re_cap e1)) \/
              (In (q, k) (blocks L1 A1) /\ (re_cap e1 = 0 \/ q <> re_buf e1))).
    { intros q k Hq. rewrite EB2 in Hq. apply in_app_or in Hq as [Hq|[Hq|Hq]].
      2: { left. injection Hq as <- <-. split; reflexivity. }
      all: assert (Hb : In (q, k) (b1 ++ b2)) by (rewrite <- EC12; apply in_or_app; first [left; exact Hq | right; exact Hq]).
      all: right; destruct EB1 as [(C0 & E)|(Cp0 & E)]; [rewrite E; split; [exact Hb | left; exact C0]|].
      all: rewrite E in NDB1 |- *; split;
             [apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb]|].
      all: right; intros ->; rewrite map_app in NDB1; cbn [map fst] in NDB1; apply NoDup_remove_2 in NDB1; apply NDB1;
             rewrite <- map_app; change (re_buf e1) with (fst (re_buf e1, k)); apply in_map; exact Hb. }
    assert (GI2 : In (G, SRC_TABLE) (blocks L2 A2)) by exact (proj1 (SURV G SRC_TABLE GI1 NBG)).
    assert (INres : In (res, dr_grow (re_cap e1)) (blocks L2 A2))
      by (rewrite EB2; apply in_or_app; right; left; reflexivity).
    assert (DJres : res + dr_grow (re_cap e1) <= G \/ G + SRC_TABLE <= res).
    { apply (blocks_disjoint Bm API _ _ _ _ res _ G SRC_TABLE M2 INres GI2).
      intros E. exact (proj2 (SURV G SRC_TABLE GI1 NBG) (eq_sym E)). }
    pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as MS2.
    match type of MS2 with msame ?P _ _ => set (P2 := P) in MS2 end.
    assert (P2S : forall a, S0 - 144 <= a < S0 -> P2 a).
    { intros a Ha. unfold P2. cbv beta. left.
      split; [left; glia|]. split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M1 Ho); glia|].
      split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M2 Ho); glia|].
      split; [unfold scratch_k; rewrite SPR2; unfold REALLOC_STACK, ALLOC_STACK; glia|].
      intros Ea. pose proof (ENI a Ea) as (EA & _). glia. }
    assert (P2I : forall a, img_plain Bm a -> P2 a).
    { intros a Hp. pose proof Hp as (Im & _ & _ & NE). pose proof (img_lo a Im) as IL. unfold P2. cbv beta. left.
      split; [right; exact Im|]. split; [exact (img_unowned _ _ _ _ a M1 Hp)|].
      split; [exact (img_unowned _ _ _ _ a M2 Hp)|].
      split; [unfold scratch_k; rewrite SPR2; unfold REALLOC_STACK, ALLOC_STACK; glia|].
      intros Ea. exact (proj1 (proj2 (ENI a Ea)) Im). }
    assert (P2B : forall q k a, In (q, k) (blocks L1 A1) -> (re_cap e1 = 0 \/ q <> re_buf e1) -> q <= a < q + k ->
              P2 a).
    { intros q k a Hq Hn Ha. unfold P2. cbv beta. right. exists q, k.
      split; [exact Hq|]. split; [glia|]. split; [exact (NBNE q k Hq Hn)|]. split; [glia|]. exact (EDJ q k a Hq Hn Ha). }
    assert (EC2' : rw_cells rsegs mem2 (SA + 16)
              [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1)); C8 (Z_to_bv 64 (re_cap e1))]).
    { rewrite <- SEGS in EC2 |- *. apply (rw_tr _ _ _ _ _ MS2 EC2). intros a Ha. cbn [cells_size csize] in Ha.
      apply (P2B G SRC_TABLE a GI1 NBG). unfold SRC_TABLE, SRC_ENTRY in *. glia. }
    assert (G1' : getr R2 1 = Z_to_bv 64 0x13954) by rgw X2.
    assert (Q8 : getr regs2 8 = Z_to_bv 64 SA)
      by (transitivity (getr R2 8); [exact (PR2 8 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q9 : getr regs2 9 = Z_to_bv 64 (dr_grow (re_cap e1)))
      by (transitivity (getr R2 9); [exact (PR2 9 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q2 : getr regs2 2 = Z_to_bv 64 (S0 - 144))
      by (transitivity (getr R2 2); [exact (PR2 2 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q3 : getr regs2 3 = getr regs 3)
      by (transitivity (getr R2 3); [exact (PR2 3 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q4 : getr regs2 4 = getr regs 4)
      by (transitivity (getr R2 4); [exact (PR2 4 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q22 : getr regs2 22 = Z_to_bv 64 384)
      by (transitivity (getr R2 22); [exact (PR2 22 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q23 : getr regs2 23 = Z_to_bv 64 9)
      by (transitivity (getr R2 23); [exact (PR2 23 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q25 : getr regs2 25 = Z_to_bv 64 DR_TU)
      by (transitivity (getr R2 25); [exact (PR2 25 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (Q26 : getr regs2 26 = Z_to_bv 64 4)
      by (transitivity (getr R2 26); [exact (PR2 26 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    rewrite G1'.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Q8, Q9, G10'. rewrite SEGS.
      eapply dr_regrow; [exact EC2' | glia]. }
    intros ms3 (can3 & (m3 & -> & MU3 & WM3r & HC3) & EQ3).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    assert (WM3 : wmono segs mem2 m3) by (rewrite SEGS; exact WM3r).
    pose proof (msame_trans _ _ _ _ _ MS2 (msame_munch _ _ _ MU3 WM3)) as MS.
    match type of MS with msame ?P _ _ => set (Pa := P) in MS end.
    assert (PS : forall a, S0 - 144 <= a < S0 -> Pa a).
    { intros a Ha. unfold Pa. cbv beta. split; [exact (P2S a Ha)|]. split; [glia|]. cbn [outside]. split; [glia | exact I]. }
    assert (PI : forall a, img_plain Bm a -> Pa a).
    { intros a Hp. unfold Pa. cbv beta. pose proof Hp as (Im & _). pose proof (img_lo a Im) as IL.
      split; [exact (P2I a Hp)|]. split; [glia|]. cbn [outside]. split; [intros R; exact (g_noimg a ltac:(glia) Im) | exact I]. }
    assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> (re_cap e1 = 0 \/ q <> re_buf e1) -> q <> G ->
              q <= a < q + k -> Pa a).
    { intros q k a Hq Hn NG Ha. unfold Pa. cbv beta. split; [exact (P2B q k a Hq Hn Ha)|].
      pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
      pose proof (blocks_disjoint Bm API _ _ _ _ q k G SRC_TABLE M1 Hq GI1 NG) as DJ.
      split; [glia|]. cbn [outside].
      split; [destruct DJ as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia | exact I]. }
    assert (PG : forall a, SA <= a < SA + 56 -> ~ (SA + 16 <= a < SA + 40) -> Pa a).
    { intros a Ha Hn. unfold Pa. cbv beta.
      split; [apply (P2B G SRC_TABLE a GI1 NBG); unfold SRC_TABLE, SRC_ENTRY in *; glia|].
      split; [glia|]. cbn [outside]. split; [glia | exact I]. }
    assert (TPr : forall c cs, rw_cells rsegs m1 c cs -> (forall a, c <= a < c + Z.of_nat (cells_size cs) -> Pa a) ->
              rw_cells rsegs m3 c cs).
    { intros c cs H HP. rewrite <- SEGS in H |- *. exact (rw_tr _ _ _ c cs MS H HP). }
    assert (OBU : bytes_at segs mem2 res (re_U e1)).
    { destruct K10 as [(C0 & B0 & U0)|(Cp & _)].
      - assert (UE : re_U e1 = []) by (apply length_zero_iff_nil; glia). rewrite UE. rewrite C0 in OB2. exact OB2.
      - rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) in OB2 by glia. cbv iota in OB2.
        apply bytes_at_app in OB2 as [OB2 _]. exact OB2. }
    assert (OBU3 : bytes_at segs m3 res (re_U e1)).
    { eapply by_tr; [exact (msame_munch _ _ _ MU3 WM3) | exact OBU |]. intros a Ha. cbv beta.
      rewrite K7 in Ha. split; [glia|]. cbn [outside].
      split; [destruct DJres as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia | exact I]. }
    assert (WR3 : forall i, 0 <= i < dr_grow (re_cap e1) -> writable_at rsegs m3 (res + i)).
    { intros i Hi. rewrite <- SEGS. exact (WM3 _ (BW _ _ _ _ res _ i M2 INres Hi)). }
    destruct (CF.gestures_end_b.bytes_of_mbytes rsegs m3 (res + re_used e1) (Z.to_nat (dr_grow (re_cap e1) - re_used e1)))
      as (junk2 & LJ2 & BJ2).
    { glia. }
    { glia. }
    { intros i Hi. apply CF.gestures_end_b.writable_mbyte. replace (res + re_used e1 + i) with (res + (re_used e1 + i)) by ring.
      apply WR3. glia. }
    assert (RC3 : rw_cells segs m3 res [CB (Z.to_nat (dr_grow (re_cap e1))) (re_U e1 ++ junk2)]).
    { rewrite SEGS. split; [split|].
      - cbn [cells_wf cell_wf]. split; [rewrite length_app; glia | exact I].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [rewrite <- SEGS; exact OBU3|].
        rewrite K7. exact BJ2.
      - split; [glia|]. split; [cbn [cells_size csize]; glia|]. intros i Hi. cbn [cells_size csize] in Hi. apply WR3. glia. }
    assert (LIVEQ : forall q, (q = G \/ q = OUT1 \/
                               In q ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1)) \/
                               In q (hs_blocks h1)) ->
              q = 0 \/ exists k, In (q, k) (blocks L1 A1) /\ (re_cap e1 = 0 \/ q <> re_buf e1)).
    { intros q Hq.
      assert (LQ : q = 0 \/ exists k, In (q, k) (blocks L1 A1)).
      { destruct Hq as [->|[->|[Hq|Hq]]].
        - right. exists SRC_TABLE. exact GI1.
        - destruct OU1 as (OF & OT). destruct (Bool.bool_dec LIVE true) as [LV|LV].
          + destruct (OT LV) as (_ & [(_ & O0 & _)|(_ & _ & OI & _)]); [left; exact O0 | right; eexists; exact OI].
          + apply Bool.not_true_is_false in LV. destruct (OF LV) as (_ & EO & _ & OB).
            destruct OUTD as [(C0 & O0 & _)|(Cp & _)]; [left; rewrite EO; exact O0|].
            right. exists CAP. rewrite EO. exact (proj1 (OB Cp)).
        - right. apply (eb_live L1 A1 m1 e1 q EK1). unfold entry_blocks. apply in_or_app. right. exact Hq.
        - right. exact (hb_live L1 A1 m1 HA h1 q SR1 Hq). }
      destruct LQ as [Q0|(k & Hk)]; [left; exact Q0 | right; exists k; split; [exact Hk|]].
      pose proof (blk_rng _ _ _ _ _ _ M1 Hk) as BR.
      apply (nb_of OUT1 e1 h1 q ND1); [|glia].
      destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [left; exact Hq | right; left; exact Hq | | right; right; left; exact Hq].
      apply in_app_or in Hq as [Hq|Hq]; [|right; right; right; right; exact Hq].
      revert Hq. destruct (re_hp e1 =? 0); intros Hq;
        [destruct Hq | destruct Hq as [Hq|[]]; right; right; right; left; symmetry; exact Hq]. }
    assert (NBK : forall q k, In (q, k) (blocks L1 A1) -> (q = re_hp e1 \/ In q (map key_addr (re_keys e1))) ->
              re_cap e1 = 0 \/ q <> re_buf e1).
    { intros q k Hq Hk. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
      apply (nb_of OUT1 e1 h1 q ND1); [|glia].
      destruct Hk as [Hk|Hk]; [right; right; right; left; exact Hk | right; right; right; right; exact Hk]. }
    assert (NGK : forall q k, In (q, k) (blocks L1 A1) -> (q = re_hp e1 \/ In q (map key_addr (re_keys e1))) -> q <> G).
    { intros q k Hq Hk. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
      apply (dx_ng OUT1 (entry_blocks e1 ++ hs_blocks h1) q ND1). right. apply in_or_app. left.
      unfold entry_blocks. apply in_or_app. right. destruct Hk as [Hk|Hk]; apply in_or_app; [left | right; exact Hk].
      rewrite <- Hk, (proj2 (Z.eqb_neq q 0)) by glia. left. reflexivity. }
    assert (NBH : forall q k, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> re_cap e1 = 0 \/ q <> re_buf e1).
    { intros q k Hq Hb. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
      apply (nb_of OUT1 e1 h1 q ND1); [right; right; left; exact Hb | glia]. }
    assert (NGH : forall q, In q (hs_blocks h1) -> q <> G)
      by (intros q Hb; apply (dx_ng OUT1 _ q ND1); right; apply in_or_app; right; exact Hb).
    assert (LO : Z.of_nat (length O) = NO)
      by (destruct OUTD as [(_ & _ & N0 & EO)|(_ & _ & _ & _ & _ & LO & _)]; [rewrite EO; cbn; clear - N0; lia | exact LO]).
    apply (UG_find_step (dgrow s) R3 L2 A2 m3 md2
      (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) res (re_used e1) (dr_grow (re_cap e1)) (re_hp e1) (re_kh e1)
          (re_pad2 e1) (re_keys e1) (re_U e1) junk2) h1 OUT1 junk1 LB1 D).
    { unfold RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X3. }
    { rgw X3. }
    { exact GR2. }
    split.
    { assert (RPc : relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 regs mem2 md2).
      { eapply (sb_comp Bm API).
        all: try first [exact AX | exact CTX | exact EU | exact BW | exact SEGS | exact RP1 | exact RP2].
        - intros a Ha. change (spZ regs) with S0 in Ha.
          unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. glia.
        - intros a [X|X]; [left|right; exact X]. rewrite SPR2 in X. change (spZ regs) with S0.
          unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *. glia.
        - intros a Hs _ Ea. cbv beta in Ea. pose proof (ENI a Ea) as (EA & ENI' & _).
          destruct Hs as [Hs|Hs]; [change (spZ regs) with S0 in Hs | exact (ENI' (GEI a Hs))].
          unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Hs. glia.
        - intros p n Hp _ Hn NF Eq. cbv beta in Eq.
          assert (INq : In (ptr_addr L p, n) (blocks L A))
            by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
          destruct (untouched s L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n BK1 OU1 INq Hn NF) as (U1 & _).
          destruct K10 as [(C0 & B0 & _)|(Cp & _)]; [pose proof (blk_rng L A mem md _ _ HM0 INq); glia|].
          apply U1. rewrite Eq. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by glia.
          apply in_or_app. left. left. reflexivity.
        - intros a Ha _ _ Ea. exfalso. cbv beta in Ea. pose proof (ENI a Ea) as (EA & ENI' & _).
          destruct Ha as [Ha|Ha]; [glia | exact (ENI' Ha)].
        - intros p n i Hp Hp1 NF Hi Ea. exfalso. cbv beta in Ea.
          pose proof RP1 as (_ & _ & _ & _ & _ & AD1 & _).
          assert (INq : In (ptr_addr L p, n) (blocks L A))
            by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
          assert (INq1 : In (ptr_addr L p, n) (blocks L1 A1)).
          { unfold blocks. apply in_map_iff. exists (p, n).
            split; [cbn [fst snd]; rewrite (AD1 p n Hp Hp1 NF); reflexivity | exact Hp1]. }
          destruct (untouched s L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n BK1 OU1 INq ltac:(glia) NF) as (U1 & _).
          pose proof (ENI _ Ea) as (_ & _ & Cp).
          assert (NE : ptr_addr L p <> re_buf e1).
          { intros Eq. apply U1. rewrite Eq. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by glia.
            apply in_or_app. left. left. reflexivity. }
          exact (EDJ _ n (ptr_addr L p + i) INq1 (or_intror NE) ltac:(glia) Ea). }
      apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPc MU3 WM3 GEI).
      intros a Ha. destruct (dx_odec [(SA + 16, SA + 40)] a) as [Ox|(lo & hi & Iw & R)]; [left; exact Ox|right].
      destruct Iw as [Iw|[]]. injection Iw as <- <-.
      right. right. right. split; [exact (g_noimg a ltac:(glia))|].
      split; [exists G, SRC_TABLE; split; [exact GI2 | unfold SRC_TABLE, SRC_ENTRY in *; glia]|].
      intros p n i _ _ _ _ NE E. apply NE. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. glia. }
    split; [exact IN2|].
    split.
    { assert (LK2 : forall pp xx nn, live_at L1 A1 pp xx nn ->
                (xx = G \/ xx = OUT1 \/ In xx (hs_blocks h1) \/ xx = re_hp e1 \/ In xx (map key_addr (re_keys e1))) ->
                live_at L2 A2 pp xx nn).
      { intros pp xx nn Lx Hx. apply (KEEP pp xx nn Lx). apply (nb_of OUT1 e1 h1 xx ND1 Hx).
        pose proof (blk_rng _ _ _ _ _ _ M1 (gr_lv _ _ _ _ _ Lx)) as BR. clear - BR. lia. }
      assert (AB : agrow s (nretF tp) ad =
                   DA (da_out ad) (Ret (nretF tp)) (da_hp ad) (da_keys ad) (da_pend ad) (da_ev ad) (da_erecs ad))
        by (unfold agrow; rewrite GTa; reflexivity).
      assert (NT : nretF (tp ++ [ev]) = (nretF tp + 1)%nat) by (rewrite nret_app, NE1; reflexivity).
      unfold DTR. exists (tp ++ [ev]), (qd ++ [qn]),
        (DA (da_out ad) (Ret (nretF tp)) (da_hp ad) (da_keys ad) (da_pend ad) (da_ev ad) (da_erecs ad)).
      split.
      - unfold RCORE, DLNK, dadr_ok, entry_links.
        cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs re_cap re_buf re_hp re_kh re_keys].
        split; [rewrite length_app, NT, RQ; reflexivity|].
        split.
        { apply p3a_wf_snoc; [exact WF0|]. rewrite Hev. destruct (re_cap e1 =? 0); [exact I|]. rewrite <- RQ.
          exact Dbuf. }
        split.
        { rewrite NT, <- RQ.
          assert (MO : forall x, p3a_ok x (length qd) -> p3a_ok x (length qd + 1)%nat)
            by (intros x Hx; exact (p3a_ok_mono _ _ _ Hx (Nat.le_add_r _ _))).
          assert (MF : forall xs, Forall (fun x => p3a_ok x (length qd)) xs ->
                         Forall (fun x => p3a_ok x (length qd + 1)%nat) xs)
            by (intros xs Hxs; apply Forall_forall; intros x Hx; exact (MO x (proj1 (Forall_forall _ _) Hxs x Hx))).
          split; [exact (MO _ Dout)|]. split; [cbn [p3a_ok]; lia|]. split; [exact (MO _ Dhp)|].
          split; [exact (MF _ Dkeys)|]. split; [exact (MF _ Dpend)|]. split; [exact (MO _ Dev) | exact (MF _ Derecs)]. }
        split.
        { revert RS2. rewrite Hev. destruct (re_cap e1 =? 0); intros RS2.
          - rewrite (p3a_runF_mal F qd qn bnd tp _ WF0 (eq_sym RQ)). exact RS2.
          - rewrite (p3a_runF_rea F qd qn bnd tp _ _ _ WF0 (eq_sym RQ) Dbuf). exact RS2. }
        split; [|exact KH].
        split.
        { intros LV OCp. rewrite (p3a_resolve_app qd [qn] _ Dout).
          apply LK2; [exact (LKo LV OCp) | right; left; reflexivity]. }
        split.
        { split.
          { intros _. change (live_at L2 A2 (nth (nretF tp) (qd ++ [qn]) (SP 0 0)) res (dr_grow (re_cap e1))).
            rewrite (p3a_nth_last qd qn (nretF tp) (eq_sym RQ)). exact LQn. }
          split.
          { intros HP. rewrite (p3a_resolve_app qd [qn] _ Dhp).
            apply LK2; [exact (LKh HP) | right; right; right; left; reflexivity]. }
          apply (gr_f2 _ _ _ _ _ Dkeys LKk). intros kk yy Hkk Hyy Hll. cbv beta in Hyy, Hll |- *.
          rewrite (p3a_resolve_app qd [qn] yy Hyy).
          apply LK2; [exact Hll | right; right; right; right; apply in_map; exact Hkk]. }
        apply (gr_src L1 A1 L2 A2 qd [qn] _ h1); [| exact Dev | exact Dpend | exact Derecs | exact LKs].
        intros pp xx nn Hxx Lxx. apply LK2; [exact Lxx | right; right; left; exact Hxx].
      - unfold RFUT. rewrite NT, <- AB. split; [rewrite <- app_assoc; exact TE1|]. split; [exact TF1 | exact TA1]. }
    split.
    { rewrite SEGS. apply (ro_munch2 mem2 m3 [(SA + 16, SA + 40)]); [rewrite <- SEGS; exact RO2 | exact MU3 |].
      intros x Hx. cbn [outside]. split; [intros R; exact (g_noimg (bv_unsigned x) ltac:(glia) Hx) | exact I]. }
    split.
    { destruct FR1 as (j0 & j1 & j2 & j4 & FR). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FR |].
      intros a Ha. cbn [cells_size csize app dr_saved] in Ha. exact (PS a ltac:(glia)). }
    split.
    { rewrite SEGS. apply ent_join; [exact K3 | exact K4 | | exact HC3 |].
      - apply TPr; [exact EC1|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; glia.
      - apply TPr; [exact EC3|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; glia. }
    split.
    { eapply entry_okw_buf; [exact MS | exact EK1 | | | exact NV | exact (proj1 (proj2 NL)) | exact INres | exact FRES
        | | exact RC3].
      - intros q k Hq Hk. exact (proj1 (SURV q k Hq (NBK q k Hq Hk))).
      - intros q k a Hq Hk Ha. exact (PB q k a Hq (NBK q k Hq Hk) (NGK q k Hq Hk) Ha).
      - glia. }
    split.
    { eapply src_at_tr0; [exact MS | exact SR1 | | |].
      - intros a Ha. apply PI, GRP. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia.
      - intros q k Hq Hb. exact (proj1 (SURV q k Hq (NBH q k Hq Hb))).
      - intros q k a Hq Hb Ha. exact (PB q k a Hq (NBH q k Hq Hb) (NGH q Hb) Ha). }
    split.
    { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi _ Ha. apply PI, GRP.
      unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia. }
    split; [exact SM1|].
    split.
    { split; [change (dr_grow (re_cap e1) = gcap (ds_cap s) (ulen s)); unfold gcap; rewrite GT; reflexivity|].
      split; [exact L2c|]. split; [exact L3c|]. split; [exact L4c|]. split; [exact L5c|]. split; [exact L6c|].
      split; [exact L7c|]. split; [exact L8c|]. split; [exact L9c|]. split; [exact L10c|].
      split; [exact L11c | exact WF1]. }
    split; [exact HI1|].
    split.
    { assert (EB' : entry_blocks (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) res (re_used e1)
                       (dr_grow (re_cap e1)) (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1) (re_U e1) junk2) =
                     res :: ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1))).
      { unfold entry_blocks. cbn [re_cap re_buf re_hp re_keys].
        rewrite (proj2 (Z.eqb_neq (dr_grow (re_cap e1)) 0)) by (clear - NV; lia). reflexivity. }
      split.
      { assert (NDl : List.NoDup ([G; OUT1] ++ (if re_cap e1 =? 0 then [] else [re_buf e1]) ++
                  (((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1)) ++ hs_blocks h1))).
        { pose proof ND1 as ND1'. apply NoDup_ListNoDup in ND1'. unfold entry_blocks in ND1'.
          rewrite <- app_assoc in ND1'. exact ND1'. }
        pose proof (nodup_mid_drop _ _ _ NDl) as ND2.
        assert (NIres : ~ In res ([G; OUT1] ++ ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++
                                   map key_addr (re_keys e1)) ++ hs_blocks h1)).
        { intros Hin.
          assert (Hq : res = G \/ res = OUT1 \/
                       In res ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1)) \/
                       In res (hs_blocks h1)).
          { cbn [app] in Hin. destruct Hin as [E|[E|Hin]]; [left; symmetry; exact E | right; left; symmetry; exact E|].
            apply in_app_or in Hin as [Hin|Hin]; [right; right; left; exact Hin | right; right; right; exact Hin]. }
          destruct (LIVEQ res Hq) as [R0|(k & Hk & Nk)]; [exact (NZ R0)|].
          exact (proj2 (SURV res k Hk Nk) eq_refl). }
        pose proof (nodup_mid_add _ _ res ND2 NIres) as ND3.
        apply NoDup_ListNoDup. rewrite EB'. exact ND3. }
      split; [exact GI2|].
      split.
      { intros q m Hq HO HE. pose proof (SV1 q m Hq HO HE) as Hq1. refine (proj1 (SURV q m Hq1 _)).
        destruct (Z.eq_dec (re_cap e1) 0) as [C|C]; [left; exact C | right]. intros ->.
        destruct K10 as [(C0 & _)|(Cp & BI & _)]; [glia|].
        assert (Em : m = re_cap e1) by exact (sb_nodup_fst _ _ _ _ NDB1 Hq1 BI).
        destruct (FB1 (re_buf e1) m Hq ltac:(glia) HO HE) as (_ & U1 & _). apply U1. unfold entry_blocks.
        rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) C). apply in_or_app. left. left. reflexivity. }
      split.
      { intros q m Hq. destruct (BACK q m Hq) as [(-> & ->)|(Hq1 & NBq)].
        - right. left. apply in_or_app. left. rewrite EB'. left. reflexivity.
        - destruct (CL1 q m Hq1) as [X|[X|X]]; [left; exact X | right; left | right; right; exact X].
          apply in_app_or in X as [X|X]; apply in_or_app; [left | right; exact X].
          rewrite EB'. right. unfold entry_blocks in X. apply in_app_or in X as [X|X]; [|exact X].
          revert X. destruct (re_cap e1 =? 0) eqn:CZ; intros X; [destruct X | destruct X as [X|[]]].
          destruct NBq as [NBq|NBq]; [apply Z.eqb_neq in CZ; exfalso; glia | congruence]. }
      intros q m Hq Hm HO HE. destruct (FB1 q m Hq Hm HO HE) as (U0 & U1 & U2).
      split; [exact U0|]. split; [|exact U2].
      rewrite EB'. intros [X|X].
      - pose proof (SV1 q m Hq HO HE) as Hq1.
        assert (NBq : re_cap e1 = 0 \/ q <> re_buf e1).
        { destruct (Z.eq_dec (re_cap e1) 0) as [C|C]; [left; exact C | right]. intros E. apply U1. rewrite E.
          unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) C). apply in_or_app. left. left. reflexivity. }
        exact (proj2 (SURV q m Hq1 NBq) (eq_sym X)).
      - apply U1. unfold entry_blocks. apply in_or_app. right. exact X. }
    split.
    { destruct GL1 as (C1 & C2 & C3 & CC4 & _).
      split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GCP; unfold G_CLIENT in *; glia|].
      split; [eapply rw_tr; [exact MS | exact C2 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      split; [eapply rw_tr; [exact MS | exact C3 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      split; [eapply rw_tr; [exact MS | exact CC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      destruct (sb_c4 m3 ERR) as (v & HV); [glia | glia | |exists v; rewrite SEGS; exact HV].
      intros i Hi. rewrite <- SEGS. apply WM3, SC2. right. glia. }
    change (DOUT s L2 A2 m3 OUT1 junk1 LB1).
    destruct OU1 as (OF & OT). split.
    + intros LV. destruct (OF LV) as (C & EO & EC' & OB).
      split; [eapply rw_tr; [exact MS | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      split; [exact EO|]. split; [exact EC'|]. intros Cp. destruct (OB Cp) as (OI & OBy).
      assert (NBo : re_cap e1 = 0 \/ OUT <> re_buf e1).
      { apply (nb_of OUT1 e1 h1 OUT ND1); [right; left; symmetry; exact EO|].
        pose proof (blk_rng _ _ _ _ _ _ M1 OI). glia. }
      split; [exact (proj1 (SURV OUT CAP OI NBo))|].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha.
      apply (PB OUT CAP a OI NBo); [apply (dx_ng OUT1 _ OUT ND1); left; symmetry; exact EO|].
      destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & _ & LJ)]; [glia|]. rewrite length_app in Ha. glia.
    + intros LV. destruct (OT LV) as (C & OB).
      split; [eapply rw_tr; [exact MS | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      destruct OB as [Z0|(Cp & NLo & OI & OFr & OBy & LJ)]; [left; exact Z0|right].
      assert (NBo : re_cap e1 = 0 \/ OUT1 <> re_buf e1).
      { apply (nb_of OUT1 e1 h1 OUT1 ND1); [right; left; reflexivity|].
        pose proof (blk_rng _ _ _ _ _ _ M1 OI). glia. }
      split; [exact Cp|]. split; [exact NLo|]. split; [exact (proj1 (SURV _ _ OI NBo))|]. split; [exact OFr|].
      split; [|exact LJ].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha.
      apply (PB OUT1 (ds_ocap s) a OI NBo); [apply (dx_ng OUT1 _ OUT1 ND1); left; reflexivity|].
      assert (LL : Z.of_nat (length LB1) = dtot D)
        by (unfold dtot; rewrite <- H8; unfold bzs; rewrite length_map; reflexivity).
      rewrite !length_app in Ha. glia.
Qed.

Lemma eintr_step : forall s c, DF s c -> ds_eintr s = true -> SR segs c (DI (dclr s)).
Proof using All.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RT1 & G10 & G11 & G20 & GR & DC1) EI.
  pose proof DC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof SR1 as (S1 & _).
  pose proof GL1 as (_ & _ & _ & _ & (ev1 & CE1)).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof pre_facts as (_ & _ & _ & _ & _ & _ & _ & _ & HTP & _).
  pose proof err_hi as EH. unfold G_LOCK_HI in F9.
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct RT1 as ((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26).
  assert (E1 : hs_eintr h1 = 1) by (rewrite L6c, EI; reflexivity).
  assert (TPV : bv_unsigned (getr R1 4) + -164 = ERR).
  { rewrite G4, HTP. unfold ERRNO_OFF in TPE. rewrite unsigned_lit by lia. lia. }
  assert (TPV2 : bv_unsigned (getr R1 4) + -160 = ERR + 4) by lia.
  assert (HC : rw_cells rsegs m1 (XH + 128) [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                                             C4 (Z_to_bv 64 (hs_closed h1)); C4 (Z_to_bv 64 1)]).
  { replace (XH + 128) with HA by (unfold DR_TU, G_S, SRC_SIZE; lia). rewrite SEGS, E1 in S1. exact S1. }
  assert (CE : rw_cells rsegs m1 (bv_unsigned (getr R1 4) + -164) [C4 ev1]) by (rewrite TPV, <- SEGS; exact CE1).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20, G26. rewrite SEGS.
    eapply (dr_eintr ELC); [exact HC | exact CE | unfold DR_TU; lia | rewrite TPV; lia | rewrite TPV; exact ERR4 |].
    rewrite TPV. left. unfold DR_TU, G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
  intros ms (can & (m2 & x1' & x10' & x11' & x12' & -> & MU & WM & HS2 & HE2) & EQ).
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  apply SR_ret.
  rewrite TPV, TPV2 in MU.
  assert (WM' : wmono segs m1 m2) by (rewrite SEGS; exact WM).
  assert (HW : WOK [(XH + 140, XH + 144); (ERR, ERR + 4)]).
  { intros lo hi [Ei|[Ei|[]]]; injection Ei as <- <-; [left | right; left]; unfold DR_TU, G_S, SRC_SIZE in *; lia. }
  destruct (dc_munch s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 _ DC1 MU WM' HW)
    as (RP2 & RO2 & FR2 & EK2 & SRC2 & OT2 & GL2 & OU2).
  exists R2, L1, A1, m2, md1, e1, (hs_eset h1 0), OUT1, junk1, LB1, D.
  split; [reflexivity|].
  split; [unfold RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
  split; [exact RP2|]. split; [exact IN1|].
  split.
  { destruct TR1 as (tp & qd & a & RC & RF).
    assert (DE : drun (dneed s) LIVE MX s (nretF tp) a = drun (dneed (dclr s)) LIVE MX (dclr s) (nretF tp) a).
    { rewrite (dneed_dclr s EI). exact (drun_eintr _ LIVE MX s (nretF tp) a GR EI). }
    rewrite DE in RF. exists tp, qd, a. split; [exact RC | exact RF]. }
  split; [exact RO2|]. split; [exact FR2|].
  split.
  { eapply rw_tr; [exact (msame_munch _ _ _ MU WM') | exact SAC1 |]. intros a Ha. cbn [cells_size csize] in Ha.
    cbv beta. pose proof (g_noimg a ltac:(lia)) as NI. split; [lia|]. cbn [outside].
    split; [intros R; apply NI, grp_img; unfold DR_TU, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [intros R; exact (NI (GEI a R)) | exact I]. }
  split; [exact EK2|].
  split.
  { apply SRC2; [|left; reflexivity]. replace HA with (XH + 128) by (unfold DR_TU, G_S, SRC_SIZE; lia).
    rewrite SEGS. exact HS2. }
  split; [exact OT2|]. split; [exact SM1|].
  split.
  { split; [exact L1c|]. split; [exact L2c|]. split; [exact L3c|]. split; [exact L4c|]. split; [exact L5c|].
    split; [reflexivity|]. split; [exact L7c|]. split; [exact L8c|]. split; [exact L9c|]. split; [exact L10c|].
    split; [exact L11c | exact WF1]. }
  split; [exact HI1|]. split; [exact BK1|]. split; [exact GL2 | exact OU2].
Qed.

Lemma exit_step : forall s c, DF s c -> ds_eintr s = false -> ds_pend s = [] -> SR segs c DPOST.
Proof using All.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RT1 & G10 & G11 & G20 & GR & DC1) EI PE.
  pose proof DC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof SM1 as (D1 & D2 & D3 & D4 & D5 & _).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & _).
  pose proof SR1 as (S1 & S2 & _ & _ & _ & S6 & _).
  pose proof GL1 as (_ & _ & _ & _ & (ev1 & CE1)).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof pre_facts as (_ & _ & _ & HRA & _ & HCEIL & H63 & _ & HTP & _).
  pose proof err_hi as EH. unfold G_LOCK_HI in F9.
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct RT1 as ((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26).
  assert (E0 : hs_eintr h1 = 0) by (rewrite L6c, EI; reflexivity).
  pose proof L7c as L7p. rewrite PE in L7p. pose proof (map_eq_nil _ _ L7p) as RN.
  assert (PC0 : rw_cells rsegs m1 (XH + 144) [C8 (Z_to_bv 64 (hl_v (hs_pending h1))); C4 (Z_to_bv 64 0);
                                              C4 (Z_to_bv 64 (hl_cap (hs_pending h1)))]).
  { replace (XH + 144) with (HA + 16) by (unfold DR_TU, G_S, SRC_SIZE; lia). destruct S6 as (P & _).
    unfold hl_n in P. rewrite RN in P. rewrite <- SEGS. exact P. }
  destruct FR1 as (j0 & j1 & j2 & j4 & FR). rewrite SEGS in FR.
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 40) _ _ FR eq_refl) as [_ FRS].
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
  destruct (dr_cut m1 SA (SA + 12) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1));
              C4 (Z_to_bv 64 (re_skip e1))] [CB 4 (re_pad1 e1)] EC1 eq_refl) as [EC0 EP].
  assert (PRS : forall R2 a10 a11 a12, Regs6ss.xregs_eqv (mkR (getr regs 1) (Z_to_bv 64 S0) (getr R1 3) (getr R1 4)
      (getr R1 5) (getr R1 6) (getr R1 7) (getr regs 8) (getr regs 9) a10 a11 a12
      (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17) (getr regs 18) (getr regs 19) (getr regs 20)
      (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31)) R2 -> regs_preserved regs R2).
  { intros R2 a10 a11 a12 X3 r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct C as [C|C]; [subst r; rgw X3|]); subst r; rgw X3. }
  destruct S2 as [C0|C1'].
  - assert (HC : rw_cells rsegs m1 (XH + 128) [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                                               C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
    { replace (XH + 128) with HA by (unfold DR_TU, G_S, SRC_SIZE; lia). rewrite SEGS, C0, E0 in S1. exact S1. }
    assert (TPV : bv_unsigned (getr R1 4) + -164 = ERR).
    { rewrite G4, HTP. unfold ERRNO_OFF in TPE. rewrite unsigned_lit by lia. lia. }
    assert (TPV2 : bv_unsigned (getr R1 4) + -160 = ERR + 4) by lia.
    assert (CE : rw_cells rsegs m1 (bv_unsigned (getr R1 4) + -164) [C4 ev1]) by (rewrite TPV, <- SEGS; exact CE1).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G8, G20, G26. rewrite SEGS.
      eapply (dr_again ELC); [exact FRS | exact HC | exact PC0 | exact CE | lia | lia | unfold DR_TU; lia | lia |
                              rewrite TPV; exact ERR4 | lia]. }
    intros ms (can & (m2 & x10' & x11' & x12' & -> & MU & WM & HE2) & EQ).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    rewrite (CF.gestures_end_b.ret_pc_of_ok2 _ HRA).
    apply SR_ret.
    rewrite TPV, TPV2 in MU.
    assert (WM' : wmono segs m1 m2) by (rewrite SEGS; exact WM).
    assert (HW : WOK [(ERR, ERR + 4)]) by (intros lo hi [Ei|[]]; injection Ei as <- <-; right; left; lia).
    apply (exit_post s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 _ R2 (re_eof e1) DC1 GR EI PE MU WM' HW).
    + intros a Ha. cbn [outside]. split; [unfold G_S, SRC_SIZE, SOURCES_MAX in *; lia | exact I].
    + replace (S0 - 144 + 144) with S0 in X2 by lia. eapply PRS. exact X2.
    + rewrite <- D5, C0, D2. reflexivity.
    + exact K1.
    + eapply rw_tr; [exact (msame_munch _ _ _ MU WM') | exact SAC1 |]. intros a Ha. cbn [cells_size csize] in Ha.
      cbv beta. pose proof (g_noimg a ltac:(lia)) as NI. split; [lia|]. cbn [outside].
      split; [intros R; exact (NI (GEI a R)) | exact I].
  - assert (HC : rw_cells rsegs m1 (XH + 128) [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                                               C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)]).
    { replace (XH + 128) with HA by (unfold DR_TU, G_S, SRC_SIZE; lia). rewrite SEGS, C1', E0 in S1. exact S1. }
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G8, G20. rewrite SEGS.
      eapply dr_closed; [exact FRS | exact EC0 | exact HC | exact PC0 | lia | lia | lia | unfold DR_TU; lia]. }
    intros ms (can & (m2 & x10' & x12' & -> & MU & WM & HE2) & EQ).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    rewrite (CF.gestures_end_b.ret_pc_of_ok2 _ HRA).
    apply SR_ret.
    assert (WM' : wmono segs m1 m2) by (rewrite SEGS; exact WM).
    assert (HW : WOK [(SA + 4, SA + 8)]) by (intros lo hi [Ei|[]]; injection Ei as <- <-; right; right; lia).
    pose proof (msame_munch _ _ _ MU WM') as MS.
    assert (TP : forall c cs, rw_cells rsegs m1 c cs ->
              (forall a, c <= a < c + Z.of_nat (cells_size cs) -> 0 <= a < 2 ^ 64 /\ outside [(SA + 4, SA + 8)] a) ->
              rw_cells rsegs m2 c cs).
    { intros c cs H HP. rewrite <- SEGS in H |- *. exact (rw_tr _ _ _ c cs MS H HP). }
    apply (exit_post s D L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 _ R2 1 DC1 GR EI PE MU WM' HW).
    + intros a Ha. cbn [outside]. split; [|exact I]. intros R. apply (g_noimg a); [lia|].
      apply grp_img. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + replace (S0 - 144 + 144) with S0 in X2 by lia. eapply PRS. exact X2.
    + rewrite <- D5, C1'. reflexivity.
    + right. reflexivity.
    + rewrite SEGS. apply ent_join; [exact K3 | exact K4 | | |].
      * apply (dr_join m2 SA (SA + 12) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (re_skip e1))]
                 [CB 4 (re_pad1 e1)]); [exact HE2 | | reflexivity].
        apply TP; [exact EP|]. intros a Ha. cbn [cells_size csize] in Ha. split; [lia|]. cbn [outside].
        split; [lia | exact I].
      * apply TP; [exact EC2|]. intros a Ha. cbn [cells_size csize] in Ha. split; [lia|]. cbn [outside].
        split; [lia | exact I].
      * apply TP; [exact EC3|]. intros a Ha. cbn [cells_size csize] in Ha. split; [lia|]. cbn [outside].
        split; [lia | exact I].
Qed.

Lemma DF_facts : forall s c, DF s c -> 4096 <= ds_cap s - ulen s /\ dwf s /\ dstrict s.
Proof using HJ.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & _ & _ & _ & _ & _ & GR & DC1).
  pose proof DC1 as (_ & _ & _ & _ & _ & _ & _ & SR1 & _ & _ & LK1 & _).
  pose proof LK1 as (_ & _ & _ & _ & _ & _ & L7c & L8c & _ & _ & _ & WF1).
  pose proof SR1 as (_ & _ & _ & _ & _ & _ & _ & PC & _).
  split; [exact GR|]. split; [exact WF1|].
  intros r rs E. rewrite <- L7c in E. rewrite <- L8c.
  destruct PC as [(RN & _)|(r0 & rs0 & RE & RO)]; [rewrite RN in E; cbn [map] in E; discriminate|].
  rewrite RE in E. cbn [map] in E. injection E as <- _. unfold bzs. rewrite length_map. lia.
Qed.

Local Abbreviation RestT := (nat -> adrF -> adrF -> list adrF -> trF * (adrF * adrF * list adrF)).

Definition anext (a : dadr) (r : adrF * adrF * list adrF) : dadr :=
  DA (fst (fst r)) (da_buf a) (snd (fst r)) (snd r) (da_pend a) (da_ev a) (da_erecs a).

Definition MTR (s : dstate) (L1 : layout) (A1 : astate) (oc : Z) (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (rest : RestT)
    : Prop :=
  exists tp qd a,
    RCORE L1 A1 oc e1 h1 OUT1 tp qd a /\
    RFUT (tp ++ fst (rest (nretF tp) (da_out a) (da_hp a) (da_keys a)))
      (drun (length (pstream s)) LIVE MX (dnext LIVE MX s)
         (nretF tp + nretF (fst (rest (nretF tp) (da_out a) (da_hp a) (da_keys a))))
         (anext a (snd (rest (nretF tp) (da_out a) (da_hp a) (da_keys a))))).

Definition lrest (no oc : Z) (H : list (list Z)) (ka : Z) (rl : list (list Z)) : RestT :=
  fun jb o ha ks =>
    (fst (fst (lines_run LIVE MX no oc H ka rl jb o ha ks)), snd (lines_run LIVE MX no oc H ka rl jb o ha ks)).

Definition srest (H : list (list Z)) (ka : Z) (l : list Z) (no oc : Z) (rl : list (list Z)) : RestT :=
  fun jb o ha ks =>
    (fst (fst (seen_tr H ka l jb ha ks)) ++
       fst (lrest no oc (seen_arr H l) (seen_ka H ka l) rl (jb + nretF (fst (fst (seen_tr H ka l jb ha ks))))
              o (fst (snd (seen_tr H ka l jb ha ks))) (snd (snd (seen_tr H ka l jb ha ks)))),
     snd (lrest no oc (seen_arr H l) (seen_ka H ka l) rl (jb + nretF (fst (fst (seen_tr H ka l jb ha ks))))
            o (fst (snd (seen_tr H ka l jb ha ks))) (snd (snd (seen_tr H ka l jb ha ks))))).

Definition dW (s : dstate) : list Z := ds_u s ++ ddata s.

Definition entry_okx (L1 : layout) (A1 : astate) (m : word -> option byte) (e1 : rentry) : Prop :=
  (re_eof e1 = 0 \/ re_eof e1 = 1) /\ (re_skip e1 = 0 \/ re_skip e1 = 1) /\
  length (re_pad1 e1) = 4%nat /\ length (re_pad2 e1) = 4%nat /\
  0 <= re_fd e1 < 2 ^ 31 /\
  (re_cap e1 = 0 \/ re_cap e1 = 8192 \/ re_cap e1 = 16384) /\
  Z.of_nat (length (re_U e1)) = re_used e1 /\ re_used e1 <= re_cap e1 /\
  ((re_cap e1 = 0 /\ re_buf e1 = 0 /\ re_used e1 = 0) \/
   (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (blocks L1 A1) /\ fresh_block Bm (re_buf e1) (re_cap e1) /\
    Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
    rw_cells segs m (re_buf e1) [CB (Z.to_nat (re_cap e1)) (re_U e1 ++ re_junk e1)])) /\
  re_nheld e1 < 2 ^ 26 /\
  ((re_hp e1 = 0 /\ re_keys e1 = []) \/
   (In (re_hp e1, re_kh e1) (blocks L1 A1) /\ fresh_block Bm (re_hp e1) (re_kh e1) /\ 8 * re_nheld e1 <= re_kh e1 /\
    8 <= re_kh e1 /\ bytes_at segs m (re_hp e1) (key_ptrs (re_keys e1)))) /\
  NoDup (map key_addr (re_keys e1)) /\
  NoDup (map key_text (re_keys e1)) /\
  Forall (key_okw L1 A1 m) (re_keys e1).

Definition DHISTg (sent kl : list (list Z)) (Dh : list Z) (s1 : dstate) (h1 : hsrc) (LB1 : list byte) : Prop :=
  bzs PS = Dh ++ pstream s1 /\ ds_ref s1 = feed ST0 Dh /\
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines ST0 Dh) /\
  firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
  hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
  ds_no s1 = NO + Z.of_nat (length (with_nul sent)) /\ bzs LB1 = with_nul sent /\
  NoDup (ds_H s1) /\ same_set (ds_H s1) (upds (keys_texts (re_keys e)) kl) /\
  ds_en s1 + Z.of_nat (length (pstream s1)) < 2 ^ 27.

Definition DGLBg (tot : Z) (m1 : word -> option byte) : Prop :=
  rw_cells segs m1 G_CLIENT [C4 (Z_to_bv 64 cl)] /\
  rw_cells segs m1 G_BROKEN [C1 (Z_to_bv 8 (if send_off cl br tot then br else dd))] /\
  rw_cells segs m1 G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells segs m1 G_EINTR [C1 (Z_to_bv 8 (if send_off cl br tot then ei else 0))] /\
  (exists ev1, rw_cells segs m1 ERR [C4 ev1]).

Definition RSTART (s : dstate) (D : list Z) : Prop :=
  ds_ref s = feed ST0 D /\ J1 (ds_u s) (ds_skip s) (ds_ref s) /\ 4096 <= ds_cap s - ulen s /\ dwf s /\
  dstrict s /\ ds_eintr s = false /\ ds_pend s <> [].

Definition dvirt (s : dstate) (sk : bool) (H : list (list Z)) (ka no oc : Z) : dstate :=
  DS (ds_cap s) (dW s) sk H ka false
     (ds_pend (dnext LIVE MX s)) (ds_off (dnext LIVE MX s))
     (ds_ref (dnext LIVE MX s)) (ds_en (dnext LIVE MX s))
     (ds_ecap (dnext LIVE MX s)) no oc.

Definition LCORE (s : dstate) (D : list Z) (sent kl : list (list Z)) (H : list (list Z)) (ka no oc nk : Z)
    (rest : RestT) (sk : bool) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (junk1 LB1 : list byte) : Prop :=
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 /\
  st_init_done A1 = true /\
  MTR s L1 A1 oc e1 h1 OUT1 rest /\
  ro_agree segs m1 /\
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] /\
  entry_okx L1 A1 m1 e1 /\
  src_at Bm L1 A1 m1 HA h1 /\
  others_at Bm m1 j (re_fd e) fs os /\
  DSAME e1 h1 /\
  DLINK (dvirt s sk H ka no oc) e1 h1 /\
  DHISTg sent kl (D ++ ddata s) (dvirt s sk H ka no oc) h1 LB1 /\
  Z.of_nat (length H) + nk + Z.of_nat (length (pstream (dvirt s sk H ka no oc))) < 2 ^ 26 /\
  RSTART s D /\
  DBLK L1 A1 e1 h1 OUT1 /\
  DGLBg (Z.of_nat (length (with_nul sent))) m1 /\
  DOUT (dvirt s sk H ka no oc) L1 A1 m1 OUT1 junk1 LB1.

Definition drlp (s : dstate) (P : nat) : list (list Z) := snd (scan (ds_skip s) [] (firstn P (dW s))).
Definition dskp (s : dstate) (P : nat) : bool := if Nat.eqb P 0 then ds_skip s else false.
Definition drlq (s : dstate) (P : nat) : list (list Z) := snd (scan (dskp s P) [] (skipn P (dW s))).
Definition dlrun (s : dstate) (P : nat) : Z * list (list Z) * Z :=
  lrun LIVE MX (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drlp s P).
Definition dlno (s : dstate) (P : nat) : Z := ds_no s + Z.of_nat (length (with_nul (drlp s P))).
Definition dloc (s : dstate) (P : nat) : Z := fst (fst (dlrun s P)).
Definition dlH (s : dstate) (P : nat) : list (list Z) := snd (fst (dlrun s P)).
Definition dlka (s : dstate) (P : nat) : Z := snd (dlrun s P).

Definition DLC (s : dstate) (D : list Z) (P : nat) (L1 : layout) (A1 : astate) (m1 : word -> option byte)
    (md1 : Model) (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (junk1 LB1 : list byte) : Prop :=
  LCORE s D (lines ST0 D ++ drlp s P) (lines ST0 D ++ drlp s P) (dlH s P) (dlka s P) (dlno s P) (dloc s P)
    (Z.of_nat (length (drlq s P)))
    (lrest (dlno s P) (dloc s P) (dlH s P) (dlka s P) (drlq s P)) (dskp s P)
    L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition dbound (s : dstate) (P : nat) : Prop :=
  (P <= length (dW s))%nat /\ (P = 0%nat \/ nth_error (dW s) (P - 1) = Some 0).

Definition dline (s : dstate) (P Q : nat) : list Z := firstn (Q - P) (skipn P (dW s)).

Definition DLL (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13bac) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    dbound s P /\ (P <= Q < length (dW s))%nat /\ nth_error (dW s) Q = Some 0 /\
    (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) /\
    DLC s D P L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DLS (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13be4) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    dbound s P /\ (P <= Q < length (dW s))%nat /\ nth_error (dW s) Q = Some 0 /\
    (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) /\
    dskp s P = false /\ (Q - P <= LINE_LIMIT)%nat /\
    LCORE s D (lines ST0 D ++ drlp s P ++ [dline s P Q]) (lines ST0 D ++ drlp s P) (dlH s P) (dlka s P)
      (dlno s P + Z.of_nat (length (dline s P Q)) + 1)
      (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1))
      (Z.of_nat (S (length (drlq s (S Q)))))
      (srest (dlH s P) (dlka s P) (dline s P Q) (dlno s P + Z.of_nat (length (dline s P Q)) + 1)
         (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)) (drlq s (S Q)))
      false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DLN (s : dstate) (P : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13b8c) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    dbound s P /\
    DLC s D P L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DLR (s : dstate) (P : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13e54) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\ getr R1 19 = Z_to_bv 64 (re_buf e1) /\
    getr R1 20 = Z_to_bv 64 (Z.of_nat (length (dW s) - P)) /\
    dbound s P /\ (forall i, (P <= i)%nat -> nth_error (dW s) i <> Some 0) /\
    DLC s D P L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DHQ (s : dstate) (c : config) : Prop := DLN s 0 c.

Lemma scan_zero_fst : forall sk acc d, fst (scan sk acc (0 :: d)) = fst (scan false [] d).
Proof using. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma scan_zero_snd : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof using. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma pstream_dnext : forall lv mx0 s, dwf s -> dstrict s -> ds_pend s <> [] -> 4096 <= ds_cap s - ulen s ->
  pstream s = ddata s ++ pstream (dnext lv mx0 s).
Proof using HG HJ O h junk.
  intros lv mx0 s W ST P H. pose proof (dnum_pos s ST H P) as NP. destruct W as [W0 _].
  unfold pstream, dnext, ddata, dwhole. cbn [ds_pend ds_off]. unfold dtail, dhead.
  set (n := dnum s) in *. clearbody n.
  destruct (ds_pend s) as [|r0 rs] eqn:PE; [congruence|]. cbn [prest].
  destruct (Z.eqb_spec (ds_off s + n) (Z.of_nat (length r0))) as [E2|E2].
  - rewrite firstn_all2 by (rewrite length_skipn; lia). destruct rs; reflexivity.
  - cbn [prest]. rewrite app_assoc. f_equal.
    replace (Z.to_nat (ds_off s + n)) with (Z.to_nat n + Z.to_nat (ds_off s))%nat by lia.
    rewrite <- skipn_skipn. symmetry. apply firstn_skipn.
Qed.

Lemma lines_len : forall st d, (length (lines st d) <= length d)%nat.
Proof using Bm G HJ O h junk regs.
  intros st d. revert st. unfold lines. induction d as [|b d IH]; intros st; [cbn; lia|].
  cbn [feed_lines]. destruct (step st b) as [st1 o]. cbn [snd]. pose proof (IH st1) as I.
  destruct (feed_lines st1 d) as [st2 ls]. cbn [snd] in I |- *. destruct o; cbn [length]; lia.
Qed.

Lemma scan_nz_app : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof using.
  induction u as [|b u IH]; intros sk acc d Hz.
  - rewrite app_nil_r. reflexivity.
  - pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
    rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma scan_lines_le : forall d sk acc, (length (snd (scan sk acc d)) <= length d)%nat.
Proof using Bm G HJ O h junk regs.
  induction d as [|b d IH]; intros sk acc; [cbn; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb].
  - rewrite scan_zero_snd. pose proof (IH false []) as I.
    destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; cbn [length]; lia.
  - rewrite (scan_nz sk acc b d Hb). pose proof (IH sk (acc ++ [b])). cbn [length]. lia.
Qed.

Lemma with_nul_cons : forall l r, with_nul (l :: r) = (l ++ [0]) ++ with_nul r.
Proof using. reflexivity. Qed.

Lemma lrun_one : forall lv mx0 no0 cp0 H0 ka0 l,
  lrun lv mx0 no0 cp0 H0 ka0 [l] =
  (send_line_cap lv mx0 no0 cp0 (Z.of_nat (length l) + 1), seen_arr H0 l, seen_ka H0 ka0 l).
Proof using. intros lv mx0 no0 cp0 H0 ka0 l. unfold lrun. cbn [lines_run fst snd]. rewrite seen_tr_m. reflexivity. Qed.

Lemma lrun_app : forall lv mx0 l1 l2 no0 cp0 H0 ka0,
  lrun lv mx0 no0 cp0 H0 ka0 (l1 ++ l2) =
  lrun lv mx0 (no0 + Z.of_nat (length (with_nul l1))) (fst (fst (lrun lv mx0 no0 cp0 H0 ka0 l1)))
    (snd (fst (lrun lv mx0 no0 cp0 H0 ka0 l1))) (snd (lrun lv mx0 no0 cp0 H0 ka0 l1)) l2.
Proof using Bm G HJ O h junk regs.
  intros lv mx0 l1. induction l1 as [|l r IH]; intros l2 no0 cp0 H0 ka0.
  - rewrite app_nil_l. change (with_nul []) with (@nil Z). cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - assert (C : forall nb cb Hb kb ls, lrun lv mx0 nb cb Hb kb (l :: ls) =
                 lrun lv mx0 (nb + (Z.of_nat (length l) + 1)) (send_line_cap lv mx0 nb cb (Z.of_nat (length l) + 1))
                   (seen_arr Hb l) (seen_ka Hb kb l) ls).
    { intros nb cb Hb kb ls. unfold lrun at 1. cbn [lines_run fst snd]. rewrite lines_run_m, seen_tr_m.
      reflexivity. }
    rewrite <- app_comm_cons, !C, IH.
    replace (no0 + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul r)))
      with (no0 + Z.of_nat (length (with_nul (l :: r)))) by (rewrite with_nul_cons, !length_app; cbn [length]; lia).
    reflexivity.
Qed.

Lemma nth_skipn_cons : forall (l : list Z) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof using.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - exact (IH n x Hn).
Qed.

Lemma firstn_nth_app : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof using.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n x Hn). reflexivity.
Qed.

Lemma firstn_split : forall P Q (l : list Z), (P <= Q)%nat -> firstn Q l = firstn P l ++ firstn (Q - P) (skipn P l).
Proof using Bm G HJ O h junk regs.
  induction P as [|P IH]; intros Q l HPQ.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct Q as [|Q]; [lia|]. destruct l as [|a l].
    + rewrite skipn_nil, !firstn_nil. reflexivity.
    + change (a :: firstn Q l = a :: firstn P l ++ firstn (Q - P) (skipn P l)).
      rewrite (IH Q l) by lia. reflexivity.
Qed.

Lemma nth_skipn : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof using.
  induction l as [|a l IH]; intros n i.
  - rewrite skipn_nil, !nth_error_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|]. change (nth_error (skipn n l) i = nth_error l (n + i)). apply IH.
Qed.

Lemma nz_firstn : forall (l : list Z) k, (forall i, (i < k)%nat -> nth_error l i <> Some 0) -> nozero (firstn k l).
Proof using Bm G HJ O h junk regs.
  unfold nozero. induction l as [|a l IH]; intros k H.
  - rewrite firstn_nil. constructor.
  - destruct k as [|k]; [change (Forall (fun b => b <> 0) (@nil Z)); constructor|].
    change (Forall (fun b => b <> 0) (a :: firstn k l)). constructor.
    + intro E. apply (H 0%nat); [lia|]. rewrite E. reflexivity.
    + apply IH. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma nz_nth : forall (l : list Z), (forall i, nth_error l i <> Some 0) -> nozero l.
Proof using.
  intros l H. unfold nozero. apply Forall_forall. intros x Hx E. subst x.
  apply In_nth_error in Hx as (n & Hn). exact (H n Hn).
Qed.

Lemma dline_len : forall s P Q, (P <= Q < length (dW s))%nat -> length (dline s P Q) = (Q - P)%nat.
Proof using HG HJ O h junk. intros s P Q H. unfold dline. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.

Lemma dline_nz : forall s P Q, (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) -> nozero (dline s P Q).
Proof using HG HJ O h junk.
  intros s P Q H. unfold dline. apply nz_firstn. intros i Hi. rewrite nth_skipn. apply H. lia.
Qed.

Lemma dW_split : forall s P Q, (P <= Q)%nat -> nth_error (dW s) Q = Some 0 ->
  skipn P (dW s) = dline s P Q ++ 0 :: skipn (S Q) (dW s).
Proof using HG HJ O h junk.
  intros s P Q HPQ HQ. unfold dline. rewrite <- (nth_skipn_cons _ _ _ HQ).
  rewrite <- (firstn_skipn (Q - P) (skipn P (dW s))) at 1.
  rewrite skipn_skipn. replace (Q - P + P)%nat with Q by lia. reflexivity.
Qed.

Lemma dW_pre_line : forall s P Q, (P <= Q)%nat -> nth_error (dW s) Q = Some 0 ->
  firstn (S Q) (dW s) = firstn P (dW s) ++ dline s P Q ++ [0].
Proof using Bm G HJ O h junk regs.
  intros s P Q HPQ HQ. rewrite (firstn_nth_app _ _ _ HQ), (firstn_split P Q _ HPQ), <- app_assoc. reflexivity.
Qed.

Lemma scan_app_z : forall p sk acc q,
  fst (scan sk acc (p ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk acc (p ++ 0 :: q)) = snd (scan sk acc (p ++ [0])) ++ snd (scan false [] q).
Proof using.
  induction p as [|b p IH]; intros sk acc q.
  - cbn [app]. rewrite scan_zero_fst, !scan_zero_snd. cbn [scan snd]. split; [reflexivity|].
    destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
  - cbn [app]. destruct (Z.eq_dec b 0) as [->|Hb].
    + rewrite scan_zero_fst, !scan_zero_snd. destruct (IH false [] q) as [I1 I2].
      split; [exact I1|]. rewrite I2. destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
    + rewrite (scan_nz sk acc b (p ++ 0 :: q) Hb), (scan_nz sk acc b (p ++ [0]) Hb). apply IH.
Qed.

Lemma scan_pre : forall s P q, dbound s P ->
  fst (scan (ds_skip s) [] (firstn P (dW s) ++ q)) = fst (scan (dskp s P) [] q) /\
  snd (scan (ds_skip s) [] (firstn P (dW s) ++ q)) = drlp s P ++ snd (scan (dskp s P) [] q).
Proof using HG HJ O h junk.
  intros s P q (HP & HN). destruct P as [|P]; [split; reflexivity|].
  assert (HN' : nth_error (dW s) P = Some 0).
  { destruct HN as [H0|H0]; [discriminate|]. replace P with (S P - 1)%nat by lia. exact H0. }
  unfold drlp, dskp. cbn [Nat.eqb]. rewrite (firstn_nth_app _ _ _ HN'), <- app_assoc. cbn [app].
  exact (scan_app_z (firstn P (dW s)) (ds_skip s) [] q).
Qed.

Lemma scan_line : forall sk ln q, nozero ln ->
  fst (scan sk [] (ln ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk [] (ln ++ 0 :: q)) =
    (if (sk || Nat.ltb LINE_LIMIT (length ln))%bool then [] else [ln]) ++ snd (scan false [] q).
Proof using.
  intros sk ln q Hz. rewrite (scan_nz_app ln sk [] _ Hz). cbn [app]. rewrite scan_zero_fst, scan_zero_snd.
  split; [reflexivity|]. destruct (sk || Nat.ltb LINE_LIMIT (length ln))%bool; reflexivity.
Qed.

Lemma drl_line : forall s P Q, dbound s P -> (P <= Q < length (dW s))%nat -> nth_error (dW s) Q = Some 0 ->
  (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) ->
  drlp s (S Q) = drlp s P ++ (if (dskp s P || Nat.ltb LINE_LIMIT (Q - P))%bool then [] else [dline s P Q]) /\
  drlq s P = (if (dskp s P || Nat.ltb LINE_LIMIT (Q - P))%bool then [] else [dline s P Q]) ++ drlq s (S Q).
Proof using HG HJ O h junk.
  intros s P Q HB HPQ HQ HNZ.
  pose proof (dline_nz s P Q HNZ) as Hz. rewrite <- (dline_len s P Q HPQ). split.
  - unfold drlp at 1. rewrite (dW_pre_line s P Q (proj1 HPQ) HQ), (proj2 (scan_pre s P _ HB)).
    rewrite (proj2 (scan_line (dskp s P) (dline s P Q) [] Hz)). cbn [scan snd]. rewrite app_nil_r. reflexivity.
  - unfold drlq at 1. rewrite (dW_split s P Q (proj1 HPQ) HQ), (proj2 (scan_line (dskp s P) (dline s P Q) _ Hz)).
    reflexivity.
Qed.

Lemma drlq_0 : forall s, nozero (ds_u s) -> drlq s 0 = drl s.
Proof using.
  intros s Hz. unfold drlq, drl, dchunk, chunk.
  change (dskp s 0) with (ds_skip s). change (skipn 0 (dW s)) with (ds_u s ++ ddata s).
  rewrite (scan_nz_app (ds_u s) (ds_skip s) [] (ddata s) Hz). cbn [app].
  destruct (scan (ds_skip s) (ds_u s) (ddata s)) as [[a b] c]. cbn [snd].
  destruct (Nat.ltb LINE_LIMIT (length b)); reflexivity.
Qed.

Lemma drl_send : forall s P Q, dbound s P -> (P <= Q < length (dW s))%nat -> nth_error (dW s) Q = Some 0 ->
  (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) -> dskp s P = false -> (Q - P <= LINE_LIMIT)%nat ->
  drlp s (S Q) = drlp s P ++ [dline s P Q] /\ drlq s P = dline s P Q :: drlq s (S Q) /\ dskp s (S Q) = false.
Proof using HG HJ O h junk.
  intros s P Q HB HPQ HQ HNZ HK HL.
  destruct (drl_line s P Q HB HPQ HQ HNZ) as [E1 E2].
  rewrite HK, (proj2 (Nat.ltb_ge LINE_LIMIT (Q - P)) HL) in E1, E2. cbn [orb app] in E1, E2.
  split; [exact E1|]. split; [exact E2|reflexivity].
Qed.

Lemma drl_skip : forall s P Q, dbound s P -> (P <= Q < length (dW s))%nat -> nth_error (dW s) Q = Some 0 ->
  (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) ->
  dskp s P = true \/ (LINE_LIMIT < Q - P)%nat ->
  drlp s (S Q) = drlp s P /\ drlq s P = drlq s (S Q) /\ dskp s (S Q) = false.
Proof using HG HJ O h junk.
  intros s P Q HB HPQ HQ HNZ HK.
  destruct (drl_line s P Q HB HPQ HQ HNZ) as [E1 E2].
  assert (C : (dskp s P || Nat.ltb LINE_LIMIT (Q - P))%bool = true).
  { destruct HK as [E|E]; [rewrite E; reflexivity|]. apply orb_true_intro. right. apply Nat.ltb_lt. exact E. }
  rewrite C in E1, E2. cbn [app] in E1, E2. rewrite app_nil_r in E1.
  split; [exact E1|]. split; [exact E2|reflexivity].
Qed.

Lemma drl_end : forall s P, dbound s P -> (forall i, (P <= i)%nat -> nth_error (dW s) i <> Some 0) ->
  drlq s P = [] /\ scan (ds_skip s) [] (dW s) = (dskp s P, skipn P (dW s), drlp s P).
Proof using HG HJ O h junk.
  intros s P HB HNZ.
  assert (Hz : nozero (skipn P (dW s))).
  { apply nz_nth. intros i. rewrite nth_skipn. apply HNZ. lia. }
  assert (E : scan (dskp s P) [] (skipn P (dW s)) = (dskp s P, skipn P (dW s), [])).
  { rewrite <- (app_nil_r (skipn P (dW s))) at 1. rewrite (scan_nz_app (skipn P (dW s)) (dskp s P) [] [] Hz).
    reflexivity. }
  split.
  - unfold drlq. rewrite E. reflexivity.
  - destruct (scan_pre s P (skipn P (dW s)) HB) as [E1 E2]. rewrite firstn_skipn in E1, E2.
    rewrite E in E1, E2. cbn [fst snd] in E1, E2. rewrite app_nil_r in E2.
    rewrite <- E1, <- E2. destruct (scan (ds_skip s) [] (dW s)) as [[a b] c]. reflexivity.
Qed.

Lemma cb_prefix : forall mm a0 nn cs rest, rw_cells rsegs mm a0 [CB nn (cells_bytes cs ++ rest)] -> cells_wf cs ->
  rw_cells rsegs mm a0 cs.
Proof using HG HJ O h junk.
  intros mm a0 nn cs rest [[W B] (H0 & H1 & H)] Wc.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in W, B, H1, H. destruct W as [W _].
  rewrite app_nil_r in B. apply bytes_at_app in B as [B _].
  rewrite length_app, (cells_bytes_length cs Wc) in W.
  split; [split; [exact Wc | exact B]|]. split; [exact H0|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

Lemma cb_cut2 : forall mm a0 (b1 b2 : list byte), rw_cells rsegs mm a0 [CB (length b1 + length b2) (b1 ++ b2)] ->
  rw_cells rsegs mm a0 [CB (length b1) b1] /\ rw_cells rsegs mm (a0 + Z.of_nat (length b1)) [CB (length b2) b2].
Proof using Bm G HJ O h junk regs.
  intros mm a0 b1 b2 [[W B] Wr].
  apply (dr_cut mm a0 (a0 + Z.of_nat (length b1)) [CB (length b1) b1] [CB (length b2) b2]);
    [|cbn [cells_size csize]; lia].
  split; [split|].
  - cbn [app cells_wf cell_wf]. repeat split.
  - cbn [app cells_bytes cbytes] in B |- *. rewrite app_nil_r in B |- *. exact B.
  - cbn [app cells_size csize] in Wr |- *.
    replace (length b1 + (length b2 + 0))%nat with (length b1 + length b2 + 0)%nat by lia. exact Wr.
Qed.

Lemma cb_join2 : forall mm a0 (b1 b2 : list byte), rw_cells rsegs mm a0 [CB (length b1) b1] ->
  rw_cells rsegs mm (a0 + Z.of_nat (length b1)) [CB (length b2) b2] ->
  rw_cells rsegs mm a0 [CB (length b1 + length b2) (b1 ++ b2)].
Proof using Bm G HJ O h junk regs.
  intros mm a0 b1 b2 X1 X2.
  destruct (dr_join mm a0 (a0 + Z.of_nat (length b1)) [CB (length b1) b1] [CB (length b2) b2] X1 X2
              ltac:(cbn [cells_size csize]; lia)) as [[W B] Wr].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_app | exact I].
  - cbn [app cells_bytes cbytes] in B |- *. rewrite app_nil_r in B |- *. exact B.
  - cbn [app cells_size csize] in Wr |- *.
    replace (length b1 + length b2 + 0)%nat with (length b1 + (length b2 + 0))%nat by lia. exact Wr.
Qed.

Lemma ro_hi : forall a, 0x21624 <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof using Bm G HJ O h junk regs.
  intros a Ha. destruct (Mem.ro_addr rsegs (Z_to_bv 64 a)) eqn:X; [|reflexivity].
  apply ro_low in X. rewrite unsigned_lit in X by lia. exfalso. lia.
Qed.

Lemma img_apart : forall q k lo hi, 0 < k -> lo < hi -> (forall i, 0 <= i < k -> ~ in_img Bm (q + i)) ->
  (forall a, lo <= a < hi -> in_img Bm a) -> q + k <= lo \/ hi <= q.
Proof using HG HJ O h junk.
  intros q k lo hi Hk Hl NQ IA.
  destruct (Z_le_gt_dec (q + k) lo) as [Le|Gt]; [left; exact Le|].
  destruct (Z_le_gt_dec hi q) as [Le2|Gt2]; [right; exact Le2|].
  exfalso. apply (NQ (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia.
  apply IA. lia.
Qed.

Lemma firstn_bzs : forall n l, firstn n (bzs l) = bzs (firstn n l).
Proof using. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Definition DRB (s : dstate) (k : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (r0 : Z * list byte) (rs0 : list (Z * list byte)),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13a94) m1 (seg_rom segs)) md1 /\ RT R1 /\
    getr R1 9 = Z_to_bv 64 (dnum s - Z.of_nat k) /\ getr R1 18 = Z_to_bv 64 (XH + 192) /\
    getr R1 19 = Z_to_bv 64 (dnum s) /\ getr R1 20 = Z_to_bv 64 XH /\
    getr R1 21 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k) /\
    getr R1 23 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k) /\ getr R1 24 = Z_to_bv 64 1 /\
    getr R1 26 = Z_to_bv 64 (fst r0) /\ getr R1 27 = Z_to_bv 64 (fst r0 + ds_off s) /\
    rw_cells segs m1 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))] /\
    hl_recs (hs_pending h1) = r0 :: rs0 /\ Z.of_nat k < dnum s /\ 4096 <= ds_cap s - ulen s /\
    ds_eintr s = false /\
    bzs (firstn (Z.to_nat (dnum s)) (re_junk e1)) = ddata s /\
    relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 /\
    st_init_done A1 = true /\
    DPU L1 A1 s e1 h1 OUT1 (lines (ds_ref s) (firstn k (ddata s))) /\
    ro_agree segs m1 /\
    (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
    rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] /\
    entry_okw L1 A1 m1 e1 /\
    src_at Bm L1 A1 m1 HA h1 /\
    others_at Bm m1 j (re_fd e) fs os /\
    DSAME e1 h1 /\
    (re_cap e1 = ds_cap s /\ bzs (re_U e1) = ds_u s /\ re_skip e1 = (if ds_skip s then 1 else 0) /\
     keys_texts (re_keys e1) = ds_H s /\ ent_ka e1 = ds_ka s /\ hs_eintr h1 = (if ds_eintr s then 1 else 0) /\
     map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = ds_pend s /\ hs_off h1 = ds_off s /\
     hs_state h1 = feed (ds_ref s) (firstn k (ddata s)) /\
     hl_n (hs_expected h1) = ds_en s + Z.of_nat (length (lines (ds_ref s) (firstn k (ddata s)))) /\
     hl_cap (hs_expected h1) =
       pcapm (ds_en s) (ds_ecap s) (lines (ds_ref s) (firstn k (ddata s))) /\
     dwf s) /\
    (bzs PS = D ++ pstream s /\ ds_ref s = feed ST0 D /\ J1 (ds_u s) (ds_skip s) (ds_ref s) /\
     map snd (hl_recs (hs_expected h1)) =
       map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines ST0 (D ++ firstn k (ddata s))) /\
     firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
     hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
     ds_no s = NO + dtot D /\ bzs LB1 = with_nul (lines ST0 D) /\
     NoDup (ds_H s) /\ same_set (ds_H s) (upds (keys_texts (re_keys e)) (lines ST0 D)) /\
     Z.of_nat (length (ds_H s)) + Z.of_nat (length (pstream s)) < 2 ^ 26 /\
     ds_en s + Z.of_nat (length (pstream s)) < 2 ^ 27) /\
    DBLK L1 A1 e1 h1 OUT1 /\
    DGLB D m1 /\
    DOUT s L1 A1 m1 OUT1 junk1 LB1.

Lemma UB_cb_c8 : forall m a bs, rw_cells rsegs m a [CB 8 bs] ->
  rw_cells rsegs m a [C8 (Z_to_bv 64 (bytes_le_to_Z bs))].
Proof using Bm G HJ O h junk regs.
  intros m a bs [[Wf Bs] W]. cbn [cells_wf cell_wf] in Wf. destruct Wf as [HL _].
  assert (L8 : le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs).
  { unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia. rewrite <- HL. exact (sb_le_rt bs). }
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes] in Bs |- *. rewrite L8. exact Bs.
  - exact W.
Qed.

Lemma read_a : forall s c, DF s c -> ds_eintr s = false -> ds_pend s <> [] -> SR segs c (DRB s 0).
Proof using All.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RT1 & G10 & G11 & G20 & GR & DC1) E P.
  pose proof DC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  rewrite E in L6c. cbv beta iota in L6c.
  assert (HRx : exists r0 rs0, hl_recs (hs_pending h1) = r0 :: rs0).
  { destruct (hl_recs (hs_pending h1)) as [|r0 rs0] eqn:HR0; [|exists r0, rs0; first [reflexivity | exact HR0]].
    exfalso. apply P. rewrite <- L7c. rewrite ?HR0. reflexivity. }
  destruct HRx as (r0 & rs0 & HR).
  assert (PE : ds_pend s = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0) by (rewrite <- L7c, HR; reflexivity).
  assert (OFF : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
  { destruct S8 as [(RN & _)|(r1 & rs1 & RE1 & RO')]; [rewrite HR in RN; discriminate|].
    rewrite HR in RE1. injection RE1 as <- <-. exact RO'. }
  assert (ULEN : ulen s = re_used e1) by (unfold ulen; rewrite <- L2c; unfold bzs; rewrite length_map; exact K7).
  assert (DH : dhead s = bzs (snd r0)) by (unfold dhead; rewrite PE; reflexivity).
  assert (GR' : 4096 <= re_cap e1 - re_used e1) by (rewrite L1c, <- ULEN; exact GR).
  set (N := Z.min (Z.of_nat (length (snd r0)) - hs_off h1) (re_cap e1 - re_used e1)).
  assert (NDEF : N = Z.min (Z.of_nat (length (snd r0)) - hs_off h1) (re_cap e1 - re_used e1)) by reflexivity.
  assert (DN : dnum s = N).
  { unfold dnum. rewrite DH, <- L1c, ULEN, <- L8c, NDEF. unfold bzs. rewrite length_map. reflexivity. }
  assert (NR : 0 < N /\ N <= re_cap e1 - re_used e1 /\ N <= Z.of_nat (length (snd r0)) - hs_off h1)
    by (rewrite NDEF; clear - OFF GR'; lia).
  assert (BUF : 0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (blocks L1 A1) /\ fresh_block Bm (re_buf e1) (re_cap e1) /\
                Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
                rw_cells segs m1 (re_buf e1) [CB (Z.to_nat (re_cap e1)) (re_U e1 ++ re_junk e1)]).
  { destruct K10 as [(C0 & _ & U0)|BB]; [clear - C0 U0 GR'; lia | exact BB]. }
  destruct BUF as (Cp & BI & BF & BJ & BC).
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  assert (CV : re_cap e1 = 8192 \/ re_cap e1 = 16384) by (clear - K6 Cp; lia).
  pose proof S6 as (P1 & P2 & P3 & _ & _ & P6).
  assert (PN : 1 <= hl_n (hs_pending h1) <= hl_cap (hs_pending h1) /\ hl_cap (hs_pending h1) < 2 ^ 30).
  { pose proof P2 as P2'. unfold hl_n in P2' |- *. rewrite HR in P2' |- *. cbn [length] in P2' |- *.
    clear - P2'. lia. }
  assert (PA : 0 < hl_cap (hs_pending h1) /\ In (hl_v (hs_pending h1), 16 * hl_cap (hs_pending h1)) (blocks L1 A1) /\
               rw_cells segs m1 (hl_v (hs_pending h1)) [CB (Z.to_nat (16 * hl_cap (hs_pending h1)))
                 (concat (map text_rec (hl_recs (hs_pending h1))) ++ hl_junk (hs_pending h1))]).
  { destruct P3 as [(C0 & _)|(Cq & PIq & _ & _ & PCq)]; [clear - C0 PN; lia|].
    split; [exact Cq|]. split; [exact PIq | exact PCq]. }
  destruct PA as (PCp & PIn & PCc).
  pose proof (blk_rng _ _ _ _ _ _ M1 PIn) as PBR.
  pose proof (blk_align _ _ _ _ _ _ M1 PIn) as PAL.
  assert (T0 : In (fst r0, Z.of_nat (length (snd r0)) + 1) (blocks L1 A1) /\
               rw_cells segs m1 (fst r0) [CB (length (snd r0) + 1) (snd r0 ++ [Z_to_bv 8 0])]).
  { pose proof (proj1 (Forall_forall _ _) P6 r0 ltac:(rewrite HR; left; reflexivity)) as (T1 & _ & T3 & _).
    split; [exact T1 | exact T3]. }
  destruct T0 as (TI & TC).
  pose proof (blk_rng _ _ _ _ _ _ M1 TI) as TBR.
  pose proof BK1 as (ND & GI1 & _).
  assert (EBUF : entry_blocks e1 =
                 re_buf e1 :: ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1))).
  { unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by (clear - Cp; lia). reflexivity. }
  rewrite EBUF in ND. apply NoDup_ListNoDup in ND.
  apply List.NoDup_cons_iff in ND as [NG ND]. apply List.NoDup_cons_iff in ND as [NOUT ND].
  cbn [app] in ND. apply List.NoDup_cons_iff in ND as [NBUF _].
  assert (GNB : G <> re_buf e1) by (intros X; apply NG; right; rewrite X; left; reflexivity).
  assert (ONB : OUT1 <> re_buf e1) by (intros X; apply NOUT; rewrite X; left; reflexivity).
  assert (ENB : forall q, In q ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1)) ->
                q <> re_buf e1) by (intros q Hq X; apply NBUF; rewrite <- X; apply in_or_app; left; exact Hq).
  assert (HSNB : forall q, In q (hs_blocks h1) -> q <> re_buf e1)
    by (intros q Hq X; apply NBUF; rewrite <- X; apply in_or_app; right; exact Hq).
  set (Pa := fun a => 0 <= a < 2 ^ 64 /\
    outside [(re_buf e1 + re_used e1, re_buf e1 + re_used e1 + N); (S0 - 144 + 32, S0 - 144 + 40)] a).
  assert (BLKP : forall q k a, In (q, k) (blocks L1 A1) -> q <> re_buf e1 -> q <= a < q + k -> Pa a).
  { intros q k a Hq NE Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Hq BI NE) as DJ.
    unfold Pa. cbn [outside]. clear - Ha QR DJ BR F1 F4 NR K7.
    split; [lia | split; [lia | split; [lia | exact I]]]. }
  assert (IMGP : forall a, in_img Bm a -> Pa a).
  { intros a Ha. pose proof (img_lo a Ha) as IL. unfold Pa. cbn [outside]. split; [clear - IL; lia|].
    split; [|split; [clear - IL F1 F3; lia | exact I]].
    intros X. apply (blk_noimg _ _ _ _ _ _ (a - re_buf e1) M1 BI); [clear - X NR K7; lia|].
    replace (re_buf e1 + (a - re_buf e1)) with a by ring. exact Ha. }
  assert (HIP : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (S0 - 144 + 32 <= a < S0 - 144 + 40) -> Pa a).
  { intros a Ha Hn. unfold Pa. cbn [outside]. clear - Ha Hn BR NR K7.
    split; [lia | split; [lia | split; [exact Hn | exact I]]]. }
  assert (TNB : fst r0 <> re_buf e1).
  { apply HSNB. apply hb_pend. unfold list_blocks. apply in_or_app. right. rewrite HR. left. reflexivity. }
  assert (PNB : hl_v (hs_pending h1) <> re_buf e1).
  { apply HSNB. apply hb_pend. unfold list_blocks. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq (hl_cap (hs_pending h1)) 0)) by (clear - PCp; lia). left. reflexivity. }
  pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 BI TI (fun X => TNB (eq_sym X))) as DJ1.
  pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 BI PIn (fun X => PNB (eq_sym X))) as DJ3.
  assert (DJ2 : re_buf e1 + re_cap e1 <= HA \/ HA + 64 <= re_buf e1).
  { apply img_apart; [clear - Cp; lia | clear - Cp; lia | intros i Hi; exact (blk_noimg _ _ _ _ _ _ i M1 BI Hi) |].
    intros a Ha.
    exact (proj1 (GRP a ltac:(clear - Ha HJ; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))). }
  assert (NRWI : forall a0 cs, rw_cells rsegs m1 a0 cs -> 0x21624 <= a0 ->
                 rw_cells rsegs (normalize rsegs m1) a0 cs).
  { intros a0 cs X Ha0. apply (rw_cells_normalize rsegs m1 a0 cs RO1r X). intros i Hi.
    pose proof (rw_cells_bound _ _ _ _ X) as RB. apply ro_hi. clear - RB Hi Ha0. lia. }
  assert (NRWB : forall a0 cs q k, rw_cells rsegs m1 a0 cs -> In (q, k) (blocks L1 A1) -> q <= a0 ->
                 a0 + Z.of_nat (cells_size cs) <= q + k -> rw_cells rsegs (normalize rsegs m1) a0 cs).
  { intros a0 cs q k X Hq L0 L0'. apply (rw_cells_normalize rsegs m1 a0 cs RO1r X). intros i Hi.
    pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    apply (ro_addr_out Bm SEGS); [clear - QR Hi L0 L0' F4; lia|].
    replace (a0 + i) with (q + (a0 + i - q)) by ring. apply (blk_noimg _ _ _ _ _ _ _ M1 Hq). clear - Hi L0 L0'. lia. }
  rewrite L6c in S1.
  assert (HSc : rw_cells rsegs (normalize rsegs m1) (XH + 128)
                  [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1)); C4 (Z_to_bv 64 (hs_closed h1));
                   C4 (Z_to_bv 64 0)]).
  { replace (XH + 128) with HA by (clear - HJ; unfold DR_TU, G_S, SRC_SIZE; lia). apply NRWI; [rewrite <- SEGS; exact S1|].
    clear - HJ. unfold G_S, SRC_SIZE. lia. }
  assert (HPc : rw_cells rsegs (normalize rsegs m1) (XH + 144)
                  [C8 (Z_to_bv 64 (hl_v (hs_pending h1))); C4 (Z_to_bv 64 (hl_n (hs_pending h1)));
                   C4 (Z_to_bv 64 (hl_cap (hs_pending h1)))]).
  { replace (XH + 144) with (HA + 16) by (clear - HJ; unfold DR_TU, G_S, SRC_SIZE; lia).
    apply NRWI; [rewrite <- SEGS; exact P1|]. clear - HJ. unfold G_S, SRC_SIZE. lia. }
  pose proof (proj1 (dr_cut _ _ _ [C8 (Z_to_bv 64 (hl_v (hs_pending h1))); C4 (Z_to_bv 64 (hl_n (hs_pending h1)))]
                       [C4 (Z_to_bv 64 (hl_cap (hs_pending h1)))] HPc eq_refl)) as HPc2.
  assert (HOc : rw_cells rsegs (normalize rsegs m1) (XH + 160)
                  [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1));
                   C4 (Z_to_bv 64 (hs_overlong h1))]).
  { replace (XH + 160) with (HA + 32) by (clear - HJ; unfold DR_TU, G_S, SRC_SIZE; lia).
    apply NRWI; [rewrite <- SEGS; exact S7|]. clear - HJ. unfold G_S, SRC_SIZE. lia. }
  pose proof (proj1 (dr_cut _ _ _ [C8 (Z_to_bv 64 (hs_off h1))]
                       [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1));
                        C4 (Z_to_bv 64 (hs_overlong h1))] HOc eq_refl)) as HOc2.
  assert (HR0 : rw_cells rsegs m1 (hl_v (hs_pending h1))
                  [C8 (Z_to_bv 64 (fst r0)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))]).
  { apply (cb_prefix m1 _ (Z.to_nat (16 * hl_cap (hs_pending h1))) _
             (concat (map text_rec rs0) ++ hl_junk (hs_pending h1))); [|cbn; repeat split].
    pose proof PCc as PC2. rewrite SEGS, HR in PC2.
    change (concat (map text_rec (r0 :: rs0))) with
      ((le8 (Z_to_bv 64 (fst r0)) ++ le8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))) ++ concat (map text_rec rs0))
      in PC2.
    cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- !app_assoc in PC2 |- *. exact PC2. }
  assert (HRc : rw_cells rsegs (normalize rsegs m1) (hl_v (hs_pending h1))
                  [C8 (Z_to_bv 64 (fst r0)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))])
    by (apply (NRWB _ _ _ _ HR0 PIn); [clear - PCp; lia | cbn [cells_size csize]; clear - PCp; lia]).
  destruct FR1 as (j0 & j1 & j2 & j4 & FRc). rewrite SEGS in FRc.
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 32) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001)]
              ([CB 8 j4] ++ SAVED) FRc ltac:(cbn [cells_size csize]; clear - j0; lia)) as [FA FB].
  destruct (dr_cut m1 (S0 - 144 + 32) (S0 - 144 + 40) [CB 8 j4] SAVED FB ltac:(cbn [cells_size csize]; clear - j4; lia))
    as [FW FS].
  assert (HWc : rw_cells rsegs (normalize rsegs m1) (S0 - 144 + 32) [C8 (Z_to_bv 64 (bytes_le_to_Z j4))])
    by (apply NRWI; [exact (UB_cb_c8 _ _ _ FW) | clear - F1 F3; lia]).
  set (src := firstn (Z.to_nat N) (skipn (Z.to_nat (hs_off h1)) (snd r0))).
  assert (LSRC : length src = Z.to_nat N).
  { unfold src. rewrite length_firstn, length_skipn. clear - NR OFF. lia. }
  assert (BSRC : bytes_at rsegs m1 (fst r0 + hs_off h1) src).
  { pose proof TC as [[_ TB] _]. rewrite SEGS in TB. cbn [cells_bytes cbytes] in TB. rewrite app_nil_r in TB.
    apply bytes_at_app in TB as [TB _].
    assert (TB2 : bytes_at rsegs m1 (fst r0)
                    (firstn (Z.to_nat (hs_off h1)) (snd r0) ++ skipn (Z.to_nat (hs_off h1)) (snd r0)))
      by (rewrite firstn_skipn; exact TB).
    apply bytes_at_app in TB2 as [_ TB2]. rewrite length_firstn in TB2.
    replace (fst r0 + Z.of_nat (Nat.min (Z.to_nat (hs_off h1)) (length (snd r0)))) with (fst r0 + hs_off h1) in TB2
      by (clear - OFF; lia).
    assert (TB3 : bytes_at rsegs m1 (fst r0 + hs_off h1)
                    (src ++ skipn (Z.to_nat N) (skipn (Z.to_nat (hs_off h1)) (snd r0))))
      by (unfold src; rewrite firstn_skipn; exact TB2).
    apply bytes_at_app in TB3 as [TB3 _]. exact TB3. }
  assert (HD1 : rw_cells rsegs m1 (re_buf e1 + re_used e1) [CB (Z.to_nat N) (firstn (Z.to_nat N) (re_junk e1))] /\
                rw_cells rsegs m1 (re_buf e1 + re_used e1 + N)
                  [CB (length (skipn (Z.to_nat N) (re_junk e1))) (skipn (Z.to_nat N) (re_junk e1))]).
  { pose proof BC as BC'. rewrite SEGS in BC'.
    replace (Z.to_nat (re_cap e1)) with (length (re_U e1) + length (re_junk e1))%nat in BC'
      by (clear - K7 BJ GR'; lia).
    destruct (cb_cut2 m1 _ _ _ BC') as [_ HD0]. rewrite K7 in HD0.
    assert (X : rw_cells rsegs m1 (re_buf e1 + re_used e1)
                  [CB (length (firstn (Z.to_nat N) (re_junk e1)) + length (skipn (Z.to_nat N) (re_junk e1)))
                      (firstn (Z.to_nat N) (re_junk e1) ++ skipn (Z.to_nat N) (re_junk e1))])
      by (rewrite <- length_app, firstn_skipn; exact HD0).
    destruct (cb_cut2 m1 _ _ _ X) as [X1 X2].
    assert (LF : length (firstn (Z.to_nat N) (re_junk e1)) = Z.to_nat N)
      by (rewrite length_firstn; clear - BJ NR; lia).
    rewrite LF in X1, X2.
    replace (re_buf e1 + re_used e1 + Z.of_nat (Z.to_nat N)) with (re_buf e1 + re_used e1 + N) in X2
      by (clear - NR; lia).
    split; assumption. }
  assert (HDc : rw_cells rsegs (normalize rsegs m1) (re_buf e1 + re_used e1)
                  [CB (Z.to_nat N) (firstn (Z.to_nat N) (re_junk e1))])
    by (apply (NRWB _ _ _ _ (proj1 HD1) BI); [clear - K7; lia | cbn [cells_size csize]; clear - NR K7; lia]).
  destruct RT1 as ((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G10, G11, G20. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply (dr_data MCP) with (sfd := hs_fd h1) (op := hs_open h1) (cl := hs_closed h1)
      (pv := hl_v (hs_pending h1)) (pn := hl_n (hs_pending h1)) (off := hs_off h1) (ta := fst r0)
      (tl := Z.of_nat (length (snd r0))) (w := Z_to_bv 64 (bytes_le_to_Z j4)) (src := src)
      (dj := firstn (Z.to_nat N) (re_junk e1)).
    - exact HSc.
    - exact HPc2.
    - exact HOc2.
    - exact HRc.
    - exact HWc.
    - exact (bytes_at_normalize rsegs m1 _ _ RO1r BSRC).
    - rewrite LSRC, <- NDEF. clear - NR. lia.
    - exact HDc.
    - apply mem_inv_normalize.
    - clear - F1 F3. lia.
    - clear - HJ. unfold DR_TU. lia.
    - unfold DR_TU. clear - HJ. lia.
    - clear - PN. lia.
    - exact OFF.
    - clear - TBR F4. lia.
    - clear - GR' CV K7. lia.
    - clear - TBR. lia.
    - clear - TBR F4. lia.
    - clear - PBR. lia.
    - clear - PAL. Z.div_mod_to_equations. lia.
    - clear - BR K7. lia.
    - clear - BR F4. lia.
    - clear - DJ1 K7. lia.
    - clear - DJ2 K7. unfold DR_TU, G_S, SRC_SIZE in *. lia.
    - clear - DJ3 PCp K7. lia.
    - clear - BR F1 F4. lia.
    - clear - TBR F1 F4. lia. }
  intros ms (can & (s0' & HQ & REL & ROS) & EQ).
  destruct HQ as (m' & x1' & x10' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x5' & x6' & x7' & x28' & x29'
    & x30' & x31' & -> & MU & WM & _ & HB & _ & HW2).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2].
  rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HB) as HB2.
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HW2) as HW2m.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  assert (MSm : msame Pa m1 m2) by exact (msame_munch _ _ _ MU2 WM2s).
  apply SR_ret.
  exists R2, L1, A1, m2, md1,
    (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1)
        (re_pad2 e1) (re_keys e1) (re_U e1) (src ++ skipn (Z.to_nat N) (re_junk e1))),
    h1, OUT1, junk1, LB1, D, r0, rs0.
  split; [reflexivity|].
  split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
  split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; rewrite DN;
          change (Z.of_nat 0) with 0; rewrite Z.sub_0_r; reflexivity|].
  split; [rgw X2|].
  split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; rewrite DN; reflexivity|].
  split; [rgw X2|].
  split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; rewrite <- L8c;
          change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
  split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; rewrite <- L8c;
          change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
  split; [rgw X2|].
  split; [rgw X2|].
  split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; rewrite <- L8c; reflexivity|].
  split; [rewrite SEGS; exact HW2m|].
  split; [exact HR|].
  split; [rewrite DN; clear - NR; lia|].
  split; [exact GR|].
  split; [exact E|].
  split.
  { cbn [re_junk]. rewrite DN, <- LSRC, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
    unfold ddata. rewrite DN, DH, <- L8c, skipn_bzs, firstn_bzs. reflexivity. }
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU2); [exact WM2s | exact GEI |].
    intros a Ha.
    assert (Hs : (S0 - 144 + 32 <= a < S0 - 144 + 40) \/ ~ (S0 - 144 + 32 <= a < S0 - 144 + 40)) by (clear - Ha; lia).
    destruct Hs as [Hs|Hs].
    { right; left. unfold spZ. assert (KD : DRAIN_K = 8512) by reflexivity. rewrite KD.
      assert (E0 : bv_unsigned (YK11.getr regs 2) = S0) by reflexivity. rewrite E0. clear - Hs F1. lia. }
    destruct (Z_lt_le_dec a (re_buf e1 + re_used e1)) as [La|La];
      [left; cbn [outside]; split; [clear - La; lia | split; [exact Hs | exact I]]|].
    destruct (Z_lt_le_dec a (re_buf e1 + re_used e1 + N)) as [Lb|Lb];
      [|left; cbn [outside]; split; [clear - Lb NDEF; lia | split; [exact Hs | exact I]]].
    right; right; right; right.
    split.
    { intros X. apply (blk_noimg _ _ _ _ _ _ (a - re_buf e1) M1 BI); [clear - La Lb NR K7; lia|].
      replace (re_buf e1 + (a - re_buf e1)) with a by ring. exact X. }
    split; [exists (re_buf e1), (re_cap e1); split; [exact BI | clear - La Lb NR K7; lia]|].
    intros p n i Hp Hp1 NF Hi _ Ea.
    pose proof RP1 as (_ & _ & _ & _ & _ & AD1 & _).
    pose proof (AD1 p n Hp Hp1 NF) as AE.
    assert (Q1 : In (ptr_addr L p, n) (blocks L1 A1))
      by (apply CF.gestures_end_b.blocks_In2; exists p; split; [exact AE | exact Hp1]).
    destruct (Z.eq_dec (ptr_addr L p) (re_buf e1)) as [EQb|NEb].
    - assert (Q0 : In (re_buf e1, n) (blocks L A))
        by (rewrite <- EQb; apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
      destruct (untouched s L1 A1 m1 e1 h1 OUT1 junk1 LB1 (re_buf e1) n BK1 OU1 Q0 ltac:(clear - Hi; lia)
                  ltac:(rewrite <- EQb; exact NF)) as [U1 _].
      apply U1. rewrite EBUF. left. reflexivity.
    - destruct (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Q1 BI NEb) as [X|X];
        clear - X Hi Ea La Lb NR K7; lia. }
  split; [exact IN1|].
  split.
  { destruct TR1 as (tp & qd & a & RC & RF). exists tp, qd, a. cbn [firstn]. rewrite lines_nil.
    cbn [pushes_run fst snd]. rewrite app_nil_r. destruct a. split; [exact RC | exact RF]. }
  split; [rewrite SEGS; exact RO2|].
  split.
  { exists j0, j1, j2, (le8 (Z_to_bv 64 (XH + 144))). rewrite SEGS.
    apply (dr_join m2 (S0 - 144) (S0 - 144 + 32) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001)]
             ([CB 8 (le8 (Z_to_bv 64 (XH + 144)))] ++ SAVED)); [| | cbn [cells_size csize]; clear - j0; lia].
    - rewrite <- SEGS. eapply rw_tr; [exact MSm | rewrite SEGS; exact FA |]. intros a Ha.
      cbn [cells_size csize] in Ha. apply HIP; clear - Ha F1 F2 F3; lia.
    - apply (dr_join m2 (S0 - 144 + 32) (S0 - 144 + 40) [CB 8 (le8 (Z_to_bv 64 (XH + 144)))] SAVED);
        [exact (dr_c8_cb _ _ _ HW2m) | | cbn [cells_size csize]; clear - j0; lia].
      rewrite <- SEGS. eapply rw_tr; [exact MSm | rewrite SEGS; exact FS |]. intros a Ha.
      cbn [cells_size csize dr_saved] in Ha. apply HIP; clear - Ha F1 F2 F3; lia. }
  split.
  { eapply rw_tr; [exact MSm | exact SAC1 |]. intros a Ha. apply (BLKP G SRC_TABLE a GI1 GNB).
    cbn [cells_size csize] in Ha. unfold SRC_TABLE, SRC_ENTRY. clear - Ha F6 F7. lia. }
  split.
  { apply (entry_okw_buf L1 A1 L1 A1 m1 m2 e1 Pa (re_buf e1) (re_cap e1) (src ++ skipn (Z.to_nat N) (re_junk e1))
             MSm EK1).
    - intros q k Hq _. exact Hq.
    - intros q k a Hq Hk Ha. apply (BLKP q k a Hq); [|exact Ha].
      destruct Hk as [->|Hk].
      + destruct (Z.eqb_spec (re_hp e1) 0) as [Z0|NZ].
        * exfalso. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR. clear - QR Z0. lia.
        * apply ENB. apply in_or_app. left. rewrite ?(proj2 (Z.eqb_neq _ 0) NZ). left. reflexivity.
      + apply ENB. apply in_or_app. right. exact Hk.
    - exact CV.
    - clear - GR'. lia.
    - exact BI.
    - exact BF.
    - rewrite length_app, LSRC, length_skipn. clear - BJ NR. lia.
    - assert (BU1 : rw_cells rsegs m1 (re_buf e1) [CB (length (re_U e1)) (re_U e1)]).
      { pose proof BC as BC'. rewrite SEGS in BC'.
        replace (Z.to_nat (re_cap e1)) with (length (re_U e1) + length (re_junk e1))%nat in BC'
          by (clear - K7 BJ GR'; lia).
        exact (proj1 (cb_cut2 m1 _ _ _ BC')). }
      assert (BU2 : rw_cells rsegs m2 (re_buf e1) [CB (length (re_U e1)) (re_U e1)]).
      { rewrite <- SEGS. eapply rw_tr; [exact MSm | rewrite SEGS; exact BU1 |]. intros a Ha.
        cbn [cells_size csize] in Ha. unfold Pa. cbn [outside]. clear - Ha K7 BR F1 F4 GR'.
        split; [lia | split; [lia | split; [lia | exact I]]]. }
      assert (BT2 : rw_cells rsegs m2 (re_buf e1 + re_used e1 + Z.of_nat (length src))
                      [CB (length (skipn (Z.to_nat N) (re_junk e1))) (skipn (Z.to_nat N) (re_junk e1))]).
      { rewrite LSRC. replace (re_buf e1 + re_used e1 + Z.of_nat (Z.to_nat N)) with (re_buf e1 + re_used e1 + N)
          by (clear - NR; lia).
        rewrite <- SEGS. eapply rw_tr; [exact MSm | rewrite SEGS; exact (proj2 HD1) |]. intros a Ha.
        cbn [cells_size csize] in Ha. rewrite length_skipn in Ha. unfold Pa. cbn [outside].
        clear - Ha K7 BR F1 F4 BJ NR GR'. split; [lia | split; [lia | split; [lia | exact I]]]. }
      assert (BS : rw_cells rsegs m2 (re_buf e1 + re_used e1) [CB (length src) src]) by (rewrite LSRC; exact HB2).
      pose proof (cb_join2 m2 _ src _ BS BT2) as BSR.
      rewrite <- length_app, <- K7 in BSR.
      pose proof (cb_join2 m2 _ (re_U e1) _ BU2 BSR) as BALL.
      rewrite SEGS.
      replace (Z.to_nat (re_cap e1)) with (length (re_U e1) + length (src ++ skipn (Z.to_nat N) (re_junk e1)))%nat
        by (rewrite length_app, LSRC, length_skipn; clear - K7 BJ NR GR'; lia).
      exact BALL. }
  split.
  { eapply src_at_tr0; [exact MSm | exact SR1 | | intros q k Hq _; exact Hq |].
    - intros a Ha. apply IMGP.
      exact (proj1 (GRP a ltac:(clear - Ha HJ; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    - intros q k a Hq Hb Ha. exact (BLKP q k a Hq (HSNB q Hb) Ha). }
  split.
  { eapply others_at_tr; [exact MSm | exact OT1 |]. intros i a Hi _ Ha. apply IMGP.
    exact (proj1 (GRP a ltac:(clear - Ha Hi; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))). }
  split; [exact SM1|].
  split.
  { split; [exact L1c|]. split; [exact L2c|]. split; [exact L3c|]. split; [exact L4c|]. split; [exact L5c|].
    split; [rewrite E; exact L6c|]. split; [exact L7c|]. split; [exact L8c|]. split; [exact L9c|].
    split; [rewrite L10c; change (Z.of_nat (length (lines (ds_ref s) (firstn 0 (ddata s))))) with 0; ring|].
    split; [exact L11c | exact WF1]. }
  split.
  { split; [exact H1h|]. split; [exact H2h|]. split; [exact H3h|].
    split; [cbn [firstn]; rewrite app_nil_r; exact H4h|].
    split; [exact H5h|]. split; [exact H6h|]. split; [exact H7h|]. split; [exact H8h|]. split; [exact H9h|].
    split; [exact H10h|]. split; [exact H11h | exact H12h]. }
  split; [exact BK1|].
  split.
  { destruct GL1 as (GC1 & GC2 & GC3 & GC4 & (ev1 & GC5)).
    split; [eapply rw_tr; [exact MSm | exact GC1 |]; intros a Ha; apply IMGP; cbn [cells_size csize] in Ha;
            exact (proj1 (GCP a ltac:(clear - Ha; lia)))|].
    split; [eapply rw_tr; [exact MSm | exact GC2 |]; intros a Ha; apply IMGP; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [eapply rw_tr; [exact MSm | exact GC3 |]; intros a Ha; apply IMGP; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [eapply rw_tr; [exact MSm | exact GC4 |]; intros a Ha; apply IMGP; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    exists ev1. eapply rw_tr; [exact MSm | exact GC5 |]. intros a Ha. apply IMGP. apply GEI.
    cbn [cells_size csize] in Ha. clear - Ha. lia. }
  destruct OU1 as (OFa & OTa). split.
  - intros LV. destruct (OFa LV) as (OC & OE & OCP & OB). split.
    + eapply rw_tr; [exact MSm | exact OC |]. intros a Ha. apply IMGP. cbn [cells_size csize] in Ha.
      exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    + split; [exact OE|]. split; [exact OCP|]. intros Cq. destruct (OB Cq) as (OI & OBy). split; [exact OI|].
      eapply by_tr; [exact MSm | exact OBy |]. intros a Ha. apply (BLKP OUT CAP a OI); [rewrite <- OE; exact ONB|].
      destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; [clear - Cq C0; lia|].
      rewrite length_app in Ha. clear - Ha LO LJ. lia.
  - intros LV. destruct (OTa LV) as (OC & OZ). split.
    + eapply rw_tr; [exact MSm | exact OC |]. intros a Ha. apply IMGP. cbn [cells_size csize] in Ha.
      exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    + destruct OZ as [OZ|(Pp & NL & OI & OFr & OBy & LJ)]; [left; exact OZ | right].
      split; [exact Pp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OFr|]. split; [|exact LJ].
      eapply by_tr; [exact MSm | exact OBy |]. intros a Ha. apply (BLKP OUT1 (ds_ocap s) a OI ONB).
      assert (LO : Z.of_nat (length O) = NO).
      { destruct OUTD as [(_ & _ & N0 & OE0)|(_ & _ & _ & _ & _ & LO & _)];
          [rewrite OE0; cbn [length]; clear - N0; lia | exact LO]. }
      assert (LLB : Z.of_nat (length LB1) = dtot D).
      { unfold dtot. rewrite <- H8h. unfold bzs. rewrite length_map. reflexivity. }
      rewrite !length_app in Ha. clear - Ha LO LLB H7h LJ. lia.
Qed.

Lemma rbl_firstn_snoc : forall {T : Type} (l : list T) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof using.
  intros T l. induction l as [|y l IH]; intros [|k] x H; cbn in H; try discriminate.
  - injection H as <-. reflexivity.
  - cbn [firstn app]. f_equal. apply IH. exact H.
Qed.

Lemma rbl_split_nth : forall {T : Type} (l : list T) i d, (i < length l)%nat ->
  l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof using.
  intros T l. induction l as [|y l IH]; intros [|i] d H; cbn [length] in H; try (exfalso; clear - H; lia).
  - reflexivity.
  - cbn [firstn nth skipn app]. f_equal. apply IH. clear - H. lia.
Qed.

Lemma rbl_firstn_mid : forall {T : Type} (b1 b2 : list T) x, firstn (S (length b1)) (b1 ++ x :: b2) = b1 ++ [x].
Proof using. intros T b1. induction b1 as [|y b1 IH]; intros b2 x; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma rbl_firstn_len : forall {T : Type} (b1 l : list T), firstn (length b1) (b1 ++ l) = b1.
Proof using. intros T b1. induction b1 as [|y b1 IH]; intros l; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma rbl_lines_le : forall d st, (length (lines st d) <= length d)%nat.
Proof using.
  induction d as [|x d IH]; intros st; [rewrite lines_nil; apply Nat.le_refl|].
  rewrite lines_cons. destruct (snd (step st x)); cbn [length]; [apply le_n_S | apply le_S]; apply IH.
Qed.

Lemma rbl_bzs_inv : forall l, map (Z_to_bv 8) (bzs l) = l.
Proof using.
  intros l. unfold bzs. rewrite map_map. induction l as [|x l IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  apply bv_eq. unfold bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma rbl_model : forall s D k b, ds_ref s = feed ST0 D -> nth_error (ddata s) k = Some b ->
  feed (ds_ref s) (firstn (S k) (ddata s)) = fst (step (feed (ds_ref s) (firstn k (ddata s))) b) /\
  lines (ds_ref s) (firstn (S k) (ddata s)) = lines (ds_ref s) (firstn k (ddata s)) ++
    match snd (step (feed (ds_ref s) (firstn k (ddata s))) b) with Some l => [l] | None => [] end /\
  lines ST0 (D ++ firstn (S k) (ddata s)) = lines ST0 (D ++ firstn k (ddata s)) ++
    match snd (step (feed (ds_ref s) (firstn k (ddata s))) b) with Some l => [l] | None => [] end.
Proof using.
  intros s D k b HD EB. rewrite (rbl_firstn_snoc _ _ _ EB).
  assert (FK : feed ST0 (D ++ firstn k (ddata s)) = feed (ds_ref s) (firstn k (ddata s)))
    by (rewrite feed_app, HD; reflexivity).
  assert (LB : forall st, lines st [b] = match snd (step st b) with Some l => [l] | None => [] end).
  { intros st. rewrite lines_cons. destruct (snd (step st b)); rewrite lines_nil; reflexivity. }
  split; [rewrite feed_app, feed_cons, feed_nil; reflexivity|].
  split; [rewrite lines_app, LB; reflexivity|].
  rewrite app_assoc, lines_app, LB, FK. reflexivity.
Qed.

Lemma pcapm_app : forall l1 l2 n cp, pcapm n cp (l1 ++ l2) = pcapm (n + Z.of_nat (length l1)) (pcapm n cp l1) l2.
Proof using Bm G HJ O h junk regs.
  induction l1 as [|l l1 IH]; intros l2 n cp.
  - cbn [app length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - assert (C : forall n0 c0 ls, pcapm n0 c0 (l :: ls) = pcapm (n0 + 1) (push_cap n0 c0) ls).
    { intros n0 c0 ls. unfold pcapm at 1. cbn [pushes_run fst snd]. apply pushes_run_m. }
    rewrite <- app_comm_cons, !C, IH.
    replace (n + 1 + Z.of_nat (length l1)) with (n + Z.of_nat (length (l :: l1))) by (cbn [length]; lia).
    reflexivity.
Qed.

Lemma rbl_ddata_len : forall s, dwf s -> length (ddata s) = Z.to_nat (dnum s).
Proof using.
  intros s (W0 & W1). unfold ddata, dnum, dhead in *. rewrite length_firstn, length_skipn.
  destruct (ds_pend s) as [|r rs] eqn:Ep.
  - cbn [length]. clear - W0. lia.
  - specialize (W1 r rs ltac:(first [exact Ep | reflexivity])). clear - W0 W1. lia.
Qed.

Lemma rbl_rng : forall a lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof using. intros a lo hi. clear - a lo hi. lia. Qed.

Lemma rbl_nd_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof using.
  induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
  cbn [app] in H. apply List.NoDup_cons_iff in H as [NI ND].
  destruct H1 as [<-|H1]; [apply NI; apply in_or_app; right; exact H2 | exact (IH l2 x ND H1 H2)].
Qed.

Lemma rbl_nd_out : forall (pre mid post : list Z) q, List.NoDup (pre ++ mid ++ post) -> In q (pre ++ post) ->
  ~ In q mid.
Proof using.
  intros pre mid post q H Hq Hm. apply in_app_or in Hq as [Hq|Hq].
  - exact (rbl_nd_disj pre (mid ++ post) q H Hq (in_or_app _ _ _ (or_introl Hm))).
  - rewrite app_assoc in H. exact (rbl_nd_disj (pre ++ mid) post q H (in_or_app _ _ _ (or_intror Hm)) Hq).
Qed.

Lemma rbl_nd_ins : forall (Y pre post : list Z), List.NoDup (pre ++ post) -> List.NoDup Y ->
  (forall y, In y Y -> ~ In y (pre ++ post)) -> List.NoDup (pre ++ Y ++ post).
Proof using.
  induction Y as [|y Y IH]; intros pre post H NY HY; [exact H|].
  apply List.NoDup_cons_iff in NY as [NI NY].
  replace (pre ++ (y :: Y) ++ post) with ((pre ++ [y]) ++ Y ++ post) by (rewrite <- app_assoc; reflexivity).
  apply IH; [| exact NY |].
  - rewrite <- app_assoc. apply nodup_mid_add; [exact H | apply HY; left; reflexivity].
  - intros z Hz Hin. rewrite <- app_assoc in Hin. apply in_app_or in Hin as [Hin|[Hin|Hin]].
    + apply (HY z (or_intror Hz)). apply in_or_app. left. exact Hin.
    + apply NI. rewrite Hin. exact Hz.
    + apply (HY z (or_intror Hz)). apply in_or_app. right. exact Hin.
Qed.

Lemma rbl_nd_swap : forall (pre X Y post : list Z), List.NoDup (pre ++ X ++ post) -> List.NoDup Y ->
  (forall y, In y (pre ++ post) -> ~ In y Y) -> List.NoDup (pre ++ Y ++ post).
Proof using.
  intros pre X Y post H NY HY. apply rbl_nd_ins; [exact (nodup_mid_drop pre X post H) | exact NY |].
  intros y Hy Hin. exact (HY y Hin Hy).
Qed.

Lemma rbl_c1 : forall mm a0 x, rw_cells rsegs mm a0 [C1 x] <-> rw_cells rsegs mm a0 [CB 1 [x]].
Proof using.
  intros mm a0 x. split; intros [[_ B] Wr]; (split; [split; [cbn; repeat split | exact B] | exact Wr]).
Qed.

Lemma rbl_cb_mid : forall mm a0 (b1 b2 : list byte) x,
  rw_cells rsegs mm a0 [CB (length b1 + S (length b2)) (b1 ++ x :: b2)] ->
  rw_cells rsegs mm a0 [CB (length b1) b1] /\ rw_cells rsegs mm (a0 + Z.of_nat (length b1)) [C1 x] /\
  rw_cells rsegs mm (a0 + Z.of_nat (length b1) + 1) [CB (length b2) b2].
Proof using Bm G HJ O h junk regs.
  intros mm a0 b1 b2 x H.
  destruct (cb_cut2 mm a0 b1 (x :: b2) H) as [X1 X2].
  destruct (cb_cut2 mm (a0 + Z.of_nat (length b1)) [x] b2 X2) as [Y1 Y2].
  split; [exact X1|]. split; [apply rbl_c1; exact Y1 | exact Y2].
Qed.

Lemma rbl_cb_join : forall mm a0 (b1 b2 : list byte) x, rw_cells rsegs mm a0 [CB (length b1) b1] ->
  rw_cells rsegs mm (a0 + Z.of_nat (length b1)) [C1 x] ->
  rw_cells rsegs mm (a0 + Z.of_nat (length b1) + 1) [CB (length b2) b2] ->
  rw_cells rsegs mm a0 [CB (length b1 + S (length b2)) (b1 ++ x :: b2)].
Proof using Bm G HJ O h junk regs.
  intros mm a0 b1 b2 x X1 X2 X3.
  pose proof (cb_join2 mm (a0 + Z.of_nat (length b1)) [x] b2 (proj1 (rbl_c1 _ _ _) X2) X3) as Y.
  exact (cb_join2 mm a0 b1 (x :: b2) X1 Y).
Qed.

Lemma rbl_cb_at : forall mm a0 (bs : list byte) i, (i < length bs)%nat -> rw_cells rsegs mm a0 [CB (length bs) bs] ->
  exists b1 x b2, bs = b1 ++ x :: b2 /\ length b1 = i /\
    rw_cells rsegs mm a0 [CB (length b1) b1] /\ rw_cells rsegs mm (a0 + Z.of_nat i) [C1 x] /\
    rw_cells rsegs mm (a0 + Z.of_nat i + 1) [CB (length b2) b2].
Proof using Bm G HJ O h junk regs.
  intros mm a0 bs i Hi H.
  pose proof (rbl_split_nth bs i (Z_to_bv 8 0) Hi) as Eb.
  assert (L1 : length (firstn i bs) = i) by (rewrite length_firstn; clear - Hi; lia).
  exists (firstn i bs), (nth i bs (Z_to_bv 8 0)), (skipn (S i) bs).
  split; [exact Eb|]. split; [exact L1|].
  rewrite Eb in H. rewrite length_app in H. cbn [length] in H.
  destruct (rbl_cb_mid mm a0 _ _ _ H) as (X1 & X2 & X3). rewrite L1 in X2, X3.
  split; [exact X1|]. split; [exact X2 | exact X3].
Qed.

Lemma rbl_bytes_nth : forall sg m a (bs : list byte) i x, bytes_at sg m a bs -> nth_error bs i = Some x ->
  bytes_at sg m (a + Z.of_nat i) [x].
Proof using.
  intros sg m a bs i x H Ex. pose proof (bytes_at_bound sg m a bs H) as Bd.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Ex; discriminate).
  apply bytes_at_of_mbyte; [clear - Bd; lia | cbn [length]; clear - Bd Hi; lia |].
  intros i' Hi'. cbn [length] in Hi'. replace i' with 0%nat by (clear - Hi'; lia).
  rewrite Nat2Z.inj_0, Z.add_0_r, (mbyte_of_bytes_at sg m a bs i H Hi), Ex. reflexivity.
Qed.

Lemma rbl_norm_hi : forall mm a0 cs, ro_agree rsegs mm -> rw_cells rsegs mm a0 cs -> 0x21624 <= a0 ->
  rw_cells rsegs (normalize rsegs mm) a0 cs.
Proof using Bm G HJ O h junk regs.
  intros mm a0 cs RO X Ha0. apply (rw_cells_normalize rsegs mm a0 cs RO X). intros i Hi.
  pose proof (rw_cells_bound _ _ _ _ X) as RB. apply ro_hi. clear - RB Hi Ha0. lia.
Qed.

Lemma rbl_norm_blk : forall L1 A1 m1 md1 mm a0 cs q k, MR L1 A1 m1 md1 -> ro_agree rsegs mm -> rw_cells rsegs mm a0 cs ->
  In (q, k) (blocks L1 A1) -> q <= a0 -> a0 + Z.of_nat (cells_size cs) <= q + k -> rw_cells rsegs (normalize rsegs mm) a0 cs.
Proof using AX SEGS.
  intros L1 A1 m1 md1 mm a0 cs q k HM RO X Hq L0 L0'. apply (rw_cells_normalize rsegs mm a0 cs RO X). intros i Hi.
  pose proof (blk_rng _ _ _ _ _ _ HM Hq) as QR. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  apply (ro_addr_out Bm SEGS); [clear - QR Hi L0 L0' ACL; lia|].
  replace (a0 + i) with (q + (a0 + i - q)) by ring. apply (blk_noimg _ _ _ _ _ _ _ HM Hq). clear - Hi L0 L0'. lia.
Qed.

Lemma rbl_apart : forall L1 A1 m1 md1 q k, MR L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) -> 0 < k ->
  q + k <= G_RELAY_LO \/ G_S + SRC_SIZE * SOURCES_MAX <= q.
Proof using AX GRP HG HJ O h junk.
  intros L1 A1 m1 md1 q k HM Hq Hk.
  apply img_apart; [exact Hk | clear - Hk; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | |].
  - intros i Hi. exact (blk_noimg _ _ _ _ _ _ i HM Hq Hi).
  - intros a Ha. exact (proj1 (GRP a Ha)).
Qed.

Lemma rbl_lb_pos : forall L1 A1 m1 LA l ln q, list_at Bm L1 A1 m1 LA l ln -> In q (list_blocks l) ->
  exists k, In (q, k) (blocks L1 A1) /\ 0 < k.
Proof using.
  intros L1 A1 m1 LA l ln q (_ & _ & C3 & _ & _ & C6) Hq.
  unfold list_blocks in Hq. apply in_app_or in Hq as [Hq|Hq].
  - revert Hq. destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct C3 as [(C0 & _)|(Cp & VI & _)]; [exfalso; exact (C C0)|].
    exists (16 * hl_cap l). split; [exact VI | clear - Cp; lia].
  - apply in_map_iff in Hq as (r & <- & Hr). destruct (proj1 (Forall_forall _ _) C6 r Hr) as (R1 & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [exact R1 | clear - r; lia].
Qed.

Lemma rbl_hb_pos : forall L1 A1 m1 HA1 h1 q, src_at Bm L1 A1 m1 HA1 h1 -> In q (hs_blocks h1) ->
  exists k, In (q, k) (blocks L1 A1) /\ 0 < k.
Proof using.
  intros L1 A1 m1 HA1 h1 q (_ & _ & _ & _ & _ & S6 & _ & _ & _ & _ & S11 & _ & _ & _ & _ & S16 & S17 & _) Hq.
  unfold hs_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [exact (rbl_lb_pos _ _ _ _ _ _ _ S6 Hq)|].
  apply in_app_or in Hq as [Hq|Hq]; [destruct Hq as [<-|[]]; exists 6000; split; [exact S11 | clear - S11; lia]|].
  apply in_app_or in Hq as [Hq|Hq]; [exact (rbl_lb_pos _ _ _ _ _ _ _ S16 Hq) | exact (rbl_lb_pos _ _ _ _ _ _ _ S17 Hq)].
Qed.

Lemma rbl_eb_pos : forall L1 A1 m1 e1 q, entry_okw L1 A1 m1 e1 -> In q (entry_blocks e1) ->
  exists k, In (q, k) (blocks L1 A1) /\ 0 < k.
Proof using.
  intros L1 A1 m1 e1 q (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & _ & E12 & _ & _ & E15) Hq.
  unfold entry_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [|apply in_app_or in Hq as [Hq|Hq]].
  - revert Hq. destruct (Z.eqb_spec (re_cap e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E10 as [(C0 & _)|(Cp & BI & _)]; [exfalso; exact (C C0) | exists (re_cap e1); split; [exact BI | exact Cp]].
  - revert Hq. destruct (Z.eqb_spec (re_hp e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E12 as [(H0 & _)|(HI & _ & _ & H8 & _)]; [exfalso; exact (C H0)|].
    exists (re_kh e1). split; [exact HI | clear - H8; lia].
  - apply in_map_iff in Hq as (k & <- & Hk). destruct (proj1 (Forall_forall _ _) E15 k Hk) as (K1 & _).
    eexists; split; [exact K1 | clear - k; lia].
Qed.

Lemma rbl_lb_nd : forall L1 A1 m1 LA l ln, list_at Bm L1 A1 m1 LA l ln -> List.NoDup (list_blocks l).
Proof using.
  intros L1 A1 m1 LA l ln (_ & _ & _ & C4 & C5 & _). apply NoDup_ListNoDup in C4.
  unfold list_blocks. destruct (hl_cap l =? 0); cbn [app]; [exact C4 | constructor; [exact C5 | exact C4]].
Qed.

Lemma rbl_rp_keep : forall L2 A2 R2 m2 md2 q m, relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 R2 m2 md2 ->
  In (q, m) (blocks L A) -> ~ FF q -> In (q, m) (blocks L2 A2).
Proof using PRE.
  intros L2 A2 R2 m2 md2 q m (_ & _ & _ & _ & _ & AD & SV & Z0 & _) Hq NF.
  apply CF.gestures_end_b.blocks_In2 in Hq as (p & Ep & Hp). apply CF.gestures_end_b.blocks_In2.
  pose proof pre_facts as (_ & HW0 & _).
  pose proof (sb_ub_nonneg A p m HW0 Hp) as Hm.
  destruct (Z.eq_dec m 0) as [->|Hm0].
  - destruct (Z0 p Hp) as [Hp2 E2]. exists p. split; [rewrite E2; exact Ep | exact Hp2].
  - rewrite <- Ep in NF. pose proof (SV p m Hp ltac:(clear - Hm Hm0; lia) NF) as Hp2.
    exists p. split; [rewrite (AD p m Hp Hp2 NF); exact Ep | exact Hp2].
Qed.

Lemma rbl_rt : forall R R', RT R -> regs_preserved R R' -> RT R'.
Proof using.
  intros R R' (G2 & G3 & G4 & G8 & G22 & G25) P. unfold RT.
  split; [transitivity (getr R 2); [exact (P 2 ltac:(unfold callee_saved; clear - G2; lia)) | exact G2]|].
  split; [transitivity (getr R 3); [exact (P 3 ltac:(unfold callee_saved; clear - G2; lia)) | exact G3]|].
  split; [transitivity (getr R 4); [exact (P 4 ltac:(unfold callee_saved; clear - G2; lia)) | exact G4]|].
  split; [transitivity (getr R 8); [exact (P 8 ltac:(unfold callee_saved; clear - G2; lia)) | exact G8]|].
  split; [transitivity (getr R 22); [exact (P 22 ltac:(unfold callee_saved; clear - G2; lia)) | exact G22]|].
  transitivity (getr R 25); [exact (P 25 ltac:(unfold callee_saved; clear - G2; lia)) | exact G25].
Qed.

Lemma rbl_rtk : forall R R', RTK R -> regs_preserved R R' -> RTK R'.
Proof using Bm G HJ O h junk.
  intros R R' (G0 & G23 & G26) P. split; [exact (rbl_rt R R' G0 P)|].
  split; [transitivity (getr R 23); [exact (P 23 ltac:(unfold callee_saved; lia)) | exact G23]|].
  transitivity (getr R 26); [exact (P 26 ltac:(unfold callee_saved; lia)) | exact G26].
Qed.

Lemma rbl_rtl : forall R R', RTL R -> regs_preserved R R' -> RTL R'.
Proof using Bm G HJ O h junk.
  intros R R' (G0 & G27) P. split; [exact (rbl_rtk R R' G0 P)|].
  transitivity (getr R 27); [exact (P 27 ltac:(unfold callee_saved; lia)) | exact G27].
Qed.

Lemma rbl_ret : YK0s.ret_ok (Z_to_bv 64 0x13ae8).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rbl_pre_lp : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre_k Bm MR LIST_PUSH_K L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. apply SC1. left.
    change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma rbl_text : forall L1 A1 m1 md1 h1 s r0 rs0, MR L1 A1 m1 md1 -> src_at Bm L1 A1 m1 HA h1 ->
  hl_recs (hs_pending h1) = r0 :: rs0 -> map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = ds_pend s ->
  hs_off h1 = ds_off s ->
  In (fst r0, Z.of_nat (length (snd r0)) + 1) (blocks L1 A1) /\
  rw_cells segs m1 (fst r0) [CB (length (snd r0) + 1) (snd r0 ++ [Z_to_bv 8 0])] /\
  0 <= ds_off s < Z.of_nat (length (snd r0)) /\ dhead s = bzs (snd r0) /\
  dnum s <= Z.of_nat (length (snd r0)) - ds_off s /\
  4096 <= fst r0 /\ fst r0 + Z.of_nat (length (snd r0)) + 1 <= YM05.alloc_ceiling.
Proof using.
  intros L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7 L8.
  pose proof SR1 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & P6) & _ & S8 & _).
  pose proof (proj1 (Forall_forall _ _) P6 r0 ltac:(rewrite HR; left; reflexivity)) as (T1 & _ & T3 & _).
  pose proof (blk_rng _ _ _ _ _ _ M1 T1) as TB.
  assert (OFF : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
  { destruct S8 as [(RN & _)|(r1 & rs1 & RE1 & RO')]; [rewrite HR in RN; discriminate|].
    rewrite HR in RE1. injection RE1 as <- <-. exact RO'. }
  assert (DH : dhead s = bzs (snd r0)) by (unfold dhead; rewrite <- L7, HR; reflexivity).
  split; [exact T1|]. split; [exact T3|]. split; [rewrite <- L8; exact OFF|]. split; [exact DH|].
  split; [unfold dnum; rewrite DH; unfold bzs; rewrite length_map; clear - OFF; lia|]. clear - TB. lia.
Qed.

Lemma rbl_byte : forall s k (r0 : Z * list byte) m1,
  rw_cells segs m1 (fst r0) [CB (length (snd r0) + 1) (snd r0 ++ [Z_to_bv 8 0])] ->
  dhead s = bzs (snd r0) -> 0 <= ds_off s -> dnum s <= Z.of_nat (length (snd r0)) - ds_off s -> Z.of_nat k < dnum s ->
  exists c, bytes_at segs m1 (fst r0 + ds_off s + Z.of_nat k) [c] /\ nth_error (ddata s) k = Some (bz c).
Proof using.
  intros s k r0 m1 TC DH O0 NL KN.
  destruct (nth_error (snd r0) (Z.to_nat (ds_off s) + k)) as [c|] eqn:EC;
    [|exfalso; apply nth_error_None in EC; clear - EC O0 NL KN; lia].
  exists c. split.
  - pose proof TC as [[_ TB] _]. cbn [cells_bytes cbytes] in TB. rewrite app_nil_r in TB.
    apply bytes_at_app in TB as [TB _].
    pose proof (rbl_bytes_nth segs m1 (fst r0) (snd r0) _ c TB EC) as X.
    replace (fst r0 + ds_off s + Z.of_nat k) with (fst r0 + Z.of_nat (Z.to_nat (ds_off s) + k)) by (clear - O0; lia).
    exact X.
  - unfold ddata. rewrite DH, nth_error_firstn.
    replace (Nat.ltb k (Z.to_nat (dnum s))) with true by (symmetry; apply Nat.ltb_lt; clear - KN; lia).
    rewrite nth_error_skipn. unfold bzs. rewrite nth_error_map, EC. reflexivity.
Qed.

Lemma rbl_src_set : forall L1 A1 L2 A2 m1 m2 HA1 h1 pj np ovl ex Pa,
  msame Pa m1 m2 -> src_at Bm L1 A1 m1 HA1 h1 ->
  (forall a, (HA1 <= a < HA1 + 32 \/ HA1 + 80 <= a < HA1 + 96) -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (list_blocks (hs_pending h1) ++ hs_partial h1 :: list_blocks (hs_held h1)) ->
     In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (list_blocks (hs_pending h1) ++ list_blocks (hs_held h1)) ->
     q <= a < q + k -> Pa a) ->
  rw_cells segs m2 (HA1 + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 np);
                               C4 (Z_to_bv 64 ovl)] ->
  0 <= np <= 6000 -> (ovl = 0 \/ ovl = 1) -> Z.of_nat (length pj) = 6000 ->
  rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) pj] -> ~ In (Z_to_bv 8 0) (firstn (Z.to_nat np) pj) ->
  list_at Bm L2 A2 m2 (HA1 + 64) ex true ->
  NoDup (list_blocks (hs_pending h1) ++ [hs_partial h1] ++ list_blocks ex ++ list_blocks (hs_held h1)) ->
  src_at Bm L2 A2 m2 HA1 (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1)
                            (hs_partial h1) pj np ovl (hs_pad h1) ex (hs_held h1)).
Proof using.
  intros L1 A1 L2 A2 m1 m2 HA1 h1 pj np ovl ex Pa MS
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18)
    HC SV HB C2 NP OV LPJ PB NZ LX NDX.
  unfold src_at, hs_W, hs_blocks.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_expected hs_held].
  split; [eapply rw_tr; [exact MS | exact S1 | intros a Ha; apply HC; cbn [cells_size csize] in Ha; clear - Ha; lia]|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split.
  { eapply list_at_tr; [exact MS | exact S6 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. apply SV; [exact Hq | apply in_or_app; left; exact Hl].
    - intros q k a Hq Hl Ha. apply (HB q k a Hq); [apply in_or_app; left; exact Hl | exact Ha]. }
  split; [exact C2|]. split; [exact S8|]. split; [exact NP|]. split; [exact OV|].
  split; [apply SV; [exact S11 | apply in_or_app; right; left; reflexivity]|].
  split; [exact S12|]. split; [exact LPJ|]. split; [exact PB|]. split; [exact NZ|]. split; [exact LX|].
  split.
  { eapply list_at_tr; [exact MS | exact S17 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. apply SV; [exact Hq | apply in_or_app; right; right; exact Hl].
    - intros q k a Hq Hl Ha. apply (HB q k a Hq); [apply in_or_app; right; exact Hl | exact Ha]. }
  exact NDX.
Qed.

Lemma rbl_bundle : forall s L1 A1 m1 L2 A2 m2 e1 h1 OUT1 junk1 LB1 D (Pa : Z -> Prop) pj np ovl ex,
  msame Pa m1 m2 ->
  (forall a, img_plain Bm a -> ~ (HA + 32 <= a < HA + 80) -> Pa a) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> q <> hs_partial h1 -> ~ In q (list_blocks (hs_expected h1)) ->
     q <= a < q + k -> Pa a) ->
  (forall a, S0 - 144 <= a < S0 -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> ~ In q (list_blocks (hs_expected h1)) -> In (q, k) (blocks L2 A2)) ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] ->
  entry_okw L1 A1 m1 e1 -> src_at Bm L1 A1 m1 HA h1 -> others_at Bm m1 j (re_fd e) fs os ->
  ds_no s = NO + dtot D -> bzs LB1 = with_nul (lines ST0 D) ->
  DBLK L1 A1 e1 h1 OUT1 -> DGLB D m1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  (exists ev, rw_cells segs m2 ERR [C4 ev]) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 np);
                              C4 (Z_to_bv 64 ovl)] ->
  0 <= np <= 6000 -> (ovl = 0 \/ ovl = 1) -> Z.of_nat (length pj) = 6000 ->
  rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) pj] -> ~ In (Z_to_bv 8 0) (firstn (Z.to_nat np) pj) ->
  list_at Bm L2 A2 m2 (HA + 64) ex true ->
  NoDup (list_blocks (hs_pending h1) ++ [hs_partial h1] ++ list_blocks ex ++ list_blocks (hs_held h1)) ->
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m2 SA [CB 56%nat (entry_bytes e1)] /\
  entry_okw L2 A2 m2 e1 /\
  src_at Bm L2 A2 m2 HA (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1)
                            (hs_partial h1) pj np ovl (hs_pad h1) ex (hs_held h1)) /\
  others_at Bm m2 j (re_fd e) fs os /\
  DGLB D m2 /\
  DOUT s L2 A2 m2 OUT1 junk1 LB1.
Proof using EHI GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s L1 A1 m1 L2 A2 m2 e1 h1 OUT1 junk1 LB1 D Pa pj np ovl ex MS HPI HPB HPF HK FR1 SAC1 EK1 SR1 OT1 HNO HLB
    BK1 GL1 OU1 ERR2 HC2 NP OV LPJ PB2 NZ LX NDX.
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof BK1 as (ND & GI1 & _).
  apply NoDup_ListNoDup in ND. unfold hs_blocks in ND.
  assert (NX : forall q, In q ((G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1]) ++
                              list_blocks (hs_held h1)) -> ~ In q (list_blocks (hs_expected h1))).
  { intros q Hq.
    apply (rbl_nd_out (G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1])
             (list_blocks (hs_expected h1)) (list_blocks (hs_held h1)) q); [|exact Hq].
    cbn [app]. rewrite <- !app_assoc. exact ND. }
  assert (NP' : forall q, In q ((G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1)) ++
                               list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)) -> q <> hs_partial h1).
  { intros q Hq Eq.
    apply (rbl_nd_out (G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1)) [hs_partial h1]
             (list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)) q); [| exact Hq | left; symmetry; exact Eq].
    cbn [app]. rewrite <- !app_assoc. exact ND. }
  assert (GX : ~ In G (list_blocks (hs_expected h1)) /\ G <> hs_partial h1).
  { split; [apply NX; left; reflexivity | apply NP'; left; reflexivity]. }
  assert (OX : ~ In OUT1 (list_blocks (hs_expected h1)) /\ OUT1 <> hs_partial h1).
  { split; [apply NX; right; left; reflexivity | apply NP'; right; left; reflexivity]. }
  assert (EX : forall q, In q (entry_blocks e1) -> ~ In q (list_blocks (hs_expected h1)) /\ q <> hs_partial h1).
  { intros q Hq. split; [apply NX | apply NP']; right; right; apply in_or_app; left; apply in_or_app; left; exact Hq. }
  assert (PX : forall q, In q (list_blocks (hs_pending h1) ++ list_blocks (hs_held h1)) ->
                 ~ In q (list_blocks (hs_expected h1)) /\ q <> hs_partial h1).
  { intros q Hq. apply in_app_or in Hq as [Hq|Hq]; split.
    - apply NX. right; right. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hq.
    - apply NP'. right; right. apply in_or_app; left. apply in_or_app; right. exact Hq.
    - apply NX. right; right. apply in_or_app; right. exact Hq.
    - apply NP'. right; right. apply in_or_app; right. apply in_or_app; right. exact Hq. }
  assert (PAX : ~ In (hs_partial h1) (list_blocks (hs_expected h1))).
  { apply NX. right; right. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. left. reflexivity. }
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FRc |]. intros a Ha. apply HPF.
    cbn [cells_size csize app dr_saved] in Ha. clear - Ha. lia. }
  split.
  { eapply rw_tr; [exact MS | exact SAC1 |]. intros a Ha. apply (HPB G SRC_TABLE a GI1 (proj2 GX) (proj1 GX)).
    cbn [cells_size csize] in Ha. unfold SRC_TABLE, SRC_ENTRY. clear - Ha F6 F7. lia. }
  split.
  { eapply entry_okw_tr; [exact MS | exact EK1 | |].
    - intros q k Hq Hb. exact (HK q k Hq (proj1 (EX q Hb))).
    - intros q k a Hq Hb Ha. exact (HPB q k a Hq (proj2 (EX q Hb)) (proj1 (EX q Hb)) Ha). }
  split.
  { eapply rbl_src_set; [exact MS | exact SR1 | | | | exact HC2 | exact NP | exact OV | exact LPJ | exact PB2 | exact NZ
                         | exact LX | exact NDX].
    - intros a Ha. apply HPI; [apply GRP|]; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    - intros q k Hq Hb. apply (HK q k Hq). apply in_app_or in Hb as [Hb|[Hb|Hb]].
      + exact (proj1 (PX q (in_or_app _ _ _ (or_introl Hb)))).
      + rewrite <- Hb. exact PAX.
      + exact (proj1 (PX q (in_or_app _ _ _ (or_intror Hb)))).
    - intros q k a Hq Hb Ha. exact (HPB q k a Hq (proj2 (PX q Hb)) (proj1 (PX q Hb)) Ha). }
  split.
  { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi Hij Ha.
    assert (NE : Z.of_nat i <> Z.of_nat j) by (intros X; apply Hij; apply Nat2Z.inj; exact X).
    apply HPI; [apply GRP|]; clear - Ha Hi NE F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
  split.
  { destruct GL1 as (GC1 & GC2 & GC3 & GC4 & _).
    split; [eapply rw_tr; [exact MS | exact GC1 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GCP|]; clear - Ha F11; unfold G_CLIENT, G_S, SRC_SIZE in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC2 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GRP|]; clear - Ha F11; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC3 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GRP|]; clear - Ha F11; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GRP|]; clear - Ha F11; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    exact ERR2. }
  destruct OU1 as (OFa & OTa). split.
  - intros LV. destruct (OFa LV) as (OC & OE & OCP & OB). split.
    + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + split; [exact OE|]. split; [exact OCP|]. intros Cq. destruct (OB Cq) as (OI & OBy).
      pose proof OX as OX'. rewrite OE in OX'.
      split; [exact (HK _ _ OI (proj1 OX'))|].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB OUT CAP a OI (proj2 OX') (proj1 OX')).
      destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; [clear - Cq C0; lia|].
      rewrite length_app in Ha. clear - Ha LO LJ. lia.
  - intros LV. destruct (OTa LV) as (OC & OZ). split.
    + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + destruct OZ as [OZ|(Pp & NL & OI & OFr & OBy & LJ)]; [left; exact OZ | right].
      split; [exact Pp|]. split; [exact NL|]. split; [exact (HK _ _ OI (proj1 OX))|]. split; [exact OFr|].
      split; [|exact LJ].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB OUT1 (ds_ocap s) a OI (proj2 OX) (proj1 OX)).
      assert (LO : Z.of_nat (length O) = NO).
      { destruct OUTD as [(_ & _ & N0 & OE0)|(_ & _ & _ & _ & _ & LO & _)];
          [rewrite OE0; cbn [length]; clear - N0; lia | exact LO]. }
      assert (LLB : Z.of_nat (length LB1) = dtot D).
      { unfold dtot. rewrite <- HLB. unfold bzs. rewrite length_map. reflexivity. }
      rewrite !length_app in Ha. clear - Ha LO LLB HNO LJ. lia.
Qed.

Lemma rbl_simple : forall s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D W pj np ovl,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] ->
  entry_okw L1 A1 m1 e1 -> src_at Bm L1 A1 m1 HA h1 -> others_at Bm m1 j (re_fd e) fs os -> DSAME e1 h1 ->
  ds_no s = NO + dtot D -> bzs LB1 = with_nul (lines ST0 D) ->
  DBLK L1 A1 e1 h1 OUT1 -> DGLB D m1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  munch W m1 m2 -> wmono segs m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 48 <= a < HA + 60) -> ~ (hs_partial h1 <= a < hs_partial h1 + 6000) ->
     outside W a) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 np);
                              C4 (Z_to_bv 64 ovl)] ->
  0 <= np <= 6000 -> (ovl = 0 \/ ovl = 1) -> Z.of_nat (length pj) = 6000 ->
  rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) pj] -> ~ In (Z_to_bv 8 0) (firstn (Z.to_nat np) pj) ->
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m2 md1 /\
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m2 SA [CB 56%nat (entry_bytes e1)] /\
  entry_okw L1 A1 m2 e1 /\
  src_at Bm L1 A1 m2 HA (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1)
                            (hs_partial h1) pj np ovl (hs_pad h1) (hs_expected h1) (hs_held h1)) /\
  others_at Bm m2 j (re_fd e) fs os /\
  DGLB D m2 /\
  DOUT s L1 A1 m2 OUT1 junk1 LB1.
Proof using AX BW EHI EU GCP GEI GRP HG HJ OUTD PRE SEGS SRC0.
  intros s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D W pj np ovl RP1 FR1 SAC1 EK1 SR1 OT1 SM1 HNO HLB BK1 GL1 OU1 MU WM
    HW HC2 NP OV LPJ PB2 NZ.
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  pose proof SR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S11 & _ & _ & _ & _ & S16 & _ & S18).
  pose proof (blk_rng _ _ _ _ _ _ M1 S11) as PR.
  pose proof (msame_munch _ _ _ MU WM) as MS.
  assert (PNI : forall a, in_img Bm a -> ~ (hs_partial h1 <= a < hs_partial h1 + 6000)).
  { intros a Ha X. apply (blk_noimg _ _ _ _ _ _ (a - hs_partial h1) M1 S11); [clear - X; lia|].
    replace (hs_partial h1 + (a - hs_partial h1)) with a by ring. exact Ha. }
  assert (HPI0 : forall a, img_plain Bm a -> ~ (HA + 48 <= a < HA + 60) -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a (Ha & _) Hn. pose proof (img_lo a Ha) as IL. split; [clear - IL; lia|].
    apply HW; [clear - IL; lia | exact Hn | exact (PNI a Ha)]. }
  assert (HPB0 : forall q k a, In (q, k) (blocks L1 A1) -> q <> hs_partial h1 -> q <= a < q + k ->
                   0 <= a < 2 ^ 64 /\ outside W a).
  { intros q k a Hq Hn Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (rbl_apart _ _ _ _ _ _ M1 Hq ltac:(clear - Ha; lia)) as QA.
    split; [clear - QR Ha F4; lia|]. apply HW; [clear - QR Ha F4; lia | |].
    - clear - QA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq S11 Hn) as [X|X]; clear - X Ha; lia. }
  assert (HPF : forall a, S0 - 144 <= a < S0 -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ha. split; [clear - Ha F1 F2 F3; lia|].
    apply HW; [clear - Ha F1 F2 F3; lia | clear - Ha F1 F3 F11; unfold G_S, SRC_SIZE in *; lia | clear - Ha PR F1; lia]. }
  assert (ERR2 : exists ev, rw_cells segs m2 ERR [C4 ev]).
  { destruct GL1 as (_ & _ & _ & _ & (ev1 & GC5)). exists ev1. eapply rw_tr; [exact MS | exact GC5 |]. intros a Ha.
    cbn [cells_size csize] in Ha. pose proof (GEI a ltac:(clear - Ha; lia)) as Hi. pose proof (img_lo a Hi) as IL.
    split; [clear - IL; lia|]. apply HW; [clear - IL; lia | | exact (PNI a Hi)].
    intros X. pose proof (GRP a ltac:(clear - X F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))
      as (_ & _ & _ & NE).
    apply NE. clear - Ha. lia. }
  pose proof S18 as NDH. apply NoDup_ListNoDup in NDH. unfold hs_blocks in NDH.
  assert (LX2 : list_at Bm L1 A1 m2 (HA + 64) (hs_expected h1) true).
  { eapply list_at_tr; [exact MS | exact S16 | | intros q k Hq _; exact Hq |].
    - intros a Ha. apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    - intros q k a Hq Hb Ha. apply (HPB0 q k a Hq); [|exact Ha]. intros X.
      apply (rbl_nd_out (list_blocks (hs_pending h1)) [hs_partial h1] _ q NDH);
        [apply in_or_app; right; apply in_or_app; left; exact Hb | left; symmetry; exact X]. }
  destruct (rbl_bundle s L1 A1 m1 L1 A1 m2 e1 h1 OUT1 junk1 LB1 D (fun a => 0 <= a < 2 ^ 64 /\ outside W a) pj np ovl
              (hs_expected h1) MS (fun a Hp Hn => HPI0 a Hp ltac:(clear - Hn; lia))
              (fun q k a Hq Hn _ Ha => HPB0 q k a Hq Hn Ha) HPF (fun q k Hq _ => Hq) FR1 SAC1 EK1 SR1 OT1 HNO HLB
              BK1 GL1 OU1 ERR2 HC2 NP OV LPJ PB2 NZ LX2 S18)
    as (FR2 & SAC2 & EK2 & SR2 & OT2 & GL2 & OU2).
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU); [exact WM | exact GEI |].
    intros a Ha. destruct (rbl_rng a (HA + 48) (HA + 60)) as [D1|D1].
    - right; right; left. split; [apply GRP; clear - D1 F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
      right; right; left. clear - D1. unfold SRC_SIZE in *. lia.
    - destruct (rbl_rng a (hs_partial h1) (hs_partial h1 + 6000)) as [D2|D2]; [|left; exact (HW a Ha D1 D2)].
      right; right; right; right. split; [intros X; exact (PNI a X D2)|].
      split; [exists (hs_partial h1), 6000; split; [exact S11 | clear - D2; lia]|].
      intros p n i Hp Hp1 NF Hi NE Ea. apply NE. rewrite Ea.
      pose proof SM1 as (_ & _ & _ & _ & _ & _ & _ & SP & _).
      pose proof SRC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S11h & _).
      right; right; right. exists (hs_partial h), 6000. split; [apply in_or_app; right; apply hb_part|].
      split; [exact S11h | rewrite <- SP; clear - D2; lia]. }
  split; [exact FR2|]. split; [exact SAC2|]. split; [exact EK2|]. split; [exact SR2|].
  split; [exact OT2|]. split; [exact GL2 | exact OU2].
Qed.

Lemma rbl_k : forall s k c, DRB s k c -> Z.of_nat k < dnum s /\ dwf s.
Proof using.
  intros s k c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & KN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LK1 & _).
  pose proof LK1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WF1). split; [exact KN | exact WF1].
Qed.

Definition DRE (s : dstate) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (r0 : Z * list byte) (rs0 : list (Z * list byte)),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13b30) m1 (seg_rom segs)) md1 /\ RT R1 /\
    getr R1 9 = Z_to_bv 64 0 /\ getr R1 18 = Z_to_bv 64 (XH + 192) /\
    getr R1 19 = Z_to_bv 64 (dnum s) /\ getr R1 20 = Z_to_bv 64 XH /\
    getr R1 21 = Z_to_bv 64 (fst r0 + ds_off s + dnum s) /\
    getr R1 23 = Z_to_bv 64 (fst r0 + ds_off s + dnum s) /\ getr R1 24 = Z_to_bv 64 1 /\
    getr R1 26 = Z_to_bv 64 (fst r0) /\ getr R1 27 = Z_to_bv 64 (fst r0 + ds_off s) /\
    rw_cells segs m1 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))] /\
    hl_recs (hs_pending h1) = r0 :: rs0 /\ 0 < dnum s /\ 4096 <= ds_cap s - ulen s /\
    ds_eintr s = false /\
    bzs (firstn (Z.to_nat (dnum s)) (re_junk e1)) = ddata s /\
    relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 /\
    st_init_done A1 = true /\
    DPU L1 A1 s e1 h1 OUT1 (dref s) /\
    ro_agree segs m1 /\
    (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
    rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] /\
    entry_okw L1 A1 m1 e1 /\
    src_at Bm L1 A1 m1 HA h1 /\
    others_at Bm m1 j (re_fd e) fs os /\
    DSAME e1 h1 /\
    (re_cap e1 = ds_cap s /\ bzs (re_U e1) = ds_u s /\ re_skip e1 = (if ds_skip s then 1 else 0) /\
     keys_texts (re_keys e1) = ds_H s /\ ent_ka e1 = ds_ka s /\ hs_eintr h1 = (if ds_eintr s then 1 else 0) /\
     map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = ds_pend s /\ hs_off h1 = ds_off s /\
     hs_state h1 = feed (ds_ref s) (ddata s) /\
     hl_n (hs_expected h1) = ds_en s + Z.of_nat (length (dref s)) /\
     hl_cap (hs_expected h1) = pcapm (ds_en s) (ds_ecap s) (dref s) /\
     dwf s) /\
    (bzs PS = D ++ pstream s /\ ds_ref s = feed ST0 D /\ J1 (ds_u s) (ds_skip s) (ds_ref s) /\
     map snd (hl_recs (hs_expected h1)) =
       map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines ST0 (D ++ ddata s)) /\
     firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
     hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
     ds_no s = NO + dtot D /\ bzs LB1 = with_nul (lines ST0 D) /\
     NoDup (ds_H s) /\ same_set (ds_H s) (upds (keys_texts (re_keys e)) (lines ST0 D)) /\
     Z.of_nat (length (ds_H s)) + Z.of_nat (length (pstream s)) < 2 ^ 26 /\
     ds_en s + Z.of_nat (length (pstream s)) < 2 ^ 27) /\
    DBLK L1 A1 e1 h1 OUT1 /\
    DGLB D m1 /\
    DOUT s L1 A1 m1 OUT1 junk1 LB1.

Lemma UB_rbl_fin : forall s k R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (r0 : Z * list byte) rs0,
  RT R1 -> getr R1 9 = Z_to_bv 64 (dnum s - Z.of_nat k) -> getr R1 18 = Z_to_bv 64 (XH + 192) ->
  getr R1 19 = Z_to_bv 64 (dnum s) -> getr R1 20 = Z_to_bv 64 XH ->
  getr R1 21 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k) ->
  getr R1 23 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k) -> getr R1 24 = Z_to_bv 64 1 ->
  getr R1 26 = Z_to_bv 64 (fst r0) -> getr R1 27 = Z_to_bv 64 (fst r0 + ds_off s) ->
  rw_cells segs m1 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))] ->
  hl_recs (hs_pending h1) = r0 :: rs0 -> Z.of_nat k < dnum s -> 4096 <= ds_cap s - ulen s ->
  ds_eintr s = false ->
  bzs (firstn (Z.to_nat (dnum s)) (re_junk e1)) = ddata s ->
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 ->
  st_init_done A1 = true ->
  DPU L1 A1 s e1 h1 OUT1 (lines (ds_ref s) (firstn (S k) (ddata s))) ->
  ro_agree segs m1 ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] ->
  entry_okw L1 A1 m1 e1 ->
  src_at Bm L1 A1 m1 HA h1 ->
  others_at Bm m1 j (re_fd e) fs os ->
  DSAME e1 h1 ->
  (re_cap e1 = ds_cap s /\ bzs (re_U e1) = ds_u s /\ re_skip e1 = (if ds_skip s then 1 else 0) /\
   keys_texts (re_keys e1) = ds_H s /\ ent_ka e1 = ds_ka s /\ hs_eintr h1 = (if ds_eintr s then 1 else 0) /\
   map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = ds_pend s /\ hs_off h1 = ds_off s /\
   hs_state h1 = feed (ds_ref s) (firstn (S k) (ddata s)) /\
   hl_n (hs_expected h1) = ds_en s + Z.of_nat (length (lines (ds_ref s) (firstn (S k) (ddata s)))) /\
   hl_cap (hs_expected h1) =
     pcapm (ds_en s) (ds_ecap s) (lines (ds_ref s) (firstn (S k) (ddata s))) /\
   dwf s) ->
  (bzs PS = D ++ pstream s /\ ds_ref s = feed ST0 D /\ J1 (ds_u s) (ds_skip s) (ds_ref s) /\
   map snd (hl_recs (hs_expected h1)) =
     map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines ST0 (D ++ firstn (S k) (ddata s))) /\
   firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
   hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
   ds_no s = NO + dtot D /\ bzs LB1 = with_nul (lines ST0 D) /\
   NoDup (ds_H s) /\ same_set (ds_H s) (upds (keys_texts (re_keys e)) (lines ST0 D)) /\
   Z.of_nat (length (ds_H s)) + Z.of_nat (length (pstream s)) < 2 ^ 26 /\
   ds_en s + Z.of_nat (length (pstream s)) < 2 ^ 27) ->
  DBLK L1 A1 e1 h1 OUT1 -> DGLB D m1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13b20) m1 (seg_rom segs)) md1)
    (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using EHI GEI HG HJ PRE SEGS.
  intros s k R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D r0 rs0 RT1 G9 G18 G19 G20 G21 G23 G24 G26 G27 W32 HR KN GR Ee
    JK RP1 IN1 TR1 RO1 FR1 SAC1 EK1 SR1 OT1 SM1 LK1 HI1 BK1 GL1 OU1.
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof LK1 as (_ & _ & _ & _ & _ & _ & L7c & L8c & _ & _ & _ & WF1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (_ & _ & OFF & _ & NLE & T4 & T5).
  pose proof gfacts as (_ & _ & _ & F4 & _).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G9, G21, G23. rewrite SEGS.
    apply dr_bnext; clear - OFF NLE T4 T5 F4 KN; lia. }
  intros ms (can & [(NE & ->)|(EQ & ->)] & EQ2);
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity); apply SR_ret.
  - left. exists R2, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, r0, rs0.
    split; [reflexivity|].
    split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; f_equal; clear - KN; lia|].
    split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; f_equal; clear - KN; lia|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; f_equal; clear - KN; lia|].
    split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|].
    split; [exact W32|].
    split; [exact HR|]. split; [clear - KN NE; lia|]. split; [exact GR|]. split; [exact Ee|]. split; [exact JK|].
    split; [exact RP1|]. split; [exact IN1|]. split; [exact TR1|]. split; [exact RO1|]. split; [exact FR1|].
    split; [exact SAC1|]. split; [exact EK1|]. split; [exact SR1|]. split; [exact OT1|]. split; [exact SM1|].
    split; [exact LK1|]. split; [exact HI1|]. split; [exact BK1|]. split; [exact GL1 | exact OU1].
  - right. split; [clear - EQ; lia|].
    assert (FA : firstn (S k) (ddata s) = ddata s)
      by (apply firstn_all2; rewrite (rbl_ddata_len s WF1); clear - EQ; lia).
    rewrite FA in TR1, LK1, HI1.
    exists R2, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, r0, rs0.
    split; [reflexivity|].
    split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; f_equal; clear - EQ; lia|].
    split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; f_equal; clear - EQ; lia|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity; simp_regs; f_equal; clear - EQ; lia|].
    split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|].
    split; [exact W32|].
    split; [exact HR|]. split; [clear - KN; lia|]. split; [exact GR|]. split; [exact Ee|]. split; [exact JK|].
    split; [exact RP1|]. split; [exact IN1|]. split; [exact TR1|]. split; [exact RO1|]. split; [exact FR1|].
    split; [exact SAC1|]. split; [exact EK1|]. split; [exact SR1|]. split; [exact OT1|]. split; [exact SM1|].
    split; [exact LK1|]. split; [exact HI1|]. split; [exact BK1|]. split; [exact GL1 | exact OU1].
Qed.

Lemma UB_rbl_zero_ovl : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29
    x30 x31 (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X p p0 ta part np ovl : Z) (c : byte),
  bytes_at rsegs m p [c] ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] ->
  mem_inv rsegs m -> 0 < ovl < 2 ^ 31 -> 0 <= np < 2 ^ 63 -> 0 < part -> part + np < 2 ^ 64 ->
  (part + np + 1 <= X + 168 \/ X + 188 <= part + np) -> 0 <= p0 <= p -> 0 < p < 2 ^ 64 -> 0 < ta < 2 ^ 64 ->
  bv_unsigned c = 0 ->
  evt rsegs (fun ms => exists m' x10',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X)
                   (Z_to_bv 64 p) x22 (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30
                   x31)
              Fr (Z_to_bv 64 0x13b20) fc None m' (seg_rom rsegs) /\
      munch [(X + 176, X + 188)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (X + 176) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) (Z_to_bv 64 p) x22
             (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30 x31)
        Fr (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs)).
Proof using.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29 x30 x31 Fr fc m
    X p p0 ta part np ovl c HB HO MI Hovl Hnp Hpart Hpn HQ Hp0 Hp Hta C0.
  destruct (dr_cut m (X + 168) (X + 176) [C8 (Z_to_bv 64 part)] [C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] HO
              ltac:(cbn [cells_size csize]; clear - X; lia)) as [_ HO2].
  destruct (dr_cut m (X + 168) (X + 184) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np)] [C4 (Z_to_bv 64 ovl)] HO
              ltac:(cbn [cells_size csize]; clear - X; lia)) as [HO1 _].
  eapply evt_cut.
  { apply (dr_byte x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29 x30 x31
             Fr fc m X p p0 ta part np ovl (part + np) c c);
      [exact HB | exact HO | reflexivity | intros X1; exfalso; exact (X1 C0) | exact HQ | exact MI |
       clear - Hovl; lia | exact Hnp | exact Hpart | exact Hpn | exact Hp0 | exact Hp | exact Hta]. }
  intros ms [(_ & x10' & ->)|[(X1 & _)|[(X1 & _)|(X1 & _)]]]; [| exfalso; exact (X1 C0) ..].
  eapply evt_cut; [eapply dr_lend; [exact HO1 | clear - Hovl; lia]|].
  intros ms [(O1 & ->)|(O0 & _)]; [|exfalso; clear - O0 Hovl; lia].
  eapply evt_mono; [eapply dr_lreset; [exact HO2 | exact MI]|].
  intros ms (m' & -> & MU & WM & MI' & HC). exists m', x10'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI' | exact HC].
Qed.

Lemma rbl_skip : forall s k c b, DRB s k c -> nth_error (ddata s) k = Some b -> b <> 0 ->
  ls_k (feed (ds_ref s) (firstn k (ddata s))) = true ->
  SR segs c (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using All.
  intros s k c b (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 &
    G20 & G21 & G23 & G24 & G26 & G27 & W32 & HR & KN & GR & Ee & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 &
    OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) EB B0 LKs.
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (TI & TC & OFF & DH & NLE & T4 & T5).
  destruct (rbl_byte s k r0 m1 TC DH ltac:(clear - OFF; lia) NLE KN) as (c & BC & EC).
  rewrite EB in EC. injection EC as EC.
  pose proof (blk_rng _ _ _ _ _ _ M1 S11) as PR.
  pose proof (rbl_apart _ _ _ _ _ _ M1 S11 ltac:(reflexivity)) as PA.
  pose proof S7 as S7r. rewrite SEGS in S7r.
  destruct (dr_cut m1 (HA + 32) (XH + 168) [C8 (Z_to_bv 64 (hs_off h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia)) as [S7a HC].
  assert (BCn : bytes_at rsegs (normalize rsegs m1) (fst r0 + ds_off s + Z.of_nat k) [c])
    by (apply (bytes_at_normalize rsegs m1 _ _ RO1r); rewrite <- SEGS; exact BC).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  rewrite <- L9c in LKs. assert (KT : ls_k (hs_state h1) = true) by exact LKs.
  unfold hs_state in LKs. cbn [ls_k] in LKs. apply Z.eqb_eq in LKs.
  assert (HCn : rw_cells rsegs (normalize rsegs m1) (XH + 168)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))])
    by (apply rbl_norm_hi; [exact RO1r | exact HC | clear - F11; unfold DR_TU in *; lia]).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20, G21, G23, G24, G26, G27. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply dr_byte with (Q := hs_partial h1 + hs_npartial h1) (jb := c);
      [exact BCn | exact HCn | reflexivity | intros _ X; exfalso; clear - X LKs; lia | | apply mem_inv_normalize |
       clear - S10; lia | clear - S9; lia | clear - PR; lia | clear - PR S9 F4; lia | clear - OFF T4; lia |
       clear - OFF NLE KN T4 T5 F4; lia | clear - T4 T5 F4; lia].
    clear - PA S9 F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
  intros ms (can & (s0' & HQ & REL & ROS) & EQ).
  destruct HQ as [(C0 & _)|[(_ & _ & x10' & x11' & ->)|[(_ & O0 & _)|(_ & O0 & _)]]];
    [exfalso; apply B0; rewrite EC; exact C0 | | exfalso; clear - O0 LKs; lia | exfalso; clear - O0 LKs; lia].
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 (normalize rsegs m1) m2 [] RO1r REL2 ROS (munch_refl _ _) (wmono_refl _ _)) as (MU2 & WM2 & RO2).
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS2.
  assert (C2 : rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1));
                                           C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]).
  { eapply rw_tr; [exact MS2 | exact S7 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia | exact I]. }
  assert (P2 : rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) (hs_pjunk h1)]).
  { eapply rw_tr; [exact MS2 | exact S14 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha PR F4; lia | exact I]. }
  assert (W32' : rw_cells segs m2 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))]).
  { eapply rw_tr; [exact MS2 | exact W32 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha F1 F2 F3; lia | exact I]. }
  destruct (rbl_simple s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D [] (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1)
              RP1 FR1 SAC1 EK1 SR1 OT1 SM1 H7h H8h BK1 GL1 OU1 MU2 WM2s (fun a _ _ _ => I) C2 S9 S10 S13 P2 S15)
    as (RP2 & FR2 & SAC2 & EK2 & SR2 & OT2 & GL2 & OU2).
  replace (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
              (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)) with h1 in SR2
    by (destruct h1; reflexivity).
  destruct (rbl_model s D k b H2h EB) as (MF & ML & ML0). rewrite <- L9c in MF, ML, ML0.
  rewrite (step_nz_k (hs_state h1) b B0 KT) in MF, ML, ML0. cbn [fst snd] in MF, ML, ML0.
  rewrite app_nil_r in ML, ML0.
  apply (UB_rbl_fin s k R2 L1 A1 m2 md1 e1 h1 OUT1 junk1 LB1 D r0 rs0).
  - unfold RT. repeat match goal with |- _ /\ _ => split end; rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - exact W32'.
  - exact HR.
  - exact KN.
  - exact GR.
  - exact Ee.
  - exact JK.
  - exact RP2.
  - exact IN1.
  - rewrite ML. exact TR1.
  - rewrite SEGS. exact RO2.
  - exact FR2.
  - exact SAC2.
  - exact EK2.
  - exact SR2.
  - exact OT2.
  - exact SM1.
  - rewrite MF, ML. repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity].
  - rewrite ML0. repeat match goal with |- _ /\ _ => split end; assumption.
  - exact BK1.
  - exact GL2.
  - exact OU2.
Qed.

Lemma rbl_long : forall s k c b, DRB s k c -> nth_error (ddata s) k = Some b -> b <> 0 ->
  ls_k (feed (ds_ref s) (firstn k (ddata s))) = false ->
  length (ls_w (feed (ds_ref s) (firstn k (ddata s)))) = LINE_LIMIT ->
  SR segs c (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using All.
  intros s k c b (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 &
    G20 & G21 & G23 & G24 & G26 & G27 & W32 & HR & KN & GR & Ee & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 &
    OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) EB B0 LKs LL.
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (TI & TC & OFF & DH & NLE & T4 & T5).
  destruct (rbl_byte s k r0 m1 TC DH ltac:(clear - OFF; lia) NLE KN) as (c & BC & EC).
  rewrite EB in EC. injection EC as EC.
  pose proof (blk_rng _ _ _ _ _ _ M1 S11) as PR.
  pose proof (rbl_apart _ _ _ _ _ _ M1 S11 ltac:(reflexivity)) as PA.
  pose proof S7 as S7r. rewrite SEGS in S7r.
  destruct (dr_cut m1 (HA + 32) (XH + 168) [C8 (Z_to_bv 64 (hs_off h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia)) as [S7a HC].
  assert (BCn : bytes_at rsegs (normalize rsegs m1) (fst r0 + ds_off s + Z.of_nat k) [c])
    by (apply (bytes_at_normalize rsegs m1 _ _ RO1r); rewrite <- SEGS; exact BC).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  rewrite <- L9c in LKs, LL. assert (KF : ls_k (hs_state h1) = false) by exact LKs.
  unfold hs_state in LKs. cbn [ls_k] in LKs. apply Z.eqb_neq in LKs.
  assert (OV0 : hs_overlong h1 = 0) by (clear - S10 LKs; lia).
  assert (NP6 : hs_npartial h1 = 6000).
  { pose proof LL as LL'. unfold hs_state, hs_W in LL'. cbn [ls_w] in LL'. unfold bzs in LL'.
    rewrite length_map, length_firstn in LL'. replace LINE_LIMIT with (Z.to_nat 6000) in LL' by reflexivity.
    clear - LL' S9 S13. lia. }
  assert (HCn : rw_cells rsegs (normalize rsegs m1) (XH + 168)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))])
    by (apply rbl_norm_hi; [exact RO1r | exact HC | clear - F11; unfold DR_TU in *; lia]).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20, G21, G23, G24, G26, G27. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply dr_byte with (Q := hs_partial h1 + hs_npartial h1) (jb := c);
      [exact BCn | exact HCn | reflexivity | intros _ _ X; exfalso; exact (X NP6) | | apply mem_inv_normalize |
       clear - S10; lia | clear - S9; lia | clear - PR; lia | clear - PR S9 F4; lia | clear - OFF T4; lia |
       clear - OFF NLE KN T4 T5 F4; lia | clear - T4 T5 F4; lia].
    clear - PA S9 F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
  intros ms (can & (s0' & HQ & REL & ROS) & EQ).
  destruct HQ as [(C0 & _)|[(_ & O1 & _)|[(_ & _ & _ & m' & x10' & x11' & x12' & -> & MU & WM & MI & HC3)|
                                         (_ & _ & N0 & _)]]];
    [exfalso; apply B0; rewrite EC; exact C0 | exfalso; exact (O1 OV0) | | exfalso; exact (N0 NP6)].
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HC3) as HC3'.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS2.
  assert (C2 : rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1));
                                           C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 1)]).
  { assert (Xa : rw_cells rsegs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1))]).
    { rewrite <- SEGS. eapply rw_tr; [exact MS2 | rewrite SEGS; exact S7a |]. intros a Ha. cbn [cells_size csize] in Ha.
      split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia|]. cbn [outside].
      split; [clear - Ha F11; unfold DR_TU, G_S, SRC_SIZE in *; lia | exact I]. }
    rewrite SEGS. apply (dr_join m2 (HA + 32) (XH + 168) _ _ Xa HC3'). cbn [cells_size csize].
    clear - F11. unfold DR_TU, G_S, SRC_SIZE in *. lia. }
  assert (P2 : rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) (hs_pjunk h1)]).
  { eapply rw_tr; [exact MS2 | exact S14 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha PR F4; lia|]. cbn [outside].
    split; [clear - Ha PA F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia | exact I]. }
  assert (W32' : rw_cells segs m2 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))]).
  { eapply rw_tr; [exact MS2 | exact W32 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha F1 F2 F3; lia|]. cbn [outside].
    split; [clear - Ha F1 F3 F11; unfold DR_TU in *; lia | exact I]. }
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 48 <= a < HA + 60) ->
                 ~ (hs_partial h1 <= a < hs_partial h1 + 6000) -> outside [(XH + 184, XH + 188)] a).
  { intros a _ Hn _. cbn [outside]. split; [clear - Hn F11; unfold DR_TU, G_S, SRC_SIZE in *; lia | exact I]. }
  destruct (rbl_simple s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D [(XH + 184, XH + 188)] (hs_pjunk h1) (hs_npartial h1) 1
              RP1 FR1 SAC1 EK1 SR1 OT1 SM1 H7h H8h BK1 GL1 OU1 MU2 WM2s HW C2 S9 (or_intror eq_refl) S13 P2 S15)
    as (RP2 & FR2 & SAC2 & EK2 & SR2 & OT2 & GL2 & OU2).
  destruct (rbl_model s D k b H2h EB) as (MF & ML & ML0). rewrite <- L9c in MF, ML, ML0.
  rewrite (step_nz_full (hs_state h1) b B0 KF LL) in MF, ML, ML0. cbn [fst snd] in MF, ML, ML0.
  rewrite app_nil_r in ML, ML0.
  apply (UB_rbl_fin s k R2 L1 A1 m2 md1 e1 (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1)
           (hs_off h1) (hs_partial h1) (hs_pjunk h1) (hs_npartial h1) 1 (hs_pad h1) (hs_expected h1) (hs_held h1))
           OUT1 junk1 LB1 D r0 rs0).
  - unfold RT. repeat match goal with |- _ /\ _ => split end; rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - exact W32'.
  - exact HR.
  - exact KN.
  - exact GR.
  - exact Ee.
  - exact JK.
  - exact RP2.
  - exact IN1.
  - rewrite ML. exact TR1.
  - rewrite SEGS. exact RO2.
  - exact FR2.
  - exact SAC2.
  - exact EK2.
  - exact SR2.
  - exact OT2.
  - exact SM1.
  - rewrite MF, ML. repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity].
  - rewrite ML0. repeat match goal with |- _ /\ _ => split end; assumption.
  - exact BK1.
  - exact GL2.
  - exact OU2.
Qed.

Lemma rbl_add : forall s k c b, DRB s k c -> nth_error (ddata s) k = Some b -> b <> 0 ->
  ls_k (feed (ds_ref s) (firstn k (ddata s))) = false ->
  length (ls_w (feed (ds_ref s) (firstn k (ddata s)))) <> LINE_LIMIT ->
  SR segs c (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using All.
  intros s k c b (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 &
    G20 & G21 & G23 & G24 & G26 & G27 & W32 & HR & KN & GR & Ee & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 &
    OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) EB B0 LKs LL.
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (TI & TC & OFF & DH & NLE & T4 & T5).
  destruct (rbl_byte s k r0 m1 TC DH ltac:(clear - OFF; lia) NLE KN) as (c & BC & EC).
  rewrite EB in EC. injection EC as EC.
  pose proof (blk_rng _ _ _ _ _ _ M1 S11) as PR.
  pose proof (rbl_apart _ _ _ _ _ _ M1 S11 ltac:(reflexivity)) as PA.
  pose proof S7 as S7r. rewrite SEGS in S7r.
  destruct (dr_cut m1 (HA + 32) (XH + 168) [C8 (Z_to_bv 64 (hs_off h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia)) as [S7a HC].
  assert (BCn : bytes_at rsegs (normalize rsegs m1) (fst r0 + ds_off s + Z.of_nat k) [c])
    by (apply (bytes_at_normalize rsegs m1 _ _ RO1r); rewrite <- SEGS; exact BC).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  rewrite <- L9c in LKs, LL. assert (KF : ls_k (hs_state h1) = false) by exact LKs.
  unfold hs_state in LKs. cbn [ls_k] in LKs. apply Z.eqb_neq in LKs.
  assert (OV0 : hs_overlong h1 = 0) by (clear - S10 LKs; lia).
  assert (NP6 : hs_npartial h1 < 6000).
  { pose proof LL as LL'. unfold hs_state, hs_W in LL'. cbn [ls_w] in LL'. unfold bzs in LL'.
    rewrite length_map, length_firstn in LL'. replace LINE_LIMIT with (Z.to_nat 6000) in LL' by reflexivity.
    clear - LL' S9 S13. lia. }
  pose proof S14 as S14r. rewrite SEGS in S14r.
  replace (Z.to_nat 6000) with (length (hs_pjunk h1)) in S14r by (clear - S13; lia).
  destruct (rbl_cb_at m1 (hs_partial h1) (hs_pjunk h1) (Z.to_nat (hs_npartial h1)) ltac:(clear - S9 S13 NP6; lia) S14r)
    as (b1 & jb & b2 & PJ & LB1' & PB1 & PJB & PB2).
  assert (PJBn : rw_cells rsegs (normalize rsegs m1) (hs_partial h1 + hs_npartial h1) [C1 jb]).
  { rewrite Z2Nat.id in PJB by (clear - S9; lia).
    apply (rbl_norm_blk L1 A1 m1 md1 m1 _ _ (hs_partial h1) 6000 M1 RO1r PJB S11);
      [clear - S9; lia | cbn [cells_size csize]; clear - S9 NP6; lia]. }
  assert (HCn : rw_cells rsegs (normalize rsegs m1) (XH + 168)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))])
    by (apply rbl_norm_hi; [exact RO1r | exact HC | clear - F11; unfold DR_TU in *; lia]).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20, G21, G23, G24, G26, G27. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply dr_byte with (Q := hs_partial h1 + hs_npartial h1) (jb := jb);
      [exact BCn | exact HCn | reflexivity | intros _ _ _; exact PJBn | | apply mem_inv_normalize |
       clear - S10; lia | clear - S9; lia | clear - PR; lia | clear - PR S9 F4; lia | clear - OFF T4; lia |
       clear - OFF NLE KN T4 T5 F4; lia | clear - T4 T5 F4; lia].
    clear - PA S9 F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
  intros ms (can & (s0' & HQ & REL & ROS) & EQ).
  destruct HQ as [(C0 & _)|[(_ & O1 & _)|[(_ & _ & N0 & _)|
                    (_ & _ & _ & m' & x10' & x11' & x12' & x13' & x14' & -> & MU & WM & MI & HC3 & HQ3)]]];
    [exfalso; apply B0; rewrite EC; exact C0 | exfalso; exact (O1 OV0) | exfalso; clear - N0 NP6; lia |].
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HC3) as HC3'.
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HQ3) as HQ3'.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS2.
  assert (Pout : forall a, hs_partial h1 <= a < hs_partial h1 + 6000 -> a <> hs_partial h1 + hs_npartial h1 ->
                   0 <= a < 2 ^ 64 /\ outside [(XH + 176, XH + 184);
                     (hs_partial h1 + hs_npartial h1, hs_partial h1 + hs_npartial h1 + 1)] a).
  { intros a Ha Hn. split; [clear - Ha PR F4; lia|]. cbn [outside].
    split; [clear - Ha PA F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia|].
    split; [clear - Hn; lia | exact I]. }
  assert (LP : length (hs_pjunk h1) = (length b1 + S (length b2))%nat) by (rewrite PJ, length_app; reflexivity).
  assert (PB1' : rw_cells rsegs m2 (hs_partial h1) [CB (length b1) b1]).
  { rewrite <- SEGS. eapply rw_tr; [exact MS2 | rewrite SEGS; exact PB1 |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply Pout; clear - Ha LB1' S9; lia. }
  assert (PB2' : rw_cells rsegs m2 (hs_partial h1 + Z.of_nat (Z.to_nat (hs_npartial h1)) + 1) [CB (length b2) b2]).
  { rewrite <- SEGS. eapply rw_tr; [exact MS2 | rewrite SEGS; exact PB2 |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply Pout; clear - Ha LB1' LP S9 S13; lia. }
  assert (P2 : rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) (b1 ++ c :: b2)]).
  { rewrite SEGS. replace (Z.to_nat 6000) with (length b1 + S (length b2))%nat by (clear - LP S13; lia).
    apply rbl_cb_join; [exact PB1' | rewrite LB1', Z2Nat.id by (clear - S9; lia); exact HQ3' | rewrite LB1'; exact PB2']. }
  assert (C2 : rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1));
                                           C8 (Z_to_bv 64 (hs_npartial h1 + 1)); C4 (Z_to_bv 64 (hs_overlong h1))]).
  { assert (Xa : rw_cells rsegs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1))]).
    { rewrite <- SEGS. eapply rw_tr; [exact MS2 | rewrite SEGS; exact S7a |]. intros a Ha. cbn [cells_size csize] in Ha.
      split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia|]. cbn [outside].
      split; [clear - Ha F11; unfold DR_TU, G_S, SRC_SIZE in *; lia|].
      split; [clear - Ha PA F11 S9 NP6; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia | exact I]. }
    rewrite SEGS. apply (dr_join m2 (HA + 32) (XH + 168) _ _ Xa HC3'). cbn [cells_size csize].
    clear - F11. unfold DR_TU, G_S, SRC_SIZE in *. lia. }
  assert (W32' : rw_cells segs m2 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))]).
  { eapply rw_tr; [exact MS2 | exact W32 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha F1 F2 F3; lia|]. cbn [outside].
    split; [clear - Ha F1 F3 F11; unfold DR_TU in *; lia|].
    split; [clear - Ha F1 PR S9 NP6; lia | exact I]. }
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 48 <= a < HA + 60) ->
                 ~ (hs_partial h1 <= a < hs_partial h1 + 6000) ->
                 outside [(XH + 176, XH + 184); (hs_partial h1 + hs_npartial h1, hs_partial h1 + hs_npartial h1 + 1)] a).
  { intros a _ Hn Hp. cbn [outside]. split; [clear - Hn F11; unfold DR_TU, G_S, SRC_SIZE in *; lia|].
    split; [clear - Hp S9 NP6; lia | exact I]. }
  assert (W1 : hs_W h1 = b1) by (unfold hs_W; rewrite PJ, <- LB1'; apply rbl_firstn_len).
  assert (NZ : ~ In (Z_to_bv 8 0) (firstn (Z.to_nat (hs_npartial h1 + 1)) (b1 ++ c :: b2))).
  { replace (Z.to_nat (hs_npartial h1 + 1)) with (S (length b1)) by (clear - LB1' S9; lia). rewrite rbl_firstn_mid.
    intros X. apply in_app_or in X as [X|[X|[]]].
    - apply S15. rewrite W1. exact X.
    - apply B0. rewrite EC. unfold bz. rewrite X. reflexivity. }
  destruct (rbl_simple s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D
              [(XH + 176, XH + 184); (hs_partial h1 + hs_npartial h1, hs_partial h1 + hs_npartial h1 + 1)]
              (b1 ++ c :: b2) (hs_npartial h1 + 1) (hs_overlong h1)
              RP1 FR1 SAC1 EK1 SR1 OT1 SM1 H7h H8h BK1 GL1 OU1 MU2 WM2s HW C2 ltac:(clear - S9 NP6; lia) S10
              ltac:(rewrite length_app; cbn [length]; clear - LP S13; lia) P2 NZ)
    as (RP2 & FR2 & SAC2 & EK2 & SR2 & OT2 & GL2 & OU2).
  destruct (rbl_model s D k b H2h EB) as (MF & ML & ML0). rewrite <- L9c in MF, ML, ML0.
  rewrite (step_nz_add (hs_state h1) b B0 KF LL) in MF, ML, ML0. cbn [fst snd] in MF, ML, ML0.
  rewrite app_nil_r in ML, ML0.
  apply (UB_rbl_fin s k R2 L1 A1 m2 md1 e1 (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1)
           (hs_off h1) (hs_partial h1) (b1 ++ c :: b2) (hs_npartial h1 + 1) (hs_overlong h1) (hs_pad h1)
           (hs_expected h1) (hs_held h1)) OUT1 junk1 LB1 D r0 rs0).
  - unfold RT. repeat match goal with |- _ /\ _ => split end; rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - exact W32'.
  - exact HR.
  - exact KN.
  - exact GR.
  - exact Ee.
  - exact JK.
  - exact RP2.
  - exact IN1.
  - rewrite ML. exact TR1.
  - rewrite SEGS. exact RO2.
  - exact FR2.
  - exact SAC2.
  - exact EK2.
  - exact SR2.
  - exact OT2.
  - exact SM1.
  - rewrite MF, ML. repeat match goal with |- _ /\ _ => split end; try assumption.
    unfold hs_state, hs_W. cbn [hs_npartial hs_pjunk hs_overlong ls_w].
    replace (Z.to_nat (hs_npartial h1 + 1)) with (S (length b1)) by (clear - LB1' S9; lia).
    rewrite rbl_firstn_mid, PJ, <- LB1', rbl_firstn_len, OV0. unfold bzs. rewrite map_app. cbn [map]. rewrite EC.
    reflexivity.
  - rewrite ML0. repeat match goal with |- _ /\ _ => split end; assumption.
  - exact BK1.
  - exact GL2.
  - exact OU2.
Qed.

Lemma rbl_reset : forall s k c b, DRB s k c -> nth_error (ddata s) k = Some b -> b = 0 ->
  ls_k (feed (ds_ref s) (firstn k (ddata s))) = true ->
  SR segs c (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using All.
  intros s k c b (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 &
    G20 & G21 & G23 & G24 & G26 & G27 & W32 & HR & KN & GR & Ee & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 &
    OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) EB B0 LKs.
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (TI & TC & OFF & DH & NLE & T4 & T5).
  destruct (rbl_byte s k r0 m1 TC DH ltac:(clear - OFF; lia) NLE KN) as (c & BC & EC).
  rewrite EB in EC. injection EC as EC.
  pose proof (blk_rng _ _ _ _ _ _ M1 S11) as PR.
  pose proof (rbl_apart _ _ _ _ _ _ M1 S11 ltac:(reflexivity)) as PA.
  pose proof S7 as S7r. rewrite SEGS in S7r.
  destruct (dr_cut m1 (HA + 32) (XH + 168) [C8 (Z_to_bv 64 (hs_off h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia)) as [S7a HC].
  assert (BCn : bytes_at rsegs (normalize rsegs m1) (fst r0 + ds_off s + Z.of_nat k) [c])
    by (apply (bytes_at_normalize rsegs m1 _ _ RO1r); rewrite <- SEGS; exact BC).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  rewrite <- L9c in LKs. assert (KT : ls_k (hs_state h1) = true) by exact LKs.
  unfold hs_state in LKs. cbn [ls_k] in LKs. apply Z.eqb_eq in LKs.
  assert (HCn : rw_cells rsegs (normalize rsegs m1) (XH + 168)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))])
    by (apply rbl_norm_hi; [exact RO1r | exact HC | clear - F11; unfold DR_TU in *; lia]).
  assert (C0 : bv_unsigned c = 0) by (unfold bz in EC; clear - EC B0; lia).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20, G21, G23, G24, G26, G27. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply UB_rbl_zero_ovl; [exact BCn | exact HCn | apply mem_inv_normalize | clear - LKs; lia | clear - S9; lia |
                            clear - PR; lia | clear - PR S9 F4; lia | | clear - OFF T4; lia |
                            clear - OFF NLE KN T4 T5 F4; lia | clear - T4 T5 F4; lia | exact C0].
    clear - PA S9 F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
  intros ms (can & (s0' & (m' & x10' & -> & MU & WM & MI & HC3) & REL & ROS) & EQ).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HC3) as HC3'.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS2.
  destruct (dr_cut m1 (HA + 32) (HA + 48) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; lia)) as [S7b _].
  assert (C2 : rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1));
                                           C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
  { assert (Xa : rw_cells rsegs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1))]).
    { rewrite <- SEGS. eapply rw_tr; [exact MS2 | rewrite SEGS; exact S7b |]. intros a Ha. cbn [cells_size csize] in Ha.
      split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia|]. cbn [outside].
      split; [clear - Ha F11; unfold DR_TU, G_S, SRC_SIZE in *; lia | exact I]. }
    rewrite SEGS. apply (dr_join m2 (HA + 32) (XH + 176) _ _ Xa HC3'). cbn [cells_size csize].
    clear - F11. unfold DR_TU, G_S, SRC_SIZE in *. lia. }
  assert (P2 : rw_cells segs m2 (hs_partial h1) [CB (Z.to_nat 6000) (hs_pjunk h1)]).
  { eapply rw_tr; [exact MS2 | exact S14 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha PR F4; lia|]. cbn [outside].
    split; [clear - Ha PA F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia | exact I]. }
  assert (W32' : rw_cells segs m2 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))]).
  { eapply rw_tr; [exact MS2 | exact W32 |]. intros a Ha. cbn [cells_size csize] in Ha.
    split; [clear - Ha F1 F2 F3; lia|]. cbn [outside].
    split; [clear - Ha F1 F3 F11; unfold DR_TU in *; lia | exact I]. }
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 48 <= a < HA + 60) ->
                 ~ (hs_partial h1 <= a < hs_partial h1 + 6000) -> outside [(XH + 176, XH + 188)] a).
  { intros a _ Hn _. cbn [outside]. split; [clear - Hn F11; unfold DR_TU, G_S, SRC_SIZE in *; lia | exact I]. }
  destruct (rbl_simple s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D [(XH + 176, XH + 188)] (hs_pjunk h1) 0 0
              RP1 FR1 SAC1 EK1 SR1 OT1 SM1 H7h H8h BK1 GL1 OU1 MU2 WM2s HW C2 ltac:(clear - F11; lia)
              (or_introl eq_refl) S13 P2 ltac:(intros []))
    as (RP2 & FR2 & SAC2 & EK2 & SR2 & OT2 & GL2 & OU2).
  destruct (rbl_model s D k b H2h EB) as (MF & ML & ML0). rewrite <- L9c, B0 in MF, ML, ML0.
  rewrite step_zero, KT in MF, ML, ML0. cbn [fst snd] in MF, ML, ML0. rewrite app_nil_r in ML, ML0.
  apply (UB_rbl_fin s k R2 L1 A1 m2 md1 e1 (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1)
           (hs_off h1) (hs_partial h1) (hs_pjunk h1) 0 0 (hs_pad h1) (hs_expected h1) (hs_held h1))
           OUT1 junk1 LB1 D r0 rs0).
  - unfold RT. repeat match goal with |- _ /\ _ => split end; rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - rgw X2.
  - exact W32'.
  - exact HR.
  - exact KN.
  - exact GR.
  - exact Ee.
  - exact JK.
  - exact RP2.
  - exact IN1.
  - rewrite ML. exact TR1.
  - rewrite SEGS. exact RO2.
  - exact FR2.
  - exact SAC2.
  - exact EK2.
  - exact SR2.
  - exact OT2.
  - exact SM1.
  - rewrite MF, ML. repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity].
  - rewrite ML0. repeat match goal with |- _ /\ _ => split end; assumption.
  - exact BK1.
  - exact GL2.
  - exact OU2.
Qed.

Lemma rbl_dblk : forall L1 A1 m1 md1 L2 A2 m2 md2 e1 h1 OUT1 pj np ovl ex,
  MR L1 A1 m1 md1 -> MR L2 A2 m2 md2 -> DBLK L1 A1 e1 h1 OUT1 -> entry_okw L1 A1 m1 e1 -> src_at Bm L1 A1 m1 HA h1 ->
  (OUT1 = 0 \/ exists k, In (OUT1, k) (blocks L1 A1) /\ 0 < k) ->
  list_at Bm L2 A2 m2 (HA + 64) ex true ->
  relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 regs m2 md2 ->
  (forall q m, In (q, m) (blocks L1 A1) -> ~ In q (list_blocks (hs_expected h1)) -> In (q, m) (blocks L2 A2)) ->
  (forall q m, In (q, m) (blocks L2 A2) ->
     (In (q, m) (blocks L1 A1) /\ (0 < m -> ~ In q (list_blocks (hs_expected h1)))) \/ In q (list_blocks ex)) ->
  (forall q m, In (q, m) (blocks L1 A1) -> 0 < m -> ~ In q (list_blocks (hs_expected h1)) -> ~ In q (list_blocks ex)) ->
  DBLK L2 A2 e1 (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
                    pj np ovl (hs_pad h1) ex (hs_held h1)) OUT1.
Proof using NODUP PRE.
  intros L1 A1 m1 md1 L2 A2 m2 md2 e1 h1 OUT1 pj np ovl ex M1 M2 (ND & GI & B3 & B4 & B5) EK1 SR1 OB LX RP2 KP CL NN.
  pose proof SR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & _).
  apply NoDup_ListNoDup in ND. unfold hs_blocks in ND.
  assert (ND2 : List.NoDup ((G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1]) ++
                            list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
  { cbn [app]. rewrite <- !app_assoc. exact ND. }
  assert (KN : forall y, In y ((G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1]) ++
                               list_blocks (hs_held h1)) -> ~ In y (list_blocks ex)).
  { intros y Hy Hx. pose proof (rbl_nd_out _ _ _ y ND2 Hy) as NE.
    assert (YP : y = 0 \/ exists k, In (y, k) (blocks L1 A1) /\ 0 < k).
    { apply in_app_or in Hy as [Hy|Hy].
      - destruct Hy as [<-|[<-|Hy]].
        + right. exists SRC_TABLE. split; [exact GI | unfold SRC_TABLE, SRC_ENTRY; clear - GI; lia].
        + exact OB.
        + right. apply in_app_or in Hy as [Hy|Hy]; [exact (rbl_eb_pos _ _ _ _ _ EK1 Hy)|].
          apply (rbl_hb_pos _ _ _ _ _ _ SR1). unfold hs_blocks. rewrite !in_app_iff in Hy. rewrite !in_app_iff.
          clear - Hy. tauto.
      - right. apply (rbl_hb_pos _ _ _ _ _ _ SR1). unfold hs_blocks. rewrite !in_app_iff. clear - Hy. tauto. }
    destruct YP as [Y0|(ky & Hk & Hk0)].
    - destruct (rbl_lb_pos _ _ _ _ _ _ _ LX Hx) as (kx & Hkx & _). pose proof (blk_rng _ _ _ _ _ _ M2 Hkx) as XR.
      clear - Y0 XR. lia.
    - exact (NN y ky Hk Hk0 NE Hx). }
  unfold DBLK. split; [|split; [|split; [|split]]].
  - apply NoDup_ListNoDup. unfold hs_blocks. cbn [hs_pending hs_partial hs_expected hs_held].
    replace (G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1] ++ list_blocks ex ++
             list_blocks (hs_held h1))
      with ((G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1]) ++ list_blocks ex ++
            list_blocks (hs_held h1)) by (cbn [app]; rewrite <- !app_assoc; reflexivity).
    apply (rbl_nd_swap _ _ _ _ ND2 (rbl_lb_nd _ _ _ _ _ _ LX)). exact KN.
  - apply KP; [exact GI|]. apply (rbl_nd_out _ _ _ G ND2). left. reflexivity.
  - intros q m Hq HO HN. apply (rbl_rp_keep _ _ _ _ _ q m RP2 Hq). intros [(_ & X)|X]; [exact (HO X) | exact (HN X)].
  - intros q m Hq. destruct (CL q m Hq) as [(Hq1 & Hn)|Hx].
    + destruct (B4 q m Hq1) as [Ho|[Hi|Ho]]; [left; exact Ho | right; left | right; right; exact Ho].
      unfold hs_blocks in Hi |- *. cbn [hs_pending hs_partial hs_expected hs_held].
      rewrite !in_app_iff in Hi. rewrite !in_app_iff.
      destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]]; [clear - Hi; tauto | clear - Hi; tauto | clear - Hi; tauto | |
                                              clear - Hi; tauto].
      exfalso. destruct (rbl_lb_pos _ _ _ _ _ _ _ S16 Hi) as (k & Hk & Hk0).
      pose proof (NODUP _ _ _ _ M1) as NDb. apply NoDup_ListNoDup in NDb.
      pose proof (sb_nodup_fst _ q m k NDb Hq1 Hk) as Emk. subst k. exact (Hn Hk0 Hi).
    + right; left. unfold hs_blocks. cbn [hs_pending hs_partial hs_expected hs_held]. rewrite !in_app_iff.
      clear - Hx. tauto.
  - intros q m Hq Hm HO HN. destruct (B5 q m Hq Hm HO HN) as (O1 & E1' & H1').
    split; [exact O1|]. split; [exact E1'|].
    unfold hs_blocks in H1' |- *. cbn [hs_pending hs_partial hs_expected hs_held].
    rewrite !in_app_iff in H1'. rewrite !in_app_iff.
    intros [X|[X|[X|X]]]; [clear - X H1'; tauto | clear - X H1'; tauto | | clear - X H1'; tauto].
    apply (NN q m (B3 q m Hq HO HN) Hm); [intros Y; clear - Y H1'; tauto | exact X].
Qed.

Lemma rbl_pushes_app : forall l1 l2 n cp jn v rs,
  pushes_run n cp (l1 ++ l2) jn v rs =
  (fst (fst (pushes_run n cp l1 jn v rs)) ++
     fst (fst (pushes_run (n + Z.of_nat (length l1)) (snd (fst (pushes_run n cp l1 jn v rs))) l2
                (jn + nretF (fst (fst (pushes_run n cp l1 jn v rs)))) (fst (snd (pushes_run n cp l1 jn v rs)))
                (snd (snd (pushes_run n cp l1 jn v rs))))),
   snd (fst (pushes_run (n + Z.of_nat (length l1)) (snd (fst (pushes_run n cp l1 jn v rs))) l2
               (jn + nretF (fst (fst (pushes_run n cp l1 jn v rs)))) (fst (snd (pushes_run n cp l1 jn v rs)))
               (snd (snd (pushes_run n cp l1 jn v rs))))),
   snd (pushes_run (n + Z.of_nat (length l1)) (snd (fst (pushes_run n cp l1 jn v rs))) l2
          (jn + nretF (fst (fst (pushes_run n cp l1 jn v rs)))) (fst (snd (pushes_run n cp l1 jn v rs)))
          (snd (snd (pushes_run n cp l1 jn v rs))))).
Proof using All.
  induction l1 as [|l r IH]; intros l2 n cp jn v rs.
  - cbn [app pushes_run fst snd length]. rewrite Z.add_0_r, nret_nil, Nat.add_0_r. cbn [app].
    destruct (pushes_run n cp l2 jn v rs) as [[t c] vr]. reflexivity.
  - cbn [app pushes_run]. rewrite IH. cbn [fst snd]. rewrite <- app_assoc, nret_app, Nat.add_assoc.
    replace (n + Z.of_nat (length (l :: r))) with (n + 1 + Z.of_nat (length r)) by (cbn [length]; clear; lia).
    reflexivity.
Qed.

Lemma rbl_lp_nret : forall v n cp len, nretF (list_push_tra v n cp len) = (if (n =? cp)%Z then 2 else 1)%nat.
Proof using All.
  intros v n cp len. unfold list_push_tra. destruct (n =? cp); [destruct (cp =? 0)|]; reflexivity.
Qed.

Lemma rbl_lp_wf : forall v n cp len jn, p3a_ok v jn -> wf_from sptr jn (list_push_tra v n cp len).
Proof using All.
  intros v n cp len jn H. unfold list_push_tra.
  destruct (n =? cp); [destruct (cp =? 0)|]; cbn [app wf_from rets]; repeat split; try exact I; exact H.
Qed.

Lemma rbl_lp_shift : forall (b : rt_R F) (qs1 qs2 post : list sptr) v p n cp len,
  (n = cp -> cp <> 0 -> resolveF qs1 v = p) -> p3a_ok v (length qs1) ->
  length qs2 = nretF (list_push_tra (Known p) n cp len) ->
  nretF (list_push_tra v n cp len) = nretF (list_push_tra (Known p) n cp len) /\
  run_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (qs1 ++ qs2 ++ post) b (length qs1)
    (list_push_tra v n cp len) = runF F qs2 b (list_push_tra (Known p) n cp len) /\
  (room_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) (qs1 ++ qs2 ++ post) b
     (length qs1) (list_push_tra v n cp len) <-> roomF F qs2 b (list_push_tra (Known p) n cp len)).
Proof using All.
  intros b qs1 qs2 post v p n cp len Hv Ho LQ. unfold runF, roomF, run_tr, room_run, list_push_tra in *.
  destruct (Z.eqb_spec n cp) as [E|E]; [destruct (Z.eqb_spec cp 0) as [C|C]|]; cbn [app] in *.
  - split; [reflexivity|]. split; [reflexivity | clear; tauto].
  - destruct qs2 as [|q0 [|q1 [|q2 qs2]]]; cbn in LQ; try discriminate.
    cbn [run_from room_from]. rewrite (p3a_resolve_app qs1 _ v Ho), (Hv E C).
    rewrite app_nth2 by (clear; lia). rewrite Nat.sub_diag. cbn [nth resolve].
    split; [reflexivity|]. split; [reflexivity | clear; tauto].
  - split; [reflexivity|]. split; [reflexivity | clear; tauto].
Qed.

Lemma rbl_lp_room : forall (b : rt_R F) (t1 rest : trF) qs1 v p n cp len,
  wf_from sptr 0 t1 -> length qs1 = nretF t1 -> p3a_ok v (length qs1) -> (n = cp -> cp <> 0 -> resolveF qs1 v = p) ->
  (forall qs, length qs = nretF (t1 ++ list_push_tra v n cp len ++ rest) ->
     roomF F qs b (t1 ++ list_push_tra v n cp len ++ rest)) ->
  forall qs2, length qs2 = nretF (list_push_tra (Known p) n cp len) ->
    roomF F qs2 (runF F qs1 b t1) (list_push_tra (Known p) n cp len).
Proof using All.
  intros b t1 rest qs1 v p n cp len Hw LQ Ho Hv HR qs2 LQ2.
  destruct (rbl_lp_shift (runF F qs1 b t1) qs1 qs2 (repeat (SP 0 0) (nretF rest)) v p n cp len Hv Ho LQ2)
    as (N0 & _ & Rm).
  apply Rm.
  assert (LL : length (qs1 ++ qs2 ++ repeat (SP 0 0) (nretF rest)) = nretF (t1 ++ list_push_tra v n cp len ++ rest))
    by (rewrite !length_app, repeat_length, LQ, LQ2, !nret_app, N0; reflexivity).
  pose proof (HR _ LL) as R. unfold roomF, room_run in R. apply room_from_app in R as [_ R].
  apply room_from_app in R as [R _].
  rewrite (p3a_run_app _ _ _ _ qs1 (qs2 ++ repeat (SP 0 0) (nretF rest)) b 0 t1) in R
    by (exact Hw || (clear - LQ; lia)).
  rewrite Nat.add_0_l, <- LQ in R. exact R.
Qed.

Lemma rbl_live_rp : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n, WF A1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p a n -> ~ F' a ->
  live_at L2 A2 p a n.
Proof using All.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n W RP [H1 E1] HF.
  pose proof RP as (_ & _ & _ & _ & _ & AD & SV & Z0 & _). rewrite <- E1 in HF.
  pose proof (sb_ub_nonneg _ p n W H1) as N0.
  destruct (Z.eq_dec n 0) as [->|Hn].
  - destruct (Z0 p H1) as [H2 E2]. split; [exact H2 | rewrite E2; exact E1].
  - assert (H2 : In (p, n) (user_blocks A2)) by (apply (SV p n H1); [clear - N0 Hn; lia | exact HF]).
    split; [exact H2|]. rewrite (AD p n H1 H2 HF). exact E1.
Qed.

Lemma rbl_live_of : forall L1 A1 p n a m, NoDup (map fst (blocks L1 A1)) -> In (p, n) (user_blocks A1) ->
  ptr_addr L1 p = a -> In (a, m) (blocks L1 A1) -> live_at L1 A1 p a m.
Proof using All.
  intros L1 A1 p n a m HN Hp Ea Hm. pose proof (p3a_sptr_of_eq L1 A1 p n HN Hp) as Es.
  destruct (sptr_of_spec L1 A1 a m HN Hm) as [H1 _]. rewrite <- Ea, Es in H1. split; [exact H1 | exact Ea].
Qed.

Lemma rbl_f2_keep : forall {T : Type} (P Q : sptr -> Z -> Z -> Prop) (X : Z -> Prop) (qd post : list sptr)
    (f g : T -> Z) ks xs,
  (forall p a n, P p a n -> X a -> Q p a n) ->
  Forall2 (fun k x => P (resolveF qd x) (f k) (g k)) ks xs -> Forall (fun x => p3a_ok x (length qd)) xs ->
  (forall k, In k ks -> X (f k)) -> Forall2 (fun k x => Q (resolveF (qd ++ post) x) (f k) (g k)) ks xs.
Proof using All.
  intros T P Q X qd post f g ks xs HK H. induction H as [|k x ks xs Hkx _ IH]; intros HO HX; [constructor|].
  apply Forall_cons_iff in HO as [HO1 HO2]. constructor.
  - rewrite (p3a_resolve_app qd post x HO1). apply HK; [exact Hkx | apply HX; left; reflexivity].
  - apply IH; [exact HO2 | intros k' Hk'; apply HX; right; exact Hk'].
Qed.

Lemma UJ_rbl_zero_push : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29
    x30 x31 (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X p p0 ta part np : Z) (c : byte),
  bytes_at rsegs m p [c] ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m -> 0 <= np < 2 ^ 63 -> 0 < part -> part + np < 2 ^ 64 ->
  (part + np + 1 <= X + 168 \/ X + 188 <= part + np) -> 0 <= p0 <= p -> 0 < p < 2 ^ 64 -> 0 < ta < 2 ^ 64 ->
  bv_unsigned c = 0 ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13ae8) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 part) (Z_to_bv 64 np) x13 x14 x15 x16
                   x17 x18 x19 (Z_to_bv 64 X) (Z_to_bv 64 p) x22 (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta)
                   (Z_to_bv 64 p0) x28 x29 x30 x31)
              Fr (Z_to_bv 64 0x1484c) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) (Z_to_bv 64 p) x22
             (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30 x31)
        Fr (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs)).
Proof using.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29 x30 x31 Fr fc m
    X p p0 ta part np c HB HO MI Hnp Hpart Hpn HQ Hp0 Hp Hta C0.
  destruct (dr_cut m (X + 168) (X + 184) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np)] [C4 (Z_to_bv 64 0)] HO
              ltac:(cbn [cells_size csize]; clear - X; lia)) as [HO1 _].
  eapply evt_cut.
  { apply (dr_byte x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29 x30 x31
             Fr fc m X p p0 ta part np 0 (part + np) c c);
      [exact HB | exact HO | reflexivity | intros X1; exfalso; exact (X1 C0) | exact HQ | exact MI |
       clear; lia | exact Hnp | exact Hpart | exact Hpn | exact Hp0 | exact Hp | exact Hta]. }
  intros ms [(_ & x10' & ->)|[(X1 & _)|[(X1 & _)|(X1 & _)]]]; [| exfalso; exact (X1 C0) ..].
  eapply evt_mono; [eapply dr_lend; [exact HO1 | clear; lia]|].
  intros ms [(X1 & _)|(_ & ->)]; [exfalso; exact (X1 eq_refl) | reflexivity].
Qed.

Lemma rbl_push : forall s k c b, DRB s k c -> nth_error (ddata s) k = Some b -> b = 0 ->
  ls_k (feed (ds_ref s) (firstn k (ddata s))) = false ->
  SR segs c (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using All.
  intros s k c b (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 &
    G20 & G21 & G23 & G24 & G26 & G27 & W32 & HR & KN & GR & Ee & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 &
    OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) EB B0 LKs.
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (TI & TC & OFF & DH & NLE & T4 & T5).
  destruct (rbl_byte s k r0 m1 TC DH ltac:(clear - OFF; lia) NLE KN) as (c & BC & EC).
  rewrite EB in EC. injection EC as EC.
  pose proof (blk_rng _ _ _ _ _ _ M1 S11) as PR.
  pose proof (rbl_apart _ _ _ _ _ _ M1 S11 ltac:(reflexivity)) as PA.
  pose proof S7 as S7r. rewrite SEGS in S7r.
  destruct (dr_cut m1 (HA + 32) (XH + 168) [C8 (Z_to_bv 64 (hs_off h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia)) as [S7a HC].
  assert (BCn : bytes_at rsegs (normalize rsegs m1) (fst r0 + ds_off s + Z.of_nat k) [c])
    by (apply (bytes_at_normalize rsegs m1 _ _ RO1r); rewrite <- SEGS; exact BC).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  rewrite <- L9c in LKs. assert (KF : ls_k (hs_state h1) = false) by exact LKs.
  unfold hs_state in LKs. cbn [ls_k] in LKs. apply Z.eqb_neq in LKs.
  assert (OV0 : hs_overlong h1 = 0) by (clear - S10 LKs; lia).
  rewrite OV0 in HC.
  assert (HCn : rw_cells rsegs (normalize rsegs m1) (XH + 168)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 0)])
    by (apply rbl_norm_hi; [exact RO1r | exact HC | clear - F11; unfold DR_TU in *; lia]).
  assert (C0 : bv_unsigned c = 0) by (unfold bz in EC; clear - EC B0; lia).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20, G21, G23, G24, G26, G27. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply UJ_rbl_zero_push; [exact BCn | exact HCn | apply mem_inv_normalize | clear - S9; lia | clear - PR; lia |
                             clear - PR S9 F4; lia | | clear - OFF T4; lia | clear - OFF NLE KN T4 T5 F4; lia |
                             clear - T4 T5 F4; lia | exact C0].
    clear - PA S9 F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
  intros ms (can & (s0' & -> & REL & ROS) & EQ).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 (normalize rsegs m1) m2 [] RO1r REL2 ROS (munch_refl _ _) (wmono_refl _ _)) as (MU2 & WM2 & RO2).
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS12.
  assert (RO2s : ro_agree segs m2) by (rewrite SEGS; exact RO2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x13ae8) by rgw X2.
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (S0 - 144)) by rgw X2.
  assert (E2_4 : getr R2 4 = getr regs 4) by rgw X2.
  assert (E2_9 : getr R2 9 = Z_to_bv 64 (dnum s - Z.of_nat k)) by rgw X2.
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (XH + 192)) by rgw X2.
  assert (E2_11 : getr R2 11 = Z_to_bv 64 (hs_partial h1)) by rgw X2.
  assert (E2_12 : getr R2 12 = Z_to_bv 64 (hs_npartial h1)) by rgw X2.
  assert (E2_18 : getr R2 18 = Z_to_bv 64 (XH + 192)) by rgw X2.
  assert (E2_19 : getr R2 19 = Z_to_bv 64 (dnum s)) by rgw X2.
  assert (E2_20 : getr R2 20 = Z_to_bv 64 XH) by rgw X2.
  assert (E2_21 : getr R2 21 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k)) by rgw X2.
  assert (E2_23 : getr R2 23 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k)) by rgw X2.
  assert (E2_24 : getr R2 24 = Z_to_bv 64 1) by rgw X2.
  assert (E2_26 : getr R2 26 = Z_to_bv 64 (fst r0)) by rgw X2.
  assert (E2_27 : getr R2 27 = Z_to_bv 64 (fst r0 + ds_off s)) by rgw X2.
  assert (RT2 : RT R2) by (unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  clear X2.
  assert (U2 : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite E2_2. apply unsigned_lit. clear - F1 F2 F3. lia. }
  assert (U10 : bv_unsigned (getr R2 10) = HA + 64).
  { rewrite E2_10, unsigned_lit by (clear - F11; unfold DR_TU in *; lia). clear - F11. unfold DR_TU, G_S, SRC_SIZE in *.
    lia. }
  assert (U11 : bv_unsigned (getr R2 11) = hs_partial h1) by (rewrite E2_11; apply unsigned_lit; clear - PR F4; lia).
  assert (U12 : bv_unsigned (getr R2 12) = hs_npartial h1) by (rewrite E2_12; apply unsigned_lit; clear - S9; lia).
  assert (RP2 : relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m2 md1).
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU2); [exact WM2s | exact GEI |].
    intros a _. left. exact I. }
  pose proof RP2 as (M2 & _).
  destruct (rbl_model s D k b H2h EB) as (MF & ML & ML0). rewrite <- L9c, B0 in MF, ML, ML0.
  rewrite step_zero, KF in MF, ML, ML0. cbn [fst snd] in MF, ML, ML0.
  change (ls_w (hs_state h1)) with (bzs (hs_W h1)) in ML, ML0.
  destruct TR1 as (tp & qd & ad & RC1 & TE1 & TF1 & TA1).
  set (ls := lines (ds_ref s) (firstn k (ddata s))) in *.
  destruct (pushes_run (ds_en s) (ds_ecap s) ls (nretF tp) (da_ev ad) (da_erecs ad)) as [[t1 c1] [v1 rs1]] eqn:EP1.
  pose proof (pushes_run_m (ds_en s) (ds_ecap s) ls (nretF tp) (da_ev ad) (da_erecs ad)) as PM1.
  rewrite EP1 in PM1. cbn [fst snd] in PM1, RC1.
  destruct RC1 as (LQ1 & WT1 & AO1 & RS1 & (LKo & LKe & LKs1) & DK1).
  pose proof AO1 as (AOo & AOb & AOh & AOk & AOp & AOv & AOr).
  cbn [apush da_out da_buf da_hp da_keys da_pend da_ev da_erecs fst snd] in AOo, AOb, AOh, AOk, AOp, AOv, AOr.
  rewrite <- LQ1 in AOo, AOb, AOh, AOk, AOp, AOv, AOr.
  assert (PEn : ds_pend s <> []) by (rewrite <- L7c, HR; discriminate).
  assert (STR : dstrict s).
  { intros r rs Er. rewrite <- L7c, HR in Er. cbn [map] in Er. injection Er as <- _.
    unfold bzs. rewrite length_map. clear - OFF. lia. }
  assert (DR : dref s = (ls ++ [bzs (hs_W h1)]) ++
                 lines (feed (ds_ref s) (firstn (S k) (ddata s))) (skipn (S k) (ddata s))).
  { unfold dref. transitivity (lines (ds_ref s) (firstn (S k) (ddata s) ++ skipn (S k) (ddata s)));
      [rewrite firstn_skipn; reflexivity|]. rewrite lines_app, ML. reflexivity. }
  assert (LW : Z.of_nat (length (hs_W h1)) = hs_npartial h1)
    by (unfold hs_W; rewrite length_firstn; clear - S9 S13; lia).
  pose proof TE1 as TE2. unfold dneed in TE2. rewrite drun_data in TE2 by assumption.
  unfold dpush in TE2. rewrite DR, rbl_pushes_app, (rbl_pushes_app ls [bzs (hs_W h1)]), EP1 in TE2.
  cbn [fst snd pushes_run] in TE2. rewrite <- !app_assoc in TE2. rewrite app_assoc in TE2.
  pose proof ROOM as RM. rewrite <- TE2 in RM.
  set (p0 := sptr_of L1 A1 (hl_v (hs_expected h1))).
  assert (TQ : list_push_tr (sh_of (known_at L1 A1) (hs_expected h1)) (bzs (hs_W h1)) =
               list_push_tra (Known p0) (ds_en s + Z.of_nat (length ls)) c1 (Z.of_nat (length (bzs (hs_W h1))))).
  { rewrite list_push_tr_tra. unfold sh_of, sh_n. cbn [sh_v sh_cap sh_recs]. rewrite length_map.
    change (Z.of_nat (length (hl_recs (hs_expected h1)))) with (hl_n (hs_expected h1)). rewrite L10c, L11c, <- PM1.
    reflexivity. }
  pose proof S16 as (X16a & X16b & X16c & X16d & X16e & X16f).
  pose proof (NODUP _ _ _ _ M1) as ND1.
  assert (CP1 : hl_cap (hs_expected h1) = c1) by (rewrite L11c, <- PM1; reflexivity).
  assert (Hv0 : c1 <> 0 -> resolveF qd v1 = p0).
  { intros Cn. pose proof LKs1 as (_ & _ & _ & (EV1 & _) & _). cbn [apush da_ev fst snd] in EV1.
    assert (Cp : 0 < hl_cap (hs_expected h1)) by (rewrite CP1 in X16b |- *; unfold hl_n in X16b; clear - X16b Cn; lia).
    specialize (EV1 Cp). symmetry. exact (p3a_live_known _ _ _ _ _ ND1 EV1). }
  assert (Hv : ds_en s + Z.of_nat (length ls) = c1 -> c1 <> 0 -> resolveF qd v1 = p0) by (intros _; exact Hv0).
  assert (RMc : forall qs, length qs = nretF (list_push_tra (Known p0) (ds_en s + Z.of_nat (length ls)) c1
                                              (Z.of_nat (length (bzs (hs_W h1))))) ->
                roomF F qs (runF F qd bnd (tp ++ t1))
                  (list_push_tra (Known p0) (ds_en s + Z.of_nat (length ls)) c1 (Z.of_nat (length (bzs (hs_W h1)))))).
  { exact (rbl_lp_room bnd (tp ++ t1) _ qd v1 p0 _ _ _ WT1 LQ1 AOv Hv RM). }
  assert (PSL : dnum s <= Z.of_nat (length (pstream s))).
  { unfold pstream, prest. rewrite <- L7c, HR. cbn [map].
    assert (LL0 : length (bzs (snd r0)) = length (snd r0)) by (unfold bzs; apply length_map).
    rewrite length_app, length_skipn, LL0. clear - NLE OFF. lia. }
  assert (L1L : (length ls <= k)%nat).
  { etransitivity; [apply rbl_lines_le|]. rewrite length_firstn. apply Nat.le_min_l. }
  pose proof S18 as NDH. apply NoDup_ListNoDup in NDH. unfold hs_blocks in NDH.
  assert (PNX : ~ In (hs_partial h1) (list_blocks (hs_expected h1))).
  { apply (rbl_nd_out (list_blocks (hs_pending h1) ++ [hs_partial h1]) _ (list_blocks (hs_held h1)));
      [rewrite <- app_assoc; exact NDH | apply in_or_app; left; apply in_or_app; right; left; reflexivity]. }
  assert (VB : 0 < hl_cap (hs_expected h1) ->
               In (hl_v (hs_expected h1), 16 * hl_cap (hs_expected h1)) (blocks L1 A1) /\
               In (hl_v (hs_expected h1)) (list_blocks (hs_expected h1))).
  { intros Cp. destruct X16c as [(C0' & _)|(_ & VI & _)]; [clear - Cp C0'; lia|]. split; [exact VI|].
    unfold list_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - Cp; lia). left. reflexivity. }
  assert (PNV : hs_partial h1 <> hl_v (hs_expected h1)).
  { intros X. destruct X16c as [(_ & V0)|(Cp & _)].
    - rewrite V0 in X. clear - X PR. lia.
    - apply PNX. rewrite X. exact (proj2 (VB Cp)). }
  assert (WB : bytes_at segs m2 (hs_partial h1) (hs_W h1)).
  { pose proof S14 as [[_ PB] _]. cbn [cells_bytes cbytes] in PB. rewrite app_nil_r in PB.
    rewrite <- (firstn_skipn (Z.to_nat (hs_npartial h1)) (hs_pjunk h1)) in PB. apply bytes_at_app in PB as [PB _].
    eapply by_tr; [exact MS12 | exact PB |]. intros a Ha. split; [|exact I].
    unfold hs_W in Ha. rewrite length_firstn in Ha. clear - Ha PR F4 S13. lia. }
  pose proof (LPC L1 A1 R2 m2 md1 (runF F qd bnd (tp ++ t1)) (hs_expected h1) true (hs_W h1)) as LP.
  cbv zeta in LP. rewrite U10, U11, U12, U2, E2_1 in LP.
  eapply SR_bind.
  { apply LP.
    - exact SEGS.
    - apply (rbl_pre_lp L1 A1 m2 md1 R2 RP2 IN1 E2_2 E2_4). rewrite E2_1. exact rbl_ret.
    - exact IN1.
    - exact RO2s.
    - intros a Ha. split.
      + apply GRP. clear - Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
      + rewrite SEGS. apply ro_hi. clear - Ha F11. unfold G_S, SRC_SIZE in *. lia.
    - unfold G_S, SRC_SIZE. clear. Z.div_mod_to_equations. lia.
    - eapply list_at_tr; [exact MS12 | exact S16 | | intros q k' Hq _; exact Hq |].
      + intros a Ha. split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia | exact I].
      + intros q k' a Hq _ Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR. split; [clear - QR Ha F4; lia | exact I].
    - intros _. clear - H6h HEC L10c L1L KN PSL H12h. lia.
    - clear - S9. lia.
    - exact WB.
    - exact LW.
    - right. left. exists (hs_partial h1), 6000. split; [exact S11|]. split; [exact PNV|]. clear - S9. lia.
    - clear - PA S9 F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - intros _. split; [exact S15 | clear - S9; lia].
    - intros X. discriminate X.
    - exact RS1.
    - rewrite TQ. exact RMc. }
  intros c3 (L3 & A3 & regs3 & mem3 & md3 & l' & dq & -> & RP3 & IN3 & (qs & LQ3 & RS3 & SHR3 & SHL3) & RO3 & LX3 & HR3 &
    HC3 & HV3 & KP3 & CL3 & NN3).
  pose proof RP3 as (M3 & _ & _ & _ & _ & _ & _ & _ & _ & RPr3 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M3) as (Hh3 & Hl3 & _).
  assert (RO3r : ro_agree rsegs mem3) by (rewrite <- SEGS; exact RO3).
  pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RP3) as MS23.
  pose proof (msame_trans _ _ _ _ _ MS12 MS23) as MS13.
  match type of MS13 with msame ?P _ _ =>
    assert (I13 : forall a, img_plain Bm a -> ~ (HA + 64 <= a < HA + 80) -> P a) end.
  { intros a Hp Hn. pose proof Hp as (Hi & _ & _ & NEr). pose proof (img_lo a Hi) as IL.
    split; [split; [clear - IL; lia | exact I]|].
    left. split; [right; exact Hi|]. split; [exact (img_unowned _ _ _ _ a M2 Hp)|].
    split; [exact (img_unowned _ _ _ _ a M3 Hp)|]. split.
    - intros [X|X]; [rewrite U2 in X | exact (NEr X)].
      clear - X IL F1 F3. unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in X. lia.
    - intros [X|(X1 & X2)]; [clear - X Hn; lia|].
      destruct (VB ltac:(clear - X1; unfold hl_n in *; lia)) as (VI & _).
      apply (blk_noimg _ _ _ _ _ _ (a - hl_v (hs_expected h1)) M1 VI); [clear - X1 X2; unfold hl_n in *; lia|].
      replace (hl_v (hs_expected h1) + (a - hl_v (hs_expected h1))) with a by ring. exact Hi. }
  match type of MS13 with msame ?P _ _ =>
    assert (B13 : forall q k' a, In (q, k') (blocks L1 A1) -> ~ In q (list_blocks (hs_expected h1)) ->
                    q <= a < q + k' -> P a) end.
  { intros q k' a Hq Hn Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    split; [split; [clear - QR Ha F4; lia | exact I]|].
    right. exists q, k'. split; [exact Hq|]. split; [clear - Ha; lia|].
    split; [intros (_ & Cp & Eq'); apply Hn; rewrite Eq'; exact (proj2 (VB Cp))|]. split; [exact Ha|].
    intros [X|(X1 & X2)].
    - apply (blk_noimg _ _ _ _ _ _ (a - q) M1 Hq); [clear - Ha; lia|]. replace (q + (a - q)) with a by ring.
      exact (proj1 (GRP a ltac:(clear - X F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    - destruct (VB ltac:(clear - X1; unfold hl_n in *; lia)) as (VI & VL).
      assert (QV : q <> hl_v (hs_expected h1)) by (intros Eq'; apply Hn; rewrite Eq'; exact VL).
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq VI QV) as [D'|D'];
        clear - D' Ha X1 X2; unfold hl_n in *; lia. }
  match type of MS13 with msame ?P _ _ => assert (F13 : forall a, S0 - 144 <= a < S0 -> P a) end.
  { intros a Ha. split; [split; [clear - Ha F1 F2 F3; lia | exact I]|]. left.
    split; [left; clear - Ha F1 F2 F3; lia|].
    split; [intros X; pose proof (owned_lo2 _ _ _ _ a M2 X) as Y; clear - Ha F1 Y; lia|].
    split; [intros X; pose proof (owned_lo2 _ _ _ _ a M3 X) as Y; clear - Ha F1 Y; lia|].
    split.
    - intros [X|X]; [rewrite U2 in X; clear - X Ha; lia|].
      pose proof (img_lo a (GEI a X)) as Y. clear - Ha F1 F3 Y. lia.
    - intros [X|(X1 & X2)]; [clear - X Ha F1 F3 F11; unfold G_S, SRC_SIZE in *; lia|].
      destruct (VB ltac:(clear - X1; unfold hl_n in *; lia)) as (VI & _). pose proof (blk_rng _ _ _ _ _ _ M1 VI) as VR.
      clear - X1 X2 VR Ha F1. unfold hl_n in *. lia. }
  destruct (dr_cut m1 (HA + 32) (HA + 48) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; lia)) as [S7b S7c].
  assert (C3 : rw_cells rsegs (normalize rsegs mem3) (XH + 176)
                 [C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]).
  { apply rbl_norm_hi; [exact RO3r | | clear - F11; unfold DR_TU in *; lia].
    replace (XH + 176) with (HA + 48) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
    rewrite <- SEGS. eapply rw_tr; [exact MS13 | rewrite SEGS; exact S7c |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply I13; [apply GRP|]; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
  assert (E3_20 : getr regs3 20 = Z_to_bv 64 XH)
    by (transitivity (getr R2 20); [exact (RPr3 20 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_20]).
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, E3_20. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO3r |].
    eapply dr_lreset; [exact C3 | apply mem_inv_normalize]. }
  intros ms4 (can4 & (s4' & (m' & -> & MU & WM & MI & HC4) & REL5 & ROS5) & EQ5).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL5) as [ECAN5 REL4]. rewrite ECAN5 in EQ5.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R4 & -> & X4).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m4 := ms_mem can4) in *.
  pose proof (sb_back mem3 m' m4 _ RO3r REL4 ROS5 MU WM) as (MU4 & WM4 & RO4).
  pose proof (rw_cells_of_rel rsegs m4 m' _ _ REL4 HC4) as HC4'.
  assert (WM4s : wmono segs mem3 m4) by (rewrite SEGS; exact WM4).
  pose proof (msame_munch _ _ _ MU4 WM4s) as MS34.
  pose proof (msame_trans _ _ _ _ _ MS13 MS34) as MS14.
  match type of MS14 with msame ?P _ _ =>
    assert (I14 : forall a, img_plain Bm a -> ~ (HA + 48 <= a < HA + 80) -> P a) end.
  { intros a Hp Hn. split; [apply I13; [exact Hp | clear - Hn; lia]|]. pose proof (img_lo a (proj1 Hp)) as IL.
    split; [clear - IL; lia|]. cbn [outside].
    split; [clear - Hn F11; unfold DR_TU, G_S, SRC_SIZE in *; lia | exact I]. }
  match type of MS14 with msame ?P _ _ =>
    assert (B14 : forall q k' a, In (q, k') (blocks L1 A1) -> ~ In q (list_blocks (hs_expected h1)) ->
                    q <= a < q + k' -> P a) end.
  { intros q k' a Hq Hn Ha. split; [exact (B13 q k' a Hq Hn Ha)|]. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (rbl_apart _ _ _ _ _ _ M1 Hq ltac:(clear - Ha; lia)) as QA.
    split; [clear - QR Ha F4; lia|]. cbn [outside].
    split; [clear - QA Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia | exact I]. }
  match type of MS14 with msame ?P _ _ => assert (F14 : forall a, S0 - 144 <= a < S0 -> P a) end.
  { intros a Ha. split; [exact (F13 a Ha)|]. split; [clear - Ha F1 F2 F3; lia|]. cbn [outside].
    split; [clear - Ha F1 F3 F11; unfold DR_TU in *; lia | exact I]. }
  assert (RPb : relay_post Bm API DRAIN_K EE FF L A regs mem md L3 A3 regs mem3 md3).
  { eapply (sb_comp Bm API); try first [exact AX | exact CTX | exact EU | exact BW | exact SEGS | exact RP2 | exact RP3].
    - intros a Ha. change (spZ regs) with S0 in Ha.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. clear - Ha F1 F2. lia.
    - intros a [X|X]; [left | right; exact X]. rewrite U2 in X. change (spZ regs) with S0.
      unfold LIST_PUSH_K, LIST_PUSH_FRAME, DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK,
        ALLOC_STACK in *. clear - X. lia.
    - intros a Hs Hn [X|(X1 & X2)].
      + destruct Hs as [Hs|Hs]; [|apply Hn; right; exact Hs].
        change (spZ regs) with S0 in Hs.
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Hs.
        clear - Hs X F1 F3 F11. unfold G_S, SRC_SIZE in *. lia.
      + destruct Hs as [Hs|Hs]; [|apply Hn; right; exact Hs].
        destruct (VB ltac:(clear - X1; unfold hl_n in *; lia)) as (VI & _).
        pose proof (blk_rng _ _ _ _ _ _ M1 VI) as VR. change (spZ regs) with S0 in Hs.
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Hs.
        clear - Hs X1 X2 VR F1. unfold hl_n in *. lia.
    - intros p n Hp Hp1 Hn NF (_ & Cp & Eq').
      assert (INq : In (ptr_addr L p, n) (blocks L A))
        by (apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
      destruct (untouched s L1 A1 m1 e1 h1 OUT1 junk1 LB1 (ptr_addr L p) n BK1 OU1 INq Hn NF) as [_ U'].
      apply U'. rewrite Eq'. apply hb_exp. exact (proj2 (VB Cp)).
    - intros a Ha Ho Hs [X|(X1 & X2)].
      + right; right; left. clear - X F11. unfold G_S, SRC_SIZE in *. lia.
      + exfalso. destruct (VB ltac:(clear - X1; unfold hl_n in *; lia)) as (VI & _).
        pose proof (blk_rng _ _ _ _ _ _ M1 VI) as VR.
        destruct Ha as [Ha|Ha]; [clear - Ha X1 X2 VR; unfold hl_n in *; lia|].
        apply (blk_noimg _ _ _ _ _ _ (a - hl_v (hs_expected h1)) M1 VI); [clear - X1 X2; unfold hl_n in *; lia|].
        replace (hl_v (hs_expected h1) + (a - hl_v (hs_expected h1))) with a by ring. exact Ha.
    - intros p n i Hp Hp1 NF Hi [X|(X1 & X2)]; exfalso.
      + assert (INq : In (ptr_addr L p, n) (blocks L A))
          by (apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
        pose proof pre_facts as (HM0 & _).
        apply (blk_noimg _ _ _ _ _ _ i HM0 INq Hi).
        exact (proj1 (GRP (ptr_addr L p + i)
                        ltac:(clear - X F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
      + assert (INq : In (ptr_addr L p, n) (blocks L A))
          by (apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
        destruct (untouched s L1 A1 m1 e1 h1 OUT1 junk1 LB1 (ptr_addr L p) n BK1 OU1 INq ltac:(clear - Hi; lia) NF)
          as [_ U'].
        pose proof RP2 as (_ & _ & _ & _ & _ & AD2 & _).
        pose proof (AD2 p n Hp Hp1 NF) as EA.
        assert (INq1 : In (ptr_addr L p, n) (blocks L1 A1))
          by (apply CF.gestures_end_b.blocks_In2; exists p; split; [exact EA | exact Hp1]).
        destruct (VB ltac:(clear - X1; unfold hl_n in *; lia)) as (VI & VL).
        assert (QV : ptr_addr L p <> hl_v (hs_expected h1))
          by (intros Eq'; apply U'; rewrite Eq'; apply hb_exp; exact VL).
        destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 INq1 VI QV) as [D'|D'];
          clear - D' Hi X1 X2; unfold hl_n in *; lia. }
  assert (RPc : relay_post Bm API DRAIN_K EE FF L A regs mem md L3 A3 regs m4 md3).
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPb MU4); [exact WM4s | exact GEI |].
    intros a Ha. destruct (rbl_rng a (XH + 176) (XH + 188)) as [D1|D1].
    - right; right; left.
      split; [apply GRP; clear - D1 F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia|].
      right; right; left. clear - D1 F11. unfold G_S, SRC_SIZE, DR_TU in *. lia.
    - left. cbn [outside]. split; [exact D1 | exact I]. }
  pose proof RPc as (M4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC4).
  assert (ERC4 : exists ev, rw_cells segs m4 ERR [C4 ev]).
  { pose proof (img_lo ERR (GEI ERR ltac:(clear - F10; lia))) as EL.
    rewrite SEGS. apply sb_c4; [clear - EL; lia | clear - F10; lia |].
    intros i Hi. rewrite <- SEGS. apply SC4. right. clear - Hi. lia. }
  assert (C4' : rw_cells segs m4 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1));
                                            C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
  { assert (Xa : rw_cells rsegs m4 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1))]).
    { rewrite <- SEGS. eapply rw_tr; [exact MS14 | rewrite SEGS; exact S7b |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply I14; [apply GRP|]; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
    rewrite SEGS. apply (dr_join m4 (HA + 32) (XH + 176) _ _ Xa HC4'). cbn [cells_size csize].
    clear - F11. unfold DR_TU, G_S, SRC_SIZE in *. lia. }
  assert (P4 : rw_cells segs m4 (hs_partial h1) [CB (Z.to_nat 6000) (hs_pjunk h1)]).
  { eapply rw_tr; [exact MS14 | exact S14 |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply (B14 (hs_partial h1) 6000 a S11 PNX). clear - Ha. lia. }
  assert (W32' : rw_cells segs m4 (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))]).
  { eapply rw_tr; [exact MS14 | exact W32 |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply F14. clear - Ha. lia. }
  assert (LX4 : list_at Bm L3 A3 m4 (HA + 64) l' true).
  { eapply list_at_tr; [exact MS34 | exact LX3 | | intros q k' Hq _; exact Hq |].
    - intros a Ha. split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia|]. cbn [outside].
      split; [clear - Ha F11; unfold DR_TU, G_S, SRC_SIZE in *; lia | exact I].
    - intros q k' a Hq _ Ha. pose proof (blk_rng _ _ _ _ _ _ M3 Hq) as QR.
      pose proof (rbl_apart _ _ _ _ _ _ M3 Hq ltac:(clear - Ha; lia)) as QA.
      split; [clear - QR Ha F4; lia|]. cbn [outside].
      split; [clear - QA Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia | exact I]. }
  assert (NDX : NoDup (list_blocks (hs_pending h1) ++ [hs_partial h1] ++ list_blocks l' ++ list_blocks (hs_held h1))).
  { apply NoDup_ListNoDup. pose proof NDH as NDH'. rewrite app_assoc in NDH'. rewrite app_assoc.
    apply (rbl_nd_swap _ (list_blocks (hs_expected h1)) _ _ NDH' (rbl_lb_nd _ _ _ _ _ _ LX3)).
    intros y Hy Hx. pose proof (rbl_nd_out _ _ _ y NDH' Hy) as NE.
    assert (Hy' : In y (hs_blocks h1))
      by (unfold hs_blocks; rewrite !in_app_iff in Hy; rewrite !in_app_iff; clear - Hy; tauto).
    destruct (rbl_hb_pos _ _ _ _ _ y SR1 Hy') as (ky & Hy1 & Hy2).
    exact (NN3 y ky Hy1 Hy2 NE Hx). }
  destruct (rbl_bundle s L1 A1 m1 L3 A3 m4 e1 h1 OUT1 junk1 LB1 D _ (hs_pjunk h1) 0 0 l' MS14
              (fun a Hp Hn => I14 a Hp ltac:(clear - Hn; lia)) (fun q k' a Hq _ Hn Ha => B14 q k' a Hq Hn Ha) F14 KP3
              FR1 SAC1 EK1 SR1 OT1 H7h H8h BK1 GL1 OU1 ERC4 C4' ltac:(clear - F11; lia) (or_introl eq_refl) S13 P4
              ltac:(intros []) LX4 NDX)
    as (FR4 & SAC4 & EK4 & SR4 & OT4 & GL4 & OU4).
  assert (OB1 : OUT1 = 0 \/ exists k', In (OUT1, k') (blocks L1 A1) /\ 0 < k').
  { destruct OU1 as (OFa & OTa).
    assert (LVd : LIVE = true \/ LIVE = false) by (destruct LIVE; [left | right]; reflexivity).
    destruct LVd as [LV|LV].
    - destruct (OTa LV) as (_ & [(_ & O0 & _)|(Pp & _ & OI & _)]);
        [left; exact O0 | right; exists (ds_ocap s); split; [exact OI | exact Pp]].
    - destruct (OFa LV) as (_ & OE & _ & OB). destruct OUTD as [(C0' & O0 & _)|(Cp & _)].
      + left. rewrite OE. exact O0.
      + right. exists CAP. rewrite OE. split; [exact (proj1 (OB Cp)) | exact Cp]. }
  pose proof (rbl_dblk L1 A1 m1 md1 L3 A3 m4 md3 e1 h1 OUT1 (hs_pjunk h1) 0 0 l' M1 M4 BK1 EK1 SR1 OB1 LX4 RPc KP3 CL3
                NN3) as BK4.
  pose proof (rbl_rt R2 regs3 RT2 RPr3) as (H2' & H3' & H4' & H8' & H22' & H25').
  assert (Q9 : getr regs3 9 = Z_to_bv 64 (dnum s - Z.of_nat k))
    by (transitivity (getr R2 9); [exact (RPr3 9 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_9]).
  assert (Q18 : getr regs3 18 = Z_to_bv 64 (XH + 192))
    by (transitivity (getr R2 18); [exact (RPr3 18 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_18]).
  assert (Q19 : getr regs3 19 = Z_to_bv 64 (dnum s))
    by (transitivity (getr R2 19); [exact (RPr3 19 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_19]).
  assert (Q21 : getr regs3 21 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k))
    by (transitivity (getr R2 21); [exact (RPr3 21 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_21]).
  assert (Q23 : getr regs3 23 = Z_to_bv 64 (fst r0 + ds_off s + Z.of_nat k))
    by (transitivity (getr R2 23); [exact (RPr3 23 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_23]).
  assert (Q24 : getr regs3 24 = Z_to_bv 64 1)
    by (transitivity (getr R2 24); [exact (RPr3 24 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_24]).
  assert (Q26 : getr regs3 26 = Z_to_bv 64 (fst r0))
    by (transitivity (getr R2 26); [exact (RPr3 26 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_26]).
  assert (Q27 : getr regs3 27 = Z_to_bv 64 (fst r0 + ds_off s))
    by (transitivity (getr R2 27); [exact (RPr3 27 ltac:(unfold callee_saved; clear - F11; lia)) | exact E2_27]).
  pose proof RP2 as (_ & W1 & _).
  assert (KEEP : forall p x n, live_at L1 A1 p x n -> (0 < hl_cap (hs_expected h1) -> x <> hl_v (hs_expected h1)) ->
                 live_at L3 A3 p x n).
  { intros p x n Hlv Hxv. apply (rbl_live_rp _ _ _ L1 A1 R2 m2 md1 L3 A3 regs3 mem3 md3 p x n W1 RP3 Hlv).
    intros (_ & Cp & Ev). exact (Hxv Cp Ev). }
  assert (XO : forall q, In q (OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ hs_partial h1 ::
                               list_blocks (hs_held h1)) ->
               0 < hl_cap (hs_expected h1) -> q <> hl_v (hs_expected h1)).
  { intros q Hq Cp Eq. pose proof BK1 as (NDb & _). apply NoDup_ListNoDup in NDb. unfold hs_blocks in NDb.
    assert (ND2 : List.NoDup ((G :: OUT1 :: entry_blocks e1 ++ list_blocks (hs_pending h1) ++ [hs_partial h1]) ++
                              list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)))
      by (cbn [app]; rewrite <- !app_assoc; exact NDb).
    apply (rbl_nd_out _ _ _ q ND2); [| rewrite Eq; exact (proj2 (VB Cp))].
    cbn [app]. right. destruct Hq as [<-|Hq]; [left; reflexivity | right]. rewrite <- !app_assoc. cbn [app]. exact Hq. }
  assert (XE : forall q, In q (entry_blocks e1) -> 0 < hl_cap (hs_expected h1) -> q <> hl_v (hs_expected h1)).
  { intros q Hq. apply XO. right. apply in_or_app. left. exact Hq. }
  assert (XP : forall q, In q (list_blocks (hs_pending h1)) -> 0 < hl_cap (hs_expected h1) ->
               q <> hl_v (hs_expected h1)).
  { intros q Hq. apply XO. right. apply in_or_app. right. apply in_or_app. left. exact Hq. }
  assert (XHL : forall q, In q (list_blocks (hs_held h1)) -> 0 < hl_cap (hs_expected h1) -> q <> hl_v (hs_expected h1)).
  { intros q Hq. apply XO. right. apply in_or_app. right. apply in_or_app. right. right. exact Hq. }
  rewrite TQ in LQ3, RS3.
  destruct (rbl_lp_shift (runF F qd bnd (tp ++ t1)) qd qs [] v1 p0 (ds_en s + Z.of_nat (length ls)) c1
              (Z.of_nat (length (bzs (hs_W h1)))) Hv AOv LQ3) as (N0 & Rn & _).
  rewrite app_nil_r in Rn.
  assert (RUN : runF F (qd ++ qs) bnd ((tp ++ t1) ++ list_push_tra v1 (ds_en s + Z.of_nat (length ls)) c1
                                                    (Z.of_nat (length (bzs (hs_W h1))))) =
                runF F qs (runF F qd bnd (tp ++ t1))
                  (list_push_tra (Known p0) (ds_en s + Z.of_nat (length ls)) c1 (Z.of_nat (length (bzs (hs_W h1)))))).
  { unfold runF at 1. unfold run_tr. rewrite run_from_app.
    rewrite (p3a_run_app _ _ _ _ qd qs bnd 0 (tp ++ t1)) by (exact WT1 || (clear - LQ1; lia)).
    rewrite Nat.add_0_l, <- LQ1. exact Rn. }
  assert (NT : (nretF tp + nretF t1)%nat = length qd) by (rewrite LQ1, nret_app; reflexivity).
  set (h3 := HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
               (hs_pjunk h1) 0 0 (hs_pad h1) l' (hs_held h1)).
  assert (TRn : DPU L3 A3 s e1 h3 OUT1 (lines (ds_ref s) (firstn (S k) (ddata s)))).
  { exists tp, (qd ++ qs), ad. split; [|split; [exact TE1 | split; [exact TF1 | exact TA1]]].
    rewrite ML, rbl_pushes_app, EP1. cbn [fst snd pushes_run]. rewrite app_nil_r, app_assoc, NT, rbl_lp_nret.
    unfold RCORE. split; [|split; [|split; [|split; [|split]]]].
    - rewrite length_app, nret_app, LQ1, LQ3, N0. reflexivity.
    - apply p3a_wf_app. split; [exact WT1|]. apply rbl_lp_wf. rewrite Nat.add_0_l, <- LQ1. exact AOv.
    - rewrite nret_app, <- LQ1, rbl_lp_nret. unfold dadr_ok.
      cbn [apush da_out da_buf da_hp da_keys da_pend da_ev da_erecs fst snd].
      assert (JL : (length qd <= length qd + (if (ds_en s + Z.of_nat (length ls) =? c1)%Z then 2 else 1))%nat)
        by (clear; destruct (_ =? _); lia).
      split; [exact (p3a_ok_mono _ _ _ AOo JL)|]. split; [exact (p3a_ok_mono _ _ _ AOb JL)|].
      split; [exact (p3a_ok_mono _ _ _ AOh JL)|].
      split; [eapply Forall_impl; [|exact AOk]; intros x Hx; exact (p3a_ok_mono _ _ _ Hx JL)|].
      split; [eapply Forall_impl; [|exact AOp]; intros x Hx; exact (p3a_ok_mono _ _ _ Hx JL)|].
      split.
      + destruct (ds_en s + Z.of_nat (length ls) =? c1); [cbn; clear; lia | apply (p3a_ok_mono _ _ _ AOv); clear; lia].
      + apply Forall_app. split; [eapply Forall_impl; [|exact AOr]; intros x Hx; exact (p3a_ok_mono _ _ _ Hx JL)|].
        constructor; [|constructor]. clear. destruct (_ =? _); cbn; lia.
    - rewrite RUN. exact RS3.
    - unfold DLNK, entry_links, src_links, expected_links, h3.
      unfold entry_links, src_links, expected_links in LKe, LKs1.
      cbn [apush da_out da_buf da_hp da_keys da_pend da_ev da_erecs fst snd hs_pending hs_partial hs_expected
           hs_held].
      cbn [apush da_out da_buf da_hp da_keys da_pend da_ev da_erecs fst snd] in LKo, LKe, LKs1.
      split; [|split].
      + intros LV Hoc. rewrite (p3a_resolve_app qd qs _ AOo). apply KEEP; [exact (LKo LV Hoc)|].
        apply XO. left. reflexivity.
      + destruct LKe as (LKb & LKh & LKk). split; [|split].
        * intros Hc. rewrite (p3a_resolve_app qd qs _ AOb). apply KEEP; [exact (LKb Hc)|]. apply XE.
          unfold entry_blocks. apply in_or_app. left.
          destruct (Z.eqb_spec (re_cap e1) 0) as [E0|E0]; [clear - Hc E0; lia | left; reflexivity].
        * intros Hc. rewrite (p3a_resolve_app qd qs _ AOh). apply KEEP; [exact (LKh Hc)|]. apply XE.
          unfold entry_blocks. apply in_or_app. right. apply in_or_app. left.
          destruct (Z.eqb_spec (re_hp e1) 0) as [E0|E0]; [contradiction | left; reflexivity].
        * refine (rbl_f2_keep (live_at L1 A1) (live_at L3 A3) _ qd qs key_addr
                    (fun k0 => Z.of_nat (length (key_text k0)) + 1) _ _ KEEP LKk AOk _).
          intros k0 Hk. apply XE. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right.
          apply in_map. exact Hk.
      + destruct LKs1 as (SPa & SPt & SPp & (SEv & SEr) & SHa & SHt).
        split; [|split; [|split; [|split; [|split]]]].
        * intros Hc. apply KEEP; [exact (SPa Hc)|]. apply XP. unfold list_blocks. apply in_or_app. left.
          destruct (Z.eqb_spec (hl_cap (hs_pending h1)) 0) as [E0|E0]; [clear - Hc E0; lia | left; reflexivity].
        * refine (rbl_f2_keep (live_at L1 A1) (live_at L3 A3) _ qd qs fst
                    (fun r => Z.of_nat (length (snd r)) + 1) _ _ KEEP SPt AOp _).
          intros r Hr. apply XP. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr.
        * apply KEEP; [exact SPp|]. apply XO. right. apply in_or_app. right. apply in_or_app. right. left.
          reflexivity.
        * rewrite HR3.
          pose proof LX3 as (_ & _ & LXc & _ & _ & LXf). rewrite HR3 in LXf. apply Forall_app in LXf as [_ LXf].
          apply Forall_inv in LXf. destruct LXf as (LXd & _).
          unfold list_push_sh, sh_of, sh_n in SHR3, SHL3. cbn [sh_v sh_cap sh_recs] in SHR3, SHL3.
          rewrite length_map in SHR3, SHL3.
          change (Z.of_nat (length (hl_recs (hs_expected h1)))) with (hl_n (hs_expected h1)) in SHR3, SHL3.
          rewrite L10c, CP1 in SHR3, SHL3.
          assert (OLD : Forall2 (fun r x => live_at L3 A3 (resolveF (qd ++ qs) x) (fst r) (Z.of_nat (length (snd r)) + 1))
                          (hl_recs (hs_expected h1)) rs1).
          { refine (rbl_f2_keep (live_at L1 A1) (live_at L3 A3) _ qd qs fst
                      (fun r => Z.of_nat (length (snd r)) + 1) _ _ KEEP SEr AOr _).
            intros r Hr _ Ev. apply X16e. rewrite <- Ev. apply in_map. exact Hr. }
          destruct (ds_en s + Z.of_nat (length ls) =? c1) eqn:EQb; cbv beta iota; try rewrite EQb in SHR3;
            try rewrite EQb in SHL3;
            destruct SHR3 as (SRc & SRv & _ & SRa); destruct SHL3 as (SLv & SLr);
            cbn [sh_v sh_cap sh_recs] in SRc, SRv, SRa, SLv, SLr; rewrite HR3, !map_app in SRa; cbn [map fst] in SRa;
            apply app_inj_tail in SRa as [_ SRd].
          -- split.
             ++ intros Cp'.
                assert (RQ : resolveF (qd ++ qs) (Ret (length qd)) = resolveF qs (Ret 0))
                  by (cbn [resolve]; rewrite app_nth2 by (clear; lia); f_equal; clear; lia).
                rewrite RQ.
                assert (GC : ListRep.grow_cap (ds_en s + Z.of_nat (length ls)) c1 <> 0)
                  by (rewrite <- SRc; clear - Cp'; lia).
                destruct (SLv GC) as (n0 & Hn0).
                destruct LXc as [(Cz & _)|(_ & LXv & _)]; [clear - Cz Cp'; lia|].
                apply (rbl_live_of L3 A3 _ n0 _ _ (NODUP _ _ _ _ M3) Hn0); [symmetry; exact (SRv GC) | exact LXv].
             ++ apply Forall2_app; [exact OLD|]. constructor; [|constructor]. cbn [fst snd].
                assert (RQ : resolveF (qd ++ qs) (Ret (Nat.pred (length qd + 2))) = resolveF qs (Ret 1))
                  by (cbn [resolve]; rewrite app_nth2 by (clear; lia); f_equal; clear; lia).
                rewrite RQ.
                destruct (SLr (Ret 1, bzs (hs_W h1)) ltac:(apply in_or_app; right; left; reflexivity)) as (n1 & Hn1).
                apply (rbl_live_of L3 A3 _ n1 _ _ (NODUP _ _ _ _ M3) Hn1); [symmetry; exact SRd | exact LXd].
          -- split.
             ++ intros Cp'. rewrite (p3a_resolve_app qd qs v1 AOv).
                assert (C1n : c1 <> 0) by (rewrite <- SRc; clear - Cp'; lia).
                rewrite (Hv0 C1n).
                change p0 with (resolveF qs (known_at L1 A1 (hl_v (hs_expected h1)))).
                destruct (SLv C1n) as (n0 & Hn0).
                destruct LXc as [(Cz & _)|(_ & LXv & _)]; [clear - Cz Cp'; lia|].
                apply (rbl_live_of L3 A3 _ n0 _ _ (NODUP _ _ _ _ M3) Hn0); [symmetry; exact (SRv C1n) | exact LXv].
             ++ apply Forall2_app; [exact OLD|]. constructor; [|constructor]. cbn [fst snd].
                assert (RQ : resolveF (qd ++ qs) (Ret (Nat.pred (length qd + 1))) = resolveF qs (Ret 0))
                  by (cbn [resolve]; rewrite app_nth2 by (clear; lia); f_equal; clear; lia).
                rewrite RQ.
                destruct (SLr (Ret 0, bzs (hs_W h1)) ltac:(apply in_or_app; right; left; reflexivity)) as (n1 & Hn1).
                apply (rbl_live_of L3 A3 _ n1 _ _ (NODUP _ _ _ _ M3) Hn1); [symmetry; exact SRd | exact LXd].
        * intros Hc. apply KEEP; [exact (SHa Hc)|]. apply XHL. unfold list_blocks. apply in_or_app. left.
          destruct (Z.eqb_spec (hl_cap (hs_held h1)) 0) as [E0|E0]; [clear - Hc E0; lia | left; reflexivity].
        * rewrite Forall_forall in SHt |- *. intros r Hr. apply KEEP; [exact (SHt r Hr)|]. apply XHL.
          unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr.
    - exact DK1. }
  pose proof (f_equal (@length _) H4h) as H4l. rewrite length_app, !length_map in H4l.
  assert (NL' : hl_n l' = hl_n (hs_expected h1) + 1)
    by (unfold hl_n; rewrite HR3, length_app, Nat2Z.inj_add; reflexivity).
  apply (UB_rbl_fin s k R4 L3 A3 m4 md3 e1 (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1)
           (hs_off h1) (hs_partial h1) (hs_pjunk h1) 0 0 (hs_pad h1) l' (hs_held h1)) OUT1 junk1 LB1 D r0 rs0).
  - unfold RT. repeat match goal with |- _ /\ _ => split end; rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - rgw X4.
  - exact W32'.
  - exact HR.
  - exact KN.
  - exact GR.
  - exact Ee.
  - exact JK.
  - exact RPc.
  - exact IN3.
  - exact TRn.
  - rewrite SEGS. exact RO4.
  - exact FR4.
  - exact SAC4.
  - exact EK4.
  - exact SR4.
  - exact OT4.
  - exact SM1.
  - cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
         hs_expected hs_held].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + rewrite MF. reflexivity.
    + rewrite NL', L10c, ML, length_app. cbn [length]. rewrite Nat2Z.inj_add. clear - F11. lia.
    + rewrite HC3, ML. unfold pcapm. rewrite rbl_pushes_app. cbn [fst snd pushes_run]. rewrite pushes_run_m.
      rewrite <- PM1, <- L10c, <- CP1. unfold ListRep.grow_cap, push_cap.
      repeat match goal with |- context [?x =? ?y] => destruct (x =? y) end; ring.
  - cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
         hs_expected hs_held].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + rewrite HR3, map_app, H4h, ML0, !map_app, <- app_assoc. cbn [map snd]. rewrite rbl_bzs_inv. reflexivity.
    + rewrite HR3, firstn_app.
      replace (length (hl_recs (hs_expected h)) - length (hl_recs (hs_expected h1)))%nat with 0%nat
        by (clear - H4l; lia).
      rewrite firstn_O, app_nil_r. exact H5h.
    + rewrite HC3, NL'. unfold ListRep.grow_cap.
      destruct (Z.eqb_spec (hl_n (hs_expected h1)) (hl_cap (hs_expected h1))) as [EN|EN];
        [destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0) as [EC0|EC0]|]; clear - H6h EN; lia.
  - exact BK4.
  - exact GL4.
  - exact OU4.
Qed.

Lemma byte_step : forall s k c, DRB s k c ->
  SR segs c (fun c' => DRB s (S k) c' \/ (S k = Z.to_nat (dnum s) /\ DRE s c')).
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE.
  intros s k c H. destruct (rbl_k s k c H) as (KN & WF1).
  destruct (nth_error (ddata s) k) as [b|] eqn:EB;
    [|exfalso; apply nth_error_None in EB; rewrite (rbl_ddata_len s WF1) in EB; clear - EB KN; lia].
  destruct (Z.eq_dec b 0) as [B0|B0]; destruct (ls_k (feed (ds_ref s) (firstn k (ddata s)))) eqn:LKs.
  - exact (rbl_reset s k c b H EB B0 LKs).
  - exact (rbl_push s k c b H EB B0 LKs).
  - exact (rbl_skip s k c b H EB B0 LKs).
  - destruct (Nat.eq_dec (length (ls_w (feed (ds_ref s) (firstn k (ddata s))))) LINE_LIMIT) as [LL|LL].
    + exact (rbl_long s k c b H EB B0 LKs LL).
    + exact (rbl_add s k c b H EB B0 LKs LL).
Qed.

Lemma rbl_loop_n : forall t k s c, (Z.to_nat (dnum s) - k <= t)%nat -> DRB s k c -> SR segs c (DRE s).
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE.
  induction t as [|t IH]; intros k s c T H; destruct (rbl_k s k c H) as (KN & _); [exfalso; clear - T KN; lia|].
  eapply SR_bind; [exact (byte_step s k c H)|]. intros c1 [H1|(_ & H1)].
  - apply (IH (S k) s c1); [clear - T; lia | exact H1].
  - apply SR_ret. exact H1.
Qed.

Lemma byte_loop : forall s c, DRB s 0 c -> SR segs c (DRE s).
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE. intros s c H. exact (rbl_loop_n _ 0 s c (le_n _) H). Qed.

Lemma rtk_okx : forall L1 A1 m e1 n, entry_okw L1 A1 m e1 -> 0 < re_cap e1 -> 0 <= n <= re_cap e1 - re_used e1 ->
  entry_okx L1 A1 m (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1 + n) (re_cap e1)
                        (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1) (re_U e1 ++ firstn (Z.to_nat n) (re_junk e1))
                        (skipn (Z.to_nat n) (re_junk e1))).
Proof using.
  intros L1 A1 m e1 n (K1 & K2 & K3 & K4 & K5 & K6 & K7 & _ & _ & K10 & K11 & K12 & K13 & K14 & K15) Cp Hn.
  destruct K10 as [(C0 & _)|(_ & BI & BF & BJ & BC)]; [clear - C0 Cp; lia|].
  unfold entry_okx. cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
  split; [exact K6|].
  split; [rewrite length_app, length_firstn, Nat2Z.inj_add, K7; clear - Hn BJ; lia|].
  split; [clear - Hn; lia|].
  split.
  { right. split; [exact Cp|]. split; [exact BI|]. split; [exact BF|].
    split; [rewrite length_skipn; clear - Hn BJ; lia|].
    rewrite <- app_assoc, firstn_skipn. exact BC. }
  split; [exact K11|]. split; [exact K12|]. split; [exact K13|]. split; [exact K14 | exact K15].
Qed.

Lemma rtk_ps : forall s, dwf s -> 0 <= dnum s -> pstream s = ddata s ++ prest (ds_pend s) (ds_off s + dnum s).
Proof using HG HJ O h junk.
  intros s (W0 & _) N0. unfold pstream, ddata, dhead. destruct (ds_pend s) as [|r rs]; cbn [prest].
  - rewrite skipn_nil, firstn_nil. reflexivity.
  - rewrite app_assoc. f_equal.
    rewrite <- (firstn_skipn (Z.to_nat (dnum s)) (skipn (Z.to_nat (ds_off s)) r)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma rtk_chunk_le : forall u sk d, (length (snd (chunk u sk d)) <= length d)%nat.
Proof using Bm G HJ O h junk regs.
  intros u sk d. unfold chunk. pose proof (scan_lines_le d sk u) as X.
  destruct (scan sk u d) as [[sk' r] ls]. cbn [snd] in X. cbv beta iota zeta.
  destruct (Nat.ltb LINE_LIMIT (length r)); exact X.
Qed.

Lemma rtk_p0 : forall s, drlp s 0 = [] /\ dskp s 0 = ds_skip s /\ dlno s 0 = ds_no s /\ dloc s 0 = ds_ocap s /\
  dlH s 0 = ds_H s /\ dlka s 0 = ds_ka s.
Proof using.
  intros s. split; [reflexivity|]. split; [reflexivity|]. split; [exact (Z.add_0_r (ds_no s))|].
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma rtk_dv : forall s, dwhole s = false ->
  dvirt s (ds_skip s) (ds_H s) (ds_ka s) (ds_no s) (ds_ocap s) =
  DS (ds_cap s) (dW s) (ds_skip s) (ds_H s) (ds_ka s) false (ds_pend s) (ds_off s + dnum s) (feed (ds_ref s) (ddata s))
     (ds_en s + Z.of_nat (length (dref s))) (pcapm (ds_en s) (ds_ecap s) (dref s))
     (ds_no s) (ds_ocap s).
Proof using. intros s W. unfold dvirt, dnext. rewrite W. reflexivity. Qed.

Lemma rtk_src_off : forall L1 A1 m1 m2 h1 off' Pa, msame Pa m1 m2 -> src_at Bm L1 A1 m1 HA h1 ->
  (forall a, (HA <= a < HA + 32 \/ HA + 40 <= a < HA + 96) -> Pa a) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> q <= a < q + k -> Pa a) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 off')] ->
  (exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= off' < Z.of_nat (length (snd r))) ->
  src_at Bm L1 A1 m2 HA (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) off' (hs_partial h1)
                           (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)).
Proof using G HJ O SEGS h junk regs.
  intros L1 A1 m1 m2 h1 off' Pa MS
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) HC HB C8' OF.
  assert (S7r : rw_cells rsegs m1 (HA + 32)
                  [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1));
                   C4 (Z_to_bv 64 (hs_overlong h1))]) by (rewrite <- SEGS; exact S7).
  destruct (dr_cut m1 (HA + 32) (HA + 32 + 8) [C8 (Z_to_bv 64 (hs_off h1))]
              [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]
              S7r eq_refl) as [_ S7b].
  assert (S7c : rw_cells segs m2 (HA + 32 + 8)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]).
  { eapply rw_tr; [exact MS | rewrite SEGS; exact S7b |]. intros a Ha. apply HC. right.
    cbn [cells_size csize] in Ha. clear - Ha. lia. }
  unfold src_at.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_expected
       hs_held].
  split; [eapply rw_tr; [exact MS | exact S1 | intros a Ha; apply HC; left; cbn [cells_size csize] in Ha; clear - Ha; lia]|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split.
  { eapply list_at_tr; [exact MS | exact S6 | intros a Ha; apply HC; left; clear - Ha; lia | intros q k Hq _; exact Hq |].
    intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_pend h1 q Hl) Ha). }
  split.
  { rewrite SEGS in C8', S7c |- *.
    exact (dr_join m2 (HA + 32) (HA + 32 + 8) _ _ C8' S7c eq_refl). }
  split; [right; exact OF|].
  split; [exact S9|]. split; [exact S10|]. split; [exact S11|]. split; [exact S12|]. split; [exact S13|].
  split.
  { eapply rw_tr; [exact MS | exact S14 |]. intros a Ha. apply (HB _ _ a S11 (hb_part h1)).
    cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. clear - Ha. lia. }
  split; [exact S15|].
  split.
  { eapply list_at_tr; [exact MS | exact S16 | intros a Ha; apply HC; right; clear - Ha; lia | intros q k Hq _; exact Hq |].
    intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_exp h1 q Hl) Ha). }
  split.
  { eapply list_at_tr; [exact MS | exact S17 | intros a Ha; apply HC; right; clear - Ha; lia | intros q k Hq _; exact Hq |].
    intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_held h1 q Hl) Ha). }
  exact S18.
Qed.

Lemma rtk_bundle : forall s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D W off' used' U' J',
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] ->
  entry_okw L1 A1 m1 e1 -> src_at Bm L1 A1 m1 HA h1 -> others_at Bm m1 j (re_fd e) fs os ->
  ds_no s = NO + dtot D -> bzs LB1 = with_nul (lines ST0 D) ->
  DBLK L1 A1 e1 h1 OUT1 -> DGLB D m1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  munch W m1 m2 -> wmono segs m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 32 <= a < HA + 40) -> ~ (SA + 24 <= a < SA + 32) -> outside W a) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 off')] ->
  rw_cells segs m2 (SA + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 used')] ->
  (exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= off' < Z.of_nat (length (snd r))) ->
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m2 md1 /\
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m2 SA [CB 56%nat (entry_bytes (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) used'
                                                  (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1) U' J'))] /\
  entry_okw L1 A1 m2 e1 /\
  src_at Bm L1 A1 m2 HA (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) off' (hs_partial h1)
                           (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)) /\
  others_at Bm m2 j (re_fd e) fs os /\
  DGLB D m2 /\
  DOUT s L1 A1 m2 OUT1 junk1 LB1.
Proof using AX BW EHI EU GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D W off' used' U' J' RP1 FR1 SAC1 EK1 SR1 OT1 HNO HLB BK1 GL1 OU1 MU WM
    HW HC2 HB2 OF.
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  pose proof EK1 as (_ & _ & K3 & K4 & _).
  pose proof BK1 as (ND & GI1 & _).
  pose proof (blk_rng _ _ _ _ _ _ M1 GI1) as GR1. unfold SRC_TABLE, SRC_ENTRY in GR1.
  pose proof (rbl_apart _ _ _ _ _ _ M1 GI1 ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as GA.
  unfold SRC_TABLE, SRC_ENTRY in GA.
  pose proof (msame_munch _ _ _ MU WM) as MS.
  apply NoDup_ListNoDup in ND. apply List.NoDup_cons_iff in ND as [NG _].
  assert (SNI : forall a, in_img Bm a -> ~ (SA + 24 <= a < SA + 32)).
  { intros a Ha X. apply (blk_noimg _ _ _ _ _ _ (a - G) M1 GI1); [unfold SRC_TABLE, SRC_ENTRY; clear - X F6 F7; lia|].
    replace (G + (a - G)) with a by ring. exact Ha. }
  assert (HPI0 : forall a, img_plain Bm a -> ~ (HA + 32 <= a < HA + 40) -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a (Ha & _) Hn. pose proof (img_lo a Ha) as IL. split; [clear - IL; lia|].
    apply HW; [clear - IL; lia | exact Hn | exact (SNI a Ha)]. }
  assert (HPB0 : forall q k a, In (q, k) (blocks L1 A1) -> q <> G -> q <= a < q + k -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros q k a Hq Hn Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (rbl_apart _ _ _ _ _ _ M1 Hq ltac:(clear - Ha; lia)) as QA.
    split; [clear - QR Ha F4; lia|]. apply HW; [clear - QR Ha F4; lia | |].
    - clear - QA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq GI1 Hn) as [X|X];
        clear - X Ha F6 F7; unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  assert (HPG : forall a, G <= a < G + 896 -> ~ (SA + 24 <= a < SA + 32) -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ha Hn. split; [clear - Ha GR1 F4; lia|]. apply HW; [clear - Ha GR1 F4; lia | | exact Hn].
    clear - GA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
  assert (HPF : forall a, S0 - 144 <= a < S0 -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ha. split; [clear - Ha F1 F2 F3; lia|].
    apply HW; [clear - Ha F1 F2 F3; lia | clear - Ha F1 F3 F11; unfold G_S, SRC_SIZE in *; lia |
               clear - Ha GR1 F1 F7; lia]. }
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU); [exact WM | exact GEI |].
    intros a Ha. destruct (rbl_rng a (HA + 32) (HA + 40)) as [D1|D1].
    - right; right; left. split; [apply GRP; clear - D1 F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
      right; right; left. clear - D1. unfold SRC_SIZE in *. lia.
    - destruct (rbl_rng a (SA + 24) (SA + 32)) as [D2|D2]; [|left; exact (HW a Ha D1 D2)].
      right; right; right; right. split; [intros X; exact (SNI a X D2)|].
      split; [exists G, SRC_TABLE; split; [exact GI1 | clear - D2 F6 F7; unfold SRC_TABLE, SRC_ENTRY in *; lia]|].
      intros p n i Hp Hp1 NF Hi NE Ea. apply NE. rewrite Ea. right; left. clear - D2. unfold SRC_ENTRY in *. lia. }
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FRc |]. intros a Ha. apply HPF.
    cbn [cells_size csize app dr_saved] in Ha. clear - Ha. lia. }
  split.
  { assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
    destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
    destruct (dr_cut m1 (SA + 16) (SA + 16 + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]
                [C8 (Z_to_bv 64 (re_cap e1))] EC2 eq_refl) as [_ EC2b].
    assert (X1 : rw_cells segs m2 SA [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1));
                                      C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact EC1 |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPG; clear - Ha F6 F7; lia. }
    assert (X2 : rw_cells segs m2 (SA + 16 + 16) [C8 (Z_to_bv 64 (re_cap e1))]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact EC2b |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPG; clear - Ha F6 F7; lia. }
    assert (X3 : rw_cells segs m2 (SA + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1));
                                             CB 4 (re_pad2 e1)]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact EC3 |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPG; clear - Ha F6 F7; lia. }
    rewrite SEGS in X1, X2, X3, HB2 |- *.
    apply ent_join; [exact K3 | exact K4 | exact X1 | | exact X3].
    exact (dr_join m2 (SA + 16) (SA + 16 + 16) _ _ HB2 X2 eq_refl). }
  split.
  { eapply entry_okw_tr; [exact MS | exact EK1 | intros q k Hq _; exact Hq |].
    intros q k a Hq Hb Ha. apply (HPB0 q k a Hq); [|exact Ha]. intros X. apply NG. right. apply in_or_app. left.
    rewrite <- X. exact Hb. }
  split.
  { apply (rtk_src_off L1 A1 m1 m2 h1 off' _ MS SR1); [| | exact HC2 | exact OF].
    - intros a Ha. apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    - intros q k a Hq Hb Ha. apply (HPB0 q k a Hq); [|exact Ha]. intros X. apply NG. right. apply in_or_app. right.
      rewrite <- X. exact Hb. }
  split.
  { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi Hij Ha.
    assert (NE : Z.of_nat i <> Z.of_nat j) by (intros X; apply Hij; apply Nat2Z.inj; exact X).
    apply HPI0; [apply GRP|]; clear - Ha Hi NE F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
  split.
  { destruct GL1 as (GC1 & GC2 & GC3 & GC4 & (ev1 & GC5)).
    split; [eapply rw_tr; [exact MS | exact GC1 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GCP|]; clear - Ha F11; unfold G_CLIENT, G_S, SRC_SIZE in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC2 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC3 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    exists ev1. eapply rw_tr; [exact MS | exact GC5 |]. intros a Ha.
    cbn [cells_size csize] in Ha. pose proof (GEI a ltac:(clear - Ha; lia)) as Hi. pose proof (img_lo a Hi) as IL.
    split; [clear - IL; lia|]. apply HW; [clear - IL; lia | | exact (SNI a Hi)].
    intros X. pose proof (GRP a ltac:(clear - X F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))
      as (_ & _ & _ & NE).
    apply NE. clear - Ha. lia. }
  destruct OU1 as (OFa & OTa). split.
  - intros LV. destruct (OFa LV) as (OC & OE & OCP & OB). split.
    + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + split; [exact OE|]. split; [exact OCP|]. intros Cq. destruct (OB Cq) as (OI & OBy).
      split; [exact OI|].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB0 OUT CAP a OI).
      * intros X. apply NG. left. rewrite OE. exact X.
      * destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; [clear - Cq C0; lia|].
        rewrite length_app in Ha. clear - Ha LO LJ. lia.
  - intros LV. destruct (OTa LV) as (OC & OZ). split.
    + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + destruct OZ as [OZ|(Pp & NL & OI & OFr & OBy & LJ)]; [left; exact OZ | right].
      split; [exact Pp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OFr|]. split; [|exact LJ].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB0 OUT1 (ds_ocap s) a OI).
      * intros X. apply NG. left. exact X.
      * assert (LO : Z.of_nat (length O) = NO).
        { destruct OUTD as [(_ & _ & N0 & OE0)|(_ & _ & _ & _ & _ & LO & _)];
            [rewrite OE0; cbn [length]; clear - N0; lia | exact LO]. }
        assert (LLB : Z.of_nat (length LB1) = dtot D).
        { unfold dtot. rewrite <- HLB. unfold bzs. rewrite length_map. reflexivity. }
        rewrite !length_app in Ha. clear - Ha LO LLB HNO LJ. lia.
Qed.

Lemma H2_rtk_seg : forall x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA0 X n pv off tl buf used : Z),
  rw_cells rsegs m (SP + 32) [C8 (Z_to_bv 64 (X + 144))] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv)] -> rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off)] ->
  rw_cells rsegs m (pv + 8) [C8 (Z_to_bv 64 tl)] ->
  rw_cells rsegs m (SA0 + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used)] -> mem_inv rsegs m ->
  pv + 16 <= X + 160 \/ X + 168 <= pv + 8 -> SA0 + 32 <= X + 160 \/ X + 168 <= SA0 + 16 ->
  0 <= SP -> 0 <= X -> 0 < pv -> pv mod 8 = 0 ->
  0 <= off -> 0 < n < 2 ^ 63 -> off + n < 2 ^ 64 -> 0 <= tl < 2 ^ 64 -> off + n <> tl ->
  0 <= used -> used + n < 2 ^ 64 -> 0 <= buf < 2 ^ 64 ->
  evt rsegs (fun ms => exists m' x12',
      ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA0) (Z_to_bv 64 (X + 144))
                   (Z_to_bv 64 (used + n)) (Z_to_bv 64 (off + n)) x12' x13 x14 x15 x16 x17 (Z_to_bv 64 buf)
                   (Z_to_bv 64 n) (Z_to_bv 64 X) x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1))
                   x28 x29 x30 x31)
              Fr (Z_to_bv 64 0x13b8c) fc None m' (seg_rom rsegs) /\
      munch [(X + 160, X + 168); (SA0 + 24, SA0 + 32)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 (off + n))] /\
      rw_cells rsegs m' (SA0 + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (used + n))])
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA0) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
             (Z_to_bv 64 n) (Z_to_bv 64 X) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        Fr (Z_to_bv 64 0x13b30) fc None m (seg_rom rsegs)).
Proof using SEGS.
  intros x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Fr fc m
    SP SA0 X n pv off tl buf used HW HP HO HR HB MI DP DS HSP HX Hpv Hpv8 Hoff Hn Hon Htl KP HU HUN HBf.
  pose proof (rw_cells_bound _ _ _ _ HB) as BB. cbn [cells_size csize] in BB.
  pose proof (rw_cells_bound _ _ _ _ HO) as BO. cbn [cells_size csize] in BO.
  eapply evt_cut.
  { eapply dr_off; [exact HW | exact HP | exact HO | exact HR | exact MI | exact DP | exact HSP | exact HX | exact Hpv |
                    exact Hpv8 | exact Hoff | clear - Hn; lia | exact Hon | exact Htl]. }
  intros ms [(_ & ma & x12' & -> & MUa & WMa & MIa & HCa)|(E & _)]; [|exfalso; exact (KP E)].
  assert (HBa : rw_cells rsegs ma (SA0 + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used)]).
  { rewrite <- SEGS. eapply rw_tr; [apply (msame_munch _ _ _ MUa); rewrite SEGS; exact WMa | rewrite SEGS; exact HB |].
    intros a Ha. cbn [cells_size csize] in Ha. split; [clear - Ha BB; lia|]. cbn [outside].
    split; [clear - Ha DS; lia | exact I]. }
  eapply evt_mono.
  { eapply dr_add; [exact HBa | exact MIa | clear - Hn; lia | exact HU | exact HUN | exact HBf]. }
  intros ms [(N0 & _)|(_ & mb & -> & MUb & WMb & _ & HCb)]; [exfalso; clear - N0 Hn; lia|].
  exists mb, x12'. split; [reflexivity|].
  split.
  { apply (munch_trans _ m ma mb).
    - apply (munch_weaken [(X + 160, X + 168)]); [|exact MUa]. intros x (H1 & H2 & _). split; [exact H1 | exact I].
    - apply (munch_weaken [(SA0 + 24, SA0 + 32)]); [|exact MUb]. intros x (H1 & H2 & _). split; [exact H2 | exact I]. }
  split; [exact (wmono_trans _ _ _ _ WMa WMb)|].
  split; [|exact HCb].
  rewrite <- SEGS. eapply rw_tr; [apply (msame_munch _ _ _ MUb); rewrite SEGS; exact WMb | rewrite SEGS; exact HCa |].
  intros a Ha. cbn [cells_size csize] in Ha. split; [clear - Ha BO; lia|]. cbn [outside].
  split; [clear - Ha DS; lia | exact I].
Qed.

Lemma H2_rtk_fut : forall s tp a, ds_eintr s = false -> ds_pend s <> [] -> dstrict s -> 4096 <= ds_cap s - ulen s ->
  dwhole s = false -> RFUT tp (drun (dneed s) LIVE MX s (nretF tp) a) ->
  RFUT ((tp ++ fst (fst (dpush s (nretF tp) a))) ++
          fst (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
                 (nretF (tp ++ fst (fst (dpush s (nretF tp) a)))) (da_out a) (da_hp a) (da_keys a)))
    (drun (length (pstream s)) LIVE MX (dnext LIVE MX s)
       (nretF (tp ++ fst (fst (dpush s (nretF tp) a))) +
        nretF (fst (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
                 (nretF (tp ++ fst (fst (dpush s (nretF tp) a)))) (da_out a) (da_hp a) (da_keys a))))
       (anext (apush a (snd (dpush s (nretF tp) a)))
          (snd (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
                 (nretF (tp ++ fst (fst (dpush s (nretF tp) a)))) (da_out a) (da_hp a) (da_keys a))))).
Proof using All.
  intros s tp a Ee PEn STR GR W (E1 & E2 & E3).
  assert (DN : dneed s = S (length (pstream s)))
    by (unfold dneed; rewrite Ee; cbn [Nat.b2n]; rewrite Nat.add_0_r; reflexivity).
  assert (DD : ddrop s a = []) by (unfold ddrop; rewrite W; reflexivity).
  rewrite DN, (drun_data _ _ _ _ _ _ GR Ee PEn STR) in E1, E2, E3. cbn [fst snd] in E1, E2, E3.
  unfold dnext_a, dlines in E1, E2, E3. rewrite W, DD, nret_nil, Nat.add_0_r in E1, E2, E3.
  cbn [app] in E1.
  rewrite !nret_app. unfold RFUT, lrest, anext, apush.
  cbn [fst snd da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  rewrite <- !app_assoc.
  split; [exact E1|]. split; [exact E2 | exact E3].
Qed.

Lemma read_tail_keep : forall s c, DRE s c -> dwhole s = false -> SR segs c (DHQ s).
Proof using All.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 & G20
    & G21 & G23 & G24 & G26 & G27 & HW32 & HR & NP & GR & E & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1
    & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) W.
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof H3h as (_ & _ & _ & NZU).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  pose proof BK1 as (_ & GI1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  rewrite E in L6c. cbv beta iota in L6c.
  assert (PE : ds_pend s = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0) by (rewrite <- L7c, HR; reflexivity).
  assert (PNE : ds_pend s <> []) by (rewrite PE; discriminate).
  assert (OFF : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
  { destruct S8 as [(RN & _)|(r1 & rs1 & RE1 & RO')]; [rewrite HR in RN; discriminate|].
    rewrite HR in RE1. injection RE1 as <- <-. exact RO'. }
  assert (STR : dstrict s).
  { intros r rs Er. rewrite PE in Er. injection Er as <- _. rewrite <- L8c. unfold bzs. rewrite length_map.
    exact (proj2 OFF). }
  assert (ULEN : ulen s = re_used e1) by (unfold ulen; rewrite <- L2c; unfold bzs; rewrite length_map; exact K7).
  assert (LH : Z.of_nat (length (dhead s)) = Z.of_nat (length (snd r0))).
  { unfold dhead. rewrite PE. unfold bzs. rewrite length_map. reflexivity. }
  assert (GR' : 4096 <= re_cap e1 - re_used e1) by (rewrite L1c, <- ULEN; exact GR).
  assert (NR : dnum s <= re_cap e1 - re_used e1 /\ hs_off h1 + dnum s <= Z.of_nat (length (snd r0))).
  { unfold dnum. rewrite LH, <- L1c, ULEN, <- L8c. clear - OFF. lia. }
  assert (KP : hs_off h1 + dnum s <> Z.of_nat (length (snd r0))).
  { intros X. unfold dwhole in W. rewrite <- L8c, LH, X, Z.eqb_refl in W. discriminate W. }
  assert (BUF : 0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (blocks L1 A1)).
  { destruct K10 as [(C0 & _ & U0)|(Cp & BI & _)]; [clear - C0 U0 GR'; lia | split; [exact Cp | exact BI]]. }
  destruct BUF as (Cp & BI).
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  pose proof S6 as (P1 & P2 & P3 & _ & _ & P6).
  assert (PN : 1 <= hl_n (hs_pending h1) <= hl_cap (hs_pending h1)).
  { pose proof P2 as P2'. unfold hl_n in P2' |- *. rewrite HR in P2' |- *. cbn [length] in P2' |- *. clear - P2'. lia. }
  assert (PA : 0 < hl_cap (hs_pending h1) /\ In (hl_v (hs_pending h1), 16 * hl_cap (hs_pending h1)) (blocks L1 A1) /\
               rw_cells segs m1 (hl_v (hs_pending h1)) [CB (Z.to_nat (16 * hl_cap (hs_pending h1)))
                 (concat (map text_rec (hl_recs (hs_pending h1))) ++ hl_junk (hs_pending h1))]).
  { destruct P3 as [(C0 & _)|(Cq & PIq & _ & _ & PCq)]; [clear - C0 PN; lia|].
    split; [exact Cq|]. split; [exact PIq | exact PCq]. }
  destruct PA as (PCp & PIn & PCc).
  pose proof (blk_rng _ _ _ _ _ _ M1 PIn) as PBR.
  pose proof (blk_align _ _ _ _ _ _ M1 PIn) as PAL.
  pose proof (rbl_apart _ _ _ _ _ _ M1 PIn ltac:(clear - PCp; lia)) as PAP.
  pose proof (rbl_apart _ _ _ _ _ _ M1 GI1 ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as GAP.
  assert (TI : In (fst r0, Z.of_nat (length (snd r0)) + 1) (blocks L1 A1)).
  { exact (proj1 (proj1 (Forall_forall _ _) P6 r0 ltac:(rewrite HR; left; reflexivity))). }
  pose proof (blk_rng _ _ _ _ _ _ M1 TI) as TBR.
  assert (HR0 : rw_cells rsegs m1 (hl_v (hs_pending h1))
                  [C8 (Z_to_bv 64 (fst r0)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))]).
  { apply (cb_prefix m1 _ (Z.to_nat (16 * hl_cap (hs_pending h1))) _
             (concat (map text_rec rs0) ++ hl_junk (hs_pending h1))); [|cbn; repeat split].
    pose proof PCc as PC2. rewrite SEGS, HR in PC2.
    change (concat (map text_rec (r0 :: rs0))) with
      ((le8 (Z_to_bv 64 (fst r0)) ++ le8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))) ++ concat (map text_rec rs0))
      in PC2.
    cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- !app_assoc in PC2 |- *. exact PC2. }
  assert (HPc : rw_cells rsegs (normalize rsegs m1) (XH + 144) [C8 (Z_to_bv 64 (hl_v (hs_pending h1)))]).
  { assert (P1r : rw_cells rsegs m1 (HA + 16)
                    [C8 (Z_to_bv 64 (hl_v (hs_pending h1))); C4 (Z_to_bv 64 (hl_n (hs_pending h1)));
                     C4 (Z_to_bv 64 (hl_cap (hs_pending h1)))]) by (rewrite <- SEGS; exact P1).
    destruct (dr_cut m1 (HA + 16) (HA + 16 + 8) [C8 (Z_to_bv 64 (hl_v (hs_pending h1)))]
                [C4 (Z_to_bv 64 (hl_n (hs_pending h1))); C4 (Z_to_bv 64 (hl_cap (hs_pending h1)))] P1r eq_refl)
      as [P1a _].
    replace (XH + 144) with (HA + 16) by (clear - HJ; unfold DR_TU, G_S, SRC_SIZE; lia).
    apply rbl_norm_hi; [exact RO1r | exact P1a | clear - HJ; unfold G_S, SRC_SIZE; lia]. }
  assert (HOc : rw_cells rsegs (normalize rsegs m1) (XH + 160) [C8 (Z_to_bv 64 (hs_off h1))]).
  { assert (S7r : rw_cells rsegs m1 (HA + 32)
                    [C8 (Z_to_bv 64 (hs_off h1)); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1));
                     C4 (Z_to_bv 64 (hs_overlong h1))]) by (rewrite <- SEGS; exact S7).
    destruct (dr_cut m1 (HA + 32) (HA + 32 + 8) [C8 (Z_to_bv 64 (hs_off h1))]
                [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]
                S7r eq_refl) as [S7a _].
    replace (XH + 160) with (HA + 32) by (clear - HJ; unfold DR_TU, G_S, SRC_SIZE; lia).
    apply rbl_norm_hi; [exact RO1r | exact S7a | clear - HJ; unfold G_S, SRC_SIZE; lia]. }
  destruct (dr_cut m1 (hl_v (hs_pending h1)) (hl_v (hs_pending h1) + 8) [C8 (Z_to_bv 64 (fst r0))]
              [C8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))] HR0 eq_refl) as [_ HR8].
  assert (HRc : rw_cells rsegs (normalize rsegs m1) (hl_v (hs_pending h1) + 8)
                  [C8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))])
    by (apply (rbl_norm_blk _ _ _ _ _ _ _ _ _ M1 RO1r HR8 PIn);
        [clear - PCp; lia | cbn [cells_size csize]; clear - PCp; lia]).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (_ & EC2 & _).
  destruct (dr_cut m1 (SA + 16) (SA + 16 + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]
              [C8 (Z_to_bv 64 (re_cap e1))] EC2 eq_refl) as [EC2a _].
  assert (HSc : rw_cells rsegs (normalize rsegs m1) (SA + 16)
                  [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))])
    by (apply (rbl_norm_blk _ _ _ _ _ _ _ _ _ M1 RO1r EC2a GI1);
        [clear - F6; lia | cbn [cells_size csize]; clear - F7; unfold SRC_TABLE, SRC_ENTRY in *; lia]).
  assert (HWc : rw_cells rsegs (normalize rsegs m1) (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))])
    by (apply rbl_norm_hi; [exact RO1r | rewrite <- SEGS; exact HW32 | clear - F1 F3; lia]).
  destruct RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G8, G19, G20. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply H2_rtk_seg.
    - exact HWc.
    - exact HPc.
    - exact HOc.
    - exact HRc.
    - exact HSc.
    - apply mem_inv_normalize.
    - clear - PAP PCp F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia.
    - clear - GAP F6 F7 F11. unfold SRC_TABLE, SRC_ENTRY, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia.
    - clear - F1 F3. lia.
    - clear - F11. unfold DR_TU. lia.
    - clear - PBR. lia.
    - clear - PAL. Z.div_mod_to_equations. lia.
    - exact (proj1 OFF).
    - clear - NP NR K6 K7. lia.
    - clear - NR TBR F4. lia.
    - clear - TBR F4. lia.
    - exact KP.
    - clear - K7. lia.
    - clear - NR K6 K7. lia.
    - clear - BR F4 Cp. lia. }
  intros ms (can & (s0' & HQ & REL & ROS) & EQ).
  destruct HQ as (m' & x12' & -> & MU & WM & HX & HB).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2].
  rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HX) as HX2.
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HB) as HB2.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  assert (HC2 : rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 (hs_off h1 + dnum s))]).
  { replace (HA + 32) with (XH + 160) by (clear - HJ; unfold DR_TU, G_S, SRC_SIZE; lia). rewrite SEGS. exact HX2. }
  assert (HB2s : rw_cells segs m2 (SA + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1 + dnum s))])
    by (rewrite SEGS; exact HB2).
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 32 <= a < HA + 40) -> ~ (SA + 24 <= a < SA + 32) ->
                 outside [(XH + 160, XH + 168); (SA + 24, SA + 32)] a).
  { intros a _ D1 D2. cbn [outside].
    split; [clear - D1 HJ; unfold DR_TU, G_S, SRC_SIZE in *; lia | split; [exact D2 | exact I]]. }
  assert (OFP : exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= hs_off h1 + dnum s < Z.of_nat (length (snd r))).
  { exists r0, rs0. split; [exact HR | clear - OFF NR KP NP; lia]. }
  destruct (rtk_bundle s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D _ (hs_off h1 + dnum s) (re_used e1 + dnum s)
              (re_U e1 ++ firstn (Z.to_nat (dnum s)) (re_junk e1)) (skipn (Z.to_nat (dnum s)) (re_junk e1))
              RP1 FR1 SAC1 EK1 SR1 OT1 H7h H8h BK1 GL1 OU1 MU2 WM2s HW HC2 HB2s OFP)
    as (RP2 & FR2 & SAC2 & EK2 & SR2 & OT2 & GL2 & OU2).
  assert (PS' : pstream s = ddata s ++ prest (ds_pend s) (ds_off s + dnum s))
    by (apply rtk_ps; [exact WF1 | clear - NP; lia]).
  assert (LPS : length (pstream s) = (length (ddata s) + length (prest (ds_pend s) (ds_off s + dnum s)))%nat)
    by (rewrite PS', length_app; reflexivity).
  apply SR_ret. unfold DHQ, DLN.
  exists R2, L1, A1, m2, md1,
    (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1 + dnum s) (re_cap e1) (re_hp e1)
        (re_kh e1) (re_pad2 e1) (re_keys e1) (re_U e1 ++ firstn (Z.to_nat (dnum s)) (re_junk e1))
        (skipn (Z.to_nat (dnum s)) (re_junk e1))),
    (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1 + dnum s) (hs_partial h1)
        (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)),
    OUT1, junk1, LB1, D.
  split; [reflexivity|].
  split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
  split; [cbn [re_buf]; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; rgw X2|].
  split; [split; [apply Nat.le_0_l | left; reflexivity]|].
  destruct (rtk_p0 s) as (P0a & P0b & P0c & P0d & P0e & P0f).
  unfold DLC, LCORE. rewrite P0a, P0b, P0c, P0d, P0e, P0f, app_nil_r, (rtk_dv s W), (drlq_0 s NZU).
  split; [exact RP2|].
  split; [exact IN1|].
  split.
  { destruct TR1 as (tp & qd & a & (LQ & WT1 & AOK & ROK & DL1 & DKH1) & RF1).
    exists (tp ++ fst (fst (dpush s (nretF tp) a))), qd, (apush a (snd (dpush s (nretF tp) a))).
    split; [|exact (H2_rtk_fut s tp a E PNE STR GR W RF1)].
    split; [exact LQ|]. split; [exact WT1|]. split; [exact AOK|]. split; [exact ROK|].
    split; [exact DL1 | exact DKH1]. }
  split; [rewrite SEGS; exact RO2|].
  split; [exact FR2|].
  split; [exact SAC2|].
  split; [apply rtk_okx; [exact EK2 | exact Cp | clear - NP NR; lia]|].
  split; [exact SR2|].
  split; [exact OT2|].
  split; [exact SM1|].
  split.
  { unfold DLINK. cbn [ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap re_cap re_U re_skip
                       re_keys hs_eintr hs_pending hs_off hs_expected].
    split; [exact L1c|].
    split; [unfold dW; rewrite <- L2c, <- JK; unfold bzs; apply map_app|].
    split; [exact L3c|]. split; [exact L4c|]. split; [exact L5c|]. split; [exact L6c|]. split; [exact L7c|].
    split; [rewrite L8c; reflexivity|]. split; [exact L9c|]. split; [exact L10c|]. split; [exact L11c|].
    unfold dwf. cbn [ds_off ds_pend]. split; [clear - OFF NP L8c; lia|].
    intros r rs Er. rewrite PE in Er. injection Er as <- _. unfold bzs. rewrite length_map. clear - NR L8c. lia. }
  split.
  { unfold DHISTg. cbn [ds_ref ds_no ds_H ds_en hs_expected].
    split; [rewrite H1h, PS', app_assoc; reflexivity|].
    split; [rewrite H2h, feed_app; reflexivity|].
    split; [exact H4h|]. split; [exact H5h|]. split; [exact H6h|]. split; [exact H7h|]. split; [exact H8h|].
    split; [exact H9h|]. split; [exact H10h|].
    unfold pstream. cbn [ds_pend ds_off]. pose proof (rbl_lines_le (ddata s) (ds_ref s)) as LL. unfold dref.
    clear - LL LPS H12h. lia. }
  split.
  { unfold pstream. cbn [ds_pend ds_off]. pose proof (rtk_chunk_le (ds_u s) (ds_skip s) (ddata s)) as CL.
    unfold drl, dchunk. clear - CL LPS H11h. lia. }
  split.
  { split; [exact H2h|]. split; [exact H3h|]. split; [exact GR|]. split; [exact WF1|]. split; [exact STR|].
    split; [exact E | exact PNE]. }
  split; [unfold DBLK in BK1 |- *; exact BK1|].
  split.
  - unfold DGLBg. unfold DGLB, brf, eif, dtot in GL2. exact GL2.
  - unfold DOUT in OU2 |- *. cbn [ds_no ds_ocap]. exact OU2.
Qed.

Definition hdrop (h1 : hsrc) (rs0 : list (Z * list byte)) (jk : list byte) : hsrc :=
  HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (HL (hl_v (hs_pending h1)) (hl_cap (hs_pending h1)) rs0 jk) 0
     (hs_partial h1) (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1).

Definition src_dl (L1 : layout) (A1 : astate) (m1 : word -> option byte) (h1 : hsrc) (o : Z) : Prop :=
  rw_cells segs m1 HA [C4 (Z_to_bv 64 (hs_fd h1)); C4 (Z_to_bv 64 (hs_open h1));
                       C4 (Z_to_bv 64 (hs_closed h1)); C4 (Z_to_bv 64 (hs_eintr h1))] /\
  (hs_closed h1 = 0 \/ hs_closed h1 = 1) /\ (hs_eintr h1 = 0 \/ hs_eintr h1 = 1) /\
  hs_open h1 = 1 /\ 0 <= hs_fd h1 < 2 ^ 31 /\
  list_at Bm L1 A1 m1 (HA + 16) (hs_pending h1) false /\
  rw_cells segs m1 (HA + 32) [C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 (hs_partial h1));
                              C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))] /\
  0 <= hs_npartial h1 <= 6000 /\ (hs_overlong h1 = 0 \/ hs_overlong h1 = 1) /\
  In (hs_partial h1, 6000) (blocks L1 A1) /\ fresh_block Bm (hs_partial h1) 6000 /\
  Z.of_nat (length (hs_pjunk h1)) = 6000 /\
  rw_cells segs m1 (hs_partial h1) [CB (Z.to_nat 6000) (hs_pjunk h1)] /\
  ~ In (Z_to_bv 8 0) (hs_W h1) /\
  list_at Bm L1 A1 m1 (HA + 64) (hs_expected h1) true /\
  list_at Bm L1 A1 m1 (HA + 80) (hs_held h1) true /\
  NoDup (hs_blocks h1).

Definition hdropl (h1 : hsrc) (rs0 : list (Z * list byte)) : hsrc :=
  hdrop h1 rs0 (text_rec (last (hl_recs (hs_pending h1)) (0, [])) ++ hl_junk (hs_pending h1)).

Definition DRF (s : dstate) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (r0 : Z * list byte) (rs0 : list (Z * list byte)),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13b70) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 19 = Z_to_bv 64 (dnum s) /\ getr R1 20 = Z_to_bv 64 XH /\
    hl_recs (hs_pending h1) = r0 :: rs0 /\ 0 < dnum s /\ 4096 <= ds_cap s - ulen s /\
    ds_eintr s = false /\ dwhole s = true /\
    bzs (firstn (Z.to_nat (dnum s)) (re_junk e1)) = ddata s /\
    relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 /\
    st_init_done A1 = true /\
    MTR s L1 A1 (ds_ocap s) e1 (hdropl h1 rs0) OUT1 (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)) /\
    ro_agree segs m1 /\
    (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
    rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] /\
    entry_okw L1 A1 m1 e1 /\
    src_dl L1 A1 m1 (hdropl h1 rs0) (ds_off s + dnum s) /\
    (forall k, ~ In (fst r0, k) (blocks L1 A1)) /\
    others_at Bm m1 j (re_fd e) fs os /\
    DSAME e1 h1 /\
    (re_cap e1 = ds_cap s /\ bzs (re_U e1) = ds_u s /\ re_skip e1 = (if ds_skip s then 1 else 0) /\
     keys_texts (re_keys e1) = ds_H s /\ ent_ka e1 = ds_ka s /\ hs_eintr h1 = (if ds_eintr s then 1 else 0) /\
     map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = ds_pend s /\ hs_off h1 = ds_off s /\
     hs_state h1 = feed (ds_ref s) (ddata s) /\
     hl_n (hs_expected h1) = ds_en s + Z.of_nat (length (dref s)) /\
     hl_cap (hs_expected h1) = pcapm (ds_en s) (ds_ecap s) (dref s) /\
     dwf s) /\
    (bzs PS = D ++ pstream s /\ ds_ref s = feed ST0 D /\ J1 (ds_u s) (ds_skip s) (ds_ref s) /\
     map snd (hl_recs (hs_expected h1)) =
       map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines ST0 (D ++ ddata s)) /\
     firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
     hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
     ds_no s = NO + dtot D /\ bzs LB1 = with_nul (lines ST0 D) /\
     NoDup (ds_H s) /\ same_set (ds_H s) (upds (keys_texts (re_keys e)) (lines ST0 D)) /\
     Z.of_nat (length (ds_H s)) + Z.of_nat (length (pstream s)) < 2 ^ 26 /\
     ds_en s + Z.of_nat (length (pstream s)) < 2 ^ 27) /\
    DBLK L1 A1 e1 h1 OUT1 /\
    DGLB D m1 /\
    DOUT s L1 A1 m1 OUT1 junk1 LB1.

Lemma drf_dblk : forall L1 A1 m1 md1 L2 A2 e1 h1 OUT1 (r0 : Z * list byte) rs0 b1 b2,
  MR L1 A1 m1 md1 -> DBLK L1 A1 e1 h1 OUT1 -> hl_recs (hs_pending h1) = r0 :: rs0 ->
  blocks L1 A1 = b1 ++ (fst r0, Z.of_nat (length (snd r0)) + 1) :: b2 -> blocks L2 A2 = b1 ++ b2 ->
  DBLK L2 A2 e1 h1 OUT1 /\ (forall k, ~ In (fst r0, k) (blocks L2 A2)) /\
  (forall q k, In (q, k) (blocks L1 A1) -> q <> fst r0 -> In (q, k) (blocks L2 A2)).
Proof using NODUP.
  intros L1 A1 m1 md1 L2 A2 e1 h1 OUT1 r0 rs0 b1 b2 M1 (ND & GI & B3 & B4 & B5) HR E1 E2.
  pose proof (NODUP _ _ _ _ M1) as NDB0. apply NoDup_ListNoDup in NDB0.
  pose proof NDB0 as NDB. rewrite E1, map_app in NDB. cbn [map fst] in NDB.
  pose proof (List.NoDup_remove_2 _ _ _ NDB) as NI.
  assert (TI : In (fst r0, Z.of_nat (length (snd r0)) + 1) (blocks L1 A1))
    by (rewrite E1; apply in_or_app; right; left; reflexivity).
  assert (R0H : In (fst r0) (hs_blocks h1))
    by (apply hb_pend; unfold list_blocks; apply in_or_app; right; rewrite HR; left; reflexivity).
  assert (KEEP : forall q k, In (q, k) (blocks L1 A1) -> q <> fst r0 -> In (q, k) (blocks L2 A2)).
  { intros q k Hq Hn. rewrite E1 in Hq. rewrite E2. apply in_app_or in Hq as [Hq|[Hq|Hq]].
    - apply in_or_app. left. exact Hq.
    - exfalso. injection Hq as Hq1 _. apply Hn. symmetry. exact Hq1.
    - apply in_or_app. right. exact Hq. }
  assert (GONE : forall k, ~ In (fst r0, k) (blocks L2 A2)).
  { intros k Hk. rewrite E2 in Hk. apply NI. rewrite <- map_app. exact (in_map fst _ _ Hk). }
  split; [|split; [exact GONE | exact KEEP]].
  split; [exact ND|].
  split.
  { apply KEEP; [exact GI|]. pose proof ND as ND'. apply NoDup_ListNoDup, List.NoDup_cons_iff in ND' as [GN _].
    intros X. apply GN. rewrite X. right. apply in_or_app. right. exact R0H. }
  split.
  { intros q m Hq Ho Hn. pose proof (B3 q m Hq Ho Hn) as Hq1. apply KEEP; [exact Hq1|]. intros X. subst q.
    pose proof (sb_nodup_fst _ (fst r0) m _ NDB0 Hq1 TI) as Em.
    destruct (B5 (fst r0) m Hq ltac:(clear - Em; lia) Ho Hn) as (_ & _ & NH). exact (NH R0H). }
  split.
  { intros q m Hq. rewrite E2 in Hq. apply B4. rewrite E1.
    apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
  exact B5.
Qed.

Lemma free_rp : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n,
  WF A1 -> In (p, n) (user_blocks A1) -> 0 < n -> MR L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  relay_post Bm API ALLOC_STACK (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) (fun q => q = ptr_addr L1 p)
    L1 A1 R1 m1 md1 L2 A2 R2 m2 md2.
Proof using AX CTX.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n HW Hp Hn HM CP SURV LN.
  destruct CP as (M' & W' & B' & LL & AD & RP & MD & FR & BY & SC).
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LL|]. split; [exact LN|].
  split; [intros q k H1 H2 _; exact (AD q k H1 H2)|].
  split; [intros q k H1 _ NF; apply SURV; [exact H1|]; intros ->; exact (NF eq_refl)|].
  split.
  { intros q H1.
    assert (Q : q <> p).
    { intros ->. pose proof (sb_nodup_fst _ p 0 n (YO10.user_block_ptrs_NoDup A1 HW) H1 Hp) as E0.
      clear - E0 Hn. lia. }
    pose proof (SURV q 0 H1 Q) as H2. split; [exact H2 | exact (AD q 0 H1 H2)]. }
  split; [intros a Hi Ho; exact (sb_owned_img Bm API AX CTX L1 A1 m1 md1 L2 A2 m2 md2 a HM M' Hi Ho)|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS NE; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | exact NE]|].
  split; [intros q k i H1 H2 _ Hi _; exact (BY q k i H1 H2 Hi)|].
  exact SC.
Qed.

Lemma pre_free : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre Bm MR L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold ALLOC_STACK in Ha. apply SC1. left.
    change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma drf_ret : YK0s.ret_ok (Z_to_bv 64 0x13b70).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rdf_live : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n, WF A1 ->
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p q n -> ~ F0 q -> live_at L2 A2 p q n.
Proof using All.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n W1 RP [Hp Hq] NF.
  pose proof RP as (_ & _ & _ & _ & _ & RPa & RPb & RPz & _). rewrite <- Hq in NF.
  destruct (Z_lt_le_dec 0 n) as [Np|Nn].
  - pose proof (RPb p n Hp Np NF) as Hp2. split; [exact Hp2|]. rewrite (RPa p n Hp Hp2 NF). exact Hq.
  - assert (N0 : n = 0) by (pose proof (sb_ub_nonneg A1 p n W1 Hp) as N1; clear - N1 Nn; lia). subst n.
    destruct (RPz p Hp) as [Hp2 Ha]. split; [exact Hp2|]. rewrite Ha. exact Hq.
Qed.

Lemma rdf_f2 : forall {X Y : Type} (R R' : X -> Y -> Prop) (Px : X -> Prop) xs ys,
  Forall2 R xs ys -> (forall x, In x xs -> Px x) -> (forall x y, Px x -> R x y -> R' x y) -> Forall2 R' xs ys.
Proof using All.
  intros X Y R R' Px xs ys H. induction H as [|x y xs' ys' Hxy Hr IH]; intros Hx Imp; [constructor|].
  constructor.
  - apply Imp; [apply Hx; left; reflexivity | exact Hxy].
  - apply IH; [intros z Hz; apply Hx; right; exact Hz | exact Imp].
Qed.

Lemma rdf_f2_cons : forall {X Y : Type} (R : X -> Y -> Prop) x xs ys,
  Forall2 R (x :: xs) ys -> exists y ys', ys = y :: ys' /\ R x y /\ Forall2 R xs ys'.
Proof using All.
  intros X Y R x xs ys H. destruct ys as [|y ys']; [inversion H|].
  exists y, ys'. split; [reflexivity|]. inversion H; subst. split; assumption.
Qed.

Lemma UI_nin : forall e1 h1 OUT1 (r0 : Z * list byte) rs0 jk,
  NoDup (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) -> hl_recs (hs_pending h1) = r0 :: rs0 ->
  forall q, q = OUT1 \/ In q (entry_blocks e1 ++ hs_blocks (hdrop h1 rs0 jk)) -> q <> fst r0.
Proof using.
  intros e1 h1 OUT1 r0 rs0 jk ND HR q Hq Eq. subst q.
  apply NoDup_ListNoDup in ND.
  assert (EH : hs_blocks h1 = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
                 fst r0 :: (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++
                            list_blocks (hs_held h1))).
  { unfold hs_blocks. unfold list_blocks at 1. rewrite HR. cbn [map]. rewrite <- app_assoc. reflexivity. }
  assert (ED : hs_blocks (hdrop h1 rs0 jk) = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
                 (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
  { unfold hs_blocks, hdrop. cbn [hs_pending hs_partial hs_expected hs_held]. unfold list_blocks at 1.
    cbn [hl_cap hl_v hl_recs]. rewrite <- app_assoc. reflexivity. }
  rewrite EH, app_assoc in ND. rewrite ED, app_assoc in Hq.
  pose proof (List.NoDup_remove_2
                (G :: OUT1 :: entry_blocks e1 ++ (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]))
                _ _ ND) as NI.
  apply NI. right. destruct Hq as [Hq|Hq]; [left; symmetry; exact Hq | right; exact Hq].
Qed.

Lemma rdf_nret : forall (T : trF) n a0, nretF (T ++ [RFree n a0]) = nretF T.
Proof using All. intros T n a0. rewrite nret_app. change (nretF [RFree n a0]) with 0%nat. lia. Qed.

Lemma rdf_runF_free : forall qd b (T : trF) n a0,
  runF F qd b (T ++ [RFree n a0]) = rt_free F (runF F qd b T) n (resolveF qd a0).
Proof using All. intros qd b T n a0. unfold runF, run_tr. rewrite run_from_app. reflexivity. Qed.

Lemma UI_links : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 qd a oc e1 h1 OUT1 (r0 : Z * list byte) rs0 jk,
  WF A1 -> relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall q, q = OUT1 \/ In q (entry_blocks e1 ++ hs_blocks (hdrop h1 rs0 jk)) -> ~ F0 q) ->
  hl_recs (hs_pending h1) = r0 :: rs0 -> DLNK L1 A1 qd a oc e1 h1 OUT1 ->
  DLNK L2 A2 qd (DA (da_out a) (da_buf a) (da_hp a) (da_keys a) (skipn 1 (da_pend a)) (da_ev a) (da_erecs a)) oc e1
    (hdrop h1 rs0 jk) OUT1.
Proof using All.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 qd a oc e1 h1 OUT1 r0 rs0 jk W1 RP NF HR
    (DO & (EL1 & EL2 & EL3) & (SL1 & SL2 & SL3 & (XL1 & XL2) & SL5 & SL6)).
  assert (T : forall p q n, live_at L1 A1 p q n -> q = OUT1 \/ In q (entry_blocks e1 ++ hs_blocks (hdrop h1 rs0 jk)) ->
                live_at L2 A2 p q n).
  { intros p q n Hl Hq. exact (rdf_live K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n W1 RP Hl (NF q Hq)). }
  assert (IE : forall q, In q (entry_blocks e1) ->
                 q = OUT1 \/ In q (entry_blocks e1 ++ hs_blocks (hdrop h1 rs0 jk))).
  { intros q Hq. right. apply in_or_app. left. exact Hq. }
  assert (IH : forall q, In q (hs_blocks (hdrop h1 rs0 jk)) ->
                 q = OUT1 \/ In q (entry_blocks e1 ++ hs_blocks (hdrop h1 rs0 jk))).
  { intros q Hq. right. apply in_or_app. right. exact Hq. }
  assert (LV : forall l, 0 < hl_cap l -> In (hl_v l) (list_blocks l)).
  { intros l C. unfold list_blocks. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - C; lia). left. reflexivity. }
  assert (LR : forall l r, In r (hl_recs l) -> In (fst r) (list_blocks l)).
  { intros l r Hr. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr. }
  rewrite HR in SL2. destruct (rdf_f2_cons _ r0 rs0 (da_pend a) SL2) as (a0 & as' & Ep & _ & SLt).
  rewrite Ep. cbn [skipn].
  unfold DLNK, entry_links, src_links, expected_links, hdrop.
  cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs hs_pending hs_partial hs_expected hs_held hl_v hl_cap hl_recs].
  split; [intros LVt C; exact (T _ _ _ (DO LVt C) (or_introl eq_refl))|].
  split.
  - split.
    { intros C. apply T; [exact (EL1 C)|]. apply IE. unfold entry_blocks. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - C; lia). left. reflexivity. }
    split.
    { intros C. apply T; [exact (EL2 C)|]. apply IE. unfold entry_blocks. apply in_or_app. right.
      apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
    apply (rdf_f2 _ _ (fun k => In (key_addr k) (entry_blocks e1)) _ _ EL3).
    + intros k Hk. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk.
    + intros k x Hk Hl. cbv beta in Hk, Hl |- *. exact (T _ _ _ Hl (IE _ Hk)).
  - split.
    { intros C. exact (T _ _ _ (SL1 C) (IH _ (hb_pend (hdrop h1 rs0 jk) _ (LV (hs_pending (hdrop h1 rs0 jk)) C)))). }
    split.
    { apply (rdf_f2 _ _ (fun r => In r rs0) _ _ SLt).
      - intros r Hr. exact Hr.
      - intros r x Hr Hl. cbv beta in Hr, Hl |- *.
        exact (T _ _ _ Hl (IH _ (hb_pend (hdrop h1 rs0 jk) _ (LR (hs_pending (hdrop h1 rs0 jk)) r Hr)))). }
    split; [exact (T _ _ _ SL3 (IH _ (hb_part (hdrop h1 rs0 jk))))|].
    split.
    { split.
      - intros C. exact (T _ _ _ (XL1 C) (IH _ (hb_exp (hdrop h1 rs0 jk) _ (LV (hs_expected (hdrop h1 rs0 jk)) C)))).
      - apply (rdf_f2 _ _ (fun r => In r (hl_recs (hs_expected h1))) _ _ XL2).
        + intros r Hr. exact Hr.
        + intros r x Hr Hl. cbv beta in Hr, Hl |- *.
          exact (T _ _ _ Hl (IH _ (hb_exp (hdrop h1 rs0 jk) _ (LR (hs_expected (hdrop h1 rs0 jk)) r Hr)))). }
    split.
    { intros C. exact (T _ _ _ (SL5 C) (IH _ (hb_held (hdrop h1 rs0 jk) _ (LV (hs_held (hdrop h1 rs0 jk)) C)))). }
    apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SL6 r Hr) as X. cbv beta in X |- *.
    exact (T _ _ _ X (IH _ (hb_held (hdrop h1 rs0 jk) _ (LR (hs_held (hdrop h1 rs0 jk)) r Hr)))).
Qed.

Lemma rdf_fut : forall s tp a, ds_eintr s = false -> ds_pend s <> [] -> dstrict s -> 4096 <= ds_cap s - ulen s ->
  dwhole s = true -> RFUT tp (drun (dneed s) LIVE MX s (nretF tp) a) ->
  RFUT (((tp ++ fst (fst (dpush s (nretF tp) a))) ++ ddrop s a) ++
          fst (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
                 (nretF ((tp ++ fst (fst (dpush s (nretF tp) a))) ++ ddrop s a)) (da_out a) (da_hp a) (da_keys a)))
    (drun (length (pstream s)) LIVE MX (dnext LIVE MX s)
       (nretF ((tp ++ fst (fst (dpush s (nretF tp) a))) ++ ddrop s a) +
        nretF (fst (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
                 (nretF ((tp ++ fst (fst (dpush s (nretF tp) a))) ++ ddrop s a)) (da_out a) (da_hp a) (da_keys a))))
       (anext (DA (da_out a) (da_buf a) (da_hp a) (da_keys a) (skipn 1 (da_pend a))
                 (fst (snd (dpush s (nretF tp) a))) (snd (snd (dpush s (nretF tp) a))))
          (snd (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s)
                 (nretF ((tp ++ fst (fst (dpush s (nretF tp) a))) ++ ddrop s a)) (da_out a) (da_hp a) (da_keys a))))).
Proof using All.
  intros s tp a Ee PEn STR GR W (E1 & E2 & E3).
  assert (DN : dneed s = S (length (pstream s)))
    by (unfold dneed; rewrite Ee; cbn [Nat.b2n]; rewrite Nat.add_0_r; reflexivity).
  rewrite DN, (drun_data _ _ _ _ _ _ GR Ee PEn STR) in E1, E2, E3. cbn [fst snd] in E1, E2, E3.
  unfold dnext_a in E1, E2, E3. rewrite W in E1, E2, E3.
  rewrite !nret_app. unfold RFUT, lrest, anext.
  cbn [fst snd da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  rewrite <- !app_assoc.
  split; [exact E1|]. split; [exact E2 | exact E3].
Qed.

Lemma UI_pre_ld : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre_k Bm MR LIST_DROP_K L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK in Ha. apply SC1. left.
    change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma UI_hb : forall h1 (r0 : Z * list byte) rs0 jk, hl_recs (hs_pending h1) = r0 :: rs0 ->
  (forall q, In q (hs_blocks (hdrop h1 rs0 jk)) -> In q (hs_blocks h1)) /\
  (forall q, In q (hs_blocks h1) -> q <> fst r0 -> In q (hs_blocks (hdrop h1 rs0 jk))) /\
  (forall pre, List.NoDup (pre ++ hs_blocks h1) -> List.NoDup (pre ++ hs_blocks (hdrop h1 rs0 jk))).
Proof using.
  intros h1 r0 rs0 jk HR.
  assert (E1 : hs_blocks h1 = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
                 fst r0 :: (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
  { unfold hs_blocks, list_blocks at 1. rewrite HR. cbn [map]. rewrite <- !app_assoc. reflexivity. }
  assert (E2 : hs_blocks (hdrop h1 rs0 jk) = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
                 (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
  { unfold hs_blocks, hdrop, list_blocks at 1. cbn [hs_pending hs_partial hs_expected hs_held hl_v hl_cap hl_recs].
    rewrite <- !app_assoc. reflexivity. }
  rewrite E1, E2. split; [|split].
  - intros q Hq. apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq].
  - intros q Hq Hn. apply in_app_or in Hq as [Hq|[Hq|Hq]]; apply in_or_app;
      [left; exact Hq | exfalso; exact (Hn (eq_sym Hq)) | right; exact Hq].
  - intros pre ND. rewrite app_assoc in ND |- *. exact (List.NoDup_remove_1 _ _ _ ND).
Qed.

Lemma UI_src_dl_tr : forall L1 A1 L2 A2 m1 m2 h1 (r0 : Z * list byte) rs0 jk o Pa,
  msame Pa m1 m2 -> src_at Bm L1 A1 m1 HA h1 -> hl_recs (hs_pending h1) = r0 :: rs0 ->
  (forall a, HA <= a < HA + 96 -> ~ (HA + 24 <= a < HA + 28 \/ HA + 32 <= a < HA + 40) -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> q <> fst r0 -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> ~ In q (list_blocks (hs_pending h1)) -> q <= a < q + k -> Pa a) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 o)] ->
  list_at Bm L2 A2 m2 (HA + 16) (hs_pending (hdrop h1 rs0 jk)) false ->
  src_dl L2 A2 m2 (hdrop h1 rs0 jk) o.
Proof using EHI GEI HG HJ O PRE SEGS h junk.
  intros L1 A1 L2 A2 m1 m2 h1 r0 rs0 jk o Pa MS
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) HR HC SV HB OC LT.
  pose proof gfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11).
  destruct (UI_hb h1 r0 rs0 jk HR) as (_ & _ & HB3).
  assert (NDd : NoDup (hs_blocks (hdrop h1 rs0 jk))).
  { pose proof S18 as S18l. apply NoDup_ListNoDup in S18l. apply NoDup_ListNoDup. exact (HB3 [] S18l). }
  pose proof S18 as ND. apply NoDup_ListNoDup in ND. unfold hs_blocks in ND.
  assert (R0P : In (fst r0) (list_blocks (hs_pending h1)))
    by (unfold list_blocks; apply in_or_app; right; rewrite HR; left; reflexivity).
  assert (NR : forall q, In q ([hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)) ->
                 ~ In q (list_blocks (hs_pending h1))).
  { intros q Hq X. exact (rbl_nd_disj _ _ q ND X Hq). }
  assert (NR0 : forall q, In q ([hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)) ->
                 q <> fst r0).
  { intros q Hq X. subst q. exact (NR _ Hq R0P). }
  assert (PI : In (hs_partial h1) ([hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)))
    by (apply in_or_app; left; left; reflexivity).
  assert (EI : forall q, In q (list_blocks (hs_expected h1)) ->
                 In q ([hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)))
    by (intros q Hq; apply in_or_app; right; apply in_or_app; left; exact Hq).
  assert (HI : forall q, In q (list_blocks (hs_held h1)) ->
                 In q ([hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)))
    by (intros q Hq; apply in_or_app; right; apply in_or_app; right; exact Hq).
  unfold hdrop in LT. cbn [hs_pending] in LT.
  unfold src_dl, hdrop.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_expected
       hs_held].
  split; [eapply rw_tr; [exact MS | exact S1 | intros a Ha; apply HC; cbn [cells_size csize] in Ha; clear - Ha; lia]|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split; [exact LT|].
  split.
  { pose proof S7 as S7r. rewrite SEGS in S7r.
    destruct (dr_cut m1 (HA + 32) (HA + 40) [C8 (Z_to_bv 64 (hs_off h1))] _ S7r
                ltac:(cbn [cells_size csize]; clear - F11; lia)) as [_ S7b].
    assert (S7c : rw_cells segs m2 (HA + 40) [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1));
                                               C4 (Z_to_bv 64 (hs_overlong h1))]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact S7b |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HC; clear - Ha; lia. }
    rewrite SEGS in OC, S7c |- *.
    exact (dr_join m2 (HA + 32) (HA + 40) [C8 (Z_to_bv 64 o)] _ OC S7c ltac:(cbn [cells_size csize]; clear - F11; lia)). }
  split; [exact S9|]. split; [exact S10|].
  split; [exact (SV _ _ S11 (hb_part h1) (NR0 _ PI))|]. split; [exact S12|]. split; [exact S13|].
  split.
  { eapply rw_tr; [exact MS | exact S14 |]. intros a Ha. apply (HB _ _ a S11 (NR _ PI)).
    cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear; lia). clear - Ha. lia. }
  split; [exact S15|].
  split.
  { eapply list_at_tr; [exact MS | exact S16 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. exact (SV q k Hq (hb_exp h1 q Hl) (NR0 _ (EI q Hl))).
    - intros q k a Hq Hl Ha. exact (HB q k a Hq (NR _ (EI q Hl)) Ha). }
  split.
  { eapply list_at_tr; [exact MS | exact S17 | intros a Ha; apply HC; clear - Ha; lia | |].
    - intros q k Hq Hl. exact (SV q k Hq (hb_held h1 q Hl) (NR0 _ (HI q Hl))).
    - intros q k a Hq Hl Ha. exact (HB q k a Hq (NR _ (HI q Hl)) Ha). }
  exact NDd.
Qed.

Lemma UI_drf_bundle : forall s L1 A1 m1 L2 A2 m2 e1 h1 OUT1 junk1 LB1 D (r0 : Z * list byte) rs0 jk (Pa : Z -> Prop) o,
  msame Pa m1 m2 -> hl_recs (hs_pending h1) = r0 :: rs0 ->
  (forall a, img_plain Bm a -> ~ (HA + 24 <= a < HA + 28 \/ HA + 32 <= a < HA + 40) -> Pa a) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> ~ In q (list_blocks (hs_pending h1)) -> q <= a < q + k -> Pa a) ->
  (forall a, S0 - 144 <= a < S0 -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> q <> fst r0 -> In (q, k) (blocks L2 A2)) ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] ->
  entry_okw L1 A1 m1 e1 -> src_at Bm L1 A1 m1 HA h1 -> others_at Bm m1 j (re_fd e) fs os ->
  ds_no s = NO + dtot D -> bzs LB1 = with_nul (lines ST0 D) ->
  DBLK L1 A1 e1 h1 OUT1 -> DGLB D m1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  (exists ev, rw_cells segs m2 ERR [C4 ev]) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 o)] ->
  list_at Bm L2 A2 m2 (HA + 16) (hs_pending (hdrop h1 rs0 jk)) false ->
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m2 SA [CB 56%nat (entry_bytes e1)] /\
  entry_okw L2 A2 m2 e1 /\
  src_dl L2 A2 m2 (hdrop h1 rs0 jk) o /\
  others_at Bm m2 j (re_fd e) fs os /\
  DGLB D m2 /\
  DOUT s L2 A2 m2 OUT1 junk1 LB1.
Proof using EHI GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s L1 A1 m1 L2 A2 m2 e1 h1 OUT1 junk1 LB1 D r0 rs0 jk Pa o MS HR HPI HPB HPF HK FR1 SAC1 EK1 SR1 OT1 HNO HLB
    BK1 GL1 OU1 ERR2 OC LT.
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof BK1 as (ND & GI1 & _).
  apply NoDup_ListNoDup in ND.
  assert (R0P : In (fst r0) (list_blocks (hs_pending h1)))
    by (unfold list_blocks; apply in_or_app; right; rewrite HR; left; reflexivity).
  assert (NX : forall q, In q (G :: OUT1 :: entry_blocks e1) -> ~ In q (list_blocks (hs_pending h1))).
  { intros q Hq X. exact (rbl_nd_disj (G :: OUT1 :: entry_blocks e1) (hs_blocks h1) q ND Hq (hb_pend h1 q X)). }
  assert (NXr : forall q, In q (G :: OUT1 :: entry_blocks e1) -> q <> fst r0).
  { intros q Hq X. subst q. exact (NX _ Hq R0P). }
  assert (GX : ~ In G (list_blocks (hs_pending h1))) by (apply NX; left; reflexivity).
  assert (OX : ~ In OUT1 (list_blocks (hs_pending h1))) by (apply NX; right; left; reflexivity).
  assert (OXr : OUT1 <> fst r0) by (apply NXr; right; left; reflexivity).
  assert (EX : forall q, In q (entry_blocks e1) -> ~ In q (list_blocks (hs_pending h1)))
    by (intros q Hq; apply NX; right; right; exact Hq).
  assert (EXr : forall q, In q (entry_blocks e1) -> q <> fst r0) by (intros q Hq; apply NXr; right; right; exact Hq).
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FRc |].
    intros a Ha. apply HPF. cbn [cells_size csize app dr_saved] in Ha. clear - Ha. lia. }
  split.
  { eapply rw_tr; [exact MS | exact SAC1 |]. intros a Ha. apply (HPB G SRC_TABLE a GI1 GX).
    cbn [cells_size csize] in Ha. unfold SRC_TABLE, SRC_ENTRY. clear - Ha F6 F7. lia. }
  split.
  { eapply entry_okw_tr; [exact MS | exact EK1 | |].
    - intros q k Hq Hb. exact (HK q k Hq (EXr q Hb)).
    - intros q k a Hq Hb Ha. exact (HPB q k a Hq (EX q Hb) Ha). }
  split.
  { eapply UI_src_dl_tr; [exact MS | exact SR1 | exact HR | | | | exact OC | exact LT].
    - intros a Ha Hn. apply HPI; [apply GRP|]; [clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
      exact Hn.
    - intros q k Hq _ Hn. exact (HK q k Hq Hn).
    - intros q k a Hq Hn Ha. exact (HPB q k a Hq Hn Ha). }
  split.
  { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi Hij Ha.
    assert (NE : Z.of_nat i <> Z.of_nat j) by (intros X; apply Hij; apply Nat2Z.inj; exact X).
    apply HPI; [apply GRP|]; clear - Ha Hi NE F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
  split.
  { destruct GL1 as (GC1 & GC2 & GC3 & GC4 & _).
    split; [eapply rw_tr; [exact MS | exact GC1 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GCP|]; clear - Ha F11; unfold G_CLIENT, G_S, SRC_SIZE in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC2 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GRP|]; clear - Ha F11; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC3 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GRP|]; clear - Ha F11; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI; [apply GRP|]; clear - Ha F11; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    exact ERR2. }
  destruct OU1 as (OFa & OTa). split.
  - intros LV. destruct (OFa LV) as (OC' & OE & OCP & OB). split.
    + eapply rw_tr; [exact MS | exact OC' |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + split; [exact OE|]. split; [exact OCP|]. intros Cq. destruct (OB Cq) as (OI & OBy).
      pose proof OX as OX'. rewrite OE in OX'. pose proof OXr as OXr'. rewrite OE in OXr'.
      split; [exact (HK _ _ OI OXr')|].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB OUT CAP a OI OX').
      destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; [clear - Cq C0; lia|].
      rewrite length_app in Ha. clear - Ha LO LJ. lia.
  - intros LV. destruct (OTa LV) as (OC' & OZ). split.
    + eapply rw_tr; [exact MS | exact OC' |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + destruct OZ as [OZ|(Pp & NL & OI & OFr & OBy & LJ)]; [left; exact OZ | right].
      split; [exact Pp|]. split; [exact NL|]. split; [exact (HK _ _ OI OXr)|]. split; [exact OFr|].
      split; [|exact LJ].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB OUT1 (ds_ocap s) a OI OX).
      assert (LO : Z.of_nat (length O) = NO).
      { destruct OUTD as [(_ & _ & N0 & OE0)|(_ & _ & _ & _ & _ & LO & _)];
          [rewrite OE0; cbn [length]; clear - N0; lia | exact LO]. }
      assert (LLB : Z.of_nat (length LB1) = dtot D).
      { unfold dtot. rewrite <- HLB. unfold bzs. rewrite length_map. reflexivity. }
      rewrite !length_app in Ha. clear - Ha LO LLB HNO LJ. lia.
Qed.

Lemma UI_src_dl_off : forall L1 A1 m1 m2 h1 o off' Pa, msame Pa m1 m2 -> src_dl L1 A1 m1 h1 o ->
  (forall a, (HA <= a < HA + 32 \/ HA + 40 <= a < HA + 96) -> Pa a) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (hs_blocks h1) -> q <= a < q + k -> Pa a) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 off')] ->
  ((hl_recs (hs_pending h1) = [] /\ off' = 0) \/
   (exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= off' < Z.of_nat (length (snd r)))) ->
  src_at Bm L1 A1 m2 HA (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) off' (hs_partial h1)
                           (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)).
Proof using G HJ O SEGS h junk regs.
  intros L1 A1 m1 m2 h1 o off' Pa MS
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18) HC HB C8' OF.
  assert (S7r : rw_cells rsegs m1 (HA + 32)
                  [C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1));
                   C4 (Z_to_bv 64 (hs_overlong h1))]) by (rewrite <- SEGS; exact S7).
  destruct (dr_cut m1 (HA + 32) (HA + 32 + 8) [C8 (Z_to_bv 64 o)]
              [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]
              S7r eq_refl) as [_ S7b].
  assert (S7c : rw_cells segs m2 (HA + 32 + 8)
                  [C8 (Z_to_bv 64 (hs_partial h1)); C8 (Z_to_bv 64 (hs_npartial h1)); C4 (Z_to_bv 64 (hs_overlong h1))]).
  { eapply rw_tr; [exact MS | rewrite SEGS; exact S7b |]. intros a Ha. apply HC. right.
    cbn [cells_size csize] in Ha. clear - Ha. lia. }
  unfold src_at.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_expected
       hs_held].
  split; [eapply rw_tr; [exact MS | exact S1 | intros a Ha; apply HC; left; cbn [cells_size csize] in Ha; clear - Ha; lia]|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split.
  { eapply list_at_tr; [exact MS | exact S6 | intros a Ha; apply HC; left; clear - Ha; lia | intros q k Hq _; exact Hq |].
    intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_pend h1 q Hl) Ha). }
  split.
  { rewrite SEGS in C8', S7c |- *.
    exact (dr_join m2 (HA + 32) (HA + 32 + 8) _ _ C8' S7c eq_refl). }
  split; [exact OF|].
  split; [exact S9|]. split; [exact S10|]. split; [exact S11|]. split; [exact S12|]. split; [exact S13|].
  split.
  { eapply rw_tr; [exact MS | exact S14 |]. intros a Ha. apply (HB _ _ a S11 (hb_part h1)).
    cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. clear - Ha. lia. }
  split; [exact S15|].
  split.
  { eapply list_at_tr; [exact MS | exact S16 | intros a Ha; apply HC; right; clear - Ha; lia | intros q k Hq _; exact Hq |].
    intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_exp h1 q Hl) Ha). }
  split.
  { eapply list_at_tr; [exact MS | exact S17 | intros a Ha; apply HC; right; clear - Ha; lia | intros q k Hq _; exact Hq |].
    intros q k a Hq Hl Ha. exact (HB q k a Hq (hb_held h1 q Hl) Ha). }
  exact S18.
Qed.

Lemma UI_rtd_bundle : forall s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D W o off' used' U' J',
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  rw_cells segs m1 SA [CB 56%nat (entry_bytes e1)] ->
  entry_okw L1 A1 m1 e1 -> src_dl L1 A1 m1 h1 o -> others_at Bm m1 j (re_fd e) fs os ->
  ds_no s = NO + dtot D -> bzs LB1 = with_nul (lines ST0 D) ->
  DBLK L1 A1 e1 h1 OUT1 -> DGLB D m1 -> DOUT s L1 A1 m1 OUT1 junk1 LB1 ->
  munch W m1 m2 -> wmono segs m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 32 <= a < HA + 40) -> ~ (SA + 24 <= a < SA + 32) -> outside W a) ->
  rw_cells segs m2 (HA + 32) [C8 (Z_to_bv 64 off')] ->
  rw_cells segs m2 (SA + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 used')] ->
  ((hl_recs (hs_pending h1) = [] /\ off' = 0) \/
   (exists r rs, hl_recs (hs_pending h1) = r :: rs /\ 0 <= off' < Z.of_nat (length (snd r)))) ->
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m2 md1 /\
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  rw_cells segs m2 SA [CB 56%nat (entry_bytes (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) used'
                                                  (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1) U' J'))] /\
  entry_okw L1 A1 m2 e1 /\
  src_at Bm L1 A1 m2 HA (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) off' (hs_partial h1)
                           (hs_pjunk h1) (hs_npartial h1) (hs_overlong h1) (hs_pad h1) (hs_expected h1) (hs_held h1)) /\
  others_at Bm m2 j (re_fd e) fs os /\
  DGLB D m2 /\
  DOUT s L1 A1 m2 OUT1 junk1 LB1.
Proof using AX BW EHI EU GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s L1 A1 m1 md1 m2 e1 h1 OUT1 junk1 LB1 D W o off' used' U' J' RP1 FR1 SAC1 EK1 SR1 OT1 HNO HLB BK1 GL1 OU1 MU
    WM HW HC2 HB2 OF.
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  pose proof EK1 as (_ & _ & K3 & K4 & _).
  pose proof BK1 as (ND & GI1 & _).
  pose proof (blk_rng _ _ _ _ _ _ M1 GI1) as GR1. unfold SRC_TABLE, SRC_ENTRY in GR1.
  pose proof (rbl_apart _ _ _ _ _ _ M1 GI1 ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)) as GA.
  unfold SRC_TABLE, SRC_ENTRY in GA.
  pose proof (msame_munch _ _ _ MU WM) as MS.
  apply NoDup_ListNoDup in ND. apply List.NoDup_cons_iff in ND as [NG _].
  assert (SNI : forall a, in_img Bm a -> ~ (SA + 24 <= a < SA + 32)).
  { intros a Ha X. apply (blk_noimg _ _ _ _ _ _ (a - G) M1 GI1); [unfold SRC_TABLE, SRC_ENTRY; clear - X F6 F7; lia|].
    replace (G + (a - G)) with a by ring. exact Ha. }
  assert (HPI0 : forall a, img_plain Bm a -> ~ (HA + 32 <= a < HA + 40) -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a (Ha & _) Hn. pose proof (img_lo a Ha) as IL. split; [clear - IL; lia|].
    apply HW; [clear - IL; lia | exact Hn | exact (SNI a Ha)]. }
  assert (HPB0 : forall q k a, In (q, k) (blocks L1 A1) -> q <> G -> q <= a < q + k -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros q k a Hq Hn Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (rbl_apart _ _ _ _ _ _ M1 Hq ltac:(clear - Ha; lia)) as QA.
    split; [clear - QR Ha F4; lia|]. apply HW; [clear - QR Ha F4; lia | |].
    - clear - QA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq GI1 Hn) as [X|X];
        clear - X Ha F6 F7; unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  assert (HPG : forall a, G <= a < G + 896 -> ~ (SA + 24 <= a < SA + 32) -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ha Hn. split; [clear - Ha GR1 F4; lia|]. apply HW; [clear - Ha GR1 F4; lia | | exact Hn].
    clear - GA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
  assert (HPF : forall a, S0 - 144 <= a < S0 -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ha. split; [clear - Ha F1 F2 F3; lia|].
    apply HW; [clear - Ha F1 F2 F3; lia | clear - Ha F1 F3 F11; unfold G_S, SRC_SIZE in *; lia |
               clear - Ha GR1 F1 F7; lia]. }
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU); [exact WM | exact GEI |].
    intros a Ha. destruct (rbl_rng a (HA + 32) (HA + 40)) as [D1|D1].
    - right; right; left. split; [apply GRP; clear - D1 F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
      right; right; left. clear - D1. unfold SRC_SIZE in *. lia.
    - destruct (rbl_rng a (SA + 24) (SA + 32)) as [D2|D2]; [|left; exact (HW a Ha D1 D2)].
      right; right; right; right. split; [intros X; exact (SNI a X D2)|].
      split; [exists G, SRC_TABLE; split; [exact GI1 | clear - D2 F6 F7; unfold SRC_TABLE, SRC_ENTRY in *; lia]|].
      intros p n i Hp Hp1 NF Hi NE Ea. apply NE. rewrite Ea. right; left. clear - D2. unfold SRC_ENTRY in *. lia. }
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FRc |].
    intros a Ha. apply HPF. cbn [cells_size csize app dr_saved] in Ha. clear - Ha. lia. }
  split.
  { assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
    destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
    destruct (dr_cut m1 (SA + 16) (SA + 16 + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]
                [C8 (Z_to_bv 64 (re_cap e1))] EC2 eq_refl) as [_ EC2b].
    assert (X1 : rw_cells segs m2 SA [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1));
                                      C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact EC1 |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPG; clear - Ha F6 F7; lia. }
    assert (X2 : rw_cells segs m2 (SA + 16 + 16) [C8 (Z_to_bv 64 (re_cap e1))]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact EC2b |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPG; clear - Ha F6 F7; lia. }
    assert (X3 : rw_cells segs m2 (SA + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1));
                                             CB 4 (re_pad2 e1)]).
    { eapply rw_tr; [exact MS | rewrite SEGS; exact EC3 |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPG; clear - Ha F6 F7; lia. }
    rewrite SEGS in X1, X2, X3, HB2 |- *.
    apply ent_join; [exact K3 | exact K4 | exact X1 | | exact X3].
    exact (dr_join m2 (SA + 16) (SA + 16 + 16) _ _ HB2 X2 eq_refl). }
  split.
  { eapply entry_okw_tr; [exact MS | exact EK1 | intros q k Hq _; exact Hq |].
    intros q k a Hq Hb Ha. apply (HPB0 q k a Hq); [|exact Ha]. intros X. apply NG. right. apply in_or_app. left.
    rewrite <- X. exact Hb. }
  split.
  { apply (UI_src_dl_off L1 A1 m1 m2 h1 o off' _ MS SR1); [| | exact HC2 | exact OF].
    - intros a Ha. apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    - intros q k a Hq Hb Ha. apply (HPB0 q k a Hq); [|exact Ha]. intros X. apply NG. right. apply in_or_app. right.
      rewrite <- X. exact Hb. }
  split.
  { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi Hij Ha.
    assert (NE : Z.of_nat i <> Z.of_nat j) by (intros X; apply Hij; apply Nat2Z.inj; exact X).
    apply HPI0; [apply GRP|]; clear - Ha Hi NE F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia. }
  split.
  { destruct GL1 as (GC1 & GC2 & GC3 & GC4 & (ev1 & GC5)).
    split; [eapply rw_tr; [exact MS | exact GC1 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GCP|]; clear - Ha F11; unfold G_CLIENT, G_S, SRC_SIZE in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC2 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC3 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    split; [eapply rw_tr; [exact MS | exact GC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia|].
    exists ev1. eapply rw_tr; [exact MS | exact GC5 |]. intros a Ha.
    cbn [cells_size csize] in Ha. pose proof (GEI a ltac:(clear - Ha; lia)) as Hi. pose proof (img_lo a Hi) as IL.
    split; [clear - IL; lia|]. apply HW; [clear - IL; lia | | exact (SNI a Hi)].
    intros X. pose proof (GRP a ltac:(clear - X F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))
      as (_ & _ & _ & NE).
    apply NE. clear - Ha. lia. }
  destruct OU1 as (OFa & OTa). split.
  - intros LV. destruct (OFa LV) as (OC & OE & OCP & OB). split.
    + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + split; [exact OE|]. split; [exact OCP|]. intros Cq. destruct (OB Cq) as (OI & OBy).
      split; [exact OI|].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB0 OUT CAP a OI).
      * intros X. apply NG. left. rewrite OE. exact X.
      * destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; [clear - Cq C0; lia|].
        rewrite length_app in Ha. clear - Ha LO LJ. lia.
  - intros LV. destruct (OTa LV) as (OC & OZ). split.
    + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. cbn [cells_size csize] in Ha.
      apply HPI0; [apply GRP|]; clear - Ha F11; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia.
    + destruct OZ as [OZ|(Pp & NL & OI & OFr & OBy & LJ)]; [left; exact OZ | right].
      split; [exact Pp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OFr|]. split; [|exact LJ].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (HPB0 OUT1 (ds_ocap s) a OI).
      * intros X. apply NG. left. exact X.
      * assert (LO : Z.of_nat (length O) = NO).
        { destruct OUTD as [(_ & _ & N0 & OE0)|(_ & _ & _ & _ & _ & LO & _)];
            [rewrite OE0; cbn [length]; clear - N0; lia | exact LO]. }
        assert (LLB : Z.of_nat (length LB1) = dtot D).
        { unfold dtot. rewrite <- HLB. unfold bzs. rewrite length_map. reflexivity. }
        rewrite !length_app in Ha. clear - Ha LO LLB HNO LJ. lia.
Qed.

Lemma read_drop_free : forall s c, DRE s c -> dwhole s = true -> SR segs c (DRF s).
Proof using All.
  intros s c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G9 & G18 & G19 &
    G20 & G21 & G23 & G24 & G26 & G27 & SP32 & HR & KN & GR & Ee & JK & RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 &
    SR1 & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1) W.
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof err_hi as EH.
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (rbl_text L1 A1 m1 md1 h1 s r0 rs0 M1 SR1 HR L7c L8c) as (TI & TC & OFF & DH & NLE & T4 & T5).
  assert (WL : ds_off s + dnum s = Z.of_nat (length (snd r0))).
  { unfold dwhole in W. apply Z.eqb_eq in W. rewrite W, DH. unfold bzs. rewrite length_map. reflexivity. }
  assert (R0P : In (fst r0) (list_blocks (hs_pending h1)))
    by (unfold list_blocks; apply in_or_app; right; rewrite HR; left; reflexivity).
  assert (R0H : In (fst r0) (hs_blocks h1)) by (apply hb_pend; exact R0P).
  assert (PEn : ds_pend s <> []) by (rewrite <- L7c, HR; discriminate).
  assert (STR : dstrict s).
  { intros r rs Er. rewrite <- L7c, HR in Er. cbn [map] in Er. injection Er as <- _.
    unfold bzs. rewrite length_map. clear - OFF. lia. }
  pose proof S6 as (P1 & P2 & P3 & _ & _ & _).
  assert (LN : hl_n (hs_pending h1) = Z.of_nat (length rs0) + 1) by (unfold hl_n; rewrite HR; cbn [length]; clear; lia).
  destruct P3 as [(C0 & _)|(Cp & VI & _ & VJ & VC)]; [exfalso; clear - P2 C0 LN; lia|].
  assert (VP : In (hl_v (hs_pending h1)) (list_blocks (hs_pending h1))).
  { unfold list_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - Cp; lia). left. reflexivity. }
  pose proof (blk_rng _ _ _ _ _ _ M1 VI) as VR.
  pose proof (blk_align _ _ _ _ _ _ M1 VI) as VAL.
  pose proof (rbl_apart _ _ _ _ _ _ M1 VI ltac:(clear - Cp; lia)) as VA.
  pose proof P1 as P1r. rewrite SEGS in P1r.
  destruct (dr_cut m1 (HA + 16) (HA + 24) [C8 (Z_to_bv 64 (hl_v (hs_pending h1)))] _ P1r
              ltac:(cbn [cells_size csize]; clear - F11; lia)) as [PV1 _].
  assert (PVn : rw_cells rsegs (normalize rsegs m1) (XH + 144) [C8 (Z_to_bv 64 (hl_v (hs_pending h1)))]).
  { replace (XH + 144) with (HA + 16) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
    apply rbl_norm_hi; [exact RO1r | exact PV1 | clear - F11; unfold G_S, SRC_SIZE in *; lia]. }
  pose proof S7 as S7r. rewrite SEGS, L8c in S7r.
  destruct (dr_cut m1 (HA + 32) (HA + 40) [C8 (Z_to_bv 64 (ds_off s))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; lia)) as [OF1 _].
  assert (OFn : rw_cells rsegs (normalize rsegs m1) (XH + 160) [C8 (Z_to_bv 64 (ds_off s))]).
  { replace (XH + 160) with (HA + 32) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
    apply rbl_norm_hi; [exact RO1r | exact OF1 | clear - F11; unfold G_S, SRC_SIZE in *; lia]. }
  assert (TRn : rw_cells rsegs (normalize rsegs m1) (hl_v (hs_pending h1))
                  [C8 (Z_to_bv 64 (fst r0)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r0))))]).
  { apply (rbl_norm_blk L1 A1 m1 md1 m1 (hl_v (hs_pending h1)) _ (hl_v (hs_pending h1))
             (16 * hl_cap (hs_pending h1)) M1 RO1r); [| exact VI | apply Z.le_refl |
                                                      cbn [cells_size csize]; clear - Cp; lia].
    apply (cb_prefix m1 _ (Z.to_nat (16 * hl_cap (hs_pending h1))) _
             (concat (map text_rec rs0) ++ hl_junk (hs_pending h1))); [|cbn [cells_wf cell_wf]; repeat split].
    cbn [cells_bytes cbytes]. rewrite app_nil_r, <- !app_assoc.
    pose proof VC as VCr. rewrite SEGS, HR in VCr. cbn [map concat] in VCr. unfold text_rec in VCr.
    rewrite <- !app_assoc in VCr. exact VCr. }
  destruct (dr_cut (normalize rsegs m1) (hl_v (hs_pending h1)) (hl_v (hs_pending h1) + 8)
              [C8 (Z_to_bv 64 (fst r0))] _ TRn ltac:(cbn [cells_size csize]; clear; lia)) as [_ TLn].
  assert (SPn : rw_cells rsegs (normalize rsegs m1) (S0 - 144 + 32) [C8 (Z_to_bv 64 (XH + 144))]).
  { apply rbl_norm_hi; [exact RO1r | rewrite <- SEGS; exact SP32 | clear - F1 F3; lia]. }
  assert (PVD : hl_v (hs_pending h1) + 16 <= XH + 160 \/ XH + 168 <= hl_v (hs_pending h1) + 8).
  { clear - VA Cp F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
  destruct RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G19, G20. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply dr_off; [exact SPn | exact PVn | exact OFn | exact TLn | apply mem_inv_normalize | exact PVD |
                    clear - F1 F3; lia | unfold DR_TU; clear; lia | clear - VR; lia |
                    clear - VAL; Z.div_mod_to_equations; lia | exact (proj1 OFF) | clear - KN; lia |
                    clear - WL T4 T5 F4; lia | clear - T4 T5 F4; lia]. }
  intros ms (can & (s0' & [(NE & _)|(EQn & m' & x12' & -> & MU & WM & MI & HC)] & REL & ROS) & EQ);
    [exfalso; exact (NE WL)|].
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HC) as HC2.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS12.
  assert (RO2s : ro_agree segs m2) by (rewrite SEGS; exact RO2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x13b70) by rgw X2.
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (S0 - 144)) by rgw X2.
  assert (E2_4 : getr R2 4 = getr regs 4) by rgw X2.
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (XH + 144)) by rgw X2.
  assert (E2_11 : getr R2 11 = Z_to_bv 64 0) by rgw X2.
  assert (E2_19 : getr R2 19 = Z_to_bv 64 (dnum s)) by rgw X2.
  assert (E2_20 : getr R2 20 = Z_to_bv 64 XH) by rgw X2.
  assert (RT2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  clear X2.
  assert (U2 : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite E2_2. apply unsigned_lit. clear - F1 F2 F3. lia. }
  assert (RP2 : relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m2 md1).
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU2); [exact WM2s | exact GEI |].
    intros a Ha. destruct (rbl_rng a (XH + 160) (XH + 168)) as [D1|D1].
    - right; right; left.
      split; [apply GRP; clear - D1 F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia|].
      right; right; left. clear - D1 F11. unfold G_S, SRC_SIZE, DR_TU in *. lia.
    - left. cbn [outside]. split; [exact D1 | exact I]. }
  pose proof RP2 as (M2 & W2 & _).
  destruct TR1 as (tp & qd & ad & (LQ & WT1 & AOK & ROK & DL1 & DKH1) & RF1).
  pose proof DL1 as (_ & _ & (_ & SP1 & _)). rewrite HR in SP1.
  destruct (rdf_f2_cons _ r0 rs0 (da_pend ad) SP1) as (x0 & xs0 & Epd & (Hp & Ep) & _).
  set (p := resolveF qd x0) in *.
  assert (SPE : sptr_of L1 A1 (fst r0) = p)
    by exact (CF.gestures_end_b.p3b_sptr_of_eq L1 A1 p (fst r0) _ (NODUP L1 A1 m1 md1 M1) (conj Hp Ep)).
  assert (U10 : bv_unsigned (getr R2 10) = XH + 144)
    by (rewrite E2_10; apply unsigned_lit; unfold DR_TU; clear - F11; lia).
  assert (U11 : bv_unsigned (getr R2 11) = 0) by (rewrite E2_11; reflexivity).
  assert (NT : nth 0 (hl_recs (hs_pending h1)) (0, []) = r0) by (rewrite HR; reflexivity).
  pose proof LDC as LD. unfold list_drop_contract in LD.
  specialize (LD L1 A1 R2 m2 md1 (runF F qd bnd (tp ++ fst (fst (dpush s (nretF tp) ad)))) (hs_pending h1) false).
  cbv zeta in LD. rewrite U10, U11 in LD. change (Z.to_nat 0) with 0%nat in LD. rewrite NT in LD.
  unfold LIST_DROP in LD.
  eapply SR_bind.
  { apply LD; clear LD.
    - exact SEGS.
    - apply (UI_pre_ld L1 A1 m2 md1 R2 RP2 IN1 E2_2 E2_4). rewrite E2_1. exact drf_ret.
    - exact IN1.
    - exact RO2s.
    - intros a Ha. split.
      + apply GRP. clear - Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia.
      + rewrite SEGS. apply ro_hi. clear - Ha F11. unfold DR_TU in *. lia.
    - clear. unfold DR_TU. Z.div_mod_to_equations. lia.
    - replace (XH + 144) with (HA + 16) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
      eapply list_at_tr; [exact MS12 | exact S6 | | intros q k Hq _; exact Hq |].
      + intros a Ha. split; [clear - Ha F11; unfold G_S, SRC_SIZE in *; lia | cbn [outside]; split; [|exact I]].
        clear - Ha F11; unfold DR_TU, G_S, SRC_SIZE in *; lia.
      + intros q k a Hq _ Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
        pose proof (rbl_apart _ _ _ _ _ _ M1 Hq ltac:(clear - Ha; lia)) as QA.
        split; [clear - QR Ha F4; lia | cbn [outside]; split; [|exact I]].
        clear - QA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia.
    - unfold hl_n. rewrite HR. cbn [length]. clear. lia.
    - exact ROK. }
  intros c3 (L3 & A3 & R3 & m3 & md3 & l' & -> & RPf & IN3 & (qs & _ & RS3 & _) & RO3 & LT3 & HV3 & HC3 & HR3 &
    HJ3 & (b1 & b2 & EB1 & EB3)).
  rewrite E2_1.
  pose proof RPf as (M3 & _ & _ & _ & _ & _ & _ & _ & _ & RPr3 & _).
  assert (EEV : forall a, hl_v (hs_pending h1) <= a < hl_v (hs_pending h1) + 16 * hl_cap (hs_pending h1) -> EE a).
  { intros a Ha. cbv beta. right; right; right. exists (hl_v (hs_pending h)), (16 * hl_cap (hs_pending h)).
    pose proof SM1 as (_ & _ & _ & _ & _ & SMv & SMc & _).
    pose proof SRC0 as (_ & _ & _ & _ & _ & (_ & _ & P3e & _) & _).
    rewrite SMv, SMc in Ha.
    destruct P3e as [(C0e & _)|(_ & VIe & _)]; [exfalso; rewrite <- SMc in C0e; clear - C0e Cp; lia|].
    split.
    { apply in_or_app. right. apply hb_pend. unfold list_blocks. apply in_or_app. left.
      assert (CN : hl_cap (hs_pending h) <> 0) by (rewrite <- SMc; clear - Cp; lia).
      rewrite (proj2 (Z.eqb_neq _ 0) CN).
      left. reflexivity. }
    split; [exact VIe|].
    exact Ha. }
  assert (EEC : forall a, HA + 24 <= a < HA + 28 -> EE a).
  { intros a Ha. cbv beta. right; right; left. clear - Ha. unfold SRC_SIZE in *. lia. }
  assert (RPb : relay_post Bm API DRAIN_K EE FF L A regs mem md L3 A3 regs m3 md3).
  { eapply (sb_comp Bm API); try first [exact AX | exact CTX | exact EU | exact BW | exact SEGS | exact RP2 | exact RPf].
    - intros a Ha. change (spZ regs) with S0 in Ha.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. clear - Ha F1 F2. lia.
    - intros a [X|X]; [left | right; exact X]. rewrite U2 in X. change (spZ regs) with S0.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, LIST_DROP_K, LIST_DROP_FRAME,
        ALLOC_STACK in *. clear - X. lia.
    - intros a Hs _ X. cbv beta in X. destruct Hs as [Hs|Hs].
      + change (spZ regs) with S0 in Hs.
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Hs.
        destruct X as [X|X]; [clear - Hs X F1 F3 F11; unfold DR_TU in *; lia | clear - Hs X VR P2 F1; lia].
      + destruct X as [X|X]; [clear - Hs X EH F11; unfold G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia|].
        apply (blk_noimg _ _ _ _ _ _ (a - hl_v (hs_pending h1)) M1 VI); [clear - X P2; lia|].
        replace (hl_v (hs_pending h1) + (a - hl_v (hs_pending h1))) with a by ring. exact (GEI a Hs).
    - intros p' n' Hp' _ Hn NF Eq'.
      assert (INq : In (ptr_addr L p', n') (blocks L A))
        by (apply CF.gestures_end_b.blocks_In2; exists p'; split; [reflexivity | exact Hp']).
      destruct (untouched s L1 A1 m1 e1 h1 OUT1 junk1 LB1 (ptr_addr L p') n' BK1 OU1 INq Hn NF) as [_ U'].
      apply U'. rewrite Eq'. exact R0H.
    - intros a Ha _ _ X. cbv beta in X. destruct X as [X|X]; [apply EEC | apply EEV];
        clear - X P2; unfold DR_TU, G_S, SRC_SIZE in *; lia.
    - intros p' n' i Hp' Hp1 NF Hi X. cbv beta in X. destruct X as [X|X]; [apply EEC | apply EEV];
        clear - X P2; unfold DR_TU, G_S, SRC_SIZE in *; lia. }
  pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RPf) as MS23.
  pose proof (msame_trans _ _ _ _ _ MS12 MS23) as MS13.
  match type of MS23 with msame ?P _ _ =>
    assert (I23 : forall a, img_plain Bm a -> ~ (HA + 24 <= a < HA + 28) -> P a) end.
  { intros a Hp' Hn. pose proof Hp' as (Hi & _ & _ & NEr). pose proof (img_lo a Hi) as IL.
    left. split; [right; exact Hi|]. split; [exact (img_unowned _ _ _ _ a M2 Hp')|].
    split; [exact (img_unowned _ _ _ _ a M3 Hp')|]. split.
    - intros [X|X]; [rewrite U2 in X; unfold LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK in X; clear - X IL F1 F3; lia |
                     exact (NEr X)].
    - intros X. cbv beta in X. destruct X as [X|X]; [clear - X Hn F11; unfold DR_TU, G_S, SRC_SIZE in *; lia|].
      apply (blk_noimg _ _ _ _ _ _ (a - hl_v (hs_pending h1)) M1 VI); [clear - X P2; lia|].
      replace (hl_v (hs_pending h1) + (a - hl_v (hs_pending h1))) with a by ring. exact Hi. }
  match type of MS13 with msame ?P _ _ =>
    assert (I13 : forall a, img_plain Bm a -> ~ (HA + 24 <= a < HA + 28 \/ HA + 32 <= a < HA + 40) -> P a) end.
  { intros a Hp' Hn. pose proof Hp' as (Hi & _). pose proof (img_lo a Hi) as IL.
    split; [split; [clear - IL; lia | cbn [outside]; split; [clear - Hn F11; unfold DR_TU, G_S, SRC_SIZE in *; lia |
                                                              exact I]]|].
    apply I23; [exact Hp' | clear - Hn; lia]. }
  match type of MS13 with msame ?P _ _ =>
    assert (B13 : forall q k a, In (q, k) (blocks L1 A1) -> ~ In q (list_blocks (hs_pending h1)) -> q <= a < q + k ->
                    P a) end.
  { intros q k a Hq Hn Ha.
    assert (Q0 : q <> fst r0) by (intros X; apply Hn; rewrite X; exact R0P).
    assert (QV : q <> hl_v (hs_pending h1)) by (intros X; apply Hn; rewrite X; exact VP).
    pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (rbl_apart _ _ _ _ _ _ M1 Hq ltac:(clear - Ha; lia)) as QA.
    split; [split; [clear - QR Ha F4; lia | cbn [outside]; split; [|exact I]]|].
    { clear - QA Ha F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia. }
    right. exists q, k. split; [exact Hq|]. split; [clear - Ha; lia|]. split; [exact Q0|]. split; [exact Ha|].
    intros X. cbv beta in X. destruct X as [X|X].
    - clear - QA Ha X F11. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *. lia.
    - destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq VI QV) as [D'|D']; clear - D' Ha X P2; lia. }
  match type of MS13 with msame ?P _ _ => assert (F13 : forall a, S0 - 144 <= a < S0 -> P a) end.
  { intros a Ha. split; [split; [clear - Ha F1 F2 F3; lia | cbn [outside]; split; [|exact I]]|].
    { clear - Ha F1 F3 F11. unfold DR_TU in *. lia. }
    left. split; [left; clear - Ha F1 F2 F3; lia|].
    split; [intros X; pose proof (owned_lo2 _ _ _ _ a M2 X) as Y; clear - Ha F1 Y; lia|].
    split; [intros X; pose proof (owned_lo2 _ _ _ _ a M3 X) as Y; clear - Ha F1 Y; lia|].
    split.
    - intros [X|X]; [rewrite U2 in X; clear - X Ha; lia|].
      pose proof (img_lo a (GEI a X)) as Y. clear - Ha F1 F3 Y. lia.
    - intros X. cbv beta in X. destruct X as [X|X];
        [clear - X Ha F1 F3 F11; unfold DR_TU in *; lia | clear - X Ha VR P2 F1; lia]. }
  assert (OC3 : rw_cells segs m3 (HA + 32) [C8 (Z_to_bv 64 (ds_off s + dnum s))]).
  { replace (HA + 32) with (XH + 160) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
    eapply rw_tr; [exact MS23 | rewrite SEGS; exact HC2 |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply I23; [apply GRP; clear - Ha F11; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX, DR_TU in *; lia|].
    clear - Ha F11. unfold DR_TU, G_S, SRC_SIZE in *. lia. }
  assert (ERR3 : exists ev, rw_cells segs m3 ERR [C4 ev]).
  { pose proof RPb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC3).
    pose proof (img_lo ERR (GEI ERR ltac:(clear - F10; lia))) as EL.
    rewrite SEGS. apply sb_c4; [clear - EL; lia | clear - F10; lia |].
    intros i Hi. rewrite <- SEGS. apply SC3. right. clear - Hi. lia. }
  destruct (drf_dblk L1 A1 m1 md1 L3 A3 e1 h1 OUT1 r0 rs0 b1 b2 M1 BK1 HR EB1 EB3) as (BK3 & GONE & KEEP).
  assert (LE : l' = hs_pending (hdropl h1 rs0)).
  { destruct l' as [v' c' rs' jk']. cbn [hl_v hl_cap hl_recs hl_junk] in HV3, HC3, HR3, HJ3.
    rewrite HR in HR3. cbn [firstn skipn app] in HR3. subst v' c' rs' jk'. reflexivity. }
  rewrite LE in LT3.
  assert (LT3' : list_at Bm L3 A3 m3 (HA + 16) (hs_pending (hdropl h1 rs0)) false).
  { replace (HA + 16) with (XH + 144) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia). exact LT3. }
  destruct (UI_drf_bundle s L1 A1 m1 L3 A3 m3 e1 h1 OUT1 junk1 LB1 D r0 rs0
              (text_rec (last (hl_recs (hs_pending h1)) (0, [])) ++ hl_junk (hs_pending h1)) _ (ds_off s + dnum s)
              MS13 HR I13 B13 F13 KEEP FR1 SAC1 EK1 SR1 OT1 H7h H8h BK1 GL1 OU1 ERR3 OC3 LT3')
    as (FR3 & SAC3 & EK3 & SR3 & OT3 & GL3 & OU3).
  assert (MT : MTR s L3 A3 (ds_ocap s) e1 (hdropl h1 rs0) OUT1
                 (lrest (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (drl s))).
  { assert (DHl : length (dhead s) = length (snd r0)) by (rewrite DH; unfold bzs; apply length_map).
    assert (DD : ddrop s ad = [RFree (Z.of_nat (length (snd r0)) + 1) x0]).
    { unfold ddrop. rewrite W, Epd. unfold list_drop_tra. rewrite DHl. reflexivity. }
    pose proof AOK as (AO1 & AO2 & AO3 & AO4 & AO5 & AO6 & AO7). cbn [da_pend apush] in AO5. rewrite Epd in AO5.
    pose proof BK1 as (NDb & _).
    exists ((tp ++ fst (fst (dpush s (nretF tp) ad))) ++ ddrop s ad), qd,
      (DA (da_out ad) (da_buf ad) (da_hp ad) (da_keys ad) (skipn 1 (da_pend ad)) (fst (snd (dpush s (nretF tp) ad)))
          (snd (snd (dpush s (nretF tp) ad)))).
    split; [|exact (rdf_fut s tp ad Ee PEn STR GR W RF1)].
    rewrite DD.
    split; [rewrite rdf_nret; exact LQ|].
    split; [exact (p3a_wf_snoc _ (RFree _ x0) WT1 (Forall_inv AO5))|].
    split.
    { rewrite rdf_nret, Epd. cbn [skipn].
      split; [exact AO1|]. split; [exact AO2|]. split; [exact AO3|]. split; [exact AO4|].
      split; [exact (Forall_inv_tail AO5)|]. split; [exact AO6 | exact AO7]. }
    split.
    { rewrite rdf_runF_free.
      assert (LDT : list_drop_tr (sh_of (known_at L1 A1) (hs_pending h1)) 0 =
                    [RFree (Z.of_nat (length (snd r0)) + 1) (Known p)]).
      { unfold list_drop_tr, sh_of, rec_drop_tr, rec_len, shr, known_at. cbn [sh_recs]. rewrite HR.
        cbn [map nth fst snd]. unfold bzs. rewrite length_map, SPE. reflexivity. }
      rewrite LDT in RS3. exact RS3. }
    split; [|exact DKH1].
    exact (UI_links _ _ _ L1 A1 R2 m2 md1 L3 A3 R3 m3 md3 qd (apush ad (snd (dpush s (nretF tp) ad))) (ds_ocap s) e1
             h1 OUT1 r0 rs0 (text_rec (last (hl_recs (hs_pending h1)) (0, [])) ++ hl_junk (hs_pending h1)) W2 RPf
             (fun q Hq => UI_nin e1 h1 OUT1 r0 rs0 _ NDb HR q Hq) HR DL1). }
  pose proof (rbl_rtl R2 R3 RT2 RPr3) as RT3.
  assert (Q19 : getr R3 19 = Z_to_bv 64 (dnum s))
    by (transitivity (getr R2 19); [exact (RPr3 19 ltac:(unfold callee_saved; clear; lia)) | exact E2_19]).
  assert (Q20 : getr R3 20 = Z_to_bv 64 XH)
    by (transitivity (getr R2 20); [exact (RPr3 20 ltac:(unfold callee_saved; clear; lia)) | exact E2_20]).
  apply SR_ret. exists R3, L3, A3, m3, md3, e1, h1, OUT1, junk1, LB1, D, r0, rs0.
  split; [reflexivity|]. split; [exact RT3|]. split; [exact Q19|]. split; [exact Q20|].
  split; [exact HR|]. split; [exact KN|]. split; [exact GR|]. split; [exact Ee|]. split; [exact W|].
  split; [exact JK|]. split; [exact RPb|]. split; [exact IN3|]. split; [exact MT|]. split; [exact RO3|].
  split; [exact FR3|]. split; [exact SAC3|]. split; [exact EK3|]. split; [exact SR3|]. split; [exact GONE|].
  split; [exact OT3|]. split; [exact SM1|]. split; [exact LK1|]. split; [exact HI1|]. split; [exact BK3|].
  split; [exact GL3 | exact OU3].
Qed.

Lemma rtd_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof using Bm G HJ O h junk regs.
  induction rs as [|r rs IH]; cbn [map concat length]; [reflexivity|].
  rewrite length_app, IH. unfold text_rec. rewrite length_app, !length_le8. clear IH. lia.
Qed.

Lemma rtd_mm : forall (r0 : Z * list byte) rs0 jk,
  mm_result (concat (map text_rec (r0 :: rs0)) ++ jk) 16 0 (16 * length rs0) =
  concat (map text_rec rs0) ++ skipn (16 * length rs0) (concat (map text_rec (r0 :: rs0)) ++ jk).
Proof using Bm G HJ O h junk regs.
  intros r0 rs0 jk. set (C := concat (map text_rec rs0)).
  assert (LC : length C = (16 * length rs0)%nat) by apply rtd_len.
  assert (LT : length (text_rec r0) = 16%nat) by (unfold text_rec; rewrite length_app, !length_le8; reflexivity).
  assert (E : skipn 16 (concat (map text_rec (r0 :: rs0)) ++ jk) = C ++ jk).
  { cbn [map concat]. rewrite <- app_assoc, <- LT, skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (FE : firstn (16 * length rs0) (C ++ jk) = C).
  { rewrite <- LC, firstn_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all. }
  unfold mm_result, slice, upd_bytes. rewrite E, FE, LC. reflexivity.
Qed.

Lemma rtd_mm_len : forall us (k : nat), (16 + k <= length us)%nat -> length (mm_result us 16 0 k) = length us.
Proof using HG HJ O h junk.
  intros us k H. unfold mm_result, slice, upd_bytes.
  rewrite !length_app, !length_firstn, !length_skipn. lia.
Qed.

Lemma rtd_dv : forall s, dwhole s = true ->
  dvirt s (ds_skip s) (ds_H s) (ds_ka s) (ds_no s) (ds_ocap s) =
  DS (ds_cap s) (dW s) (ds_skip s) (ds_H s) (ds_ka s) false (dtail s) 0 (feed (ds_ref s) (ddata s))
     (ds_en s + Z.of_nat (length (dref s))) (pcapm (ds_en s) (ds_ecap s) (dref s))
     (ds_no s) (ds_ocap s).
Proof using. intros s W. unfold dvirt, dnext. rewrite W. reflexivity. Qed.

Lemma rtd_ps : forall s, dwhole s = true -> prest (dtail s) 0 = prest (ds_pend s) (ds_off s + dnum s).
Proof using.
  intros s W. unfold dwhole, dhead in W. apply Z.eqb_eq in W. unfold dtail.
  revert W. destruct (ds_pend s) as [|r rs]; intros W; cbn [prest] in W |- *; [reflexivity|].
  rewrite W, Nat2Z.id, skipn_all. destruct rs as [|r1 rs]; reflexivity.
Qed.

Lemma rtd_hb : forall h1 (r0 : Z * list byte) rs0 jk, hl_recs (hs_pending h1) = r0 :: rs0 ->
  (forall q, In q (hs_blocks (hdrop h1 rs0 jk)) -> In q (hs_blocks h1)) /\
  (forall q, In q (hs_blocks h1) -> q <> fst r0 -> In q (hs_blocks (hdrop h1 rs0 jk))) /\
  (forall pre, List.NoDup (pre ++ hs_blocks h1) -> List.NoDup (pre ++ hs_blocks (hdrop h1 rs0 jk))).
Proof using.
  intros h1 r0 rs0 jk HR.
  assert (E1 : hs_blocks h1 = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
                 fst r0 :: (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
  { unfold hs_blocks, list_blocks at 1. rewrite HR. cbn [map]. rewrite <- !app_assoc. reflexivity. }
  assert (E2 : hs_blocks (hdrop h1 rs0 jk) = (if hl_cap (hs_pending h1) =? 0 then [] else [hl_v (hs_pending h1)]) ++
                 (map fst rs0 ++ [hs_partial h1] ++ list_blocks (hs_expected h1) ++ list_blocks (hs_held h1))).
  { unfold hs_blocks, hdrop, list_blocks at 1. cbn [hs_pending hs_partial hs_expected hs_held hl_v hl_cap hl_recs].
    rewrite <- !app_assoc. reflexivity. }
  rewrite E1, E2. split; [|split].
  - intros q Hq. apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq].
  - intros q Hq Hn. apply in_app_or in Hq as [Hq|[Hq|Hq]]; apply in_or_app;
      [left; exact Hq | exfalso; exact (Hn (eq_sym Hq)) | right; exact Hq].
  - intros pre ND. rewrite app_assoc in ND |- *. exact (List.NoDup_remove_1 _ _ _ ND).
Qed.

Lemma rtd_dblk : forall L1 A1 e1 h1 OUT1 (r0 : Z * list byte) rs0 jk,
  DBLK L1 A1 e1 h1 OUT1 -> hl_recs (hs_pending h1) = r0 :: rs0 -> (forall k, ~ In (fst r0, k) (blocks L1 A1)) ->
  DBLK L1 A1 e1 (hdrop h1 rs0 jk) OUT1.
Proof using.
  intros L1 A1 e1 h1 OUT1 r0 rs0 jk (ND & GI & B3 & B4 & B5) HR GONE.
  destruct (rtd_hb h1 r0 rs0 jk HR) as (HB1 & HB2 & HB3).
  split; [apply NoDup_ListNoDup; apply NoDup_ListNoDup in ND; exact (HB3 (G :: OUT1 :: entry_blocks e1) ND)|].
  split; [exact GI|]. split; [exact B3|].
  split.
  { intros q m Hq. destruct (B4 q m Hq) as [X|[X|X]]; [left; exact X | right; left | right; right; exact X].
    apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right].
    apply HB2; [exact X|]. intros Eq. subst q. exact (GONE m Hq). }
  intros q m Hq Hm Ho Hn. destruct (B5 q m Hq Hm Ho Hn) as (X1 & X2 & X3).
  split; [exact X1|]. split; [exact X2|]. intros X. exact (X3 (HB1 q X)).
Qed.

Lemma read_tail_drop : forall s c, DRE s c -> dwhole s = true -> SR segs c (DHQ s).
Proof using All.
  intros s c H W. eapply SR_bind; [exact (read_drop_free s c H W)|]. clear c H.
  intros c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & r0 & rs0 & -> & RT1 & G19 & G20 & HR & NP &
    GR & E & _ & JK & RP1 & IN1 & MT1 & RO1 & FR1 & SAC1 & EK1 & SR1 & GONE & OT1 & SM1 & LK1 & HI1 & BK1 & GL1 & OU1).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1h & H2h & H3h & H4h & H5h & H6h & H7h & H8h & H9h & H10h & H11h & H12h).
  pose proof H3h as (_ & _ & _ & NZU).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  pose proof BK1 as (NDb & GI1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  rewrite E in L6c. cbv beta iota in L6c.
  assert (PE : ds_pend s = bzs (snd r0) :: map (fun r => bzs (snd r)) rs0) by (rewrite <- L7c, HR; reflexivity).
  assert (PNE : ds_pend s <> []) by (rewrite PE; discriminate).
  assert (LH : Z.of_nat (length (dhead s)) = Z.of_nat (length (snd r0))).
  { unfold dhead. rewrite PE. unfold bzs. rewrite length_map. reflexivity. }
  assert (WL : ds_off s + dnum s = Z.of_nat (length (snd r0))).
  { unfold dwhole in W. apply Z.eqb_eq in W. rewrite W. exact LH. }
  assert (STR : dstrict s).
  { intros r rs Er. rewrite PE in Er. injection Er as <- _. unfold bzs. rewrite length_map. clear - WL NP. lia. }
  assert (ULEN : ulen s = re_used e1) by (unfold ulen; rewrite <- L2c; unfold bzs; rewrite length_map; exact K7).
  assert (GR' : 4096 <= re_cap e1 - re_used e1) by (rewrite L1c, <- ULEN; exact GR).
  assert (NR : dnum s <= re_cap e1 - re_used e1).
  { unfold dnum. rewrite <- L1c, ULEN. clear; lia. }
  assert (BUF : 0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (blocks L1 A1)).
  { destruct K10 as [(C0 & _ & U0)|(Cp & BI & _)]; [clear - C0 U0 GR'; lia | split; [exact Cp | exact BI]]. }
  destruct BUF as (Cp & BI).
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  pose proof SR1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & _).
  pose proof S7 as S7r. rewrite SEGS in S7r.
  destruct (dr_cut m1 (HA + 32) (HA + 40) [C8 (Z_to_bv 64 (ds_off s + dnum s))] _ S7r
              ltac:(cbn [cells_size csize]; clear - F11; lia)) as [OC1 _].
  assert (OCn : rw_cells rsegs (normalize rsegs m1) (XH + 160) [C8 (Z_to_bv 64 (ds_off s + dnum s))]).
  { replace (XH + 160) with (HA + 32) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
    apply rbl_norm_hi; [exact RO1r | exact OC1 | clear - F11; unfold G_S, SRC_SIZE in *; lia]. }
  destruct RT1 as (((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26) & G27).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G20. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO1r |].
    eapply dr_dropn; [exact OCn | apply mem_inv_normalize]. }
  intros ms (can & (s0' & (m' & -> & MU & WM & _ & HX) & REL & ROS) & EQ).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2]. rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can) in *.
  pose proof (sb_back m1 m' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m' _ _ REL2 HX) as HX2.
  assert (RT2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  assert (E2_19 : getr R2 19 = Z_to_bv 64 (dnum s)) by rgw X2.
  assert (E2_20 : getr R2 20 = Z_to_bv 64 XH) by rgw X2.
  clear X2.
  assert (WM2s : wmono segs m1 m2) by (rewrite SEGS; exact WM2).
  pose proof (msame_munch _ _ _ MU2 WM2s) as MS12.
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (_ & EC2 & _).
  destruct (dr_cut m1 (SA + 16) (SA + 16 + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]
              [C8 (Z_to_bv 64 (re_cap e1))] EC2 eq_refl) as [EC2a _].
  assert (EC2m : rw_cells rsegs m2 (SA + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]).
  { rewrite <- SEGS. eapply rw_tr; [exact MS12 | rewrite SEGS; exact EC2a |]. intros a Ha. cbn [cells_size csize] in Ha.
    pose proof (g_noimg a ltac:(clear - Ha; lia)) as NI. split; [clear - Ha F4 F5 F6 F7 F8; lia|]. cbn [outside].
    split; [intros R; apply NI, grp_img; unfold DR_TU, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia | exact I]. }
  assert (HSc : rw_cells rsegs (normalize rsegs m2) (SA + 16)
                  [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))])
    by (apply (rbl_norm_blk _ _ _ _ _ _ _ _ _ M1 RO2 EC2m GI1);
        [clear - F6; lia | cbn [cells_size csize]; clear - F7; unfold SRC_TABLE, SRC_ENTRY in *; lia]).
  destruct RT2 as (((Y2 & Y3 & Y4 & Y8 & Y22 & Y25) & Y23 & Y26) & Y27).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y8, E2_19. rewrite SEGS.
    eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact RO2 |].
    eapply dr_add; [exact HSc | apply mem_inv_normalize | | | | ].
    - split; [clear - NP; lia | clear - NR K6 K7; lia].
    - clear - K7. lia.
    - clear - NR K6 K7. lia.
    - clear - BR F4 Cp. lia. }
  intros ms (can' & (s1' & [(N0 & _)|(NPp & m'' & -> & MU' & WM' & _ & HB)] & REL' & ROS') & EQ');
    [exfalso; clear - N0 NP; lia|].
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL') as [ECAN' REL3]. rewrite ECAN' in EQ'.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ' eq_refl eq_refl) as (R3 & -> & X3).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m3 := ms_mem can') in *.
  pose proof (sb_back m2 m'' m3 _ RO2 REL3 ROS' MU' WM') as (MU3 & WM3 & RO3).
  pose proof (rw_cells_of_rel rsegs m3 m'' _ _ REL3 HB) as HB3.
  assert (WM3s : wmono segs m2 m3) by (rewrite SEGS; exact WM3).
  assert (MU13 : munch [(XH + 160, XH + 168); (SA + 24, SA + 32)] m1 m3).
  { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
    rewrite (MU3 x (conj Hx2 I)). exact (MU2 x (conj Hx1 I)). }
  assert (WM13 : wmono segs m1 m3) by (eapply wmono_trans; [exact WM2s | exact WM3s]).
  assert (HC3 : rw_cells segs m3 (HA + 32) [C8 (Z_to_bv 64 0)]).
  { replace (HA + 32) with (XH + 160) by (clear - F11; unfold DR_TU, G_S, SRC_SIZE in *; lia).
    eapply rw_tr; [exact (msame_munch _ _ _ MU3 WM3s) | rewrite SEGS; exact HX2 |].
    intros a Ha. cbn [cells_size csize] in Ha. split; [clear - Ha F11; unfold DR_TU in *; lia|].
    cbn [outside]. split; [|exact I]. intros X.
    apply (g_noimg a ltac:(clear - X; lia)). apply grp_img. clear - Ha F11.
    unfold DR_TU, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
  assert (HB3s : rw_cells segs m3 (SA + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1 + dnum s))])
    by (rewrite SEGS; exact HB3).
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 32 <= a < HA + 40) -> ~ (SA + 24 <= a < SA + 32) ->
                 outside [(XH + 160, XH + 168); (SA + 24, SA + 32)] a).
  { intros a _ D1 D2. cbn [outside]. split; [clear - D1 F11; unfold DR_TU, G_S, SRC_SIZE in *; lia|].
    split; [exact D2 | exact I]. }
  assert (OF : (hl_recs (hs_pending (hdropl h1 rs0)) = [] /\ 0 = 0) \/
               (exists r rs, hl_recs (hs_pending (hdropl h1 rs0)) = r :: rs /\ 0 <= 0 < Z.of_nat (length (snd r)))).
  { pose proof S6 as (_ & _ & _ & _ & _ & S6f). unfold hdropl, hdrop in S6f |- *. cbn [hs_pending hl_recs] in S6f |- *.
    destruct rs0 as [|r1 rs1]; [left; split; reflexivity | right].
    exists r1, rs1. split; [reflexivity|].
    destruct (Forall_inv S6f) as (_ & _ & _ & _ & L1r). specialize (L1r eq_refl). clear - L1r. lia. }
  pose proof (rtd_dblk L1 A1 e1 h1 OUT1 r0 rs0
                (text_rec (last (hl_recs (hs_pending h1)) (0, [])) ++ hl_junk (hs_pending h1)) BK1 HR GONE) as BK2.
  destruct (UI_rtd_bundle s L1 A1 m1 md1 m3 e1 (hdropl h1 rs0) OUT1 junk1 LB1 D _ (ds_off s + dnum s) 0
              (re_used e1 + dnum s) (re_U e1 ++ firstn (Z.to_nat (dnum s)) (re_junk e1))
              (skipn (Z.to_nat (dnum s)) (re_junk e1))
              RP1 FR1 SAC1 EK1 SR1 OT1 H7h H8h BK2 GL1 OU1 MU13 WM13 HW HC3 HB3s OF)
    as (RP3 & FR3 & SAC3 & EK3 & SR3 & OT3 & GL3 & OU3).
  assert (PS' : pstream s = ddata s ++ prest (ds_pend s) (ds_off s + dnum s))
    by (apply rtk_ps; [exact WF1 | clear - NP; lia]).
  assert (LPS : length (pstream s) = (length (ddata s) + length (prest (ds_pend s) (ds_off s + dnum s)))%nat)
    by (rewrite PS', length_app; reflexivity).
  pose proof (rtd_ps s W) as PSD.
  assert (Y18 : getr R3 18 = Z_to_bv 64 (re_buf e1)) by rgw X3.
  apply SR_ret.
  exists R3, L1, A1, m3, md1,
    (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1 + dnum s) (re_cap e1) (re_hp e1)
        (re_kh e1) (re_pad2 e1) (re_keys e1) (re_U e1 ++ firstn (Z.to_nat (dnum s)) (re_junk e1))
        (skipn (Z.to_nat (dnum s)) (re_junk e1))),
    (hdropl h1 rs0), OUT1, junk1, LB1, D.
  split; [reflexivity|].
  split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3|].
  split; [rewrite Y18; f_equal; cbn [re_buf Z.of_nat]; clear; lia|].
  split; [split; [clear; lia | left; reflexivity]|].
  destruct (rtk_p0 s) as (P0a & P0b & P0c & P0d & P0e & P0f).
  unfold DLC, LCORE. rewrite P0a, P0b, P0c, P0d, P0e, P0f, app_nil_r, (rtd_dv s W), (drlq_0 s NZU).
  split; [exact RP3|].
  split; [exact IN1|].
  split; [exact MT1|].
  split; [rewrite SEGS; exact RO3|].
  split; [exact FR3|].
  split; [exact SAC3|].
  split; [apply rtk_okx; [exact EK3 | exact Cp | clear - NP NR; lia]|].
  split; [exact SR3|].
  split; [exact OT3|].
  split; [exact SM1|].
  split.
  { unfold DLINK, hdropl, hdrop.
    cbn [ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap re_cap re_U re_skip re_keys hs_eintr
         hs_pending hs_off hs_expected hl_recs].
    split; [exact L1c|].
    split; [unfold dW; rewrite <- L2c, <- JK; unfold bzs; apply map_app|].
    split; [exact L3c|]. split; [exact L4c|]. split; [exact L5c|]. split; [exact L6c|].
    split; [unfold dtail; rewrite <- L7c, HR; reflexivity|].
    split; [reflexivity|]. split; [exact L9c|]. split; [exact L10c|]. split; [exact L11c|].
    unfold dwf. cbn [ds_off ds_pend]. split; [clear; lia|]. intros r rs _. clear; lia. }
  split.
  { unfold DHISTg, hdropl, hdrop. cbn [ds_ref ds_no ds_H ds_en hs_expected].
    split; [rewrite H1h, PS', app_assoc; unfold pstream; cbn [ds_pend ds_off]; rewrite PSD; reflexivity|].
    split; [rewrite H2h, feed_app; reflexivity|].
    split; [exact H4h|]. split; [exact H5h|]. split; [exact H6h|]. split; [exact H7h|]. split; [exact H8h|].
    split; [exact H9h|]. split; [exact H10h|].
    unfold pstream. cbn [ds_pend ds_off]. rewrite PSD. pose proof (rbl_lines_le (ddata s) (ds_ref s)) as LL.
    unfold dref. clear - LL LPS H12h. lia. }
  split.
  { unfold pstream. cbn [ds_pend ds_off]. rewrite PSD. pose proof (rtk_chunk_le (ds_u s) (ds_skip s) (ddata s)) as CL.
    unfold drl, dchunk. clear - CL LPS H11h. lia. }
  split.
  { split; [exact H2h|]. split; [exact H3h|]. split; [exact GR|]. split; [exact WF1|]. split; [exact STR|].
    split; [exact E | exact PNE]. }
  split; [unfold DBLK in BK2 |- *; exact BK2|].
  split.
  - unfold DGLBg. unfold DGLB, brf, eif, dtot in GL3. exact GL3.
  - unfold DOUT in OU3 |- *. cbn [ds_no ds_ocap]. exact OU3.
Qed.

Lemma read_tail : forall s c, DRE s c -> SR segs c (DHQ s).
Proof using All.
  intros s c H. destruct (dwhole s) eqn:W.
  - exact (read_tail_drop s c H W).
  - exact (read_tail_keep s c H W).
Qed.

Lemma read_step : forall s c, DF s c -> ds_eintr s = false -> ds_pend s <> [] -> SR segs c (DHQ s).
Proof using All.
  intros s c H E P. eapply SR_bind; [exact (read_a s c H E P)|]. intros c1 H1.
  eapply SR_bind; [exact (byte_loop s c1 H1)|]. intros c2 H2. exact (read_tail s c2 H2).
Qed.

Lemma fb_none : forall (U : list byte) i, StrFun.find_byte 0 U = None -> nth_error (bzs U) i <> Some 0.
Proof using.
  intros U i FB E. unfold bzs in E. rewrite nth_error_map in E.
  destruct (nth_error U i) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate].
  injection E as E. exact (StrFun.find_byte_None 0 U FB i b Eb E).
Qed.

Lemma fb_some : forall (U : list byte) i, StrFun.find_byte 0 U = Some i ->
  (i < length U)%nat /\ nth_error (bzs U) i = Some 0 /\ (forall k, (k < i)%nat -> nth_error (bzs U) k <> Some 0).
Proof using.
  intros U i FB. destruct (StrFun.find_byte_Some 0 U i FB) as (IL & (b & Eb & Hb) & IM).
  split; [exact IL|]. split.
  - unfold bzs. rewrite nth_error_map, Eb. cbn [option_map]. unfold bz. rewrite Hb. reflexivity.
  - intros k Hk E. unfold bzs in E. rewrite nth_error_map in E.
    destruct (nth_error U k) as [b'|] eqn:Eb'; cbn [option_map] in E; [|discriminate].
    injection E as E. exact (IM k b' Hk Eb' E).
Qed.

Lemma fb_skip_some : forall s (U : list byte) P i, bzs U = dW s -> StrFun.find_byte 0 (skipn P U) = Some i ->
  (P + i < length (dW s))%nat /\ nth_error (dW s) (P + i) = Some 0 /\
  (forall k, (P <= k < P + i)%nat -> nth_error (dW s) k <> Some 0).
Proof using HG HJ O h junk.
  intros s U P i EW FB. destruct (fb_some _ _ FB) as (IL & IZ & IM).
  assert (ES : bzs (skipn P U) = skipn P (dW s)) by (rewrite <- skipn_bzs, EW; reflexivity).
  assert (LW : length (dW s) = length U) by (rewrite <- EW; unfold bzs; apply length_map).
  rewrite ES in IZ, IM. rewrite length_skipn in IL.
  split; [lia|]. split.
  - rewrite <- nth_skipn. exact IZ.
  - intros k Hk. replace k with (P + (k - P))%nat by lia. rewrite <- nth_skipn. apply IM. lia.
Qed.

Lemma fb_skip_none : forall s (U : list byte) P, bzs U = dW s -> StrFun.find_byte 0 (skipn P U) = None ->
  forall k, (P <= k)%nat -> nth_error (dW s) k <> Some 0.
Proof using HG HJ O h junk.
  intros s U P EW FB k Hk E.
  assert (ES : bzs (skipn P U) = skipn P (dW s)) by (rewrite <- skipn_bzs, EW; reflexivity).
  apply (fb_none (skipn P U) (k - P) FB). rewrite ES, nth_skipn. replace (P + (k - P))%nat with k by lia. exact E.
Qed.

Lemma dl_buf : forall s sk Hk ka no oc L1 A1 m1 md1 e1 h1, MR L1 A1 m1 md1 -> entry_okx L1 A1 m1 e1 ->
  DLINK (dvirt s sk Hk ka no oc) e1 h1 ->
  bzs (re_U e1) = dW s /\ length (re_U e1) = length (dW s) /\ re_used e1 = Z.of_nat (length (dW s)) /\
  bytes_at segs m1 (re_buf e1) (re_U e1) /\ 0 <= re_buf e1 /\ re_buf e1 + re_used e1 < 2 ^ 64 /\
  (0 < re_used e1 -> 0 < re_buf e1).
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros s sk Hk ka no oc L1 A1 m1 md1 e1 h1 M1 (_ & _ & _ & _ & _ & _ & K7 & K8 & K9 & _) (_ & L2c & _).
  pose proof gfacts as (_ & _ & _ & F4 & _).
  assert (EW : bzs (re_U e1) = dW s) by exact L2c.
  assert (LW : length (re_U e1) = length (dW s)) by (rewrite <- EW; unfold bzs; symmetry; apply length_map).
  split; [exact EW|]. split; [exact LW|]. split; [rewrite <- LW; lia|].
  destruct K9 as [(C0 & B0 & U0)|(Cp & BI & BF & BJ & BC)].
  - assert (UN : re_U e1 = []).
    { destruct (re_U e1) as [|b0 U'] eqn:EU0; [reflexivity|]. rewrite ?EU0 in K7. cbn [length] in K7. lia. }
    rewrite UN, B0. split.
    + split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
    + split; [lia|]. split; [lia|]. intros UP. lia.
  - pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
    destruct BC as [[_ BB] _]. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
    apply bytes_at_app in BB as [BB _].
    split; [exact BB|]. split; [lia|]. split; [lia|]. intros _. lia.
Qed.

Lemma dl_wx : wx_apart rsegs = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma ret_pc_13bac : ret_pc (Z_to_bv 64 0x13bac) = Z_to_bv 64 0x13bac.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Definition Hid (P : Prop) : Prop := P.
Ltac hide := repeat match goal with
  | H : ?P \/ ?Q |- _ => change (Hid (P \/ Q)) in H
  | H : ?P -> ?Q |- _ => lazymatch Q with False => fail | _ => change (Hid (P -> Q)) in H end
  end.

Lemma LL6000 : Z.of_nat LINE_LIMIT = 6000.
Proof using. reflexivity. Qed.

Lemma with_nul_app : forall l1 l2, with_nul (l1 ++ l2) = with_nul l1 ++ with_nul l2.
Proof using. intros l1 l2. unfold with_nul. rewrite map_app, concat_app. reflexivity. Qed.

Lemma with_nul_one : forall l, with_nul [l] = l ++ [0].
Proof using. intros l. unfold with_nul. cbn [map concat]. apply app_nil_r. Qed.

Lemma with_nul_in : forall l ls, In l ls -> (length l < length (with_nul ls))%nat.
Proof using HG HJ O h junk.
  intros l ls. induction ls as [|x r IH]; intros H; [destruct H|].
  rewrite with_nul_cons, !length_app. cbn [length].
  destruct H as [->|H]; [lia | specialize (IH H); lia].
Qed.

Lemma drlq_split : forall s P, dbound s P -> drlq s 0 = drlp s P ++ drlq s P.
Proof using HG HJ O h junk.
  intros s P HB. destruct (scan_pre s P (skipn P (dW s)) HB) as [_ E]. rewrite firstn_skipn in E. exact E.
Qed.

Lemma dline_in : forall s D X P Q, RSTART s D -> bzs PS = (D ++ ddata s) ++ X -> dbound s P ->
  (P <= Q < length (dW s))%nat -> nth_error (dW s) Q = Some 0 ->
  (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) -> dskp s P = false -> (Q - P <= LINE_LIMIT)%nat ->
  In (dline s P Q) LS0.
Proof using HG HJ O junk.
  intros s D X P Q (RF & J & _) EP HB HPQ HQ HNZ HK HL.
  destruct (drl_send s P Q HB HPQ HQ HNZ HK HL) as (_ & E2 & _).
  assert (Hz : nozero (ds_u s)) by (destruct J as (_ & _ & _ & Z0); exact Z0).
  assert (EL : drl s = lines (ds_ref s) (ddata s)).
  { pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) (ddata s) J) as C. unfold drl, dchunk. revert C.
    destruct (chunk (ds_u s) (ds_skip s) (ddata s)) as [[u' k'] ls]. intros C. cbv beta iota in C.
    destruct C as [C _]. exact C. }
  rewrite EP, !lines_app, <- RF, <- EL, <- (drlq_0 s Hz), (drlq_split s P HB), E2.
  apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.

Lemma nd3 : forall (g o : Z) l, NoDup (g :: o :: l) -> g <> o /\ ~ In g l /\ ~ In o l.
Proof using.
  intros g o l H. apply NoDup_ListNoDup in H.
  apply List.NoDup_cons_iff in H as [H1 H]. apply List.NoDup_cons_iff in H as [H2 _].
  split; [intros E; apply H1; left; symmetry; exact E|].
  split; [intros I; apply H1; right; exact I | exact H2].
Qed.

Lemma rp_keep : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k, WF A1 ->
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  In (q, k) (blocks L1 A1) -> (0 < k -> ~ F0 q) -> In (q, k) (blocks L2 A2).
Proof using G HJ O h junk regs.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k W1
    (M2 & W2 & B2 & LL & LN & AD & SV & Z0 & OW & RP & MD & FR & BY & SC) Hq HF.
  apply CF.gestures_end_b.blocks_In2 in Hq as (p & Ep & Hp). subst q.
  apply CF.gestures_end_b.blocks_In2.
  pose proof (sb_ub_nonneg A1 p k W1 Hp) as K0.
  destruct (Z.eq_dec k 0) as [->|Kn].
  - destruct (Z0 p Hp) as [Hp2 EA]. exists p. split; [exact EA | exact Hp2].
  - assert (NF : ~ F0 (ptr_addr L1 p)) by (apply HF; lia).
    pose proof (SV p k Hp ltac:(lia) NF) as Hp2. exists p. split; [exact (AD p k Hp Hp2 NF) | exact Hp2].
Qed.

Lemma eb_livex : forall L1 A1 m1 e1 q, entry_okx L1 A1 m1 e1 -> In q (entry_blocks e1) ->
  exists k, In (q, k) (blocks L1 A1).
Proof using HG HJ O h junk.
  intros L1 A1 m1 e1 q (_ & _ & _ & _ & _ & _ & _ & _ & E9 & _ & E11 & _ & _ & E14) Hq.
  unfold entry_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [|apply in_app_or in Hq as [Hq|Hq]].
  - revert Hq. destruct (Z.eqb_spec (re_cap e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E9 as [(C0 & _)|(_ & BI & _)]; [lia | exists (re_cap e1); exact BI].
  - revert Hq. destruct (Z.eqb_spec (re_hp e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E11 as [(H0 & _)|(HI & _)]; [lia | exists (re_kh e1); exact HI].
  - apply in_map_iff in Hq as (k & <- & Hk). destruct (proj1 (Forall_forall _ _) E14 k Hk) as (K1 & _).
    eexists; exact K1.
Qed.

Lemma entry_okx_tr : forall L1 A1 L2 A2 m1 m2 e1 Pa, msame Pa m1 m2 -> entry_okx L1 A1 m1 e1 ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1) -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1) -> q <= a < q + k -> Pa a) ->
  entry_okx L2 A2 m2 e1.
Proof using.
  intros L1 A1 L2 A2 m1 m2 e1 Pa MS (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) SV HP.
  assert (IB : re_cap e1 <> 0 -> In (re_buf e1) (entry_blocks e1)).
  { intros C. unfold entry_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
  assert (IH : re_hp e1 <> 0 -> In (re_hp e1) (entry_blocks e1)).
  { intros C. unfold entry_blocks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
  assert (IK : forall k, In k (re_keys e1) -> In (key_addr k) (entry_blocks e1)).
  { intros k Hk. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
  unfold entry_okx. do 8 (split; [assumption|]).
  split.
  { destruct E9 as [Z0|(C0 & BI & BF & BJ & BC)]; [left; exact Z0 | right].
    assert (CN : re_cap e1 <> 0) by (clear - C0; lia).
    split; [exact C0|]. split; [exact (SV _ _ BI (IB CN))|]. split; [exact BF|]. split; [exact BJ|].
    eapply rw_tr; [exact MS | exact BC |]. intros a Ha. apply (HP _ _ a BI (IB CN)).
    cbn [cells_size csize] in Ha. clear - Ha C0. lia. }
  split; [exact E10|].
  split.
  { destruct E11 as [Z0|(HI & HF & H8 & H8' & HB)]; [left; exact Z0 | right].
    assert (HN : re_hp e1 <> 0) by (destruct HF as (HF1 & _); clear - HF1; lia).
    split; [exact (SV _ _ HI (IH HN))|]. split; [exact HF|]. split; [exact H8|]. split; [exact H8'|].
    eapply by_tr; [exact MS | exact HB |]. intros a Ha. apply (HP _ _ a HI (IH HN)).
    rewrite CF.gestures_end_b.key_ptrs_length in Ha. unfold re_nheld in H8. clear - Ha H8. lia. }
  split; [exact E12|]. split; [exact E13|].
  apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) E14 k Hk) as (K1 & K2 & K3 & K4 & K5).
  split; [exact (SV _ _ K1 (IK k Hk))|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  eapply by_tr; [exact MS | exact K3 |]. intros a Ha. apply (HP _ _ a K1 (IK k Hk)).
  rewrite length_app in Ha. cbn [length] in Ha. clear - Ha. lia.
Qed.

Definition esk0 (e1 : rentry) : rentry :=
  RE (re_fd e1) (re_eof e1) 0 (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1)
     (re_pad2 e1) (re_keys e1) (re_U e1) (re_junk e1).

Lemma entry_okx_sk0 : forall L1 A1 m1 e1, entry_okx L1 A1 m1 e1 -> entry_okx L1 A1 m1 (esk0 e1).
Proof using.
  intros L1 A1 m1 e1 (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
  unfold entry_okx.
  exact (conj E1 (conj (or_introl eq_refl) (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 (conj E8 (conj E9
    (conj E10 (conj E11 (conj E12 (conj E13 E14))))))))))))).
Qed.

Lemma core_tr : forall L1 A1 m1 L2 A2 m2 e1 h1 Pa, msame Pa m1 m2 ->
  (exists j0 j1 j2 j4, rw_cells segs m1 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) ->
  entry_okx L1 A1 m1 e1 -> src_at Bm L1 A1 m1 HA h1 -> others_at Bm m1 j (re_fd e) fs os ->
  (forall a, S0 - 144 <= a < S0 -> Pa a) ->
  (forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX -> Pa a) ->
  (forall q k, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) -> In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) -> q <= a < q + k -> Pa a) ->
  (exists j0 j1 j2 j4, rw_cells segs m2 (S0 - 144) ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED)) /\
  entry_okx L2 A2 m2 e1 /\ src_at Bm L2 A2 m2 HA h1 /\ others_at Bm m2 j (re_fd e) fs os.
Proof using EHI GEI HG HJ O PRE SEGS h junk.
  intros L1 A1 m1 L2 A2 m2 e1 h1 Pa MS (j0 & j1 & j2 & j4 & FR) EK SR0 OT HF HI SV HB. hide.
  pose proof gfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11).
  split.
  { exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FR |]. intros a Ha. apply HF.
    unfold dr_saved in Ha. cbn [cells_size csize app] in Ha. lia. }
  split.
  { eapply entry_okx_tr; [exact MS | exact EK | |].
    - intros q k Hq Hi. apply SV; [exact Hq | apply in_or_app; left; exact Hi].
    - intros q k a Hq Hi Ha. apply (HB q k a Hq); [apply in_or_app; left; exact Hi | exact Ha]. }
  split.
  { eapply src_at_tr0; [exact MS | exact SR0 | | |].
    - intros a Ha. apply HI. unfold G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - intros q k Hq Hi. apply SV; [exact Hq | apply in_or_app; right; exact Hi].
    - intros q k a Hq Hi Ha. apply (HB q k a Hq); [apply in_or_app; right; exact Hi | exact Ha]. }
  eapply others_at_tr; [exact MS | exact OT |]. intros i a Hi _ Ha. apply HI.
  unfold G_S, SRC_SIZE, SOURCES_MAX in *. lia.
Qed.

Lemma ro_off : forall a, 0 <= a < 2 ^ 64 -> ~ in_img Bm a -> ro_addr rsegs (wa a) = false.
Proof using SEGS.
  intros a Ha NI. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  exfalso. apply NI. exact (ro_in_img Bm SEGS a Ha E).
Qed.

Lemma mem_back : forall m m2, mem_rel rsegs m2 (normalize rsegs m) -> ro_same rsegs m m2 -> m2 = m.
Proof using.
  intros m m2 [HR _] RS. apply FunctionalExtensionality.functional_extensionality. intros a.
  destruct (ro_addr rsegs a) eqn:E; [exact (RS a E)|].
  pose proof (HR a) as X. unfold normalize in X. rewrite E in X. symmetry. exact X.
Qed.

Lemma core_skip : forall s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2,
  LCORE s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 ->
  munch [(SA + 8, SA + 12)] m1 m2 -> wmono rsegs m1 m2 -> rw_cells rsegs m2 (SA + 8) [C4 (Z_to_bv 64 0)] ->
  LCORE s D sent kl Hk ka no oc nk rest false L1 A1 m2 md1 (esk0 e1) h1 OUT1 junk1 LB1.
Proof using AX BW EHI EU GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2
    (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NB1 & RS1 & BK1 & GL1 & OU1)
    MU WM C0.
  hide. pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & _).
  pose proof HG as (_ & GF & _).
  pose proof BK1 as (ND & GI & _).
  destruct (nd3 _ _ _ ND) as (GO & GN & ON).
  assert (WM' : wmono segs m1 m2) by (rewrite SEGS; exact WM).
  pose proof (msame_munch _ _ _ MU WM') as MS.
  assert (PG : forall a, 0 <= a < 2 ^ 64 -> ~ (G <= a < G + SRC_TABLE) ->
            0 <= a < 2 ^ 64 /\ outside [(SA + 8, SA + 12)] a).
  { intros a Ha Hn. split; [exact Ha|]. cbn [outside]. split; [|exact I]. unfold SRC_TABLE, SRC_ENTRY in Hn. lia. }
  assert (PI : forall a, in_img Bm a -> 0 <= a < 2 ^ 64 /\ outside [(SA + 8, SA + 12)] a).
  { intros a Ha. pose proof (img_lo a Ha) as IL. apply PG; [lia|]. intros Hg. destruct GF as (_ & _ & GF3).
    apply (GF3 (a - G)); [lia|]. replace (G + (a - G)) with a by lia. exact Ha. }
  assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> q <> G -> q <= a < q + k ->
            0 <= a < 2 ^ 64 /\ outside [(SA + 8, SA + 12)] a).
  { intros q k a Hq Hne Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR. apply PG; [lia|].
    destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq GI Hne) as [D0|D0]; unfold SRC_TABLE, SRC_ENTRY in *;
      lia. }
  assert (PFa : forall a, S0 - 144 <= a < S0 -> 0 <= a < 2 ^ 64 /\ outside [(SA + 8, SA + 12)] a).
  { intros a Ha. apply PG; [lia|]. unfold SRC_TABLE, SRC_ENTRY. lia. }
  assert (PIa : forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX ->
            0 <= a < 2 ^ 64 /\ outside [(SA + 8, SA + 12)] a).
  { intros a Ha. apply PI. exact (proj1 (GRP a ltac:(unfold G_RELAY_LO, G_S in *; lia))). }
  assert (PSa : forall q k, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) ->
            In (q, k) (blocks L1 A1)) by (intros q k Hq _; exact Hq).
  assert (PBa : forall q k a, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) -> q <= a < q + k ->
            0 <= a < 2 ^ 64 /\ outside [(SA + 8, SA + 12)] a).
  { intros q k a Hq Hi Ha. apply (PB q k a Hq); [intros ->; exact (GN Hi) | exact Ha]. }
  destruct (core_tr L1 A1 m1 L1 A1 m2 e1 h1 _ MS FR1 EK1 SR1 OT1 PFa PIa PSa PBa) as (FR2 & EK2 & SR2 & OT2).
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU); [exact WM' | exact GEI |].
    intros a Ha. destruct (Z_lt_le_dec a (SA + 8)) as [D0|D0]; [left; cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec a (SA + 12)) as [D2|D2]; [|left; cbn [outside]; split; [lia | exact I]].
    right. right. right. right. split.
    - destruct GF as (_ & _ & GF3). intros Hi. apply (GF3 (a - G)); [unfold SRC_TABLE, SRC_ENTRY; lia|].
      replace (G + (a - G)) with a by lia. exact Hi.
    - split; [exists G, SRC_TABLE; split; [exact GI | unfold SRC_TABLE, SRC_ENTRY; lia]|].
      intros p n i _ _ _ _ NE E. apply NE. rewrite E. right. left. unfold SRC_ENTRY. lia. }
  split; [exact IN1|]. split; [exact TR1|].
  split.
  { rewrite SEGS. apply (ro_munch2 m1 m2 [(SA + 8, SA + 12)]); [rewrite <- SEGS; exact RO1 | exact MU |].
    intros x Hx. exact (proj2 (PI _ Hx)). }
  split; [exact FR2|].
  split.
  { assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
    pose proof EK1 as (_ & _ & K3 & K4 & _).
    destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
    destruct (dr_cut m1 SA (SA + 8) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1))]
                [C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)] EC1 eq_refl) as [EA EB].
    destruct (dr_cut m1 (SA + 8) (SA + 12) [C4 (Z_to_bv 64 (re_skip e1))] [CB 4 (re_pad1 e1)] EB
                ltac:(cbn [cells_size csize]; lia)) as [_ EP].
    assert (TRc : forall c cs, rw_cells rsegs m1 c cs ->
              (forall a, c <= a < c + Z.of_nat (cells_size cs) -> ~ (SA + 8 <= a < SA + 12)) ->
              rw_cells rsegs m2 c cs).
    { intros c cs Hc Hp. pose proof (rw_cells_bound _ _ _ _ Hc) as CB0. rewrite <- SEGS. rewrite <- SEGS in Hc.
      apply (rw_tr _ m1 m2 c cs MS Hc). intros a Ha. split; [lia|]. cbn [outside].
      split; [exact (Hp a Ha) | exact I]. }
    pose proof (TRc _ _ EA ltac:(intros a Ha; cbn [cells_size csize] in Ha; lia)) as EA2.
    pose proof (TRc _ _ EP ltac:(intros a Ha; cbn [cells_size csize] in Ha; lia)) as EP2.
    pose proof (TRc _ _ EC2 ltac:(intros a Ha; cbn [cells_size csize] in Ha; lia)) as EC2'.
    pose proof (TRc _ _ EC3 ltac:(intros a Ha; cbn [cells_size csize] in Ha; lia)) as EC3'.
    assert (EB2 : rw_cells rsegs m2 (SA + 8) [C4 (Z_to_bv 64 0); CB 4 (re_pad1 e1)]).
    { apply (dr_join m2 (SA + 8) (SA + 12) [C4 (Z_to_bv 64 0)] [CB 4 (re_pad1 e1)] C0 EP2).
      cbn [cells_size csize]. lia. }
    assert (E12 : rw_cells rsegs m2 SA [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1)); C4 (Z_to_bv 64 0);
                                         CB 4 (re_pad1 e1)]).
    { apply (dr_join m2 SA (SA + 8) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1))]
               [C4 (Z_to_bv 64 0); CB 4 (re_pad1 e1)] EA2 EB2). reflexivity. }
    rewrite SEGS. exact (ent_join m2 SA (esk0 e1) K3 K4 E12 EC2' EC3'). }
  split; [exact (entry_okx_sk0 _ _ _ _ EK2)|].
  split; [exact SR2|]. split; [exact OT2|]. split; [exact SM1|].
  split.
  { destruct LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
    split; [exact L1c|]. split; [exact L2c|]. split; [reflexivity|].
    split; [exact L4c|]. split; [exact L5c|]. split; [exact L6c|]. split; [exact L7c|]. split; [exact L8c|].
    split; [exact L9c|]. split; [exact L10c|]. split; [exact L11c | exact WF1]. }
  split; [exact HI1|]. split; [exact NB1|]. split; [exact RS1|]. split; [exact BK1|].
  split.
  { destruct GL1 as (G1c & G2c & G3c & G4c & (ev1 & G5c)).
    split; [eapply rw_tr; [exact MS | exact G1c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GCP a ltac:(lia)))|].
    split; [eapply rw_tr; [exact MS | exact G2c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))|].
    split; [eapply rw_tr; [exact MS | exact G3c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))|].
    split; [eapply rw_tr; [exact MS | exact G4c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))|].
    exists ev1. eapply rw_tr; [exact MS | exact G5c |]. intros a Ha. apply PI. cbn [cells_size csize] in Ha.
    apply GEI. lia. }
  destruct OU1 as (OF1 & OT1'). hide.
  assert (LO : Z.of_nat (length O) = NO).
  { destruct OUTD as [(_ & _ & N0 & E0)|(_ & _ & _ & _ & _ & L0 & _)]; [rewrite E0; cbn [length Z.of_nat]; lia | exact L0]. }
  split.
  - intros LV. destruct (OF1 LV) as (C1 & E1 & E2 & E3).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))|].
    split; [exact E1|]. split; [exact E2|].
    intros Cp. destruct (E3 Cp) as (I3 & B3). split; [exact I3|].
    eapply by_tr; [exact MS | exact B3 |]. intros a Ha. apply (PB OUT CAP a I3).
    + intros X. apply GO. rewrite E1. symmetry. exact X.
    + destruct OUTD as [(C0' & _)|(_ & _ & _ & _ & _ & L0 & LJ)]; [lia|]. rewrite length_app in Ha. lia.
  - intros LV. destruct (OT1' LV) as (C1 & D1).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))|].
    destruct D1 as [D1|(Cp & NL & I3 & F3' & B3 & LJ)]; [left; exact D1 | right].
    split; [exact Cp|]. split; [exact NL|]. split; [exact I3|]. split; [exact F3'|].
    split; [|exact LJ].
    eapply by_tr; [exact MS | exact B3 |]. intros a Ha. apply (PB OUT1 _ a I3); [intros X; apply GO; symmetry; exact X|].
    pose proof HI1 as (_ & _ & _ & _ & _ & HN & HLB & _).
    assert (LL : Z.of_nat (length LB1) = Z.of_nat (length (with_nul sent)))
      by (rewrite <- HLB; unfold bzs; rewrite length_map; reflexivity).
    rewrite !length_app in Ha. lia.
Qed.

Lemma ret_ok_13be4 : YK0s.ret_ok (Z_to_bv 64 0x13be4).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma pre_send : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre_k Bm MR SEND_LINE_K L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. apply SC1.
    left. change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma fsep : forall q n lo hi, fresh_block Bm q n -> 0 < n -> lo < hi -> (forall a, lo <= a < hi -> in_img Bm a) ->
  q + n <= lo \/ hi <= q.
Proof using HG HJ O h junk.
  intros q n lo hi (_ & _ & Hf) Hn Hlh Himg.
  destruct (Z_le_gt_dec (q + n) lo) as [D0|D0]; [left; exact D0|].
  destruct (Z_le_gt_dec hi q) as [D1|D1]; [right; exact D1|]. exfalso.
  apply (Hf (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia. apply Himg. lia.
Qed.

Ltac pr_tac PR r X := etransitivity; [exact (PR r ltac:(unfold callee_saved; lia)) | exact X].

Ltac UH_pr PR r X := etransitivity; [exact (PR r ltac:(unfold callee_saved; clear - PR; lia)) | exact X].

Lemma lsd_live : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n, WF A1 ->
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p q n -> ~ F0 q -> live_at L2 A2 p q n.
Proof using All.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n W1 RP [Hp Hq] NF.
  pose proof RP as (_ & _ & _ & _ & _ & RPa & RPb & RPz & _). rewrite <- Hq in NF.
  destruct (Z_lt_le_dec 0 n) as [Np|Nn].
  - pose proof (RPb p n Hp Np NF) as Hp2. split; [exact Hp2|]. rewrite (RPa p n Hp Hp2 NF). exact Hq.
  - assert (N0 : n = 0) by (pose proof (sb_ub_nonneg A1 p n W1 Hp) as N1; clear - N1 Nn; lia). subst n.
    destruct (RPz p Hp) as [Hp2 Ha]. split; [exact Hp2|]. rewrite Ha. exact Hq.
Qed.

Lemma lsd_f2 : forall {X Y : Type} (R R' : X -> Y -> Prop) (Px : X -> Prop) (Py : Y -> Prop) xs ys,
  Forall2 R xs ys -> Forall Py ys -> (forall x, In x xs -> Px x) ->
  (forall x y, Px x -> Py y -> R x y -> R' x y) -> Forall2 R' xs ys.
Proof using All.
  intros X Y R R' Px Py xs ys H. induction H as [|x y xs' ys' Hxy Hr IH]; intros Fy Hx Imp; [constructor|].
  constructor.
  - apply Imp; [apply Hx; left; reflexivity | exact (Forall_inv Fy) | exact Hxy].
  - apply IH; [exact (Forall_inv_tail Fy) | intros z Hz; apply Hx; right; exact Hz | exact Imp].
Qed.

Lemma lsd_links : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 qd qs a a' e1 h1, WF A1 ->
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall q, In q (entry_blocks e1 ++ hs_blocks h1) -> ~ F0 q) -> dadr_ok (length qd) a ->
  da_buf a' = da_buf a -> da_hp a' = da_hp a -> da_keys a' = da_keys a -> da_pend a' = da_pend a ->
  da_ev a' = da_ev a -> da_erecs a' = da_erecs a ->
  entry_links L1 A1 qd a e1 -> src_links L1 A1 qd (known_at L A) a h1 ->
  entry_links L2 A2 (qd ++ qs) a' e1 /\ src_links L2 A2 (qd ++ qs) (known_at L A) a' h1.
Proof using All.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 qd qs a a' e1 h1 W1 RP NF (_ & Ob & Oh & Ok & Op & Oe & Or)
    Eb Eh Ek Ep Ee Er (EL1 & EL2 & EL3) (SL1 & SL2 & SL3 & (XL1 & XL2) & SL5 & SL6).
  assert (T : forall p q n, live_at L1 A1 p q n -> In q (entry_blocks e1 ++ hs_blocks h1) -> live_at L2 A2 p q n).
  { intros p q n Hl Hq. exact (lsd_live K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n W1 RP Hl (NF q Hq)). }
  assert (RA : forall x, p3a_ok x (length qd) -> resolveF (qd ++ qs) x = resolveF qd x).
  { intros x Hx. exact (p3a_resolve_app qd qs x Hx). }
  assert (KN : forall z, resolveF (qd ++ qs) (known_at L A z) = resolveF qd (known_at L A z)) by (intros z; reflexivity).
  assert (IE : forall q, In q (entry_blocks e1) -> In q (entry_blocks e1 ++ hs_blocks h1)).
  { intros q Hq. apply in_or_app. left. exact Hq. }
  assert (IH : forall q, In q (hs_blocks h1) -> In q (entry_blocks e1 ++ hs_blocks h1)).
  { intros q Hq. apply in_or_app. right. exact Hq. }
  assert (LV : forall l, 0 < hl_cap l -> In (hl_v l) (list_blocks l)).
  { intros l C. unfold list_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. left. reflexivity. }
  assert (LR : forall l r, In r (hl_recs l) -> In (fst r) (list_blocks l)).
  { intros l r Hr. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr. }
  unfold entry_links, src_links, expected_links. rewrite Eb, Eh, Ek, Ep, Ee, Er.
  split.
  - split.
    { intros C. rewrite (RA _ Ob). apply T; [exact (EL1 C)|]. apply IE. unfold entry_blocks. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ 0)) by lia. left. reflexivity. }
    split.
    { intros C. rewrite (RA _ Oh). apply T; [exact (EL2 C)|]. apply IE. unfold entry_blocks. apply in_or_app. right.
      apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
    apply (lsd_f2 _ _ (fun k => In (key_addr k) (entry_blocks e1 ++ hs_blocks h1)) (fun x => p3a_ok x (length qd))
             _ _ EL3 Ok).
    + intros k Hk. apply IE. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk.
    + intros k x Hk Hx Hl. cbv beta in Hk, Hx, Hl |- *. rewrite (RA _ Hx). exact (T _ _ _ Hl Hk).
  - split; [intros C; rewrite KN; exact (T _ _ _ (SL1 C) (IH _ (hb_pend _ _ (LV _ C))))|].
    split.
    { apply (lsd_f2 _ _ (fun r => In (fst r) (entry_blocks e1 ++ hs_blocks h1)) (fun x => p3a_ok x (length qd))
               _ _ SL2 Op).
      - intros r Hr. exact (IH _ (hb_pend _ _ (LR _ _ Hr))).
      - intros r x Hr Hx Hl. cbv beta in Hr, Hx, Hl |- *. rewrite (RA _ Hx). exact (T _ _ _ Hl Hr). }
    split; [rewrite KN; exact (T _ _ _ SL3 (IH _ (hb_part h1)))|].
    split.
    { split.
      - intros C. rewrite (RA _ Oe). exact (T _ _ _ (XL1 C) (IH _ (hb_exp _ _ (LV _ C)))).
      - apply (lsd_f2 _ _ (fun r => In (fst r) (entry_blocks e1 ++ hs_blocks h1)) (fun x => p3a_ok x (length qd))
                 _ _ XL2 Or).
        + intros r Hr. exact (IH _ (hb_exp _ _ (LR _ _ Hr))).
        + intros r x Hr Hx Hl. cbv beta in Hr, Hx, Hl |- *. rewrite (RA _ Hx). exact (T _ _ _ Hl Hr). }
    split; [intros C; rewrite KN; exact (T _ _ _ (SL5 C) (IH _ (hb_held _ _ (LV _ C))))|].
    apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SL6 r Hr) as X. cbv beta in X |- *.
    rewrite KN. exact (T _ _ _ X (IH _ (hb_held _ _ (LR _ _ Hr)))).
Qed.

Lemma lsd_dadr : forall n n' a o, dadr_ok n a -> (n <= n')%nat -> p3a_ok o n' ->
  dadr_ok n' (DA o (da_buf a) (da_hp a) (da_keys a) (da_pend a) (da_ev a) (da_erecs a)).
Proof using All.
  intros n n' a o (_ & O2 & O3 & O4 & O5 & O6 & O7) Hn Ho.
  assert (M : forall x, p3a_ok x n -> p3a_ok x n') by (intros x Hx; exact (p3a_ok_mono x n n' Hx Hn)).
  unfold dadr_ok. cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
  split; [exact Ho|]. split; [exact (M _ O2)|]. split; [exact (M _ O3)|].
  split; [exact (Forall_impl (fun x => p3a_ok x n') M O4)|].
  split; [exact (Forall_impl (fun x => p3a_ok x n') M O5)|].
  split; [exact (M _ O6) | exact (Forall_impl (fun x => p3a_ok x n') M O7)].
Qed.

Lemma lsd_room_pre : forall (t1 X : trF), wf_from sptr 0 t1 -> t1 ++ X = TR ->
  forall qs1, length qs1 = nretF t1 -> roomF F qs1 bnd t1.
Proof using All.
  intros t1 X W E. apply (p3a_room_pre F bnd t1 X W). rewrite E. exact ROOM.
Qed.

Lemma lsd_room : forall (b : rt_R F) (t1 : trF) qs1 o1 live mx0 NO0 CAP0 LEN0 p,
  wf_from sptr 0 t1 -> p3a_ok o1 (nretF t1) -> length qs1 = nretF t1 ->
  (live = true -> CAP0 <> 0 -> resolveF qs1 o1 = p) ->
  (forall qs, length qs = nretF (t1 ++ send_line_tr live mx0 NO0 CAP0 LEN0 (nretF t1) o1) ->
     roomF F qs b (t1 ++ send_line_tr live mx0 NO0 CAP0 LEN0 (nretF t1) o1)) ->
  forall qs2, length qs2 = nretF (send_line_tr live mx0 NO0 CAP0 LEN0 0 (Known p)) ->
    roomF F qs2 (runF F qs1 b t1) (send_line_tr live mx0 NO0 CAP0 LEN0 0 (Known p)).
Proof using All.
  intros b t1 qs1 o1 live mx0 NO0 CAP0 LEN0 p Hw Ho LQ Hp HR. destruct live.
  - exact (p3a_cat_room F b t1 qs1 o1 true mx0 NO0 CAP0 LEN0 p Hw Ho LQ (Hp eq_refl) HR).
  - intros qs2 _. exact I.
Qed.

Lemma lsd_run : forall (b : rt_R F) (t1 : trF) qs1 qs2 o1 live mx0 NO0 CAP0 LEN0 p,
  wf_from sptr 0 t1 -> p3a_ok o1 (nretF t1) -> length qs1 = nretF t1 ->
  (live = true -> CAP0 <> 0 -> resolveF qs1 o1 = p) ->
  nretF (t1 ++ send_line_tr live mx0 NO0 CAP0 LEN0 (nretF t1) o1) =
    (length qs1 + nretF (send_line_tr live mx0 NO0 CAP0 LEN0 0 (Known p)))%nat /\
  runF F (qs1 ++ qs2) b (t1 ++ send_line_tr live mx0 NO0 CAP0 LEN0 (nretF t1) o1) =
    runF F qs2 (runF F qs1 b t1) (send_line_tr live mx0 NO0 CAP0 LEN0 0 (Known p)) /\
  (live = true -> send_line_cap live mx0 NO0 CAP0 LEN0 <> 0 ->
    resolveF (qs1 ++ qs2) (send_line_out live mx0 NO0 CAP0 LEN0 (nretF t1) o1) =
    resolveF qs2 (send_line_out live mx0 NO0 CAP0 LEN0 0 (Known p))).
Proof using All.
  intros b t1 qs1 qs2 o1 live mx0 NO0 CAP0 LEN0 p Hw Ho LQ Hp. destruct live.
  - exact (p3a_cat_run F b t1 qs1 qs2 o1 true mx0 NO0 CAP0 LEN0 p Hw Ho LQ (Hp eq_refl)).
  - change (send_line_tr false mx0 NO0 CAP0 LEN0 (nretF t1) o1) with (@nil (rev sptr)).
    change (send_line_tr false mx0 NO0 CAP0 LEN0 0 (Known p)) with (@nil (rev sptr)).
    rewrite app_nil_r. split; [rewrite LQ; change (nretF []) with 0%nat; lia|].
    split; [|intros X; discriminate X].
    unfold runF, run_tr. rewrite (p3a_run_app _ _ _ _ qs1 qs2 b 0 t1) by (exact Hw || lia). reflexivity.
Qed.

Lemma lsd_lrest : forall no oc H ka l r jb o ha ks,
  lrest no oc H ka (l :: r) jb o ha ks =
  (send_line_tr LIVE MX no oc (Z.of_nat (length l) + 1) jb o ++
     fst (srest H ka l (no + Z.of_nat (length l) + 1) (send_line_cap LIVE MX no oc (Z.of_nat (length l) + 1)) r
            (jb + nretF (send_line_tr LIVE MX no oc (Z.of_nat (length l) + 1) jb o))
            (send_line_out LIVE MX no oc (Z.of_nat (length l) + 1) jb o) ha ks),
   snd (srest H ka l (no + Z.of_nat (length l) + 1) (send_line_cap LIVE MX no oc (Z.of_nat (length l) + 1)) r
            (jb + nretF (send_line_tr LIVE MX no oc (Z.of_nat (length l) + 1) jb o))
            (send_line_out LIVE MX no oc (Z.of_nat (length l) + 1) jb o) ha ks)).
Proof using All.
  intros no oc H ka l r jb o ha ks. unfold srest, lrest. cbn [lines_run fst snd]. rewrite seen_tr_m.
  replace (no + Z.of_nat (length l) + 1) with (no + (Z.of_nat (length l) + 1)) by ring. reflexivity.
Qed.

Lemma sdp_live : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n, WF A1 ->
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p q n -> ~ F0 q -> live_at L2 A2 p q n.
Proof using All.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n W1 RP [Hp Hq] NF.
  pose proof RP as (_ & _ & _ & _ & _ & RPa & RPb & RPz & _). rewrite <- Hq in NF.
  destruct (Z_lt_le_dec 0 n) as [Np|Nn].
  - pose proof (RPb p n Hp Np NF) as Hp2. split; [exact Hp2|]. rewrite (RPa p n Hp Hp2 NF). exact Hq.
  - assert (N0 : n = 0) by (pose proof (sb_ub_nonneg A1 p n W1 Hp) as N1; clear - N1 Nn; lia). subst n.
    destruct (RPz p Hp) as [Hp2 Ha]. split; [exact Hp2|]. rewrite Ha. exact Hq.
Qed.

Lemma sdp_f2 : forall {X Y : Type} (R R' : X -> Y -> Prop) (Px : X -> Prop) xs ys,
  Forall2 R xs ys -> (forall x, In x xs -> Px x) -> (forall x y, Px x -> R x y -> R' x y) -> Forall2 R' xs ys.
Proof using All.
  intros X Y R R' Px xs ys H. induction H as [|x y xs' ys' Hxy Hr IH]; intros Hx Imp; [constructor|].
  constructor.
  - apply Imp; [apply Hx; left; reflexivity | exact Hxy].
  - apply IH; [intros z Hz; apply Hx; right; exact Hz | exact Imp].
Qed.

Lemma sdp_f2s : forall {X Y : Type} (R : X -> Y -> Prop) xa x xb l, Forall2 R (xa ++ x :: xb) l ->
  exists ya y yb, l = ya ++ y :: yb /\ length ya = length xa /\ Forall2 R xa ya /\ R x y /\ Forall2 R xb yb.
Proof using All.
  intros X Y R xa x xb l H. apply Forall2_app_inv_l in H as (ya & l2 & Fa & Fb & ->).
  destruct l2 as [|y yb]; [inversion Fb|].
  assert (Hxy : R x y) by (inversion Fb; assumption).
  assert (Hb : Forall2 R xb yb) by (inversion Fb; assumption).
  exists ya, y, yb. split; [reflexivity|]. split; [symmetry; exact (Forall2_length Fa)|].
  split; [exact Fa|]. split; [exact Hxy | exact Hb].
Qed.

Lemma sdp_f2sw : forall {X Y : Type} (R : X -> Y -> Prop) (dx : X) (dy : Y) n xa x xb ya y yb,
  n = length xa -> length ya = length xa -> Forall2 R xa ya -> R x y -> Forall2 R xb yb ->
  Forall2 R (swap_remove dx n (xa ++ x :: xb)) (swap_remove dy n (ya ++ y :: yb)).
Proof using All.
  intros X Y R dx dy n xa x xb ya y yb -> LY Fa Hxy. revert yb.
  induction xb as [|z xb' _] using List.rev_ind; intros yb Fb.
  - destruct yb as [|w yb]; [|inversion Fb].
    rewrite swap_remove_last, <- LY, swap_remove_last. exact Fa.
  - apply Forall2_app_inv_l in Fb as (yb' & yz & Fb2 & HZ & ->).
    destruct yz as [|w yz]; [inversion HZ|].
    destruct yz as [|w' yz]; [|apply Forall2_length in HZ; cbn in HZ; lia].
    assert (Hzw : R z w) by (inversion HZ; assumption).
    rewrite swap_remove_mid, <- LY, swap_remove_mid.
    apply Forall2_app; [exact Fa | constructor; [exact Hzw | exact Fb2]].
Qed.

Lemma sdp_fsw : forall {X : Type} (Pr : X -> Prop) (d : X) a x b n, n = length a -> Forall Pr (a ++ x :: b) ->
  Forall Pr (swap_remove d n (a ++ x :: b)).
Proof using All.
  intros X Pr d a x b n -> H. apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) H).
  apply (Permutation.Permutation_in _ (Permutation.Permutation_sym (swap_remove_perm d a x b))). right. exact Hz.
Qed.

Lemma sdp_src : forall L1 A1 L2 A2 qd nm (a a' : dadr) h1,
  (forall p q n, live_at L1 A1 p q n -> In q (hs_blocks h1) -> live_at L2 A2 p q n) ->
  da_pend a' = da_pend a -> da_ev a' = da_ev a -> da_erecs a' = da_erecs a ->
  src_links L1 A1 qd nm a h1 -> src_links L2 A2 qd nm a' h1.
Proof using All.
  intros L1 A1 L2 A2 qd nm a a' h1 T Ep Ee Er (SL1 & SL2 & SL3 & (XL1 & XL2) & SL5 & SL6).
  assert (LV : forall l, 0 < hl_cap l -> In (hl_v l) (list_blocks l)).
  { intros l C. unfold list_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. left. reflexivity. }
  assert (LR : forall l r, In r (hl_recs l) -> In (fst r) (list_blocks l)).
  { intros l r Hr. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr. }
  unfold src_links, expected_links. rewrite Ep, Ee, Er.
  split; [intros C; exact (T _ _ _ (SL1 C) (hb_pend _ _ (LV _ C)))|].
  split.
  { apply (sdp_f2 _ _ (fun r => In (fst r) (hs_blocks h1)) _ _ SL2).
    - intros r Hr. exact (hb_pend _ _ (LR _ _ Hr)).
    - intros r x Hr Hl. cbv beta in Hr, Hl |- *. exact (T _ _ _ Hl Hr). }
  split; [exact (T _ _ _ SL3 (hb_part h1))|].
  split.
  { split.
    - intros C. exact (T _ _ _ (XL1 C) (hb_exp _ _ (LV _ C))).
    - apply (sdp_f2 _ _ (fun r => In (fst r) (hs_blocks h1)) _ _ XL2).
      + intros r Hr. exact (hb_exp _ _ (LR _ _ Hr)).
      + intros r x Hr Hl. cbv beta in Hr, Hl |- *. exact (T _ _ _ Hl Hr). }
  split; [intros C; exact (T _ _ _ (SL5 C) (hb_held _ _ (LV _ C)))|].
  apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SL6 r Hr) as X. cbv beta in X |- *.
  exact (T _ _ _ X (hb_held _ _ (LR _ _ Hr))).
Qed.

Lemma sdp_runF_free : forall qd b (tp : trF) n x,
  runF F qd b (tp ++ [RFree n x]) = rt_free F (runF F qd b tp) n (resolveF qd x).
Proof using All. intros qd b tp n x. unfold runF, run_tr. rewrite run_from_app. reflexivity. Qed.

Lemma sdp_nret1 : forall (tp : trF) n x, nretF (tp ++ [RFree n x]) = nretF tp.
Proof using All. intros tp n x. rewrite nret_app. exact (Nat.add_0_r _). Qed.

Lemma sdp_nr0 : forall jb n (x : adrF), (jb + nretF [RFree n x])%nat = jb.
Proof using All. intros jb n x. exact (Nat.add_0_r jb). Qed.

Lemma sdp_nrc : forall n (x : adrF) (t : trF), nretF (RFree n x :: t) = nretF t.
Proof using All. intros n x t. reflexivity. Qed.

Lemma line_send : forall s P Q R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
  RTL R1 -> getr R1 1 = Z_to_bv 64 0x13be4 -> getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) ->
  getr R1 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) ->
  getr R1 11 = Z_to_bv 64 (Z.of_nat (length (dline s P Q)) + 1) ->
  getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) ->
  dbound s P -> (P <= Q < length (dW s))%nat -> nth_error (dW s) Q = Some 0 ->
  (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) -> dskp s P = false -> (Q - P <= LINE_LIMIT)%nat ->
  DLC s D P L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 SEND_LINE) m1 (seg_rom segs)) md1) (DLS s P Q).
Proof using All.
  intros s P Q R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D RT1 G1 G9 G10 G11 G18 DB HPQ HQ HNZ HK HL DLC1.
  unfold DLC in DLC1.
  destruct DLC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NB1 & RS1 & BK1 &
    GL1 & OU1).
  hide. pose proof pre_facts as (HM0 & _ & _ & _ & _ & HCEIL & H63 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & W1 & B1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof (NODUP _ _ _ _ M1) as ND1.
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof EK1 as (_ & _ & K3 & K4 & _ & _ & K7 & K8 & K9 & _).
  pose proof HG as (_ & GF & _).
  pose proof BK1 as (ND & GI & BK3 & BK4 & BK5).
  destruct (nd3 _ _ _ ND) as (GO & GN & ON).
  destruct (drl_send s P Q DB HPQ HQ HNZ HK HL) as (EP1 & EQ1 & ES1).
  assert (LLN : length (dline s P Q) = (Q - P)%nat) by exact (dline_len s P Q HPQ).
  assert (UPOS : 0 < re_used e1) by (rewrite EUd; lia).
  destruct K9 as [(C0 & _ & U0)|(Cp & BI & BF & BJ & BC)]; [lia|].
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  assert (BIE : In (re_buf e1) (entry_blocks e1)).
  { unfold entry_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0)) by lia. left. reflexivity. }
  assert (BO : re_buf e1 <> OUT1) by (intros X; apply ON; rewrite <- X; apply in_or_app; left; exact BIE).
  set (Bl := firstn (Q - P + 1) (skipn P (re_U e1))).
  assert (LBl : length Bl = (Q - P + 1)%nat).
  { unfold Bl. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
  assert (BBl : bytes_at segs m1 (re_buf e1 + Z.of_nat P) Bl).
  { pose proof BS as T. rewrite <- (firstn_skipn P (re_U e1)) in T. apply bytes_at_app in T as [_ T].
    rewrite firstn_length_le in T by lia. rewrite <- (firstn_skipn (Q - P + 1) (skipn P (re_U e1))) in T.
    apply bytes_at_app in T as [T _]. exact T. }
  assert (ZBl : bzs Bl = dline s P Q ++ [0]).
  { unfold Bl. rewrite <- firstn_bzs, <- skipn_bzs, EW, (dW_split s P Q (proj1 HPQ) HQ), firstn_app.
    rewrite firstn_all2 by lia. rewrite LLN. replace (Q - P + 1 - (Q - P))%nat with 1%nat by lia. reflexivity. }
  pose proof HI1 as (HP1 & _ & _ & _ & _ & HN1 & HLB1 & _).
  assert (HN : dlno s P = NO + Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P)))) by exact HN1.
  assert (INL : In (dline s P Q) LS0) by exact (dline_in s D _ P Q RS1 HP1 DB HPQ HQ HNZ HK HL).
  pose proof (with_nul_in _ _ INL) as TOTL.
  assert (LVE : send_live cl (if send_off cl br (Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P)))) then br else dd)
                  dd (Z.of_nat (length (dline s P Q)) + 1) = LIVE).
  { apply CF.gestures_end_b.live_step2; [exact Hcl | exact Hbr | exact Hdd | lia | lia]. }
  rewrite EQ1 in TR1.
  destruct TR1 as (tp & qd & a & (LQ & WF1 & AOK & ROK & (DO1 & DE1 & DS1) & DKH1) & RFe & RFs & RFa).
  rewrite lsd_lrest in RFe, RFs, RFa. cbn [fst snd] in RFe, RFs, RFa.
  destruct (p3a_slt_wf LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) (nretF tp) (da_out a)
              (proj1 AOK)) as (WT1 & OK1).
  assert (WF2 : wf_from sptr 0 (tp ++ send_line_tr LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)
                                      (nretF tp) (da_out a))) by (apply p3a_wf_app; split; [exact WF1 | exact WT1]).
  pose proof RFe as RFe'. rewrite <- !app_assoc in RFe'. rewrite (app_assoc tp) in RFe'.
  pose proof (lsd_room_pre _ _ WF2 RFe') as RMp. clear RFe'.
  assert (LO : Z.of_nat (length O) = NO).
  { destruct OUTD as [(_ & _ & N0 & E0)|(_ & _ & _ & _ & _ & L0 & _)]; [rewrite E0; cbn [length Z.of_nat]; lia | exact L0]. }
  assert (LLB : Z.of_nat (length LB1) = Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P)))).
  { rewrite <- HLB1. unfold bzs. rewrite length_map. reflexivity. }
  assert (PK : exists (nc cc oc : word) (Oc jc : list byte),
    rw_cells segs m1 G_OUTV [C8 mx; C8 nc; C8 cc; C8 oc] /\ bv_unsigned oc = OUT1 /\ bv_unsigned nc < 2 ^ 47 /\
    ((bv_unsigned cc = 0 /\ bv_unsigned oc = 0 /\ bv_unsigned nc = 0 /\ Oc = []) \/
     (0 < bv_unsigned cc /\ bv_unsigned nc <= bv_unsigned cc /\ In (bv_unsigned oc, bv_unsigned cc) (blocks L1 A1) /\
      fresh_block Bm (bv_unsigned oc) (bv_unsigned cc) /\ bytes_at segs m1 (bv_unsigned oc) (Oc ++ jc) /\
      Z.of_nat (length Oc) = bv_unsigned nc /\ Z.of_nat (length jc) = bv_unsigned cc - bv_unsigned nc)) /\
    (LIVE = true -> bv_unsigned nc = dlno s P /\ bv_unsigned cc = dloc s P /\ Oc = O ++ LB1) /\
    (LIVE = false -> nc = nout /\ cc = cap /\ oc = out /\ Oc = O /\ jc = junk /\ dloc s P = CAP)).
  { destruct OU1 as (OF1 & OT1'). pose proof (bv_unsigned_in_range 64 nout) as RNO.
    change (bv_modulus 64) with (2 ^ 64) in RNO.
    destruct (Bool.bool_dec LIVE true) as [LV|LV].
    - destruct (OT1' LV) as (C1 & D1).
      exists (Z_to_bv 64 (dlno s P)), (Z_to_bv 64 (dloc s P)), (Z_to_bv 64 OUT1), (O ++ LB1), junk1.
      assert (NN : 0 <= dlno s P) by lia.
      split; [exact C1|].
      destruct D1 as [(Z1 & Z2 & Z3 & Z4 & Z5)|(Cp' & NL & I3 & F3' & B3 & LJ)].
      + assert (E1 : dloc s P = 0) by exact Z1. assert (E3 : dlno s P = 0) by exact Z3.
        rewrite E1, E3, Z2, Z4, Z5. rewrite !unsigned_lit by lia.
        split; [reflexivity|]. split; [lia|]. split; [left; repeat split; reflexivity|].
        split; [intros _; split; [reflexivity|]; split; reflexivity|].
        intros LF. rewrite LV in LF. discriminate.
      + assert (CP' : 0 < dloc s P) by exact Cp'.
        assert (NL' : dlno s P <= dloc s P) by exact NL.
        assert (I3' : In (OUT1, dloc s P) (blocks L1 A1)) by exact I3.
        assert (F3'' : fresh_block Bm OUT1 (dloc s P)) by exact F3'.
        assert (LJ' : Z.of_nat (length junk1) = dloc s P - dlno s P) by exact LJ.
        pose proof (blk_rng _ _ _ _ _ _ M1 I3') as BR3.
        rewrite !unsigned_lit by lia.
        split; [reflexivity|]. split; [lia|].
        split; [right; split; [lia|]; split; [exact NL'|]; split; [exact I3'|]; split; [exact F3''|];
                split; [rewrite <- app_assoc; exact B3|]; split; [rewrite length_app, Nat2Z.inj_add; lia | exact LJ']|].
        split; [intros _; split; [reflexivity|]; split; reflexivity|].
        intros LF. rewrite LV in LF. discriminate.
    - apply Bool.not_true_is_false in LV. destruct (OF1 LV) as (C1 & E1 & E2 & E3).
      exists nout, cap, out, O, junk.
      split; [exact C1|]. split; [symmetry; exact E1|].
      split; [destruct OUTD as [(_ & _ & N0 & _)|(_ & NL & I0 & _)]; [lia|];
              pose proof (blk_rng _ _ _ _ _ _ HM0 I0); lia|].
      split.
      { destruct OUTD as [Z0|(Cp' & NL & _ & F0 & _ & LO0 & LJ0)]; [left; exact Z0 | right].
        destruct (E3 Cp') as (I3 & B3).
        split; [exact Cp'|]. split; [exact NL|]. split; [exact I3|]. split; [exact F0|]. split; [exact B3|].
        split; [exact LO0 | exact LJ0]. }
      split; [intros LT; rewrite LV in LT; discriminate|].
      intros _. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity | exact E2]. }
  destruct PK as (nc & cc & oc & Oc & jc & COc & UOc & NCB & OUc & PKL & PKN). hide.
  assert (ESLt : forall jj oo,
    send_line_tr LIVE MX (bv_unsigned nc) (bv_unsigned cc) (Z.of_nat (length (dline s P Q)) + 1) jj oo =
    send_line_tr LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) jj oo).
  { intros jj oo. destruct (Bool.bool_dec LIVE true) as [LV|LV].
    - destruct (PKL LV) as (E1 & E2 & _). rewrite E1, E2. reflexivity.
    - apply Bool.not_true_is_false in LV. unfold send_line_tr. rewrite LV. reflexivity. }
  assert (ESLo : forall jj oo,
    send_line_out LIVE MX (bv_unsigned nc) (bv_unsigned cc) (Z.of_nat (length (dline s P Q)) + 1) jj oo =
    send_line_out LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) jj oo).
  { intros jj oo. destruct (Bool.bool_dec LIVE true) as [LV|LV].
    - destruct (PKL LV) as (E1 & E2 & _). rewrite E1, E2. reflexivity.
    - apply Bool.not_true_is_false in LV. unfold send_line_out. rewrite LV. reflexivity. }
  assert (HPo : LIVE = true -> dloc s P <> 0 -> resolveF qd (da_out a) = sptr_of L1 A1 (bv_unsigned oc)).
  { intros LV C. destruct (PKL LV) as (_ & EC & _).
    assert (CP : 0 < dloc s P)
      by (destruct OUc as [(Z0 & _)|(Cp' & _)]; [clear - Z0 EC C; lia | clear - Cp' EC; lia]).
    destruct (DO1 LV CP) as [Hin Ha]. rewrite UOc, <- Ha. symmetry. exact (p3a_sptr_of_eq L1 A1 _ _ ND1 Hin). }
  assert (HE2 : forall x, bv_unsigned oc <= x < bv_unsigned oc + bv_unsigned cc ->
                  x < YM05.alloc_ceiling /\ ~ in_img Bm x).
  { intros x Hx. destruct OUc as [(Z0 & _)|(Cp' & _ & _ & (FQ1 & FQ2 & FQ3) & _)]; [lia|].
    split; [lia|]. replace x with (bv_unsigned oc + (x - bv_unsigned oc)) by lia. apply FQ3. lia. }
  destruct GL1 as (CCL1 & CBR1 & CDD1 & CEI1 & (ev1 & CER1)).
  pose proof RT1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  assert (U2 : bv_unsigned (getr R1 2) = S0 - 144) by (rewrite H2; apply unsigned_lit; lia).
  assert (U10 : bv_unsigned (getr R1 10) = re_buf e1 + Z.of_nat P) by (rewrite G10; apply unsigned_lit; lia).
  assert (U11 : bv_unsigned (getr R1 11) = Z.of_nat (length (dline s P Q)) + 1) by (rewrite G11; apply unsigned_lit; lia).
  pose proof SLC as SL. unfold send_line_contract in SL.
  specialize (SL L1 A1 R1 m1 md1 (runF F qd bnd tp) Bl Oc jc cl
                (if send_off cl br (Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P)))) then br else dd) dd
                (if send_off cl br (Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P)))) then ei else 0)
                mx nc cc oc ev1).
  cbv zeta in SL. unfold known_at in SL. rewrite U2, U10, U11, G1, LVE in SL.
  eapply SR_mono.
  { apply SL; clear SL.
    - exact SEGS.
    - apply (pre_send L1 A1 m1 md1 R1 RP1 IN1); [exact H2 | exact H4 | rewrite G1; exact ret_ok_13be4].
    - exact IN1.
    - exact TPE.
    - exact ERR4.
    - unfold G_RELAY_HI, G_LOCK_HI in *. lia.
    - exact RO1.
    - exact BBl.
    - lia.
    - destruct (fsep (re_buf e1) (re_cap e1) G_RELAY_LO G_RELAY_HI BF ltac:(lia) ltac:(unfold G_RELAY_LO, G_RELAY_HI; lia)
                (fun a Ha => proj1 (GRP a ltac:(unfold G_RELAY_LO, G_RELAY_HI, G_S, SRC_SIZE, SOURCES_MAX in *; lia))))
        as [X|X]; [left | right]; lia.
    - destruct (fsep (re_buf e1) (re_cap e1) ERR (ERR + 4) BF ltac:(lia) ltac:(lia) GEI) as [X|X]; [left | right]; lia.
    - left. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. lia.
    - intros a0 Ha. apply GRP. unfold G_RELAY_LO, G_RELAY_HI, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - exact GCP.
    - exact GEI.
    - right. exists (re_buf e1), (re_cap e1). split; [exact BI|]. split; [lia|]. split; [lia|]. rewrite UOc. exact BO.
    - exact Hcl.
    - destruct (send_off _ _ _); [exact Hbr | exact Hdd].
    - exact Hdd.
    - destruct (send_off _ _ _); [exact Hei | left; reflexivity].
    - exact CCL1.
    - exact CBR1.
    - exact CDD1.
    - exact CEI1.
    - exact COc.
    - exact CER1.
    - destruct OUc as [Z0|(Cp' & NL & I3 & F3' & B3 & LO' & LJ')]; [left; exact Z0 | right].
      split; [exact Cp'|]. split; [exact NL|]. split; [exact I3|]. split; [exact F3'|]. split; [exact B3|].
      split; [exact LO'|]. split; [exact LJ'|].
      rewrite UOc in I3 |- *. destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 BI I3 BO) as [X|X]; [left | right]; lia.
    - pose proof LL6000. lia.
    - exact ROK.
    - rewrite ESLt.
      exact (lsd_room bnd tp qd (da_out a) LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)
               (sptr_of L1 A1 (bv_unsigned oc)) WF1 (proj1 AOK) LQ HPo RMp). }
  intros c' (L2 & A2 & R2 & m2 & md2 & OUT' & CAP' & junk' & -> & RP2 & IN2 & (qs & LQs & ROK2 & LO2) & RO2 & XB2 &
    CCL2 & CBR2 & CDD2 & CEI2 & NL2 & LV2). clear SL.
  rewrite ESLt in LQs, ROK2. rewrite ESLo in LO2. hide.
  destruct (lsd_run bnd tp qd qs (da_out a) LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)
              (sptr_of L1 A1 (bv_unsigned oc)) WF1 (proj1 AOK) LQ HPo) as (N2 & RN2 & FO2).
  pose proof RP2 as (M2 & W2 & _ & _ & _ & _ & _ & _ & _ & RPr2 & _).
  pose proof (NODUP _ _ _ _ M2) as ND2.
  assert (PR : forall r, callee_saved r -> getr R2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)) by exact RPr2.
  assert (RT2 : RTL R2).
  { unfold RTL, RTK, RT. split; [split; [|split]|].
    - split; [UH_pr PR 2 H2|]. split; [UH_pr PR 3 H3|]. split; [UH_pr PR 4 H4|]. split; [UH_pr PR 8 H8|].
      split; [UH_pr PR 22 H22 | UH_pr PR 25 H25].
    - UH_pr PR 23 H23.
    - UH_pr PR 26 H26.
    - UH_pr PR 27 H27. }
  assert (G9' : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by UH_pr PR 9 G9.
  assert (G18' : getr R2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by UH_pr PR 18 G18.
  assert (SPR1 : spZ R1 = S0 - 144) by exact U2.
  assert (RPc : relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 regs m2 md2).
  { eapply (sb_comp Bm API).
    all: try first [exact RP1 | exact RP2 | exact AX | exact CTX | exact EU | exact BW | exact SEGS].
    - intros a0 Ha. change (spZ regs) with S0 in Ha.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. lia.
    - intros a0 [X|X]; [left | right; exact X]. rewrite SPR1 in X. change (spZ regs) with S0.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *. lia.
    - intros a0 [X|X] Hn Y; [|exfalso; apply Hn; right; exact X]. cbv beta in Y.
      change (spZ regs) with S0 in X.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in X.
      unfold send_writes, G_BROKEN, G_EINTR, G_OUTV in Y.
      destruct Y as [Y|[Y|[Y|(_ & Y)]]]; [lia | lia | lia | destruct (HE2 a0 Y); lia].
    - intros p n Hp Hp1 Hn NF E. cbv beta in NF, E. destruct E as (LVt & E).
      assert (QB : In (ptr_addr L p, n) (blocks L A))
        by (apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
      rewrite UOc in E.
      assert (NO1 : ptr_addr L p <> OUT) by (intros X; apply NF; left; split; [exact LVt | exact X]).
      assert (NI1 : ~ In (ptr_addr L p) (entry_blocks e ++ hs_blocks h)) by (intros X; apply NF; right; exact X).
      destruct (BK5 _ _ QB Hn NO1 NI1) as (X & _). exact (X E).
    - intros a0 Ha _ _ Y. cbv beta in Y |- *.
      unfold send_writes in Y. destruct Y as [Y|[Y|[Y|(LVt & Y)]]].
      + left. unfold send_writes. left. exact Y.
      + left. unfold send_writes. right. left. exact Y.
      + left. unfold send_writes. right. right. left. exact Y.
      + exfalso. destruct (HE2 a0 Y) as [Y1 Y2]. destruct Ha as [Ha|Ha]; [lia | exact (Y2 Ha)].
    - intros p n i Hp Hp1 NF Hi Y. cbv beta in Y, NF |- *.
      unfold send_writes in Y. destruct Y as [Y|[Y|[Y|(LVt & Y)]]];
        [left; unfold send_writes; left; exact Y | left; unfold send_writes; right; left; exact Y |
         left; unfold send_writes; right; right; left; exact Y |].
      exfalso.
      assert (QB : In (ptr_addr L p, n) (blocks L A))
        by (apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
      assert (NO1 : ptr_addr L p <> OUT) by (intros X; apply NF; left; split; [exact LVt | exact X]).
      assert (NI1 : ~ In (ptr_addr L p) (entry_blocks e ++ hs_blocks h)) by (intros X; apply NF; right; exact X).
      destruct (BK5 _ _ QB ltac:(lia) NO1 NI1) as (X & _).
      pose proof (BK3 _ _ QB NO1 NI1) as QB1.
      destruct OUc as [(Z0 & _)|(Cp' & _ & I3 & _)]; [lia|]. rewrite UOc in I3, Y.
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 QB1 I3 X); lia. }
  assert (TR2 : forall OUT2, (LIVE = true -> OUT2 = OUT') ->
    MTR s L2 A2 (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)) e1 h1 OUT2
      (srest (dlH s P) (dlka s P) (dline s P Q) (dlno s P + Z.of_nat (length (dline s P Q)) + 1)
         (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)) (drlq s (S Q)))).
  { intros OUT2 EO2.
    exists (tp ++ send_line_tr LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) (nretF tp) (da_out a)),
      (qd ++ qs),
      (DA (send_line_out LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) (nretF tp) (da_out a))
          (da_buf a) (da_hp a) (da_keys a) (da_pend a) (da_ev a) (da_erecs a)).
    split.
    - split; [rewrite length_app, N2, LQs; reflexivity|].
      split; [exact WF2|].
      split; [apply (lsd_dadr (nretF tp)); [exact AOK | rewrite nret_app; apply Nat.le_add_r | rewrite nret_app; exact OK1]|].
      split; [rewrite RN2; exact ROK2|].
      split; [|exact DKH1].
      split.
      + intros LV CP. rewrite (EO2 LV). cbn [da_out].
        destruct (PKL LV) as (EN & EC & _). destruct (LV2 LV) as (_ & ECAP & _).
        assert (ECP : send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) = CAP')
          by (rewrite ECAP, EN, EC; reflexivity).
        rewrite (FO2 LV ltac:(clear - CP; lia)), ECP. exact (LO2 LV).
      + apply (lsd_links _ _ _ _ _ _ _ _ _ _ _ _ _ qd qs a _ e1 h1 W1 RP2); try reflexivity.
        * intros q Hq Y. cbv beta in Y. destruct Y as (_ & X). rewrite UOc in X. apply ON. rewrite <- X. exact Hq.
        * rewrite LQ. exact AOK.
        * exact DE1.
        * exact DS1.
    - unfold RFUT. cbn [da_out da_hp da_keys]. rewrite !nret_app. rewrite <- (app_assoc tp).
      rewrite nret_app, Nat.add_assoc in RFe, RFs, RFa.
      split; [exact RFe|]. split; [exact RFs | exact RFa]. }
  pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as MS.
  match type of MS with msame ?Pa0 _ _ => set (Pa := Pa0) in MS end.
  assert (NSW_hi : forall a0, YM05.alloc_ceiling <= a0 -> ~ send_writes LIVE (bv_unsigned oc) (bv_unsigned cc) a0).
  { intros a0 Ha Y. unfold send_writes, G_BROKEN, G_EINTR, G_OUTV in Y.
    destruct Y as [Y|[Y|[Y|(_ & Y)]]]; [lia | lia | lia | destruct (HE2 a0 Y); lia]. }
  assert (NSW_blk : forall q k a0, In (q, k) (blocks L1 A1) -> (LIVE = true -> q <> OUT1) -> q <= a0 < q + k ->
                      ~ send_writes LIVE (bv_unsigned oc) (bv_unsigned cc) a0).
  { intros q k a0 Hq Hne Ha Y. pose proof (blk_noimg _ _ _ _ _ _ (a0 - q) M1 Hq ltac:(lia)) as NI.
    replace (q + (a0 - q)) with a0 in NI by lia.
    unfold send_writes in Y. destruct Y as [Y|[Y|[Y|(LVt & Y)]]].
    - apply NI. exact (proj1 (GRP a0 ltac:(unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    - apply NI. exact (proj1 (GRP a0 ltac:(unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    - apply NI. exact (proj1 (GRP a0 ltac:(unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
    - destruct OUc as [(Z0 & _)|(Cp' & _ & I3 & _)]; [lia|]. rewrite UOc in I3, Y.
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq I3 (Hne LVt)); lia. }
  assert (NSW_img : forall a0, G_S <= a0 < G_S + SRC_SIZE * SOURCES_MAX ->
                      ~ send_writes LIVE (bv_unsigned oc) (bv_unsigned cc) a0).
  { intros a0 Ha Y. unfold send_writes in Y.
    destruct Y as [Y|[Y|[Y|(_ & Y)]]]; [unfold G_BROKEN, G_S in *; lia | unfold G_EINTR, G_S in *; lia |
                                       unfold G_OUTV, G_S in *; lia |].
    destruct (HE2 a0 Y) as [_ Y2]. apply Y2.
    exact (proj1 (GRP a0 ltac:(unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))). }
  assert (PF : forall a0, S0 - 144 <= a0 < S0 -> Pa a0).
  { intros a0 Ha. unfold Pa. left. split; [left; lia|].
    split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M1 Ho); lia|].
    split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M2 Ho); lia|].
    split; [unfold scratch_k; rewrite SPR1; unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK;
            intros [X|X]; lia|].
    apply NSW_hi. lia. }
  assert (PIm : forall a0, G_S <= a0 < G_S + SRC_SIZE * SOURCES_MAX -> Pa a0).
  { intros a0 Ha. pose proof (GRP a0 ltac:(unfold G_RELAY_LO, G_S in *; lia)) as IP.
    unfold Pa. left. split; [right; exact (proj1 IP)|].
    split; [exact (img_unowned _ _ _ _ _ M1 IP)|]. split; [exact (img_unowned _ _ _ _ _ M2 IP)|].
    split; [|exact (NSW_img a0 Ha)].
    pose proof (img_lo a0 (proj1 IP)) as IL. destruct IP as (_ & _ & _ & IE).
    unfold scratch_k. rewrite SPR1. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    intros [X|X]; [lia | exact (IE X)]. }
  assert (PBk : forall q k a0, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) -> q <= a0 < q + k ->
                  Pa a0).
  { intros q k a0 Hq Hi Ha. assert (Hne : q <> OUT1) by (intros ->; exact (ON Hi)).
    unfold Pa. right. exists q, k. split; [exact Hq|]. split; [lia|].
    split; [rewrite UOc; intros (_ & X); exact (Hne X)|]. split; [exact Ha|].
    exact (NSW_blk q k a0 Hq (fun _ => Hne) Ha). }
  assert (PSv : forall q k, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) ->
                  In (q, k) (blocks L2 A2)).
  { intros q k Hq Hi. apply (rp_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W1 RP2 Hq). intros _ X. cbv beta in X.
    destruct X as (_ & X). rewrite UOc in X. apply ON. rewrite <- X. exact Hi. }
  destruct (core_tr L1 A1 m1 L2 A2 m2 e1 h1 Pa MS FR1 EK1 SR1 OT1 PF PIm PSv PBk) as (FR2 & EK2 & SR2 & OT2).
  assert (SAC2 : rw_cells segs m2 SA [CB 56%nat (entry_bytes e1)]).
  { eapply rw_tr; [exact MS | exact SAC1 |]. intros a0 Ha. cbn [cells_size csize] in Ha.
    unfold Pa. right. exists G, SRC_TABLE. split; [exact GI|]. split; [unfold SRC_TABLE, SRC_ENTRY; lia|].
    split; [rewrite UOc; intros (_ & X); exact (GO X)|]. split; [unfold SRC_TABLE, SRC_ENTRY; lia|].
    exact (NSW_blk G SRC_TABLE a0 GI (fun _ => GO) ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)). }
  assert (GI2 : In (G, SRC_TABLE) (blocks L2 A2)).
  { apply (rp_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W1 RP2 GI). intros _ X. cbv beta in X. destruct X as (_ & X).
    rewrite UOc in X. exact (GO X). }
  assert (LK2 : DLINK (dvirt s false (dlH s P) (dlka s P) (dlno s P + Z.of_nat (length (dline s P Q)) + 1)
                  (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1))) e1 h1).
  { rewrite HK in LK1. exact LK1. }
  assert (NB2 : Z.of_nat (length (dlH s P)) + Z.of_nat (S (length (drlq s (S Q)))) +
                Z.of_nat (length (pstream (dvirt s false (dlH s P) (dlka s P)
                   (dlno s P + Z.of_nat (length (dline s P Q)) + 1)
                   (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1))))) < 2 ^ 26).
  { rewrite EQ1 in NB1. exact NB1. }
  assert (WNE : with_nul (lines ST0 D ++ drlp s P ++ [dline s P Q]) =
                with_nul (lines ST0 D ++ drlp s P) ++ dline s P Q ++ [0]).
  { rewrite (app_assoc (lines ST0 D) (drlp s P) [dline s P Q]), (with_nul_app (lines ST0 D ++ drlp s P) [dline s P Q]),
      with_nul_one. reflexivity. }
  assert (HI2 : DHISTg (lines ST0 D ++ drlp s P ++ [dline s P Q]) (lines ST0 D ++ drlp s P) (D ++ ddata s)
                  (dvirt s false (dlH s P) (dlka s P) (dlno s P + Z.of_nat (length (dline s P Q)) + 1)
                     (send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1)))
                  h1 (LB1 ++ Bl)).
  { destruct HI1 as (_ & HR1 & HX1 & HX2 & HX3 & _ & _ & HD1 & HS1 & HE1).
    split; [exact HP1|]. split; [exact HR1|]. split; [exact HX1|]. split; [exact HX2|]. split; [exact HX3|].
    split.
    { cbn [ds_no dvirt]. rewrite HN, WNE, !length_app. cbn [length]. lia. }
    split.
    { assert (BA : bzs (LB1 ++ Bl) = bzs LB1 ++ bzs Bl) by (unfold bzs; apply map_app).
      rewrite BA, HLB1, ZBl, WNE. reflexivity. }
    split; [exact HD1|]. split; [exact HS1 | exact HE1]. }
  assert (TOTE : Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P ++ [dline s P Q]))) =
                 Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P))) + (Z.of_nat (length (dline s P Q)) + 1)).
  { rewrite WNE, !length_app. cbn [length]. lia. }
  assert (GL2 : DGLBg (Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P ++ [dline s P Q])))) m2).
  { unfold DGLBg. rewrite TOTE.
    rewrite (CF.gestures_end_b.br_step2 cl br dd (Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P))))
               (Z.of_nat (length (dline s P Q)) + 1) Hcl Hbr Hdd ltac:(lia) ltac:(lia)) in CBR2.
    rewrite (CF.gestures_end_b.ei_step2 cl br dd ei (Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P))))
               (Z.of_nat (length (dline s P Q)) + 1) Hcl Hbr Hdd ltac:(lia) ltac:(lia)) in CEI2.
    split; [exact CCL2|]. split; [exact CBR2|]. split; [exact CDD2|]. split; [exact CEI2|].
    destruct (Bool.bool_dec LIVE true) as [LV|LV].
    - destruct (LV2 LV) as (_ & _ & _ & (ev2 & CE2) & _). exists ev2. exact CE2.
    - apply Bool.not_true_is_false in LV. destruct (NL2 LV) as (_ & CE2 & _). eexists. exact CE2. }
  assert (LIV : forall q, In q (entry_blocks e1 ++ hs_blocks h1) -> exists k, In (q, k) (blocks L1 A1)).
  { intros q Hq. apply in_app_or in Hq as [Hq|Hq];
      [exact (eb_livex _ _ _ _ _ EK1 Hq) | exact (hb_live _ _ _ _ _ _ SR1 Hq)]. }
  assert (BK3' : forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
                   In (q, m) (blocks L2 A2)).
  { intros q m Hq Q1 Q2. apply (rp_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W1 RP2 (BK3 q m Hq Q1 Q2)).
    intros Mp X. cbv beta in X. destruct X as (_ & X). rewrite UOc in X. destruct (BK5 q m Hq Mp Q1 Q2) as (Y & _).
    exact (Y X). }
  destruct (Bool.bool_dec LIVE true) as [LV|LV].
  - destruct (PKL LV) as (EN & EC & EO).
    destruct (LV2 LV) as (NLE & ECAP & FRS & _ & FSV & (b1 & b2 & c1 & c2 & EB2 & EBC & EB1) & OB2 & LJ2 & COV2).
    assert (OUTB : In (OUT', CAP') (blocks L2 A2)) by (rewrite EB2; apply in_or_app; right; left; reflexivity).
    assert (CAPP : 0 < CAP') by (pose proof (bv_unsigned_in_range 64 nc); lia).
    assert (QO' : forall q k, In (q, k) (blocks L1 A1) -> q <> OUT1 -> In (q, k) (blocks L2 A2) -> q <> OUT').
    { intros q k Hq Hne Hq2 E. destruct (Z_lt_le_dec 0 k) as [Kp|Kn].
      - exact (FSV q k Hq ltac:(rewrite UOc; exact Hne) Kp E).
      - subst q. pose proof (CF.gestures_end_b.nodup_fst _ OUT' k CAP' ND2 Hq2 OUTB). lia. }
    exists R2, L2, A2, m2, md2, e1, h1, OUT', junk', (LB1 ++ Bl), D.
    split; [reflexivity|]. split; [exact RT2|]. split; [exact G9'|]. split; [exact G18'|].
    split; [exact DB|]. split; [exact HPQ|]. split; [exact HQ|]. split; [exact HNZ|]. split; [exact HK|].
    split; [exact HL|].
    split; [exact RPc|]. split; [exact IN2|]. split; [exact (TR2 OUT' (fun _ => eq_refl))|]. split; [exact RO2|].
    split; [exact FR2|].
    split; [exact SAC2|]. split; [exact EK2|]. split; [exact SR2|]. split; [exact OT2|]. split; [exact SM1|].
    split; [exact LK2|]. split; [exact HI2|]. split; [exact NB2|]. split; [exact RS1|].
    split.
    { split.
      { apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
        apply List.NoDup_cons_iff in ND as [_ ND']. apply List.NoDup_cons_iff in ND' as [_ ND'].
        constructor; [|constructor; [|exact ND']].
        - intros [X|X]; [exact (QO' G SRC_TABLE GI GO GI2 (eq_sym X)) | exact (GN X)].
        - intros X. destruct (LIV _ X) as (k & Hk).
          assert (Hne : OUT' <> OUT1) by (intros E; apply ON; rewrite <- E; exact X).
          exact (QO' OUT' k Hk Hne (PSv _ _ Hk X) eq_refl). }
      split; [exact GI2|]. split; [exact BK3'|].
      split.
      { intros q m Hq. rewrite EB2 in Hq. apply CF.gestures_end_b.in_mid_iff in Hq. destruct Hq as [Hq|E].
        - rewrite EBC in Hq.
          assert (Hq1 : In (q, m) (blocks L1 A1) /\ q <> OUT1).
          { destruct EB1 as [(C0' & E1)|(Cp' & E1)].
            - rewrite <- E1 in Hq. split; [exact Hq|]. intros ->.
              destruct OUc as [(_ & Z2 & _)|(Cp'' & _)]; [|lia]. rewrite UOc in Z2.
              pose proof (blk_rng _ _ _ _ _ _ M1 Hq). lia.
            - pose proof (CF.gestures_end_b.rm_in _ b1 b2 (bv_unsigned oc, bv_unsigned cc) (q, m) ND1 E1) as R.
              cbn [fst] in R. apply R in Hq. destruct Hq as [Q1 Q2]. split; [exact Q1 | rewrite <- UOc; exact Q2]. }
          destruct Hq1 as [Q1 Q2].
          destruct (BK4 q m Q1) as [X|[X|X]]; [left; exact X | right; left; exact X | exfalso; exact (Q2 X)].
        - injection E as E1 E2. subst q m. right. right. reflexivity. }
      intros q m Hq Hm Q1 Q2. destruct (BK5 q m Hq Hm Q1 Q2) as (X1 & X2 & X3).
      split; [|split; [exact X2 | exact X3]].
      exact (FSV q m (BK3 q m Hq Q1 Q2) ltac:(rewrite UOc; exact X1) Hm). }
    split; [exact GL2|].
    split; [intros LF; rewrite LV in LF; discriminate|].
    intros _. cbn [ds_no ds_ocap dvirt].
    assert (ENO : dlno s P + Z.of_nat (length (dline s P Q)) + 1 =
                  bv_unsigned nc + (Z.of_nat (length (dline s P Q)) + 1)) by lia.
    assert (ECP : send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1) = CAP')
      by (rewrite ECAP, EN, EC; reflexivity).
    rewrite ENO, ECP. split; [exact COV2|].
    right. split; [lia|]. split; [lia|]. split; [exact OUTB|]. split; [exact FRS|].
    split; [rewrite EO in OB2; rewrite <- !app_assoc in OB2 |- *; exact OB2 | lia].
  - apply Bool.not_true_is_false in LV.
    destruct (PKN LV) as (EN & EC & EO & EOc & EJ & ECP). subst nc cc oc Oc jc.
    destruct (NL2 LV) as (EBL & _ & COV2).
    exists R2, L2, A2, m2, md2, e1, h1, OUT1, junk1, (LB1 ++ Bl), D.
    split; [reflexivity|]. split; [exact RT2|]. split; [exact G9'|]. split; [exact G18'|].
    split; [exact DB|]. split; [exact HPQ|]. split; [exact HQ|]. split; [exact HNZ|]. split; [exact HK|].
    split; [exact HL|].
    split; [exact RPc|]. split; [exact IN2|].
    split; [apply TR2; intros LT; rewrite LV in LT; discriminate|]. split; [exact RO2|]. split; [exact FR2|].
    split; [exact SAC2|]. split; [exact EK2|]. split; [exact SR2|]. split; [exact OT2|]. split; [exact SM1|].
    split; [exact LK2|]. split; [exact HI2|]. split; [exact NB2|]. split; [exact RS1|].
    split.
    { split; [exact ND|]. split; [exact GI2|]. split; [exact BK3'|].
      split; [intros q m Hq; rewrite EBL in Hq; exact (BK4 q m Hq) | exact BK5]. }
    split; [exact GL2|].
    split.
    + intros _. cbn [ds_no ds_ocap dvirt]. split; [exact COV2|]. split; [symmetry; exact UOc|].
      split; [unfold send_line_cap; rewrite LV; exact ECP|].
      intros CpO. destruct OUc as [(Z0 & _)|(_ & _ & I3 & _ & B3 & LO' & LJ')]; [lia|].
      split; [rewrite EBL; exact I3|].
      eapply by_tr; [exact MS | exact B3 |]. intros a0 Ha. unfold Pa. right.
      exists (bv_unsigned out), (bv_unsigned cap). split; [exact I3|]. split; [lia|].
      split; [intros (LT & _); rewrite LV in LT; discriminate|].
      split; [rewrite length_app in Ha; lia|].
      apply (NSW_blk _ _ a0 I3); [intros LT; rewrite LV in LT; discriminate | rewrite length_app in Ha; lia].
    + intros LT. rewrite LV in LT. discriminate.
Qed.

Lemma UC_memchr : forall R1 m1 md1 (a0 n : Z) (bs : list byte) (Pc : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> ro_agree segs m1 ->
  getr R1 10 = Z_to_bv 64 a0 -> getr R1 11 = Z_to_bv 64 0 -> getr R1 12 = Z_to_bv 64 n ->
  bytes_at segs m1 a0 bs -> Z.of_nat (length bs) = n -> a0 + n < 2 ^ 64 ->
  (forall R2, getr R2 1 = getr R1 1 -> getr R2 2 = getr R1 2 -> getr R2 3 = getr R1 3 ->
     getr R2 4 = getr R1 4 -> getr R2 8 = getr R1 8 -> getr R2 18 = getr R1 18 -> getr R2 19 = getr R1 19 ->
     getr R2 20 = getr R1 20 -> getr R2 22 = getr R1 22 -> getr R2 23 = getr R1 23 -> getr R2 25 = getr R1 25 ->
     getr R2 26 = getr R1 26 -> getr R2 27 = getr R1 27 ->
     getr R2 10 = Z_to_bv 64 (match StrFun.find_byte 0 bs with Some i => a0 + Z.of_nat i | None => 0 end) ->
     SR segs (mkCfg (YK11.mkst R2 (ret_pc (getr R1 1)) m1 (seg_rom segs)) md1) Pc) ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 MEMCHR) m1 (seg_rom segs)) md1) Pc.
Proof using HG HJ MCH O SEGS h junk.
  intros R1 m1 md1 a0 n bs Pc Hh Hl RO G10 G11 G12 BS LN BND K.
  pose proof BS as (B0 & _).
  rewrite SEGS in RO, BS.
  pose proof MCH as MC. unfold memchr_contract in MC.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G10, G11, G12. rewrite SEGS.
    apply (evt_normalize rsegs); [exact dl_wx | exact RO |].
    apply MC with (buf := bs).
    - rewrite unsigned_lit by lia. exact (bytes_at_normalize rsegs m1 a0 bs RO BS).
    - rewrite !unsigned_lit by lia. unfold StrFun.memchr_ok. rewrite firstn_all2 by lia.
      destruct (StrFun.find_byte (0 mod 256) bs); [left|]; lia.
    - apply mem_inv_normalize. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & -> &
    MU1' & _ & _ & _).
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m2 eqn:Em2. subst can1. clear Em2.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m1 RO) HR1 ROS1 MU1') as MU1.
  assert (ME : m2 = m1).
  { apply FunctionalExtensionality.functional_extensionality. intros x. apply MU1. exact I. }
  subst m2.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  apply K; try rgw X2.
  rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs.
  rewrite !unsigned_lit by lia. unfold StrFun.memchr_res. rewrite firstn_all2 by lia. reflexivity.
Qed.

Lemma next_step : forall s P c, DLN s P c -> SR segs c (fun c' => (exists Q, DLL s P Q c') \/ DLR s P c').
Proof using All.
  intros s P c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RTL1 & G18 & DB & DLC1).
  pose proof DLC1 as (RP1 & _ & _ & RO1 & FR1 & SAC1 & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof EK1 as (_ & K2 & K3 & K4 & _).
  pose proof DB as (DB1 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). hide.
  pose proof HG as (_ & GF & _).
  assert (RO1' : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & _).
  destruct (dr_cut m1 (SA + 16) (SA + 32) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 (re_used e1))]
              [C8 (Z_to_bv 64 (re_cap e1))] EC2 ltac:(cbn [cells_size csize]; lia)) as [EC3 _].
  destruct (dr_cut m1 SA (SA + 8) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1))]
              [C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)] EC1 eq_refl) as [_ EB].
  destruct (dr_cut m1 (SA + 8) (SA + 12) [C4 (Z_to_bv 64 (re_skip e1))] [CB 4 (re_pad1 e1)] EB
              ltac:(cbn [cells_size csize]; lia)) as [ES _].
  destruct FR1 as (j0 & j1 & j2 & j4 & FRc). rewrite SEGS in FRc.
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 24) [CB 8 j0; CB 8 j1; CB 8 j2]
              ([C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED) FRc ltac:(cbn [cells_size csize]; lia)) as [_ FRd].
  destruct (dr_cut m1 (S0 - 144 + 24) (S0 - 144 + 32) [C8 (Z_to_bv 64 6001)] ([CB 8 j4] ++ SAVED) FRd
              ltac:(cbn [cells_size csize]; lia)) as [C6k _].
  assert (NIG : forall a, G <= a < G + SRC_TABLE -> ~ in_img Bm a).
  { intros a Ha Hi. destruct GF as (_ & _ & GF3). apply (GF3 (a - G)); [lia|].
    replace (G + (a - G)) with a by lia. exact Hi. }
  assert (ESn : rw_cells rsegs (normalize rsegs m1) (SA + 8) [C4 (Z_to_bv 64 (re_skip e1))]).
  { apply sb_rw_norm; [exact RO1' | exact ES |]. intros i Hi. cbn [cells_size csize] in Hi.
    apply ro_off; [lia|]. apply NIG. unfold SRC_TABLE, SRC_ENTRY. lia. }
  assert (C6n : rw_cells rsegs (normalize rsegs m1) (S0 - 144 + 24) [C8 (Z_to_bv 64 6001)]).
  { apply sb_rw_norm; [exact RO1' | exact C6k |]. intros i Hi. cbn [cells_size csize] in Hi. apply sb_ro_ge. lia. }
  assert (SK : 0 <= re_skip e1 < 2 ^ 31) by (destruct K2 as [E|E]; rewrite E; lia).
  pose proof RTL1 as (((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26) & G27).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G8, G18. rewrite SEGS.
    eapply dr_line; [exact EC3 | lia | lia | lia]. }
  intros ms (can & -> & EQ).
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  assert (Y1 : getr R2 1 = Z_to_bv 64 0x13bac) by rgw X2.
  assert (Y10 : getr R2 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  assert (Y11 : getr R2 11 = Z_to_bv 64 0) by rgw X2.
  assert (Y12 : getr R2 12 = Z_to_bv 64 (re_used e1 - Z.of_nat P)).
  { rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. f_equal. lia. }
  assert (Y18 : getr R2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  assert (Y19 : getr R2 19 = Z_to_bv 64 (re_buf e1)) by rgw X2.
  assert (Y20 : getr R2 20 = Z_to_bv 64 (Z.of_nat (length (dW s) - P))).
  { rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. f_equal. lia. }
  assert (BS' : bytes_at segs m1 (re_buf e1 + Z.of_nat P) (skipn P (re_U e1))).
  { pose proof BS as T. rewrite <- (firstn_skipn P (re_U e1)) in T. apply bytes_at_app in T as [_ T].
    rewrite firstn_length_le in T by lia. exact T. }
  apply (UC_memchr R2 m1 md1 (re_buf e1 + Z.of_nat P) (re_used e1 - Z.of_nat P) (skipn P (re_U e1)));
    [exact Hh | exact Hl | exact RO1 | exact Y10 | exact Y11 | exact Y12 | exact BS' | rewrite length_skipn; lia |
     lia |].
  intros R3 E1 E2 E3 E4 E8 E18 E19 E20 E22 E23 E25 E26 E27 E10.
  rewrite Y1, ret_pc_13bac.
  assert (RTL3 : RTL R3)
    by (unfold RTL, RTK, RT; rewrite E2, E3, E4, E8, E22, E23, E25, E26, E27; exact RTL2).
  pose proof RTL3 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  revert E10. destruct (StrFun.find_byte 0 (skipn P (re_U e1))) as [i|] eqn:FB; intros E10.
  - destruct (fb_skip_some s (re_U e1) P i EW FB) as (IL & IZ & IM).
    apply SR_ret. left. exists (P + i)%nat, R3, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D.
    split; [reflexivity|]. split; [exact RTL3|].
    split; [rewrite E10; f_equal; lia|]. split; [rewrite E18; exact Y18|].
    split; [exact DB|]. split; [lia|]. split; [exact IZ|]. split; [exact IM|]. exact DLC1.
  - eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, H2, H8, E10, E18, Y18. rewrite SEGS.
      apply (evt_normalize rsegs); [exact dl_wx | exact RO1' |].
      eapply dr_hit; [exact ESn | exact C6n | apply mem_inv_normalize | exact SK | lia | lia | intros X; lia]. }
    intros ms (can & (s0 & [(_ & ->)|[(R0 & _)|(R0 & _)]] & REL & ROS) & EQ4);
      [| exfalso; exact (R0 eq_refl) | exfalso; exact (R0 eq_refl)].
    destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
    remember (ms_mem can) as m2 eqn:Em2. subst can. clear Em2.
    pose proof (mem_back m1 m2 HR ROS) as ME. subst m2.
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply SR_ret. right. exists R4, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D.
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X4|].
    split; [rgw X4|]. split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity; simp_regs;
                              rewrite E19; exact Y19|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity; simp_regs; rewrite E20; exact Y20|].
    split; [exact DB|]. split; [exact (fb_skip_none s (re_U e1) P EW FB)|]. exact DLC1.
Qed.

Lemma scan_start : forall s c, DHQ s c -> SR segs c (fun c' => (exists Q, DLL s 0 Q c') \/ DLR s 0 c').
Proof using All.
  intros s c H. exact (next_step s 0 c H).
Qed.

Lemma line_test : forall s P Q c, DLL s P Q c -> SR segs c (fun c' => DLS s P Q c' \/ DLN s (S Q) c').
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RTL1 & G10 & G18 & DB & HPQ & HQ &
    HNZ & DLC1).
  pose proof DLC1 as (RP1 & _ & _ & RO1 & FR1 & SAC1 & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof EK1 as (_ & K2 & K3 & K4 & _).
  pose proof LK1 as (_ & _ & L3c & _).
  assert (L3' : re_skip e1 = if dskp s P then 1 else 0) by exact L3c.
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). hide.
  pose proof HG as (_ & GF & _).
  assert (RO1' : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & _ & _).
  destruct (dr_cut m1 SA (SA + 8) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1))]
              [C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)] EC1 eq_refl) as [_ EB].
  destruct (dr_cut m1 (SA + 8) (SA + 12) [C4 (Z_to_bv 64 (re_skip e1))] [CB 4 (re_pad1 e1)] EB
              ltac:(cbn [cells_size csize]; lia)) as [ES _].
  destruct FR1 as (j0 & j1 & j2 & j4 & FRc). rewrite SEGS in FRc.
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 24) [CB 8 j0; CB 8 j1; CB 8 j2]
              ([C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED) FRc ltac:(cbn [cells_size csize]; lia)) as [_ FRd].
  destruct (dr_cut m1 (S0 - 144 + 24) (S0 - 144 + 32) [C8 (Z_to_bv 64 6001)] ([CB 8 j4] ++ SAVED) FRd
              ltac:(cbn [cells_size csize]; lia)) as [C6k _].
  assert (NIG : forall a, G <= a < G + SRC_TABLE -> ~ in_img Bm a).
  { intros a Ha Hi. destruct GF as (_ & _ & GF3). apply (GF3 (a - G)); [lia|].
    replace (G + (a - G)) with a by lia. exact Hi. }
  assert (ESn : rw_cells rsegs (normalize rsegs m1) (SA + 8) [C4 (Z_to_bv 64 (re_skip e1))]).
  { apply sb_rw_norm; [exact RO1' | exact ES |]. intros i Hi. cbn [cells_size csize] in Hi.
    apply ro_off; [lia|]. apply NIG. unfold SRC_TABLE, SRC_ENTRY. lia. }
  assert (C6n : rw_cells rsegs (normalize rsegs m1) (S0 - 144 + 24) [C8 (Z_to_bv 64 6001)]).
  { apply sb_rw_norm; [exact RO1' | exact C6k |]. intros i Hi. cbn [cells_size csize] in Hi. apply sb_ro_ge. lia. }
  pose proof RTL1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  assert (SK : 0 <= re_skip e1 < 2 ^ 31) by (destruct K2 as [E|E]; rewrite E; lia).
  assert (BPOS : 0 < re_buf e1) by (apply BP; lia).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, H2, H8, G10, G18. rewrite SEGS.
    apply (evt_normalize rsegs); [exact dl_wx | exact RO1' |].
    eapply dr_hit; [exact ESn | exact C6n | apply mem_inv_normalize | exact SK | lia | lia | intros _; lia]. }
  intros ms (can & (s0 & Q0 & REL & ROS) & EQ).
  destruct Q0 as [(R0 & _)|[(_ & SKC & m' & e10 & e11 & -> & MU' & WM' & _ & C0')|(_ & SK0 & LT & ->)]].
  - exfalso. clear - R0 BPOS. lia.
  - destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
    remember (ms_mem can) as m2 eqn:Em2. subst can. clear Em2.
    pose proof (mem_rel_normalize rsegs m1 RO1') as MRN.
    pose proof (munch_rel rsegs _ _ _ _ _ MRN HR ROS MU') as MU2.
    pose proof (wmono_rel rsegs _ _ _ _ MRN HR ROS WM') as WM2.
    pose proof (KindB.rw_cells_of_rel _ _ _ _ _ HR C0') as C02.
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R3 & -> & X3).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    assert (RTL3 : RTL R3) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3).
    pose proof RTL3 as (((P2 & P3 & P4 & P8 & P22 & P25) & P23 & P26) & P27).
    assert (Y9 : getr R3 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X3.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y9, P27. rewrite SEGS.
      eapply dr_next; lia. }
    intros ms (can & -> & EQ4).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply SR_ret. right.
    assert (SKL : dskp s P = true \/ (LINE_LIMIT < Q - P)%nat).
    { destruct SKC as [SKC|SKC]; [left | right; pose proof LL6000; lia].
      destruct (dskp s P) eqn:DK; [reflexivity|]. exfalso. exact (SKC L3'). }
    destruct (drl_skip s P Q DB HPQ HQ HNZ SKL) as (E1 & E2 & E3).
    exists R4, L1, A1, m2, md1, (esk0 e1), h1, OUT1, junk1, LB1, D.
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X4|].
    split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity; simp_regs;
            change (re_buf (esk0 e1)) with (re_buf e1); f_equal; lia|].
    split; [unfold dbound; split; [lia | right; replace (S Q - 1)%nat with Q by lia; exact HQ]|].
    unfold DLC, dlH, dlka, dlno, dloc, dlrun in DLC1 |- *. rewrite E1, <- E2, E3.
    exact (core_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 DLC1 MU2 WM2 C02).
  - destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
    remember (ms_mem can) as m2 eqn:Em2. subst can. clear Em2.
    pose proof (mem_back m1 m2 HR ROS) as ME. subst m2.
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R3 & -> & X3).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    assert (HK : dskp s P = false)
      by (destruct (dskp s P) eqn:DK; [rewrite L3' in SK0; discriminate | reflexivity]).
    assert (HL : (Q - P <= LINE_LIMIT)%nat) by (pose proof LL6000; lia).
    change (Z_to_bv 64 0x13328) with (Z_to_bv 64 SEND_LINE).
    eapply SR_mono; [apply (line_send s P Q R3 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D) | intros c' H'; left; exact H'].
    + unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X3.
    + rgw X3.
    + rgw X3.
    + rgw X3.
    + rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X3) by reflexivity. simp_regs. rewrite (dline_len s P Q HPQ).
      f_equal. lia.
    + rgw X3.
    + exact DB.
    + exact HPQ.
    + exact HQ.
    + exact HNZ.
    + exact HK.
    + exact HL.
    + exact DLC1.
Qed.

Definition DLSF (s : dstate) (P Q : nat) : Prop :=
  dbound s P /\ (P <= Q < length (dW s))%nat /\ nth_error (dW s) Q = Some 0 /\
  (forall i, (P <= i < Q)%nat -> nth_error (dW s) i <> Some 0) /\ dskp s P = false /\ (Q - P <= LINE_LIMIT)%nat.

Definition sv_no (s : dstate) (P Q : nat) : Z := dlno s P + Z.of_nat (length (dline s P Q)) + 1.
Definition sv_oc (s : dstate) (P Q : nat) : Z :=
  send_line_cap LIVE MX (dlno s P) (dloc s P) (Z.of_nat (length (dline s P Q)) + 1).
Definition sv_rest (s : dstate) (P Q : nat) : RestT :=
  lrest (sv_no s P Q) (sv_oc s P Q) (seen_arr (dlH s P) (dline s P Q)) (seen_ka (dlH s P) (dlka s P) (dline s P Q))
    (drlq s (S Q)).

Definition DLSB (s : dstate) (P Q : nat) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (junk1 LB1 : list byte) (D : list Z) : Prop :=
  DLSF s P Q /\
  LCORE s D (lines ST0 D ++ drlp s P ++ [dline s P Q]) (lines ST0 D ++ drlp s P) (dlH s P) (dlka s P)
    (sv_no s P Q) (sv_oc s P Q) (Z.of_nat (S (length (drlq s (S Q)))))
    (srest (dlH s P) (dlka s P) (dline s P Q) (sv_no s P Q) (sv_oc s P Q) (drlq s (S Q)))
    false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DLNB (s : dstate) (P Q : nat) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (e1 : rentry) (h1 : hsrc) (OUT1 : Z) (junk1 LB1 : list byte) (D : list Z) : Prop :=
  DLSF s P Q /\
  LCORE s D (lines ST0 D ++ drlp s P ++ [dline s P Q]) (lines ST0 D ++ drlp s P ++ [dline s P Q])
    (seen_arr (dlH s P) (dline s P Q)) (seen_ka (dlH s P) (dlka s P) (dline s P Q))
    (sv_no s P Q) (sv_oc s P Q) (Z.of_nat (length (drlq s (S Q)))) (sv_rest s P Q)
    false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Definition DGS (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (k : gkind) (jj : nat) (bg : Z),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13c7c) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj) /\ getr R1 20 = Z_to_bv 64 bg /\
    0 <= bg < 2 ^ 64 /\ (bg = 0 <-> k = GBegin) /\
    gesture (dline s P Q) = Some (k, firstn jj (dline s P Q)) /\ (13 < jj < Q - P)%nat /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Definition DGA (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (k : gkind) (jj : nat) (bg : Z),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13d14) m1 (seg_rom segs)) md1 /\ RT R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    rw_cells segs m1 (S0 - 144) [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 (re_nheld e1))] /\
    rw_cells segs m1 (S0 - 144 + 32) [C8 (Z_to_bv 64 (Z.of_nat jj))] /\
    0 <= bg < 2 ^ 64 /\ (bg = 0 <-> k = GBegin) /\
    gesture (dline s P Q) = Some (k, firstn jj (dline s P Q)) /\ (13 < jj < Q - P)%nat /\
    index_of (firstn jj (dline s P Q)) (dlH s P) = None /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Definition DGF (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (jj n : nat),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x15f4c) m1 (seg_rom segs)) md1 /\ RT R1 /\
    getr R1 1 = Z_to_bv 64 0x13dc8 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 10 = Z_to_bv 64 (key_addr (nth n (re_keys e1) (0, [], []))) /\
    getr R1 19 = Z_to_bv 64 (8 * Z.of_nat n) /\ getr R1 23 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n) /\
    (n < length (re_keys e1))%nat /\
    gesture (dline s P Q) = Some (GEnd, firstn jj (dline s P Q)) /\ (13 < jj < Q - P)%nat /\
    index_of (firstn jj (dline s P Q)) (dlH s P) = Some n /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Definition DGK (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (jj : nat),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 STRNDUP) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 1 = Z_to_bv 64 0x13d5c /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\ getr R1 11 = Z_to_bv 64 (Z.of_nat jj) /\
    gesture (dline s P Q) = Some (GBegin, firstn jj (dline s P Q)) /\ (13 < jj < Q - P)%nat /\
    index_of (firstn jj (dline s P Q)) (dlH s P) = None /\
    re_hp e1 <> 0 /\ re_kh e1 = 8 * (re_nheld e1 + 1) /\
    DLSF s P Q /\
    LCORE s D (lines ST0 D ++ drlp s P ++ [dline s P Q]) (lines ST0 D ++ drlp s P) (dlH s P)
      (seen_ka (dlH s P) (dlka s P) (dline s P Q))
      (sv_no s P Q) (sv_oc s P Q) (Z.of_nat (S (length (drlq s (S Q)))))
      (fun jb o ha ks =>
         (RMalloc (Z.of_nat jj + 1) :: fst (sv_rest s P Q (S jb) o ha (ks ++ [Ret jb])),
          snd (sv_rest s P Q (S jb) o ha (ks ++ [Ret jb]))))
      false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.

Lemma sn_dlno : forall s P Q, drlp s (S Q) = drlp s P ++ [dline s P Q] -> dlno s (S Q) = sv_no s P Q.
Proof using Bm G HJ O h junk regs.
  intros s P Q E. unfold sv_no, dlno. rewrite E. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
  rewrite app_nil_r, !length_app. cbn [length]. lia.
Qed.

Lemma sn_dlrun : forall s P Q, drlp s (S Q) = drlp s P ++ [dline s P Q] ->
  dlrun s (S Q) = (sv_oc s P Q, seen_arr (dlH s P) (dline s P Q), seen_ka (dlH s P) (dlka s P) (dline s P Q)).
Proof using Bm G HJ O junk regs.
  intros s P Q E. unfold dlrun at 1. rewrite E, lrun_app, lrun_one.
  unfold sv_oc, dlno, dloc, dlH, dlka, dlrun. reflexivity.
Qed.

Lemma dln_of : forall s P Q R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
  RTL R1 -> getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat (S Q)) ->
  DLNB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D ->
  DLN s (S Q) (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13b8c) m1 (seg_rom segs)) md1).
Proof using HG HJ.
  intros s P Q R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D HR H18 [HF HL].
  destruct HF as (HB & HPQ & HQ & HNZ & HK & HLL).
  destruct (drl_send s P Q HB HPQ HQ HNZ HK HLL) as (E1 & _ & E3).
  pose proof (sn_dlrun s P Q E1) as ER.
  assert (Eoc : dloc s (S Q) = sv_oc s P Q) by (unfold dloc; rewrite ER; reflexivity).
  assert (EH : dlH s (S Q) = seen_arr (dlH s P) (dline s P Q)) by (unfold dlH; rewrite ER; reflexivity).
  assert (Eka : dlka s (S Q) = seen_ka (dlH s P) (dlka s P) (dline s P Q))
    by (unfold dlka; rewrite ER; reflexivity).
  pose proof (sn_dlno s P Q E1) as Eno.
  unfold DLN. exists R1, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D.
  split; [reflexivity|]. split; [exact HR|]. split; [exact H18|].
  split.
  { unfold dbound. split; [lia|]. right. replace (S Q - 1)%nat with Q by lia. exact HQ. }
  unfold DLC. rewrite Eoc, EH, Eka, Eno, E1, E3. exact HL.
Qed.

Lemma sn_lcore_kl : forall s D sent kl kl' l H ka no oc nk nk' rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1,
  LCORE s D sent kl H ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 ->
  kl' = kl ++ [l] -> seen_arr H l = H -> nk' <= nk ->
  LCORE s D sent kl' H ka no oc nk' rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1.
Proof using HG HJ.
  intros s D sent kl kl' l H ka no oc nk nk' rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 HL Ek HA Hn. subst kl'.
  destruct HL as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14).
  destruct X12 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
  cbn [dvirt ds_H] in Y8, Y9.
  assert (Y8' : List.NoDup H) by (apply NoDup_ListNoDup; exact Y8).
  destruct (seen_arr_ok H (upds (keys_texts (re_keys e)) kl) l Y8' Y9) as [_ HS]. rewrite HA in HS.
  unfold LCORE.
  refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj X10
    (conj X11 (conj _ (conj _ X14))))))))))))); [|lia].
  unfold DHISTg.
  refine (conj Y1 (conj Y2 (conj Y3 (conj Y4 (conj Y5 (conj Y6 (conj Y7 (conj Y8 (conj _ Y10))))))))).
  cbn [dvirt ds_H]. unfold upds in HS |- *. rewrite fold_left_app. exact HS.
Qed.

Lemma dlnb_same : forall s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
  DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D ->
  (forall jb ha ks, seen_tr (dlH s P) (dlka s P) (dline s P Q) jb ha ks = ([], dlka s P, (ha, ks))) ->
  seen_arr (dlH s P) (dline s P Q) = dlH s P ->
  DLNB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.
Proof using HG HJ.
  intros s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D [HF HL] E HA.
  assert (EK : seen_ka (dlH s P) (dlka s P) (dline s P Q) = dlka s P) by (unfold seen_ka; rewrite E; reflexivity).
  assert (ER : srest (dlH s P) (dlka s P) (dline s P Q) (sv_no s P Q) (sv_oc s P Q) (drlq s (S Q)) = sv_rest s P Q).
  { apply FunctionalExtensionality.functional_extensionality; intros jx.
    apply FunctionalExtensionality.functional_extensionality; intros ox.
    apply FunctionalExtensionality.functional_extensionality; intros hx.
    apply FunctionalExtensionality.functional_extensionality; intros kx.
    unfold srest, sv_rest. cbv beta. rewrite E. cbn [fst snd app]. rewrite nret_nil, Nat.add_0_r.
    rewrite <- surjective_pairing. reflexivity. }
  unfold DLNB. split; [exact HF|]. rewrite ER in HL. rewrite EK, HA.
  eapply sn_lcore_kl; [exact HL | apply app_assoc | exact HA | lia].
Qed.

Definition sv_last (s : dstate) (P Q : nat) (A : Z) : Z :=
  match last_space_from 0 (dline s P Q) with Some j => A + Z.of_nat j | None => 0 end.

Definition DST1 (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13bf0) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 10 = Z_to_bv 64 (sv_last s P Q (re_buf e1 + Z.of_nat P)) /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Definition DST2 (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (v : Z),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13c08) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 19 = Z_to_bv 64 (sv_last s P Q (re_buf e1 + Z.of_nat P)) /\
    getr R1 10 = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64 /\ (v = 0 <-> firstn 13 (dline s P Q) = K_GESTURE) /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Definition DST3 (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (jj : nat) (r : Z),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13c54) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj) /\
    getr R1 21 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1) /\
    getr R1 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\ (r = 0 <-> skipn (S jj) (dline s P Q) = W_BEGIN) /\
    firstn 13 (dline s P Q) = K_GESTURE /\ nth 13 (dline s P Q) 0 = SPACE /\
    last_space_from 0 (dline s P Q) = Some jj /\ (13 < jj < Q - P)%nat /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Definition DST4 (s : dstate) (P Q : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (jj : nat) (bg r : Z),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13c78) m1 (seg_rom segs)) md1 /\ RTL R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj) /\ getr R1 20 = Z_to_bv 64 bg /\
    0 <= bg < 2 ^ 64 /\ bg <> 0 /\ skipn (S jj) (dline s P Q) <> W_BEGIN /\
    getr R1 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\ (r = 0 <-> skipn (S jj) (dline s P Q) = W_END) /\
    firstn 13 (dline s P Q) = K_GESTURE /\ nth 13 (dline s P Q) 0 = SPACE /\
    last_space_from 0 (dline s P Q) = Some jj /\ (13 < jj < Q - P)%nat /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Lemma core_stk : forall s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 lo,
  LCORE s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 ->
  S0 - 8512 <= lo -> munch [(lo, S0 - 144)] m1 m2 -> wmono rsegs m1 m2 ->
  LCORE s D sent kl Hk ka no oc nk rest sk L1 A1 m2 md1 e1 h1 OUT1 junk1 LB1.
Proof using AX BW EHI EU GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 lo
    (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NB1 & RS1 & BK1 & GL1 & OU1)
    HLO MU WM.
  hide. pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  assert (DK : DRAIN_K = 8512) by reflexivity.
  pose proof RP1 as (M1 & _).
  assert (WM' : wmono segs m1 m2) by (rewrite SEGS; exact WM).
  pose proof (msame_munch _ _ _ MU WM') as MS.
  assert (PL : forall a, 0 <= a < YM05.alloc_ceiling -> 0 <= a < 2 ^ 64 /\ outside [(lo, S0 - 144)] a).
  { intros a Ha. split; [clear - Ha F4; lia|]. cbn [outside]. split; [clear - Ha HLO F1; lia | exact I]. }
  assert (PI : forall a, in_img Bm a -> 0 <= a < 2 ^ 64 /\ outside [(lo, S0 - 144)] a).
  { intros a Ha. pose proof (img_lo a Ha) as IL. apply PL. clear - IL F3. lia. }
  assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> q <= a < q + k ->
            0 <= a < 2 ^ 64 /\ outside [(lo, S0 - 144)] a).
  { intros q k a Hq Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR. apply PL. clear - Ha BR. lia. }
  assert (PFa : forall a, S0 - 144 <= a < S0 -> 0 <= a < 2 ^ 64 /\ outside [(lo, S0 - 144)] a).
  { intros a Ha. split; [clear - Ha F1 F2 F3; lia|]. cbn [outside]. split; [clear - Ha; lia | exact I]. }
  assert (PIa : forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX ->
            0 <= a < 2 ^ 64 /\ outside [(lo, S0 - 144)] a).
  { intros a Ha. apply PI. exact (proj1 (GRP a ltac:(clear - Ha; unfold G_RELAY_LO, G_S in *; lia))). }
  assert (PSa : forall q k, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) ->
            In (q, k) (blocks L1 A1)) by (intros q k Hq _; exact Hq).
  assert (PBa : forall q k a, In (q, k) (blocks L1 A1) -> In q (entry_blocks e1 ++ hs_blocks h1) -> q <= a < q + k ->
            0 <= a < 2 ^ 64 /\ outside [(lo, S0 - 144)] a).
  { intros q k a Hq _ Ha. exact (PB q k a Hq Ha). }
  destruct (core_tr L1 A1 m1 L1 A1 m2 e1 h1 _ MS FR1 EK1 SR1 OT1 PFa PIa PSa PBa) as (FR2 & EK2 & SR2 & OT2).
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU); [exact WM' | exact GEI |].
    intros a Ha. destruct (Z_lt_le_dec a lo) as [D0|D0]; [left; cbn [outside]; split; [clear - D0; lia | exact I]|].
    destruct (Z_lt_le_dec a (S0 - 144)) as [D2|D2]; [|left; cbn [outside]; split; [clear - D2; lia | exact I]].
    right. left. change (spZ regs) with S0. rewrite DK. clear - D0 D2 HLO F1. lia. }
  split; [exact IN1|]. split; [exact TR1|].
  split.
  { rewrite SEGS. apply (ro_munch2 m1 m2 [(lo, S0 - 144)]); [rewrite <- SEGS; exact RO1 | exact MU |].
    intros x Hx. exact (proj2 (PI _ Hx)). }
  split; [exact FR2|].
  split.
  { eapply rw_tr; [exact MS | exact SAC1 |]. intros a Ha. apply PL. cbn [cells_size csize] in Ha.
    clear - Ha F5 F6 F7 F8. lia. }
  split; [exact EK2|]. split; [exact SR2|]. split; [exact OT2|]. split; [exact SM1|].
  split; [exact LK1|]. split; [exact HI1|]. split; [exact NB1|]. split; [exact RS1|]. split; [exact BK1|].
  split.
  { destruct GL1 as (G1c & G2c & G3c & G4c & (ev1 & G5c)).
    split; [eapply rw_tr; [exact MS | exact G1c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GCP a ltac:(clear - Ha; lia)))|].
    split; [eapply rw_tr; [exact MS | exact G2c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [eapply rw_tr; [exact MS | exact G3c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [eapply rw_tr; [exact MS | exact G4c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    exists ev1. eapply rw_tr; [exact MS | exact G5c |]. intros a Ha. apply PI. cbn [cells_size csize] in Ha.
    apply GEI. clear - Ha. lia. }
  destruct OU1 as (OF1 & OT1'). hide.
  assert (LOO : Z.of_nat (length O) = NO).
  { destruct OUTD as [(_ & _ & N0 & E0)|(_ & _ & _ & _ & _ & L0 & _)];
      [rewrite E0; cbn [length Z.of_nat]; clear - N0; lia | exact L0]. }
  split.
  - intros LV. destruct (OF1 LV) as (C1 & E1 & E2 & E3).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [exact E1|]. split; [exact E2|].
    intros Cp. destruct (E3 Cp) as (I3 & B3). split; [exact I3|].
    eapply by_tr; [exact MS | exact B3 |]. intros a Ha. apply (PB OUT CAP a I3).
    destruct OUTD as [(C0' & _)|(_ & _ & _ & _ & _ & L0 & LJ)]; [clear - C0' Cp; lia|].
    rewrite length_app in Ha. clear - Ha L0 LJ. lia.
  - intros LV. destruct (OT1' LV) as (C1 & D1).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    destruct D1 as [D1|(Cp & NL & I3 & F3' & B3 & LJ)]; [left; exact D1 | right].
    split; [exact Cp|]. split; [exact NL|]. split; [exact I3|]. split; [exact F3'|].
    split; [|exact LJ].
    eapply by_tr; [exact MS | exact B3 |]. intros a Ha. apply (PB OUT1 _ a I3).
    pose proof HI1 as (_ & _ & _ & _ & _ & HN & HLB & _).
    assert (LL : Z.of_nat (length LB1) = Z.of_nat (length (with_nul sent)))
      by (rewrite <- HLB; unfold bzs; rewrite length_map; reflexivity).
    rewrite !length_app in Ha. clear - Ha LOO LL LJ HN. lia.
Qed.

Lemma ret_pc_13bf0 : ret_pc (Z_to_bv 64 0x13bf0) = Z_to_bv 64 0x13bf0.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma bzs_app_cons : forall l1 b l2, bzs (l1 ++ b :: l2) = bzs l1 ++ bz b :: bzs l2.
Proof using. intros l1 b l2. unfold bzs. rewrite map_app. reflexivity. Qed.

Lemma lsf_rfind : forall (l : list byte) i,
  last_space_from i (bzs l) = option_map (fun k => (i + k)%nat) (lib.U.Prog.memrchr_c.rfind_byte 32 l).
Proof using Bm G HJ O h junk regs.
  induction l as [|b l IH]; intros i; [reflexivity|].
  unfold bzs in *. cbn [map last_space_from lib.U.Prog.memrchr_c.rfind_byte]. rewrite (IH (S i)).
  destruct (lib.U.Prog.memrchr_c.rfind_byte 32 l) as [k|]; cbn [option_map]; [f_equal; lia|].
  unfold bz, SPACE. destruct (bv_unsigned b =? 32); cbn [option_map]; [f_equal; lia | reflexivity].
Qed.

Lemma seen_strrchr : forall s P Q c, DLS s P Q c -> SR segs c (DST1 s P Q).
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RTL1 & G9 & G18 & DB & HPQ & HQ &
    HNZ & HK & HL & LC1).
  pose proof LC1 as (RP1 & _ & _ & RO1 & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof EK1 as (_ & _ & _ & _ & _ & _ & K7 & K8 & K9 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RTL1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  assert (DK : DRAIN_K = 8512) by reflexivity.
  assert (RO1' : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  assert (UPOS : 0 < re_used e1) by (rewrite EUd; clear - HPQ; lia).
  destruct K9 as [(C0 & _ & U0)|(Cp & BI & BF & BJ & BC)]; [exfalso; clear - U0 UPOS; lia|].
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  destruct BC as [[_ BUJ] _]. cbn [cells_bytes cbytes] in BUJ. rewrite app_nil_r in BUJ.
  destruct (dx_slack L1 A1 m1 md1 (re_buf e1) (re_cap e1 - 1) M1) as (sl & Lsl & Hsl);
    [replace (re_cap e1 - 1 + 1) with (re_cap e1) by ring; exact BI | clear - BR; lia | clear - Cp; lia
    | clear - BR F4; lia |].
  assert (BUJS : bytes_at segs m1 (re_buf e1) ((re_U e1 ++ re_junk e1) ++ sl)).
  { apply bytes_at_app. split; [exact BUJ|].
    replace (re_buf e1 + Z.of_nat (length (re_U e1 ++ re_junk e1))) with (re_buf e1 + (re_cap e1 - 1) + 1);
      [exact Hsl | rewrite length_app; clear - K7 BJ; lia]. }
  set (lb := firstn (Q - P) (skipn P (re_U e1))).
  set (slk := skipn (S Q) (re_U e1) ++ re_junk e1 ++ sl).
  assert (LLB : length lb = (Q - P)%nat).
  { unfold lb. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. clear - LW HPQ. lia. }
  assert (LSL : Z.of_nat (length slk) = re_cap e1 - Z.of_nat Q - 1 + (- (re_buf e1 + (re_cap e1 - 1) + 1)) mod 8).
  { unfold slk. rewrite !length_app, length_skipn. clear - LW HPQ K7 BJ Lsl. lia. }
  assert (ES : skipn P (re_U e1) = lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1)).
  { apply bzs_inj. unfold lb. rewrite bzs_app_cons, <- firstn_bzs, <- !skipn_bzs, EW.
    exact (dW_split s P Q (proj1 HPQ) HQ). }
  assert (E2 : bzs lb = dline s P Q).
  { unfold lb, dline. rewrite <- firstn_bzs, <- skipn_bzs, EW. reflexivity. }
  assert (NZ : ~ In (Z_to_bv 8 0) lb).
  { intros HI. pose proof (dline_nz s P Q HNZ) as NZd. rewrite <- E2 in NZd. unfold nozero in NZd.
    assert (IN0 : In 0 (bzs lb)).
    { unfold bzs. apply in_map_iff. exists (Z_to_bv 8 0). split; [reflexivity | exact HI]. }
    exact (proj1 (Forall_forall _ _) NZd 0 IN0 eq_refl). }
  assert (EB : (re_U e1 ++ re_junk e1) ++ sl = firstn P (re_U e1) ++ lb ++ Z_to_bv 8 0 :: slk).
  { unfold slk. rewrite <- (firstn_skipn P (re_U e1)) at 1. rewrite ES. rewrite <- !app_assoc. reflexivity. }
  assert (BL : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P) (lb ++ Z_to_bv 8 0 :: slk)).
  { rewrite EB in BUJS. apply bytes_at_app in BUJS as [_ T]. rewrite firstn_length_le in T by (clear - LW HPQ; lia).
    rewrite <- SEGS. exact T. }
  assert (STK1 : stk rsegs m1 (S0 - 176) (S0 - 144)).
  { split; [clear - F1 F3; lia|]. split; [clear - F2; lia|]. intros a Ha.
    assert (W : writable_at rsegs m1 a).
    { rewrite <- SEGS. apply SC1. left. change (spZ regs) with S0. rewrite DK. clear - Ha. lia. }
    split; [exact W|]. destruct (KindB.writable_hi_present m1 a ltac:(clear - Ha F1 F2 F3; lia) W) as [bb E].
    exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr. rewrite SEGS. apply dr_seen. }
  intros ms (can & HC & EQ). cbv beta in HC. subst can.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  pose proof RTL2 as (((J2 & J3 & J4 & J8 & J22 & J25) & J23 & J26) & J27).
  assert (Y1 : getr R2 1 = Z_to_bv 64 0x13bf0) by rgw X2.
  assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
  assert (Y10 : getr R2 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  assert (Y11 : getr R2 11 = Z_to_bv 64 32) by rgw X2.
  assert (Y18 : getr R2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  pose proof SRR as SR0. unfold strrchr_contract in SR0.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y1, J2, Y10, Y11. rewrite SEGS.
    apply (evt_normalize rsegs); [exact dl_wx | exact RO1' |].
    apply SR0 with (str := lb) (slack := slk) (lo := S0 - 176).
    - rewrite unsigned_lit by (clear - B0 BU EUd HPQ; lia). exact (bytes_at_normalize rsegs m1 _ _ RO1' BL).
    - exact NZ.
    - rewrite unsigned_lit by (clear - B0 BU EUd HPQ; lia). rewrite LSL, LLB. clear - HPQ LW K7 K8.
      Z.div_mod_to_equations. lia.
    - apply mem_inv_normalize.
    - rewrite unsigned_lit by (clear - F1 F2 F3; lia). apply KindB.stk_normalize; [exact STK1 | clear - F1 F3; lia].
    - rewrite unsigned_lit by (clear - F1 F2 F3; lia). unfold STRRCHR_K. clear - F1. lia.
    - left. rewrite !unsigned_lit by (clear - B0 BU EUd HPQ F1 F2 F3; lia). rewrite LSL, LLB. unfold STRRCHR_K.
      clear - HPQ LW K7 K8 BR F1. Z.div_mod_to_equations. lia. }
  intros ms (can & (s0 & Q0 & REL & ROS) & EQ').
  destruct Q0 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU' & WM' & _ & _ & _).
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
  remember (ms_mem can) as m2 eqn:Em2. subst can. clear Em2.
  pose proof (mem_rel_normalize rsegs m1 RO1') as MRN.
  pose proof (munch_rel rsegs _ _ _ _ _ MRN HR ROS MU') as MU2.
  pose proof (wmono_rel rsegs _ _ _ _ MRN HR ROS WM') as WM2.
  rewrite unsigned_lit in MU2 by (clear - F1 F2 F3; lia). unfold STRRCHR_K in MU2.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ' eq_refl eq_refl) as (R3 & -> & X3).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  rewrite ret_pc_13bf0.
  apply SR_ret.
  exists R3, L1, A1, m2, md1, e1, h1, OUT1, junk1, LB1, D.
  split; [reflexivity|].
  split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3|].
  split; [rgw X3|].
  split; [rgw X3|].
  split.
  { rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X3) by reflexivity. simp_regs. f_equal.
    rewrite !unsigned_lit by (clear - B0 BU EUd HPQ; lia). change (32 mod 256) with 32.
    rewrite strrchr_res_nonnul by discriminate. unfold sv_last. rewrite <- E2, lsf_rfind.
    destruct (lib.U.Prog.memrchr_c.rfind_byte 32 lb); reflexivity. }
  unfold DLSB. split; [exact (conj DB (conj HPQ (conj HQ (conj HNZ (conj HK HL)))))|].
  apply (core_stk s D _ _ _ _ _ _ _ _ false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 (S0 - 144 - 32) LC1);
    [clear - F1; lia | exact MU2 | exact WM2].
Qed.

Definition K_GB : list byte := map (Z_to_bv 8) K_GESTURE.

Lemma K_GB_z : bzs K_GB = K_GESTURE.
Proof using. vm_compute. reflexivity. Qed.

Lemma K_GB_nz : Forall (fun b : byte => bv_unsigned b <> 0) K_GB.
Proof using.
  unfold K_GB, K_GESTURE. cbn [map].
  repeat (apply Forall_cons; [intros E; vm_compute in E; discriminate E|]). apply Forall_nil.
Qed.

Lemma K_GB_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x103e6 K_GB.
Proof using.
  intros m MI.
  pose proof (ro_cells_image rsegs m 0x103e6 K_GB MI ltac:(vm_compute; reflexivity) ltac:(clear - MI; lia)
                ltac:(change (length K_GB) with 13%nat; clear - MI; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma ret_pc_13c08 : ret_pc (Z_to_bv 64 0x13c08) = Z_to_bv 64 0x13c08.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma dr_walk_stop : forall (a b : byte) l r k,
  (bv_unsigned a = 0 \/ bv_unsigned b = 0 \/ k = 0%nat \/ bv_unsigned a <> bv_unsigned b) ->
  StrFun.strncmp_walk (a :: l) (b :: r) k = Some (bv_unsigned a - bv_unsigned b).
Proof using.
  intros a b l r k H. cbn [StrFun.strncmp_walk].
  destruct (bv_unsigned a =? 0) eqn:E1; [reflexivity|].
  destruct (bv_unsigned b =? 0) eqn:E2; [reflexivity|].
  destruct (Nat.eqb k 0) eqn:E3; [reflexivity|].
  destruct (bv_unsigned a =? bv_unsigned b) eqn:E4; [|reflexivity].
  apply Z.eqb_neq in E1. apply Z.eqb_neq in E2. apply Nat.eqb_neq in E3. apply Z.eqb_eq in E4.
  exfalso. clear - H E1 E2 E3 E4. lia.
Qed.

Lemma dr_walk_go : forall (a b : byte) l r k,
  bv_unsigned a <> 0 -> bv_unsigned a = bv_unsigned b ->
  StrFun.strncmp_walk (a :: l) (b :: r) (S k) = StrFun.strncmp_walk l r k.
Proof using.
  intros a b l r k Ha Hab. cbn [StrFun.strncmp_walk].
  rewrite (proj2 (Z.eqb_neq _ _) Ha), <- Hab, (proj2 (Z.eqb_neq _ _) Ha), Z.eqb_refl. reflexivity.
Qed.

Lemma dr_walk : forall r lb slk k, length r = S k ->
  Forall (fun b : byte => bv_unsigned b <> 0) lb -> Forall (fun b : byte => bv_unsigned b <> 0) r ->
  exists v, StrFun.strncmp_walk (lb ++ Z_to_bv 8 0 :: slk) r k = Some v /\ -256 < v < 256 /\
    (v = 0 <-> firstn (S k) (bzs lb) = bzs r).
Proof using.
  induction r as [|b r IH]; intros lb slk k LR NL NR; [discriminate LR|].
  pose proof (Forall_inv NR) as NB. pose proof (Forall_inv_tail NR) as NR'. cbv beta in NB.
  pose proof (StrFun.byte_range b) as RB.
  destruct lb as [|a lb]; cbn [app].
  - assert (Z0' : bv_unsigned (Z_to_bv 8 0) = 0) by (rewrite Z_to_bv_unsigned; reflexivity).
    exists (bv_unsigned (Z_to_bv 8 0) - bv_unsigned b).
    split; [apply dr_walk_stop; left; exact Z0'|].
    rewrite Z0'. split; [clear - RB; lia|].
    split; [intros E; exfalso; clear - E NB; lia|].
    intros E. unfold bzs in E. cbn [map firstn] in E. discriminate E.
  - pose proof (Forall_inv NL) as NA. pose proof (Forall_inv_tail NL) as NL'. cbv beta in NA.
    pose proof (StrFun.byte_range a) as RA.
    destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [EAB|NAB].
    + destruct k as [|k].
      * destruct r as [|b' r]; [|exfalso; cbn in LR; clear - LR; lia].
        exists (bv_unsigned a - bv_unsigned b).
        split; [apply dr_walk_stop; right; right; left; reflexivity|].
        split; [clear - RA RB; lia|].
        split; [intros _ | intros _; clear - EAB; lia].
        change (firstn 1 (bzs (a :: lb))) with [bz a]. change (bzs [b]) with [bz b].
        unfold bz. rewrite EAB. reflexivity.
      * rewrite (dr_walk_go a b _ _ _ NA EAB).
        destruct (IH lb slk k ltac:(cbn in LR; clear - LR; lia) NL' NR') as (v & WV & VB & VE).
        exists v. split; [exact WV|]. split; [exact VB|].
        change (firstn (S (S k)) (bzs (a :: lb))) with (bz a :: firstn (S k) (bzs lb)).
        change (bzs (b :: r)) with (bz b :: bzs r).
        split; intros HV.
        -- apply VE in HV. rewrite HV. unfold bz. rewrite EAB. reflexivity.
        -- injection HV as HA HT. apply VE. exact HT.
    + exists (bv_unsigned a - bv_unsigned b).
      split; [apply dr_walk_stop; right; right; right; exact NAB|].
      split; [clear - RA RB; lia|].
      split; [intros E; exfalso; clear - E NAB; lia|].
      intros E. exfalso. apply NAB.
      change (firstn (S k) (bzs (a :: lb))) with (bz a :: firstn k (bzs lb)) in E.
      change (bzs (b :: r)) with (bz b :: bzs r) in E.
      injection E as EA ER. exact EA.
Qed.

Lemma seen_strncmp : forall s P Q c, DST1 s P Q c -> SR segs c (DST2 s P Q).
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RTL1 & G9 & G18 & G10 & DF & LC1).
  pose proof DF as (DB & HPQ & HQ & HNZ & HK & HL).
  pose proof LC1 as (RP1 & _ & _ & RO1 & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RTL1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  assert (RO1' : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  set (lb := firstn (Q - P) (skipn P (re_U e1))).
  assert (ES : skipn P (re_U e1) = lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1)).
  { apply bzs_inj. unfold lb. rewrite bzs_app_cons, <- firstn_bzs, <- !skipn_bzs, EW.
    exact (dW_split s P Q (proj1 HPQ) HQ). }
  assert (E2 : bzs lb = dline s P Q).
  { unfold lb, dline. rewrite <- firstn_bzs, <- skipn_bzs, EW. reflexivity. }
  assert (NZb : Forall (fun b : byte => bv_unsigned b <> 0) lb).
  { pose proof (dline_nz s P Q HNZ) as NZd. rewrite <- E2 in NZd. unfold nozero, bzs in NZd.
    apply Forall_forall. intros b Hb. exact (proj1 (Forall_forall _ _) NZd (bz b) (in_map bz lb b Hb)). }
  assert (BL : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P) (lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1))).
  { pose proof BS as T. rewrite <- (firstn_skipn P (re_U e1)), ES in T. apply bytes_at_app in T as [_ T2].
    rewrite firstn_length_le in T2 by (clear - LW HPQ; lia). rewrite <- SEGS. exact T2. }
  destruct (dr_walk K_GB lb (skipn (S Q) (re_U e1)) 12 eq_refl NZb K_GB_nz) as (v & WK & VB & VE).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr. rewrite SEGS. apply dr_gverb. }
  intros ms (can & HC & EQ). cbv beta in HC. subst can.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  pose proof RTL2 as (((J2 & J3 & J4 & J8 & J22 & J25) & J23 & J26) & J27).
  assert (Y1 : getr R2 1 = Z_to_bv 64 0x13c08) by rgw X2.
  assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
  assert (Y10 : getr R2 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  assert (Y11 : getr R2 11 = Z_to_bv 64 0x103e6) by rgw X2.
  assert (Y12 : getr R2 12 = Z_to_bv 64 13) by rgw X2.
  assert (Y18 : getr R2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  assert (Y19 : getr R2 19 = Z_to_bv 64 (sv_last s P Q (re_buf e1 + Z.of_nat P))) by rgw X2.
  pose proof SNC as SN0. unfold strncmp_contract in SN0.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y1, Y10, Y11, Y12. rewrite SEGS.
    apply (evt_normalize rsegs); [exact dl_wx | exact RO1' |].
    apply SN0 with (ls := lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1)) (rs := K_GB) (v := v).
    - rewrite unsigned_lit by (clear - B0 BU EUd HPQ; lia). exact (bytes_at_normalize rsegs m1 _ _ RO1' BL).
    - change (bv_unsigned (Z_to_bv 64 0x103e6)) with 0x103e6. apply K_GB_at, mem_inv_normalize.
    - change (bv_unsigned (Z_to_bv 64 13)) with 13. exact WK.
    - apply mem_inv_normalize. }
  intros ms (can & (s0 & Q0 & REL & ROS) & EQ').
  destruct Q0 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU' & WM' & _ & _ & _).
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
  remember (ms_mem can) as m2 eqn:Em2. subst can. clear Em2.
  pose proof (mem_rel_normalize rsegs m1 RO1') as MRN.
  pose proof (munch_rel rsegs _ _ _ _ _ MRN HR ROS MU') as MU2.
  pose proof (wmono_rel rsegs _ _ _ _ MRN HR ROS WM') as WM2.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ' eq_refl eq_refl) as (R3 & -> & X3).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  rewrite ret_pc_13c08.
  apply SR_ret.
  exists R3, L1, A1, m2, md1, e1, h1, OUT1, junk1, LB1, D, (v mod 2 ^ 64).
  split; [reflexivity|].
  split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3|].
  split; [rgw X3|].
  split; [rgw X3|].
  split; [rgw X3|].
  split.
  { rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X3) by reflexivity. simp_regs.
    apply bv_eq. rewrite !unsigned_lit_wrap, Z.mod_mod by (clear - VB; lia). reflexivity. }
  split; [clear - VB; Z.div_mod_to_equations; lia|].
  split.
  { rewrite <- E2, <- K_GB_z. split; intros HV.
    - apply VE. clear - VB HV. Z.div_mod_to_equations. lia.
    - apply VE in HV. rewrite HV. reflexivity. }
  unfold DLSB. split; [exact DF|].
  apply (core_stk s D _ _ _ _ _ _ _ _ false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 (S0 - 144) LC1);
    [clear - F1; lia | | exact WM2].
  apply (munch_weaken []); [intros x _; exact I | exact MU2].
Qed.

Lemma gt_lsf_lt : forall l i q, last_space_from i l = Some q -> (i <= q < i + length l)%nat.
Proof using.
  induction l as [|b l IH]; intros i q H; cbn [last_space_from] in H; [discriminate H|].
  cbn [length]. revert H. destruct (last_space_from (S i) l) as [k|] eqn:E; intros H.
  - injection H as <-. pose proof (IH _ _ E) as X. clear - X. lia.
  - revert H. destruct (b =? SPACE); intros H; [injection H as <-; clear; lia | discriminate H].
Qed.

Lemma gt_lsf_ge : forall l i k, (k < length l)%nat -> nth k l 0 = SPACE ->
  exists q, last_space_from i l = Some q /\ (i + k <= q)%nat.
Proof using.
  induction l as [|b l IH]; intros i k Hk Hn; cbn [length] in Hk; [clear - Hk; lia|].
  cbn [last_space_from]. destruct k as [|k].
  - cbn [nth] in Hn. destruct (last_space_from (S i) l) as [q|] eqn:E.
    + exists q. split; [reflexivity|]. pose proof (gt_lsf_lt _ _ _ E) as X. clear - X. lia.
    + rewrite Hn, Z.eqb_refl. exists i. split; [reflexivity | clear; lia].
  - cbn [nth] in Hn. destruct (IH (S i) k ltac:(clear - Hk; lia) Hn) as (q & E & Hq). rewrite E.
    exists q. split; [reflexivity | clear - Hq; lia].
Qed.

Lemma gt_none : forall l, (firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE -> (13 < length l)%nat ->
  forall q, last_space_from 0 l = Some q -> (13 < q)%nat -> False) -> gesture l = None.
Proof using.
  intros l H. unfold gesture.
  destruct (list_eqb (firstn 13 l) K_GESTURE) eqn:E1; [|reflexivity].
  destruct (Z.eqb_spec (nth 13 l 0) SPACE) as [E2|E2]; [|reflexivity].
  destruct (Nat.ltb_spec 13 (length l)) as [E3|E3]; [|reflexivity].
  destruct (last_space_from 0 l) as [q|] eqn:E4; [|reflexivity].
  destruct (Nat.ltb_spec 13 q) as [E5|E5]; [|reflexivity].
  exfalso. revert E1. unfold list_eqb.
  destruct (list_eq_dec Z.eq_dec (firstn 13 l) K_GESTURE) as [E1'|_]; intros E1; [|discriminate E1].
  exact (H E1' E2 E3 q eq_refl E5).
Qed.

Lemma gt_begin : forall m, ro_agree rsegs m -> bytes_at rsegs m 0x10358 (map (Z_to_bv 8) W_BEGIN ++ [Z_to_bv 8 0]).
Proof using Bm G HJ O h junk regs.
  intros m Hro.
  pose proof (ro_cells_image rsegs (normalize rsegs m) 0x10358 (map (Z_to_bv 8) W_BEGIN ++ [Z_to_bv 8 0])
                (mem_inv_normalize rsegs m) ltac:(vm_compute; reflexivity) ltac:(lia)
                ltac:(unfold W_BEGIN; cbn; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  exact (proj2 (bytes_at_rel rsegs m (normalize rsegs m) _ _ (mem_rel_normalize rsegs m Hro)) RO).
Qed.

Lemma ret_pc_13c54 : ret_pc (Z_to_bv 64 0x13c54) = Z_to_bv 64 0x13c54.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma seen_gtest : forall s P Q c, DST2 s P Q c -> SR segs c (fun c' => DLN s (S Q) c' \/ DST3 s P Q c').
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & v & -> & RTL1 & G9 & G18 & G19 &
    G10 & Vr & Viff & DLSB1).
  pose proof DLSB1 as (DF1 & LC1).
  pose proof DF1 as (DB & HPQ & HQ & HNZ & HK & HL).
  pose proof LC1 as (RP1 & _ & _ & RO1 & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof EK1 as (_ & _ & _ & _ & _ & _ & K7 & K8 & K9 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RTL1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  assert (RO1' : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  assert (UPOS : 0 < re_used e1) by (rewrite EUd; clear - HPQ; lia).
  assert (BPOS : 0 < re_buf e1) by exact (BP UPOS).
  destruct K9 as [(C0 & _ & U0)|(Cp & BI & BF & BJ & BC)]; [exfalso; clear - U0 UPOS; lia|].
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  set (lb := firstn (Q - P) (skipn P (re_U e1))).
  set (slk := skipn (S Q) (re_U e1)).
  assert (LLB : length lb = (Q - P)%nat).
  { unfold lb. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. clear - LW HPQ. lia. }
  assert (ES : skipn P (re_U e1) = lb ++ Z_to_bv 8 0 :: slk).
  { apply bzs_inj. unfold lb, slk. rewrite bzs_app_cons, <- firstn_bzs, <- !skipn_bzs, EW.
    exact (dW_split s P Q (proj1 HPQ) HQ). }
  assert (E2 : bzs lb = dline s P Q).
  { unfold lb, dline. rewrite <- firstn_bzs, <- skipn_bzs, EW. reflexivity. }
  assert (LD : length (dline s P Q) = (Q - P)%nat) by (rewrite <- E2; unfold bzs; rewrite length_map; exact LLB).
  assert (NZ : ~ In (Z_to_bv 8 0) lb).
  { intros HI. pose proof (dline_nz s P Q HNZ) as NZd. rewrite <- E2 in NZd. unfold nozero in NZd.
    assert (IN0 : In 0 (bzs lb)).
    { unfold bzs. apply in_map_iff. exists (Z_to_bv 8 0). split; [reflexivity | exact HI]. }
    exact (proj1 (Forall_forall _ _) NZd 0 IN0 eq_refl). }
  assert (BL : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P) (lb ++ Z_to_bv 8 0 :: slk)).
  { rewrite <- ES. pose proof BS as T. rewrite <- (firstn_skipn P (re_U e1)) in T.
    apply bytes_at_app in T as [_ T]. rewrite firstn_length_le in T by (clear - LW HPQ; lia).
    rewrite <- SEGS. exact T. }
  assert (L13 : re_buf e1 + Z.of_nat P + 13 < 2 ^ 64) by (clear - BR F4 K8 EUd HPQ; lia).
  assert (LSB : forall q, last_space_from 0 (dline s P Q) = Some q -> (q < Q - P)%nat).
  { intros q E. pose proof (gt_lsf_lt _ _ _ E) as X. rewrite LD in X. clear - X. lia. }
  assert (LST : 0 <= sv_last s P Q (re_buf e1 + Z.of_nat P) /\ sv_last s P Q (re_buf e1 + Z.of_nat P) + 1 < 2 ^ 64).
  { unfold sv_last. destruct (last_space_from 0 (dline s P Q)) as [q|] eqn:E; [|clear; lia].
    pose proof (LSB q eq_refl) as X. clear - X B0 BU EUd HPQ. lia. }
  set (b := nth 13 (lb ++ Z_to_bv 8 0 :: slk) (Z_to_bv 8 0)).
  assert (BVb : bv_unsigned b = nth 13 (dline s P Q ++ 0 :: bzs slk) 0).
  { change (bv_unsigned b) with (bz (nth 13 (lb ++ Z_to_bv 8 0 :: slk) (Z_to_bv 8 0))).
    rewrite <- (map_nth bz (lb ++ Z_to_bv 8 0 :: slk) (Z_to_bv 8 0) 13).
    change (map bz (lb ++ Z_to_bv 8 0 :: slk)) with (bzs (lb ++ Z_to_bv 8 0 :: slk)).
    rewrite bzs_app_cons, E2. reflexivity. }
  assert (BV13 : (13 < length (dline s P Q))%nat -> bv_unsigned b = nth 13 (dline s P Q) 0).
  { intros X. rewrite BVb. apply app_nth1. exact X. }
  assert (BV13e : length (dline s P Q) = 13%nat -> bv_unsigned b = 0).
  { intros X. rewrite BVb, app_nth2 by (rewrite X; lia). rewrite X. reflexivity. }
  assert (HB : v = 0 -> rw_cells rsegs m1 (re_buf e1 + Z.of_nat P + 13) [C1 b]).
  { intros V0. apply (proj1 Viff) in V0.
    pose proof (f_equal (@length Z) V0) as X. rewrite length_firstn in X.
    change (length K_GESTURE) with 13%nat in X.
    assert (LG : (13 <= Q - P)%nat) by (rewrite <- LD; clear - X; lia).
    pose proof BL as (BL0 & BL1 & BL2).
    assert (BB : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P + 13) [b]).
    { split; [clear - BL0; lia|]. split; [cbn [length]; clear - L13; lia|].
      intros i Hi. cbn [length] in Hi. assert (I0 : i = 0%nat) by (clear - Hi; lia). subst i.
      replace (re_buf e1 + Z.of_nat P + 13 + Z.of_nat 0) with (re_buf e1 + Z.of_nat P + Z.of_nat 13) by lia.
      rewrite BL2 by (rewrite length_app, LLB; cbn [length]; clear - LG; lia).
      change (nth_error [b] 0) with (Some b). unfold b. apply nth_error_nth'.
      rewrite length_app, LLB. cbn [length]. clear - LG. lia. }
    pose proof BC as [_ (_ & _ & WW)]. cbn [cells_size csize] in WW.
    split; [split; [exact (conj I I) | exact BB]|].
    rewrite <- SEGS. split; [clear - B0; lia|]. split; [cbn [cells_size csize]; clear - L13; lia|].
    intros i Hi. cbn [cells_size csize] in Hi.
    replace (re_buf e1 + Z.of_nat P + 13 + i) with (re_buf e1 + (Z.of_nat P + 13 + i)) by lia.
    apply WW. clear - Hi LG HPQ EUd K8 Cp. lia. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G10, G18, G19, H23, H26, H27. rewrite SEGS.
    apply dr_gtest with (b := b);
      [exact HB | exact Vr | clear - BPOS; lia | exact L13 | exact (proj1 LST) | exact (proj2 LST)]. }
  intros ms (can & [(FL & x10' & x11' & ->)|(V0 & B32 & LN0 & LN13 & ->)] & EQ);
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  - assert (GN : gesture (dline s P Q) = None).
    { apply gt_none. intros KG SP LT q LJ J13.
      assert (V0 : v = 0) by (apply (proj2 Viff); exact KG).
      assert (Elst : sv_last s P Q (re_buf e1 + Z.of_nat P) = re_buf e1 + Z.of_nat P + Z.of_nat q)
        by (unfold sv_last; rewrite LJ; reflexivity).
      rewrite Elst, (BV13 LT), SP in FL. unfold SPACE in FL. clear - FL V0 J13 B0. lia. }
    assert (ST : forall jb ha ks, seen_tr (dlH s P) (dlka s P) (dline s P Q) jb ha ks = ([], dlka s P, (ha, ks)))
      by (intros jx hx kx; unfold seen_tr; rewrite GN; reflexivity).
    assert (SAR : seen_arr (dlH s P) (dline s P Q) = dlH s P) by (unfold seen_arr; rewrite GN; reflexivity).
    assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
    pose proof RTL2 as (((P2 & P3 & P4 & P8 & P22 & P25) & P23 & P26) & P27).
    assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y9, P27. rewrite SEGS.
      eapply dr_next; clear - B0 BU EUd HPQ; lia. }
    intros ms (can & -> & EQ4).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply SR_ret. left.
    apply (dln_of s P Q R4 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D).
    + unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X4.
    + rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity. simp_regs. f_equal. clear; lia.
    + exact (dlnb_same s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D DLSB1 ST SAR).
  - assert (KG : firstn 13 (dline s P Q) = K_GESTURE) by (apply (proj1 Viff); exact V0).
    assert (LG : (13 <= length (dline s P Q))%nat).
    { pose proof (f_equal (@length Z) KG) as X. rewrite length_firstn in X.
      change (length K_GESTURE) with 13%nat in X. clear - X. lia. }
    assert (LT : (13 < length (dline s P Q))%nat).
    { destruct (Nat.eq_dec (length (dline s P Q)) 13) as [E|E]; [|clear - LG E; lia].
      exfalso. rewrite (BV13e E) in B32. discriminate B32. }
    assert (SP : nth 13 (dline s P Q) 0 = SPACE) by (rewrite <- (BV13 LT); exact B32).
    destruct (gt_lsf_ge (dline s P Q) 0 13 LT SP) as (jj & LJ & J13).
    assert (Elst : sv_last s P Q (re_buf e1 + Z.of_nat P) = re_buf e1 + Z.of_nat P + Z.of_nat jj)
      by (unfold sv_last; rewrite LJ; reflexivity).
    assert (JJ : (13 < jj < Q - P)%nat).
    { split; [|exact (LSB jj LJ)]. destruct (Nat.eq_dec jj 13) as [E|E]; [|clear - J13 E; lia].
      exfalso. apply LN13. rewrite Elst, E. clear; lia. }
    assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
    pose proof RTL2 as (((J2 & J3 & J4 & J8 & J22 & J25) & J23 & J26) & J27).
    assert (Y1 : getr R2 1 = Z_to_bv 64 0x13c54) by rgw X2.
    assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
    assert (Y10 : getr R2 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1)) by (rewrite <- Elst; rgw X2).
    assert (Y11 : getr R2 11 = Z_to_bv 64 0x10358) by rgw X2.
    assert (Y18 : getr R2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
    assert (Y19 : getr R2 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj)) by (rewrite <- Elst; rgw X2).
    assert (Y21 : getr R2 21 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1)) by (rewrite <- Elst; rgw X2).
    set (sx := skipn (S jj) lb).
    set (sy := map (Z_to_bv 8) W_BEGIN).
    assert (BX : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1) (sx ++ [Z_to_bv 8 0])).
    { assert (EL : lb ++ Z_to_bv 8 0 :: slk = firstn (S jj) lb ++ (sx ++ [Z_to_bv 8 0]) ++ slk).
      { unfold sx. rewrite <- (firstn_skipn (S jj) lb) at 1. rewrite <- !app_assoc. reflexivity. }
      pose proof BL as T. rewrite EL in T. apply bytes_at_app in T as [_ T].
      rewrite firstn_length_le in T by (rewrite LLB; clear - JJ; lia). apply bytes_at_app in T as [T _].
      replace (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1) with (re_buf e1 + Z.of_nat P + Z.of_nat (S jj)) by lia.
      exact T. }
    assert (NZX : ~ In (Z_to_bv 8 0) sx).
    { unfold sx. intros HI. apply NZ. rewrite <- (firstn_skipn (S jj) lb). apply in_or_app. right. exact HI. }
    assert (BY : bytes_at rsegs m1 0x10358 (sy ++ [Z_to_bv 8 0])) by exact (gt_begin m1 RO1').
    assert (NZY : ~ In (Z_to_bv 8 0) sy).
    { unfold sy. intros HI. apply (in_map bz) in HI. vm_compute in HI. clear - HI. lia. }
    pose proof SCM as SC0. unfold strcmp_contract in SC0.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y1, Y10, Y11. rewrite SEGS.
      apply SC0 with (sx := sx) (sy := sy).
      - rewrite unsigned_lit by (clear - B0 BU EUd HPQ JJ; lia). exact BX.
      - exact NZX.
      - rewrite unsigned_lit by (clear; lia). exact BY.
      - exact NZY. }
    intros ms (can & (r & x11' & x12' & x13' & -> & RIFF) & EQ').
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ' eq_refl eq_refl) as (R3 & -> & X3).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    rewrite ret_pc_13c54.
    apply SR_ret. right.
    assert (RR : 0 <= bv_unsigned r < 2 ^ 64)
      by (pose proof (bv_unsigned_in_range 64 r) as X; unfold bv_modulus in X; exact X).
    exists R3, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, jj, (bv_unsigned r).
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [exact RR|].
    split.
    { rewrite <- E2, skipn_bzs. split.
      - intros R0. assert (RZ : r = Z_to_bv 64 0) by (rewrite <- (Z_to_bv_bv_unsigned r), R0; reflexivity).
        apply (proj1 RIFF) in RZ. change (skipn (S jj) lb) with sx. rewrite RZ. unfold sy. reflexivity.
      - intros EB. assert (EX : sx = sy).
        { apply bzs_inj. unfold sx. rewrite EB. unfold sy. reflexivity. }
        apply (proj2 RIFF) in EX. rewrite EX. reflexivity. }
    split; [exact KG|]. split; [exact SP|]. split; [exact LJ|]. split; [exact JJ|].
    exact DLSB1.
Qed.

Lemma dl_gesture : forall l jj, firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE -> last_space_from 0 l = Some jj ->
  (13 < jj < length l)%nat ->
  gesture l = if list_eqb (skipn (S jj) l) W_BEGIN then Some (GBegin, firstn jj l)
              else if list_eqb (skipn (S jj) l) W_END then Some (GEnd, firstn jj l) else None.
Proof using.
  intros l jj HK HS HL HLJ. unfold gesture. rewrite HK, HS, HL, list_eqb_refl, Z.eqb_refl. cbv beta iota.
  rewrite (proj2 (Nat.ltb_lt 13 (length l))) by (clear - HLJ; lia).
  rewrite (proj2 (Nat.ltb_lt 13 jj)) by (clear - HLJ; lia). reflexivity.
Qed.

Definition W_END_B : list byte := map (Z_to_bv 8) W_END.

Lemma W_END_B_z : bzs W_END_B = W_END.
Proof using. vm_compute. reflexivity. Qed.

Lemma W_END_B_nz : ~ In (Z_to_bv 8 0) W_END_B.
Proof using.
  unfold W_END_B, W_END. cbn [map In].
  intros [E|[E|[E|[]]]]; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Qed.

Lemma W_END_B_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x103af (W_END_B ++ [Z_to_bv 8 0]).
Proof using.
  intros m MI.
  pose proof (ro_cells_image rsegs m 0x103af (W_END_B ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity)
                ltac:(clear - MI; lia)
                ltac:(change (length (W_END_B ++ [Z_to_bv 8 0])) with 4%nat; clear - MI; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma ret_pc_13c78 : ret_pc (Z_to_bv 64 0x13c78) = Z_to_bv 64 0x13c78.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma seen_gbeg : forall s P Q c, DST3 s P Q c -> SR segs c (fun c' => DGS s P Q c' \/ DST4 s P Q c').
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & jj & r & -> & RTL1 & G9 & G18 & G19 &
    G21 & G10 & RB & RE & HK & HS & HL & JJ & DL).
  pose proof DL as (DF & LC1).
  pose proof DF as (DB & HPQ & HQ & HNZ & _ & _).
  pose proof LC1 as (RP1 & _ & _ & RO1 & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RTL1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  assert (RO1' : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  assert (LLN : length (dline s P Q) = (Q - P)%nat) by exact (dline_len s P Q HPQ).
  set (lb := firstn (Q - P) (skipn P (re_U e1))).
  assert (ES : skipn P (re_U e1) = lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1)).
  { apply bzs_inj. unfold lb. rewrite bzs_app_cons, <- firstn_bzs, <- !skipn_bzs, EW.
    exact (dW_split s P Q (proj1 HPQ) HQ). }
  assert (E2 : bzs lb = dline s P Q).
  { unfold lb, dline. rewrite <- firstn_bzs, <- skipn_bzs, EW. reflexivity. }
  assert (NZb : Forall (fun b : byte => bv_unsigned b <> 0) lb).
  { pose proof (dline_nz s P Q HNZ) as NZd. rewrite <- E2 in NZd. unfold nozero, bzs in NZd.
    apply Forall_forall. intros b Hb. exact (proj1 (Forall_forall _ _) NZd (bz b) (in_map bz lb b Hb)). }
  assert (BL : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P) (lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1))).
  { pose proof BS as T. rewrite <- (firstn_skipn P (re_U e1)), ES in T. apply bytes_at_app in T as [_ T2].
    rewrite firstn_length_le in T2 by (clear - LW HPQ; lia). rewrite <- SEGS. exact T2. }
  assert (LLB : length lb = (Q - P)%nat).
  { rewrite <- LLN, <- E2. unfold bzs. rewrite length_map. reflexivity. }
  assert (BX : bytes_at rsegs m1 (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1) (skipn (S jj) lb ++ [Z_to_bv 8 0])).
  { pose proof BL as T. rewrite <- (firstn_skipn (S jj) lb), <- app_assoc in T.
    apply bytes_at_app in T as [_ T2]. rewrite firstn_length_le in T2 by (clear - LLB JJ; lia).
    replace (skipn (S jj) lb ++ Z_to_bv 8 0 :: skipn (S Q) (re_U e1))
      with ((skipn (S jj) lb ++ [Z_to_bv 8 0]) ++ skipn (S Q) (re_U e1)) in T2 by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in T2 as [T3 _].
    replace (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1) with (re_buf e1 + Z.of_nat P + Z.of_nat (S jj))
      by (clear - JJ; lia).
    exact T3. }
  assert (NZs : ~ In (Z_to_bv 8 0) (skipn (S jj) lb)).
  { intros HI. assert (HI' : In (Z_to_bv 8 0) lb).
    { rewrite <- (firstn_skipn (S jj) lb). apply in_or_app. right. exact HI. }
    pose proof (proj1 (Forall_forall _ _) NZb _ HI') as Z0. cbv beta in Z0. apply Z0. vm_compute. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G10. rewrite SEGS. apply dr_gbeg. exact RB. }
  intros ms (can & HC & EQ). cbv beta in HC.
  destruct HC as [(R0 & ->)|(R0 & ->)].
  - subst r.
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply SR_ret. left.
    exists R2, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, GBegin, jj, 0.
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
    split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|].
    split; [exact RB|].
    split; [split; intros _; reflexivity|].
    split.
    { rewrite (dl_gesture _ jj HK HS HL ltac:(rewrite LLN; exact JJ)), (proj1 RE eq_refl), list_eqb_refl.
      reflexivity. }
    split; [exact JJ | exact DL].
  - destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
    pose proof RTL2 as (((J2 & J3 & J4 & J8 & J22 & J25) & J23 & J26) & J27).
    assert (Y1 : getr R2 1 = Z_to_bv 64 0x13c78) by rgw X2.
    assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
    assert (Y10 : getr R2 10 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj + 1)) by rgw X2.
    assert (Y11 : getr R2 11 = Z_to_bv 64 0x103af) by rgw X2.
    assert (Y18 : getr R2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
    assert (Y19 : getr R2 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat P + Z.of_nat jj)) by rgw X2.
    assert (Y20 : getr R2 20 = Z_to_bv 64 r) by rgw X2.
    pose proof SCM as SC0. unfold strcmp_contract in SC0.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y1, Y10, Y11. rewrite SEGS.
      apply (evt_normalize rsegs); [exact dl_wx | exact RO1' |].
      apply SC0 with (sx := skipn (S jj) lb) (sy := W_END_B).
      - rewrite unsigned_lit by (clear - B0 BU EUd HPQ JJ; lia). exact (bytes_at_normalize rsegs m1 _ _ RO1' BX).
      - exact NZs.
      - change (bv_unsigned (Z_to_bv 64 0x103af)) with 0x103af. apply W_END_B_at, mem_inv_normalize.
      - exact W_END_B_nz. }
    intros ms (can & (s0 & Q0 & REL & ROS) & EQ').
    destruct Q0 as (r' & x11' & x12' & x13' & -> & RE').
    destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
    remember (ms_mem can) as m2 eqn:Em2. subst can. clear Em2.
    pose proof (mem_rel_normalize rsegs m1 RO1') as MRN.
    assert (MU2 : munch [] m1 m2) by (eapply munch_rel; [exact MRN | exact HR | exact ROS | apply munch_refl]).
    assert (WM2 : wmono rsegs m1 m2) by (eapply wmono_rel; [exact MRN | exact HR | exact ROS | apply wmono_refl]).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ' eq_refl eq_refl) as (R3 & -> & X3).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    rewrite ret_pc_13c78.
    apply SR_ret. right.
    exists R3, L1, A1, m2, md1, e1, h1, OUT1, junk1, LB1, D, jj, r, (bv_unsigned r').
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3|].
    split; [rgw X3|]. split; [rgw X3|]. split; [rgw X3|]. split; [rgw X3|].
    split; [exact RB|]. split; [exact R0|].
    split; [intros E; apply R0; apply RE; exact E|].
    split; [rgw X3|].
    split; [pose proof (bv_unsigned_in_range 64 r') as RR; change (bv_modulus 64) with (2 ^ 64) in RR; exact RR|].
    split.
    { rewrite <- E2, skipn_bzs, <- W_END_B_z. split; intros HV.
      - assert (Er : r' = Z_to_bv 64 0) by (apply bv_eq; rewrite HV; vm_compute; reflexivity).
        rewrite (proj1 RE' Er). reflexivity.
      - apply bzs_inj in HV. apply (proj2 RE') in HV. rewrite HV. vm_compute. reflexivity. }
    split; [exact HK|]. split; [exact HS|]. split; [exact HL|]. split; [exact JJ|].
    unfold DLSB. split; [exact DF|].
    apply (core_stk s D _ _ _ _ _ _ _ _ false L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 (S0 - 144) LC1);
      [clear - F1; lia | | exact WM2].
    apply (munch_weaken []); [intros x _; exact I | exact MU2].
Qed.

Lemma seen_gend : forall s P Q c, DST4 s P Q c -> SR segs c (fun c' => DLN s (S Q) c' \/ DGS s P Q c').
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & jj & bg & r & -> & RTL1 & G9 & G18 &
    G19 & G20 & BGr & BG0 & NB & G10 & RB & RE & HK & HS & HL & JJ & DL).
  pose proof DL as (DF & LC1).
  pose proof DF as (DB & HPQ & _).
  pose proof LC1 as (RP1 & _ & _ & _ & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BS & B0 & BU & BP).
  pose proof RTL1 as (((H2 & H3 & H4 & H8 & H22 & H25) & H23 & H26) & H27).
  pose proof (dl_gesture _ jj HK HS HL ltac:(rewrite (dline_len s P Q HPQ); exact JJ)) as GE.
  assert (NBb : list_eqb (skipn (S jj) (dline s P Q)) W_BEGIN = false).
  { destruct (list_eqb (skipn (S jj) (dline s P Q)) W_BEGIN) eqn:E; [|reflexivity].
    exfalso. exact (NB (list_eqb_true _ _ E)). }
  rewrite NBb in GE.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G10. rewrite SEGS. apply dr_gend. exact RB. }
  intros ms (can & HC & EQ). cbv beta in HC.
  destruct HC as [(R0 & ->)|(R0 & ->)];
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  - assert (NEb : list_eqb (skipn (S jj) (dline s P Q)) W_END = false).
    { destruct (list_eqb (skipn (S jj) (dline s P Q)) W_END) eqn:E; [|reflexivity].
      exfalso. exact (R0 (proj2 RE (list_eqb_true _ _ E))). }
    rewrite NEb in GE.
    assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
    pose proof RTL2 as (((P2 & P3 & P4 & P8 & P22 & P25) & P23 & P26) & P27).
    assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y9, P27. rewrite SEGS.
      eapply dr_next; clear - B0 BU EUd HPQ; lia. }
    intros ms (can & -> & EQ4).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply SR_ret. left.
    apply (dln_of s P Q R4 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D).
    + unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X4.
    + rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity. simp_regs. f_equal. clear; lia.
    + apply dlnb_same; [exact DL | intros jx hx kx; unfold seen_tr; rewrite GE; reflexivity |
                         unfold seen_arr; rewrite GE; reflexivity].
  - apply SR_ret. right. subst r.
    exists R2, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, GEnd, jj, bg.
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2|].
    split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|]. split; [rgw X2|].
    split; [exact BGr|].
    split; [split; intros E; [exfalso; exact (BG0 E) | discriminate E]|].
    split; [rewrite GE, (proj1 RE eq_refl), list_eqb_refl; reflexivity|].
    split; [exact JJ | exact DL].
Qed.

Lemma seen_test : forall s P Q c, DLS s P Q c -> SR segs c (fun c' => DLN s (S Q) c' \/ DGS s P Q c').
Proof using All.
  intros s P Q c H0.
  eapply SR_bind; [exact (seen_strrchr s P Q c H0)|]. intros c1 H1.
  eapply SR_bind; [exact (seen_strncmp s P Q c1 H1)|]. intros c2 H2.
  eapply SR_bind; [exact (seen_gtest s P Q c2 H2)|]. intros c3 [H3|H3]; [apply SR_ret; left; exact H3|].
  eapply SR_bind; [exact (seen_gbeg s P Q c3 H3)|]. intros c4 [H4|H4]; [apply SR_ret; right; exact H4|].
  exact (seen_gend s P Q c4 H4).
Qed.

Lemma UE_rp_13ce8 : ret_pc (Z_to_bv 64 0x13ce8) = Z_to_bv 64 0x13ce8.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma UE_rp_13d00 : ret_pc (Z_to_bv 64 0x13d00) = Z_to_bv 64 0x13d00.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma UE_ix_app_none : forall x a b, index_of x a = None ->
  index_of x (a ++ b) = match index_of x b with Some m => Some (length a + m)%nat | None => None end.
Proof using.
  intros x a b. induction a as [|y a IH]; intros E; cbn [app].
  - cbn [length]. destruct (index_of x b) as [m|]; [f_equal; lia | reflexivity].
  - cbn [index_of] in E |- *. destruct (key_eqb y x) eqn:Ey; [discriminate|].
    destruct (index_of x a) as [m0|] eqn:Em; cbn [option_map] in E; [discriminate|].
    rewrite (IH eq_refl). cbn [length]. destruct (index_of x b) as [m|]; cbn [option_map];
      [f_equal; lia | reflexivity].
Qed.

Lemma UE_ix_found : forall x H n, (n < length H)%nat ->
  index_of x (firstn n H) = None -> key_eqb (nth n H []) x = true ->
  index_of x H = Some n.
Proof using HG HJ O h junk.
  intros x H n Hn E Ek.
  rewrite <- (firstn_skipn n H), (UE_ix_app_none x _ _ E).
  assert (Hs : index_of x (skipn n H) = Some 0%nat).
  { destruct (skipn n H) as [|y t] eqn:Es.
    - exfalso. assert (L0 : length (skipn n H) = (length H - n)%nat) by apply length_skipn.
      rewrite Es in L0. cbn [length] in L0. lia.
    - assert (Ey : y = nth n H []).
      { destruct (StrFun.skipn_cons_nth H n y t Es) as [Hne _].
        assert (Hnn : nth_error H n = Some (nth n H [])) by (apply nth_error_nth'; exact Hn).
        rewrite Hne in Hnn. injection Hnn as E2. exact E2. }
      cbn [index_of]. rewrite Ey, Ek. reflexivity. }
  rewrite Hs. cbv iota. rewrite firstn_length_le by lia. f_equal. lia.
Qed.

Lemma UE_firstn_S_nth : forall {X} (l : list X) n (d : X), (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof using Bm G HJ O h junk regs.
  induction l as [|a l IH]; intros n d Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|].
  cbn [firstn nth]. rewrite (IH n d) by (cbn [length] in Hn; lia). reflexivity.
Qed.

Lemma UE_ix_Sn : forall x H n, (n < length H)%nat ->
  index_of x (firstn n H) = None -> key_eqb (nth n H []) x = false ->
  index_of x (firstn (S n) H) = None.
Proof using Bm G HJ O h junk regs.
  intros x H n Hn E Ek. rewrite (UE_firstn_S_nth H n [] Hn), (UE_ix_app_none x _ _ E).
  cbn [index_of option_map]. rewrite Ek. reflexivity.
Qed.

Lemma UE_walk_eq : forall ls rs k, length ls = S k -> length rs = S k ->
  ~ In (Z_to_bv 8 0) ls -> ~ In (Z_to_bv 8 0) rs ->
  forall v, StrFun.strncmp_walk ls rs k = Some v -> (v = 0 <-> ls = rs) /\ -256 < v < 256.
Proof using HG HJ O h junk.
  induction ls as [|a l' IH]; intros rs k Hls Hrs Hnl Hnr v Hw; [cbn [length] in Hls; discriminate|].
  destruct rs as [|b r']; [cbn [length] in Hrs; discriminate|].
  cbn [length] in Hls, Hrs. injection Hls as Hls'. injection Hrs as Hrs'.
  assert (Ha0 : (bv_unsigned a =? 0) = false).
  { apply Z.eqb_neq. intros E. apply Hnl. left. apply bv_eq. rewrite E. reflexivity. }
  assert (Hb0 : (bv_unsigned b =? 0) = false).
  { apply Z.eqb_neq. intros E. apply Hnr. left. apply bv_eq. rewrite E. reflexivity. }
  pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
  change (bv_modulus 8) with 256 in Ra, Rb.
  assert (Hnl' : ~ In (Z_to_bv 8 0) l') by (intros H; apply Hnl; right; exact H).
  assert (Hnr' : ~ In (Z_to_bv 8 0) r') by (intros H; apply Hnr; right; exact H).
  cbn [StrFun.strncmp_walk] in Hw. rewrite Ha0, Hb0 in Hw. cbn [orb] in Hw.
  destruct (bv_unsigned a =? bv_unsigned b) eqn:Eab; cbn [negb] in Hw.
  - apply Z.eqb_eq in Eab. rewrite Bool.orb_false_r in Hw.
    destruct k as [|k0]; cbn [Nat.eqb] in Hw.
    + injection Hw as <-.
      assert (l' = []) by (apply length_zero_iff_nil; exact Hls').
      assert (r' = []) by (apply length_zero_iff_nil; exact Hrs'). subst l' r'.
      split; [|lia]. split; intros E.
      * f_equal. apply bv_eq. lia.
      * injection E as Eab2. apply bv_eq in Eab2. lia.
    + destruct (IH r' k0 Hls' Hrs' Hnl' Hnr' v Hw) as [Hiff Hvb]. split; [|exact Hvb].
      split; intros E.
      * apply (proj1 Hiff) in E. f_equal; [apply bv_eq; exact Eab | exact E].
      * injection E as _ El'. apply (proj2 Hiff). exact El'.
  - rewrite Bool.orb_true_r in Hw. injection Hw as <-. apply Z.eqb_neq in Eab.
    split; [|lia]. split; intros E; [lia|].
    exfalso. injection E as Eab2 _. apply Eab. rewrite Eab2. reflexivity.
Qed.

Lemma UE_walk_total : forall ls rs k, length ls = S k -> length rs = S k ->
  exists v, StrFun.strncmp_walk ls rs k = Some v.
Proof using.
  induction ls as [|a l' IH]; intros rs k Hls Hrs; [discriminate|].
  destruct rs as [|b r']; [discriminate|].
  cbn [length] in Hls, Hrs. injection Hls as Hls'. injection Hrs as Hrs'.
  cbn [StrFun.strncmp_walk].
  destruct ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 ||
            negb (bv_unsigned a =? bv_unsigned b))%bool.
  - eexists; reflexivity.
  - destruct k as [|k0]; [eexists; reflexivity | exact (IH r' k0 Hls' Hrs')].
Qed.

Lemma UE_strlen : forall R1 m1 md1 (p : Z) (str slack : list byte) (Pc : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> ro_agree segs m1 ->
  getr R1 10 = Z_to_bv 64 p -> 0 <= p ->
  p + Z.of_nat (length str) + 1 + Z.of_nat (length slack) < 2 ^ 64 ->
  bytes_at segs m1 p (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (forall R2, getr R2 1 = getr R1 1 -> getr R2 2 = getr R1 2 -> getr R2 3 = getr R1 3 ->
     getr R2 4 = getr R1 4 -> getr R2 8 = getr R1 8 -> getr R2 9 = getr R1 9 -> getr R2 18 = getr R1 18 ->
     getr R2 19 = getr R1 19 -> getr R2 20 = getr R1 20 -> getr R2 21 = getr R1 21 -> getr R2 22 = getr R1 22 ->
     getr R2 23 = getr R1 23 -> getr R2 24 = getr R1 24 -> getr R2 25 = getr R1 25 -> getr R2 26 = getr R1 26 ->
     getr R2 27 = getr R1 27 -> getr R2 10 = Z_to_bv 64 (Z.of_nat (length str)) ->
     SR segs (mkCfg (YK11.mkst R2 (ret_pc (getr R1 1)) m1 (seg_rom segs)) md1) Pc) ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 STRLEN) m1 (seg_rom segs)) md1) Pc.
Proof using HG HJ O SEGS SLN h junk.
  intros R1 m1 md1 p str slack Pc Hh Hl RO G10 Hp Hpb BS Hnz Hsl K.
  rewrite SEGS in RO, BS.
  pose proof SLN as SL. unfold strlen_contract in SL.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G10. rewrite SEGS.
    apply (evt_normalize rsegs); [exact dl_wx | exact RO |].
    apply SL with (str := str) (slack := slack).
    - rewrite unsigned_lit by lia. exact (bytes_at_normalize rsegs m1 p _ RO BS).
    - exact Hnz.
    - rewrite unsigned_lit by lia. exact Hsl.
    - apply mem_inv_normalize. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & -> &
    MU1' & _ & _ & _).
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m2 eqn:Em2. subst can1. clear Em2.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m1 RO) HR1 ROS1 MU1') as MU1.
  assert (ME : m2 = m1).
  { apply FunctionalExtensionality.functional_extensionality. intros x. apply MU1. exact I. }
  subst m2.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  apply K; rgw X2.
Qed.

Lemma UE_strncmp : forall R1 m1 md1 (p q cnt v : Z) (ls rs : list byte) (Pc : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> ro_agree segs m1 ->
  getr R1 10 = Z_to_bv 64 p -> getr R1 11 = Z_to_bv 64 q -> getr R1 12 = Z_to_bv 64 cnt ->
  0 <= cnt < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  bytes_at segs m1 p ls -> bytes_at segs m1 q rs -> StrFun.strncmp_model ls rs cnt = Some v ->
  (forall R2, getr R2 1 = getr R1 1 -> getr R2 2 = getr R1 2 -> getr R2 3 = getr R1 3 ->
     getr R2 4 = getr R1 4 -> getr R2 8 = getr R1 8 -> getr R2 9 = getr R1 9 -> getr R2 18 = getr R1 18 ->
     getr R2 19 = getr R1 19 -> getr R2 20 = getr R1 20 -> getr R2 21 = getr R1 21 -> getr R2 22 = getr R1 22 ->
     getr R2 23 = getr R1 23 -> getr R2 24 = getr R1 24 -> getr R2 25 = getr R1 25 -> getr R2 26 = getr R1 26 ->
     getr R2 27 = getr R1 27 -> getr R2 10 = Z_to_bv 64 v ->
     SR segs (mkCfg (YK11.mkst R2 (ret_pc (getr R1 1)) m1 (seg_rom segs)) md1) Pc) ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 STRNCMP) m1 (seg_rom segs)) md1) Pc.
Proof using G HJ O SEGS SNC h junk regs.
  intros R1 m1 md1 p q cnt v ls rs Pc Hh Hl RO G10 G11 G12 Hcnt Hp Hq BSl BSr HM K.
  rewrite SEGS in RO, BSl, BSr.
  pose proof SNC as SN. unfold strncmp_contract in SN.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G10, G11, G12. rewrite SEGS.
    apply (evt_normalize rsegs); [exact dl_wx | exact RO |].
    apply SN with (ls := ls) (rs := rs) (v := v).
    - rewrite unsigned_lit by lia. exact (bytes_at_normalize rsegs m1 p _ RO BSl).
    - rewrite unsigned_lit by lia. exact (bytes_at_normalize rsegs m1 q _ RO BSr).
    - rewrite unsigned_lit by lia. exact HM.
    - apply mem_inv_normalize. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & -> &
    MU1' & _ & _ & _ & _).
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m2 eqn:Em2. subst can1. clear Em2.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m1 RO) HR1 ROS1 MU1') as MU1.
  assert (ME : m2 = m1).
  { apply FunctionalExtensionality.functional_extensionality. intros x. apply MU1. exact I. }
  subst m2.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  apply K; rgw X2.
Qed.

Lemma UE_c8cb3 : forall m ad (w0 w1 w2 : word),
  rw_cells rsegs m ad [C8 w0; C8 w1; C8 w2] -> rw_cells rsegs m ad [CB 8 (le8 w0); CB 8 (le8 w1); CB 8 (le8 w2)].
Proof using.
  intros m ad w0 w1 w2 ((WF & BS) & WR). split.
  - split.
    + cbn [cells_wf cell_wf]. split; [apply length_le8|]. split; [apply length_le8|].
      split; [apply length_le8 | exact I].
    + cbn [cells_bytes cbytes] in BS |- *. exact BS.
  - cbn [cells_size csize] in WR |- *. exact WR.
Qed.

Lemma UE_c8I : forall sg m ad (v : word), 0 <= ad -> ad + 8 <= 2 ^ 64 ->
  bytes_at sg m ad (le8 v) -> (forall i, 0 <= i < 8 -> writable_at sg m (ad + i)) ->
  rw_cells sg m ad [C8 v].
Proof using Bm G HJ O h junk regs.
  intros sg m ad v H0 H1 BS WR. split.
  - split; [cbn [cells_wf cell_wf]; split; exact I | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BS].
  - cbn [cells_size csize]. split; [exact H0|]. split; [lia|]. intros i Hi. exact (WR i Hi).
Qed.

Lemma UE_keyslot : forall L1 A1 m1 md1 e1 (n : nat),
  MR L1 A1 m1 md1 -> entry_okx L1 A1 m1 e1 -> (n < length (re_keys e1))%nat -> re_hp e1 <> 0 ->
  rw_cells rsegs m1 (re_hp e1 + 8 * Z.of_nat n) [C8 (Z_to_bv 64 (key_addr (nth n (re_keys e1) (0, [], []))))].
Proof using BW HG HJ O SEGS h junk.
  intros L1 A1 m1 md1 e1 n HM EK NL HP0.
  pose proof EK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E11 & _).
  destruct E11 as [(H0 & _)|(HI & HF & H8 & H8' & HB)]; [exfalso; exact (HP0 H0)|].
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  remember (nth n (re_keys e1) (0, [], [])) as k eqn:Ek.
  assert (NE : nth_error (re_keys e1) n = Some k) by (rewrite Ek; apply nth_error_nth'; exact NL).
  destruct (nth_error_split _ _ _ NE) as (ka & kb & Eks & Lka).
  assert (BSlot : bytes_at segs m1 (re_hp e1 + 8 * Z.of_nat n) (le8 (Z_to_bv 64 (key_addr k)))).
  { pose proof HB as X. rewrite Eks, CF.gestures_end_b.key_ptrs_app in X. apply bytes_at_app in X as [_ X].
    rewrite CF.gestures_end_b.key_ptrs_length, CF.gestures_end_b.key_ptrs_cons in X.
    apply bytes_at_app in X as [X _].
    replace (re_hp e1 + Z.of_nat (8 * length ka)) with (re_hp e1 + 8 * Z.of_nat n) in X by (rewrite Lka; lia).
    exact X. }
  pose proof (blk_rng _ _ _ _ _ _ HM HI) as (BR1 & BR2).
  unfold re_nheld in H8.
  apply (UE_c8I rsegs m1 (re_hp e1 + 8 * Z.of_nat n) (Z_to_bv 64 (key_addr k))).
  - lia.
  - clear - BR1 BR2 NL H8 ACL. nia.
  - rewrite <- SEGS. exact BSlot.
  - intros i Hi. rewrite <- SEGS.
    replace (re_hp e1 + 8 * Z.of_nat n + i) with (re_hp e1 + (8 * Z.of_nat n + i)) by ring.
    apply (BW _ _ _ _ (re_hp e1) (re_kh e1) _ HM HI). clear - Hi NL H8. nia.
Qed.

Lemma UE_c8w : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> writable_at rsegs m (a + i)) -> exists v, rw_cells rsegs m a [C8 v].
Proof using Bm G HJ O h junk regs.
  intros m a H0 H1 W.
  destruct (sb_wr_rd m (a + 0) (W 0 ltac:(lia))) as [b0 E0].
  destruct (sb_wr_rd m (a + 1) (W 1 ltac:(lia))) as [b1 E1].
  destruct (sb_wr_rd m (a + 2) (W 2 ltac:(lia))) as [b2 E2].
  destruct (sb_wr_rd m (a + 3) (W 3 ltac:(lia))) as [b3 E3].
  destruct (sb_wr_rd m (a + 4) (W 4 ltac:(lia))) as [b4 E4].
  destruct (sb_wr_rd m (a + 5) (W 5 ltac:(lia))) as [b5 E5].
  destruct (sb_wr_rd m (a + 6) (W 6 ltac:(lia))) as [b6 E6].
  destruct (sb_wr_rd m (a + 7) (W 7 ltac:(lia))) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (L8 : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
    exact (sb_le_rt [b0; b1; b2; b3; b4; b5; b6; b7]). }
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, L8. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error];
      [exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (W i Hi).
Qed.

Lemma UE_gtr : forall s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 (v0 v1 v2 v4 : word),
  LCORE s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 ->
  munch [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)] m1 m2 -> wmono rsegs m1 m2 ->
  rw_cells rsegs m2 (S0 - 144) [C8 v0; C8 v1; C8 v2] -> rw_cells rsegs m2 (S0 - 144 + 32) [C8 v4] ->
  LCORE s D sent kl Hk ka no oc nk rest sk L1 A1 m2 md1 e1 h1 OUT1 junk1 LB1.
Proof using AX BW EHI EU GCP GEI GRP HG HJ OUTD PRE SEGS.
  intros s D sent kl Hk ka no oc nk rest sk L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 m2 v0 v1 v2 v4
    (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NB1 & RS1 & BK1 & GL1 & OU1)
    MU WM C3 C4.
  hide. pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  assert (DK : DRAIN_K = 8512) by reflexivity.
  pose proof RP1 as (M1 & _).
  assert (WM' : wmono segs m1 m2) by (rewrite SEGS; exact WM).
  pose proof (msame_munch _ _ _ MU WM') as MS.
  assert (PL : forall a, 0 <= a < YM05.alloc_ceiling ->
            0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)] a).
  { intros a Ha. split; [clear - Ha F4; lia|]. cbn [outside].
    split; [clear - Ha F1; lia|]. split; [clear - Ha F1; lia | exact I]. }
  assert (PI : forall a, in_img Bm a ->
            0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)] a).
  { intros a Ha. pose proof (img_lo a Ha) as IL. apply PL. clear - IL F3. lia. }
  assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> q <= a < q + k ->
            0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)] a).
  { intros q k a Hq Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR. apply PL. clear - Ha BR. lia. }
  assert (PF : forall a, (S0 - 144 + 24 <= a < S0 - 144 + 32 \/ S0 - 144 + 40 <= a < S0) ->
            0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)] a).
  { intros a Ha. split; [clear - Ha F1 F2 F3; lia|]. cbn [outside].
    split; [clear - Ha; lia|]. split; [clear - Ha; lia | exact I]. }
  assert (PIa : forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX ->
            0 <= a < 2 ^ 64 /\ outside [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)] a).
  { intros a Ha. apply PI. exact (proj1 (GRP a ltac:(clear - Ha; unfold G_RELAY_LO, G_S in *; lia))). }
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MU); [exact WM' | exact GEI |].
    intros a Ha. destruct (Z_lt_le_dec a (S0 - 144)) as [D0|D0].
    { left. cbn [outside]. split; [clear - D0; lia|]. split; [clear - D0; lia | exact I]. }
    destruct (Z_lt_le_dec a (S0 - 144 + 40)) as [D2|D2].
    2:{ left. cbn [outside]. split; [clear - D2; lia|]. split; [clear - D2; lia | exact I]. }
    right. left. change (spZ regs) with S0. rewrite DK. clear - D0 D2 F1. lia. }
  split; [exact IN1|]. split; [exact TR1|].
  split.
  { rewrite SEGS. apply (ro_munch2 m1 m2 [(S0 - 144, S0 - 144 + 24); (S0 - 144 + 32, S0 - 144 + 40)]);
      [rewrite <- SEGS; exact RO1 | exact MU |].
    intros x Hx. exact (proj2 (PI _ Hx)). }
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FR). rewrite SEGS in FR.
    destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 24) [CB 8 j0; CB 8 j1; CB 8 j2]
                ([C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED) FR ltac:(cbn [cells_size csize]; lia)) as [_ FRt].
    destruct (dr_cut m1 (S0 - 144 + 24) (S0 - 144 + 32) [C8 (Z_to_bv 64 6001)] ([CB 8 j4] ++ SAVED) FRt
                ltac:(cbn [cells_size csize]; lia)) as [F61 FRt2].
    destruct (dr_cut m1 (S0 - 144 + 32) (S0 - 144 + 40) [CB 8 j4] SAVED FRt2
                ltac:(cbn [cells_size csize]; lia)) as [_ FSV].
    rewrite <- SEGS in F61, FSV.
    assert (F61' : rw_cells segs m2 (S0 - 144 + 24) [C8 (Z_to_bv 64 6001)]).
    { eapply rw_tr; [exact MS | exact F61 |]. intros a Ha. cbn [cells_size csize] in Ha. apply PF. clear - Ha. lia. }
    assert (FSV' : rw_cells segs m2 (S0 - 144 + 40) SAVED).
    { eapply rw_tr; [exact MS | exact FSV |]. intros a Ha. unfold dr_saved in Ha. cbn [cells_size csize app] in Ha.
      apply PF. clear - Ha. lia. }
    rewrite SEGS in F61', FSV'.
    exists (le8 v0), (le8 v1), (le8 v2), (le8 v4). rewrite SEGS.
    apply (dr_join m2 (S0 - 144) (S0 - 144 + 24) [CB 8 (le8 v0); CB 8 (le8 v1); CB 8 (le8 v2)]
             ([C8 (Z_to_bv 64 6001); CB 8 (le8 v4)] ++ SAVED));
      [exact (UE_c8cb3 m2 _ v0 v1 v2 C3) | | cbn [cells_size csize]; lia].
    apply (dr_join m2 (S0 - 144 + 24) (S0 - 144 + 32) [C8 (Z_to_bv 64 6001)] ([CB 8 (le8 v4)] ++ SAVED));
      [exact F61' | | cbn [cells_size csize]; lia].
    apply (dr_join m2 (S0 - 144 + 32) (S0 - 144 + 40) [CB 8 (le8 v4)] SAVED);
      [exact (dr_c8_cb m2 _ v4 C4) | exact FSV' | cbn [cells_size csize]; lia]. }
  split.
  { eapply rw_tr; [exact MS | exact SAC1 |]. intros a Ha. apply PL. cbn [cells_size csize] in Ha.
    clear - Ha F5 F6 F7 F8. lia. }
  split.
  { eapply entry_okx_tr; [exact MS | exact EK1 | |].
    - intros q k Hq _. exact Hq.
    - intros q k a Hq _ Ha. exact (PB q k a Hq Ha). }
  split.
  { eapply src_at_tr0; [exact MS | exact SR1 | | |].
    - intros a Ha. apply PIa. clear - Ha F11. unfold G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - intros q k Hq _. exact Hq.
    - intros q k a Hq _ Ha. exact (PB q k a Hq Ha). }
  split.
  { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi _ Ha. apply PIa.
    clear - Ha Hi. unfold G_S, SRC_SIZE, SOURCES_MAX in *. lia. }
  split; [exact SM1|]. split; [exact LK1|]. split; [exact HI1|]. split; [exact NB1|]. split; [exact RS1|].
  split; [exact BK1|].
  split.
  { destruct GL1 as (G1c & G2c & G3c & G4c & (ev1 & G5c)).
    split; [eapply rw_tr; [exact MS | exact G1c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GCP a ltac:(clear - Ha; lia)))|].
    split; [eapply rw_tr; [exact MS | exact G2c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [eapply rw_tr; [exact MS | exact G3c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [eapply rw_tr; [exact MS | exact G4c |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    exists ev1. eapply rw_tr; [exact MS | exact G5c |]. intros a Ha. apply PI. cbn [cells_size csize] in Ha.
    apply GEI. clear - Ha. lia. }
  destruct OU1 as (OF1 & OT1'). hide.
  assert (LOO : Z.of_nat (length O) = NO).
  { destruct OUTD as [(_ & _ & N0 & E0)|(_ & _ & _ & _ & _ & L0 & _)];
      [rewrite E0; cbn [length Z.of_nat]; clear - N0; lia | exact L0]. }
  split.
  - intros LV. destruct (OF1 LV) as (C1 & E1 & E2 & E3).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    split; [exact E1|]. split; [exact E2|].
    intros Cp. destruct (E3 Cp) as (I3 & B3). split; [exact I3|].
    eapply by_tr; [exact MS | exact B3 |]. intros a Ha. apply (PB OUT CAP a I3).
    destruct OUTD as [(C0' & _)|(_ & _ & _ & _ & _ & L0 & LJ)]; [clear - C0' Cp; lia|].
    rewrite length_app in Ha. clear - Ha L0 LJ. lia.
  - intros LV. destruct (OT1' LV) as (C1 & D1).
    split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
            exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                      lia)))|].
    destruct D1 as [D1|(Cp & NL & I3 & F3' & B3 & LJ)]; [left; exact D1 | right].
    split; [exact Cp|]. split; [exact NL|]. split; [exact I3|]. split; [exact F3'|].
    split; [|exact LJ].
    eapply by_tr; [exact MS | exact B3 |]. intros a Ha. apply (PB OUT1 _ a I3).
    pose proof HI1 as (_ & _ & _ & _ & _ & HN & HLB & _).
    assert (LL : Z.of_nat (length LB1) = Z.of_nat (length (with_nul sent)))
      by (rewrite <- HLB; unfold bzs; rewrite length_map; reflexivity).
    rewrite !length_app in Ha. clear - Ha LOO LL LJ HN. lia.
Qed.

Definition UE_SCANI (s : dstate) (P Q n : nat) (c : config) : Prop :=
  exists R1 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (k : gkind) (jj : nat) (bg : Z),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13cc4) m1 (seg_rom segs)) md1 /\ RT R1 /\
    getr R1 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) /\ getr R1 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) /\
    getr R1 19 = Z_to_bv 64 (8 * Z.of_nat n) /\ getr R1 20 = Z_to_bv 64 1 /\
    getr R1 24 = Z_to_bv 64 (re_nheld e1 - Z.of_nat n) /\ getr R1 26 = Z_to_bv 64 (re_hp e1) /\
    getr R1 27 = Z_to_bv 64 1 /\
    rw_cells rsegs m1 (S0 - 144)
      [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 (re_nheld e1)); C8 (Z_to_bv 64 (re_nheld e1 * 8))] /\
    rw_cells rsegs m1 (S0 - 144 + 32) [C8 (Z_to_bv 64 (Z.of_nat jj))] /\
    0 <= bg < 2 ^ 64 /\ (bg = 0 <-> k = GBegin) /\
    gesture (dline s P Q) = Some (k, firstn jj (dline s P Q)) /\ (13 < jj < Q - P)%nat /\
    (n < length (dlH s P))%nat /\ index_of (firstn jj (dline s P Q)) (firstn n (dlH s P)) = None /\
    DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D.

Lemma UE_after : forall s P Q (n : nat) R m1 md1 L1 A1 e1 h1 OUT1 junk1 LB1 D (k : gkind) (jj : nat) (bg : Z),
  RT R -> getr R 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q) -> getr R 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P) ->
  getr R 19 = Z_to_bv 64 (8 * Z.of_nat n) -> getr R 20 = Z_to_bv 64 1 ->
  getr R 24 = Z_to_bv 64 (re_nheld e1 - Z.of_nat n) -> getr R 26 = Z_to_bv 64 (re_hp e1) ->
  getr R 27 = Z_to_bv 64 1 ->
  rw_cells rsegs m1 (S0 - 144)
    [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 (re_nheld e1)); C8 (Z_to_bv 64 (re_nheld e1 * 8))] ->
  rw_cells rsegs m1 (S0 - 144 + 32) [C8 (Z_to_bv 64 (Z.of_nat jj))] ->
  0 <= bg < 2 ^ 64 -> (bg = 0 <-> k = GBegin) ->
  gesture (dline s P Q) = Some (k, firstn jj (dline s P Q)) -> (13 < jj < Q - P)%nat ->
  (n < length (dlH s P))%nat -> index_of (firstn jj (dline s P Q)) (firstn (S n) (dlH s P)) = None ->
  DLSB s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D ->
  SR segs (mkCfg (YK11.mkst R (Z_to_bv 64 0x13d04) m1 (seg_rom segs)) md1)
    (fun c' => UE_SCANI s P Q (S n) c' \/ DGA s P Q c').
Proof using All.
  intros s P Q n R m1 md1 L1 A1 e1 h1 OUT1 junk1 LB1 D k jj bg
    RT0 H9 H18 H19 H20 H24 H26 H27 SPc SPk BGb BGk GES JJ NLn IXsn LC1.
  pose proof LC1 as [DFs LCc].
  pose proof LCc as (RP1 & _ & _ & _ & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof RT0 as (H2 & H3 & H4 & H8 & H22 & H25).
  pose proof EK1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & _).
  pose proof LK1 as (_ & _ & _ & L4c & _).
  assert (HLEN : length (dlH s P) = length (re_keys e1))
    by (rewrite <- (L4c : keys_texts (re_keys e1) = dlH s P); unfold keys_texts; apply length_map).
  assert (RNH : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
  rewrite HLEN in NLn.
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 16) [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 (re_nheld e1))]
              [C8 (Z_to_bv 64 (re_nheld e1 * 8))] SPc ltac:(cbn [cells_size csize]; lia)) as [SPbn SP16].
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, H2, H19, H24. rewrite SEGS.
    eapply dr_hstep;
      [exact SP16 | lia | rewrite RNH in E10; clear - E10 NLn; nia |
       rewrite RNH in E10 |- *; clear - E10; split; [lia | nia] | rewrite RNH in E10 |- *; clear - E10 NLn; lia]. }
  intros ms (can & [(NEstep & ->)|(EQstep & ->)] & EQ);
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & X');
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  - apply SR_ret. left. exists R', L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, k, jj, bg.
    split; [reflexivity|].
    split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X'|].
    split; [rgw X'|]. split; [rgw X'|].
    split; [replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia; rgw X'|].
    split; [rgw X'|].
    split; [replace (re_nheld e1 - Z.of_nat (S n)) with (re_nheld e1 - Z.of_nat n - 1) by lia; rgw X'|].
    split; [rgw X'|]. split; [rgw X'|].
    split; [exact SPc|]. split; [exact SPk|]. split; [exact BGb|]. split; [exact BGk|]. split; [exact GES|].
    split; [exact JJ|].
    split; [rewrite HLEN; rewrite RNH in NEstep; clear - NEstep NLn; lia|].
    split; [exact IXsn|]. exact LC1.
  - apply SR_ret. right. unfold DGA. exists R', L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, k, jj, bg.
    split; [reflexivity|].
    split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X'|].
    split; [rgw X'|]. split; [rgw X'|].
    split; [rewrite SEGS; exact SPbn|]. split; [rewrite SEGS; exact SPk|].
    split; [exact BGb|]. split; [exact BGk|]. split; [exact GES|]. split; [exact JJ|].
    split.
    { assert (Hdl : firstn (S n) (dlH s P) = dlH s P)
        by (apply firstn_all2; rewrite HLEN; rewrite RNH in EQstep; clear - EQstep NLn; lia).
      rewrite <- Hdl. exact IXsn. }
    exact LC1.
Qed.

Lemma UE_body : forall s P Q n c, UE_SCANI s P Q n c ->
  SR segs c (fun c' => UE_SCANI s P Q (S n) c' \/ DLN s (S Q) c' \/ DGA s P Q c' \/ DGF s P Q c').
Proof using All.
  intros s P Q n c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & k & jj & bg & -> & RT1 & G9 & G18 &
    G19 & G20 & G24 & G26 & G27 & SPc & SPk & BGb & BGk & GES & JJ & NLn & IXn & LC1).
  pose proof LC1 as [DFs LCc].
  pose proof LCc as (RP1 & _ & _ & RO1 & _ & _ & EK1 & _ & _ & _ & LK1 & _).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof DFs as (DBd & PQ & HQz & HNZ & HSKp & HLL).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & _).
  pose proof EK1 as (K1e & K2e & K3e & K4e & K5e & K6e & K7e & K8e & K9e & K10e & K11e & K12e & K13e & K14e).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BSb & B0b & BU & BP).
  assert (HLEN : length (dlH s P) = length (re_keys e1))
    by (rewrite <- (L4c : keys_texts (re_keys e1) = dlH s P); unfold keys_texts; apply length_map).
  assert (NLk : (n < length (re_keys e1))%nat) by (rewrite <- HLEN; exact NLn).
  assert (RNH : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
  assert (HP0 : re_hp e1 <> 0).
  { destruct K11e as [(H0 & KS0)|(HI & _)]; [rewrite KS0 in NLk; cbn [length] in NLk; clear - NLk; lia|].
    pose proof (blk_rng _ _ _ _ _ _ M1 HI) as (BR1 & _). clear - BR1; lia. }
  assert (HPb : 0 < re_hp e1 /\ re_hp e1 + 8 * re_nheld e1 <= YM05.alloc_ceiling).
  { destruct K11e as [(H0 & _)|(HI & _ & H8 & _)]; [exfalso; exact (HP0 H0)|].
    pose proof (blk_rng _ _ _ _ _ _ M1 HI) as (BR1 & BR2). clear - BR1 BR2 H8 HP0. lia. }
  pose proof (UE_keyslot L1 A1 m1 md1 e1 n M1 EK1 NLk HP0) as Hslot.
  remember (nth n (re_keys e1) (0, [], [])) as kn eqn:Ekn.
  assert (IKn : In kn (re_keys e1)) by (rewrite Ekn; apply nth_In; exact NLk).
  destruct (proj1 (Forall_forall _ _) K14e kn IKn) as (KK1 & KF & KB & KZ & KL).
  assert (ENth : nth n (dlH s P) [] = bzs (key_text kn)).
  { rewrite Ekn, <- (L4c : keys_texts (re_keys e1) = dlH s P). unfold keys_texts.
    rewrite (nth_indep (map (fun k => bzs (key_text k)) (re_keys e1)) []
               (bzs (key_text (0, [], [])))) by (rewrite length_map; exact NLk).
    exact (map_nth (fun k => bzs (key_text k)) (re_keys e1) (0, [], []) n). }
  remember (firstn jj (skipn P (re_U e1))) as buf eqn:Ebuf.
  assert (LB : length buf = jj)
    by (rewrite Ebuf; apply firstn_length_le; rewrite length_skipn; clear - LW PQ JJ; lia).
  assert (EB : bzs buf = firstn jj (dline s P Q)).
  { rewrite Ebuf, <- firstn_bzs, <- skipn_bzs, EW. unfold dline. rewrite firstn_firstn, Nat.min_l by (clear - JJ; lia).
    reflexivity. }
  assert (BB : bytes_at segs m1 (re_buf e1 + Z.of_nat P) buf).
  { pose proof BSb as X. rewrite <- (firstn_skipn P (re_U e1)) in X. apply bytes_at_app in X as [_ X].
    rewrite <- (firstn_skipn jj (skipn P (re_U e1))) in X. apply bytes_at_app in X as [X _].
    rewrite firstn_length_le in X by (clear - LW PQ; lia). rewrite Ebuf. exact X. }
  assert (NZx : nozero (bzs buf)).
  { rewrite Ebuf, <- firstn_bzs, <- skipn_bzs, EW. apply nz_firstn. intros i Hi. rewrite nth_skipn. apply HNZ.
    clear - Hi JJ; lia. }
  assert (NZb : ~ In (Z_to_bv 8 0) buf).
  { intros Hin. unfold nozero in NZx. rewrite Forall_forall in NZx.
    apply (NZx (bz (Z_to_bv 8 0))); [unfold bzs; apply in_map; exact Hin | reflexivity]. }
  pose proof (blk_rng _ _ _ _ _ _ M1 KK1) as (BRk1 & BRk2).
  destruct (dx_slack L1 A1 m1 md1 (key_addr kn) (Z.of_nat (length (key_text kn))) M1 KK1
              ltac:(clear - BRk1; lia) ltac:(apply Nat2Z.is_nonneg) ltac:(clear - BRk2 ACL; lia))
    as (slack & Lslack & BSslack).
  assert (BKK : bytes_at segs m1 (key_addr kn) (key_text kn ++ Z_to_bv 8 0 :: slack)).
  { replace (key_text kn ++ Z_to_bv 8 0 :: slack) with ((key_text kn ++ [Z_to_bv 8 0]) ++ slack)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact KB|]. rewrite length_app. cbn [length].
    replace (key_addr kn + Z.of_nat (length (key_text kn) + 1))
      with (key_addr kn + Z.of_nat (length (key_text kn)) + 1) by (clear - kn; lia). exact BSslack. }
  assert (KBt : bytes_at segs m1 (key_addr kn) (key_text kn))
    by (pose proof KB as KBc; apply bytes_at_app in KBc as [KBc _]; exact KBc).
  assert (KADDR : 0 <= key_addr kn < 2 ^ 64) by (clear - BRk1 BRk2 ACL; lia).
  assert (BUFADDR : 0 <= re_buf e1 + Z.of_nat P < 2 ^ 64) by (clear - B0b BU EUd PQ; lia).
  assert (JJ64 : 0 <= Z.of_nat jj < 2 ^ 64) by (clear - JJ PQ EUd BU B0b; lia).
  assert (CNT : 1 <= re_nheld e1 - Z.of_nat n < 2 ^ 31) by (rewrite RNH; clear - NLk K10e RNH; lia).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G19, G20, G26, G27. rewrite SEGS.
    eapply dr_hlen; [reflexivity | exact Hslot | clear - HPb; lia | clear - n; lia]. }
  intros ms1 (can1 & -> & EQ1).
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  assert (b1 : getr R2 1 = Z_to_bv 64 0x13ce8) by rgw X2.
  assert (b10 : getr R2 10 = Z_to_bv 64 (key_addr kn)) by rgw X2.
  apply (UE_strlen R2 m1 md1 (key_addr kn) (key_text kn) slack);
    [exact Hh | exact Hl | exact RO1 | exact b10 | clear - BRk1; lia | clear - BRk2 Lslack ACL; lia | exact BKK |
     exact KZ | clear - Lslack; lia |].
  intros R3 S1 S2 S3 S4 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 S10r.
  rewrite b1, UE_rp_13ce8.
  assert (c2 : getr R3 2 = Z_to_bv 64 (S0 - 144)) by (rewrite S2; rgw X2).
  assert (c3 : getr R3 3 = getr regs 3) by (rewrite S3; rgw X2).
  assert (c4 : getr R3 4 = getr regs 4) by (rewrite S4; rgw X2).
  assert (c8 : getr R3 8 = Z_to_bv 64 SA) by (rewrite S8; rgw X2).
  assert (c9 : getr R3 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by (rewrite S9; rgw X2).
  assert (c18 : getr R3 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by (rewrite S18; rgw X2).
  assert (c19 : getr R3 19 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite S19; rgw X2).
  assert (c20 : getr R3 20 = Z_to_bv 64 1) by (rewrite S20; rgw X2).
  assert (c21 : getr R3 21 = Z_to_bv 64 (key_addr kn)) by (rewrite S21; rgw X2).
  assert (c22 : getr R3 22 = Z_to_bv 64 384) by (rewrite S22; rgw X2).
  assert (c23 : getr R3 23 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite S23; rgw X2).
  assert (c24 : getr R3 24 = Z_to_bv 64 (re_nheld e1 - Z.of_nat n)) by (rewrite S24; rgw X2).
  assert (c25 : getr R3 25 = Z_to_bv 64 DR_TU) by (rewrite S25; rgw X2).
  assert (c26 : getr R3 26 = Z_to_bv 64 (re_hp e1)) by (rewrite S26; rgw X2).
  assert (c27 : getr R3 27 = Z_to_bv 64 1) by (rewrite S27; rgw X2).
  assert (c10 : getr R3 10 = Z_to_bv 64 (Z.of_nat (length (key_text kn)))) by exact S10r.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, c2, c10. rewrite SEGS.
    eapply dr_hcmp; [exact SPk | clear - KL; lia | exact JJ64]. }
  intros ms2 (can2 & [(NEcmp & ->)|(EQcmp & ->)] & EQ2);
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R4 & -> & X4);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  - assert (Kf : key_eqb (nth n (dlH s P) []) (firstn jj (dline s P Q)) = false).
    { rewrite ENth, <- EB. apply Bool.not_true_is_false. intros Heq. apply key_eqb_spec in Heq.
      apply (f_equal (@length _)) in Heq. unfold bzs in Heq. rewrite !length_map, LB in Heq.
      apply NEcmp. rewrite Heq. reflexivity. }
    eapply SR_mono.
    + eapply (UE_after s P Q n R4 m1 md1 L1 A1 e1 h1 OUT1 junk1 LB1 D k jj bg);
        [ unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X4
        | rgw X4 | rgw X4 | rgw X4 | rgw X4 | rgw X4 | rgw X4 | rgw X4
        | exact SPc | exact SPk | exact BGb | exact BGk | exact GES | exact JJ | exact NLn
        | exact (UE_ix_Sn _ _ _ NLn IXn Kf) | exact LC1 ].
    + intros c' [HSn|HDGA]; [left; exact HSn | right; right; left; exact HDGA].
  - assert (LKjj : length (key_text kn) = jj) by (apply Nat2Z.inj; exact EQcmp).
    assert (jjpos : (0 < jj)%nat) by (clear - JJ; lia).
    destruct (UE_walk_total (key_text kn) buf (jj - 1) ltac:(clear - LKjj jjpos; lia) ltac:(clear - LB jjpos; lia))
      as (v & Hwv).
    destruct (UE_walk_eq (key_text kn) buf (jj - 1) ltac:(clear - LKjj jjpos; lia) ltac:(clear - LB jjpos; lia)
                KZ NZb v Hwv) as (Hiff & Hvb).
    assert (SMv : StrFun.strncmp_model (key_text kn) buf (Z.of_nat jj) = Some v).
    { unfold StrFun.strncmp_model. rewrite (proj2 (Z.eqb_neq _ 0)) by (clear - JJ; lia).
      replace (Z.to_nat (Z.of_nat jj - 1)) with (jj - 1)%nat by (clear - jjpos; lia). exact Hwv. }
    assert (d1 : getr R4 1 = Z_to_bv 64 0x13d00) by rgw X4.
    assert (d10 : getr R4 10 = Z_to_bv 64 (key_addr kn)) by rgw X4.
    assert (d11 : getr R4 11 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X4.
    assert (d12 : getr R4 12 = Z_to_bv 64 (Z.of_nat jj)) by rgw X4.
    apply (UE_strncmp R4 m1 md1 (key_addr kn) (re_buf e1 + Z.of_nat P) (Z.of_nat jj) v (key_text kn) buf);
      [exact Hh | exact Hl | exact RO1 | exact d10 | exact d11 | exact d12 | exact JJ64 | exact KADDR | exact BUFADDR |
       exact KBt | exact BB | exact SMv |].
    intros R5 T1 T2 T3 T4 T8 T9 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T10v.
    rewrite d1, UE_rp_13d00.
    pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(clear - v; lia)) as Vmod.
    assert (EZ : Z_to_bv 64 v = Z_to_bv 64 (v mod 2 ^ 64))
      by (apply bv_eq; rewrite !unsigned_lit_wrap; rewrite Z.mod_mod by (clear - v; lia); reflexivity).
    assert (Vzero : v mod 2 ^ 64 = 0 <-> v = 0)
      by (split; intros HE; [clear - HE Hvb; Z.div_mod_to_equations; nia | subst; reflexivity]).
    assert (e2 : getr R5 2 = Z_to_bv 64 (S0 - 144)) by (rewrite T2; rgw X4).
    assert (e3 : getr R5 3 = getr regs 3) by (rewrite T3; rgw X4).
    assert (e4 : getr R5 4 = getr regs 4) by (rewrite T4; rgw X4).
    assert (e8 : getr R5 8 = Z_to_bv 64 SA) by (rewrite T8; rgw X4).
    assert (e9 : getr R5 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by (rewrite T9; rgw X4).
    assert (e18 : getr R5 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by (rewrite T18; rgw X4).
    assert (e19 : getr R5 19 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite T19; rgw X4).
    assert (e20 : getr R5 20 = Z_to_bv 64 1) by (rewrite T20; rgw X4).
    assert (e22 : getr R5 22 = Z_to_bv 64 384) by (rewrite T22; rgw X4).
    assert (e23 : getr R5 23 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite T23; rgw X4).
    assert (e24 : getr R5 24 = Z_to_bv 64 (re_nheld e1 - Z.of_nat n)) by (rewrite T24; rgw X4).
    assert (e25 : getr R5 25 = Z_to_bv 64 DR_TU) by (rewrite T25; rgw X4).
    assert (e26 : getr R5 26 = Z_to_bv 64 (re_hp e1)) by (rewrite T26; rgw X4).
    assert (e27 : getr R5 27 = Z_to_bv 64 1) by (rewrite T27; rgw X4).
    assert (e10 : getr R5 10 = Z_to_bv 64 (v mod 2 ^ 64)) by (rewrite T10v; exact EZ).
    destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 8) [C8 (Z_to_bv 64 bg)]
                [C8 (Z_to_bv 64 (re_nheld e1)); C8 (Z_to_bv 64 (re_nheld e1 * 8))] SPc
                ltac:(cbn [cells_size csize]; clear - bg; lia)) as [BGcell _].
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, e2, e10, e19, e23, e24, e26. rewrite SEGS.
      eapply dr_hfound;
        [exact BGcell | reflexivity | exact Hslot | exact Vmod | exact BGb | clear - HPb; lia | clear - n; lia |
         clear - CNT; lia]. }
    intros ms3 (can3 & [(VN & ->)|[(V0 & BG0 & ->)|(V0 & BGN & ->)]] & EQ3);
      destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R6 & -> & X6);
      replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    + assert (vne : v <> 0) by (intros ->; apply VN; rewrite Z.mod_0_l by (clear - VN; lia); reflexivity).
      assert (Kf : key_eqb (nth n (dlH s P) []) (firstn jj (dline s P Q)) = false).
      { rewrite ENth, <- EB. apply Bool.not_true_is_false. intros Heq. apply key_eqb_spec in Heq.
        apply bzs_inj in Heq. apply vne. apply (proj2 Hiff). exact Heq. }
      eapply SR_mono.
      * eapply (UE_after s P Q n R6 m1 md1 L1 A1 e1 h1 OUT1 junk1 LB1 D k jj bg);
          [ unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X6
          | rgw X6 | rgw X6 | rgw X6 | rgw X6 | rgw X6 | rgw X6 | rgw X6
          | exact SPc | exact SPk | exact BGb | exact BGk | exact GES | exact JJ | exact NLn
          | exact (UE_ix_Sn _ _ _ NLn IXn Kf) | exact LC1 ].
      * intros c' [HSn|HDGA]; [left; exact HSn | right; right; left; exact HDGA].
    + assert (veq : v = 0) by (apply Vzero; exact V0).
      assert (Hmatch : key_text kn = buf) by (apply (proj1 Hiff); exact veq).
      assert (Ktrue : key_eqb (nth n (dlH s P) []) (firstn jj (dline s P Q)) = true)
        by (rewrite ENth, <- EB; apply key_eqb_spec; rewrite Hmatch; reflexivity).
      assert (IXsome : index_of (firstn jj (dline s P Q)) (dlH s P) = Some n)
        by (apply UE_ix_found; [exact NLn | exact IXn | exact Ktrue]).
      assert (kB : k = GBegin) by (apply BGk; exact BG0).
      rewrite kB in GES.
      assert (STeq : forall jb ha ks, seen_tr (dlH s P) (dlka s P) (dline s P Q) jb ha ks = ([], dlka s P, (ha, ks)))
        by (intros jx hx kx; unfold seen_tr; rewrite GES; cbv beta iota; rewrite IXsome; reflexivity).
      assert (SAeq : seen_arr (dlH s P) (dline s P Q) = dlH s P)
        by (unfold seen_arr; rewrite GES, IXsome; reflexivity).
      assert (f2 : getr R6 2 = Z_to_bv 64 (S0 - 144)) by rgw X6.
      assert (f3 : getr R6 3 = getr regs 3) by rgw X6.
      assert (f4 : getr R6 4 = getr regs 4) by rgw X6.
      assert (f8 : getr R6 8 = Z_to_bv 64 SA) by rgw X6.
      assert (f9 : getr R6 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X6.
      assert (f22 : getr R6 22 = Z_to_bv 64 384) by rgw X6.
      assert (f23 : getr R6 23 = Z_to_bv 64 9) by rgw X6.
      assert (f25 : getr R6 25 = Z_to_bv 64 DR_TU) by rgw X6.
      assert (f26 : getr R6 26 = Z_to_bv 64 4) by rgw X6.
      assert (f27 : getr R6 27 = Z_to_bv 64 (-1)) by rgw X6.
      eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
      { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, f9, f27. rewrite SEGS.
        eapply dr_next; [clear - B0b; lia | clear - BU EUd PQ; lia]. }
      intros ms4 (can4 & -> & EQ4).
      destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R8 & -> & X8).
      replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
      apply SR_ret. right. left.
      apply (dln_of s P Q R8 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D).
      * unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X8.
      * rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X8) by reflexivity; simp_regs. f_equal. clear - Q; lia.
      * apply (dlnb_same s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D LC1 STeq SAeq).
    + assert (veq : v = 0) by (apply Vzero; exact V0).
      assert (Hmatch : key_text kn = buf) by (apply (proj1 Hiff); exact veq).
      assert (Ktrue : key_eqb (nth n (dlH s P) []) (firstn jj (dline s P Q)) = true)
        by (rewrite ENth, <- EB; apply key_eqb_spec; rewrite Hmatch; reflexivity).
      assert (IXsome : index_of (firstn jj (dline s P Q)) (dlH s P) = Some n)
        by (apply UE_ix_found; [exact NLn | exact IXn | exact Ktrue]).
      assert (kE : k = GEnd) by (destruct k; [exfalso; apply BGN; apply BGk; reflexivity | reflexivity]).
      rewrite kE in GES.
      apply SR_ret. right. right. right. unfold DGF.
      exists R6, L1, A1, m1, md1, e1, h1, OUT1, junk1, LB1, D, jj, n.
      split; [reflexivity|].
      split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X6|].
      split; [rgw X6|]. split; [rgw X6|]. split; [rgw X6|].
      split; [rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X6) by reflexivity; simp_regs; rewrite <- Ekn; reflexivity|].
      split; [rgw X6|]. split; [rgw X6|].
      split; [exact NLk|]. split; [exact GES|]. split; [exact JJ|]. split; [exact IXsome|]. exact LC1.
Qed.

Lemma UE_loop : forall fuel s P Q n c, (length (dlH s P) - n <= fuel)%nat -> UE_SCANI s P Q n c ->
  SR segs c (fun c' => DLN s (S Q) c' \/ DGA s P Q c' \/ DGF s P Q c').
Proof using All.
  induction fuel as [|fuel IH]; intros s P Q n c Hj H.
  - exfalso. destruct H as (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & k & jj & bg & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NLn & _). lia.
  - eapply SR_bind; [exact (UE_body s P Q n c H)|]. intros c' [HSn|[HDLN|[HDGA|HDGF]]].
    + apply (IH s P Q (S n) c'); [|exact HSn].
      destruct HSn as (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & k & jj & bg & _ & _ & _ &
        _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NLn & _). lia.
    + apply SR_ret. left. exact HDLN.
    + apply SR_ret. right. left. exact HDGA.
    + apply SR_ret. right. right. exact HDGF.
Qed.

Lemma seen_scan : forall s P Q c, DGS s P Q c ->
  SR segs c (fun c' => DLN s (S Q) c' \/ DGA s P Q c' \/ DGF s P Q c').
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & k & jj & bg & -> & RT1 & G9 & G18 &
    G19 & G20 & BGb & BGk & GES & JJ & LC1).
  pose proof LC1 as [DFs LCc].
  pose proof LCc as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NK1 & RST1 & BK1 & GL1 &
    OU1).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof RT1 as (((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26) & G27).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof EK1 as (K1e & K2e & K3e & K4e & K5e & K6e & K7e & K8e & K9e & K10e & K11e & K12e & K13e & K14e).
  pose proof DFs as (DBd & PQ & HQz & HNZ & HSKp & HLL).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BSb & B0b & BU & BP).
  assert (HLEN : length (dlH s P) = length (re_keys e1))
    by (rewrite <- (L4c : keys_texts (re_keys e1) = dlH s P); unfold keys_texts; apply length_map).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  assert (NHb : 0 <= re_nheld e1 < 2 ^ 31) by (split; [unfold re_nheld; lia | clear - K10e; lia]).
  assert (HHe : 0 < re_nheld e1 -> 0 < re_hp e1 < 2 ^ 64 /\ re_hp e1 mod 8 = 0).
  { intros NP. destruct K11e as [(H0 & KS0)|(HI & _ & _ & HK8 & _)].
    - exfalso. unfold re_nheld in NP. rewrite KS0 in NP. cbn [length Z.of_nat] in NP. lia.
    - pose proof (blk_rng _ _ _ _ _ _ M1 HI) as (BR1 & BR2). pose proof (blk_align _ _ _ _ _ _ M1 HI) as BA.
      split; [clear - BR1 BR2 HK8 ACL; lia|]. clear - BA. Z.div_mod_to_equations. lia. }
  assert (DLLb : re_buf e1 + Z.of_nat P + Z.of_nat jj < 2 ^ 64) by (clear - BU EUd PQ JJ; lia).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3e K4e) as (_ & _ & EC3).
  destruct (dr_cut m1 (SA + 40) (SA + 52) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]
              [CB 4 (re_pad2 e1)] EC3 ltac:(cbn [cells_size csize]; lia)) as [EH40 _].
  assert (EHN : rw_cells rsegs (normalize rsegs m1) (SA + 40)
                  [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1r EH40). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [clear - Hi F5 F6 F7 F8 F4; lia|]. apply g_noimg. clear - Hi. lia. }
  destruct FR1 as (j0 & j1 & j2 & j4 & FR). rewrite SEGS in FR.
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 24) [CB 8 j0; CB 8 j1; CB 8 j2]
              ([C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED) FR ltac:(cbn [cells_size csize]; lia)) as [FRh FRt].
  destruct (dr_cut m1 (S0 - 144 + 24) (S0 - 144 + 32) [C8 (Z_to_bv 64 6001)] ([CB 8 j4] ++ SAVED) FRt
              ltac:(cbn [cells_size csize]; lia)) as [_ FRt2].
  destruct (dr_cut m1 (S0 - 144 + 32) (S0 - 144 + 40) [CB 8 j4] SAVED FRt2
              ltac:(cbn [cells_size csize]; lia)) as [FR4 _].
  assert (FRhN : rw_cells rsegs (normalize rsegs m1) (S0 - 144) [CB 8 j0; CB 8 j1; CB 8 j2]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1r FRh). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [clear - Hi F1 F2 F3; lia|].
    intros Im; pose proof (img_lo _ Im) as IL; clear - IL F1 F3 Hi; lia. }
  assert (FR4N : rw_cells rsegs (normalize rsegs m1) (S0 - 144 + 32) [CB 8 j4]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1r FR4). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [clear - Hi F1 F2 F3; lia|].
    intros Im; pose proof (img_lo _ Im) as IL; clear - IL F1 F3 Hi; lia. }
  destruct FRhN as (_ & (_ & _ & WRh)).
  destruct FR4N as (_ & (_ & _ & WR4)).
  cbn [cells_size csize] in WRh, WR4.
  destruct (UE_c8w (normalize rsegs m1) (S0 - 144)) as (w0 & SPw0);
    [clear - F1 F2 F3; lia | clear - F1 F2 F3; lia | intros i Hi; apply WRh; lia |].
  destruct (UE_c8w (normalize rsegs m1) (S0 - 144 + 8)) as (w1 & SPw1);
    [clear - F1 F2 F3; lia | clear - F1 F2 F3; lia |
     intros i Hi; replace (S0 - 144 + 8 + i) with (S0 - 144 + (8 + i)) by lia; apply WRh; lia |].
  destruct (UE_c8w (normalize rsegs m1) (S0 - 144 + 16)) as (w2 & SPw2);
    [clear - F1 F2 F3; lia | clear - F1 F2 F3; lia |
     intros i Hi; replace (S0 - 144 + 16 + i) with (S0 - 144 + (16 + i)) by lia; apply WRh; lia |].
  destruct (UE_c8w (normalize rsegs m1) (S0 - 144 + 32)) as (w4 & SP4);
    [clear - F1 F2 F3; lia | clear - F1 F2 F3; lia | intros i Hi; apply WR4; lia |].
  pose proof (dr_join (normalize rsegs m1) (S0 - 144) (S0 - 144 + 8) [C8 w0] [C8 w1; C8 w2] SPw0
                (dr_join (normalize rsegs m1) (S0 - 144 + 8) (S0 - 144 + 16) [C8 w1] [C8 w2] SPw1 SPw2
                   ltac:(cbn [cells_size csize]; lia))
                ltac:(cbn [cells_size csize]; lia)) as SPcells.
  cbn [app] in SPcells.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G8, G18, G19, G20. rewrite SEGS.
    eapply (evt_normalize rsegs); [exact dl_wx | exact RO1r |].
    eapply dr_gscan;
      [exact EHN | exact SPcells | exact SP4 | apply mem_inv_normalize | left; clear - F1 F7 F8; lia | exact NHb |
       split; lia | exact DLLb | exact BGb | exact HHe]. }
  intros ms3 (can3 & (s3 & QP & REL3 & ROS3) & EQ3).
  destruct QP as [(NH0 & m3' & -> & MU3' & WM3' & MI3' & SPa3' & SPb3')|
                  (NHpos & m3' & -> & MU3' & WM3' & MI3' & SPa3' & SPb3')];
    destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [CAN3 HR3];
    rewrite CAN3 in EQ3;
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R' & -> & X');
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity);
    set (m3 := ms_mem can3) in *;
    pose proof (sb_back m1 m3' m3 _ RO1r HR3 ROS3 MU3' WM3') as (MU3 & WM3r & RO3r);
    pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 SPa3') as SPa;
    pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 SPb3') as SPb;
    replace (re_buf e1 + Z.of_nat P + Z.of_nat jj - (re_buf e1 + Z.of_nat P)) with (Z.of_nat jj) in SPb by lia;
    assert (DLSB3 : DLSB s P Q L1 A1 m3 md1 e1 h1 OUT1 junk1 LB1 D)
      by (split; [exact DFs | eapply UE_gtr; [exact LCc | exact MU3 | exact WM3r | exact SPa | exact SPb]]).
  - assert (RKe : re_keys e1 = [])
      by (apply length_zero_iff_nil; apply Nat2Z.inj; unfold re_nheld in NH0; rewrite NH0; reflexivity).
    assert (dlHnil : dlH s P = [])
      by (rewrite <- (L4c : keys_texts (re_keys e1) = dlH s P); unfold keys_texts; rewrite RKe; reflexivity).
    destruct (dr_cut m3 (S0 - 144) (S0 - 144 + 16) [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 (re_nheld e1))] [C8 w2] SPa
                ltac:(cbn [cells_size csize]; lia)) as [SPbn _].
    apply SR_ret. right. left. unfold DGA.
    exists R', L1, A1, m3, md1, e1, h1, OUT1, junk1, LB1, D, k, jj, bg.
    split; [reflexivity|].
    split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X'|].
    split; [rgw X'|]. split; [rgw X'|].
    split; [rewrite SEGS; exact SPbn|]. split; [rewrite SEGS; exact SPb|].
    split; [exact BGb|]. split; [exact BGk|]. split; [exact GES|]. split; [exact JJ|].
    split; [rewrite dlHnil; reflexivity|]. exact DLSB3.
  - apply (UE_loop (length (dlH s P)) s P Q 0); [lia|].
    unfold UE_SCANI. exists R', L1, A1, m3, md1, e1, h1, OUT1, junk1, LB1, D, k, jj, bg.
    split; [reflexivity|].
    split; [unfold RT; repeat match goal with |- _ /\ _ => split end; rgw X'|].
    split; [rgw X'|]. split; [rgw X'|].
    split; [replace (8 * Z.of_nat 0) with 0 by lia; rgw X'|].
    split; [rgw X'|].
    split; [replace (re_nheld e1 - Z.of_nat 0) with (re_nheld e1) by lia; rgw X'|].
    split; [rgw X'|]. split; [rgw X'|].
    split; [exact SPa|]. split; [exact SPb|]. split; [exact BGb|]. split; [exact BGk|]. split; [exact GES|].
    split; [exact JJ|].
    split; [rewrite HLEN; unfold re_nheld in NHpos; lia|].
    split; [cbn [firstn index_of]; reflexivity|]. exact DLSB3.
Qed.

Lemma sa_ret_ok : YK0s.ret_ok (Z_to_bv 64 0x13d48).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma sa_nb : forall OUT1 e1 h1 q, NoDup (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) ->
  (q = G \/ q = OUT1 \/ In q (hs_blocks h1) \/ In q (if re_cap e1 =? 0 then [] else [re_buf e1]) \/
   In q (map key_addr (re_keys e1))) ->
  ent_ka e1 = 0 \/ q <> re_hp e1.
Proof using.
  intros OUT1 e1 h1 q ND Hq. unfold ent_ka.
  destruct (Z.eqb_spec (re_hp e1) 0) as [C|C]; [left; reflexivity | right]. intros E.
  unfold entry_blocks in ND. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) C) in ND.
  apply NoDup_ListNoDup in ND.
  assert (ND' : List.NoDup ((G :: OUT1 :: (if re_cap e1 =? 0 then [] else [re_buf e1])) ++
                            re_hp e1 :: (map key_addr (re_keys e1) ++ hs_blocks h1))).
  { rewrite <- !app_assoc in ND. exact ND. }
  apply NoDup_remove_2 in ND'. apply ND'. rewrite <- E.
  destruct Hq as [X|[X|[X|[X|X]]]].
  - left. symmetry. exact X.
  - right. left. symmetry. exact X.
  - right. right. apply in_or_app. right. apply in_or_app. right. exact X.
  - right. right. apply in_or_app. left. exact X.
  - right. right. apply in_or_app. right. apply in_or_app. left. exact X.
Qed.

Lemma sa_okx : forall L1 A1 L2 A2 m1 m2 e1 Pa res,
  msame Pa m1 m2 -> entry_okx L1 A1 m1 e1 ->
  (forall q k, In (q, k) (blocks L1 A1) -> ((re_cap e1 <> 0 /\ q = re_buf e1) \/ In q (map key_addr (re_keys e1))) ->
     In (q, k) (blocks L2 A2)) ->
  (forall q k a, In (q, k) (blocks L1 A1) -> ((re_cap e1 <> 0 /\ q = re_buf e1) \/ In q (map key_addr (re_keys e1))) ->
     q <= a < q + k -> Pa a) ->
  In (res, re_nheld e1 * 8 + 8) (blocks L2 A2) -> fresh_block Bm res (re_nheld e1 * 8 + 8) ->
  bytes_at segs m2 res (key_ptrs (re_keys e1)) ->
  entry_okx L2 A2 m2 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) res
                        (re_nheld e1 * 8 + 8) (re_pad2 e1) (re_keys e1) (re_U e1) (re_junk e1)).
Proof using HG HJ O h junk.
  intros L1 A1 L2 A2 m1 m2 e1 Pa res MS
    (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) SV HP RI RF RB.
  unfold entry_okx, re_nheld.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys].
  unfold re_nheld in E10, E11, RI, RF.
  do 8 (split; [assumption|]).
  split.
  { destruct E9 as [Z0|(C0 & BI & BF & BJ & BC)]; [left; exact Z0 | right].
    assert (IB : (re_cap e1 <> 0 /\ re_buf e1 = re_buf e1) \/ In (re_buf e1) (map key_addr (re_keys e1)))
      by (left; split; [clear - C0; lia | reflexivity]).
    split; [exact C0|]. split; [exact (SV _ _ BI IB)|]. split; [exact BF|]. split; [exact BJ|].
    eapply rw_tr; [exact MS | exact BC |]. intros a Ha. apply (HP _ _ a BI IB).
    cbn [cells_size csize] in Ha. clear - Ha C0. lia. }
  split; [exact E10|].
  split.
  { right. split; [exact RI|]. split; [exact RF|]. split; [lia|]. split; [lia|]. exact RB. }
  split; [exact E12|]. split; [exact E13|].
  apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) E14 k Hk) as (K1 & K2 & K3 & K4 & K5).
  assert (IK : (re_cap e1 <> 0 /\ key_addr k = re_buf e1) \/ In (key_addr k) (map key_addr (re_keys e1)))
    by (right; apply in_map; exact Hk).
  split; [exact (SV _ _ K1 IK)|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  eapply by_tr; [exact MS | exact K3 |]. intros a Ha. apply (HP _ _ a K1 IK).
  rewrite length_app in Ha. cbn [length] in Ha. clear - Ha. lia.
Qed.

Lemma sa_hist : forall sent kl Dh s sk H ka ka' no oc h1 LB1,
  DHISTg sent kl Dh (dvirt s sk H ka no oc) h1 LB1 -> DHISTg sent kl Dh (dvirt s sk H ka' no oc) h1 LB1.
Proof using. intros sent kl Dh s sk H ka ka' no oc h1 LB1 X. exact X. Qed.

Lemma sa_pst : forall s sk H ka ka' no oc, pstream (dvirt s sk H ka' no oc) = pstream (dvirt s sk H ka no oc).
Proof using. reflexivity. Qed.

Lemma sa_out : forall s sk H ka ka' no oc L1 A1 m1 OUT1 junk1 LB1,
  DOUT (dvirt s sk H ka no oc) L1 A1 m1 OUT1 junk1 LB1 -> DOUT (dvirt s sk H ka' no oc) L1 A1 m1 OUT1 junk1 LB1.
Proof using. intros s sk H ka ka' no oc L1 A1 m1 OUT1 junk1 LB1 X. exact X. Qed.

Lemma sa_link : forall s sk H ka ka' no oc e1 e2 h1,
  DLINK (dvirt s sk H ka no oc) e1 h1 -> re_cap e2 = re_cap e1 -> re_U e2 = re_U e1 -> re_skip e2 = re_skip e1 ->
  re_keys e2 = re_keys e1 -> ent_ka e2 = ka' -> DLINK (dvirt s sk H ka' no oc) e2 h1.
Proof using.
  intros s sk H ka ka' no oc e1 e2 h1 (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1)
    E1 E2 E3 E4 E5.
  split; [rewrite E1; exact L1c|]. split; [rewrite E2; exact L2c|]. split; [rewrite E3; exact L3c|].
  split; [rewrite E4; exact L4c|]. split; [exact E5|].
  split; [exact L6c|]. split; [exact L7c|]. split; [exact L8c|]. split; [exact L9c|]. split; [exact L10c|].
  split; [exact L11c | exact WF1].
Qed.

Lemma H2_saa_ra : forall L1 A1 R1 m1 md1 b cap0 buf0 n pre rest p0,
  call_pre_k Bm MR REALLOC_STACK L1 A1 R1 m1 md1 -> ro_agree segs m1 ->
  0 < cap0 -> live_at L1 A1 p0 buf0 cap0 ->
  getr R1 10 = Z_to_bv 64 buf0 -> getr R1 11 = Z_to_bv 64 n -> Z.of_nat (length pre) <= n ->
  bytes_at segs m1 buf0 (pre ++ rest) -> Z.of_nat (length (pre ++ rest)) = cap0 ->
  rt_ok F A1 b -> rt_room F b n ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x178f8) m1 (seg_rom segs)) md1)
    (RLT b cap0 buf0 n p0 pre L1 A1 R1 m1 md1).
Proof using All.
  intros L1 A1 R1 m1 md1 b cap0 buf0 n pre rest p0 PRE1 RO1 Cp [Hp Ep] E10 E11 LE OB LOLD RES ROOMn.
  pose proof PRE1 as (HM1 & HW1 & _).
  assert (A10 : getr R1 10 = Z_to_bv 64 (ptr_addr L1 p0)) by (rewrite Ep; exact E10).
  assert (AOLD : forall i, 0 <= i < cap0 ->
            mbyte segs m1 (ptr_addr L1 p0 + i) = nth_error (pre ++ rest) (Z.to_nat i)).
  { intros i Hi. rewrite Ep. pose proof (mbyte_of_bytes_at segs m1 _ _ (Z.to_nat i) OB ltac:(lia)) as X.
    rewrite Z2Nat.id in X by lia. exact X. }
  eapply SR_mono; [exact (RAC L1 A1 R1 m1 md1 p0 cap0 n (pre ++ rest) b PRE1 RO1 Hp A10 E11 AOLD LOLD RES ROOMn)|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & A0 & NZ & AL & FR & BLK & KEPT & RO2 & GK & SURV & CPY
             & INI2 & LN & q & Hq & Eq & RES2).
  exists L2, A2, regs2, mem2, md2, res, q. split; [reflexivity|].
  split.
  { pose proof (sb_realloc_rp Bm API AX CTX L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 p0 cap0 HW1 Hp Cp HM1 CP SURV LN)
      as RP. rewrite Ep in RP. exact RP. }
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split.
  { destruct BLK as (b1 & b2 & c1 & c2 & E1 & E2 & E3). rewrite Ep in E1.
    exists b1, b2, c1, c2. split; [exact E2|]. split; [exact E3|]. right. split; [exact Cp | exact E1]. }
  split; [exact RO2|].
  split.
  { pose proof FR as (FR1 & FR2 & _). pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    rewrite length_app in LOLD.
    apply bytes_at_of_mbyte; [clear - FR1; lia | clear - FR1 FR2 ACL LE; lia |].
    intros i Hi. rewrite (CPY (Z.of_nat i) ltac:(clear - Hi LOLD LE; lia)). rewrite Nat2Z.id.
    apply nth_error_app1. exact Hi. }
  split; [exact INI2|].
  split; [split; [exact Hq | exact Eq]|].
  split.
  { intros p x k [Hpk Epx] Hx.
    assert (NP : p <> p0).
    { intros E. subst p. destruct Hx as [Hx|Hx]; [clear - Hx Cp; lia|]. apply Hx. rewrite <- Epx. exact Ep. }
    pose proof (SURV p k Hpk NP) as Hpk2. split; [exact Hpk2|].
    pose proof CP as (_ & _ & _ & _ & AD & _). rewrite (AD p k Hpk Hpk2). exact Epx. }
  rewrite (proj2 (Z.eqb_neq cap0 0)) by lia. exact RES2.
Qed.

Lemma seen_add_a : forall s P Q c, DGA s P Q c -> SR segs c (fun c' => DLN s (S Q) c' \/ DGK s P Q c').
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & k & jj & bg & -> & RT1 & G9 & G18 &
    SK1 & SK2 & BGr & BGk & GS & JJ & IX & DFs & LC1).
  pose proof LC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NK1 & RST1 & BK1 & GL1
    & OU1).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & W1 & B1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
  destruct (dr_cut m1 (SA + 40) (SA + 48) [C8 (Z_to_bv 64 (re_hp e1))]
              [C4 (Z_to_bv 64 (re_nheld e1)); CB 4 (re_pad2 e1)] EC3 ltac:(cbn [cells_size csize]; lia)) as [EH1 EH2].
  assert (NHD : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
  assert (NH : 0 <= re_nheld e1 < 2 ^ 26) by (split; [rewrite NHD; lia | exact K10]).
  assert (SK1r : rw_cells rsegs m1 (S0 - 144) [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 (re_nheld e1))])
    by (rewrite <- SEGS; exact SK1).
  pose proof DFs as (DBd & PQ & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BSb & B0b & BU & BP).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G2, G8. rewrite SEGS.
    eapply dr_gadd; [exact SK1r | exact EH1 | exact BGr | clear - NH; lia]. }
  intros ms (can & [(NB & ->)|(B0 & ->)] & EQ);
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  - assert (KE : k = GEnd).
    { destruct k; [exfalso; exact (NB (proj2 BGk eq_refl)) | reflexivity]. }
    subst k.
    assert (ST : forall jb ha ks, seen_tr (dlH s P) (dlka s P) (dline s P Q) jb ha ks = ([], dlka s P, (ha, ks))).
    { intros jb ha ks. unfold seen_tr. rewrite GS. cbv beta iota. rewrite IX. reflexivity. }
    assert (SAR : seen_arr (dlH s P) (dline s P Q) = dlH s P).
    { unfold seen_arr. rewrite GS. cbv beta iota. rewrite IX. reflexivity. }
    assert (RTL2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
    pose proof RTL2 as (((P2 & P3 & P4 & P8 & P22 & P25) & P23 & P26) & P27).
    assert (Y9 : getr R2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X2.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y9, P27. rewrite SEGS.
      eapply dr_next; clear - B0b BU EUd PQ; lia. }
    intros ms (can4 & -> & EQ4).
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply SR_ret. left.
    apply (dln_of s P Q R4 L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D).
    + unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X4.
    + rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity. simp_regs. f_equal. clear; lia.
    + exact (dlnb_same s P Q L1 A1 m1 md1 e1 h1 OUT1 junk1 LB1 D (conj DFs LC1) ST SAR).
  - assert (KB : k = GBegin) by (apply BGk; exact B0). subst k.
    pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & _).
    assert (L4' : keys_texts (re_keys e1) = dlH s P) by exact L4c.
    assert (L5' : ent_ka e1 = dlka s P) by exact L5c.
    assert (HLEN : length (dlH s P) = length (re_keys e1)) by (rewrite <- L4'; unfold keys_texts; apply length_map).
    assert (LX : length (firstn jj (dline s P Q)) = jj).
    { rewrite firstn_length_le; [reflexivity|]. rewrite (dline_len s P Q PQ). glia. }
    assert (ST : forall j0 ha ks, seen_tr (dlH s P) (dlka s P) (dline s P Q) j0 ha ks =
                 ([if ent_ka e1 =? 0 then RMalloc (re_nheld e1 * 8 + 8)
                   else RRealloc (ent_ka e1) (re_nheld e1 * 8 + 8) ha; RMalloc (Z.of_nat jj + 1)],
                  re_nheld e1 * 8 + 8, (Ret j0, ks ++ [Ret (S j0)]))).
    { intros j0 ha ks. unfold seen_tr. rewrite GS. cbv beta iota. rewrite IX. cbv beta iota zeta.
      rewrite <- L5', LX.
      replace ((Z.of_nat (length (dlH s P)) + 1) * 8) with (re_nheld e1 * 8 + 8)
        by (rewrite HLEN; clear - NHD; lia).
      reflexivity. }
    assert (EKa : seen_ka (dlH s P) (dlka s P) (dline s P Q) = re_nheld e1 * 8 + 8)
      by (unfold seen_ka; rewrite ST; reflexivity).
    destruct TR1 as (tp & qd & ad & (RQ & WF0 & DOK & RS1 & (LKo & (LKb & LKh & LKk) & LKs) & KH) & TE1 & TF1 & TA1).
    destruct DOK as (Dout & Dbuf & Dhp & Dkeys & Dpend & Dev & Derecs).
    rewrite <- RQ in Dout, Dbuf, Dhp, Dkeys, Dpend, Dev, Derecs.
    remember (if ent_ka e1 =? 0 then RMalloc (re_nheld e1 * 8 + 8)
              else RRealloc (ent_ka e1) (re_nheld e1 * 8 + 8) (da_hp ad)) as ev eqn:Hev.
    assert (NE1 : nretF [ev] = 1%nat) by (rewrite Hev; destruct (ent_ka e1 =? 0); reflexivity).
    assert (N2 : forall x, nretF [ev; RMalloc x] = 2%nat)
      by (intros x; rewrite Hev; destruct (ent_ka e1 =? 0); reflexivity).
    assert (NT : nretF (tp ++ [ev]) = (nretF tp + 1)%nat) by (rewrite nret_app, NE1; reflexivity).
    assert (ER : srest (dlH s P) (dlka s P) (dline s P Q) (sv_no s P Q) (sv_oc s P Q) (drlq s (S Q)) (nretF tp)
                   (da_out ad) (da_hp ad) (da_keys ad) =
                 (ev :: RMalloc (Z.of_nat jj + 1) ::
                    fst (sv_rest s P Q (S (nretF tp + 1)) (da_out ad) (Ret (nretF tp))
                           (da_keys ad ++ [Ret (nretF tp + 1)])),
                  snd (sv_rest s P Q (S (nretF tp + 1)) (da_out ad) (Ret (nretF tp))
                         (da_keys ad ++ [Ret (nretF tp + 1)])))).
    { unfold srest, sv_rest. cbv beta. rewrite ST, <- Hev. cbn [fst snd app]. rewrite N2.
      replace (nretF tp + 2)%nat with (S (nretF tp + 1)) by lia.
      replace (S (nretF tp)) with (nretF tp + 1)%nat by lia. reflexivity. }
    rewrite ER in TE1, TF1, TA1. cbn [fst snd] in TE1, TF1, TA1.
    assert (NN : forall t, (nretF tp + nretF (ev :: t) = nretF tp + 1 + nretF t)%nat).
    { intros t. change (ev :: t) with ([ev] ++ t). rewrite nret_app, NE1. lia. }
    rewrite NN in TE1, TF1, TA1.
    assert (RMn : rt_room F (runF F qd bnd tp) (re_nheld e1 * 8 + 8)).
    { pose proof ROOM as RM. rewrite <- TE1, <- app_assoc in RM.
      apply (p3a_room_next F qd bnd tp ev _ _ WF0 (eq_sym RQ) RM).
      rewrite Hev. destruct (ent_ka e1 =? 0); [left; reflexivity | right; exists (ent_ka e1), (da_hp ad); reflexivity]. }
    assert (PRE2 : call_pre_k Bm MR REALLOC_STACK L1 A1 R2 m1 md1).
    { apply (pre_realloc L1 A1 m1 md1 R2 RP1 IN1); [rgw X2 | rgw X2 |].
      rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. exact sa_ret_ok. }
    assert (KHC : (re_hp e1 = 0 /\ ent_ka e1 = 0 /\ re_keys e1 = []) \/
                  (re_hp e1 <> 0 /\ ent_ka e1 = re_kh e1 /\ In (re_hp e1, re_kh e1) (blocks L1 A1) /\
                   fresh_block Bm (re_hp e1) (re_kh e1) /\ 8 * re_nheld e1 <= re_kh e1 /\ 8 <= re_kh e1 /\
                   bytes_at segs m1 (re_hp e1) (key_ptrs (re_keys e1)))).
    { destruct K11 as [(H0 & KS0)|(HI & HF & H8 & H8' & HB)].
      - left. split; [exact H0|]. split; [unfold ent_ka; rewrite H0; reflexivity | exact KS0].
      - right. assert (HN : re_hp e1 <> 0) by (destruct HF as (HF1 & _); lia).
        split; [exact HN|]. split; [unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ 0) HN); reflexivity|].
        repeat (split; [assumption|]); assumption. }
    assert (RLc : SR segs (mkCfg (YK11.mkst R2 (Z_to_bv 64 0x178f8) m1 (seg_rom segs)) md1)
              (RLT (runF F qd bnd tp) (ent_ka e1) (re_hp e1) (re_nheld e1 * 8 + 8) (resolveF qd (da_hp ad))
                  (key_ptrs (re_keys e1)) L1 A1 R2 m1 md1)).
    { destruct KHC as [(H0 & KA0 & KS0)|(HN & KA & HI & HF & H8 & H8' & HB)].
      - rewrite KA0, H0, KS0.
        apply UG_rlt_rn; [exact PRE2 | exact RO1 | | rgw X2 | clear - NH; lia | | exact RS1 | exact RMn].
        rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. rewrite H0. reflexivity.
        rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity. simp_regs. rewrite MALPC.
        intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate.
      - rewrite KA.
        pose proof (blk_rng _ _ _ _ _ _ M1 HI) as BRh.
        pose proof HF as (HF1 & HF2 & HF3).
        pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
        assert (WRH : forall i, 0 <= i < re_kh e1 -> writable_at rsegs m1 (re_hp e1 + i)).
        { intros i Hi. rewrite <- SEGS. exact (BW _ _ _ _ (re_hp e1) _ i M1 HI Hi). }
        destruct (CF.gestures_end_b.bytes_of_mbytes rsegs m1 (re_hp e1 + 8 * re_nheld e1)
                    (Z.to_nat (re_kh e1 - 8 * re_nheld e1))) as (rest & LR & BR).
        { glia. }
        { glia. }
        { intros i Hi. apply CF.gestures_end_b.writable_mbyte.
          replace (re_hp e1 + 8 * re_nheld e1 + i) with (re_hp e1 + (8 * re_nheld e1 + i)) by ring.
          apply WRH. glia. }
        apply (H2_saa_ra L1 A1 R2 m1 md1 (runF F qd bnd tp) (re_kh e1) (re_hp e1) (re_nheld e1 * 8 + 8)
                 (key_ptrs (re_keys e1)) rest (resolveF qd (da_hp ad)));
          [exact PRE2 | exact RO1 | glia | exact (LKh HN) | rgw X2 | rgw X2 | | | | exact RS1 | exact RMn].
        + rewrite CF.gestures_end_b.key_ptrs_length. glia.
        + apply bytes_at_app. split; [exact HB|]. rewrite CF.gestures_end_b.key_ptrs_length.
          replace (re_hp e1 + Z.of_nat (8 * length (re_keys e1))) with (re_hp e1 + 8 * re_nheld e1) by glia.
          rewrite SEGS. exact BR.
        + rewrite length_app, CF.gestures_end_b.key_ptrs_length, LR. glia. }
    eapply SR_bind; [exact RLc|].
    intros c' (L2 & A2 & regs2 & mem2 & md2 & res & qn & -> & RP2 & G10' & NZ & FRES & BLK & RO2 & OB2 & IN2 & LQn
               & KEEP & RS2).
    pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & PR2 & _ & _ & _ & SC2).
    destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
    destruct BLK as (b1 & b2 & c1 & c2 & EB2 & EC12 & EB1).
    pose proof BK1 as (ND1 & GI1 & SV1 & CL1 & FB1).
    pose proof HI1 as (_ & _ & _ & _ & _ & H6h & H7h & _).
    pose proof pre_facts as (HM0 & _ & _ & _ & _ & HCEIL & H63 & _ & _ & _).
    pose proof err_hi as EH. unfold G_LOCK_HI in F9.
    pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    pose proof FRES as (FR1r & FR2r & FR3r).
    assert (SPR2 : spZ R2 = S0 - 144).
    { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X2) by reflexivity.
      simp_regs. apply unsigned_lit. glia. }
    assert (NDB1 : List.NoDup (map fst (blocks L1 A1))) by (apply NoDup_ListNoDup; exact (NODUP _ _ _ _ M1)).
    assert (NDB2 : List.NoDup (map fst (blocks L2 A2))) by (apply NoDup_ListNoDup; exact (NODUP _ _ _ _ M2)).
    assert (ENI : forall a, re_hp e1 <= a < re_hp e1 + ent_ka e1 ->
              a < YM05.alloc_ceiling /\ ~ in_img Bm a /\ re_hp e1 <> 0).
    { intros a Ha. destruct KHC as [(H0 & KA0 & _)|(HN & KA & HI & (HF1 & HF2 & HF3) & _)]; [exfalso; glia|].
      split; [glia|]. split; [|exact HN]. replace a with (re_hp e1 + (a - re_hp e1)) by ring. apply HF3. glia. }
    assert (EDJ : forall q k a, In (q, k) (blocks L1 A1) -> (ent_ka e1 = 0 \/ q <> re_hp e1) -> q <= a < q + k ->
              ~ (re_hp e1 <= a < re_hp e1 + ent_ka e1)).
    { intros q k0 a Hq Hn Ha. destruct Hn as [C|C]; [glia|].
      destruct KHC as [(_ & KA0 & _)|(_ & KA & HI & _)]; [glia|].
      pose proof (blocks_disjoint Bm API _ _ _ _ q k0 (re_hp e1) (re_kh e1) M1 Hq HI C) as DJ.
      clear - DJ Ha KA. lia. }
    assert (NBNE : forall q k, In (q, k) (blocks L1 A1) -> (ent_ka e1 = 0 \/ q <> re_hp e1) -> q <> re_hp e1).
    { intros q k0 Hq Hn E. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR. destruct Hn as [Hn|Hn]; [|exact (Hn E)].
      destruct KHC as [(H0 & _)|(HN & KA & _ & _ & _ & H8' & _)]; glia. }
    assert (NBG : ent_ka e1 = 0 \/ G <> re_hp e1) by (apply (sa_nb OUT1 e1 h1 G ND1); left; reflexivity).
    assert (SURV : forall q k, In (q, k) (blocks L1 A1) -> (ent_ka e1 = 0 \/ q <> re_hp e1) ->
              In (q, k) (blocks L2 A2) /\ q <> res).
    { intros q k0 Hq Hn. assert (Hc : In (q, k0) (c1 ++ c2)).
      { rewrite EC12. destruct EB1 as [(_ & E)|(Cp0 & E)]; rewrite E in Hq; [exact Hq|].
        apply in_app_or in Hq as [Hq|[Hq|Hq]]; [apply in_or_app; left; exact Hq | | apply in_or_app; right; exact Hq].
        injection Hq as <- <-. destruct Hn as [Hn|Hn]; [exfalso; glia | congruence]. }
      split; [rewrite EB2; apply in_app_or in Hc as [Hc|Hc]; apply in_or_app; [left; exact Hc | right; right; exact Hc]|].
      intros ->. rewrite EB2, map_app in NDB2. cbn [map fst] in NDB2. apply NoDup_remove_2 in NDB2. apply NDB2.
      rewrite <- map_app. change res with (fst (res, k0)). apply in_map. exact Hc. }
    assert (BACK : forall q k, In (q, k) (blocks L2 A2) -> (q = res /\ k = re_nheld e1 * 8 + 8) \/
              (In (q, k) (blocks L1 A1) /\ (ent_ka e1 = 0 \/ q <> re_hp e1))).
    { intros q k0 Hq. rewrite EB2 in Hq. apply in_app_or in Hq as [Hq|[Hq|Hq]].
      2: { left. injection Hq as <- <-. split; reflexivity. }
      all: assert (Hb : In (q, k0) (b1 ++ b2))
             by (rewrite <- EC12; apply in_or_app; first [left; exact Hq | right; exact Hq]).
      all: right; destruct EB1 as [(C0 & E)|(Cp0 & E)]; [rewrite E; split; [exact Hb | left; exact C0]|].
      all: rewrite E in NDB1 |- *; split;
             [apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb]|].
      all: right; intros ->; rewrite map_app in NDB1; cbn [map fst] in NDB1; apply NoDup_remove_2 in NDB1;
             apply NDB1; rewrite <- map_app; change (re_hp e1) with (fst (re_hp e1, k0)); apply in_map; exact Hb. }
    assert (GI2 : In (G, SRC_TABLE) (blocks L2 A2)) by exact (proj1 (SURV G SRC_TABLE GI1 NBG)).
    assert (INres : In (res, re_nheld e1 * 8 + 8) (blocks L2 A2))
      by (rewrite EB2; apply in_or_app; right; left; reflexivity).
    assert (DJres : res + (re_nheld e1 * 8 + 8) <= G \/ G + SRC_TABLE <= res).
    { apply (blocks_disjoint Bm API _ _ _ _ res _ G SRC_TABLE M2 INres GI2).
      intros E. exact (proj2 (SURV G SRC_TABLE GI1 NBG) (eq_sym E)). }
    pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as MS2.
    match type of MS2 with msame ?PP _ _ => set (P2 := PP) in MS2 end.
    assert (P2S : forall a, S0 - 144 <= a < S0 -> P2 a).
    { intros a Ha. unfold P2. cbv beta. left.
      split; [left; glia|]. split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M1 Ho); glia|].
      split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M2 Ho); glia|].
      split; [unfold scratch_k; rewrite SPR2; unfold REALLOC_STACK, ALLOC_STACK; glia|].
      intros Ea. pose proof (ENI a Ea) as (EA & _). glia. }
    assert (P2I : forall a, img_plain Bm a -> P2 a).
    { intros a Hp. pose proof Hp as (Im & _ & _ & NE). pose proof (img_lo a Im) as IL. unfold P2. cbv beta. left.
      split; [right; exact Im|]. split; [exact (img_unowned _ _ _ _ a M1 Hp)|].
      split; [exact (img_unowned _ _ _ _ a M2 Hp)|].
      split; [unfold scratch_k; rewrite SPR2; unfold REALLOC_STACK, ALLOC_STACK; glia|].
      intros Ea. exact (proj1 (proj2 (ENI a Ea)) Im). }
    assert (P2B : forall q k a, In (q, k) (blocks L1 A1) -> (ent_ka e1 = 0 \/ q <> re_hp e1) -> q <= a < q + k ->
              P2 a).
    { intros q k0 a Hq Hn Ha. unfold P2. cbv beta. right. exists q, k0.
      split; [exact Hq|]. split; [glia|]. split; [exact (NBNE q k0 Hq Hn)|]. split; [glia|].
      exact (EDJ q k0 a Hq Hn Ha). }
    assert (EH1' : rw_cells rsegs mem2 (SA + 40) [C8 (Z_to_bv 64 (re_hp e1))]).
    { rewrite <- SEGS in EH1 |- *. apply (rw_tr _ _ _ _ _ MS2 EH1). intros a Ha. cbn [cells_size csize] in Ha.
      apply (P2B G SRC_TABLE a GI1 NBG). unfold SRC_TABLE, SRC_ENTRY in *. glia. }
    assert (RO2r : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RO2).
    assert (EHN : rw_cells rsegs (normalize rsegs mem2) (SA + 40) [C8 (Z_to_bv 64 (re_hp e1))]).
    { apply (rw_cells_normalize rsegs mem2 _ _ RO2r EH1'). intros i Hi. cbn [cells_size csize] in Hi.
      apply (ro_addr_out Bm SEGS); [glia|]. apply g_noimg. glia. }
    assert (SK2m : rw_cells rsegs mem2 (S0 - 144 + 32) [C8 (Z_to_bv 64 (Z.of_nat jj))]).
    { rewrite <- SEGS. apply (rw_tr _ _ _ _ _ MS2 SK2). intros a Ha. cbn [cells_size csize] in Ha.
      apply P2S. clear - Ha. lia. }
    assert (SKN : rw_cells rsegs (normalize rsegs mem2) (S0 - 144 + 32) [C8 (Z_to_bv 64 (Z.of_nat jj))]).
    { apply (rw_cells_normalize rsegs mem2 _ _ RO2r SK2m). intros i Hi. cbn [cells_size csize] in Hi.
      apply (ro_addr_out Bm SEGS); [clear - Hi F1 F2 F3; lia|].
      intros Im; pose proof (img_lo _ Im) as IL; clear - IL F1 F3 Hi; lia. }
    assert (G1' : getr R2 1 = Z_to_bv 64 0x13d48) by rgw X2.
    assert (V2 : getr regs2 2 = Z_to_bv 64 (S0 - 144))
      by (transitivity (getr R2 2); [exact (PR2 2 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V3 : getr regs2 3 = getr regs 3)
      by (transitivity (getr R2 3); [exact (PR2 3 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V4 : getr regs2 4 = getr regs 4)
      by (transitivity (getr R2 4); [exact (PR2 4 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V8 : getr regs2 8 = Z_to_bv 64 SA)
      by (transitivity (getr R2 8); [exact (PR2 8 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V9 : getr regs2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q))
      by (transitivity (getr R2 9); [exact (PR2 9 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V18 : getr regs2 18 = Z_to_bv 64 (re_buf e1 + Z.of_nat P))
      by (transitivity (getr R2 18); [exact (PR2 18 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V22 : getr regs2 22 = Z_to_bv 64 384)
      by (transitivity (getr R2 22); [exact (PR2 22 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V23 : getr regs2 23 = Z_to_bv 64 9)
      by (transitivity (getr R2 23); [exact (PR2 23 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V25 : getr regs2 25 = Z_to_bv 64 DR_TU)
      by (transitivity (getr R2 25); [exact (PR2 25 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V26 : getr regs2 26 = Z_to_bv 64 4)
      by (transitivity (getr R2 26); [exact (PR2 26 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    assert (V27 : getr regs2 27 = Z_to_bv 64 (-1))
      by (transitivity (getr R2 27); [exact (PR2 27 ltac:(unfold callee_saved; clear - PR2; lia)) | rgw X2]).
    rewrite G1'.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, V2, V8, G10', V18. rewrite SEGS.
      eapply (evt_normalize rsegs); [exact dl_wx | exact RO2r |].
      eapply dr_gnew; [exact EHN | exact SKN | apply mem_inv_normalize | left; clear - F1 F7 F8; lia | glia]. }
    intros ms3 (can3 & (s3 & QP & REL3 & ROS3) & EQ3).
    destruct QP as [(R0 & _)|(_ & m3' & -> & MU3' & WM3' & _ & HC3' & _)]; [exfalso; exact (NZ R0)|].
    destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [ECAN3 HR3].
    rewrite ECAN3 in EQ3.
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    set (m3 := ms_mem can3) in *.
    pose proof (sb_back mem2 m3' m3 _ RO2r HR3 ROS3 MU3' WM3') as (MU3 & WM3r & RO3r).
    pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 HC3') as HC3.
    assert (WM3 : wmono segs mem2 m3) by (rewrite SEGS; exact WM3r).
    pose proof (msame_trans _ _ _ _ _ MS2 (msame_munch _ _ _ MU3 WM3)) as MS.
    match type of MS with msame ?PP _ _ => set (Pa := PP) in MS end.
    assert (PS : forall a, S0 - 144 <= a < S0 -> Pa a).
    { intros a Ha. unfold Pa. cbv beta. split; [exact (P2S a Ha)|]. split; [glia|]. cbn [outside].
      split; [glia | exact I]. }
    assert (PI : forall a, img_plain Bm a -> Pa a).
    { intros a Hp. unfold Pa. cbv beta. pose proof Hp as (Im & _). pose proof (img_lo a Im) as IL.
      split; [exact (P2I a Hp)|]. split; [glia|]. cbn [outside].
      split; [intros Rw; exact (g_noimg a ltac:(glia) Im) | exact I]. }
    assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> (ent_ka e1 = 0 \/ q <> re_hp e1) -> q <> G ->
              q <= a < q + k -> Pa a).
    { intros q k0 a Hq Hn NG Ha. unfold Pa. cbv beta. split; [exact (P2B q k0 a Hq Hn Ha)|].
      pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
      pose proof (blocks_disjoint Bm API _ _ _ _ q k0 G SRC_TABLE M1 Hq GI1 NG) as DJ.
      split; [glia|]. cbn [outside].
      split; [destruct DJ as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia | exact I]. }
    assert (PG : forall a, SA <= a < SA + 56 -> ~ (SA + 40 <= a < SA + 48) -> Pa a).
    { intros a Ha Hn. unfold Pa. cbv beta.
      split; [apply (P2B G SRC_TABLE a GI1 NBG); unfold SRC_TABLE, SRC_ENTRY in *; glia|].
      split; [glia|]. cbn [outside]. split; [glia | exact I]. }
    assert (TPr : forall c cs, rw_cells rsegs m1 c cs -> (forall a, c <= a < c + Z.of_nat (cells_size cs) -> Pa a) ->
              rw_cells rsegs m3 c cs).
    { intros c0 cs HX HP. rewrite <- SEGS in HX |- *. exact (rw_tr _ _ _ c0 cs MS HX HP). }
    assert (OBK3 : bytes_at segs m3 res (key_ptrs (re_keys e1))).
    { eapply by_tr; [exact (msame_munch _ _ _ MU3 WM3) | exact OB2 |]. intros a Ha. cbv beta.
      rewrite CF.gestures_end_b.key_ptrs_length in Ha. split; [glia|]. cbn [outside].
      split; [destruct DJres as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia | exact I]. }
    assert (NBK : forall q, ((re_cap e1 <> 0 /\ q = re_buf e1) \/ In q (map key_addr (re_keys e1))) ->
              (ent_ka e1 = 0 \/ q <> re_hp e1) /\ q <> G).
    { intros q Hq.
      assert (Hq' : In q (if re_cap e1 =? 0 then [] else [re_buf e1]) \/ In q (map key_addr (re_keys e1))).
      { destruct Hq as [(C & ->)|Hq]; [left; rewrite (proj2 (Z.eqb_neq _ 0) C); left; reflexivity | right; exact Hq]. }
      split; [apply (sa_nb OUT1 e1 h1 q ND1); right; right; right; exact Hq'|].
      apply (dx_ng OUT1 (entry_blocks e1 ++ hs_blocks h1) q ND1). right. apply in_or_app. left.
      unfold entry_blocks. destruct Hq' as [X|X]; apply in_or_app; [left; exact X | right; apply in_or_app; right; exact X]. }
    assert (NBH : forall q, In q (hs_blocks h1) -> ent_ka e1 = 0 \/ q <> re_hp e1)
      by (intros q Hb; apply (sa_nb OUT1 e1 h1 q ND1); right; right; left; exact Hb).
    assert (NGH : forall q, In q (hs_blocks h1) -> q <> G)
      by (intros q Hb; apply (dx_ng OUT1 _ q ND1); right; apply in_or_app; right; exact Hb).
    assert (LIVEQ : forall q, (q = G \/ q = OUT1 \/ In q (hs_blocks h1) \/
                               In q (if re_cap e1 =? 0 then [] else [re_buf e1]) \/ In q (map key_addr (re_keys e1))) ->
              q = 0 \/ exists k, In (q, k) (blocks L1 A1) /\ (ent_ka e1 = 0 \/ q <> re_hp e1)).
    { intros q Hq.
      assert (LQ : q = 0 \/ exists k, In (q, k) (blocks L1 A1)).
      { destruct Hq as [->|[->|[Hq|[Hq|Hq]]]].
        - right. exists SRC_TABLE. exact GI1.
        - destruct OU1 as (OF & OT). destruct (Bool.bool_dec LIVE true) as [LV|LV].
          + destruct (OT LV) as (_ & [(_ & O0 & _)|(_ & _ & OI & _)]); [left; exact O0 | right; eexists; exact OI].
          + apply Bool.not_true_is_false in LV. destruct (OF LV) as (_ & EO & _ & OB).
            destruct OUTD as [(C0 & O0 & _)|(Cp & _)]; [left; rewrite EO; exact O0|].
            right. exists CAP. rewrite EO. exact (proj1 (OB Cp)).
        - right. exact (hb_live L1 A1 m1 HA h1 q SR1 Hq).
        - right. revert Hq. destruct (Z.eqb_spec (re_cap e1) 0) as [C|C]; intros Hq; [destruct Hq|].
          destruct Hq as [<-|[]]. destruct K9 as [(C0 & _)|(_ & BI & _)]; [lia | exists (re_cap e1); exact BI].
        - right. apply in_map_iff in Hq as (kk & <- & Hk).
          destruct (proj1 (Forall_forall _ _) K14 kk Hk) as (KK1 & _). eexists; exact KK1. }
      destruct LQ as [Q0|(k0 & Hk)]; [left; exact Q0 | right; exists k0; split; [exact Hk|]].
      exact (sa_nb OUT1 e1 h1 q ND1 Hq). }
    assert (LO : Z.of_nat (length O) = NO)
      by (destruct OUTD as [(_ & _ & N0 & EO)|(_ & _ & _ & _ & _ & LO & _)]; [rewrite EO; cbn; clear - N0; lia | exact LO]).
    assert (EB' : entry_blocks (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1)
                    (re_cap e1) res (re_nheld e1 * 8 + 8) (re_pad2 e1) (re_keys e1) (re_U e1) (re_junk e1)) =
                  (if re_cap e1 =? 0 then [] else [re_buf e1]) ++ res :: map key_addr (re_keys e1)).
    { unfold entry_blocks. cbn [re_cap re_buf re_hp re_keys]. rewrite (proj2 (Z.eqb_neq res 0) NZ). reflexivity. }
    assert (RPc : relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 regs mem2 md2).
    { eapply (sb_comp Bm API).
      all: try first [exact AX | exact CTX | exact EU | exact BW | exact SEGS | exact RP1 | exact RP2].
      - intros a Ha. change (spZ regs) with S0 in Ha.
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. glia.
      - intros a [X|X]; [left|right; exact X]. rewrite SPR2 in X. change (spZ regs) with S0.
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *. glia.
      - intros a Hs _ Ea. cbv beta in Ea. pose proof (ENI a Ea) as (EA & ENI' & _).
        destruct Hs as [Hs|Hs]; [change (spZ regs) with S0 in Hs | exact (ENI' (GEI a Hs))].
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Hs. glia.
      - intros p n Hp _ Hn NF Eq. cbv beta in Eq.
        assert (INq : In (ptr_addr L p, n) (blocks L A))
          by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
        destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n BK1 OU1 INq Hn NF) as (U1 & _).
        pose proof (blk_rng L A mem md _ _ HM0 INq) as BRq.
        apply U1. rewrite Eq. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0)) by glia.
        apply in_or_app. right. apply in_or_app. left. left. reflexivity.
      - intros a Ha _ _ Ea. exfalso. cbv beta in Ea. pose proof (ENI a Ea) as (EA & ENI' & _).
        destruct Ha as [Ha|Ha]; [glia | exact (ENI' Ha)].
      - intros p n i Hp Hp1 NF Hi Ea. exfalso. cbv beta in Ea.
        pose proof RP1 as (_ & _ & _ & _ & _ & AD1 & _).
        assert (INq : In (ptr_addr L p, n) (blocks L A))
          by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
        assert (INq1 : In (ptr_addr L p, n) (blocks L1 A1)).
        { unfold blocks. apply in_map_iff. exists (p, n).
          split; [cbn [fst snd]; rewrite (AD1 p n Hp Hp1 NF); reflexivity | exact Hp1]. }
        destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n BK1 OU1 INq ltac:(glia) NF) as (U1 & _).
        pose proof (ENI _ Ea) as (_ & _ & Cp).
        assert (NE : ptr_addr L p <> re_hp e1).
        { intros Eq. apply U1. rewrite Eq. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Cp).
          apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
        exact (EDJ _ n (ptr_addr L p + i) INq1 (or_intror NE) ltac:(glia) Ea). }
    apply SR_ret. right.
    exists R3, L2, A2, m3, md2,
      (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) res
          (re_nheld e1 * 8 + 8) (re_pad2 e1) (re_keys e1) (re_U e1) (re_junk e1)), h1, OUT1, junk1, LB1, D, jj.
    split; [reflexivity|].
    split; [unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [rgw X3|].
    split; [exact GS|]. split; [exact JJ|]. split; [exact IX|]. split; [exact NZ|].
    split; [cbn [re_kh]; unfold re_nheld; cbn [re_keys]; lia|].
    split; [exact DFs|].
    rewrite EKa.
    split.
    { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPc MU3 WM3 GEI).
      intros a Ha. destruct (dx_odec [(SA + 40, SA + 48)] a) as [Ox|(lo & hi & Iw & Rw)]; [left; exact Ox|right].
      destruct Iw as [Iw|[]]. injection Iw as <- <-.
      right. right. right. split; [exact (g_noimg a ltac:(glia))|].
      split; [exists G, SRC_TABLE; split; [exact GI2 | unfold SRC_TABLE, SRC_ENTRY in *; glia]|].
      intros p n i _ _ _ _ NE E. apply NE. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. glia. }
    split; [exact IN2|].
    split.
    { unfold MTR. exists (tp ++ [ev]), (qd ++ [qn]),
        (DA (da_out ad) (da_buf ad) (Ret (nretF tp)) (da_keys ad) (da_pend ad) (da_ev ad) (da_erecs ad)).
      split.
      - unfold RCORE, DLNK, dadr_ok, entry_links.
        cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs re_cap re_buf re_hp re_kh re_keys].
        split; [rewrite length_app, NT, RQ; reflexivity|].
        split.
        { apply p3a_wf_snoc; [exact WF0|]. rewrite Hev. destruct (ent_ka e1 =? 0); [exact I|]. rewrite <- RQ.
          exact Dhp. }
        split.
        { rewrite NT, <- RQ.
          assert (MO : forall x, p3a_ok x (length qd) -> p3a_ok x (length qd + 1)%nat)
            by (intros x Hx; exact (p3a_ok_mono _ _ _ Hx (Nat.le_add_r _ _))).
          assert (MF : forall xs, Forall (fun x => p3a_ok x (length qd)) xs ->
                         Forall (fun x => p3a_ok x (length qd + 1)%nat) xs)
            by (intros xs Hxs; apply Forall_forall; intros x Hx; exact (MO x (proj1 (Forall_forall _ _) Hxs x Hx))).
          split; [exact (MO _ Dout)|]. split; [exact (MO _ Dbuf)|]. split; [cbn [p3a_ok]; glia|].
          split; [exact (MF _ Dkeys)|]. split; [exact (MF _ Dpend)|]. split; [exact (MO _ Dev) | exact (MF _ Derecs)]. }
        split.
        { revert RS2. rewrite Hev. destruct (ent_ka e1 =? 0); intros RS2.
          - rewrite (p3a_runF_mal F qd qn bnd tp _ WF0 (eq_sym RQ)). exact RS2.
          - rewrite (p3a_runF_rea F qd qn bnd tp _ _ _ WF0 (eq_sym RQ) Dhp). exact RS2. }
        split; [|unfold DKH; right; cbn [re_kh]; clear - NH; lia].
        split.
        { intros LV OCp. rewrite (p3a_resolve_app qd [qn] _ Dout).
          apply KEEP; [exact (LKo LV OCp)|]. apply (sa_nb OUT1 e1 h1 OUT1 ND1). right. left. reflexivity. }
        split.
        { split.
          { intros Cp. rewrite (p3a_resolve_app qd [qn] _ Dbuf).
            apply KEEP; [exact (LKb Cp)|]. apply (sa_nb OUT1 e1 h1 _ ND1). right. right. right. left.
            rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by glia. left. reflexivity. }
          split.
          { intros _. change (live_at L2 A2 (nth (nretF tp) (qd ++ [qn]) (SP 0 0)) res (re_nheld e1 * 8 + 8)).
            rewrite (p3a_nth_last qd qn (nretF tp) (eq_sym RQ)). exact LQn. }
          apply (gr_f2 _ _ _ _ _ Dkeys LKk). intros kk yy Hkk Hyy Hll. cbv beta in Hyy, Hll |- *.
          rewrite (p3a_resolve_app qd [qn] yy Hyy).
          apply KEEP; [exact Hll|]. apply (sa_nb OUT1 e1 h1 _ ND1). right. right. right. right.
          apply in_map. exact Hkk. }
        apply (gr_src L1 A1 L2 A2 qd [qn] _ h1); [| exact Dev | exact Dpend | exact Derecs | exact LKs].
        intros pp xx nn Hxx Lxx. apply KEEP; [exact Lxx|]. apply (sa_nb OUT1 e1 h1 xx ND1). right. right. left.
        exact Hxx.
      - unfold RFUT. rewrite NT. cbv beta. cbn [da_out da_hp da_keys fst snd].
        rewrite <- (app_assoc tp [ev]). split; [exact TE1|]. split; [exact TF1 | exact TA1]. }
    split; [rewrite SEGS; exact RO3r|].
    split.
    { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FRc |].
      intros a Ha. cbn [cells_size csize app dr_saved] in Ha. exact (PS a ltac:(glia)). }
    split.
    { rewrite SEGS. apply ent_join; [exact K3 | exact K4 | | |].
      - apply TPr; [exact EC1|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; glia.
      - apply TPr; [exact EC2|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; glia.
      - apply (dr_join m3 (SA + 40) (SA + 48) [C8 (Z_to_bv 64 res)]
                 [C4 (Z_to_bv 64 (re_nheld e1)); CB 4 (re_pad2 e1)]); [exact HC3 | | cbn [cells_size csize]; lia].
        apply TPr; [exact EH2|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; glia. }
    split.
    { apply (sa_okx L1 A1 L2 A2 m1 m3 e1 Pa res MS EK1); [| | exact INres | exact FRES | exact OBK3].
      - intros q k0 Hq Hk. exact (proj1 (SURV q k0 Hq (proj1 (NBK q Hk)))).
      - intros q k0 a Hq Hk Ha. exact (PB q k0 a Hq (proj1 (NBK q Hk)) (proj2 (NBK q Hk)) Ha). }
    split.
    { eapply src_at_tr0; [exact MS | exact SR1 | | |].
      - intros a Ha. apply PI, GRP. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia.
      - intros q k0 Hq Hb. exact (proj1 (SURV q k0 Hq (NBH q Hb))).
      - intros q k0 a Hq Hb Ha. exact (PB q k0 a Hq (NBH q Hb) (NGH q Hb) Ha). }
    split.
    { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi _ Ha. apply PI, GRP.
      unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia. }
    split; [exact SM1|].
    split.
    { apply (sa_link s false (dlH s P) (dlka s P) _ (sv_no s P Q) (sv_oc s P Q) e1);
        [exact LK1 | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold ent_ka. cbn [re_hp re_kh]. rewrite (proj2 (Z.eqb_neq res 0) NZ). reflexivity. }
    split; [exact (sa_hist _ _ _ _ _ _ _ _ _ _ _ _ HI1)|].
    split; [rewrite (sa_pst s false (dlH s P) (dlka s P)); exact NK1|].
    split; [exact RST1|].
    split.
    { split.
      { assert (NDl : List.NoDup (([G; OUT1] ++ (if re_cap e1 =? 0 then [] else [re_buf e1])) ++
                  (if re_hp e1 =? 0 then [] else [re_hp e1]) ++ (map key_addr (re_keys e1) ++ hs_blocks h1))).
        { pose proof ND1 as ND1'. apply NoDup_ListNoDup in ND1'. unfold entry_blocks in ND1'.
          rewrite <- !app_assoc in ND1'. rewrite <- !app_assoc. exact ND1'. }
        pose proof (nodup_mid_drop _ _ _ NDl) as ND2.
        assert (NIres : ~ In res (([G; OUT1] ++ (if re_cap e1 =? 0 then [] else [re_buf e1])) ++
                                  (map key_addr (re_keys e1) ++ hs_blocks h1))).
        { intros Hin.
          assert (Hq : res = G \/ res = OUT1 \/ In res (hs_blocks h1) \/
                       In res (if re_cap e1 =? 0 then [] else [re_buf e1]) \/ In res (map key_addr (re_keys e1))).
          { cbn [app] in Hin. destruct Hin as [E|[E|Hin]]; [left; symmetry; exact E | right; left; symmetry; exact E|].
            apply in_app_or in Hin as [Hin|Hin]; [right; right; right; left; exact Hin|].
            apply in_app_or in Hin as [Hin|Hin]; [right; right; right; right; exact Hin | right; right; left; exact Hin]. }
          destruct (LIVEQ res Hq) as [R0|(k0 & Hk & Nk)]; [exact (NZ R0)|].
          exact (proj2 (SURV res k0 Hk Nk) eq_refl). }
        pose proof (nodup_mid_add _ _ res ND2 NIres) as ND3.
        apply NoDup_ListNoDup. rewrite EB'. rewrite <- !app_assoc in ND3. rewrite <- !app_assoc. exact ND3. }
      split; [exact GI2|].
      split.
      { intros q m Hq HO HE. pose proof (SV1 q m Hq HO HE) as Hq1. refine (proj1 (SURV q m Hq1 _)).
        destruct (Z.eq_dec (ent_ka e1) 0) as [C|C]; [left; exact C | right]. intros ->.
        destruct KHC as [(H0 & KA0 & _)|(HN & KA & HI & _ & _ & H8' & _)]; [glia|].
        assert (Em : m = re_kh e1) by exact (sb_nodup_fst _ _ _ _ NDB1 Hq1 HI).
        destruct (FB1 (re_hp e1) m Hq ltac:(glia) HO HE) as (_ & U1 & _). apply U1. unfold entry_blocks.
        rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) HN). apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
      split.
      { intros q m Hq. destruct (BACK q m Hq) as [(-> & ->)|(Hq1 & NBq)].
        - right. left. apply in_or_app. left. rewrite EB'. apply in_or_app. right. left. reflexivity.
        - destruct (CL1 q m Hq1) as [X|[X|X]]; [left; exact X | right; left | right; right; exact X].
          apply in_app_or in X as [X|X]; apply in_or_app; [left | right; exact X].
          rewrite EB'. unfold entry_blocks in X. apply in_app_or in X as [X|X]; [apply in_or_app; left; exact X|].
          apply in_app_or in X as [X|X]; [|apply in_or_app; right; right; exact X].
          exfalso. revert X. destruct (Z.eqb_spec (re_hp e1) 0) as [HZ|HZ]; intros X; [destruct X | destruct X as [X|[]]].
          destruct NBq as [NBq|NBq]; [|exact (NBq (eq_sym X))].
          destruct KHC as [(H0 & _)|(_ & KA & _ & _ & _ & H8' & _)]; glia. }
      intros q m Hq Hm HO HE. destruct (FB1 q m Hq Hm HO HE) as (U0 & U1 & U2).
      split; [exact U0|]. split; [|exact U2].
      rewrite EB'. intros X. apply in_app_or in X as [X|[X|X]].
      - apply U1. unfold entry_blocks. apply in_or_app. left. exact X.
      - pose proof (SV1 q m Hq HO HE) as Hq1.
        assert (NBq : ent_ka e1 = 0 \/ q <> re_hp e1).
        { destruct (Z.eq_dec (re_hp e1) 0) as [C|C].
          - left. unfold ent_ka. rewrite C. reflexivity.
          - right. intros E. apply U1. rewrite E. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) C).
            apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
        exact (proj2 (SURV q m Hq1 NBq) (eq_sym X)).
      - apply U1. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. exact X. }
    split.
    { destruct GL1 as (C1 & C2 & C3 & CC4 & _).
      split; [eapply rw_tr; [exact MS | exact C1 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GCP; unfold G_CLIENT in *; glia|].
      split; [eapply rw_tr; [exact MS | exact C2 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      split; [eapply rw_tr; [exact MS | exact C3 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      split; [eapply rw_tr; [exact MS | exact CC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      destruct (sb_c4 m3 ERR) as (v & HV); [glia | glia | |exists v; rewrite SEGS; exact HV].
      intros i Hi. rewrite <- SEGS. apply WM3, SC2. right. glia. }
    apply (sa_out s false (dlH s P) (dlka s P)).
    destruct OU1 as (OF & OT). split.
    + intros LV. destruct (OF LV) as (C & EO & EC' & OB).
      split; [eapply rw_tr; [exact MS | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      split; [exact EO|]. split; [exact EC'|]. intros Cp. destruct (OB Cp) as (OI & OBy).
      assert (NBo : ent_ka e1 = 0 \/ OUT <> re_hp e1).
      { rewrite <- EO. apply (sa_nb OUT1 e1 h1 OUT1 ND1). right. left. reflexivity. }
      split; [exact (proj1 (SURV OUT CAP OI NBo))|].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha.
      apply (PB OUT CAP a OI NBo); [apply (dx_ng OUT1 _ OUT ND1); left; symmetry; exact EO|].
      destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & _ & LJ)]; [glia|]. rewrite length_app in Ha. glia.
    + intros LV. destruct (OT LV) as (C & OB).
      split; [eapply rw_tr; [exact MS | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
              apply PI, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
      destruct OB as [Z0|(Cp & NLo & OI & OFr & OBy & LJ)]; [left; exact Z0|right].
      assert (NBo : ent_ka e1 = 0 \/ OUT1 <> re_hp e1)
        by (apply (sa_nb OUT1 e1 h1 OUT1 ND1); right; left; reflexivity).
      split; [exact Cp|]. split; [exact NLo|]. split; [exact (proj1 (SURV _ _ OI NBo))|]. split; [exact OFr|].
      split; [|exact LJ].
      eapply by_tr; [exact MS | exact OBy |]. intros a Ha.
      apply (PB OUT1 _ a OI NBo); [apply (dx_ng OUT1 _ OUT1 ND1); left; reflexivity|].
      assert (LL : Z.of_nat (length LB1) = Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P ++ [dline s P Q]))))
        by (rewrite <- H7h; unfold bzs; rewrite length_map; reflexivity).
      rewrite !length_app in Ha. glia.
Qed.

Lemma sb_ret_ok : YK0s.ret_ok (Z_to_bv 64 0x13d5c).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma sb_pre_dup : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre_k Bm MR STRNDUP_STACK L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold STRNDUP_STACK, ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold STRNDUP_STACK, ALLOC_STACK in Ha. apply SC1. left.
    change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma sb_dup_rp : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 (E : Z -> Prop), MR L1 A1 m1 md1 ->
  call_post_k Bm MR STRNDUP_STACK L1 A1 R1 m1 md1 E L2 A2 R2 m2 md2 ->
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ E a) ->
  (forall q k, In (q, k) (user_blocks A1) -> In (q, k) (user_blocks A2)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  relay_post Bm API STRNDUP_STACK (fun _ => False) (fun _ => False) L1 A1 R1 m1 md1 L2 A2 R2 m2 md2.
Proof using AX CTX.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 E HM CP NE SURV LN.
  destruct CP as (M' & W' & B' & LL & AD & RP & MD & FR & BY & SC).
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LL|]. split; [exact LN|].
  split; [intros q k H1 H2 _; exact (AD q k H1 H2)|].
  split; [intros q k H1 _ _; exact (SURV q k H1)|].
  split; [intros q H1; pose proof (SURV q 0 H1) as H2; split; [exact H2 | exact (AD q 0 H1 H2)]|].
  split; [intros a Hi Ho; exact (sb_owned_img Bm API AX CTX L1 A1 m1 md1 L2 A2 m2 md2 a HM M' Hi Ho)|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS _; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | exact (NE a Ha)]|].
  split; [intros q k i H1 H2 _ Hi _; exact (BY q k i H1 H2 Hi)|].
  exact SC.
Qed.

Lemma sb_c8w : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> writable_at rsegs m (a + i)) -> exists v, rw_cells rsegs m a [C8 v].
Proof using Bm G HJ O h junk regs.
  intros m a H0 H1 W.
  destruct (sb_wr_rd m (a + 0) (W 0 ltac:(lia))) as [b0 E0].
  destruct (sb_wr_rd m (a + 1) (W 1 ltac:(lia))) as [b1 E1].
  destruct (sb_wr_rd m (a + 2) (W 2 ltac:(lia))) as [b2 E2].
  destruct (sb_wr_rd m (a + 3) (W 3 ltac:(lia))) as [b3 E3].
  destruct (sb_wr_rd m (a + 4) (W 4 ltac:(lia))) as [b4 E4].
  destruct (sb_wr_rd m (a + 5) (W 5 ltac:(lia))) as [b5 E5].
  destruct (sb_wr_rd m (a + 6) (W 6 ltac:(lia))) as [b6 E6].
  destruct (sb_wr_rd m (a + 7) (W 7 ltac:(lia))) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (L8 : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
    exact (sb_le_rt [b0; b1; b2; b3; b4; b5; b6; b7]). }
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, L8. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error];
      [exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (W i Hi).
Qed.

Lemma sb_nd_snoc : forall {X : Type} (l : list X) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof using.
  intros X l x. induction l as [|y l IH]; intros ND NI; cbn [app].
  - constructor; [intros [] | constructor].
  - apply List.NoDup_cons_iff in ND as [Hy Hl]. constructor.
    + intros Hin. apply in_app_or in Hin as [Hin|[Hin|[]]]; [exact (Hy Hin)|]. apply NI. left. symmetry. exact Hin.
    + apply IH; [exact Hl|]. intros Hin. apply NI. right. exact Hin.
Qed.

Lemma sb_eb_live : forall L1 A1 m1 e1 q, entry_okx L1 A1 m1 e1 -> In q (entry_blocks e1) ->
  exists k, In (q, k) (blocks L1 A1).
Proof using HG HJ O h junk.
  intros L1 A1 m1 e1 q (_ & _ & _ & _ & _ & _ & _ & _ & E9 & _ & E11 & _ & _ & E14) Hq.
  unfold entry_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [|apply in_app_or in Hq as [Hq|Hq]].
  - revert Hq. destruct (Z.eqb_spec (re_cap e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E9 as [(C0 & _)|(_ & BI & _)]; [lia | exists (re_cap e1); exact BI].
  - revert Hq. destruct (Z.eqb_spec (re_hp e1) 0) as [C|C]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct E11 as [(H0 & _)|(HI & _)]; [lia | exists (re_kh e1); exact HI].
  - apply in_map_iff in Hq as (k & <- & Hk). destruct (proj1 (Forall_forall _ _) E14 k Hk) as (K1 & _).
    eexists; exact K1.
Qed.

Lemma sb_hp_nd : forall OUT1 e1 h1, NoDup (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) -> re_hp e1 <> 0 ->
  ~ In (re_hp e1) (G :: OUT1 :: (if re_cap e1 =? 0 then [] else [re_buf e1]) ++ map key_addr (re_keys e1) ++
                   hs_blocks h1).
Proof using.
  intros OUT1 e1 h1 ND H0. apply NoDup_ListNoDup in ND.
  assert (E : G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1 =
              (G :: OUT1 :: (if re_cap e1 =? 0 then [] else [re_buf e1])) ++
              re_hp e1 :: (map key_addr (re_keys e1) ++ hs_blocks h1)).
  { unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) H0). cbn [app]. rewrite <- !app_assoc. reflexivity. }
  rewrite E in ND. apply NoDup_remove_2 in ND. exact ND.
Qed.

Lemma sb_okx : forall L1 A1 L2 A2 m1 m2 e1 Pa (k : Z * list byte * list byte),
  msame Pa m1 m2 -> entry_okx L1 A1 m1 e1 ->
  (forall q n, In (q, n) (blocks L1 A1) -> In q (entry_blocks e1) -> In (q, n) (blocks L2 A2)) ->
  (forall q n a, In (q, n) (blocks L1 A1) -> In q (entry_blocks e1) -> q <= a < q + n ->
     (q <> re_hp e1 \/ a < re_hp e1 + 8 * re_nheld e1) -> Pa a) ->
  (re_cap e1 = 0 \/ re_buf e1 <> re_hp e1) -> ~ In (re_hp e1) (map key_addr (re_keys e1)) ->
  re_hp e1 <> 0 -> re_kh e1 = 8 * (re_nheld e1 + 1) -> re_nheld e1 + 1 < 2 ^ 26 ->
  bytes_at segs m2 (re_hp e1 + 8 * re_nheld e1) (le8 (Z_to_bv 64 (key_addr k))) ->
  key_okw L2 A2 m2 k -> ~ In (key_addr k) (map key_addr (re_keys e1)) ->
  ~ In (key_text k) (map key_text (re_keys e1)) ->
  entry_okx L2 A2 m2 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1)
    (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1 ++ [k]) (re_U e1) (re_junk e1)).
Proof using HG HJ O h junk.
  intros L1 A1 L2 A2 m1 m2 e1 Pa k MS (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14)
    SV HP NBH NKH H0 KH NL SB KO NA NT.
  assert (IB : re_cap e1 <> 0 -> In (re_buf e1) (entry_blocks e1)).
  { intros C. unfold entry_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
  assert (IH : In (re_hp e1) (entry_blocks e1)).
  { unfold entry_blocks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ 0) H0). left. reflexivity. }
  assert (IK : forall k0, In k0 (re_keys e1) -> In (key_addr k0) (entry_blocks e1)).
  { intros k0 Hk. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
  assert (NN : 0 <= re_nheld e1) by (unfold re_nheld; lia).
  destruct E11 as [(Z0 & _)|(HI & HF & H8 & H8' & HB)]; [exfalso; exact (H0 Z0)|].
  match goal with |- entry_okx _ _ _ ?e2 => assert (RN : re_nheld e2 = re_nheld e1 + 1) end.
  { unfold re_nheld. cbn [re_keys]. rewrite length_app. cbn [length]. lia. }
  unfold entry_okx. rewrite RN.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys].
  do 8 (split; [assumption|]).
  split.
  { destruct E9 as [Z0|(C0 & BI & BF & BJ & BC)]; [left; exact Z0 | right].
    assert (CN : re_cap e1 <> 0) by lia.
    split; [exact C0|]. split; [exact (SV _ _ BI (IB CN))|]. split; [exact BF|]. split; [exact BJ|].
    eapply rw_tr; [exact MS | exact BC |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply (HP _ _ a BI (IB CN)); [lia|]. left. destruct NBH as [C|C]; [lia | exact C]. }
  split; [lia|].
  split.
  { right. split; [exact (SV _ _ HI IH)|]. split; [exact HF|]. split; [lia|]. split; [lia|].
    rewrite CF.gestures_end_b.key_ptrs_app. apply bytes_at_app. split.
    - eapply by_tr; [exact MS | exact HB |]. intros a Ha. rewrite CF.gestures_end_b.key_ptrs_length in Ha.
      apply (HP _ _ a HI IH); [unfold re_nheld in H8; lia | right; unfold re_nheld; lia].
    - rewrite CF.gestures_end_b.key_ptrs_length.
      replace (re_hp e1 + Z.of_nat (8 * length (re_keys e1))) with (re_hp e1 + 8 * re_nheld e1)
        by (unfold re_nheld; lia).
      change (key_ptrs [k]) with (le8 (Z_to_bv 64 (key_addr k)) ++ []). rewrite app_nil_r. exact SB. }
  split.
  { apply NoDup_ListNoDup. rewrite map_app. cbn [map].
    apply sb_nd_snoc; [apply NoDup_ListNoDup; exact E12 | exact NA]. }
  split.
  { apply NoDup_ListNoDup. rewrite map_app. cbn [map].
    apply sb_nd_snoc; [apply NoDup_ListNoDup; exact E13 | exact NT]. }
  apply Forall_app. split; [|constructor; [exact KO | constructor]].
  apply Forall_forall. intros k0 Hk. destruct (proj1 (Forall_forall _ _) E14 k0 Hk) as (K1 & K2 & K3 & K4 & K5).
  split; [exact (SV _ _ K1 (IK k0 Hk))|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  eapply by_tr; [exact MS | exact K3 |]. intros a Ha. apply (HP _ _ a K1 (IK k0 Hk)).
  - rewrite length_app in Ha. cbn [length] in Ha. lia.
  - left. intros E. apply NKH. rewrite <- E. apply in_map. exact Hk.
Qed.

Lemma sb_blk : forall L1 A1 L2 A2 e1 h1 OUT1 d (k : Z * list byte * list byte),
  DBLK L1 A1 e1 h1 OUT1 -> key_addr k = d ->
  (forall q n, In (q, n) (blocks L1 A1) -> In (q, n) (blocks L2 A2)) ->
  (forall q n, In (q, n) (blocks L2 A2) -> q = d \/ In (q, n) (blocks L1 A1)) ->
  ~ In d (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) -> (forall n, ~ In (d, n) (blocks L1 A1)) ->
  DBLK L2 A2 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1)
                 (re_kh e1) (re_pad2 e1) (re_keys e1 ++ [k]) (re_U e1) (re_junk e1)) h1 OUT1.
Proof using.
  intros L1 A1 L2 A2 e1 h1 OUT1 d k (ND1 & GI1 & SV1 & CL1 & FB1) Ek SVB BACK NI NB.
  match goal with |- DBLK _ _ ?e2 _ _ => assert (EB : entry_blocks e2 = entry_blocks e1 ++ [d]) end.
  { unfold entry_blocks. cbn [re_cap re_buf re_hp re_keys]. rewrite map_app. cbn [map]. rewrite Ek, !app_assoc.
    reflexivity. }
  unfold DBLK. rewrite EB.
  split.
  { apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND1.
    replace (G :: OUT1 :: (entry_blocks e1 ++ [d]) ++ hs_blocks h1)
      with ((G :: OUT1 :: entry_blocks e1) ++ d :: hs_blocks h1) by (cbn [app]; rewrite <- !app_assoc; reflexivity).
    apply nodup_mid_add; [exact ND1 | exact NI]. }
  split; [exact (SVB _ _ GI1)|].
  split; [intros q m Hq HO HE; exact (SVB _ _ (SV1 q m Hq HO HE))|].
  split.
  { intros q m Hq. destruct (BACK q m Hq) as [->|Hq1].
    - right. left. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
    - destruct (CL1 q m Hq1) as [X|[X|X]]; [left; exact X | right; left | right; right; exact X].
      apply in_app_or in X as [X|X]; apply in_or_app; [left; apply in_or_app; left; exact X | right; exact X]. }
  intros q m Hq Hm HO HE. destruct (FB1 q m Hq Hm HO HE) as (U0 & U1 & U2).
  split; [exact U0|]. split; [|exact U2].
  intros X. apply in_app_or in X as [X|[X|[]]]; [exact (U1 X)|]. subst q.
  exact (NB m (SV1 d m Hq HO HE)).
Qed.

Lemma sb_link : forall s sk H H' ka no oc e1 e2 h1,
  DLINK (dvirt s sk H ka no oc) e1 h1 -> re_cap e2 = re_cap e1 -> re_U e2 = re_U e1 -> re_skip e2 = re_skip e1 ->
  keys_texts (re_keys e2) = H' -> ent_ka e2 = ent_ka e1 -> DLINK (dvirt s sk H' ka no oc) e2 h1.
Proof using.
  intros s sk H H' ka no oc e1 e2 h1 (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1)
    E1 E2 E3 E4 E5.
  split; [rewrite E1; exact L1c|]. split; [rewrite E2; exact L2c|]. split; [rewrite E3; exact L3c|].
  split; [exact E4|]. split; [rewrite E5; exact L5c|].
  split; [exact L6c|]. split; [exact L7c|]. split; [exact L8c|]. split; [exact L9c|]. split; [exact L10c|].
  split; [exact L11c | exact WF1].
Qed.

Lemma sb_hist : forall sent kl kl' l Dh s sk H ka no oc h1 LB1,
  DHISTg sent kl Dh (dvirt s sk H ka no oc) h1 LB1 -> kl' = kl ++ [l] ->
  DHISTg sent kl' Dh (dvirt s sk (seen_arr H l) ka no oc) h1 LB1.
Proof using.
  intros sent kl kl' l Dh s sk H ka no oc h1 LB1 (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10) Ek. subst kl'.
  cbn [dvirt ds_H] in Y8, Y9.
  assert (Y8' : List.NoDup H) by (apply NoDup_ListNoDup; exact Y8).
  destruct (seen_arr_ok H (upds (keys_texts (re_keys e)) kl) l Y8' Y9) as [HN HS].
  unfold DHISTg.
  refine (conj Y1 (conj Y2 (conj Y3 (conj Y4 (conj Y5 (conj Y6 (conj Y7 (conj _ (conj _ Y10))))))))).
  - cbn [dvirt ds_H]. apply NoDup_ListNoDup. exact HN.
  - cbn [dvirt ds_H]. unfold upds in HS |- *. rewrite fold_left_app. exact HS.
Qed.

Lemma sb_pst : forall s sk H H' ka no oc, pstream (dvirt s sk H' ka no oc) = pstream (dvirt s sk H ka no oc).
Proof using. reflexivity. Qed.

Lemma sb_out : forall s sk H H' ka no oc L1 A1 m1 OUT1 junk1 LB1,
  DOUT (dvirt s sk H ka no oc) L1 A1 m1 OUT1 junk1 LB1 -> DOUT (dvirt s sk H' ka no oc) L1 A1 m1 OUT1 junk1 LB1.
Proof using. intros s sk H H' ka no oc L1 A1 m1 OUT1 junk1 LB1 X. exact X. Qed.

Lemma H2_sab_live : forall K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n, WF A1 ->
  relay_post Bm API K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p q n -> ~ F0 q -> live_at L2 A2 p q n.
Proof using All.
  intros K E F0 L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p q n W1 RP [Hp Hq] NF.
  pose proof RP as (_ & _ & _ & _ & _ & RPa & RPb & RPz & _). rewrite <- Hq in NF.
  destruct (Z_lt_le_dec 0 n) as [Np|Nn].
  - pose proof (RPb p n Hp Np NF) as Hp2. split; [exact Hp2|]. rewrite (RPa p n Hp Hp2 NF). exact Hq.
  - assert (N0 : n = 0) by (pose proof (sb_ub_nonneg A1 p n W1 Hp) as N1; clear - N1 Nn; lia). subst n.
    destruct (RPz p Hp) as [Hp2 Ha]. split; [exact Hp2|]. rewrite Ha. exact Hq.
Qed.

Lemma H2_sab_nret : forall (tp : trF) n, nretF (tp ++ [RMalloc n]) = S (nretF tp).
Proof using All. intros tp n. rewrite nret_app. change (nretF [RMalloc n]) with 1%nat. lia. Qed.

Lemma H2_sab_nretc : forall n (X : trF), nretF (RMalloc n :: X) = S (nretF X).
Proof using All. intros n X. reflexivity. Qed.

Lemma H2_sab_room : forall (tp X1 X2 : trF) qd n, wf_from sptr 0 tp -> length qd = nretF tp ->
  (tp ++ RMalloc n :: X1) ++ X2 = TR -> rt_room F (runF F qd bnd tp) n.
Proof using All.
  intros tp X1 X2 qd n W LQ E.
  assert (E' : tp ++ RMalloc n :: X1 ++ X2 = TR) by (rewrite <- E, <- app_assoc; reflexivity).
  apply (p3a_room_next F qd bnd tp (RMalloc n) (X1 ++ X2) n W (eq_sym LQ)); [|left; reflexivity].
  rewrite E'. exact ROOM.
Qed.

Lemma H2_sab_mtr : forall s P Q (jj : nat) K L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 oc e1 h1 OUT1 d (buf : list byte) tp qd a,
  WF A1 -> relay_post Bm API K (fun _ => False) (fun _ => False) L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  NoDup (map fst (blocks L2 A2)) -> In (d, Z.of_nat jj + 1) (blocks L2 A2) -> length buf = jj ->
  RCORE L1 A1 oc e1 h1 OUT1 tp qd a ->
  RFUT (tp ++ RMalloc (Z.of_nat jj + 1) ::
          fst (sv_rest s P Q (S (nretF tp)) (da_out a) (da_hp a) (da_keys a ++ [Ret (nretF tp)])))
    (drun (length (pstream s)) LIVE MX (dnext LIVE MX s)
       (nretF tp + nretF (RMalloc (Z.of_nat jj + 1) ::
          fst (sv_rest s P Q (S (nretF tp)) (da_out a) (da_hp a) (da_keys a ++ [Ret (nretF tp)]))))
       (anext a (snd (sv_rest s P Q (S (nretF tp)) (da_out a) (da_hp a) (da_keys a ++ [Ret (nretF tp)]))))) ->
  rt_ok F A2 (rt_malloc F (runF F qd bnd tp) (Z.of_nat jj + 1)) ->
  MTR s L2 A2 oc (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1)
                    (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1 ++ [(d, buf, [])]) (re_U e1) (re_junk e1))
    h1 OUT1 (sv_rest s P Q).
Proof using All.
  intros s P Q jj K L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 oc e1 h1 OUT1 d buf tp qd a W1 RP ND IND LB
    (RQ & WF0 & DOK & RS1 & (LKo & (LKb & LKh & LKk) & LKs) & KH) RF RS2.
  pose proof DOK as (Nout & Nbuf & Nhp & Nkeys & Npend & Nev & Nerecs).
  pose proof DOK as (Dout & Dbuf & Dhp & Dkeys & Dpend & Dev & Derecs).
  rewrite <- RQ in Dout, Dbuf, Dhp, Dkeys, Dpend, Dev, Derecs.
  assert (T : forall p x n, live_at L1 A1 p x n -> live_at L2 A2 p x n)
    by (intros p x n Hl; exact (H2_sab_live K _ _ L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p x n W1 RP Hl (fun X => X))).
  assert (RA : forall x, p3a_ok x (length qd) -> resolveF (qd ++ [sptr_of L2 A2 d]) x = resolveF qd x)
    by (intros x Hx; exact (p3a_resolve_app qd [sptr_of L2 A2 d] x Hx)).
  unfold MTR. exists (tp ++ [RMalloc (Z.of_nat jj + 1)]), (qd ++ [sptr_of L2 A2 d]),
    (DA (da_out a) (da_buf a) (da_hp a) (da_keys a ++ [Ret (nretF tp)]) (da_pend a) (da_ev a) (da_erecs a)).
  split.
  - unfold RCORE, DLNK, dadr_ok, entry_links. rewrite H2_sab_nret.
    cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs re_cap re_buf re_hp re_kh re_keys].
    split; [rewrite length_app, RQ; cbn [length]; lia|].
    split; [apply p3a_wf_snoc; [exact WF0 | exact I]|].
    split.
    { assert (MO : forall x, p3a_ok x (nretF tp) -> p3a_ok x (S (nretF tp)))
        by (intros x Hx; exact (p3a_ok_mono x _ _ Hx (Nat.le_succ_diag_r _))).
      assert (MF : forall xs, Forall (fun x => p3a_ok x (nretF tp)) xs ->
                     Forall (fun x => p3a_ok x (S (nretF tp))) xs)
        by (intros xs Hxs; exact (Forall_impl (fun x => p3a_ok x (S (nretF tp))) MO Hxs)).
      split; [exact (MO _ Nout)|]. split; [exact (MO _ Nbuf)|]. split; [exact (MO _ Nhp)|].
      split; [apply Forall_app; split; [exact (MF _ Nkeys) | constructor; [cbn [p3a_ok]; lia | constructor]]|].
      split; [exact (MF _ Npend)|]. split; [exact (MO _ Nev) | exact (MF _ Nerecs)]. }
    split; [rewrite (p3a_runF_mal F qd (sptr_of L2 A2 d) bnd tp _ WF0 (eq_sym RQ)); exact RS2|].
    split; [|exact KH].
    split; [intros LV OCp; rewrite (RA _ Dout); exact (T _ _ _ (LKo LV OCp))|].
    split.
    { split; [intros C; rewrite (RA _ Dbuf); exact (T _ _ _ (LKb C))|].
      split; [intros C; rewrite (RA _ Dhp); exact (T _ _ _ (LKh C))|].
      apply Forall2_app.
      - apply (gr_f2 _ _ _ _ _ Dkeys LKk). intros k y _ Hy Hl. cbv beta in Hl |- *.
        rewrite (RA _ Hy). exact (T _ _ _ Hl).
      - constructor; [|constructor]. cbv beta.
        change (resolveF (qd ++ [sptr_of L2 A2 d]) (Ret (nretF tp)))
          with (nth (nretF tp) (qd ++ [sptr_of L2 A2 d]) (SP 0 0)).
        rewrite (p3a_nth_last qd (sptr_of L2 A2 d) (nretF tp) (eq_sym RQ)).
        unfold key_addr, key_text. cbn [fst snd]. rewrite LB.
        exact (sptr_of_spec L2 A2 d (Z.of_nat jj + 1) ND IND). }
    exact (gr_src L1 A1 L2 A2 qd [sptr_of L2 A2 d] a h1 (fun p x n _ Hl => T p x n Hl) Dev Dpend Derecs LKs).
  - rewrite H2_sab_nret. cbn [da_out da_hp da_keys].
    set (X := sv_rest s P Q (S (nretF tp)) (da_out a) (da_hp a) (da_keys a ++ [Ret (nretF tp)])) in *.
    assert (EN : (S (nretF tp) + nretF (fst X) = nretF tp + nretF (RMalloc (Z.of_nat jj + 1) :: fst X))%nat)
      by (rewrite H2_sab_nretc; lia).
    rewrite EN, <- app_assoc. exact RF.
Qed.

Lemma seen_add_b : forall s P Q c, DGK s P Q c -> SR segs c (DLN s (S Q)).
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & jj & -> & RT1 & G1 & G9 & G18 &
    G10 & G11 & GS & JJ & IX & HP0 & KH & DFs & LC1).
  pose proof LC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NK1 & RST1 & BK1 & GL1
    & OU1).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & W1 & B1 & _).
  pose proof RT1 as (((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26) & G27).
  pose proof pre_facts as (_ & _ & _ & _ & _ & HCEIL & H63 & _ & _ & _).
  pose proof err_hi as EH. unfold G_LOCK_HI in F9.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof BK1 as (ND1 & GI1 & SV1 & CL1 & FB1).
  pose proof HI1 as (_ & _ & _ & _ & _ & H6h & H7h & _).
  pose proof DFs as (DBd & PQ & HQz & HNZ & HSKp & HLL).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & BSb & B0b & BU & BP).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
  assert (NHD : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
  assert (NN : 0 <= re_nheld e1) by (rewrite NHD; lia).
  assert (L4' : keys_texts (re_keys e1) = dlH s P) by exact L4c.
  assert (HLEN : length (dlH s P) = length (re_keys e1)) by (rewrite <- L4'; unfold keys_texts; apply length_map).
  assert (NL : re_nheld e1 + 1 < 2 ^ 26) by (rewrite NHD, <- HLEN; glia).
  assert (JBz : Z.of_nat jj < 6000).
  { unfold LINE_LIMIT in HLL. assert (X : (jj < 6000)%nat) by glia. apply Nat2Z.inj_lt in X.
    change (Z.of_nat 6000) with 6000 in X. exact X. }
  assert (JJz : 13 < Z.of_nat jj).
  { assert (X : (13 < jj)%nat) by glia. apply Nat2Z.inj_lt in X. change (Z.of_nat 13) with 13 in X. exact X. }
  destruct K9 as [(C0 & _ & U0)|(Cp & BI & BFr & BJ & BC)]; [exfalso; glia|].
  destruct K11 as [(H0 & _)|(HI & HF & H8 & H8' & HB)]; [exfalso; exact (HP0 H0)|].
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BRb.
  pose proof (blk_rng _ _ _ _ _ _ M1 HI) as BRh.
  pose proof (blk_align _ _ _ _ _ _ M1 HI) as BAh.
  pose proof HF as (HF1 & HF2 & HF3).
  assert (NHG : re_hp e1 <> G) by (intros E; apply (sb_hp_nd OUT1 e1 h1 ND1 HP0); left; symmetry; exact E).
  pose proof (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 HI GI1 NHG) as DJh.
  assert (NHO : OUT1 <> re_hp e1) by (intros E; apply (sb_hp_nd OUT1 e1 h1 ND1 HP0); right; left; exact E).
  assert (NHH : forall q, In q (hs_blocks h1) -> q <> re_hp e1).
  { intros q Hb E. apply (sb_hp_nd OUT1 e1 h1 ND1 HP0). rewrite <- E. right. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (NGH : forall q, In q (hs_blocks h1) -> q <> G)
    by (intros q Hb; apply (dx_ng OUT1 _ q ND1); right; apply in_or_app; right; exact Hb).
  assert (LX : length (firstn jj (dline s P Q)) = jj).
  { rewrite firstn_length_le; [reflexivity|]. rewrite (dline_len s P Q PQ). glia. }
  remember (firstn jj (skipn P (re_U e1))) as buf eqn:Ebuf.
  assert (LB : length buf = jj).
  { rewrite Ebuf. apply firstn_length_le. rewrite length_skipn. glia. }
  assert (EB : bzs buf = firstn jj (dline s P Q)).
  { rewrite Ebuf, <- firstn_bzs, <- skipn_bzs, EW. unfold dline. rewrite firstn_firstn, Nat.min_l by glia.
    reflexivity. }
  assert (BB : bytes_at segs m1 (re_buf e1 + Z.of_nat P) buf).
  { pose proof BSb as X. rewrite <- (firstn_skipn P (re_U e1)) in X. apply bytes_at_app in X as [_ X].
    rewrite <- (firstn_skipn jj (skipn P (re_U e1))) in X. apply bytes_at_app in X as [X _].
    rewrite firstn_length_le in X by glia. rewrite Ebuf. exact X. }
  assert (NZx : nozero (bzs buf)).
  { rewrite Ebuf, <- firstn_bzs, <- skipn_bzs, EW. apply nz_firstn. intros i Hi. rewrite nth_skipn. apply HNZ.
    glia. }
  assert (NZb : ~ In (Z_to_bv 8 0) buf).
  { intros Hin. unfold nozero in NZx. rewrite Forall_forall in NZx.
    apply (NZx (bz (Z_to_bv 8 0))); [unfold bzs; apply in_map; exact Hin | reflexivity]. }
  assert (FB : firstn jj buf = buf) by (rewrite <- LB; apply firstn_all).
  assert (FBN : StrFun.find_byte 0 buf = None).
  { apply StrFun.find_byte_notin. intros b Hb E. apply NZb. replace (Z_to_bv 8 0) with b; [exact Hb|].
    apply bv_eq. rewrite E. reflexivity. }
  assert (SNL : StrFun.strnlen_res (Z.of_nat jj) buf = Z.of_nat jj).
  { unfold StrFun.strnlen_res. rewrite Nat2Z.id, FB, FBN. reflexivity. }
  assert (MOK : StrFun.memchr_ok (re_buf e1 + Z.of_nat P) 0 (Z.of_nat jj) buf).
  { unfold StrFun.memchr_ok. rewrite Nat2Z.id, FB, FBN. cbv beta iota. rewrite LB. lia. }
  assert (SAR2 : seen_arr (dlH s P) (dline s P Q) = dlH s P ++ [firstn jj (dline s P Q)]).
  { unfold seen_arr. rewrite GS. cbv beta iota. rewrite IX. reflexivity. }
  destruct TR1 as (tp & qd & ad & RC1 & RF1).
  pose proof RC1 as (RQ & WF0 & _ & RS1 & _).
  assert (RMn : rt_room F (runF F qd bnd tp) (Z.of_nat jj + 1))
    by exact (H2_sab_room tp _ _ qd (Z.of_nat jj + 1) WF0 RQ (proj1 RF1)).
  assert (SPR1 : spZ R1 = S0 - 144).
  { change (spZ R1) with (bv_unsigned (getr R1 2)). rewrite G2. apply unsigned_lit. glia. }
  assert (PRE2 : call_pre_k Bm MR STRNDUP_STACK L1 A1 R1 m1 md1).
  { apply (sb_pre_dup L1 A1 m1 md1 R1 RP1 IN1 G2 G4). rewrite G1. exact sb_ret_ok. }
  assert (DISJ : re_buf e1 + Z.of_nat P + Z.of_nat (length buf) <= spZ R1 - STRNDUP_STACK \/
                 (spZ R1 <= re_buf e1 + Z.of_nat P /\ re_buf e1 + Z.of_nat P + Z.of_nat (length buf) <= 2 ^ 64)).
  { left. rewrite SPR1, LB. unfold STRNDUP_STACK, ALLOC_STACK. glia. }
  assert (LEN : StrFun.strnlen_res (Z.of_nat jj) buf + 1 <= 2 ^ 28) by (rewrite SNL; clear - JBz; lia).
  assert (ROOMd : rt_room F (runF F qd bnd tp) (StrFun.strnlen_res (Z.of_nat jj) buf + 1))
    by (rewrite SNL; exact RMn).
  assert (OKs : 0 < re_buf e1 + Z.of_nat P < 2 ^ 64) by glia.
  assert (OKn : 0 <= Z.of_nat jj < 2 ^ 64) by glia.
  assert (HOME : str_home Bm L1 A1 (spZ R1) (re_buf e1 + Z.of_nat P) (StrFun.strnlen_res (Z.of_nat jj) buf)).
  { rewrite SNL. right. left. exists (re_buf e1), (re_cap e1). split; [exact BI | glia]. }
  eapply SR_bind.
  { exact (SDC L1 A1 R1 m1 md1 (re_buf e1 + Z.of_nat P) (Z.of_nat jj) buf (runF F qd bnd tp) PRE2 G10 G11
             OKn (fun i Hi => mbyte_of_bytes_at segs m1 _ buf i BB Hi) MOK OKs DISJ HOME LEN RS1 ROOMd RO1). }
  clear HOME DISJ LEN ROOMd OKs OKn MOK PRE2.
  intros c' (L2 & A2 & regs2 & mem2 & md2 & d & -> & CP & G10' & DNZ & _ & DFR & DBL & _ & DCPY & RO2 & _ & SURVu &
    INI2 & LN & RS2).
  rewrite SNL in CP, DFR, DBL, DCPY, RS2. rewrite Nat2Z.id, FB in DCPY.
  pose proof DFR as (DF1 & DF2 & DF3).
  assert (NE2 : forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ (d <= a < d + Z.of_nat jj + 1)).
  { intros a [Ha|Ha] Hd; [glia|]. apply (DF3 (a - d)); [glia|]. replace (d + (a - d)) with a by ring. exact Ha. }
  pose proof (sb_dup_rp L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 _ M1 CP NE2 SURVu LN) as RP2.
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & PR2 & _ & _ & _ & SC2).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  assert (RO2r : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RO2).
  destruct DBL as (bb1 & bb2 & EB2 & EB1).
  assert (NDB2 : List.NoDup (map fst (blocks L2 A2))) by (apply NoDup_ListNoDup; exact (NODUP _ _ _ _ M2)).
  assert (SURVb : forall q n, In (q, n) (blocks L1 A1) -> In (q, n) (blocks L2 A2)).
  { intros q n Hq. rewrite EB1 in Hq. rewrite EB2. apply in_app_or in Hq as [Hq|Hq]; apply in_or_app;
      [left; exact Hq | right; right; exact Hq]. }
  assert (DNEW : forall q n, In (q, n) (blocks L1 A1) -> q <> d).
  { intros q n Hq E. subst q. rewrite EB1 in Hq. rewrite EB2, map_app in NDB2. cbn [map fst] in NDB2.
    apply NoDup_remove_2 in NDB2. apply NDB2. rewrite <- map_app. change d with (fst (d, n)). apply in_map.
    exact Hq. }
  assert (BACKb : forall q n, In (q, n) (blocks L2 A2) -> q = d \/ In (q, n) (blocks L1 A1)).
  { intros q n Hq. rewrite EB2 in Hq. rewrite EB1. apply in_app_or in Hq as [Hq|[Hq|Hq]].
    - right. apply in_or_app. left. exact Hq.
    - left. injection Hq as <- _. reflexivity.
    - right. apply in_or_app. right. exact Hq. }
  assert (INd : In (d, Z.of_nat jj + 1) (blocks L2 A2)) by (rewrite EB2; apply in_or_app; right; left; reflexivity).
  assert (HI2 : In (re_hp e1, re_kh e1) (blocks L2 A2)) by exact (SURVb _ _ HI).
  assert (GI2 : In (G, SRC_TABLE) (blocks L2 A2)) by exact (SURVb _ _ GI1).
  pose proof (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M2 INd GI2 (fun E => DNEW _ _ GI1 (eq_sym E))) as DJd.
  pose proof (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M2 INd HI2 (fun E => DNEW _ _ HI (eq_sym E))) as DJdh.
  assert (RPc : relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 regs mem2 md2).
  { eapply (sb_comp Bm API).
    all: try first [exact AX | exact CTX | exact EU | exact BW | exact SEGS | exact RP1 | exact RP2].
    - intros a Ha. change (spZ regs) with S0 in Ha.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. glia.
    - intros a [X|X]; [left|right; exact X]. rewrite SPR1 in X. unfold STRNDUP_STACK, ALLOC_STACK in X.
      change (spZ regs) with S0.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. clear - X. lia.
    - intros a _ _ X. exact X.
    - intros p n _ _ _ _ X. exact X.
    - intros a _ _ _ X. exfalso. exact X.
    - intros p n i _ _ _ _ X. exfalso. exact X. }
  pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as MS2.
  match type of MS2 with msame ?PP _ _ => set (P2 := PP) in MS2 end.
  assert (P2S : forall a, S0 - 144 <= a < S0 -> P2 a).
  { intros a Ha. unfold P2. cbv beta. left.
    split; [left; glia|]. split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M1 Ho); glia|].
    split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M2 Ho); glia|].
    split; [unfold scratch_k; rewrite SPR1; unfold STRNDUP_STACK, ALLOC_STACK; glia | intros []]. }
  assert (P2I : forall a, img_plain Bm a -> P2 a).
  { intros a Hp. pose proof Hp as (Im & _ & _ & NE). pose proof (img_lo a Im) as IL. unfold P2. cbv beta. left.
    split; [right; exact Im|]. split; [exact (img_unowned _ _ _ _ a M1 Hp)|].
    split; [exact (img_unowned _ _ _ _ a M2 Hp)|].
    split; [unfold scratch_k; rewrite SPR1; unfold STRNDUP_STACK, ALLOC_STACK; glia | intros []]. }
  assert (P2B : forall q k a, In (q, k) (blocks L1 A1) -> q <= a < q + k -> P2 a).
  { intros q k0 a Hq Ha. unfold P2. cbv beta. right. exists q, k0.
    split; [exact Hq|]. split; [glia|]. split; [intros []|]. split; [glia | intros []]. }
  destruct (dr_cut m1 (SA + 40) (SA + 52) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]
              [CB 4 (re_pad2 e1)] EC3 ltac:(cbn [cells_size csize]; lia)) as [EH1 EH2].
  assert (EH1' : rw_cells rsegs mem2 (SA + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]).
  { pose proof EH1 as X. rewrite <- SEGS in X |- *. apply (rw_tr _ _ _ _ _ MS2 X). intros a Ha.
    cbn [cells_size csize] in Ha. apply (P2B G SRC_TABLE a GI1). unfold SRC_TABLE, SRC_ENTRY in *. glia. }
  assert (EHN : rw_cells rsegs (normalize rsegs mem2) (SA + 40)
                  [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]).
  { apply (rw_cells_normalize rsegs mem2 _ _ RO2r EH1'). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [glia|]. apply g_noimg. glia. }
  destruct (sb_c8w mem2 (re_hp e1 + 8 * re_nheld e1)) as (jw & SL2); [glia | glia | |].
  { intros i Hi. rewrite <- SEGS.
    replace (re_hp e1 + 8 * re_nheld e1 + i) with (re_hp e1 + (8 * re_nheld e1 + i)) by ring.
    apply (BW _ _ _ _ (re_hp e1) (re_kh e1) _ M2 HI2). glia. }
  assert (SLNm : rw_cells rsegs (normalize rsegs mem2) (re_hp e1 + 8 * re_nheld e1) [C8 jw]).
  { apply (rw_cells_normalize rsegs mem2 _ _ RO2r SL2). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [glia|].
    replace (re_hp e1 + 8 * re_nheld e1 + i) with (re_hp e1 + (8 * re_nheld e1 + i)) by ring. apply HF3. glia. }
  assert (V2 : getr regs2 2 = Z_to_bv 64 (S0 - 144))
    by (transitivity (getr R1 2); [exact (PR2 2 ltac:(unfold callee_saved; glia)) | exact G2]).
  assert (V3 : getr regs2 3 = getr regs 3)
    by (transitivity (getr R1 3); [exact (PR2 3 ltac:(unfold callee_saved; glia)) | exact G3]).
  assert (V4 : getr regs2 4 = getr regs 4)
    by (transitivity (getr R1 4); [exact (PR2 4 ltac:(unfold callee_saved; glia)) | exact G4]).
  assert (V8 : getr regs2 8 = Z_to_bv 64 SA)
    by (transitivity (getr R1 8); [exact (PR2 8 ltac:(unfold callee_saved; glia)) | exact G8]).
  assert (V9 : getr regs2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q))
    by (transitivity (getr R1 9); [exact (PR2 9 ltac:(unfold callee_saved; glia)) | exact G9]).
  assert (V22 : getr regs2 22 = Z_to_bv 64 384)
    by (transitivity (getr R1 22); [exact (PR2 22 ltac:(unfold callee_saved; glia)) | exact G22]).
  assert (V23 : getr regs2 23 = Z_to_bv 64 9)
    by (transitivity (getr R1 23); [exact (PR2 23 ltac:(unfold callee_saved; glia)) | exact G23]).
  assert (V25 : getr regs2 25 = Z_to_bv 64 DR_TU)
    by (transitivity (getr R1 25); [exact (PR2 25 ltac:(unfold callee_saved; glia)) | exact G25]).
  assert (V26 : getr regs2 26 = Z_to_bv 64 4)
    by (transitivity (getr R1 26); [exact (PR2 26 ltac:(unfold callee_saved; glia)) | exact G26]).
  assert (V27 : getr regs2 27 = Z_to_bv 64 (-1))
    by (transitivity (getr R1 27); [exact (PR2 27 ltac:(unfold callee_saved; glia)) | exact G27]).
  assert (G10p : getr regs2 10 = Z_to_bv 64 d) by exact G10'.
  match goal with |- context [YK11.mkst regs2 ?pc mem2 _] =>
    replace pc with (Z_to_bv 64 0x13d5c) by (first [exact G1 | symmetry; exact G1]) end.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, V8, G10p, V23, V26, V27. rewrite SEGS.
    eapply (evt_normalize rsegs); [exact dl_wx | exact RO2r |].
    eapply dr_gkeep; [exact EHN | reflexivity | exact SLNm | apply mem_inv_normalize | | glia | glia | glia |
                      clear - BAh; lia].
    destruct DJh as [DJ|DJ]; [left | right]; unfold SRC_TABLE, SRC_ENTRY in *; glia. }
  intros ms3 (can3 & (s3 & QP & REL3 & ROS3) & EQ3).
  destruct QP as [(C0 & _)|(_ & m3' & y11 & y12 & y13 & y14 & y15 & y16 & -> & MU3' & WM3' & _ & HC3' & HS3')];
    [exfalso; exact (DNZ C0)|].
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [ECAN3 HR3].
  rewrite ECAN3 in EQ3.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m3 := ms_mem can3) in *.
  assert (RTL3 : RTL R3) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3).
  pose proof RTL3 as (((P2r & P3r & P4r & P8r & P22r & P25r) & P23r & P26r) & P27r).
  assert (Y9 : getr R3 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X3.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y9, P27r. rewrite SEGS.
    eapply dr_next; clear - B0b BU EUd PQ; lia. }
  intros ms4 (can4 & -> & EQ4).
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  pose proof (sb_back mem2 m3' m3 _ RO2r HR3 ROS3 MU3' WM3') as (MU3 & WM3r & RO3r).
  pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 HC3') as HC3.
  pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 HS3') as HS3.
  assert (WM3 : wmono segs mem2 m3) by (rewrite SEGS; exact WM3r).
  pose proof (msame_trans _ _ _ _ _ MS2 (msame_munch _ _ _ MU3 WM3)) as MSa.
  match type of MSa with msame ?PP _ _ => set (Pa := PP) in MSa end.
  assert (PSk : forall a, S0 - 144 <= a < S0 -> Pa a).
  { intros a Ha. unfold Pa. cbv beta. split; [exact (P2S a Ha)|]. split; [glia|]. cbn [outside].
    split; [glia|]. split; [glia | exact I]. }
  assert (PIm : forall a, img_plain Bm a -> Pa a).
  { intros a Hp. unfold Pa. cbv beta. pose proof Hp as (Im & _). pose proof (img_lo a Im) as IL.
    split; [exact (P2I a Hp)|]. split; [glia|]. cbn [outside].
    split; [intros Rw; exact (g_noimg a ltac:(glia) Im)|]. split; [|exact I].
    intros Rw. apply (HF3 (a - re_hp e1)); [glia|]. replace (re_hp e1 + (a - re_hp e1)) with a by ring. exact Im. }
  assert (PBk : forall q k a, In (q, k) (blocks L1 A1) -> q <> G -> q <= a < q + k ->
              (q <> re_hp e1 \/ a < re_hp e1 + 8 * re_nheld e1) -> Pa a).
  { intros q k0 a Hq NG Ha Hh0. unfold Pa. cbv beta. split; [exact (P2B q k0 a Hq Ha)|].
    pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
    pose proof (blocks_disjoint Bm API _ _ _ _ q k0 G SRC_TABLE M1 Hq GI1 NG) as DJ.
    split; [glia|]. cbn [outside].
    split; [destruct DJ as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia|]. split; [|exact I].
    destruct Hh0 as [Hh0|Hh0]; [|glia].
    destruct (blocks_disjoint Bm API _ _ _ _ q k0 (re_hp e1) (re_kh e1) M1 Hq HI Hh0) as [DJ2|DJ2]; glia. }
  assert (PGk : forall a, SA <= a < SA + 56 -> ~ (SA + 48 <= a < SA + 52) -> Pa a).
  { intros a Ha Hn. unfold Pa. cbv beta.
    split; [apply (P2B G SRC_TABLE a GI1); unfold SRC_TABLE, SRC_ENTRY in *; glia|].
    split; [glia|]. cbn [outside]. split; [exact Hn|]. split; [|exact I].
    destruct DJh as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia. }
  assert (TPr : forall c cs, rw_cells rsegs m1 c cs -> (forall a, c <= a < c + Z.of_nat (cells_size cs) -> Pa a) ->
            rw_cells rsegs m3 c cs).
  { intros c0 cs HX HP. rewrite <- SEGS in HX |- *. exact (rw_tr _ _ _ c0 cs MSa HX HP). }
  assert (BD3 : bytes_at segs m3 d (buf ++ [Z_to_bv 8 0])).
  { assert (BD2 : bytes_at segs mem2 d (buf ++ [Z_to_bv 8 0])).
    { apply bytes_at_of_mbyte; [glia | rewrite length_app, LB; cbn [length]; glia |].
      intros i Hi. rewrite length_app, LB in Hi. cbn [length] in Hi. apply DCPY. glia. }
    eapply by_tr; [exact (msame_munch _ _ _ MU3 WM3) | exact BD2 |]. intros a Ha. cbv beta.
    rewrite length_app, LB in Ha. cbn [length] in Ha.
    split; [glia|]. cbn [outside].
    split; [destruct DJd as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia|].
    split; [destruct DJdh as [DJ|DJ]; glia | exact I]. }
  assert (KO : key_okw L2 A2 m3 (d, buf, [])).
  { unfold key_okw, key_addr, key_text. cbn [fst snd]. rewrite LB.
    split; [exact INd|]. split; [exact DFR|]. split; [exact BD3|]. split; [exact NZb|]. glia. }
  assert (SB : bytes_at segs m3 (re_hp e1 + 8 * re_nheld e1) (le8 (Z_to_bv 64 (key_addr (d, buf, []))))).
  { rewrite SEGS. destruct HS3 as [[_ BB3] _]. cbn [cells_bytes cbytes] in BB3. rewrite app_nil_r in BB3.
    exact BB3. }
  assert (EK2 : entry_okx L2 A2 m3 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1)
                  (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1 ++ [(d, buf, [])]) (re_U e1)
                  (re_junk e1))).
  { apply (sb_okx L1 A1 L2 A2 m1 m3 e1 Pa (d, buf, []) MSa EK1).
    - intros q n Hq _. exact (SURVb q n Hq).
    - intros q n a Hq Hb Ha Hh0. apply (PBk q n a Hq); [|exact Ha | exact Hh0].
      apply (dx_ng OUT1 _ q ND1). right. apply in_or_app. left. exact Hb.
    - right. intros E. apply (sb_hp_nd OUT1 e1 h1 ND1 HP0). right. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by glia. left. exact E.
    - intros X. apply (sb_hp_nd OUT1 e1 h1 ND1 HP0). right. right. apply in_or_app. right. apply in_or_app. left.
      exact X.
    - exact HP0.
    - exact KH.
    - exact NL.
    - exact SB.
    - exact KO.
    - intros X. apply in_map_iff in X as (k0 & Ek & Hk). destruct (proj1 (Forall_forall _ _) K14 k0 Hk) as (KK1 & _).
      exact (DNEW _ _ KK1 Ek).
    - intros X. apply (index_of_none _ _ IX). rewrite <- L4', <- EB. unfold keys_texts.
      rewrite <- (map_map key_text bzs). apply in_map. exact X. }
  assert (SAC2 : rw_cells segs m3 SA [CB 56%nat (entry_bytes (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1)
                   (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1)
                   (re_keys e1 ++ [(d, buf, [])]) (re_U e1) (re_junk e1)))]).
  { assert (RN : re_nheld (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1)
                   (re_hp e1) (re_kh e1) (re_pad2 e1) (re_keys e1 ++ [(d, buf, [])]) (re_U e1) (re_junk e1)) =
                 re_nheld e1 + 1) by (unfold re_nheld; cbn [re_keys]; rewrite length_app; cbn [length]; lia).
    rewrite SEGS. apply ent_join; [exact K3 | exact K4 | | |].
    - apply TPr; [exact EC1|]. intros a Ha. cbn [cells_size csize] in Ha. apply PGk; glia.
    - apply TPr; [exact EC2|]. intros a Ha. cbn [cells_size csize] in Ha. apply PGk; glia.
    - rewrite RN.
      apply (dr_join m3 (SA + 40) (SA + 52) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1 + 1))]
               [CB 4 (re_pad2 e1)]); [exact HC3 | | cbn [cells_size csize]; lia].
      apply TPr; [exact EH2|]. intros a Ha. cbn [cells_size csize] in Ha. apply PGk; glia. }
  assert (LIVEQ : forall q, In q (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) ->
            q = 0 \/ exists k, In (q, k) (blocks L1 A1)).
  { intros q Hq. destruct Hq as [Hq|[Hq|Hq]].
    - right. exists SRC_TABLE. rewrite <- Hq. exact GI1.
    - subst q. destruct OU1 as (OF & OT). destruct (Bool.bool_dec LIVE true) as [LV|LV].
      + destruct (OT LV) as (_ & [(_ & O0 & _)|(_ & _ & OI & _)]); [left; exact O0 | right; eexists; exact OI].
      + apply Bool.not_true_is_false in LV. destruct (OF LV) as (_ & EO & _ & OB).
        destruct OUTD as [(C0 & O0 & _)|(Cp0 & _)]; [left; rewrite EO; exact O0|].
        right. exists CAP. rewrite EO. exact (proj1 (OB Cp0)).
    - apply in_app_or in Hq as [Hq|Hq].
      + right. exact (sb_eb_live L1 A1 m1 e1 q EK1 Hq).
      + right. exact (hb_live L1 A1 m1 HA h1 q SR1 Hq). }
  assert (NI : ~ In d (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1)).
  { intros Hin. destruct (LIVEQ d Hin) as [D0|(k0 & Hk)]; [exact (DNZ D0) | exact (DNEW _ _ Hk eq_refl)]. }
  assert (KT : keys_texts (re_keys e1 ++ [(d, buf, [])]) = seen_arr (dlH s P) (dline s P Q)).
  { rewrite SAR2, <- L4'. unfold keys_texts. rewrite map_app, <- EB. reflexivity. }
  assert (LO : Z.of_nat (length O) = NO)
    by (destruct OUTD as [(_ & _ & N0 & EO)|(_ & _ & _ & _ & _ & LO & _)]; [rewrite EO; cbn; clear - N0; lia | exact LO]).
  apply SR_ret.
  apply (dln_of s P Q R4 L2 A2 m3 md2
    (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1)
        (re_pad2 e1) (re_keys e1 ++ [(d, buf, [])]) (re_U e1) (re_junk e1)) h1 OUT1 junk1 LB1 D).
  { unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X4. }
  { rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity. simp_regs. cbn [re_buf]. f_equal. clear; lia. }
  unfold DLNB. split; [exact DFs|]. unfold LCORE.
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPc MU3 WM3 GEI).
    intros a Ha.
    destruct (dx_odec [(SA + 48, SA + 52); (re_hp e1 + 8 * re_nheld e1, re_hp e1 + 8 * re_nheld e1 + 8)] a)
      as [Ox|(lo & hi & Iw & Rw)]; [left; exact Ox|right].
    destruct Iw as [Iw|[Iw|[]]]; injection Iw as <- <-.
    - right. right. right. split; [exact (g_noimg a ltac:(glia))|].
      split; [exists G, SRC_TABLE; split; [exact GI2 | unfold SRC_TABLE, SRC_ENTRY in *; glia]|].
      intros p n i _ _ _ _ NE E. apply NE. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. glia.
    - right. right. right. split.
      { intros Im. apply (HF3 (a - re_hp e1)); [glia|]. replace (re_hp e1 + (a - re_hp e1)) with a by ring.
        exact Im. }
      split; [exists (re_hp e1), (re_kh e1); split; [exact HI2 | glia]|].
      intros p n i Hp Hp2 NF Hi _ E.
      assert (INq : In (ptr_addr L p, n) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
      destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n BK1 OU1 INq ltac:(glia) NF) as (U1 & _).
      assert (NEh : ptr_addr L p <> re_hp e1).
      { intros Eq. apply U1. rewrite Eq. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) HP0).
        apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
      pose proof RPc as (_ & _ & _ & _ & _ & ADc & _).
      rewrite <- (ADc p n Hp Hp2 NF) in E, NEh.
      assert (INq2 : In (ptr_addr L2 p, n) (blocks L2 A2))
        by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp2]).
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M2 INq2 HI2 NEh) as [DJ|DJ]; glia. }
  split; [exact INI2|].
  split.
  { exact (H2_sab_mtr s P Q jj STRNDUP_STACK L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 (sv_oc s P Q) e1 h1 OUT1 d buf tp qd
             ad W1 RP2 (NODUP _ _ _ _ M2) INd LB RC1 RF1 RS2). }
  split; [rewrite SEGS; exact RO3r|].
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MSa | exact FRc |].
    intros a Ha. cbn [cells_size csize app dr_saved] in Ha. exact (PSk a ltac:(glia)). }
  split; [exact SAC2|].
  split; [exact EK2|].
  split.
  { eapply src_at_tr0; [exact MSa | exact SR1 | | |].
    - intros a Ha. apply PIm, GRP. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia.
    - intros q k0 Hq _. exact (SURVb q k0 Hq).
    - intros q k0 a Hq Hb Ha. exact (PBk q k0 a Hq (NGH q Hb) Ha (or_introl (NHH q Hb))). }
  split.
  { eapply others_at_tr; [exact MSa | exact OT1 |]. intros i a Hi _ Ha. apply PIm, GRP.
    unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia. }
  split; [exact SM1|].
  split.
  { apply (sb_link s false (dlH s P) _ _ _ _ e1); [exact LK1 | reflexivity | reflexivity | reflexivity | exact KT |].
    reflexivity. }
  split; [eapply sb_hist; [exact HI1 | apply app_assoc]|].
  split.
  { rewrite (sb_pst s false (dlH s P)), SAR2, length_app. cbn [length]. glia. }
  split; [exact RST1|].
  split.
  { exact (sb_blk L1 A1 L2 A2 e1 h1 OUT1 d (d, buf, []) BK1 eq_refl SURVb BACKb NI
             (fun n Hn => DNEW d n Hn eq_refl)). }
  split.
  { destruct GL1 as (C1 & C2 & C3 & CC4 & _).
    split; [eapply rw_tr; [exact MSa | exact C1 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GCP; unfold G_CLIENT in *; glia|].
    split; [eapply rw_tr; [exact MSa | exact C2 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    split; [eapply rw_tr; [exact MSa | exact C3 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    split; [eapply rw_tr; [exact MSa | exact CC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    destruct (sb_c4 m3 ERR) as (v & HV); [glia | glia | |exists v; rewrite SEGS; exact HV].
    intros i Hi. rewrite <- SEGS. apply WM3, SC2. right. glia. }
  apply (sb_out s false (dlH s P)).
  destruct OU1 as (OF & OT). split.
  - intros LV. destruct (OF LV) as (C & EO & EC' & OB).
    split; [eapply rw_tr; [exact MSa | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    split; [exact EO|]. split; [exact EC'|]. intros Cp0. destruct (OB Cp0) as (OI & OBy).
    split; [exact (SURVb _ _ OI)|].
    eapply by_tr; [exact MSa | exact OBy |]. intros a Ha.
    apply (PBk OUT CAP a OI); [apply (dx_ng OUT1 _ OUT ND1); left; symmetry; exact EO | |
                               left; rewrite <- EO; exact NHO].
    destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & _ & LJ)]; [glia|]. rewrite length_app in Ha. glia.
  - intros LV. destruct (OT LV) as (C & OB).
    split; [eapply rw_tr; [exact MSa | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    destruct OB as [Z0|(Cp0 & NLo & OI & OFr & OBy & LJ)]; [left; exact Z0|right].
    split; [exact Cp0|]. split; [exact NLo|]. split; [exact (SURVb _ _ OI)|]. split; [exact OFr|].
    split; [|exact LJ].
    eapply by_tr; [exact MSa | exact OBy |]. intros a Ha.
    apply (PBk OUT1 _ a OI); [apply (dx_ng OUT1 _ OUT1 ND1); left; reflexivity | | left; exact NHO].
    assert (LL : Z.of_nat (length LB1) = Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P ++ [dline s P Q]))))
      by (rewrite <- H7h; unfold bzs; rewrite length_map; reflexivity).
    rewrite !length_app in Ha. glia.
Qed.

Lemma sd_ret_ok : YK0s.ret_ok (Z_to_bv 64 0x13dc8).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma sd_pre_free : forall L1 A1 m1 md1 R2,
  relay_post Bm API DRAIN_K EE FF L A regs mem md L1 A1 regs m1 md1 -> st_init_done A1 = true ->
  getr R2 2 = Z_to_bv 64 (S0 - 144) -> getr R2 4 = getr regs 4 -> YK0s.ret_ok (getr R2 1) ->
  call_pre Bm MR L1 A1 R2 m1 md1.
Proof using EHI GEI HG HJ O PRE SEGS junk.
  intros L1 A1 m1 md1 R2 (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1) IN1 G2 G4 HRA.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _ & HTP & _).
  pose proof gfacts as (_ & _ & F3 & _).
  assert (SPR : spZ R2 = S0 - 144).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite G2. apply unsigned_lit. clear - HCEIL H63 F3. lia. }
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  split; [rewrite SPR; clear - HAL; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold ALLOC_STACK; clear - HCEIL; lia|].
  split; [rewrite SPR; clear - H63 HCEIL F3; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold ALLOC_STACK in Ha. apply SC1. left.
    change (spZ regs) with S0. unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK.
    clear - Ha. lia. }
  split; [exact (eq_trans G4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite IN1 in X. discriminate.
Qed.

Lemma sd_free_rp : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n,
  WF A1 -> In (p, n) (user_blocks A1) -> 0 < n -> MR L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  relay_post Bm API ALLOC_STACK (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) (fun q => q = ptr_addr L1 p)
    L1 A1 R1 m1 md1 L2 A2 R2 m2 md2.
Proof using AX CTX HG HJ O h junk.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n HW Hp Hn HM CP SURV LN.
  destruct CP as (M' & W' & B' & LL & AD & RP & MD & FR & BY & SC).
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LL|]. split; [exact LN|].
  split; [intros q k H1 H2 _; exact (AD q k H1 H2)|].
  split; [intros q k H1 _ NF; apply SURV; [exact H1|]; intros ->; exact (NF eq_refl)|].
  split.
  { intros q H1.
    assert (Qn : q <> p).
    { intros ->. pose proof (sb_nodup_fst _ p 0 n (YO10.user_block_ptrs_NoDup A1 HW) H1 Hp). lia. }
    pose proof (SURV q 0 H1 Qn) as H2. split; [exact H2 | exact (AD q 0 H1 H2)]. }
  split; [intros a Hi Ho; exact (sb_owned_img Bm API AX CTX L1 A1 m1 md1 L2 A2 m2 md2 a HM M' Hi Ho)|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS NE; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | exact NE]|].
  split; [intros q k i H1 H2 _ Hi _; exact (BY q k i H1 H2 Hi)|].
  exact SC.
Qed.

Lemma sd_c8 : forall m a v, bytes_at rsegs m a (le8 v) ->
  (forall i, 0 <= i < 8 -> writable_at rsegs m (a + i)) -> rw_cells rsegs m a [C8 v].
Proof using Bm G HJ O h junk regs.
  intros m a v B W. pose proof (bytes_at_bound rsegs m a _ B) as BB. rewrite length_le8 in BB.
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (W i Hi).
Qed.

Lemma sd_nd_l : forall (l1 l2 : list Z) q, List.NoDup (l1 ++ l2) -> In q l2 -> ~ In q l1.
Proof using.
  induction l1 as [|y l1 IH]; intros l2 q ND H2 H1; [destruct H1|].
  cbn [app] in ND. apply List.NoDup_cons_iff in ND as [Ny ND].
  destruct H1 as [->|H1]; [apply Ny; apply in_or_app; right; exact H2 | exact (IH l2 q ND H2 H1)].
Qed.

Lemma sd_nd_r : forall (l1 l2 : list Z) q, List.NoDup (l1 ++ l2) -> In q l1 -> ~ In q l2.
Proof using. intros l1 l2 q ND H1 H2. exact (sd_nd_l l1 l2 q ND H2 H1). Qed.

Lemma sd_nk : forall OUT1 e1 h1 q, NoDup (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1) ->
  In q (map key_addr (re_keys e1)) ->
  q <> G /\ q <> OUT1 /\ ~ In q (hs_blocks h1) /\ ~ In q (if re_cap e1 =? 0 then [] else [re_buf e1]) /\
  ~ In q (if re_hp e1 =? 0 then [] else [re_hp e1]).
Proof using.
  intros OUT1 e1 h1 q ND Hq. apply NoDup_ListNoDup in ND.
  assert (IE : In q (entry_blocks e1)).
  { unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. exact Hq. }
  apply List.NoDup_cons_iff in ND as [NG ND]. apply List.NoDup_cons_iff in ND as [NO ND].
  split; [intros E; apply NG; right; apply in_or_app; left; rewrite <- E; exact IE|].
  split; [intros E; apply NO; apply in_or_app; left; rewrite <- E; exact IE|].
  split; [exact (sd_nd_r _ _ q ND IE)|].
  apply List.NoDup_app_remove_r in ND. unfold entry_blocks in ND.
  split.
  - apply (sd_nd_l _ _ q ND). apply in_or_app. right. exact Hq.
  - apply List.NoDup_app_remove_l in ND. exact (sd_nd_l _ _ q ND Hq).
Qed.

Lemma sd_swap_map : forall {X Y : Type} (f : X -> Y) (dx : X) a x b,
  map f (swap_remove dx (length a) (a ++ x :: b)) = swap_remove (f dx) (length a) (map f (a ++ x :: b)).
Proof using.
  intros X Y f dx a x b. induction b as [|z b' _] using List.rev_ind.
  - rewrite swap_remove_last, map_app. cbn [map].
    replace (length a) with (length (map f a)) by apply length_map. rewrite swap_remove_last. reflexivity.
  - rewrite swap_remove_mid, !map_app. cbn [map]. rewrite map_app. cbn [map].
    replace (length a) with (length (map f a)) by apply length_map. rewrite swap_remove_mid. reflexivity.
Qed.

Lemma sd_ptrs : forall Pa m m' hp (ka kb : list (Z * list byte * list byte)) k d,
  msame Pa m m' -> bytes_at segs m hp (key_ptrs (ka ++ k :: kb)) ->
  (forall a, hp <= a < hp + 8 * Z.of_nat (length kb) + 8 * Z.of_nat (length ka) ->
     ~ (hp + 8 * Z.of_nat (length ka) <= a < hp + 8 * Z.of_nat (length ka) + 8) -> Pa a) ->
  bytes_at segs m' (hp + 8 * Z.of_nat (length ka)) (le8 (Z_to_bv 64 (key_addr (last (ka ++ k :: kb) d)))) ->
  bytes_at segs m' hp (key_ptrs (swap_remove d (length ka) (ka ++ k :: kb))).
Proof using HG HJ O h junk.
  intros Pa m m' hp ka kb k d MS B0 HP SL.
  rewrite CF.gestures_end_b.key_ptrs_app in B0. apply bytes_at_app in B0 as [BA BR].
  rewrite CF.gestures_end_b.key_ptrs_cons in BR. apply bytes_at_app in BR as [_ BK].
  rewrite CF.gestures_end_b.key_ptrs_length, length_le8 in BK.
  assert (BA' : bytes_at segs m' hp (key_ptrs ka)).
  { eapply by_tr; [exact MS | exact BA |]. intros a Ha. rewrite CF.gestures_end_b.key_ptrs_length in Ha.
    apply HP; lia. }
  revert BK HP SL. induction kb as [|z kb' _] using List.rev_ind; intros BK HP SL.
  - rewrite swap_remove_last. exact BA'.
  - rewrite swap_remove_mid.
    replace (ka ++ k :: kb' ++ [z]) with ((ka ++ k :: kb') ++ [z]) in SL by (rewrite <- app_assoc; reflexivity).
    rewrite last_last in SL.
    rewrite CF.gestures_end_b.key_ptrs_app, CF.gestures_end_b.key_ptrs_cons.
    apply bytes_at_app. split; [exact BA'|].
    apply bytes_at_app. split.
    + rewrite CF.gestures_end_b.key_ptrs_length.
      replace (hp + Z.of_nat (8 * length ka)) with (hp + 8 * Z.of_nat (length ka)) by lia. exact SL.
    + rewrite CF.gestures_end_b.key_ptrs_app in BK. apply bytes_at_app in BK as [BK _].
      rewrite CF.gestures_end_b.key_ptrs_length, length_le8.
      eapply by_tr; [exact MS | exact BK |]. intros a Ha. rewrite CF.gestures_end_b.key_ptrs_length in Ha.
      rewrite length_app in HP. cbn [length] in HP. apply HP; lia.
Qed.

Lemma sd_okx : forall L1 A1 L2 A2 m1 m2 e1 Pa (ka kb : list (Z * list byte * list byte)) k d,
  msame Pa m1 m2 -> entry_okx L1 A1 m1 e1 -> re_keys e1 = ka ++ k :: kb ->
  (forall q n, In (q, n) (blocks L1 A1) -> In q (entry_blocks e1) -> q <> key_addr k -> In (q, n) (blocks L2 A2)) ->
  (forall q n a, In (q, n) (blocks L1 A1) -> In q (entry_blocks e1) -> q <> key_addr k -> q <= a < q + n ->
     (q <> re_hp e1 \/ ~ (re_hp e1 + 8 * Z.of_nat (length ka) <= a < re_hp e1 + 8 * Z.of_nat (length ka) + 8)) ->
     Pa a) ->
  (re_cap e1 = 0 \/ re_buf e1 <> re_hp e1) -> ~ In (re_hp e1) (map key_addr (re_keys e1)) ->
  (re_cap e1 = 0 \/ re_buf e1 <> key_addr k) -> re_hp e1 <> 0 ->
  bytes_at segs m2 (re_hp e1 + 8 * Z.of_nat (length ka)) (le8 (Z_to_bv 64 (key_addr (last (re_keys e1) d)))) ->
  entry_okx L2 A2 m2 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1)
    (re_hp e1) (re_kh e1) (re_pad2 e1) (swap_remove d (length ka) (re_keys e1)) (re_U e1) (re_junk e1)).
Proof using HG HJ O h junk.
  intros L1 A1 L2 A2 m1 m2 e1 Pa ka kb k d MS (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14)
    EK SV HP NBH NKH NBK H0 SL.
  pose proof (swap_remove_perm d ka k kb) as PM. rewrite <- EK in PM.
  assert (IKS : forall k0, In k0 (swap_remove d (length ka) (re_keys e1)) -> In k0 (re_keys e1)).
  { intros k0 Hk. apply (Permutation.Permutation_in _ (Permutation.Permutation_sym PM)). right. exact Hk. }
  assert (NDA : List.NoDup (key_addr k :: map key_addr (swap_remove d (length ka) (re_keys e1)))).
  { apply (Permutation.Permutation_NoDup (Permutation.Permutation_map key_addr PM)). apply NoDup_ListNoDup.
    exact E12. }
  assert (NDT : List.NoDup (key_text k :: map key_text (swap_remove d (length ka) (re_keys e1)))).
  { apply (Permutation.Permutation_NoDup (Permutation.Permutation_map key_text PM)). apply NoDup_ListNoDup.
    exact E13. }
  apply List.NoDup_cons_iff in NDA as [NIA NDA]. apply List.NoDup_cons_iff in NDT as [_ NDT].
  assert (LKS : length (re_keys e1) = S (length (swap_remove d (length ka) (re_keys e1))))
    by exact (Permutation.Permutation_length PM).
  assert (IB : re_cap e1 <> 0 -> In (re_buf e1) (entry_blocks e1)).
  { intros C. unfold entry_blocks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ 0) C). left. reflexivity. }
  assert (IH : In (re_hp e1) (entry_blocks e1)).
  { unfold entry_blocks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ 0) H0). left. reflexivity. }
  assert (IK : forall k0, In k0 (re_keys e1) -> In (key_addr k0) (entry_blocks e1)).
  { intros k0 Hk. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
  assert (HNK : re_hp e1 <> key_addr k).
  { intros E. apply NKH. rewrite E. apply in_map. rewrite EK. apply in_or_app. right. left. reflexivity. }
  destruct E11 as [(Z0 & _)|(HI & HF & H8 & H8' & HB)]; [exfalso; exact (H0 Z0)|].
  match goal with |- entry_okx _ _ _ ?e2 => assert (RN : re_nheld e2 = re_nheld e1 - 1) end.
  { unfold re_nheld. cbn [re_keys]. rewrite LKS. lia. }
  unfold entry_okx. rewrite RN.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys].
  do 8 (split; [assumption|]).
  split.
  { destruct E9 as [Z0|(C0 & BI & BF & BJ & BC)]; [left; exact Z0 | right].
    assert (CN : re_cap e1 <> 0) by lia.
    assert (NB : re_buf e1 <> key_addr k) by (destruct NBK as [C|C]; [lia | exact C]).
    split; [exact C0|]. split; [exact (SV _ _ BI (IB CN) NB)|]. split; [exact BF|]. split; [exact BJ|].
    eapply rw_tr; [exact MS | exact BC |]. intros a Ha. cbn [cells_size csize] in Ha.
    apply (HP _ _ a BI (IB CN) NB); [lia|]. left. destruct NBH as [C|C]; [lia | exact C]. }
  split; [lia|].
  split.
  { right. split; [exact (SV _ _ HI IH HNK)|]. split; [exact HF|]. split; [lia|]. split; [exact H8'|].
    rewrite EK. rewrite EK in SL.
    apply (sd_ptrs Pa m1 m2 (re_hp e1) ka kb k d MS); [rewrite <- EK; exact HB | | exact SL].
    intros a Ha Hn. apply (HP _ _ a HI IH HNK); [|right; exact Hn].
    unfold re_nheld in H8. rewrite EK, length_app in H8. cbn [length] in H8. lia. }
  split; [apply NoDup_ListNoDup; exact NDA|].
  split; [apply NoDup_ListNoDup; exact NDT|].
  apply Forall_forall. intros k0 Hk0. pose proof (IKS k0 Hk0) as Hk.
  assert (NK0 : key_addr k0 <> key_addr k) by (intros E; apply NIA; rewrite <- E; apply in_map; exact Hk0).
  destruct (proj1 (Forall_forall _ _) E14 k0 Hk) as (KK1 & KK2 & KK3 & KK4 & KK5).
  split; [exact (SV _ _ KK1 (IK k0 Hk) NK0)|]. split; [exact KK2|]. split; [|split; [exact KK4 | exact KK5]].
  eapply by_tr; [exact MS | exact KK3 |]. intros a Ha. apply (HP _ _ a KK1 (IK k0 Hk) NK0).
  - rewrite length_app in Ha. cbn [length] in Ha. lia.
  - left. intros E. apply NKH. rewrite <- E. apply in_map. exact Hk.
Qed.

Lemma sd_blk : forall L1 A1 L2 A2 e1 e2 h1 OUT1 dq nk,
  DBLK L1 A1 e1 h1 OUT1 ->
  (forall q n, In (q, n) (blocks L1 A1) -> q <> dq -> In (q, n) (blocks L2 A2)) ->
  (forall q n, In (q, n) (blocks L2 A2) -> In (q, n) (blocks L1 A1) /\ q <> dq) ->
  In (dq, nk) (blocks L1 A1) -> 0 < nk -> List.NoDup (map fst (blocks L1 A1)) ->
  Permutation.Permutation (entry_blocks e1) (dq :: entry_blocks e2) ->
  DBLK L2 A2 e2 h1 OUT1.
Proof using HG HJ O junk.
  intros L1 A1 L2 A2 e1 e2 h1 OUT1 dq nk (ND1 & GI1 & SV1 & CL1 & FB1) SURV BACK INk Hnk NDB PM.
  assert (IDQ : In dq (entry_blocks e1)).
  { apply (Permutation.Permutation_in _ (Permutation.Permutation_sym PM)). left. reflexivity. }
  assert (I21 : forall q, In q (entry_blocks e2) -> In q (entry_blocks e1)).
  { intros q Hq. apply (Permutation.Permutation_in _ (Permutation.Permutation_sym PM)). right. exact Hq. }
  assert (I12 : forall q, In q (entry_blocks e1) -> q <> dq -> In q (entry_blocks e2)).
  { intros q Hq Hn. apply (Permutation.Permutation_in _ PM) in Hq.
    destruct Hq as [E|Hq]; [exfalso; exact (Hn (eq_sym E)) | exact Hq]. }
  assert (DQ0 : forall m, In (dq, m) (blocks L1 A1) -> 0 < m).
  { intros m Hm. pose proof (sb_nodup_fst _ dq m nk NDB Hm INk) as E. lia. }
  assert (NGD : G <> dq).
  { intros E. pose proof ND1 as X. apply NoDup_ListNoDup in X. apply List.NoDup_cons_iff in X as [NG _].
    apply NG. right. apply in_or_app. left. rewrite E. exact IDQ. }
  unfold DBLK.
  split.
  { apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND1.
    assert (PM2 : Permutation.Permutation (G :: OUT1 :: entry_blocks e1 ++ hs_blocks h1)
                    (dq :: G :: OUT1 :: entry_blocks e2 ++ hs_blocks h1)).
    { eapply Permutation.perm_trans.
      - apply Permutation.perm_skip, Permutation.perm_skip, Permutation.Permutation_app_tail, PM.
      - change (Permutation.Permutation ([G; OUT1] ++ dq :: (entry_blocks e2 ++ hs_blocks h1))
                  (dq :: [G; OUT1] ++ (entry_blocks e2 ++ hs_blocks h1))).
        apply Permutation.Permutation_sym, Permutation.Permutation_middle. }
    pose proof (Permutation.Permutation_NoDup PM2 ND1) as X. apply List.NoDup_cons_iff in X as [_ X]. exact X. }
  split; [exact (SURV _ _ GI1 NGD)|].
  split.
  { intros q m Hq HO HE. pose proof (SV1 q m Hq HO HE) as Hq1. apply (SURV _ _ Hq1). intros ->.
    destruct (FB1 dq m Hq (DQ0 m Hq1) HO HE) as (_ & U1 & _). exact (U1 IDQ). }
  split.
  { intros q m Hq. destruct (BACK q m Hq) as (Hq1 & Hn).
    destruct (CL1 q m Hq1) as [X|[X|X]]; [left; exact X | right; left | right; right; exact X].
    apply in_app_or in X as [X|X]; apply in_or_app; [left; exact (I12 q X Hn) | right; exact X]. }
  intros q m Hq Hm HO HE. destruct (FB1 q m Hq Hm HO HE) as (U0 & U1 & U2).
  split; [exact U0|]. split; [intros X; exact (U1 (I21 q X)) | exact U2].
Qed.

Lemma seen_drop : forall s P Q c, DGF s P Q c -> SR segs c (DLN s (S Q)).
Proof using All.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & jj & n & -> & RT1 & G1 & G9 & G18 &
    G10 & G19 & G23 & NL & GS & JJ & IX & DFs & LC1).
  pose proof LC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & NK1 & RST1 & BK1 & GL1
    & OU1).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RP1 as (M1 & W1 & B1 & _).
  pose proof RT1 as (G2 & G3 & G4 & G8 & G22 & G25).
  pose proof pre_facts as (_ & _ & _ & _ & _ & HCEIL & H63 & _ & _ & _).
  pose proof err_hi as EH. unfold G_LOCK_HI in F9.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof BK1 as (ND1 & GI1 & SV1 & CL1 & FB1).
  pose proof HI1 as (_ & _ & _ & _ & _ & H6h & H7h & _).
  pose proof DFs as (DBd & PQ & HQz & HNZ & HSKp & HLL).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (_ & _ & UEUd & _ & UB0 & UBU & _).
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
  assert (NHD : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
  assert (L4' : keys_texts (re_keys e1) = dlH s P) by exact L4c.
  remember (nth n (re_keys e1) (0, [], [])) as k eqn:Ek.
  assert (NE : nth_error (re_keys e1) n = Some k) by (rewrite Ek; apply nth_error_nth'; exact NL).
  destruct (nth_error_split _ _ _ NE) as (ka & kb & Eks & Lka). subst n.
  assert (IKk : In k (re_keys e1)) by (rewrite Eks; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) K14 k IKk) as (KK1 & KF & KB & KZ & KL).
  pose proof (index_of_some _ _ _ IX) as (xa & xb & EH0 & Lxa).
  assert (LX : length (firstn jj (dline s P Q)) = jj).
  { rewrite firstn_length_le; [reflexivity|]. rewrite (dline_len s P Q PQ). glia. }
  assert (EXk : bzs (key_text k) = firstn jj (dline s P Q)).
  { assert (X1 : nth (length ka) (dlH s P) [] = firstn jj (dline s P Q)).
    { rewrite EH0, <- Lxa, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
    rewrite <- L4', Eks in X1. unfold keys_texts in X1. rewrite map_app in X1. cbn [map] in X1.
    rewrite app_nth2 in X1 by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag in X1. exact X1. }
  assert (LK : length (key_text k) = jj).
  { rewrite <- LX, <- EXk. unfold bzs. rewrite length_map. reflexivity. }
  rewrite LK in KK1, KF.
  assert (JJz : 13 < Z.of_nat jj).
  { assert (X : (13 < jj)%nat) by glia. apply Nat2Z.inj_lt in X. change (Z.of_nat 13) with 13 in X. exact X. }
  assert (ST : forall jb ha ks, seen_tr (dlH s P) (dlka s P) (dline s P Q) jb ha ks =
            ([RFree (Z.of_nat jj + 1) (nth (length ka) ks adr0)], dlka s P, (ha, swap_remove adr0 (length ka) ks))).
  { intros jb ha ks. unfold seen_tr. rewrite GS. cbv beta iota. rewrite IX. cbv beta iota zeta. rewrite LX.
    reflexivity. }
  assert (EK : seen_ka (dlH s P) (dlka s P) (dline s P Q) = dlka s P) by (unfold seen_ka; rewrite ST; reflexivity).
  assert (ER : forall jb o ha ks,
            srest (dlH s P) (dlka s P) (dline s P Q) (sv_no s P Q) (sv_oc s P Q) (drlq s (S Q)) jb o ha ks =
            (RFree (Z.of_nat jj + 1) (nth (length ka) ks adr0) ::
               fst (sv_rest s P Q jb o ha (swap_remove adr0 (length ka) ks)),
             snd (sv_rest s P Q jb o ha (swap_remove adr0 (length ka) ks)))).
  { intros jb o ha ks. unfold srest, sv_rest. cbv beta. rewrite ST. cbn [fst snd app]. rewrite sdp_nr0.
    reflexivity. }
  assert (SAR2 : seen_arr (dlH s P) (dline s P Q) = swap_remove [] (length ka) (dlH s P)).
  { unfold seen_arr. rewrite GS. cbv beta iota. rewrite IX. reflexivity. }
  assert (LSW : (length (swap_remove [] (length ka) (dlH s P)) < length (dlH s P))%nat).
  { rewrite EH0, <- Lxa, length_swap_remove, length_app. cbn [length]. lia. }
  assert (KT : keys_texts (swap_remove (0, [], []) (length ka) (re_keys e1)) = seen_arr (dlH s P) (dline s P Q)).
  { rewrite SAR2, <- L4', Eks. unfold keys_texts. rewrite sd_swap_map. reflexivity. }
  destruct TR1 as (tp & qd & fa & RC1 & RF1).
  pose proof RC1 as (LQ & WF1 & DOK & RTO & (LV1 & EL1 & SL1) & DKH1).
  pose proof EL1 as (EL1b & EL1h & EL1k).
  rewrite Eks in EL1k.
  destruct (sdp_f2s _ ka k kb (da_keys fa) EL1k) as (ya & y & yb & Ey & Lya & FA & Ry & FB).
  assert (NY : nth (length ka) (da_keys fa) adr0 = y) by (rewrite Ey, <- Lya; apply nth_middle).
  pose proof DOK as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  assert (PY : p3a_ok y (nretF tp)).
  { rewrite Ey in O4. apply (proj1 (Forall_forall _ _) O4). apply in_or_app. right. left. reflexivity. }
  rewrite ER in RF1. cbn [fst snd] in RF1. rewrite NY, sdp_nrc in RF1.
  pose proof Ry as Ry'. cbv beta in Ry'. unfold live_at in Ry'. destruct Ry' as (Hpk & Ep). rewrite LK in Hpk.
  pose proof (blk_rng _ _ _ _ _ _ M1 KK1) as BRk.
  pose proof KF as (KF1 & KF2 & KF3).
  destruct K11 as [(H0 & K0)|(HI & HF & H8 & H8' & HB)].
  { exfalso. rewrite K0 in Eks. exact (app_cons_not_nil _ _ _ Eks). }
  pose proof (blk_rng _ _ _ _ _ _ M1 HI) as BRh.
  pose proof (blk_align _ _ _ _ _ _ M1 HI) as AL16.
  pose proof HF as (HF1 & HF2 & HF3).
  assert (HP0 : re_hp e1 <> 0) by glia.
  assert (IKA : In (key_addr k) (map key_addr (re_keys e1))) by (apply in_map; exact IKk).
  destruct (sd_nk OUT1 e1 h1 _ ND1 IKA) as (NKG & NKO & NKH & NKB & NKP).
  assert (NHK : re_hp e1 <> key_addr k).
  { intros E. apply NKP. rewrite (proj2 (Z.eqb_neq _ 0) HP0). left. exact E. }
  assert (NGK : G <> key_addr k) by (intros E; exact (NKG (eq_sym E))).
  assert (NHG : re_hp e1 <> G) by (intros E; apply (sb_hp_nd OUT1 e1 h1 ND1 HP0); left; symmetry; exact E).
  pose proof (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 HI GI1 NHG) as DJh.
  assert (NHO : OUT1 <> re_hp e1) by (intros E; apply (sb_hp_nd OUT1 e1 h1 ND1 HP0); right; left; exact E).
  assert (NHH : forall q, In q (hs_blocks h1) -> q <> re_hp e1).
  { intros q Hb E. apply (sb_hp_nd OUT1 e1 h1 ND1 HP0). rewrite <- E. right. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (NGH : forall q, In q (hs_blocks h1) -> q <> G)
    by (intros q Hb; apply (dx_ng OUT1 _ q ND1); right; apply in_or_app; right; exact Hb).
  assert (NKHs : forall q, In q (hs_blocks h1) -> q <> key_addr k) by (intros q Hb E; apply NKH; rewrite <- E; exact Hb).
  assert (NE0 : re_keys e1 <> []).
  { intros E. rewrite Eks in E. symmetry in E. exact (app_cons_not_nil _ _ _ E). }
  destruct (@exists_last _ (re_keys e1) NE0) as (ks0 & kl & El).
  assert (IKl : In kl (re_keys e1)) by (rewrite El; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) K14 kl IKl) as (KL1 & _).
  pose proof (blk_rng _ _ _ _ _ _ M1 KL1) as BRl.
  assert (LPB : bytes_at segs m1 (re_hp e1 + 8 * (re_nheld e1 - 1)) (le8 (Z_to_bv 64 (key_addr kl)))).
  { pose proof HB as X. rewrite El, CF.gestures_end_b.key_ptrs_app in X.
    apply bytes_at_app in X as [_ X]. rewrite CF.gestures_end_b.key_ptrs_length in X.
    change (key_ptrs [kl]) with (le8 (Z_to_bv 64 (key_addr kl)) ++ []) in X. rewrite app_nil_r in X.
    replace (re_hp e1 + 8 * (re_nheld e1 - 1)) with (re_hp e1 + Z.of_nat (8 * length ks0)); [exact X|].
    unfold re_nheld. rewrite El, length_app. cbn [length]. lia. }
  assert (SPR1 : spZ R1 = S0 - 144).
  { change (spZ R1) with (bv_unsigned (getr R1 2)). rewrite G2. apply unsigned_lit. glia. }
  assert (PRE2 : call_pre Bm MR L1 A1 R1 m1 md1).
  { apply (sd_pre_free L1 A1 m1 md1 R1 RP1 IN1 G2 G4). rewrite G1. exact sd_ret_ok. }
  pose proof FRC as FRf. unfold free_contract_rt in FRf. rewrite FREEPC in FRf.
  eapply SR_bind.
  { apply (FRf L1 A1 R1 m1 md1 (resolveF qd y) _ (runF F qd bnd tp) PRE2 RO1 Hpk); [rewrite Ep; exact G10 | exact RTO]. }
  intros c3 (L2 & A2 & regs2 & mem2 & md2 & -> & CP & (bb1 & bb2 & EB1 & EB2) & _ & RO2 & _ & SURVu & INI2 & LN &
    RS2).
  rewrite Ep in EB1.
  pose proof (sd_free_rp L1 A1 R1 m1 md1 L2 A2 regs2 mem2 md2 (resolveF qd y) _ W1 Hpk ltac:(clear - jj; lia) M1 CP
                SURVu LN) as RP2.
  rewrite Ep in RP2.
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & PR2 & _ & _ & _ & SC2).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  assert (RO2r : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RO2).
  assert (NDB1 : List.NoDup (map fst (blocks L1 A1))) by (apply NoDup_ListNoDup; exact (NODUP _ _ _ _ M1)).
  assert (BACKb : forall q m, In (q, m) (blocks L2 A2) -> In (q, m) (blocks L1 A1) /\ q <> key_addr k).
  { intros q m Hq. rewrite EB2 in Hq. split.
    - rewrite EB1. apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq].
    - intros ->. pose proof NDB1 as X. rewrite EB1, map_app in X. cbn [map fst] in X. apply NoDup_remove_2 in X.
      apply X. rewrite <- map_app. change (key_addr k) with (fst (key_addr k, m)). apply in_map. exact Hq. }
  assert (SURVb : forall q m, In (q, m) (blocks L1 A1) -> q <> key_addr k -> In (q, m) (blocks L2 A2)).
  { intros q m Hq Hn. rewrite EB1 in Hq. rewrite EB2. apply in_app_or in Hq as [Hq|[Hq|Hq]].
    - apply in_or_app. left. exact Hq.
    - exfalso. injection Hq as E _. exact (Hn (eq_sym E)).
    - apply in_or_app. right. exact Hq. }
  assert (HI2 : In (re_hp e1, re_kh e1) (blocks L2 A2)) by exact (SURVb _ _ HI NHK).
  assert (GI2 : In (G, SRC_TABLE) (blocks L2 A2)) by exact (SURVb _ _ GI1 NGK).
  assert (RPc : relay_post Bm API DRAIN_K EE FF L A regs mem md L2 A2 regs mem2 md2).
  { eapply (sb_comp Bm API).
    all: try first [exact AX | exact CTX | exact EU | exact BW | exact SEGS | exact RP1 | exact RP2].
    - intros a Ha. change (spZ regs) with S0 in Ha.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. glia.
    - intros a [X|X]; [left|right; exact X]. rewrite SPR1 in X. unfold ALLOC_STACK in X.
      change (spZ regs) with S0.
      unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. clear - X. lia.
    - intros a Hs _ Ea. cbv beta in Ea. destruct Hs as [Hs|Hs].
      + change (spZ regs) with S0 in Hs.
        unfold DRAIN_K, DRAIN_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Hs. glia.
      + apply (KF3 (a - key_addr k)); [glia|]. replace (key_addr k + (a - key_addr k)) with a by ring.
        exact (GEI a Hs).
    - intros p0 n0 Hp0 _ Hn NF Eq. cbv beta in Eq.
      assert (INq : In (ptr_addr L p0, n0) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p0, n0); split; [reflexivity | exact Hp0]).
      destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n0 BK1 OU1 INq Hn NF) as (U1 & _).
      apply U1. rewrite Eq. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. exact IKA.
    - intros a Ha _ _ Ea. exfalso. cbv beta in Ea. destruct Ha as [Ha|Ha]; [glia|].
      apply (KF3 (a - key_addr k)); [glia|]. replace (key_addr k + (a - key_addr k)) with a by ring. exact Ha.
    - intros p0 n0 i Hp0 Hp1 NF Hi Ea. exfalso. cbv beta in Ea.
      pose proof RP1 as (_ & _ & _ & _ & _ & AD1 & _).
      assert (INq : In (ptr_addr L p0, n0) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p0, n0); split; [reflexivity | exact Hp0]).
      assert (INq1 : In (ptr_addr L p0, n0) (blocks L1 A1)).
      { unfold blocks. apply in_map_iff. exists (p0, n0).
        split; [cbn [fst snd]; rewrite (AD1 p0 n0 Hp0 Hp1 NF); reflexivity | exact Hp1]. }
      destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n0 BK1 OU1 INq ltac:(glia) NF) as (U1 & _).
      assert (NE1 : ptr_addr L p0 <> key_addr k).
      { intros Eq. apply U1. rewrite Eq. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right.
        exact IKA. }
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 INq1 KK1 NE1) as [DJ|DJ]; glia. }
  pose proof (rp_msame _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as MS2.
  match type of MS2 with msame ?PP _ _ => set (P2 := PP) in MS2 end.
  assert (P2S : forall a, S0 - 144 <= a < S0 -> P2 a).
  { intros a Ha. unfold P2. cbv beta. left.
    split; [left; glia|]. split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M1 Ho); glia|].
    split; [intros Ho; pose proof (owned_lo2 _ _ _ _ _ M2 Ho); glia|].
    split; [unfold scratch_k; rewrite SPR1; unfold ALLOC_STACK; glia | glia]. }
  assert (P2I : forall a, img_plain Bm a -> P2 a).
  { intros a Hp0. pose proof Hp0 as (Im & _ & _ & NE2). pose proof (img_lo a Im) as IL. unfold P2. cbv beta. left.
    split; [right; exact Im|]. split; [exact (img_unowned _ _ _ _ a M1 Hp0)|].
    split; [exact (img_unowned _ _ _ _ a M2 Hp0)|].
    split; [unfold scratch_k; rewrite SPR1; unfold ALLOC_STACK; glia|].
    intros Ea. apply (KF3 (a - key_addr k)); [glia|]. replace (key_addr k + (a - key_addr k)) with a by ring.
    exact Im. }
  assert (P2B : forall q k0 a, In (q, k0) (blocks L1 A1) -> q <> key_addr k -> q <= a < q + k0 -> P2 a).
  { intros q k0 a Hq Hn Ha. unfold P2. cbv beta. right. exists q, k0.
    split; [exact Hq|]. split; [glia|]. split; [exact Hn|]. split; [glia|].
    destruct (blocks_disjoint Bm API _ _ _ _ q k0 (key_addr k) _ M1 Hq KK1 Hn) as [DJ|DJ]; glia. }
  destruct (dr_cut m1 (SA + 40) (SA + 52) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]
              [CB 4 (re_pad2 e1)] EC3 ltac:(cbn [cells_size csize]; lia)) as [EH1 EH2].
  assert (EH1' : rw_cells rsegs mem2 (SA + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]).
  { pose proof EH1 as X. rewrite <- SEGS in X |- *. apply (rw_tr _ _ _ _ _ MS2 X). intros a Ha.
    cbn [cells_size csize] in Ha. apply (P2B G SRC_TABLE a GI1 NGK). unfold SRC_TABLE, SRC_ENTRY in *. glia. }
  assert (EHN : rw_cells rsegs (normalize rsegs mem2) (SA + 40)
                  [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))]).
  { apply (rw_cells_normalize rsegs mem2 _ _ RO2r EH1'). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [glia|]. apply g_noimg. glia. }
  assert (WRH2 : forall i, 0 <= i < re_kh e1 -> writable_at rsegs mem2 (re_hp e1 + i)).
  { intros i Hi. rewrite <- SEGS. exact (BW _ _ _ _ (re_hp e1) (re_kh e1) i M2 HI2 Hi). }
  destruct (sb_c8w mem2 (re_hp e1 + 8 * Z.of_nat (length ka))) as (jw & SL2); [glia | glia | |].
  { intros i Hi.
    replace (re_hp e1 + 8 * Z.of_nat (length ka) + i) with (re_hp e1 + (8 * Z.of_nat (length ka) + i)) by ring.
    apply WRH2. glia. }
  assert (SLNm : rw_cells rsegs (normalize rsegs mem2) (re_hp e1 + 8 * Z.of_nat (length ka)) [C8 jw]).
  { apply (rw_cells_normalize rsegs mem2 _ _ RO2r SL2). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [glia|].
    replace (re_hp e1 + 8 * Z.of_nat (length ka) + i) with (re_hp e1 + (8 * Z.of_nat (length ka) + i)) by ring.
    apply HF3. glia. }
  assert (LP2 : rw_cells rsegs mem2 (re_hp e1 + 8 * (re_nheld e1 - 1)) [C8 (Z_to_bv 64 (key_addr kl))]).
  { apply sd_c8.
    - rewrite <- SEGS. eapply by_tr; [exact MS2 | exact LPB |]. intros a Ha. rewrite length_le8 in Ha.
      apply (P2B (re_hp e1) (re_kh e1) a HI NHK). glia.
    - intros i Hi.
      replace (re_hp e1 + 8 * (re_nheld e1 - 1) + i) with (re_hp e1 + (8 * (re_nheld e1 - 1) + i)) by ring.
      apply WRH2. glia. }
  assert (LPNm : rw_cells rsegs (normalize rsegs mem2) (re_hp e1 + 8 * (re_nheld e1 - 1))
                   [C8 (Z_to_bv 64 (key_addr kl))]).
  { apply (rw_cells_normalize rsegs mem2 _ _ RO2r LP2). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEGS); [glia|].
    replace (re_hp e1 + 8 * (re_nheld e1 - 1) + i) with (re_hp e1 + (8 * (re_nheld e1 - 1) + i)) by ring.
    apply HF3. glia. }
  assert (V2 : getr regs2 2 = Z_to_bv 64 (S0 - 144))
    by (transitivity (getr R1 2); [exact (PR2 2 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G2]).
  assert (V3 : getr regs2 3 = getr regs 3)
    by (transitivity (getr R1 3); [exact (PR2 3 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G3]).
  assert (V4 : getr regs2 4 = getr regs 4)
    by (transitivity (getr R1 4); [exact (PR2 4 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G4]).
  assert (V8 : getr regs2 8 = Z_to_bv 64 SA)
    by (transitivity (getr R1 8); [exact (PR2 8 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G8]).
  assert (V9 : getr regs2 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q))
    by (transitivity (getr R1 9); [exact (PR2 9 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G9]).
  assert (V19 : getr regs2 19 = Z_to_bv 64 (8 * Z.of_nat (length ka)))
    by (transitivity (getr R1 19); [exact (PR2 19 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G19]).
  assert (V22 : getr regs2 22 = Z_to_bv 64 384)
    by (transitivity (getr R1 22); [exact (PR2 22 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G22]).
  assert (V25 : getr regs2 25 = Z_to_bv 64 DR_TU)
    by (transitivity (getr R1 25); [exact (PR2 25 ltac:(unfold callee_saved; clear - PR2; lia)) | exact G25]).
  match goal with |- context [YK11.mkst regs2 ?pc mem2 _] =>
    replace pc with (Z_to_bv 64 0x13dc8) by (first [exact G1 | symmetry; exact G1]) end.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, V8, V19. rewrite SEGS.
    eapply (evt_normalize rsegs); [exact dl_wx | exact RO2r |].
    eapply dr_gdrop; [exact EHN | reflexivity | exact SLNm | reflexivity | exact LPNm | apply mem_inv_normalize | | |
                      glia | glia | clear - AL16; Z.div_mod_to_equations; lia | glia |
                      clear - ka; Z.div_mod_to_equations; lia | glia].
    all: destruct DJh as [DJ|DJ]; [left | right]; unfold SRC_TABLE, SRC_ENTRY in *; glia. }
  intros ms3 (can3 & (s3 & QP & REL3 & ROS3) & EQ3).
  destruct QP as (m3' & y10 & y11 & y12 & y13 & y14 & -> & MU3' & WM3' & _ & HC3' & HS3').
  destruct (KindB.ms_rel_MS _ _ _ _ _ _ _ _ _ REL3) as [ECAN3 HR3].
  rewrite ECAN3 in EQ3.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  assert (RTL3 : RTL R3) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3).
  pose proof RTL3 as (((Y2 & Y3 & Y4 & Y8 & Y22 & Y25) & Y23 & Y26) & Y27).
  assert (Y9 : getr R3 9 = Z_to_bv 64 (re_buf e1 + Z.of_nat Q)) by rgw X3.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y9, Y27. rewrite SEGS.
    eapply dr_next; clear - UB0 UBU UEUd PQ; lia. }
  intros ms4 (can4 & -> & EQ4).
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m3 := ms_mem can3) in *.
  pose proof (sb_back mem2 m3' m3 _ RO2r HR3 ROS3 MU3' WM3') as (MU3 & WM3r & RO3r).
  pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 HC3') as HC3.
  pose proof (rw_cells_of_rel rsegs m3 m3' _ _ HR3 HS3') as HS3.
  assert (WM3 : wmono segs mem2 m3) by (rewrite SEGS; exact WM3r).
  pose proof (msame_trans _ _ _ _ _ MS2 (msame_munch _ _ _ MU3 WM3)) as MSa.
  match type of MSa with msame ?PP _ _ => set (Pa := PP) in MSa end.
  assert (PSk : forall a, S0 - 144 <= a < S0 -> Pa a).
  { intros a Ha. unfold Pa. cbv beta. split; [exact (P2S a Ha)|]. split; [glia|]. cbn [outside].
    split; [glia|]. split; [glia | exact I]. }
  assert (PIm : forall a, img_plain Bm a -> Pa a).
  { intros a Hp0. unfold Pa. cbv beta. pose proof Hp0 as (Im & _). pose proof (img_lo a Im) as IL.
    split; [exact (P2I a Hp0)|]. split; [glia|]. cbn [outside].
    split; [intros Rw; exact (g_noimg a ltac:(glia) Im)|]. split; [|exact I].
    intros Rw. apply (HF3 (a - re_hp e1)); [glia|]. replace (re_hp e1 + (a - re_hp e1)) with a by ring. exact Im. }
  assert (PBk : forall q k0 a, In (q, k0) (blocks L1 A1) -> q <> G -> q <> key_addr k -> q <= a < q + k0 ->
              (q <> re_hp e1 \/
               ~ (re_hp e1 + 8 * Z.of_nat (length ka) <= a < re_hp e1 + 8 * Z.of_nat (length ka) + 8)) -> Pa a).
  { intros q k0 a Hq NG NK Ha Hh0. unfold Pa. cbv beta. split; [exact (P2B q k0 a Hq NK Ha)|].
    pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as BR.
    pose proof (blocks_disjoint Bm API _ _ _ _ q k0 G SRC_TABLE M1 Hq GI1 NG) as DJ.
    split; [glia|]. cbn [outside].
    split; [destruct DJ as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia|]. split; [|exact I].
    destruct Hh0 as [Hh0|Hh0]; [|exact Hh0].
    destruct (blocks_disjoint Bm API _ _ _ _ q k0 (re_hp e1) (re_kh e1) M1 Hq HI Hh0) as [DJ2|DJ2]; glia. }
  assert (PGk : forall a, SA <= a < SA + 56 -> ~ (SA + 48 <= a < SA + 52) -> Pa a).
  { intros a Ha Hn. unfold Pa. cbv beta.
    split; [apply (P2B G SRC_TABLE a GI1 NGK); unfold SRC_TABLE, SRC_ENTRY in *; glia|].
    split; [glia|]. cbn [outside]. split; [exact Hn|]. split; [|exact I].
    destruct DJh as [DJ|DJ]; unfold SRC_TABLE, SRC_ENTRY in *; glia. }
  assert (TPr : forall c cs, rw_cells rsegs m1 c cs -> (forall a, c <= a < c + Z.of_nat (cells_size cs) -> Pa a) ->
            rw_cells rsegs m3 c cs).
  { intros c0 cs HX HP. rewrite <- SEGS in HX |- *. exact (rw_tr _ _ _ c0 cs MSa HX HP). }
  assert (SL3 : bytes_at segs m3 (re_hp e1 + 8 * Z.of_nat (length ka))
                  (le8 (Z_to_bv 64 (key_addr (last (re_keys e1) (0, [], [])))))).
  { rewrite El, last_last, SEGS. destruct HS3 as [[_ BB3] _]. cbn [cells_bytes cbytes] in BB3.
    rewrite app_nil_r in BB3. exact BB3. }
  assert (EK2 : entry_okx L2 A2 m3 (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1)
                  (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1) (swap_remove (0, [], []) (length ka) (re_keys e1))
                  (re_U e1) (re_junk e1))).
  { apply (sd_okx L1 A1 L2 A2 m1 m3 e1 Pa ka kb k (0, [], []) MSa EK1 Eks).
    - intros q m Hq _ Hn. exact (SURVb q m Hq Hn).
    - intros q m a Hq Hb Hn Ha Hh0. apply (PBk q m a Hq); [ | exact Hn | exact Ha | exact Hh0].
      apply (dx_ng OUT1 _ q ND1). right. apply in_or_app. left. exact Hb.
    - destruct (Z.eq_dec (re_cap e1) 0) as [C|C]; [left; exact C | right]. intros E.
      apply (sb_hp_nd OUT1 e1 h1 ND1 HP0). right. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ 0) C). left. exact E.
    - intros X. apply (sb_hp_nd OUT1 e1 h1 ND1 HP0). right. right. apply in_or_app. right. apply in_or_app. left.
      exact X.
    - destruct (Z.eq_dec (re_cap e1) 0) as [C|C]; [left; exact C | right]. intros E.
      apply NKB. rewrite (proj2 (Z.eqb_neq _ 0) C). left. exact E.
    - exact HP0.
    - exact SL3. }
  assert (SAC2 : rw_cells segs m3 SA [CB 56%nat (entry_bytes (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1)
                   (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1)
                   (swap_remove (0, [], []) (length ka) (re_keys e1)) (re_U e1) (re_junk e1)))]).
  { assert (RN : re_nheld (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1)
                   (re_hp e1) (re_kh e1) (re_pad2 e1) (swap_remove (0, [], []) (length ka) (re_keys e1)) (re_U e1)
                   (re_junk e1)) = re_nheld e1 - 1).
    { unfold re_nheld. cbn [re_keys]. rewrite Eks, length_swap_remove, length_app. cbn [length]. lia. }
    rewrite SEGS. apply ent_join; [exact K3 | exact K4 | | |].
    - apply TPr; [exact EC1|]. intros a Ha. cbn [cells_size csize] in Ha. apply PGk; glia.
    - apply TPr; [exact EC2|]. intros a Ha. cbn [cells_size csize] in Ha. apply PGk; glia.
    - rewrite RN.
      apply (dr_join m3 (SA + 40) (SA + 52) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1 - 1))]
               [CB 4 (re_pad2 e1)]); [exact HC3 | | cbn [cells_size csize]; lia].
      apply TPr; [exact EH2|]. intros a Ha. cbn [cells_size csize] in Ha. apply PGk; glia. }
  pose proof (swap_remove_perm (0, [], []) ka k kb) as PMk. rewrite <- Eks in PMk.
  assert (PMe : Permutation.Permutation (entry_blocks e1) (key_addr k :: entry_blocks (RE (re_fd e1) (re_eof e1)
                  (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1)
                  (swap_remove (0, [], []) (length ka) (re_keys e1)) (re_U e1) (re_junk e1)))).
  { unfold entry_blocks. cbn [re_cap re_buf re_hp re_keys]. rewrite !app_assoc.
    eapply Permutation.perm_trans;
      [apply Permutation.Permutation_app_head, (Permutation.Permutation_map key_addr PMk)|].
    cbn [map]. apply Permutation.Permutation_sym, Permutation.Permutation_middle. }
  assert (LO : Z.of_nat (length O) = NO)
    by (destruct OUTD as [(_ & _ & N0 & EO)|(_ & _ & _ & _ & _ & LO & _)]; [rewrite EO; cbn; clear - N0; lia | exact LO]).
  assert (LVT : forall p0 q0 n0, live_at L1 A1 p0 q0 n0 -> q0 <> key_addr k -> live_at L2 A2 p0 q0 n0).
  { intros p0 q0 n0 Hl Hq. exact (sdp_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W1 RP2 Hl Hq). }
  assert (NKS : forall k0, In k0 (swap_remove (0, [], []) (length ka) (re_keys e1)) -> key_addr k0 <> key_addr k).
  { pose proof (swap_remove_perm (0, [], []) ka k kb) as PM0. rewrite <- Eks in PM0.
    assert (ND0 : List.NoDup (key_addr k :: map key_addr (swap_remove (0, [], []) (length ka) (re_keys e1)))).
    { apply (Permutation.Permutation_NoDup (Permutation.Permutation_map key_addr PM0)). apply NoDup_ListNoDup.
      exact K12. }
    apply List.NoDup_cons_iff in ND0 as [NI _]. intros k0 Hk0 E. apply NI. rewrite <- E. apply in_map. exact Hk0. }
  assert (FK1 : Forall2 (fun k0 a0 => live_at L1 A1 (resolveF qd a0) (key_addr k0)
                                        (Z.of_nat (length (key_text k0)) + 1))
                  (swap_remove (0, [], []) (length ka) (re_keys e1)) (swap_remove adr0 (length ka) (da_keys fa))).
  { rewrite Eks, Ey. exact (sdp_f2sw _ (0, [], []) adr0 (length ka) ka k kb ya y yb eq_refl Lya FA Ry FB). }
  apply SR_ret.
  apply (dln_of s P Q R4 L2 A2 m3 md2
    (RE (re_fd e1) (re_eof e1) (re_skip e1) (re_pad1 e1) (re_buf e1) (re_used e1) (re_cap e1) (re_hp e1) (re_kh e1)
        (re_pad2 e1) (swap_remove (0, [], []) (length ka) (re_keys e1)) (re_U e1) (re_junk e1)) h1 OUT1 junk1 LB1 D).
  { unfold RTL, RTK, RT. repeat match goal with |- _ /\ _ => split end; rgw X4. }
  { rewrite (CF.gestures_end_b.getr_of_eqv2 _ _ _ X4) by reflexivity. simp_regs. cbn [re_buf]. f_equal.
    clear - Q. lia. }
  unfold DLNB. split; [exact DFs|]. rewrite EK. unfold LCORE.
  split.
  { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPc MU3 WM3 GEI).
    intros a Ha.
    destruct (dx_odec [(SA + 48, SA + 52);
                       (re_hp e1 + 8 * Z.of_nat (length ka), re_hp e1 + 8 * Z.of_nat (length ka) + 8)] a)
      as [Ox|(lo & hi & Iw & Rw)]; [left; exact Ox|right].
    destruct Iw as [Iw|[Iw|[]]]; injection Iw as <- <-.
    - right. right. right. split; [exact (g_noimg a ltac:(glia))|].
      split; [exists G, SRC_TABLE; split; [exact GI2 | unfold SRC_TABLE, SRC_ENTRY in *; glia]|].
      intros p0 n0 i0 _ _ _ _ NE1 E. apply NE1. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. glia.
    - right. right. right. split.
      { intros Im. apply (HF3 (a - re_hp e1)); [glia|]. replace (re_hp e1 + (a - re_hp e1)) with a by ring.
        exact Im. }
      split; [exists (re_hp e1), (re_kh e1); split; [exact HI2 | glia]|].
      intros p0 n0 i0 Hp0 Hp2 NF Hi _ E.
      assert (INq : In (ptr_addr L p0, n0) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p0, n0); split; [reflexivity | exact Hp0]).
      destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 _ n0 BK1 OU1 INq ltac:(glia) NF) as (U1 & _).
      assert (NEh : ptr_addr L p0 <> re_hp e1).
      { intros Eq. apply U1. rewrite Eq. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) HP0).
        apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
      pose proof RPc as (_ & _ & _ & _ & _ & ADc & _).
      rewrite <- (ADc p0 n0 Hp0 Hp2 NF) in E, NEh.
      assert (INq2 : In (ptr_addr L2 p0, n0) (blocks L2 A2))
        by (unfold blocks; apply in_map_iff; exists (p0, n0); split; [reflexivity | exact Hp2]).
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M2 INq2 HI2 NEh) as [DJ|DJ]; glia. }
  split; [exact (INI2 IN1)|].
  split.
  { exists (tp ++ [RFree (Z.of_nat jj + 1) y]), qd,
      (DA (da_out fa) (da_buf fa) (da_hp fa) (swap_remove adr0 (length ka) (da_keys fa)) (da_pend fa) (da_ev fa)
          (da_erecs fa)).
    split.
    - unfold RCORE, DLNK, dadr_ok. rewrite sdp_nret1. cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
      split; [exact LQ|]. split; [exact (p3a_wf_snoc tp (RFree (Z.of_nat jj + 1) y) WF1 PY)|].
      split.
      { refine (conj O1 (conj O2 (conj O3 (conj _ (conj O5 (conj O6 O7)))))).
        rewrite Ey. rewrite Ey in O4. exact (sdp_fsw _ adr0 ya y yb (length ka) (eq_sym Lya) O4). }
      split; [rewrite sdp_runF_free; exact RS2|].
      split; [|exact DKH1].
      split; [intros HLv Hoc; exact (LVT _ _ _ (LV1 HLv Hoc) (fun E => NKO (eq_sym E)))|].
      split.
      + unfold entry_links. cbn [re_cap re_buf re_hp re_kh re_keys da_buf da_hp da_keys].
        split.
        { intros C. apply (LVT _ _ _ (EL1b C)). intros E. apply NKB.
          rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by (clear - C; lia). left. exact E. }
        split; [intros C; exact (LVT _ _ _ (EL1h C) NHK)|].
        apply (sdp_f2 _ _ (fun k0 => key_addr k0 <> key_addr k) _ _ FK1); [exact NKS|].
        intros k0 y0 Hk0 Hl. cbv beta in Hk0, Hl |- *. exact (LVT _ _ _ Hl Hk0).
      + apply (sdp_src L1 A1 L2 A2 qd (known_at L A) fa _ h1);
          [exact (fun p0 q0 n0 Hl Hq => LVT p0 q0 n0 Hl (NKHs q0 Hq)) | reflexivity | reflexivity | reflexivity |
           exact SL1].
    - rewrite sdp_nret1, <- app_assoc. cbn [app da_out da_hp da_keys]. unfold anext in RF1 |- *.
      cbn [da_buf da_pend da_ev da_erecs]. exact RF1. }
  split; [rewrite SEGS; exact RO3r|].
  split.
  { destruct FR1 as (j0 & j1 & j2 & j4 & FRc). exists j0, j1, j2, j4. eapply rw_tr; [exact MSa | exact FRc |].
    intros a Ha. cbn [cells_size csize app dr_saved] in Ha. exact (PSk a ltac:(glia)). }
  split; [exact SAC2|].
  split; [exact EK2|].
  split.
  { eapply src_at_tr0; [exact MSa | exact SR1 | | |].
    - intros a Ha. apply PIm, GRP. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia.
    - intros q k0 Hq Hb. exact (SURVb q k0 Hq (NKHs q Hb)).
    - intros q k0 a Hq Hb Ha. exact (PBk q k0 a Hq (NGH q Hb) (NKHs q Hb) Ha (or_introl (NHH q Hb))). }
  split.
  { eapply others_at_tr; [exact MSa | exact OT1 |]. intros i a Hi _ Ha. apply PIm, GRP.
    unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *. glia. }
  split; [exact SM1|].
  split.
  { apply (sb_link s false (dlH s P) _ _ _ _ e1); [exact LK1 | reflexivity | reflexivity | reflexivity | exact KT |].
    reflexivity. }
  split; [eapply sb_hist; [exact HI1 | apply app_assoc]|].
  split.
  { rewrite (sb_pst s false (dlH s P)), SAR2. glia. }
  split; [exact RST1|].
  split.
  { exact (sd_blk L1 A1 L2 A2 e1 _ h1 OUT1 (key_addr k) (Z.of_nat jj + 1) BK1 SURVb BACKb KK1 ltac:(lia) NDB1
             PMe). }
  split.
  { destruct GL1 as (C1 & C2 & C3 & CC4 & _).
    split; [eapply rw_tr; [exact MSa | exact C1 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GCP; unfold G_CLIENT in *; glia|].
    split; [eapply rw_tr; [exact MSa | exact C2 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    split; [eapply rw_tr; [exact MSa | exact C3 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    split; [eapply rw_tr; [exact MSa | exact CC4 |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    destruct (sb_c4 m3 ERR) as (v & HV); [glia | glia | |exists v; rewrite SEGS; exact HV].
    intros i Hi. rewrite <- SEGS. apply WM3, SC2. right. glia. }
  apply (sb_out s false (dlH s P)).
  destruct OU1 as (OF & OT). split.
  - intros LV. destruct (OF LV) as (C & EO & EC' & OB).
    split; [eapply rw_tr; [exact MSa | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    split; [exact EO|]. split; [exact EC'|]. intros Cp0. destruct (OB Cp0) as (OI & OBy).
    assert (NOK : OUT <> key_addr k) by (rewrite <- EO; intros E; exact (NKO (eq_sym E))).
    split; [exact (SURVb _ _ OI NOK)|].
    eapply by_tr; [exact MSa | exact OBy |]. intros a Ha.
    apply (PBk OUT CAP a OI); [apply (dx_ng OUT1 _ OUT ND1); left; symmetry; exact EO | exact NOK | |
                               left; rewrite <- EO; exact NHO].
    destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & _ & LJ)]; [glia|]. rewrite length_app in Ha. glia.
  - intros LV. destruct (OT LV) as (C & OB).
    split; [eapply rw_tr; [exact MSa | exact C |]; intros a Ha; cbn [cells_size csize] in Ha;
            apply PIm, GRP; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; glia|].
    destruct OB as [Z0|(Cp0 & NLo & OI & OFr & OBy & LJ)]; [left; exact Z0|right].
    assert (NOK : OUT1 <> key_addr k) by (intros E; exact (NKO (eq_sym E))).
    split; [exact Cp0|]. split; [exact NLo|]. split; [exact (SURVb _ _ OI NOK)|]. split; [exact OFr|].
    split; [|exact LJ].
    eapply by_tr; [exact MSa | exact OBy |]. intros a Ha.
    apply (PBk OUT1 _ a OI); [apply (dx_ng OUT1 _ OUT1 ND1); left; reflexivity | exact NOK | | left; exact NHO].
    assert (LL : Z.of_nat (length LB1) = Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P ++ [dline s P Q]))))
      by (rewrite <- H7h; unfold bzs; rewrite length_map; reflexivity).
    rewrite !length_app in Ha. glia.
Qed.

Lemma seen_step : forall s P Q c, DLS s P Q c -> SR segs c (DLN s (S Q)).
Proof using All.
  intros s P Q c H0.
  eapply SR_bind; [exact (seen_test s P Q c H0)|]. intros c1 [H1|H1]; [apply SR_ret; exact H1|].
  eapply SR_bind; [exact (seen_scan s P Q c1 H1)|]. intros c2 [H2|[H2|H2]];
    [apply SR_ret; exact H2 | | exact (seen_drop s P Q c2 H2)].
  eapply SR_bind; [exact (seen_add_a s P Q c2 H2)|]. intros c3 [H3|H3];
    [apply SR_ret; exact H3 | exact (seen_add_b s P Q c3 H3)].
Qed.

Lemma ret_pc_13e68 : ret_pc (Z_to_bv 64 0x13e68) = Z_to_bv 64 0x13e68.
Proof using. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma mm_rest : forall (us : list byte) P, (P <= length us)%nat ->
  mm_result us P 0 (length us - P) = skipn P us ++ skipn (length us - P) us.
Proof using.
  intros us P HP. unfold mm_result, upd_bytes, slice.
  assert (E : firstn (length us - P) (skipn P us) = skipn P us).
  { apply firstn_all2. rewrite length_skipn. clear - HP. lia. }
  rewrite E, length_skipn. reflexivity.
Qed.

Lemma ll_le : forall n : nat, Z.of_nat n <= 6000 -> Nat.ltb LINE_LIMIT n = false.
Proof using.
  intros n H. apply Nat.ltb_ge. apply Nat2Z.inj_le. unfold LINE_LIMIT. change (Z.of_nat 6000) with 6000. exact H.
Qed.

Lemma ll_gt : forall n : nat, 6001 <= Z.of_nat n -> Nat.ltb LINE_LIMIT n = true.
Proof using.
  intros n H. apply Nat.ltb_lt. apply Nat2Z.inj_lt. unfold LINE_LIMIT. change (Z.of_nat 6000) with 6000.
  clear - H. lia.
Qed.

Lemma nz_in : forall U : list byte, nozero (bzs U) -> ~ In (Z_to_bv 8 0) U.
Proof using.
  intros U H Hin. unfold nozero, bzs in H. rewrite Forall_forall in H.
  apply (H (bz (Z_to_bv 8 0))); [apply in_map; exact Hin | vm_compute; reflexivity].
Qed.

Lemma entry_okw_rest : forall L1 A1 m1 m2 e1 Pa sk2 used2 U2 junk2,
  msame Pa m1 m2 -> entry_okx L1 A1 m1 e1 ->
  (forall q k a, In (q, k) (blocks L1 A1) -> (q = re_hp e1 \/ In q (map key_addr (re_keys e1))) -> q <= a < q + k ->
     Pa a) ->
  0 < re_cap e1 -> (sk2 = 0 \/ sk2 = 1) -> Z.of_nat (length U2) = used2 -> used2 <= 6000 -> ~ In (Z_to_bv 8 0) U2 ->
  Z.of_nat (length junk2) = re_cap e1 - used2 ->
  rw_cells segs m2 (re_buf e1) [CB (Z.to_nat (re_cap e1)) (U2 ++ junk2)] ->
  entry_okw L1 A1 m2 (RE (re_fd e1) (re_eof e1) sk2 (re_pad1 e1) (re_buf e1) used2 (re_cap e1) (re_hp e1) (re_kh e1)
                        (re_pad2 e1) (re_keys e1) U2 junk2).
Proof using.
  intros L1 A1 m1 m2 e1 Pa sk2 used2 U2 junk2 MS
    (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) HP Cp Hs LU HU NZ LJ RC.
  destruct E9 as [(C0 & _)|(_ & BI & BF & _)]; [clear - C0 Cp; lia|].
  unfold entry_okw, re_nheld.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_junk re_hp re_kh re_keys].
  unfold re_nheld in E10, E11.
  split; [exact E1|]. split; [exact Hs|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  split; [exact E6|]. split; [exact LU|]. split; [exact HU|]. split; [exact NZ|].
  split; [right; split; [exact Cp|]; split; [exact BI|]; split; [exact BF|]; split; [exact LJ | exact RC]|].
  split; [exact E10|].
  split.
  { destruct E11 as [Z0|(HI & HF & H8 & H8' & HB)]; [left; exact Z0 | right].
    split; [exact HI|]. split; [exact HF|]. split; [exact H8|]. split; [exact H8'|].
    eapply by_tr; [exact MS | exact HB |]. intros a Ha. apply (HP _ _ a HI); [left; reflexivity|].
    rewrite CF.gestures_end_b.key_ptrs_length in Ha. clear - Ha H8. lia. }
  split; [exact E12|]. split; [exact E13|].
  apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) E14 k Hk) as (K1 & K2 & K3 & K4 & K5).
  split; [exact K1|]. split; [exact K2|]. split; [|split; [exact K4 | exact K5]].
  eapply by_tr; [exact MS | exact K3 |]. intros a Ha. apply (HP _ _ a K1); [right; apply in_map; exact Hk|].
  rewrite length_app in Ha. cbn [length] in Ha. clear - Ha. lia.
Qed.

Lemma rest_step : forall s P c, DLR s P c -> SR segs c (DI (dnext LIVE MX s)).
Proof using All.
  intros s P c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & -> & RTL1 & G18 & G19 & G20 & DB & NZP &
    DLC1).
  pose proof DLC1 as (RP1 & IN1 & TR1 & RO1 & FR1 & SAC1 & EK1 & SR1 & OT1 & SM1 & LK1 & HI1 & LN1 & RS1 & BK1 & GL1 &
    OU1).
  pose proof RP1 as (M1 & _).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (dl_buf s _ _ _ _ _ L1 A1 m1 md1 e1 h1 M1 EK1 LK1) as (EW & LW & EUd & _ & _ & _ & _).
  pose proof EK1 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14).
  pose proof LK1 as (L1c & L2c & L3c & L4c & L5c & L6c & L7c & L8c & L9c & L10c & L11c & WF1).
  pose proof HI1 as (H1g & H2g & H3g & H4g & H5g & H6g & H7g & H8g & H9g & H10g).
  pose proof RS1 as (RS_ref & RS_J1 & RS_gr & RS_wf & RS_st & RS_ei & RS_pe).
  pose proof BK1 as (ND & GI1 & _).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof RTL1 as (((G2 & G3 & G4 & G8 & G22 & G25) & G23 & G26) & G27).
  pose proof DB as (DB1 & _).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEGS; exact RO1).
  destruct (drl_end s P DB NZP) as [DQ SCN0].
  pose proof RS_J1 as (_ & _ & _ & UZ).
  assert (SCN : scan (ds_skip s) (ds_u s) (ddata s) = (dskp s P, skipn P (dW s), drlp s P)).
  { rewrite <- SCN0. unfold dW. rewrite (scan_nz_app (ds_u s) (ds_skip s) [] (ddata s) UZ). reflexivity. }
  assert (DCH : dchunk s = if Nat.ltb LINE_LIMIT (length (skipn P (dW s))) then ([], true, drlp s P)
                           else (skipn P (dW s), dskp s P, drlp s P)).
  { unfold dchunk, chunk. rewrite SCN. reflexivity. }
  assert (DRL : drl s = drlp s P) by (unfold drl; rewrite DCH; destruct (Nat.ltb _ _); reflexivity).
  assert (CK2 : drl s = lines (ds_ref s) (ddata s) /\
                J1 (fst (fst (dchunk s))) (snd (fst (dchunk s))) (feed (ds_ref s) (ddata s))).
  { pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) (ddata s) RS_J1) as CK. unfold drl, dchunk.
    destruct (chunk (ds_u s) (ds_skip s) (ddata s)) as [[u' sk'] ls]. cbv beta iota in CK. exact CK. }
  assert (LINES : lines ST0 (D ++ ddata s) = lines ST0 D ++ drlp s P).
  { rewrite lines_app, <- RS_ref, <- (proj1 CK2), DRL; reflexivity. }
  assert (EUS : ds_u (dnext LIVE MX s) = fst (fst (dchunk s))) by reflexivity.
  assert (ESS : ds_skip (dnext LIVE MX s) = snd (fst (dchunk s))) by reflexivity.
  assert (EH : ds_H (dnext LIVE MX s) = dlH s P)
    by (unfold dnext, dlH, dlrun; cbn [ds_H]; rewrite DRL; reflexivity).
  assert (EKA : ds_ka (dnext LIVE MX s) = dlka s P)
    by (unfold dnext, dlka, dlrun; cbn [ds_ka]; rewrite DRL; reflexivity).
  assert (EOC : ds_ocap (dnext LIVE MX s) = dloc s P)
    by (unfold dnext, dloc, dlrun; cbn [ds_ocap]; rewrite DRL; reflexivity).
  assert (ENO : ds_no (dnext LIVE MX s) = dlno s P)
    by (unfold dnext, dlno; cbn [ds_no]; rewrite DRL; reflexivity).
  destruct (dneed_dnext LIVE MX s RS_gr RS_pe RS_wf RS_st RS_ei) as [NDN WFn].
  assert (DTR1 : DTR L1 A1 (dnext LIVE MX s) e1 h1 OUT1).
  { assert (FU : forall jn an, drun (dneed (dnext LIVE MX s)) LIVE MX (dnext LIVE MX s) jn an =
                               drun (length (pstream s)) LIVE MX (dnext LIVE MX s) jn an).
    { intros jn an. apply drain_run_fuel; [exact WFn | apply le_n |].
      change (dneed s) with (S (length (pstream s) + Nat.b2n (ds_eintr s))) in NDN.
      rewrite RS_ei in NDN. cbn [Nat.b2n] in NDN. clear - NDN. lia. }
    destruct TR1 as (tp & qd & a & RC & RF). destruct a as [ao ab ah ak ap av ar].
    rewrite DQ in RF. unfold lrest, anext in RF.
    cbn [lines_run fst snd da_out da_buf da_hp da_keys da_pend da_ev da_erecs] in RF.
    rewrite app_nil_r, nret_nil, Nat.add_0_r in RF.
    exists tp, qd, (DA ao ab ah ak ap av ar). rewrite FU, EOC. split; [exact RC | exact RF]. }
  assert (CAP4 : 4096 <= re_cap e1).
  { assert (CS : re_cap e1 = ds_cap s) by exact L1c. pose proof RS_gr as X. unfold ulen in X. clear - CS X. lia. }
  destruct K9 as [(C0 & _)|(Cp & BI & BF & BJ & BC)]; [exfalso; clear - C0 CAP4; lia|].
  assert (CAPB : re_cap e1 <= 16384) by (clear - K6; lia).
  pose proof (blk_rng _ _ _ _ _ _ M1 BI) as BR.
  set (rem := Z.of_nat (length (dW s) - P)) in *.
  assert (REMD : rem = Z.of_nat (length (dW s) - P)) by reflexivity.
  assert (ARITH : 4096 <= re_buf e1 /\ re_buf e1 + re_cap e1 <= YM05.alloc_ceiling /\ YM05.alloc_ceiling < 2 ^ 47 /\
                  0 <= rem /\ Z.of_nat P + rem = re_used e1 /\ re_used e1 <= re_cap e1 /\ re_cap e1 <= 16384).
  { clear - BR F4 REMD EUd DB1 K8 CAPB. lia. }
  assert (EBUF : entry_blocks e1 =
                 re_buf e1 :: ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1))).
  { unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0)) by (clear - Cp; lia). reflexivity. }
  pose proof ND as ND'. rewrite EBUF in ND'. apply NoDup_ListNoDup in ND'.
  apply List.NoDup_cons_iff in ND' as [NG ND']. apply List.NoDup_cons_iff in ND' as [NOUT ND'].
  cbn [app] in ND'. apply List.NoDup_cons_iff in ND' as [NBUF _].
  assert (GNB : G <> re_buf e1) by (intros X; apply NG; right; rewrite X; left; reflexivity).
  assert (ONB : OUT1 <> re_buf e1) by (intros X; apply NOUT; rewrite X; left; reflexivity).
  assert (ENB : forall q, In q ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1)) ->
                q <> re_buf e1) by (intros q Hq X; apply NBUF; rewrite <- X; apply in_or_app; left; exact Hq).
  assert (HSNB : forall q, In q (hs_blocks h1) -> q <> re_buf e1)
    by (intros q Hq X; apply NBUF; rewrite <- X; apply in_or_app; right; exact Hq).
  assert (OGN : OUT1 <> G) by exact (dx_ng OUT1 _ OUT1 ND (or_introl eq_refl)).
  assert (NGH : forall q, In q (hs_blocks h1) -> q <> G)
    by (intros q Hb; apply (dx_ng OUT1 _ q ND); right; apply in_or_app; right; exact Hb).
  pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 BI GI1 (fun X => GNB (eq_sym X))) as DJBG.
  assert (DJBS : re_buf e1 + re_cap e1 <= SA \/ SA + 56 <= re_buf e1)
    by (unfold SRC_TABLE, SRC_ENTRY in DJBG; clear - DJBG F6 F7; lia).
  pose (WA := [(SA + 8, SA + 12); (SA + 24, SA + 32); (re_buf e1, re_buf e1 + rem)]).
  assert (PH : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> 0 <= a < 2 ^ 64 /\ outside WA a).
  { intros a Ha. unfold WA. cbn [outside]. clear - Ha ARITH F7 F8. repeat split; lia. }
  assert (PI : forall a, in_img Bm a -> 0 <= a < 2 ^ 64 /\ outside WA a).
  { intros a Ha. pose proof (img_lo a Ha) as IL.
    assert (NB : ~ (re_buf e1 <= a < re_buf e1 + rem)).
    { intros X. apply (blk_noimg _ _ _ _ _ _ (a - re_buf e1) M1 BI); [clear - X ARITH; lia|].
      replace (re_buf e1 + (a - re_buf e1)) with a by ring. exact Ha. }
    unfold WA. cbn [outside]. split; [clear - IL; lia|].
    split; [intros X; exact (g_noimg a ltac:(clear - X; lia) Ha)|].
    split; [intros X; exact (g_noimg a ltac:(clear - X; lia) Ha)|].
    split; [exact NB | exact I]. }
  assert (PB : forall q k a, In (q, k) (blocks L1 A1) -> q <> re_buf e1 -> q <> G -> q <= a < q + k ->
            0 <= a < 2 ^ 64 /\ outside WA a).
  { intros q k a Hq N1 N2 Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
    pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Hq BI N1) as DJ1.
    pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Hq GI1 N2) as DJ2.
    unfold SRC_TABLE, SRC_ENTRY in DJ2. unfold WA. cbn [outside].
    clear - Ha QR DJ1 DJ2 F4 F6 F7 ARITH. repeat split; lia. }
  assert (PG : forall a, SA <= a < SA + 56 -> ~ (SA + 8 <= a < SA + 12) -> ~ (SA + 24 <= a < SA + 32) ->
            0 <= a < 2 ^ 64 /\ outside WA a).
  { intros a Ha N1 N2. unfold WA. cbn [outside]. split; [clear - Ha F4 F5 F6 F7 F8; lia|].
    split; [exact N1|]. split; [exact N2|]. split; [clear - Ha DJBS ARITH; lia | exact I]. }
  assert (EC : rw_cells rsegs m1 SA [CB 56 (entry_bytes e1)]) by (rewrite <- SEGS; exact SAC1).
  destruct (ent_cells _ _ _ EC K3 K4) as (EC1 & EC2 & EC3).
  destruct (dr_cut m1 SA (SA + 8) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1))]
              [C4 (Z_to_bv 64 (re_skip e1)); CB 4 (re_pad1 e1)] EC1 ltac:(cbn [cells_size csize]; glia))
    as [ECfe ECsp].
  destruct (dr_cut m1 (SA + 8) (SA + 12) [C4 (Z_to_bv 64 (re_skip e1))] [CB 4 (re_pad1 e1)] ECsp
              ltac:(cbn [cells_size csize]; glia)) as [ECs ECp].
  destruct (dr_cut m1 (SA + 16) (SA + 24) [C8 (Z_to_bv 64 (re_buf e1))]
              [C8 (Z_to_bv 64 (re_used e1)); C8 (Z_to_bv 64 (re_cap e1))] EC2 ltac:(cbn [cells_size csize]; glia))
    as [ECb ECuc].
  destruct (dr_cut m1 (SA + 24) (SA + 32) [C8 (Z_to_bv 64 (re_used e1))] [C8 (Z_to_bv 64 (re_cap e1))] ECuc
              ltac:(cbn [cells_size csize]; glia)) as [ECu ECc].
  assert (FIN : forall R4 m4 sk2 used2 U2 junk2, RTK R4 -> munch WA m1 m4 -> wmono rsegs m1 m4 -> ro_agree rsegs m4 ->
            (sk2 = 0 \/ sk2 = 1) -> rw_cells rsegs m4 (SA + 8) [C4 (Z_to_bv 64 sk2)] ->
            rw_cells rsegs m4 (SA + 24) [C8 (Z_to_bv 64 used2)] ->
            rw_cells rsegs m4 (re_buf e1) [CB (Z.to_nat (re_cap e1)) (U2 ++ junk2)] ->
            Z.of_nat (length U2) = used2 -> used2 <= 6000 -> ~ In (Z_to_bv 8 0) U2 ->
            Z.of_nat (length junk2) = re_cap e1 - used2 ->
            bzs U2 = ds_u (dnext LIVE MX s) ->
            sk2 = (if ds_skip (dnext LIVE MX s) then 1 else 0) ->
            DI (dnext LIVE MX s) (mkCfg (YK11.mkst R4 (Z_to_bv 64 0x13924) m4 (seg_rom segs)) md1)).
  { intros R4 m4 sk2 used2 U2 junk2 RT4 MUA WMA RO4 SK HS HU HB LU HU6 NZ LJ EUq ESKq.
    assert (WMs : wmono segs m1 m4) by (rewrite SEGS; exact WMA).
    pose proof (msame_munch WA m1 m4 MUA WMs) as MS.
    assert (TP4 : forall c cs, rw_cells rsegs m1 c cs ->
              (forall a, c <= a < c + Z.of_nat (cells_size cs) -> 0 <= a < 2 ^ 64 /\ outside WA a) ->
              rw_cells rsegs m4 c cs).
    { intros c cs H HP. rewrite <- SEGS in H |- *. exact (rw_tr _ _ _ c cs MS H HP). }
    exists R4, L1, A1, m4, md1,
      (RE (re_fd e1) (re_eof e1) sk2 (re_pad1 e1) (re_buf e1) used2 (re_cap e1) (re_hp e1) (re_kh e1) (re_pad2 e1)
          (re_keys e1) U2 junk2), h1, OUT1, junk1, LB1, (D ++ ddata s).
    split; [reflexivity|]. split; [exact RT4|].
    split.
    { apply (sb_kA Bm API AX EU BW SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1 MUA); [exact WMs | exact GEI |].
      intros a Ha. destruct (dx_odec WA a) as [Ox|(lo & hi & Iw & R)]; [left; exact Ox|right].
      right; right; right.
      unfold WA in Iw. destruct Iw as [Iw|[Iw|[Iw|[]]]]; injection Iw as <- <-.
      - split; [exact (g_noimg a ltac:(clear - R; lia))|].
        split; [exists G, SRC_TABLE; split; [exact GI1 | unfold SRC_TABLE, SRC_ENTRY; clear - R F6 F7; lia]|].
        intros p n i _ _ _ _ NE E. apply NE. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. clear - R; lia.
      - split; [exact (g_noimg a ltac:(clear - R; lia))|].
        split; [exists G, SRC_TABLE; split; [exact GI1 | unfold SRC_TABLE, SRC_ENTRY; clear - R F6 F7; lia]|].
        intros p n i _ _ _ _ NE E. apply NE. rewrite E. cbv beta. right. left. unfold SRC_ENTRY. clear - R; lia.
      - split.
        { intros X. apply (blk_noimg _ _ _ _ _ _ (a - re_buf e1) M1 BI); [clear - R ARITH; lia|].
          replace (re_buf e1 + (a - re_buf e1)) with a by ring. exact X. }
        split; [exists (re_buf e1), (re_cap e1); split; [exact BI | clear - R ARITH; lia]|].
        intros p n i Hp Hp1 NF Hi _ Ea.
        pose proof RP1 as (_ & _ & _ & _ & _ & AD1 & _).
        pose proof (AD1 p n Hp Hp1 NF) as AE.
        assert (Q1 : In (ptr_addr L p, n) (blocks L1 A1))
          by (apply CF.gestures_end_b.blocks_In2; exists p; split; [exact AE | exact Hp1]).
        destruct (Z.eq_dec (ptr_addr L p) (re_buf e1)) as [EQb|NEb].
        + assert (Q0 : In (re_buf e1, n) (blocks L A))
            by (rewrite <- EQb; apply CF.gestures_end_b.blocks_In2; exists p; split; [reflexivity | exact Hp]).
          destruct (untouched _ L1 A1 m1 e1 h1 OUT1 junk1 LB1 (re_buf e1) n BK1 OU1 Q0 ltac:(clear - Hi; lia)
                      ltac:(rewrite <- EQb; exact NF)) as [U1 _].
          apply U1. rewrite EBUF. left. reflexivity.
        + destruct (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Q1 BI NEb) as [X|X];
            clear - X Hi Ea R ARITH; lia. }
    split; [exact IN1|].
    split; [exact DTR1|].
    split; [rewrite SEGS; exact RO4|].
    split.
    { destruct FR1 as (j0 & j1 & j2 & j4 & FR). exists j0, j1, j2, j4. eapply rw_tr; [exact MS | exact FR |].
      intros a Ha. apply PH. cbn [cells_size csize app dr_saved] in Ha. clear - Ha F1 F2 F3. lia. }
    split.
    { assert (J1' : rw_cells rsegs m4 SA [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1));
                                         C4 (Z_to_bv 64 sk2); CB 4 (re_pad1 e1)]).
      { refine (dr_join m4 SA (SA + 8) [C4 (Z_to_bv 64 (re_fd e1)); C4 (Z_to_bv 64 (re_eof e1))]
                  [C4 (Z_to_bv 64 sk2); CB 4 (re_pad1 e1)] _ _ ltac:(cbn [cells_size csize]; glia)).
        - apply TP4; [exact ECfe|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; clear - Ha; lia.
        - refine (dr_join m4 (SA + 8) (SA + 12) [C4 (Z_to_bv 64 sk2)] [CB 4 (re_pad1 e1)] HS _
                    ltac:(cbn [cells_size csize]; glia)).
          apply TP4; [exact ECp|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; clear - Ha; lia. }
      assert (J2' : rw_cells rsegs m4 (SA + 16) [C8 (Z_to_bv 64 (re_buf e1)); C8 (Z_to_bv 64 used2);
                                                 C8 (Z_to_bv 64 (re_cap e1))]).
      { refine (dr_join m4 (SA + 16) (SA + 24) [C8 (Z_to_bv 64 (re_buf e1))]
                  [C8 (Z_to_bv 64 used2); C8 (Z_to_bv 64 (re_cap e1))] _ _ ltac:(cbn [cells_size csize]; glia)).
        - apply TP4; [exact ECb|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; clear - Ha; lia.
        - refine (dr_join m4 (SA + 24) (SA + 32) [C8 (Z_to_bv 64 used2)] [C8 (Z_to_bv 64 (re_cap e1))] HU _
                    ltac:(cbn [cells_size csize]; glia)).
          apply TP4; [exact ECc|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; clear - Ha; lia. }
      assert (J3' : rw_cells rsegs m4 (SA + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1));
                                                 CB 4 (re_pad2 e1)]).
      { apply TP4; [exact EC3|]. intros a Ha. cbn [cells_size csize] in Ha. apply PG; clear - Ha; lia. }
      rewrite SEGS. apply ent_join; [exact K3 | exact K4 | exact J1' | exact J2' | exact J3']. }
    split.
    { apply (entry_okw_rest L1 A1 m1 m4 e1 _ sk2 used2 U2 junk2 MS EK1);
        [ | exact Cp | exact SK | exact LU | exact HU6 | exact NZ | exact LJ | rewrite SEGS; exact HB].
      intros q k a Hq Hk Ha. pose proof (blk_rng _ _ _ _ _ _ M1 Hq) as QR.
      assert (QL : In q ((if re_hp e1 =? 0 then [] else [re_hp e1]) ++ map key_addr (re_keys e1))).
      { apply in_or_app. destruct Hk as [Hk|Hk]; [left | right; exact Hk].
        rewrite Hk, (proj2 (Z.eqb_neq (re_hp e1) 0)) by (clear - QR Hk; lia). left. reflexivity. }
      apply (PB q k a Hq (ENB q QL)); [|exact Ha].
      apply (dx_ng OUT1 (entry_blocks e1 ++ hs_blocks h1) q ND). right. apply in_or_app. left.
      rewrite EBUF. right. exact QL. }
    split.
    { eapply src_at_tr0; [exact MS | exact SR1 | | intros q k Hq _; exact Hq |].
      - intros a Ha. apply PI.
        exact (proj1 (GRP a ltac:(clear - Ha HJ; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
      - intros q k a Hq Hb Ha. exact (PB q k a Hq (HSNB q Hb) (NGH q Hb) Ha). }
    split.
    { eapply others_at_tr; [exact MS | exact OT1 |]. intros i a Hi _ Ha. apply PI.
      exact (proj1 (GRP a ltac:(clear - Ha Hi; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))). }
    split; [exact SM1|].
    split.
    { unfold DLINK. split; [exact L1c|]. split; [exact EUq|]. split; [exact ESKq|].
      split; [rewrite EH; exact L4c|]. split; [rewrite EKA; exact L5c|].
      split; [exact L6c|]. split; [exact L7c|]. split; [exact L8c|]. split; [exact L9c|].
      split; [exact L10c|]. split; [exact L11c | exact WFn]. }
    split.
    { unfold DHIST.
      split; [exact H1g|]. split; [exact H2g|]. split; [exact (proj2 CK2)|].
      split; [exact H3g|]. split; [exact H4g|]. split; [exact H5g|].
      split; [rewrite ENO; unfold dtot; rewrite LINES; exact H6g|].
      split; [rewrite LINES; exact H7g|].
      split; [rewrite EH; exact H8g|].
      split; [rewrite EH, LINES; exact H9g|].
      split; [|exact H10g].
      rewrite EH. rewrite DQ in LN1. cbn [length] in LN1.
      change (pstream (dnext LIVE MX s)) with
        (pstream (dvirt s (dskp s P) (dlH s P) (dlka s P) (dlno s P) (dloc s P))).
      clear - LN1. lia. }
    split; [exact BK1|].
    split.
    { unfold DGLB, brf, eif, dtot. rewrite LINES.
      destruct GL1 as (GC1 & GC2 & GC3 & GC4 & (ev1 & GC5)).
      split; [eapply rw_tr; [exact MS | exact GC1 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
              exact (proj1 (GCP a ltac:(clear - Ha; lia)))|].
      split; [eapply rw_tr; [exact MS | exact GC2 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
              exact (proj1 (GRP a ltac:(clear - Ha; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                        lia)))|].
      split; [eapply rw_tr; [exact MS | exact GC3 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
              exact (proj1 (GRP a ltac:(clear - Ha; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                        lia)))|].
      split; [eapply rw_tr; [exact MS | exact GC4 |]; intros a Ha; apply PI; cbn [cells_size csize] in Ha;
              exact (proj1 (GRP a ltac:(clear - Ha; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *;
                                        lia)))|].
      exists ev1. eapply rw_tr; [exact MS | exact GC5 |]. intros a Ha. apply PI. apply GEI.
      cbn [cells_size csize] in Ha. clear - Ha. lia. }
    assert (DOV : DOUT (dvirt s (dskp s P) (dlH s P) (dlka s P) (dlno s P) (dloc s P)) L1 A1 m4 OUT1 junk1 LB1).
    { destruct OU1 as (OFa & OTa). split.
      - intros LV. destruct (OFa LV) as (OC & OE & OCP & OB). split.
        + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. apply PI. cbn [cells_size csize] in Ha.
          exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
        + split; [exact OE|]. split; [exact OCP|]. intros Cq. destruct (OB Cq) as (OI & OBy). split; [exact OI|].
          eapply by_tr; [exact MS | exact OBy |]. intros a Ha.
          apply (PB OUT CAP a OI); [rewrite <- OE; exact ONB | rewrite <- OE; exact OGN |].
          destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJo)]; [clear - Cq C0; lia|].
          rewrite length_app in Ha. clear - Ha LO LJo. lia.
      - intros LV. destruct (OTa LV) as (OC & OZ). split.
        + eapply rw_tr; [exact MS | exact OC |]. intros a Ha. apply PI. cbn [cells_size csize] in Ha.
          exact (proj1 (GRP a ltac:(clear - Ha; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
        + destruct OZ as [OZ|(Pp & NL & OI & OFr & OBy & LJo)]; [left; exact OZ | right].
          split; [exact Pp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OFr|]. split; [|exact LJo].
          eapply by_tr; [exact MS | exact OBy |]. intros a Ha. apply (PB OUT1 _ a OI ONB OGN).
          assert (LO : Z.of_nat (length O) = NO).
          { destruct OUTD as [(_ & _ & N0 & OE0)|(_ & _ & _ & _ & _ & LO & _)];
              [rewrite OE0; cbn [length]; clear - N0; lia | exact LO]. }
          assert (LLB : Z.of_nat (length LB1) = Z.of_nat (length (with_nul (lines ST0 D ++ drlp s P)))).
          { rewrite <- H7g. unfold bzs. rewrite length_map. reflexivity. }
          rewrite !length_app in Ha. clear - Ha LO LLB H6g LJo. lia. }
    unfold DOUT in DOV |- *. rewrite ENO, EOC. exact DOV. }
  assert (NSA : forall m c cs, ro_agree rsegs m -> rw_cells rsegs m c cs -> SA <= c ->
            c + Z.of_nat (cells_size cs) <= SA + 56 -> rw_cells rsegs (normalize rsegs m) c cs).
  { intros m c cs Hr X Lo Up. apply (rw_cells_normalize rsegs m c cs Hr X). intros i Hi.
    apply (ro_addr_out Bm SEGS); [clear - Lo Up Hi F4 F5 F6 F7 F8; lia | apply g_noimg; clear - Lo Up Hi; lia]. }
  assert (NHI : forall m c cs, ro_agree rsegs m -> rw_cells rsegs m c cs -> 0x21624 <= c ->
            rw_cells rsegs (normalize rsegs m) c cs).
  { intros m c cs Hr X Lo. apply (rw_cells_normalize rsegs m c cs Hr X). intros i Hi.
    pose proof (rw_cells_bound _ _ _ _ X) as RB. apply ro_hi. clear - RB Hi Lo. lia. }
  assert (NBF : forall m c cs, ro_agree rsegs m -> rw_cells rsegs m c cs -> re_buf e1 <= c ->
            c + Z.of_nat (cells_size cs) <= re_buf e1 + re_cap e1 -> rw_cells rsegs (normalize rsegs m) c cs).
  { intros m c cs Hr X Lo Up. apply (rw_cells_normalize rsegs m c cs Hr X). intros i Hi.
    apply (ro_addr_out Bm SEGS); [clear - Lo Up Hi ARITH; lia|].
    replace (c + i) with (re_buf e1 + (c + i - re_buf e1)) by ring.
    apply (blk_noimg _ _ _ _ _ _ _ M1 BI). clear - Lo Up Hi; lia. }
  assert (ECun : rw_cells rsegs (normalize rsegs m1) (SA + 24) [C8 (Z_to_bv 64 (re_used e1))])
    by (apply NSA; [exact RO1r | exact ECu | glia | cbn [cells_size csize]; glia]).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, G8, G20. rewrite SEGS.
    eapply (evt_normalize rsegs); [exact dl_wx | exact RO1r |].
    eapply dr_rest; [exact ECun | apply mem_inv_normalize]. }
  intros ms (can1 & (s1 & (m2' & -> & MU & WM & _ & HU2) & REL & ROS) & EQ).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL2].
  rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R2 & -> & X2).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m2 := ms_mem can1) in *.
  pose proof (sb_back m1 m2' m2 _ RO1r REL2 ROS MU WM) as (MU2 & WM2 & RO2).
  pose proof (rw_cells_of_rel rsegs m2 m2' _ _ REL2 HU2) as HU2r.
  clear MU WM HU2 REL ROS EQ ECAN REL2.
  assert (RT2 : RTL R2) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X2).
  pose proof RT2 as (((P2 & P3 & P4 & P8 & P22 & P25) & P23 & P26) & P27).
  assert (Y1 : getr R2 1 = Z_to_bv 64 0x13e68) by rgw X2.
  assert (Y10 : getr R2 10 = Z_to_bv 64 (re_buf e1)) by rgw X2.
  assert (Y11 : getr R2 11 = Z_to_bv 64 (re_buf e1 + Z.of_nat P)) by rgw X2.
  assert (Y12 : getr R2 12 = Z_to_bv 64 rem) by rgw X2.
  assert (BU1 : rw_cells rsegs m1 (re_buf e1) [CB (length (re_U e1)) (re_U e1)] /\
                rw_cells rsegs m1 (re_buf e1 + Z.of_nat (length (re_U e1)))
                  [CB (length (re_junk e1)) (re_junk e1)]).
  { pose proof BC as BC'. rewrite SEGS in BC'.
    replace (Z.to_nat (re_cap e1)) with (length (re_U e1) + length (re_junk e1))%nat in BC'
      by (clear - K7 BJ ARITH; lia).
    exact (cb_cut2 m1 _ _ _ BC'). }
  destruct BU1 as [BU1 BJ1].
  assert (BU2 : rw_cells rsegs m2 (re_buf e1) [CB (length (re_U e1)) (re_U e1)]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ BU1 MU2 WM2). cbn [disjoint_from cells_size csize].
    clear - ARITH DJBS K7. repeat split; lia. }
  assert (BU2n : rw_cells rsegs (normalize rsegs m2) (re_buf e1) [CB (length (re_U e1)) (re_U e1)]).
  { apply NBF; [exact RO2 | exact BU2 | apply Z.le_refl | cbn [cells_size csize]; clear - ARITH K7; lia]. }
  pose proof MMV as MM. unfold memmove_contract in MM.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Y10, Y11, Y12. rewrite SEGS.
    eapply (evt_normalize rsegs); [exact dl_wx | exact RO2 |].
    apply MM with (U := re_buf e1) (us := re_U e1).
    - destruct BU2n as [[_ Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. split; assumption.
    - clear - ARITH. lia.
    - rewrite !unsigned_lit by (clear - ARITH; lia). clear - ARITH K7. lia.
    - rewrite !unsigned_lit by (clear - ARITH; lia). clear - ARITH K7. lia.
    - rewrite unsigned_lit by (clear - ARITH; lia). clear - ARITH. lia.
    - apply mem_inv_normalize. }
  intros ms (can2 & (s2 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3' &
    -> & MU & WM & _ & UA3) & REL & ROS) & EQ).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL3].
  rewrite ECAN in EQ.
  destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R3 & -> & X3).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  set (m3 := ms_mem can2) in *.
  rewrite !unsigned_lit in MU by (clear - ARITH; lia).
  rewrite !unsigned_lit in UA3 by (clear - ARITH; lia).
  pose proof (sb_back m2 m3' m3 _ RO2 REL3 ROS MU WM) as (MU3 & WM3 & RO3).
  replace (Z.to_nat (re_buf e1 + Z.of_nat P - re_buf e1)) with P in UA3 by glia.
  replace (Z.to_nat (re_buf e1 - re_buf e1)) with 0%nat in UA3 by glia.
  replace (Z.to_nat rem) with (length (re_U e1) - P)%nat in UA3 by glia.
  rewrite (mm_rest (re_U e1) P) in UA3 by glia.
  assert (BM3 : rw_cells rsegs m3 (re_buf e1)
                  [CB (length (skipn P (re_U e1) ++ skipn (length (re_U e1) - P) (re_U e1)))
                      (skipn P (re_U e1) ++ skipn (length (re_U e1) - P) (re_U e1))]).
  { apply (rw_cells_of_rel rsegs m3 m3' _ _ REL3). destruct UA3 as [Hb Hw]. split; [split|].
    - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw. }
  clear MU WM UA3 REL ROS EQ ECAN REL3.
  assert (MU13 : munch [(SA + 24, SA + 32); (re_buf e1, re_buf e1 + rem)] m1 m3).
  { apply (munch_trans _ m1 m2 m3).
    - apply (munch_weaken [(SA + 24, SA + 32)]); [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *.
      clear - Hx. tauto.
    - apply (munch_weaken [(re_buf e1, re_buf e1 + rem)]); [|exact MU3]. intros x Hx. cbn [outside] in Hx |- *.
      clear - Hx. tauto. }
  pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM13.
  assert (MUA3 : munch WA m1 m3).
  { apply (munch_trans _ m1 m2 m3).
    - apply (munch_weaken [(SA + 24, SA + 32)]); [|exact MU2]. intros x Hx. unfold WA in Hx.
      cbn [outside] in Hx |- *. clear - Hx. tauto.
    - apply (munch_weaken [(re_buf e1, re_buf e1 + rem)]); [|exact MU3]. intros x Hx. unfold WA in Hx.
      cbn [outside] in Hx |- *. clear - Hx. tauto. }
  assert (BJ3 : rw_cells rsegs m3 (re_buf e1 + Z.of_nat (length (re_U e1)))
                  [CB (length (re_junk e1)) (re_junk e1)]).
  { apply (rw_cells_transport rsegs _ m1 m3 _ _ BJ1 MU13 WM13). cbn [disjoint_from cells_size csize].
    clear - ARITH DJBS K7 BJ. repeat split; lia. }
  assert (LMM : length (skipn P (re_U e1) ++ skipn (length (re_U e1) - P) (re_U e1)) = length (re_U e1))
    by (rewrite length_app, !length_skipn; glia).
  rewrite <- LMM in BJ3.
  pose proof (cb_join2 m3 _ _ _ BM3 BJ3) as BALL3.
  replace (length (skipn P (re_U e1) ++ skipn (length (re_U e1) - P) (re_U e1)) + length (re_junk e1))%nat
    with (Z.to_nat (re_cap e1)) in BALL3 by (clear - LMM K7 BJ ARITH; lia).
  assert (ECs3 : rw_cells rsegs m3 (SA + 8) [C4 (Z_to_bv 64 (re_skip e1))]).
  { apply (rw_cells_transport rsegs _ m1 m3 _ _ ECs MU13 WM13). cbn [disjoint_from cells_size csize].
    clear - ARITH DJBS. repeat split; lia. }
  assert (HU3 : rw_cells rsegs m3 (SA + 24) [C8 (Z_to_bv 64 rem)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ HU2r MU3 WM3). cbn [disjoint_from cells_size csize].
    clear - ARITH DJBS. repeat split; lia. }
  pose proof FR1 as (j0 & j1 & j2 & j4 & FRs).
  assert (FRr : rw_cells rsegs m1 (S0 - 144)
                  ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED))
    by (rewrite <- SEGS; exact FRs).
  destruct (dr_cut m1 (S0 - 144) (S0 - 144 + 24) [CB 8 j0; CB 8 j1; CB 8 j2]
              ([C8 (Z_to_bv 64 6001); CB 8 j4] ++ SAVED) FRr ltac:(cbn [cells_size csize]; glia)) as [_ FRx].
  destruct (dr_cut m1 (S0 - 144 + 24) (S0 - 144 + 32) [C8 (Z_to_bv 64 6001)] ([CB 8 j4] ++ SAVED) FRx
              ltac:(cbn [cells_size csize]; glia)) as [FR16 _].
  assert (FR3 : rw_cells rsegs m3 (S0 - 144 + 24) [C8 (Z_to_bv 64 6001)]).
  { apply (rw_cells_transport rsegs _ m1 m3 _ _ FR16 MU13 WM13). cbn [disjoint_from cells_size csize].
    clear - ARITH F1 F7 F8. repeat split; lia. }
  assert (ECs3n : rw_cells rsegs (normalize rsegs m3) (SA + 8) [C4 (Z_to_bv 64 (re_skip e1))])
    by (apply NSA; [exact RO3 | exact ECs3 | glia | cbn [cells_size csize]; glia]).
  assert (HU3n : rw_cells rsegs (normalize rsegs m3) (SA + 24) [C8 (Z_to_bv 64 rem)])
    by (apply NSA; [exact RO3 | exact HU3 | glia | cbn [cells_size csize]; glia]).
  assert (FR3n : rw_cells rsegs (normalize rsegs m3) (S0 - 144 + 24) [C8 (Z_to_bv 64 6001)])
    by (apply NHI; [exact RO3 | exact FR3 | glia]).
  assert (RT3 : RTL R3) by (unfold RTL, RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X3).
  pose proof RT3 as (((Q2 & Q3 & Q4 & Q8 & Q22 & Q25) & Q23 & Q26) & Q27).
  rewrite Y1, ret_pc_13e68.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite CF.gestures_end_b.canon_mkst2, CF.gestures_end_b.mkR_of_getr, Q2, Q8. rewrite SEGS.
    eapply (evt_normalize rsegs); [exact dl_wx | exact RO3 |].
    eapply dr_back; [exact ECs3n | exact HU3n | exact FR3n | apply mem_inv_normalize | clear - ARITH; lia]. }
  intros ms (can3 & (s3 & [(LT & ->)|(GE & m4' & -> & MU & WM & _ & HS4 & HU4)] & REL & ROS) & EQ);
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [ECAN REL4]; rewrite ECAN in EQ;
    destruct (CF.gestures_end_b.eqv_mkst2 _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R4 & -> & X4);
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity);
    (assert (RT4 : RTK R4) by (unfold RTK, RT; repeat match goal with |- _ /\ _ => split end; rgw X4)).
  - pose proof (sb_back m3 (normalize rsegs m3) (ms_mem can3) [] RO3 REL4 ROS (munch_refl _ _) (wmono_refl _ _))
      as (MU4 & _ & _).
    assert (ME : ms_mem can3 = m3).
    { apply FunctionalExtensionality.functional_extensionality. intros x. apply MU4. exact I. }
    rewrite ME. apply SR_ret.
    assert (LEN1 : Z.of_nat (length (skipn P (dW s))) <= 6000) by (rewrite length_skipn; glia).
    pose proof BALL3 as BALL1. rewrite <- app_assoc in BALL1.
    apply (FIN R4 m3 (re_skip e1) rem (skipn P (re_U e1)) (skipn (length (re_U e1) - P) (re_U e1) ++ re_junk e1)
             RT4 MUA3 WM13 RO3 K2 ECs3 HU3 BALL1).
    + rewrite length_skipn. glia.
    + glia.
    + apply nz_in. rewrite <- skipn_bzs, EW. apply nz_nth. intros i. rewrite nth_skipn. apply NZP.
      apply Nat.le_add_r.
    + rewrite length_app, !length_skipn. clear - LW K7 BJ ARITH REMD DB1. lia.
    + rewrite EUS, DCH, (ll_le _ LEN1). cbn [fst]. rewrite <- skipn_bzs, EW; reflexivity.
    + rewrite ESS, DCH, (ll_le _ LEN1). cbn [fst snd]. exact L3c.
  - set (m4 := ms_mem can3) in *.
    pose proof (sb_back m3 m4' m4 _ RO3 REL4 ROS MU WM) as (MU4 & WM4 & RO4).
    pose proof (rw_cells_of_rel rsegs m4 m4' _ _ REL4 HS4) as HS4r.
    pose proof (rw_cells_of_rel rsegs m4 m4' _ _ REL4 HU4) as HU4r.
    apply SR_ret.
    assert (LEN2 : 6001 <= Z.of_nat (length (skipn P (dW s)))) by (rewrite length_skipn; glia).
    assert (BALL4 : rw_cells rsegs m4 (re_buf e1) [CB (Z.to_nat (re_cap e1))
                      ((skipn P (re_U e1) ++ skipn (length (re_U e1) - P) (re_U e1)) ++ re_junk e1)]).
    { apply (rw_cells_transport rsegs _ m3 m4 _ _ BALL3 MU4 WM4). cbn [disjoint_from cells_size csize].
      clear - ARITH DJBS. repeat split; lia. }
    assert (MUA4 : munch WA m1 m4).
    { apply (munch_trans _ m1 m3 m4); [exact MUA3|].
      apply (munch_weaken [(SA + 8, SA + 12); (SA + 24, SA + 32)]); [|exact MU4].
      intros x Hx. unfold WA in Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
    apply (FIN R4 m4 1 0 [] ((skipn P (re_U e1) ++ skipn (length (re_U e1) - P) (re_U e1)) ++ re_junk e1)
             RT4 MUA4 (wmono_trans _ _ _ _ WM13 WM4) RO4 (or_intror eq_refl) HS4r HU4r BALL4).
    + reflexivity.
    + glia.
    + intros [].
    + rewrite !length_app, !length_skipn. clear - K7 BJ LW DB1. lia.
    + rewrite EUS, DCH, (ll_gt _ LEN2); reflexivity.
    + rewrite ESS, DCH, (ll_gt _ LEN2); reflexivity.
Qed.

Lemma DLL_bounds : forall s P Q c, DLL s P Q c -> (P <= Q < length (dW s))%nat.
Proof using.
  intros s P Q c (R1 & L1 & A1 & m1 & md1 & e1 & h1 & OUT1 & junk1 & LB1 & D & _ & _ & _ & _ & _ & B & _). exact B.
Qed.

Lemma line_loop : forall k s P Q c, (length (dW s) - P <= k)%nat -> DLL s P Q c ->
  SR segs c (fun c' => exists P', DLR s P' c').
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE.
  induction k as [|k IH]; intros s P Q c K H; pose proof (DLL_bounds s P Q c H) as B; [lia|].
  assert (NX : forall c2, DLN s (S Q) c2 -> SR segs c2 (fun c' => exists P', DLR s P' c')).
  { intros c2 H2. eapply SR_bind; [exact (next_step s (S Q) c2 H2)|]. intros c3 [(Q' & H3)|H3].
    - apply (IH s (S Q) Q' c3); [lia | exact H3].
    - apply SR_ret. exists (S Q). exact H3. }
  eapply SR_bind; [exact (line_test s P Q c H)|]. intros c1 [H1|H1].
  - eapply SR_bind; [exact (seen_step s P Q c1 H1)|]. exact NX.
  - exact (NX c1 H1).
Qed.

Lemma round_step : forall s c, DF s c -> ds_eintr s = false -> ds_pend s <> [] ->
  SR segs c (DI (dnext LIVE MX s)).
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE.
  intros s c H E P.
  eapply SR_bind; [exact (read_step s c H E P)|]. intros c1 H1.
  eapply SR_bind; [exact (scan_start s c1 H1)|]. intros c2 [(Q & H2)|H2].
  - eapply SR_bind; [exact (line_loop _ s 0 Q c2 (le_n _) H2)|]. intros c3 (P' & H3).
    exact (rest_step s P' c3 H3).
  - exact (rest_step s 0 c2 H2).
Qed.

Lemma loop : forall n s c, (dneed s <= n)%nat -> DI s c -> SR segs c DPOST.
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE.
  induction n as [|n IH]; intros s c N H; [unfold dneed in N; lia|].
  eapply SR_bind; [exact (grow_step s c H)|]. intros c1 H1.
  destruct (DF_facts _ _ H1) as (GR & WF & STR).
  destruct (ds_eintr (dgrow s)) eqn:EI.
  - eapply SR_bind; [exact (eintr_step _ c1 H1 EI)|]. intros c2 H2.
    apply (IH (dclr (dgrow s)) c2); [|exact H2].
    pose proof (dneed_dclr (dgrow s) EI) as E. change (dneed (dgrow s)) with (dneed s) in E. lia.
  - destruct (ds_pend (dgrow s)) as [|r0 rs] eqn:PE.
    + exact (exit_step _ c1 H1 EI PE).
    + assert (NE : ds_pend (dgrow s) <> []) by (rewrite PE; discriminate).
      eapply SR_bind; [exact (round_step _ c1 H1 EI NE)|]. intros c2 H2.
      apply (IH (dnext LIVE MX (dgrow s)) c2); [|exact H2].
      destruct (dneed_dnext LIVE MX (dgrow s) GR NE WF STR EI) as [E _].
      change (dneed (dgrow s)) with (dneed s) in E. lia.
Qed.

Lemma run_main : SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 DRAIN) mem (seg_rom segs)) md) DPOST.
Proof using AX BW CBR CCL CDD CEI CERR COUT CTX EHI ELC EOK ERR4 EU FRC FREEPC GCP GEI GRP HE0 HEC HFD HG HJ HND HNH HPL HSK HSW Hbr Hcl Hdd Hei INIT LDC LPC MCH MCP MMV NODUP OTH OUTD PRE RAC RES0 RNC MALPC RO0 ROOM SCM SDC SEGS SLACK SLC SLN SNC SRC0 SRR TPE.
  eapply SR_bind; [exact entry_step|]. intros c H.
  exact (loop _ (drain_init NO CAP e h) c (le_n _) H).
Qed.

End Run.
End DH.

Theorem drain_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (Bm : malloc_syms) (API : AllocAPI Bm) (F : ResFormT) :
  AllocExtra Bm (aa_MR API) -> ctx_owned Bm API -> block_slack_present Bm API -> blocks_writable Bm API ->
  errno_unowned Bm API -> ms_free Bm = 0x15f4c ->
  (forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A))) ->
  realloc_contract_rt Bm API F 0x178f8 -> realloc_null_contract_rt Bm API F 0x178f8 -> ms_malloc Bm = 0x1608c ->
  __errno_location_contract ->
  send_line_contract Bm API F -> list_push_contract Bm API F -> strndup_contract_rt Bm API F ->
  free_contract_rt Bm API F -> memchr_contract -> memmove_contract -> memcpy_contract -> strrchr_contract ->
  strcmp_contract -> strncmp_contract -> strlen_contract -> list_drop_contract Bm API F ->
  drain_contract Bm API F.
Proof.
  intros AX CTX SLACK BW EU FREEPC NODUP RAC RNC MALPC ELC SLC LPC SDC FRC MCH MMV MCP SRR SCM SNC SLN LDC.
  unfold drain_contract. intros L A regs mem md bnd e h j fs os G O junk cl br dd ei mx nout cap out. cbv zeta.
  intros H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26
    H27 H28 H29 H30 H31 H32 H33 H34 H35 H36.
  exact (run_main Bm API F AX CTX SLACK BW EU FREEPC NODUP RAC RNC MALPC ELC SLC LPC SDC FRC MCH MMV MCP SRR SCM SNC SLN LDC
    L A regs mem md bnd e h j fs os G O junk cl br dd ei mx nout cap out H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11
    H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36).
Qed.
