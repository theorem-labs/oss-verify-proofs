(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_scan1 Z_tr_st1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma st_step_keep : forall f X t mc n prevlen nextlen count mx mn,
  1 <= mn -> n <= mc -> count + 1 < mx -> nextlen = Len X t (n + 1) ->
  send_tree_loop (S f) X t mc n prevlen nextlen count mx mn = send_tree_loop f X t mc (n + 1) prevlen (Len X t (n + 1)) (count + 1) mx mn.
Proof.
  intros f X t mc n prevlen nextlen count mx mn Hmn Hn Hc E. rewrite send_loop_S by exact Hmn. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Hn), (proj2 (Z.ltb_lt _ _) Hc), (proj2 (Z.eqb_eq _ _) E). reflexivity.
Qed.

Lemma st_step_emit : forall f X t mc n prevlen nextlen count mx mn,
  1 <= mn -> n <= mc -> (mx <= count + 1 \/ nextlen <> Len X t (n + 1)) ->
  send_tree_loop (S f) X t mc n prevlen nextlen count mx mn
  = send_tree_loop f (sbs_run X (st_calls X mn nextlen prevlen (count + 1))) t mc (n + 1) nextlen (Len X t (n + 1)) 0
      (fst (tree_counts nextlen (Len X t (n + 1)))) (snd (tree_counts nextlen (Len X t (n + 1)))).
Proof.
  intros f X t mc n prevlen nextlen count mx mn Hmn Hn Hc. rewrite send_loop_S by exact Hmn. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Hn).
  replace ((count + 1 <? mx) && (nextlen =? Len X t (n + 1))) with false.
  2:{ symmetry. apply andb_false_iff. destruct Hc as [Hc|Hc]; [left; apply Z.ltb_ge; exact Hc| right; apply Z.eqb_neq; exact Hc]. }
  destruct (tree_counts nextlen (Len X t (n + 1))); reflexivity.
Qed.

Lemma st_ok_keep : forall P f X t mc n prevlen nextlen count mx mn,
  n <= mc -> count + 1 < mx -> nextlen = Len X t (n + 1) ->
  send_tree_ok P (S f) X t mc n prevlen nextlen count mx mn -> send_tree_ok P f X t mc (n + 1) prevlen (Len X t (n + 1)) (count + 1) mx mn.
Proof.
  intros P f X t mc n prevlen nextlen count mx mn Hn Hc E H. cbn [send_tree_ok] in H. cbv zeta in H.
  rewrite (proj2 (Z.leb_le _ _) Hn), (proj2 (Z.ltb_lt _ _) Hc), (proj2 (Z.eqb_eq _ _) E) in H. exact H.
Qed.

Lemma st_ok_emit : forall P f X t mc n prevlen nextlen count mx mn,
  n <= mc -> (mx <= count + 1 \/ nextlen <> Len X t (n + 1)) ->
  send_tree_ok P (S f) X t mc n prevlen nextlen count mx mn ->
  sbs_ok P X (st_calls X mn nextlen prevlen (count + 1))
  /\ send_tree_ok P f (sbs_run X (st_calls X mn nextlen prevlen (count + 1))) t mc (n + 1) nextlen (Len X t (n + 1)) 0
       (fst (tree_counts nextlen (Len X t (n + 1)))) (snd (tree_counts nextlen (Len X t (n + 1)))).
Proof.
  intros P f X t mc n prevlen nextlen count mx mn Hn Hc H. cbn [send_tree_ok] in H. cbv zeta in H.
  rewrite (proj2 (Z.leb_le _ _) Hn) in H.
  replace ((count + 1 <? mx) && (nextlen =? Len X t (n + 1))) with false in H.
  2:{ symmetry. apply andb_false_iff. destruct Hc as [Hc|Hc]; [left; apply Z.ltb_ge; exact Hc| right; apply Z.eqb_neq; exact Hc]. }
  destruct (tree_counts nextlen (Len X t (n + 1))); exact H.
Qed.

Lemma tree_counts_0 : forall c, tree_counts c 0 = (138, 3).
Proof. reflexivity. Qed.
Lemma tree_counts_nz : forall c n, n <> 0 -> tree_counts c n = (if c =? n then 6 else 7, if c =? n then 3 else 4).
Proof. intros c n H. unfold tree_counts. rewrite (proj2 (Z.eqb_neq _ _) H). destruct (c =? n); reflexivity. Qed.


Definition st_trip_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 nextlen' : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists s6 s7 s8 wbb PB' PD' BB' BV' prevlen' count' mx' mn' pcx m',
    ms' = MS (stR L T (mc + 1) n1 nextlen' ra sp gp tp (wz prevlen') (wz count') (wz count') (wz mx') (wz mn') (wz prevlen') s6 s7 s8 s9 s10 s11)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = send_tree_loop f (upd4 s PB' PD' BB' BV') t mc n1 prevlen' nextlen' count' mx' mn'
    /\ send_tree_ok 65536 f (upd4 s PB' PD' BB' BV') t mc n1 prevlen' nextlen' count' mx' mn'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4)
    /\ -1 <= prevlen' <= 15
    /\ ((pcx = 0x1caa0 /\ n1 <= mc) \/ (pcx = 0x1cf44 /\ n1 = mc + 1)).

Lemma st_latch : forall (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 nextlen' : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen' count' mx' mn' : Z) (wbb : word)
    (ra sp gp tp s1 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  R = send_tree_loop f (upd4 s PB PD BB BV) t mc n1 prevlen' nextlen' count' mx' mn' ->
  send_tree_ok 65536 f (upd4 s PB PD BB BV) t mc n1 prevlen' nextlen' count' mx' mn' ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count' < mx' -> (mx' = 138 \/ mx' = 6 \/ mx' = 7) -> (mn' = 3 \/ mn' = 4) -> -1 <= prevlen' <= 15 ->
  0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  evt psegs (st_trip_post L s t T mc n1 nextlen' f R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T (mc + 1) n1 nextlen' ra sp gp tp (wz prevlen') s1 (wz count') (wz mx') (wz mn') s5 s6 s7 s8 s9 s10 s11) F (wz 0x1ca94) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI MU WM ER OK RBV RPD Rc Rmx Rmn Rpl Rn Rmc. unfold stR.
  zs2. zs2. zstep. br_cases_s K.
  - apply evt_done. unfold st_trip_post, stR. exists s6, s7, s8, wbb, PB, PD, BB, BV, prevlen', count', mx', mn'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EMH|]. split; [exact HBB|].
    split; [exact ER|]. split; [exact OK|]. split; [exact RBV|]. split; [exact RPD|]. split; [exact Rc|].
    split; [exact Rmx|]. split; [exact Rmn|]. split; [exact Rpl|]. right. split; [reflexivity| lia].
  - apply evt_done. unfold st_trip_post, stR. exists s6, s7, s8, wbb, PB, PD, BB, BV, prevlen', count', mx', mn'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EMH|]. split; [exact HBB|].
    split; [exact ER|]. split; [exact OK|]. split; [exact RBV|]. split; [exact RPD|]. split; [exact Rc|].
    split; [exact Rmx|]. split; [exact Rmn|]. split; [exact Rpl|]. left. split; [reflexivity| lia].
Qed.

Lemma st_tail : forall (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 curlen nextlen' : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV pcx : Z) (wbb : word)
    (ra sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  R = send_tree_loop f (upd4 s PB PD BB BV) t mc n1 curlen nextlen' 0 (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  send_tree_ok 65536 f (upd4 s PB PD BB BV) t mc n1 curlen nextlen' 0 (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= curlen <= 15 -> 0 <= nextlen' < 65536 -> 0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  ((pcx = 0x1cb64 /\ nextlen' <> 0) \/ (pcx = 0x1cf38 /\ nextlen' = 0)) ->
  evt psegs (st_trip_post L s t T mc n1 nextlen' f R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T (mc + 1) n1 nextlen' ra sp gp tp (wz curlen) s1 (wz 0) s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz pcx) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI MU WM ER OK RBV RPD Rcl Rnl Rn Rmc [[-> NZ]|[-> ZE]]; unfold stR.
  - rewrite tree_counts_nz in ER, OK by exact NZ. cbn [fst snd] in ER, OK.
    do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn.
    eapply (st_latch L s t T mc n1 nextlen' f R m0 PB PD BB BV curlen 0 (if curlen =? nextlen' then 6 else 7) (if curlen =? nextlen' then 3 else 4) wbb);
      try eassumption; try lia; destruct (curlen =? nextlen'); auto; lia.
  - subst nextlen'. rewrite tree_counts_0 in ER, OK. cbn [fst snd] in ER, OK.
    do 3 zs2.
    eapply (st_latch L s t T mc n1 0 f R m0 PB PD BB BV curlen 0 138 3 wbb); try eassumption; try lia; auto.
Qed.
