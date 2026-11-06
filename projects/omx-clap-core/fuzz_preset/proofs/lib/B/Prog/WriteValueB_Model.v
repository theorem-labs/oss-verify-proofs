(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d, twin c90d4fa54d43), lane WriteValueB
   (a Theorem Labs lane): the PURE writer-model lemmas the image-B' write_value walk composes, over the batch kit's writer texts (the
   batch cut 7cdbb61b5fa0: lib/A/PRH_FnWriter.v, lib/A/PRH_Base.v). No machine state
   is stepped and no image is named here.
   PORTED from a Theorem Labs lane's WalkS7a files (a working branch 7819c4b4583: lib/A/Prog/S7a_WriterRet.v
   blob 29e79f90789a, lib/A/Prog/S7a_WriterLive.v blob 4a32ca8f73b9): the model's steps and the room count, the run
   events (prhW_evs_len, prhWriter_ev_at), the position along a run (prhWriter_put_pos, prhWriter_ret_pos, _nil,
   _step), the doubling-chain and text-length lemmas (:907-909).
   The batch kit's REBIND (2026-10-30), each change forced by the batch kit's texts and nothing else:
   - prh_oks has two more parameters (ns, the calls' requests; most, g_most) and a refusal sets g_ran_out only at a
     request <= most; the writer texts' posts state prh_granted (DEAD-PUT and its kin), and prhWriter_ret_ok gained the refused-
     grow arm and the refusal peak prhWriter_rpeak. This walk composes only granted runs: prhW_oksg (the chosen-
     failure conjunct, prh_granted, g_ran_out kept) and prhWriter_blk (the granted arms) are its carried form;
     prhWriter_ret_ok_g / prhWriter_ret_ok_of_g convert from / to the batch kit's prhWriter_ret_ok, binding prh_oks's ns to the
     text's own prhWriter_reqs ok st P and most to its own prh_ledger's most;
   - tput_specX's NULL arm keeps the position with the callee's history (`exists hist'`);
   - the entry live sum (LIVE_<fn>, prhWriter_live) is gone: a callee takes prh_live_evs over its own events and
     prh_cons_from over their number, supplied from the caller's by prhW_live_mid / prhW_cons_mid (and _pre).
   Numerals: 2 ^ 64 (WORD range); 4096 (LENGTH: a doubling chain's first capacity, prhWL_base); 24 / 4 (LENGTH: the
   failed field of the out struct). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Local Open Scope Z_scope.

(* ======== S7a_WriterRet.v (blob 29e79f90789a), whole; Section c takes the #102 ledger cells most / own ======== *)
(* ---- the room count ---- *)
(* the model's steps: a put that does not grow keeps every field but the text; a grow adds one call, steps the
   counter by one (mod 2 ^ 64), and is chosen (cnt = fail: the bit is ignored), accepted (bit true) or refused *)
Lemma prhW_putN_cons_grow : forall ok st b P, prhWriter_grows st b = true ->
  prhWriter_putN ok st (b :: P) = prhWriter_putN (tl ok) (prhWriter_put1 (hd true ok) st b) P.
Proof. intros ok st b P H. cbn [prhWriter_putN]. rewrite H. reflexivity. Qed.

Lemma prhW_putN_cons_nogrow : forall ok st b P, prhWriter_grows st b = false ->
  prhWriter_putN ok st (b :: P) = prhWriter_putN ok (WriterApp.put1 st b) P.
Proof. intros ok st b P H. cbn [prhWriter_putN]. rewrite H. reflexivity. Qed.

Lemma prhW_nogrow_f : forall st b, prhWriter_grows st b = false ->
  WriterApp.w_failed (WriterApp.put1 st b) = WriterApp.w_failed st /\
  WriterApp.w_cap (WriterApp.put1 st b) = WriterApp.w_cap st /\
  WriterApp.w_cnt (WriterApp.put1 st b) = WriterApp.w_cnt st /\
  WriterApp.w_fail (WriterApp.put1 st b) = WriterApp.w_fail st /\
  WriterApp.w_calls (WriterApp.put1 st b) = WriterApp.w_calls st.
Proof.
  intros st b H. unfold prhWriter_grows, prhWriter_need in H.
  destruct (Z.eqb_spec (WriterApp.w_failed st) 0) as [E|E].
  - try rewrite (proj2 (Z.eqb_eq _ _) E) in H. cbn [andb] in H.
    assert (Hp : WriterApp.put1 st b = WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st)
                   (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_calls st)).
    { unfold WriterApp.put1. rewrite (proj2 (Z.eqb_eq _ _) E). cbn [negb].
      rewrite (proj2 (Z.leb_le _ _) (proj1 (Z.ltb_ge _ _) H)). reflexivity. }
    rewrite Hp. cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    rewrite E. repeat split; reflexivity.
  - assert (Hp : WriterApp.put1 st b = st).
    { unfold WriterApp.put1. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. }
    rewrite Hp. repeat split; reflexivity.
Qed.

Lemma prhW_put1_grow_calls : forall okb st b, prhWriter_grows st b = true ->
  WriterApp.w_calls (prhWriter_put1 okb st b) =
    WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)].
Proof.
  intros okb st b Hg. unfold prhWriter_put1. rewrite Hg.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [|destruct okb]; reflexivity.
Qed.

Lemma prhW_put1_grow_cnt : forall okb st b, prhWriter_grows st b = true ->
  WriterApp.w_cnt (prhWriter_put1 okb st b) = (WriterApp.w_cnt st + 1) mod 2 ^ 64.
Proof.
  intros okb st b Hg. unfold prhWriter_put1. rewrite Hg.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [|destruct okb]; reflexivity.
Qed.

Lemma prhW_put1_grow_cases : forall okb st b, prhWriter_grows st b = true ->
  (WriterApp.w_cnt st = WriterApp.w_fail st /\ WriterApp.w_failed (prhWriter_put1 okb st b) = 1 /\
   WriterApp.w_cap (prhWriter_put1 okb st b) = WriterApp.w_cap st) \/
  (WriterApp.w_cnt st <> WriterApp.w_fail st /\ okb = true /\
   WriterApp.w_failed (prhWriter_put1 okb st b) = 0 /\
   WriterApp.w_fail (prhWriter_put1 okb st b) = WriterApp.w_fail st /\
   WriterApp.w_cap (prhWriter_put1 okb st b) = WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)) \/
  (WriterApp.w_cnt st <> WriterApp.w_fail st /\ okb = false /\
   WriterApp.w_failed (prhWriter_put1 okb st b) = 1 /\
   WriterApp.w_fail (prhWriter_put1 okb st b) = WriterApp.w_fail st /\
   WriterApp.w_cap (prhWriter_put1 okb st b) = WriterApp.w_cap st).
Proof.
  intros okb st b Hg. unfold prhWriter_put1. rewrite Hg.
  destruct (Z.eqb_spec (WriterApp.w_cnt st) (WriterApp.w_fail st)) as [E|E].
  - left. cbn [WriterApp.w_failed WriterApp.w_cap]. split; [exact E|]. split; reflexivity.
  - right. destruct okb.
    + left. cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_fail].
      split; [exact E|]. repeat split; reflexivity.
    + right. cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_fail].
      split; [exact E|]. repeat split; reflexivity.
Qed.

Lemma prhW_put1_chosen : forall okb okb' st b, WriterApp.w_cnt st = WriterApp.w_fail st ->
  prhWriter_put1 okb st b = prhWriter_put1 okb' st b.
Proof.
  intros okb okb' st b E. unfold prhWriter_put1.
  destruct (prhWriter_grows st b); [|reflexivity].
  rewrite (proj2 (Z.eqb_eq _ _) E). reflexivity.
Qed.

(* a failed state stays put *)
Lemma prhW_putN_failed : forall P ok st, WriterApp.w_failed st <> 0 -> prhWriter_putN ok st P = st.
Proof.
  induction P as [|b P IH]; intros ok st H; [reflexivity|].
  assert (Hg : prhWriter_grows st b = false).
  { unfold prhWriter_grows. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. }
  rewrite (prhW_putN_cons_nogrow ok st b P Hg).
  assert (Hp : WriterApp.put1 st b = st).
  { unfold WriterApp.put1. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. }
  rewrite Hp. apply IH. exact H.
Qed.

Lemma prhW_calls_le : forall P ok st,
  (length (WriterApp.w_calls st) <= length (WriterApp.w_calls (prhWriter_putN ok st P)))%nat.
Proof.
  induction P as [|b P IH]; intros ok st; [apply le_n|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok st b P Hg).
    specialize (IH (tl ok) (prhWriter_put1 (hd true ok) st b)).
    rewrite (prhW_put1_grow_calls (hd true ok) st b Hg), length_app in IH. cbn [length] in IH. lia.
  - rewrite (prhW_putN_cons_nogrow ok st b P Hg).
    specialize (IH ok (WriterApp.put1 st b)).
    destruct (prhW_nogrow_f st b Hg) as (_ & _ & _ & _ & Hc). rewrite Hc in IH. exact IH.
Qed.

(* the call count, step by step *)
Lemma prhW_k_nil : forall ok st, prhWriter_k ok st [] = 0%nat.
Proof. intros ok st. unfold prhWriter_k. cbn [prhWriter_putN]. lia. Qed.

Lemma prhW_k_grow : forall ok st b P, prhWriter_grows st b = true ->
  prhWriter_k ok st (b :: P) = S (prhWriter_k (tl ok) (prhWriter_put1 (hd true ok) st b) P).
Proof.
  intros ok st b P Hg. unfold prhWriter_k. rewrite (prhW_putN_cons_grow ok st b P Hg).
  pose proof (prhW_calls_le P (tl ok) (prhWriter_put1 (hd true ok) st b)) as H.
  rewrite (prhW_put1_grow_calls (hd true ok) st b Hg), length_app in H |- *. cbn [length] in H |- *. lia.
Qed.

Lemma prhW_k_nogrow : forall ok st b P, prhWriter_grows st b = false ->
  prhWriter_k ok st (b :: P) = prhWriter_k ok (WriterApp.put1 st b) P.
Proof.
  intros ok st b P Hg. unfold prhWriter_k. rewrite (prhW_putN_cons_nogrow ok st b P Hg).
  destruct (prhW_nogrow_f st b Hg) as (_ & _ & _ & _ & Hc). rewrite Hc. reflexivity.
Qed.

Lemma prhW_k_failed : forall ok st P, WriterApp.w_failed st <> 0 -> prhWriter_k ok st P = 0%nat.
Proof. intros ok st P H. unfold prhWriter_k. rewrite (prhW_putN_failed P ok st H). lia. Qed.

(* outcome-list indexing *)
Lemma prhW_nth0 : forall l : list bool, nth 0 l true = hd true l.
Proof. intros [|x l]; reflexivity. Qed.

Lemma prhW_nth_tl : forall (l : list bool) i, nth i (tl l) true = nth (S i) l true.
Proof. intros [|x l] i; [destruct i|]; reflexivity. Qed.

Lemma prhW_skipn_S : forall (l : list bool) n, skipn (S n) l = skipn n (tl l).
Proof. intros [|x l] n; [destruct n|]; reflexivity. Qed.

Lemma prhW_skipn_nil : forall n, skipn n (@nil bool) = (@nil bool).
Proof. intros [|n]; reflexivity. Qed.

Lemma prhW_nth_skipn : forall n (l : list bool) j, nth j (skipn n l) true = nth (n + j) l true.
Proof.
  induction n as [|n IH]; intros l j; [reflexivity|].
  destruct l as [|x l]; [destruct j; reflexivity|].
  exact (IH l j).
Qed.

Lemma prhW_nth_map_seq : forall (f : nat -> bool) n i,
  nth i (map f (seq 0 n)) true = if (i <? n)%nat then f i else true.
Proof.
  intros f n i. destruct (Nat.ltb_spec i n) as [H|H].
  - rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; exact H).
    rewrite map_nth, seq_nth by exact H. reflexivity.
  - rewrite nth_overflow; [reflexivity|]. rewrite length_map, length_seq. exact H.
Qed.

(* P1 ++ P2: the run of P2 starts at P1's end state with the outcomes left after P1's calls *)
Lemma prhW_putN_app : forall P1 P2 ok st,
  prhWriter_putN ok st (P1 ++ P2) =
    prhWriter_putN (skipn (prhWriter_k ok st P1) ok) (prhWriter_putN ok st P1) P2.
Proof.
  induction P1 as [|b P1 IH]; intros P2 ok st.
  - rewrite prhW_k_nil. reflexivity.
  - rewrite <- app_comm_cons.
    destruct (prhWriter_grows st b) eqn:Hg.
    + rewrite (prhW_putN_cons_grow ok st b (P1 ++ P2) Hg), (prhW_putN_cons_grow ok st b P1 Hg),
        (prhW_k_grow ok st b P1 Hg), prhW_skipn_S.
      apply IH.
    + rewrite (prhW_putN_cons_nogrow ok st b (P1 ++ P2) Hg), (prhW_putN_cons_nogrow ok st b P1 Hg),
        (prhW_k_nogrow ok st b P1 Hg).
      apply IH.
Qed.

Lemma prhW_k_app : forall P1 P2 ok st,
  prhWriter_k ok st (P1 ++ P2) =
    (prhWriter_k ok st P1 + prhWriter_k (skipn (prhWriter_k ok st P1) ok) (prhWriter_putN ok st P1) P2)%nat.
Proof.
  intros P1 P2 ok st.
  pose proof (prhW_putN_app P1 P2 ok st) as E.
  pose proof (prhW_calls_le P1 ok st) as H1.
  pose proof (prhW_calls_le P2 (skipn (prhWriter_k ok st P1) ok) (prhWriter_putN ok st P1)) as H2.
  set (ok2 := skipn (prhWriter_k ok st P1) ok) in *. clearbody ok2.
  unfold prhWriter_k. rewrite E. lia.
Qed.

(* under any outcomes a run either follows the all-accepting run or ends failed *)
Lemma prhW_putN_ok_or_failed : forall P ok st,
  prhWriter_putN ok st P = prhWriter_putN [] st P \/ WriterApp.w_failed (prhWriter_putN ok st P) <> 0.
Proof.
  induction P as [|b P IH]; intros ok st; [left; reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok st b P Hg), (prhW_putN_cons_grow [] st b P Hg). cbn [tl hd].
    destruct (prhW_put1_grow_cases (hd true ok) st b Hg) as [(Hc & _) | [(Hc & Ho & _) | (Hc & Ho & Hf & _)]].
    + rewrite (prhW_put1_chosen (hd true ok) true st b Hc). apply IH.
    + rewrite Ho. apply IH.
    + right. rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b)) by lia. lia.
  - rewrite (prhW_putN_cons_nogrow ok st b P Hg), (prhW_putN_cons_nogrow [] st b P Hg). apply IH.
Qed.

(* ---- THE RUN EVENTS OF A RUN OF PUTS, counted (the prhWriter_evs, PRH_FnWriter.v:162-178 @5f7cd294e4b6: one event
   per GRANTED grow). Their number is a function of the start and the end state: the run's fuzz_realloc calls
   (prhWriter_k) less the one call that left the writer failed, if the run ended failed. So a caller whose composed
   outcome list comes from prhW_app_model (only its end state is known) still knows the exact advance. ---- *)
Section ev. Context {cp : CfParams}.
Lemma prhW_evs_len : forall P ok st,
  (length (prhWriter_evs ok st P) +
   (if (WriterApp.w_failed st =? 0)%Z && negb (WriterApp.w_failed (prhWriter_putN ok st P) =? 0)%Z then 1 else 0))%nat =
  prhWriter_k ok st P.
Proof.
  induction P as [|b P IH]; intros ok st.
  - cbn [prhWriter_evs prhWriter_putN length]. rewrite prhW_k_nil.
    destruct (WriterApp.w_failed st =? 0); reflexivity.
  - destruct (prhWriter_grows st b) eqn:Hg.
    + cbn [prhWriter_evs]. rewrite Hg, (prhW_putN_cons_grow ok st b P Hg), (prhW_k_grow ok st b P Hg).
      assert (Hf : WriterApp.w_failed st = 0).
      { unfold prhWriter_grows in Hg. apply andb_prop in Hg. destruct Hg as (Hg' & _). apply Z.eqb_eq in Hg'. exact Hg'. }
      rewrite (proj2 (Z.eqb_eq _ _) Hf).
      destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
        as [(Hc & Ho & _) | [(Hc & Hok & Ho & _) | (Hc & Hok & Ho & _)]].
      * (* the allocation set to fail: no event, the writer failed *)
        rewrite (proj2 (Z.eqb_eq _ _) Hc). cbn [orb app].
        rewrite (prhWriter_evs_failed P (tl ok) (prhWriter_put1 (hd true ok) st b) ltac:(lia)),
          (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b) ltac:(lia)),
          (prhW_k_failed (tl ok) (prhWriter_put1 (hd true ok) st b) P ltac:(lia)), Ho.
        reflexivity.
      * (* granted: one event *)
        rewrite (proj2 (Z.eqb_neq _ _) Hc). rewrite Hok in Ho |- *. cbn [orb negb app length].
        specialize (IH (tl ok) (prhWriter_put1 true st b)). rewrite (proj2 (Z.eqb_eq _ _) Ho) in IH.
        revert IH.
        destruct (WriterApp.w_failed (prhWriter_putN (tl ok) (prhWriter_put1 true st b) P) =? 0);
          cbn [andb negb]; intro IH; lia.
      * (* refused: no event, the writer failed *)
        rewrite (proj2 (Z.eqb_neq _ _) Hc). rewrite Hok in Ho |- *. cbn [orb negb app].
        rewrite (prhWriter_evs_failed P (tl ok) (prhWriter_put1 false st b) ltac:(lia)),
          (prhW_putN_failed P (tl ok) (prhWriter_put1 false st b) ltac:(lia)),
          (prhW_k_failed (tl ok) (prhWriter_put1 false st b) P ltac:(lia)), Ho.
        reflexivity.
    + cbn [prhWriter_evs]. rewrite Hg, (prhW_putN_cons_nogrow ok st b P Hg), (prhW_k_nogrow ok st b P Hg).
      destruct (prhW_nogrow_f st b Hg) as (Hfe & _). rewrite <- Hfe. apply IH.
Qed.

(* the next put's event premise (tput_specX, PRH_FnWriter.v:384-388 @5f7cd294e4b6) at the exact advance after the
   puts PP under the outcomes ok, from the caller's ENTRY premise over all its puts (all granted) *)
Lemma prhWriter_ev_at : forall rp_sm rp_x rp_os rp_i rp_c st PP bs R ok,
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (PP ++ bs :: R)) ->
  rp_c = (rp_i + length (prhWriter_evs ok st PP))%nat ->
  prhWriter_grows (prhWriter_putN ok st PP) bs = true ->
  WriterApp.w_cnt (prhWriter_putN ok st PP) <> WriterApp.w_fail (prhWriter_putN ok st PP) ->
  nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_c = Some (prhWriter_ev (prhWriter_putN ok st PP) bs).
Proof.
  intros rp_sm rp_x rp_os rp_i rp_c st PP bs R ok HE -> Hg Hc.
  assert (Hf : WriterApp.w_failed (prhWriter_putN ok st PP) = 0).
  { unfold prhWriter_grows in Hg. apply andb_prop in Hg. destruct Hg as (Hg' & _). apply Z.eqb_eq in Hg'. exact Hg'. }
  assert (Hst : prhWriter_putN ok st PP = prhWriter_putN [] st PP).
  { destruct (prhW_putN_ok_or_failed PP ok st) as [E|E]; [exact E | contradiction]. }
  assert (HL : length (prhWriter_evs ok st PP) = length (prhWriter_evs [] st PP)).
  { pose proof (prhW_evs_len PP ok st) as L1. pose proof (prhW_evs_len PP [] st) as L2.
    assert (Hk : prhWriter_k ok st PP = prhWriter_k [] st PP) by (unfold prhWriter_k; rewrite Hst; reflexivity).
    rewrite <- Hst in L2. rewrite (proj2 (Z.eqb_eq _ _) Hf) in L1, L2.
    revert L1 L2. destruct (WriterApp.w_failed st =? 0); cbn [andb negb]; intros L1 L2; lia. }
  rewrite HL. rewrite prhWriter_evs_app0 in HE. apply prh_run_at_app_iff in HE. destruct HE as (_ & HE).
  rewrite Hst in Hg, Hc |- *. cbn [prhWriter_evs hd tl] in HE.
  rewrite Hg, (proj2 (Z.eqb_neq _ _) Hc) in HE. cbn [orb negb] in HE.
  apply prh_run_at_app_iff in HE. destruct HE as (HE & _).
  apply prh_run_at_one. exact HE.
Qed.
End ev.

Lemma prhW_k_le : forall P ok st, (prhWriter_k ok st P <= prhWriter_k [] st P)%nat.
Proof.
  induction P as [|b P IH]; intros ok st.
  - rewrite !prhW_k_nil. apply le_n.
  - destruct (prhWriter_grows st b) eqn:Hg.
    + rewrite (prhW_k_grow ok st b P Hg), (prhW_k_grow [] st b P Hg). cbn [tl hd].
      destruct (prhW_put1_grow_cases (hd true ok) st b Hg) as [(Hc & _) | [(Hc & Ho & _) | (Hc & Ho & Hf & _)]].
      * rewrite (prhW_put1_chosen (hd true ok) true st b Hc).
        specialize (IH (tl ok) (prhWriter_put1 true st b)). lia.
      * rewrite Ho. specialize (IH (tl ok) (prhWriter_put1 true st b)). lia.
      * rewrite (prhW_k_failed (tl ok) (prhWriter_put1 (hd true ok) st b) P) by lia. lia.
    + rewrite (prhW_k_nogrow ok st b P Hg), (prhW_k_nogrow [] st b P Hg). apply IH.
Qed.


(* the calls a run makes never exceed the all-accepting run's *)
Lemma prhWriter_k_le_ngrow : forall ok st P, (prhWriter_k ok st P <= prhWriter_ngrow st P)%nat.
Proof. intros ok st P. unfold prhWriter_ngrow. apply prhW_k_le. Qed.

(* the all-accepting count of P1 ++ P2 covers P1's plus P2's from the actual state after P1 under any outcomes *)
Lemma prhWriter_ngrow_app_le : forall ok st P1 P2,
  (prhWriter_ngrow st P1 + prhWriter_ngrow (prhWriter_putN ok st P1) P2 <= prhWriter_ngrow st (P1 ++ P2))%nat.
Proof.
  intros ok st P1 P2. unfold prhWriter_ngrow.
  rewrite (prhW_k_app P1 P2 [] st), prhW_skipn_nil.
  enough (H : (prhWriter_k [] (prhWriter_putN ok st P1) P2 <= prhWriter_k [] (prhWriter_putN [] st P1) P2)%nat)
    by lia.
  destruct (prhW_putN_ok_or_failed P1 ok st) as [E|E].
  - rewrite E. apply le_n.
  - rewrite (prhW_k_failed [] (prhWriter_putN ok st P1) P2 E). apply Nat.le_0_l.
Qed.

(* ---- the composition's model facts ---- *)

(* a run with no call keeps the counter and the allocation set to fail *)
Lemma prhW_k0 : forall P ok st, prhWriter_k ok st P = 0%nat ->
  WriterApp.w_cnt (prhWriter_putN ok st P) = WriterApp.w_cnt st /\
  WriterApp.w_fail (prhWriter_putN ok st P) = WriterApp.w_fail st.
Proof.
  induction P as [|b P IH]; intros ok st Hk; [split; reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_k_grow ok st b P Hg) in Hk. discriminate Hk.
  - rewrite (prhW_k_nogrow ok st b P Hg) in Hk. rewrite (prhW_putN_cons_nogrow ok st b P Hg).
    destruct (IH ok (WriterApp.put1 st b) Hk) as [H1 H2].
    destruct (prhW_nogrow_f st b Hg) as (_ & _ & Hc & Hf & _).
    rewrite H1, H2, Hc, Hf. split; reflexivity.
Qed.

(* a run with k > 0 calls steps the counter k times, with the 2 ^ 64 wrap *)
Lemma prhW_kpos : forall P ok st, (0 < prhWriter_k ok st P)%nat ->
  WriterApp.w_cnt (prhWriter_putN ok st P) = (WriterApp.w_cnt st + Z.of_nat (prhWriter_k ok st P)) mod 2 ^ 64.
Proof.
  induction P as [|b P IH]; intros ok st Hk.
  - rewrite prhW_k_nil in Hk. lia.
  - destruct (prhWriter_grows st b) eqn:Hg.
    + rewrite (prhW_k_grow ok st b P Hg), (prhW_putN_cons_grow ok st b P Hg).
      destruct (Nat.eq_dec (prhWriter_k (tl ok) (prhWriter_put1 (hd true ok) st b) P) 0) as [E|E].
      * rewrite (proj1 (prhW_k0 P _ _ E)), (prhW_put1_grow_cnt (hd true ok) st b Hg), E. reflexivity.
      * rewrite (IH (tl ok) (prhWriter_put1 (hd true ok) st b)) by lia.
        rewrite (prhW_put1_grow_cnt (hd true ok) st b Hg).
        rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia). f_equal. lia.
    + rewrite (prhW_k_nogrow ok st b P Hg) in Hk |- *. rewrite (prhW_putN_cons_nogrow ok st b P Hg).
      rewrite (IH ok (WriterApp.put1 st b) Hk).
      destruct (prhW_nogrow_f st b Hg) as (_ & _ & Hc & _ & _). rewrite Hc. reflexivity.
Qed.

(* a run that ends not failed started not failed and never met the allocation set to fail *)
Lemma prhW_notfailed : forall P ok st, WriterApp.w_failed (prhWriter_putN ok st P) = 0 ->
  WriterApp.w_failed st = 0 /\ WriterApp.w_fail (prhWriter_putN ok st P) = WriterApp.w_fail st.
Proof.
  induction P as [|b P IH]; intros ok st H; [split; [exact H|reflexivity]|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok st b P Hg) in H |- *.
    destruct (IH _ _ H) as [H1 H2]. rewrite H2. split.
    + unfold prhWriter_grows in Hg. apply andb_prop in Hg. destruct Hg as [Hg _].
      exact (proj1 (Z.eqb_eq _ _) Hg).
    + destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
        as [(_ & Hf & _) | [(_ & _ & _ & Hfl & _) | (_ & _ & Hf & _)]]; [lia | exact Hfl | lia].
  - rewrite (prhW_putN_cons_nogrow ok st b P Hg) in H |- *.
    destruct (IH _ _ H) as [H1 H2].
    destruct (prhW_nogrow_f st b Hg) as (Hfd & _ & _ & Hfl & _).
    split; [lia|]. rewrite H2. exact Hfl.
Qed.

(* the run reads only the bits of its first k calls *)
Lemma prhW_putN_agree : forall P ok ok' st,
  (forall i, (i < prhWriter_k ok st P)%nat -> nth i ok' true = nth i ok true) ->
  prhWriter_putN ok' st P = prhWriter_putN ok st P.
Proof.
  induction P as [|b P IH]; intros ok ok' st H; [reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok' st b P Hg), (prhW_putN_cons_grow ok st b P Hg).
    assert (H0 : hd true ok' = hd true ok).
    { rewrite <- !prhW_nth0. apply H. rewrite (prhW_k_grow ok st b P Hg). lia. }
    rewrite H0. apply IH. intros i Hi. rewrite !prhW_nth_tl. apply H.
    rewrite (prhW_k_grow ok st b P Hg). lia.
  - rewrite (prhW_putN_cons_nogrow ok' st b P Hg), (prhW_putN_cons_nogrow ok st b P Hg).
    apply IH. intros i Hi. apply H. rewrite (prhW_k_nogrow ok st b P Hg). exact Hi.
Qed.

(* ... and ignores the bit of a call whose (wrapped) counter is the allocation set to fail *)
Lemma prhW_putN_agree_c : forall P ok ok' st,
  0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  (forall i, (i < prhWriter_k ok st P)%nat ->
     (WriterApp.w_cnt st + Z.of_nat i) mod 2 ^ 64 <> WriterApp.w_fail st -> nth i ok' true = nth i ok true) ->
  prhWriter_putN ok' st P = prhWriter_putN ok st P.
Proof.
  induction P as [|b P IH]; intros ok ok' st Hr H; [reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok' st b P Hg), (prhW_putN_cons_grow ok st b P Hg).
    destruct (Z.eq_dec (WriterApp.w_cnt st) (WriterApp.w_fail st)) as [E|E].
    + rewrite (prhW_put1_chosen (hd true ok') (hd true ok) st b E).
      destruct (prhW_put1_grow_cases (hd true ok) st b Hg) as [(_ & Hf & _) | [(Hc & _) | (Hc & _)]];
        [| exfalso; exact (Hc E) | exfalso; exact (Hc E)].
      rewrite (prhW_putN_failed P (tl ok') (prhWriter_put1 (hd true ok) st b)) by lia.
      rewrite (prhW_putN_failed P (tl ok) (prhWriter_put1 (hd true ok) st b)) by lia.
      reflexivity.
    + assert (H0 : hd true ok' = hd true ok).
      { rewrite <- !prhW_nth0. apply H.
        - rewrite (prhW_k_grow ok st b P Hg). lia.
        - change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Z.mod_small by exact Hr. exact E. }
      rewrite H0. apply IH.
      * rewrite (prhW_put1_grow_cnt (hd true ok) st b Hg). apply Z.mod_pos_bound.
        apply Z.pow_pos_nonneg; lia.
      * intros i Hi Hm. rewrite !prhW_nth_tl. apply H.
        -- rewrite (prhW_k_grow ok st b P Hg). lia.
        -- assert (Hfl : WriterApp.w_fail (prhWriter_put1 (hd true ok) st b) = WriterApp.w_fail st).
           { destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
               as [(Hc & _) | [(_ & _ & _ & Hfl & _) | (_ & _ & _ & Hfl & _)]];
               [exfalso; exact (E Hc) | exact Hfl | exact Hfl]. }
           rewrite (prhW_put1_grow_cnt (hd true ok) st b Hg), Hfl in Hm.
           rewrite Z.add_mod_idemp_l in Hm by (apply Z.pow_nonzero; lia).
           replace (WriterApp.w_cnt st + Z.of_nat (S i)) with (WriterApp.w_cnt st + 1 + Z.of_nat i) by lia.
           exact Hm.
  - rewrite (prhW_putN_cons_nogrow ok' st b P Hg), (prhW_putN_cons_nogrow ok st b P Hg).
    destruct (prhW_nogrow_f st b Hg) as (_ & _ & Hc & Hf & _).
    apply IH.
    + rewrite Hc. exact Hr.
    + intros i Hi Hm. apply H.
      * rewrite (prhW_k_nogrow ok st b P Hg). exact Hi.
      * rewrite Hc, Hf in Hm. exact Hm.
Qed.

(* the outcome list of a composed run: the first run's k1 bits, then the second run's k2 bits, where a bit at
   whole-run counter c0 + k1 + j = f0 is false, and a bit at second-run counter c1 + j = f1 is true (both are calls
   the model decides by the counter alone) *)
Definition prhW_okc (ok1 ok2 : list bool) (k1 k2 : nat) (c0 f0 c1 f1 : Z) : list bool :=
  map (fun i => if (i <? k1)%nat then nth i ok1 true
                else if c0 + Z.of_nat k1 + Z.of_nat (i - k1) =? f0 then false
                else if c1 + Z.of_nat (i - k1) =? f1 then true
                else nth (i - k1) ok2 true)
    (seq 0 (k1 + k2)).

Lemma prhW_okc_lo : forall ok1 ok2 k1 k2 c0 f0 c1 f1 i, (i < k1)%nat ->
  nth i (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) true = nth i ok1 true.
Proof.
  intros ok1 ok2 k1 k2 c0 f0 c1 f1 i Hi. unfold prhW_okc. rewrite prhW_nth_map_seq. cbv beta.
  destruct (Nat.ltb_spec i (k1 + k2)) as [_|H]; [|lia].
  destruct (Nat.ltb_spec i k1) as [_|H]; [reflexivity|lia].
Qed.

Lemma prhW_okc_hi : forall ok1 ok2 k1 k2 c0 f0 c1 f1 j, (j < k2)%nat ->
  nth (k1 + j) (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) true =
    (if c0 + Z.of_nat k1 + Z.of_nat j =? f0 then false
     else if c1 + Z.of_nat j =? f1 then true else nth j ok2 true).
Proof.
  intros ok1 ok2 k1 k2 c0 f0 c1 f1 j Hj. unfold prhW_okc. rewrite prhW_nth_map_seq. cbv beta.
  destruct (Nat.ltb_spec (k1 + j) (k1 + k2)) as [_|H]; [|lia].
  destruct (Nat.ltb_spec (k1 + j) k1) as [H|_]; [lia|].
  replace (k1 + j - k1)%nat with j by lia. reflexivity.
Qed.

(* with c0 >= 0, a second-run call at the whole-run counter f0 is at second-run counter f1 *)
Lemma prhW_ctr : forall (c0 f0 c1 f1 : Z) (k1 j : nat),
  0 <= c0 -> f1 < 2 ^ 64 -> f1 = f0 ->
  (k1 = 0%nat -> c1 = c0) -> ((0 < k1)%nat -> c1 = (c0 + Z.of_nat k1) mod 2 ^ 64) ->
  c0 + Z.of_nat k1 + Z.of_nat j = f0 -> c1 + Z.of_nat j = f1.
Proof.
  intros c0 f0 c1 f1 k1 j H0 Hf E Hk0 Hkp He. subst f0.
  destruct (Nat.eq_dec k1 0) as [Ek|Ek].
  - rewrite (Hk0 Ek). subst k1. lia.
  - rewrite (Hkp ltac:(lia)). rewrite Z.mod_small; [lia|]. lia.
Qed.

(* THE OUTCOMES OF A RUN OF PUTS AS THIS WALK CARRIES THEM (the batch kit: every writer text this walk calls or states posts
   prh_granted for the outcomes ok it binds - DEAD-PUT / -INDENT / -PUTSTRING / -WRITEVALUE, PRH_FnWriter.v): the
   chosen-failure conjunct of PRH_Base.prh_oks, no refusal (prh_granted), and g_ran_out kept. prhW_oks_of_g gives the batch kit's
   prh_oks from it at ANY request list ns and g_most (with no refusal its two refusal conjuncts are vacuous); the walk
   instantiates them by unification with the text it concludes, i.e. ns := prhWriter_reqs ok st P and most := the
   `most` of that text's prh_ledger. prhW_g_of_oks is the converse under prh_granted. *)
Definition prhW_oksg (ok : list bool) (cnt fail : Z) (k : nat) (ran ran' : Z) : Prop :=
  (forall i, (i < k)%nat -> cnt + Z.of_nat i = fail -> nth i ok true = false) /\
  prh_granted ok cnt fail k /\ ran' = ran.

Lemma prhW_oks_of_g : forall ok cnt fail k ns most ran ran',
  prhW_oksg ok cnt fail k ran ran' -> prh_oks ok cnt fail k ns most ran ran'.
Proof.
  intros ok cnt fail k ns most ran ran' (A & G & E). unfold prh_oks.
  split; [exact A|]. split; [left; exact E|].
  intros i Hi Hr _. exfalso. unfold prh_refused in Hr. apply andb_prop in Hr. destruct Hr as (H1 & H2).
  apply negb_true_iff in H1, H2. apply Z.eqb_neq in H2. exact (H2 (G i Hi H1)).
Qed.

Lemma prhW_g_of_oks : forall ok cnt fail k ns most ran ran',
  prh_oks ok cnt fail k ns most ran ran' -> prh_granted ok cnt fail k -> prhW_oksg ok cnt fail k ran ran'.
Proof.
  intros ok cnt fail k ns most ran ran' (A & B & _) G.
  split; [exact A|]. split; [exact G|].
  destruct B as [E | (_ & i & Hi & Hr & _)]; [exact E|]. exfalso.
  unfold prh_refused in Hr. apply andb_prop in Hr. destruct Hr as (H1 & H2).
  apply negb_true_iff in H1, H2. apply Z.eqb_neq in H2. exact (H2 (G i Hi H1)).
Qed.

Lemma prhW_oks_core : forall (c0 f0 c1 f1 : Z) (k1 k2 : nat) ok1 ok2 ran ran1 ran2,
  0 <= c0 -> 0 <= f1 < 2 ^ 64 ->
  (k1 = 0%nat -> c1 = c0) -> ((0 < k1)%nat -> c1 = (c0 + Z.of_nat k1) mod 2 ^ 64) ->
  ((0 < k2)%nat -> f1 = f0) ->
  prhW_oksg ok1 c0 f0 k1 ran ran1 -> prhW_oksg ok2 c1 f1 k2 ran1 ran2 ->
  prhW_oksg (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) c0 f0 (k1 + k2) ran ran2.
Proof.
  intros c0 f0 c1 f1 k1 k2 ok1 ok2 ran ran1 ran2 H0 Hf Hk0 Hkp Hff Hok1 Hok2.
  destruct Hok1 as (A1 & G1 & E1). destruct Hok2 as (A2 & G2 & E2).
  assert (Hsplit : forall i, (i < k1 + k2)%nat -> (i < k1)%nat \/ exists j, (j < k2)%nat /\ i = (k1 + j)%nat).
  { intros i Hi. destruct (Nat.lt_ge_cases i k1) as [H|H]; [left; exact H|right].
    exists (i - k1)%nat. split; lia. }
  split; [|split].
  - intros i Hi He. destruct (Hsplit i Hi) as [Hl|(j & Hj & ->)].
    + rewrite prhW_okc_lo by exact Hl. exact (A1 i Hl He).
    + rewrite prhW_okc_hi by exact Hj.
      destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat j) f0) as [_|E3]; [reflexivity|].
      exfalso. apply E3. lia.
  - intros i Hi Hb. destruct (Hsplit i Hi) as [Hl|(j & Hj & ->)].
    + rewrite prhW_okc_lo in Hb by exact Hl. exact (G1 i Hl Hb).
    + rewrite prhW_okc_hi in Hb by exact Hj. revert Hb.
      destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat j) f0) as [E3|E3]; [intros _; lia|].
      destruct (Z.eqb_spec (c1 + Z.of_nat j) f1) as [E4|E4]; intros Hb;
        [exfalso; exact (diff_true_false Hb)|].
      exfalso. exact (E4 (G2 j Hj Hb)).
  - congruence.
Qed.

(* the model side of the composition: one outcome list for P1 ++ P2 that ends where the two runs end, with
   prhW_oksg from the two runs' prhW_oksg *)
Lemma prhW_app_model : forall st P1 P2 ok1 ok2 ran ran1 ran2,
  0 <= WriterApp.w_cnt st ->
  0 <= WriterApp.w_cnt (prhWriter_putN ok1 st P1) < 2 ^ 64 ->
  0 <= WriterApp.w_fail (prhWriter_putN ok1 st P1) < 2 ^ 64 ->
  prhW_oksg ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) ran ran1 ->
  prhW_oksg ok2 (WriterApp.w_cnt (prhWriter_putN ok1 st P1)) (WriterApp.w_fail (prhWriter_putN ok1 st P1))
    (prhWriter_k ok2 (prhWriter_putN ok1 st P1) P2) ran1 ran2 ->
  exists ok, prhWriter_putN ok st (P1 ++ P2) = prhWriter_putN ok2 (prhWriter_putN ok1 st P1) P2 /\
    prhW_oksg ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P1 ++ P2)) ran ran2.
Proof.
  intros st P1 P2 ok1 ok2 ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2.
  assert (Hc1a : prhWriter_k ok1 st P1 = 0%nat ->
    WriterApp.w_cnt (prhWriter_putN ok1 st P1) = WriterApp.w_cnt st).
  { intros E. exact (proj1 (prhW_k0 P1 ok1 st E)). }
  assert (Hc1b : (0 < prhWriter_k ok1 st P1)%nat -> WriterApp.w_cnt (prhWriter_putN ok1 st P1) =
    (WriterApp.w_cnt st + Z.of_nat (prhWriter_k ok1 st P1)) mod 2 ^ 64).
  { intros E. exact (prhW_kpos P1 ok1 st E). }
  assert (Hff : (0 < prhWriter_k ok2 (prhWriter_putN ok1 st P1) P2)%nat ->
    WriterApp.w_fail (prhWriter_putN ok1 st P1) = WriterApp.w_fail st).
  { intros E. destruct (Z.eq_dec (WriterApp.w_failed (prhWriter_putN ok1 st P1)) 0) as [F|F].
    - exact (proj2 (prhW_notfailed P1 ok1 st F)).
    - rewrite (prhW_k_failed ok2 (prhWriter_putN ok1 st P1) P2 F) in E. lia. }
  set (st1 := prhWriter_putN ok1 st P1) in *.
  set (k1 := prhWriter_k ok1 st P1) in *.
  set (k2 := prhWriter_k ok2 st1 P2) in *.
  set (okc := prhW_okc ok1 ok2 k1 k2 (WriterApp.w_cnt st) (WriterApp.w_fail st)
                (WriterApp.w_cnt st1) (WriterApp.w_fail st1)).
  assert (HA : prhWriter_putN okc st P1 = st1).
  { unfold st1. apply prhW_putN_agree. intros i Hi. unfold okc. apply prhW_okc_lo. exact Hi. }
  assert (HkA : prhWriter_k okc st P1 = k1).
  { unfold prhWriter_k at 1. rewrite HA. reflexivity. }
  assert (Hskip : prhWriter_putN (skipn k1 okc) st1 P2 = prhWriter_putN ok2 st1 P2).
  { apply prhW_putN_agree_c; [exact Hr1|]. intros j Hj Hm.
    assert (Hj0 : (0 < k2)%nat) by (unfold k2; lia).
    rewrite prhW_nth_skipn. unfold okc. rewrite prhW_okc_hi by exact Hj.
    destruct (Z.eqb_spec (WriterApp.w_cnt st + Z.of_nat k1 + Z.of_nat j) (WriterApp.w_fail st)) as [E1|E1].
    - exfalso. apply Hm.
      rewrite (prhW_ctr _ _ _ _ k1 j Hc0 (proj2 Hf1) (Hff Hj0) Hc1a Hc1b E1).
      apply Z.mod_small. exact Hf1.
    - destruct (Z.eqb_spec (WriterApp.w_cnt st1 + Z.of_nat j) (WriterApp.w_fail st1)) as [E2|E2].
      + exfalso. apply Hm. rewrite E2. apply Z.mod_small. exact Hf1.
      + reflexivity. }
  exists okc. split.
  - rewrite prhW_putN_app, HkA, HA. exact Hskip.
  - rewrite prhW_k_app, HkA, HA.
    replace (prhWriter_k (skipn k1 okc) st1 P2) with k2.
    + unfold okc. exact (prhW_oks_core _ _ _ _ _ _ _ _ _ _ _ Hc0 Hf1 Hc1a Hc1b Hff Hok1 Hok2).
    + unfold k2, prhWriter_k. rewrite Hskip. reflexivity.
Qed.

(* the capacity a run ends with is the start's or nonzero (a grow's newcap is never 0) *)
Lemma prhW_dbl_nz : forall f c n, c <> 0 -> WriterSpec.dbl f c n <> 0.
Proof.
  induction f as [|f IH]; intros c n H; cbn [WriterSpec.dbl]; [exact H|].
  destruct (n <=? c); [exact H|]. apply IH. lia.
Qed.

Lemma prhW_newcap_nz : forall c n, WriterSpec.newcap c n <> 0.
Proof.
  intros c n. unfold WriterSpec.newcap. apply prhW_dbl_nz.
  destruct (Z.eqb_spec c 0); lia.
Qed.

Lemma prhW_cap_after : forall P ok st,
  WriterApp.w_cap (prhWriter_putN ok st P) = WriterApp.w_cap st \/ WriterApp.w_cap (prhWriter_putN ok st P) <> 0.
Proof.
  induction P as [|b P IH]; intros ok st; [left; reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok st b P Hg).
    destruct (IH (tl ok) (prhWriter_put1 (hd true ok) st b)) as [E|E]; [|right; exact E].
    rewrite E.
    destruct (prhW_put1_grow_cases (hd true ok) st b Hg)
      as [(_ & _ & Hc) | [(_ & _ & _ & _ & Hc) | (_ & _ & _ & _ & Hc)]].
    + left. exact Hc.
    + right. rewrite Hc. apply prhW_newcap_nz.
    + left. exact Hc.
  - rewrite (prhW_putN_cons_nogrow ok st b P Hg).
    destruct (IH ok (WriterApp.put1 st b)) as [E|E]; [|right; exact E].
    left. rewrite E. destruct (prhW_nogrow_f st b Hg) as (_ & Hc & _). exact Hc.
Qed.

(* a list with no repeated key: an entry at its head is found there only *)
Lemma prhW_nodup_head : forall (a : Z * Z) (L m1 m2 : list (Z * Z)),
  NoDup (map fst (a :: L)) -> a :: L = m1 ++ a :: m2 -> m1 = [] /\ m2 = L.
Proof.
  intros a L m1 m2 Hnd E. destruct m1 as [|x m1].
  - pose proof (f_equal (@tl (Z * Z)) E) as E'. cbn [tl app] in E'. split; [reflexivity|symmetry; exact E'].
  - exfalso. pose proof (f_equal (@tl (Z * Z)) E) as EL. cbn [tl app] in EL.
    assert (Hin : In (fst a) (map fst L)) by (rewrite EL; apply in_map; apply in_elt).
    cbn [map] in Hnd. inversion Hnd; subst.
    match goal with Hn : ~ _ |- _ => apply Hn end.
    first [ exact Hin | apply list_elem_of_In; exact Hin | apply elem_of_list_In; exact Hin ].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* the granted arms of the batch kit's prhWriter_ret_ok (PRH_FnWriter.v: the capacity kept with no refusal, or the buffer grown,
   at the refusal peak 0), named: the batch kit's refused-grow arm needs a refusal, and prh_granted excludes it *)
Definition prhWriter_blk (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak buf : Z) (st : WriterApp.wst)
  (ly' : alayout) (S' : astate) (Lam' : list (Z * Z)) (peak' buf' : Z) (st' : WriterApp.wst) : Prop :=
  (WriterApp.w_cap st' = WriterApp.w_cap st /\ buf' = buf /\ Lam' = Lam /\ peak' = peak /\
   Permutation (ablocks B ly' S') (ablocks B ly S))
  \/
  (WriterApp.w_cap st < WriterApp.w_cap st' /\
   exists l1 l2 b1 b2,
     ((WriterApp.w_cap st = 0 /\ l1 = [] /\ l2 = Lam /\ b1 = [] /\ b2 = ablocks B ly S) \/
      (WriterApp.w_cap st <> 0 /\ Lam = l1 ++ (buf, WriterApp.w_cap st) :: l2 /\
       ablocks B ly S = b1 ++ (buf - cf_head, WriterApp.w_cap st + cf_head) :: b2)) /\
     Lam' = (buf', WriterApp.w_cap st') :: l1 ++ l2 /\
     peak' = Z.max peak (Ledger.lsum (l1 ++ l2) + WriterApp.w_cap st') /\
     Permutation (ablocks B ly' S') ((buf' - cf_head, WriterApp.w_cap st' + cf_head) :: b1 ++ b2)).

(* The batch kit's prhWriter_ret_ok at outcomes ok with no refusal is the walk's granted form, and back. The refusal peak
   prhWriter_rpeak is 0 under prh_granted (PRH_Base.prh_refused_peak_granted), so the grown arm's
   Z.max (Z.max peak ..) (prhWriter_rpeak ..) is Z.max peak .. at a peak that is not negative (the entry ledger's
   0 <= lsum Lam <= peak). In prhWriter_ret_ok_of_g, the batch kit's prh_oks is met at its own request list
   ns := prhWriter_reqs ok st P and its own `most` (the argument of the text's prh_ledger), by prhW_oks_of_g. *)
Lemma prhWriter_ret_ok_g : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md',
  0 <= peak ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ->
  exists ran' buf' Lam' peak',
    prhW_oksg ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ran ran' /\
    prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
      (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own /\
    prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P).
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' Hpk G H.
  unfold prhWriter_ret_ok in H. cbv zeta in H.
  destruct H as (ran' & buf' & Lam' & peak' & K & OUT & LG & ARMS).
  exists ran', buf', Lam', peak'.
  split; [exact (prhW_g_of_oks _ _ _ _ _ _ _ _ K G)|]. split; [exact OUT|]. split; [exact LG|].
  unfold prhWriter_blk.
  destruct ARMS as [A1 | [(_ & _ & _ & (i & Hi & Hr) & _) | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hp)]].
  - left. exact A1.
  - exfalso. unfold prh_refused in Hr. apply andb_prop in Hr. destruct Hr as (H1 & H2).
    apply negb_true_iff in H1, H2. apply Z.eqb_neq in H2. exact (H2 (G i Hi H1)).
  - right. split; [exact Lt|]. exists l1, l2, b1, b2. split; [exact Hc|]. split; [exact EL|].
    split; [|exact Hp].
    rewrite Ep. unfold prhWriter_rpeak. rewrite (prh_refused_peak_granted _ _ _ _ _ G). lia.
Qed.

Lemma prhWriter_ret_ok_of_g : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'
    ran' buf' Lam' peak',
  0 <= peak ->
  prhW_oksg ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ran ran' ->
  prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) ->
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
    (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own ->
  prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P) ->
  prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ran' buf' Lam' peak'
    Hpk K OUT LG BLK.
  pose proof K as (_ & G & _).
  unfold prhWriter_ret_ok. cbv zeta.
  exists ran', buf', Lam', peak'.
  split; [exact (prhW_oks_of_g _ _ _ _ _ _ _ _ K)|]. split; [exact OUT|]. split; [exact LG|].
  destruct BLK as [A1 | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hp)].
  - left. exact A1.
  - right. right. split; [exact Lt|]. exists l1, l2, b1, b2. split; [exact Hc|]. split; [exact EL|].
    split; [|exact Hp].
    rewrite Ep. unfold prhWriter_rpeak. rewrite (prh_refused_peak_granted _ _ _ _ _ G). lia.
Qed.

(* two blocks arms in a row are one: the second grow removes the first grow's buffer, the head of Lam1 *)
Lemma prhW_blk_trans : forall ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 st1 ly2 S2 Lam2 peak2 buf2 st2,
  NoDup (map fst Lam1) ->
  (WriterApp.w_cap st1 = WriterApp.w_cap st \/ WriterApp.w_cap st1 <> 0) ->
  prhWriter_blk ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 st1 ->
  prhWriter_blk ly1 S1 Lam1 peak1 buf1 st1 ly2 S2 Lam2 peak2 buf2 st2 ->
  prhWriter_blk ly S Lam peak buf st ly2 S2 Lam2 peak2 buf2 st2.
Proof.
  intros ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 st1 ly2 S2 Lam2 peak2 buf2 st2 Hnd Hcap H1 H2.
  unfold prhWriter_blk in *.
  destruct H1 as [(Ec1 & Eb1 & EL1 & Ep1 & Hp1) | (Lt1 & l1 & l2 & b1 & b2 & Hc1 & EL1 & Ep1 & Hp1)];
  destruct H2 as [(Ec2 & Eb2 & EL2 & Ep2 & Hp2) | (Lt2 & m1 & m2 & c1 & c2 & Hc2 & EL2 & Ep2 & Hp2)].
  - (* same, same *)
    left. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    eapply perm_trans; [exact Hp2|exact Hp1].
  - (* same, grow *)
    right. split; [lia|].
    destruct Hc2 as [(Z0 & -> & -> & -> & ->) | (NZ & EL & EA)].
    + exists [], Lam, [], (ablocks B ly S). split; [left; split; [lia|repeat split; reflexivity]|].
      split; [rewrite EL2, EL1; reflexivity|].
      split; [rewrite Ep2, Ep1, EL1; reflexivity|].
      eapply perm_trans; [exact Hp2|]. apply perm_skip. exact Hp1.
    + assert (Hin : In (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) (ablocks B ly S)).
      { eapply Permutation_in; [exact Hp1|]. rewrite EA. apply in_elt. }
      apply in_split in Hin. destruct Hin as (d1 & d2 & Ed).
      exists m1, m2, d1, d2. split.
      * right. split; [lia|]. split.
        -- rewrite <- EL1, <- Eb1, <- Ec1. exact EL.
        -- rewrite <- Eb1, <- Ec1. exact Ed.
      * split; [exact EL2|]. split; [rewrite Ep2, Ep1; reflexivity|].
        eapply perm_trans; [exact Hp2|]. apply perm_skip.
        assert (Hx : Permutation (c1 ++ (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) :: c2)
                       (d1 ++ (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) :: d2)).
        { rewrite <- EA, <- Ed. exact Hp1. }
        eapply Permutation_app_inv. exact Hx.
  - (* grow, same *)
    right. split; [lia|]. exists l1, l2, b1, b2. split; [exact Hc1|].
    split; [rewrite EL2, EL1, Eb2, Ec2; reflexivity|].
    split; [rewrite Ep2, Ep1, Ec2; reflexivity|].
    rewrite Eb2, Ec2. eapply perm_trans; [exact Hp2|exact Hp1].
  - (* grow, grow *)
    right. split; [lia|]. exists l1, l2, b1, b2. split; [exact Hc1|].
    destruct Hc2 as [(Z0 & _) | (NZ & EL & EA)]; [exfalso; destruct Hcap; lia|].
    assert (E : (buf1, WriterApp.w_cap st1) :: l1 ++ l2 = m1 ++ (buf1, WriterApp.w_cap st1) :: m2).
    { rewrite <- EL1. exact EL. }
    rewrite EL1 in Hnd. destruct (prhW_nodup_head _ _ _ _ Hnd E) as [-> ->].
    split; [rewrite EL2; reflexivity|].
    split.
    + rewrite Ep2, Ep1. change (Ledger.lsum ([] ++ l1 ++ l2)) with (Ledger.lsum (l1 ++ l2)). lia.
    + eapply perm_trans; [exact Hp2|]. apply perm_skip.
      assert (Hx : Permutation (c1 ++ (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) :: c2)
                     ([] ++ (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) :: b1 ++ b2)).
      { rewrite <- EA. exact Hp1. }
      change (Permutation (c1 ++ c2) ([] ++ b1 ++ b2)).
      eapply Permutation_app_inv. exact Hx.
Qed.


(* ---- THE MODEL-RUN POSITION along a run of puts. prhWriter_put_pos names tput_specX's per-arm position post (the batch kit,
   PRH_FnWriter.v tput_specX), keyed on the failed field at o + 24; its NULL arm (f' = 1) keeps the position with the
   CALLEE's history (`exists hist'`, the batch kit). prhWriter_ret_pos is the post of the writer texts that call put
   (tindent_specX, tput_string_specX, twrite_value_specX) VERBATIM in the batch kit's shape: prhWriter_ret_ok under the outcomes
   ok, prh_granted for them (DEAD-PUT and its kin), and the position at the EXACT advance rp_i + length (prhWriter_evs ok st P).
   prhWriter_ret_pos_nil starts a run; prhWriter_ret_pos_step adds one put (the put's event premise is
   prhWriter_ev_at). ---- *)
Definition prhWriter_put_pos (rp_sm : list Z -> Z * Z) (rp_x : list Z)
  (rp_os : list (option nat * option nat * option nat)) (rp_H0 : list Z) (rp_i : nat) (rp_hist : list YG00.chunk)
  (st : WriterApp.wst) (bs : list Z) (o : Z) (W' : world segs) (mem' : word -> option byte) (S' : astate) : Prop :=
  (prhWriter_grows st bs = false -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\
  (prhWriter_grows st bs = true -> forall f', val_mem segs (mrestrict (w_H W') mem') (o + 24) 4 f' ->
     (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\
     (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S')).

Definition prhWriter_ret_pos (rp_sm : list Z -> Z * Z) (rp_x : list Z)
  (rp_os : list (option nat * option nat * option nat)) (rp_H0 : list Z) (rp_i : nat)
  (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak ran most own o buf : Z) (st : WriterApp.wst) (P : list (list Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) : Prop :=
  exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' /\
    prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) /\
    exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st P))%nat rp_H0 hist' S'.

(* the empty run: no outcome, no event, the entry position *)
Lemma prhWriter_ret_pos_nil : forall rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Lam peak ran most own o buf st
    ly' S' Hp' W' regs' mem' md',
  prhWriter_out W' mem' Lam o buf st ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S' ->
  prhWriter_ret_pos rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st [] ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Lam peak ran most own o buf st ly' S' Hp' W' regs' mem' md'
    Hout Hled Hperm Hp.
  pose proof Hled as Hb. apply prh_ledger_bounds in Hb. destruct Hb as (Hpk & _).
  assert (K0 : prhW_oksg [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st []) ran ran).
  { rewrite prhW_k_nil. split; [intros i Hi; exfalso; lia|]. split; [intros i Hi; exfalso; lia | reflexivity]. }
  exists []. split; [|split].
  - apply (prhWriter_ret_ok_of_g [] ly S Lam peak ran most own o buf st [] ly' S' Hp' W' regs' mem' md'
      ran buf Lam peak ltac:(lia) K0 Hout Hled).
    left. repeat split; try reflexivity. exact Hperm.
  - exact (proj1 (proj2 K0)).
  - exists rp_hist. cbn [prhWriter_evs length]. rewrite Nat.add_0_r. exact Hp.
Qed.

(* one more put: the run PP so far opened (outcomes ok1 with no refusal), then the put's batch-kit text post (its per-arm
   position at rp_c, the advance after PP, and its prhWriter_ret_ok over [bs] with prh_granted) *)
Lemma prhWriter_ret_pos_step : forall rp_sm rp_x rp_os rp_H0 rp_i rp_c hist1 ly S Lam peak ran most own o buf st PP bs
    ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1 ly2 S2 Hp2 W2 regs2 mem2 md2,
  0 <= WriterApp.w_cnt st -> 0 <= peak ->
  rp_c = (rp_i + length (prhWriter_evs ok1 st PP))%nat ->
  prhW_oksg ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st PP) ran ran1 ->
  prhWriter_out W1 mem1 Lam1 o buf1 (prhWriter_putN ok1 st PP) ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st PP))
    (WriterApp.w_fail (prhWriter_putN ok1 st PP)) ran1 most own ->
  prhWriter_blk ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 (prhWriter_putN ok1 st PP) ->
  prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_c hist1 (prhWriter_putN ok1 st PP) bs o W2 mem2 S2 ->
  (exists ok2, prhWriter_ret_ok B ok2 ly1 S1 Lam1 peak1 ran1 most own o buf1 (prhWriter_putN ok1 st PP) [bs]
       ly2 S2 Hp2 W2 regs2 mem2 md2 /\
     prh_granted ok2 (WriterApp.w_cnt (prhWriter_putN ok1 st PP)) (WriterApp.w_fail (prhWriter_putN ok1 st PP))
       (prhWriter_k ok2 (prhWriter_putN ok1 st PP) [bs])) ->
  prhWriter_ret_pos rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st (PP ++ [bs]) ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
  intros rp_sm rp_x rp_os rp_H0 rp_i rp_c hist1 ly S Lam peak ran most own o buf st PP bs ok1 ran1 buf1 Lam1 peak1
    ly1 S1 Hp1 W1 mem1 ly2 S2 Hp2 W2 regs2 mem2 md2 Hc0 Hpk Hrc Hok1 Hout1 Hled1 Hblk1 (HN & HG) (ok2 & Hret2 & G2).
  pose proof Hled1 as Hb1. apply prh_ledger_bounds in Hb1. destruct Hb1 as (Hpk1 & _ & Hr1 & Hf1 & _).
  assert (Hpk1' : 0 <= peak1) by lia.
  destruct (prhWriter_ret_ok_g ok2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpk1' G2 Hret2)
    as (ran2 & buf2 & Lam2 & peak2 & Hok2 & Hout2 & Hled2 & Hblk2).
  pose proof Hled1 as Hnd1. apply prh_ledger_nodup in Hnd1.
  destruct (prhW_app_model st PP [bs] ok1 ok2 ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2) as (ok & Hput & Hoks).
  pose proof (prhW_cap_after PP ok1 st) as Hcap.
  exists ok. split; [|split].
  { apply (prhWriter_ret_ok_of_g ok ly S Lam peak ran most own o buf st (PP ++ [bs]) ly2 S2 Hp2 W2 regs2 mem2 md2
      ran2 buf2 Lam2 peak2 Hpk Hoks); rewrite Hput; [exact Hout2 | exact Hled2 |].
    eapply prhW_blk_trans; [exact Hnd1 | exact Hcap | exact Hblk1 | exact Hblk2]. }
  { exact (proj1 (proj2 Hoks)). }
  (* the position: the number of events is the number of calls less the call that failed the writer *)
  pose proof (prhW_evs_len (PP ++ [bs]) ok st) as LW.
  pose proof (prhW_evs_len PP ok1 st) as L1.
  unfold prhWriter_k in LW, L1. rewrite Hput in LW.
  pose proof (prhW_calls_le PP ok1 st) as M1.
  pose proof (prhW_calls_le [bs] ok2 (prhWriter_putN ok1 st PP)) as M2.
  pose proof Hout2 as (_ & _ & _ & _ & _ & _ & Hv2 & H012 & _).
  subst rp_c.
  destruct (prhWriter_grows (prhWriter_putN ok1 st PP) bs) eqn:Hg.
  - (* a grow: one call *)
    assert (Hf1' : WriterApp.w_failed (prhWriter_putN ok1 st PP) = 0).
    { unfold prhWriter_grows in Hg. apply andb_prop in Hg. destruct Hg as (Hg' & _). apply Z.eqb_eq in Hg'. exact Hg'. }
    assert (Hf0 : WriterApp.w_failed st = 0).
    { destruct (Z.eq_dec (WriterApp.w_failed st) 0) as [E|E]; [exact E|].
      rewrite (prhW_putN_failed PP ok1 st E) in Hf1'. contradiction. }
    assert (E2 : prhWriter_putN ok2 (prhWriter_putN ok1 st PP) [bs] =
                 prhWriter_put1 (hd true ok2) (prhWriter_putN ok1 st PP) bs)
      by (rewrite (prhW_putN_cons_grow ok2 _ bs [] Hg); reflexivity).
    pose proof (prhW_put1_grow_calls (hd true ok2) (prhWriter_putN ok1 st PP) bs Hg) as HC2.
    rewrite E2 in LW, M2, Hv2, H012. rewrite HC2, length_app in LW, M2. cbn [length] in LW, M2.
    rewrite (proj2 (Z.eqb_eq _ _) Hf0) in LW, L1. rewrite (proj2 (Z.eqb_eq _ _) Hf1') in L1. cbn [andb negb] in L1.
    destruct (HG eq_refl _ Hv2) as (HS & HF).
    destruct H012 as [E0 | E1].
    + (* granted: one event, the position advanced by one *)
      destruct (HS E0) as (h2 & HPS2). exists h2.
      rewrite (proj2 (Z.eqb_eq _ _) E0) in LW. cbn [andb negb] in LW.
      replace (rp_i + length (prhWriter_evs ok st (PP ++ [bs])))%nat
        with (Datatypes.S (rp_i + length (prhWriter_evs ok1 st PP))) by lia.
      exact HPS2.
    + (* fuzz_realloc returned NULL (the allocation set to fail): no event, the position kept, the callee's history *)
      destruct (HF ltac:(lia)) as (h2 & HPS2). exists h2.
      rewrite E1 in LW. cbn [andb negb Z.eqb] in LW.
      replace (rp_i + length (prhWriter_evs ok st (PP ++ [bs])))%nat
        with (rp_i + length (prhWriter_evs ok1 st PP))%nat by lia.
      exact HPS2.
  - (* no grow: no call, no event, the position kept *)
    assert (E2 : prhWriter_putN ok2 (prhWriter_putN ok1 st PP) [bs] = WriterApp.put1 (prhWriter_putN ok1 st PP) bs)
      by (rewrite (prhW_putN_cons_nogrow ok2 _ bs [] Hg); reflexivity).
    destruct (prhW_nogrow_f (prhWriter_putN ok1 st PP) bs Hg) as (Hfe & _ & _ & _ & Hce).
    rewrite E2, Hfe, Hce in LW.
    exists hist1.
    replace (rp_i + length (prhWriter_evs ok st (PP ++ [bs])))%nat
      with (rp_i + length (prhWriter_evs ok1 st PP))%nat.
    + exact (HN eq_refl).
    + revert LW L1.
      destruct ((WriterApp.w_failed st =? 0) && negb (WriterApp.w_failed (prhWriter_putN ok1 st PP) =? 0));
        intros LW L1; lia.
Qed.

End c.

(* ======== S7a_WriterLive.v (blob 4a32ca8f73b9): the doubling-chain and text-length lemmas this walk still uses
   (the batch kit retired the entry live sum, so the capacity-grid composition prhWriter_newcap_step and its chain lemmas went
   with it) ======== *)
(* ---- newcap over one doubling chain: newcap c y = dbl 64 (prhWL_base c) y ---- *)
Definition prhWL_base (c : Z) : Z := if c =? 0 then 4096 else c.

Lemma prhWL_newcap_eq : forall c y, WriterSpec.newcap c y = WriterSpec.dbl 64%nat (prhWL_base c) y.
Proof. reflexivity. Qed.

Lemma prhWL_dbl_O : forall c y, WriterSpec.dbl O c y = c.
Proof. reflexivity. Qed.

Lemma prhWL_dbl_S_le : forall f c y, y <= c -> WriterSpec.dbl (S f) c y = c.
Proof. intros f c y H. cbn [WriterSpec.dbl]. destruct (Z.leb_spec y c); [reflexivity | lia]. Qed.

Lemma prhWL_dbl_S_gt : forall f c y, c < y -> WriterSpec.dbl (S f) c y = WriterSpec.dbl f (2 * c) y.
Proof. intros f c y H. cbn [WriterSpec.dbl]. destruct (Z.leb_spec y c); [lia | reflexivity]. Qed.

(* dbl never goes below its start *)
Lemma prhWL_dbl_ge_c : forall f c y, 0 <= c -> c <= WriterSpec.dbl f c y.
Proof.
  induction f as [|f IH]; intros c y Hc; [rewrite prhWL_dbl_O; lia|].
  destruct (Z.le_gt_cases y c).
  - rewrite prhWL_dbl_S_le by lia. lia.
  - rewrite prhWL_dbl_S_gt by lia. specialize (IH (2 * c) y ltac:(lia)). lia.
Qed.

(* ---- a run's first put ---- *)
Lemma prhWL_putN_g : forall ok st b P, prhWriter_grows st b = true ->
  prhWriter_putN ok st (b :: P) = prhWriter_putN (tl ok) (prhWriter_put1 (hd true ok) st b) P.
Proof. intros ok st b P E. cbn [prhWriter_putN]. rewrite E. reflexivity. Qed.

Lemma prhWL_putN_ng : forall ok st b P, prhWriter_grows st b = false ->
  prhWriter_putN ok st (b :: P) = prhWriter_putN ok (WriterApp.put1 st b) P.
Proof. intros ok st b P E. cbn [prhWriter_putN]. rewrite E. reflexivity. Qed.

(* ---- one put of a run: the text is kept or extended by b; the capacity is kept or grown to newcap ---- *)
Definition prhWL_step (st st' : WriterApp.wst) (b : list Z) : Prop :=
  (WriterApp.w_text st' = WriterApp.w_text st \/ WriterApp.w_text st' = WriterApp.w_text st ++ b) /\
  (WriterApp.w_cap st' = WriterApp.w_cap st \/
   WriterApp.w_cap st' = WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)).

Ltac prhWL_stepfin := split; first [left; reflexivity | right; reflexivity].

Lemma prhWL_put1_step : forall st b, prhWL_step st (WriterApp.put1 st b) b.
Proof.
  intros st b. unfold prhWL_step, WriterApp.put1, prhWriter_need. cbv zeta.
  destruct (WriterApp.w_failed st =? 0); [|prhWL_stepfin].
  destruct (Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b) + 1 <=? WriterApp.w_cap st);
    [prhWL_stepfin|].
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); prhWL_stepfin.
Qed.

Lemma prhWL_hput1_step : forall okb st b, prhWL_step st (prhWriter_put1 okb st b) b.
Proof.
  intros okb st b. unfold prhWriter_put1.
  destruct (prhWriter_grows st b); [|apply prhWL_put1_step].
  unfold prhWL_step. cbv zeta.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [prhWL_stepfin|].
  destruct okb; prhWL_stepfin.
Qed.

Lemma prhWL_step_len : forall st st' b, prhWL_step st st' b ->
  (length (WriterApp.w_text st') <= length (WriterApp.w_text st) + length b)%nat.
Proof. intros st st' b [[Ht|Ht] _]; rewrite Ht; [|rewrite length_app]; lia. Qed.

Lemma prhWriter_putN_len_le : forall ok st P,
  (length (WriterApp.w_text (prhWriter_putN ok st P)) <= length (WriterApp.w_text st) + length (concat P))%nat.
Proof.
  intros ok st P. revert ok st.
  induction P as [|b P IH]; intros ok st; [cbn [prhWriter_putN concat]; lia|].
  cbn [concat]. rewrite length_app.
  destruct (prhWriter_grows st b) eqn:E.
  - rewrite (prhWL_putN_g ok st b P E). pose proof (IH (tl ok) (prhWriter_put1 (hd true ok) st b)).
    pose proof (prhWL_step_len _ _ _ (prhWL_hput1_step (hd true ok) st b)). lia.
  - rewrite (prhWL_putN_ng ok st b P E). pose proof (IH ok (WriterApp.put1 st b)).
    pose proof (prhWL_step_len _ _ _ (prhWL_put1_step st b)). lia.
Qed.

(* ======== The batch kit: A CALLEE'S RUN PREMISES FROM THE CALLER'S ========
   the batch kit's writer texts take, besides the run events (prh_run_at), the call's window of consumer allocations
   (PRH_Base.prh_cons_from over the length of its all-granted events) and the live room at each of its events
   (PRH_Base.prh_live_evs over the same events). A caller that has written the pieces P (outcomes ok) and calls a
   callee on the pieces Q of its own run P ++ Q ++ R supplies both from its own entry premises: the window by
   prh_cons_from_sub (prhW_cons_mid), the live room by the live list at the call state, which is the entry's moved by
   the events of P (prhW_live_mid: the granted arms prhWriter_blk move the allocator's blocks exactly as the buffer
   moves, and so does the all-granted run's events, prhW_hlive_run). When P left the writer failed the callee makes
   no event and both are trivial. *)

(* a grow strictly raises the capacity: newcap c y > c when 0 <= c < y *)
Lemma prhW_newcap_gt : forall c y, 0 <= c -> c < y -> c < WriterSpec.newcap c y.
Proof.
  intros c y Hc Hy. rewrite prhWL_newcap_eq. unfold prhWL_base.
  destruct (Z.eqb_spec c 0) as [E|E]; cbv iota.
  - pose proof (prhWL_dbl_ge_c 64 4096 y ltac:(lia)). lia.
  - rewrite (prhWL_dbl_S_gt 63 c y Hy). pose proof (prhWL_dbl_ge_c 63 (2 * c) y ltac:(lia)). lia.
Qed.

Lemma prhW_grow_gt : forall st b, 0 <= WriterApp.w_cap st -> prhWriter_grows st b = true ->
  WriterApp.w_cap st < WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b).
Proof.
  intros st b Hc0 Hg. apply prhW_newcap_gt; [exact Hc0|].
  unfold prhWriter_grows in Hg. apply andb_prop in Hg. destruct Hg as (_ & Hg). apply Z.ltb_lt in Hg. exact Hg.
Qed.

(* the sum of a list of requests does not depend on its order *)
Lemma prhW_zsum_perm : forall a b : list Z, Permutation a b -> fold_right Z.add 0 a = fold_right Z.add 0 b.
Proof. intros a b H. induction H; cbn [fold_right]; lia. Qed.

Section lv. Context {cp : CfParams}.

(* the all-granted run's events, one step *)
Lemma prhW_evs_cons_grow0 : forall st b P, prhWriter_grows st b = true ->
  prhWriter_evs [] st (b :: P) =
    (if WriterApp.w_cnt st =? WriterApp.w_fail st then [] else [prhWriter_ev st b]) ++
    prhWriter_evs [] (prhWriter_put1 true st b) P.
Proof.
  intros st b P Hg. cbn [prhWriter_evs hd tl]. rewrite Hg.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); reflexivity.
Qed.

Lemma prhW_evs_cons_nogrow0 : forall st b P, prhWriter_grows st b = false ->
  prhWriter_evs [] st (b :: P) = prhWriter_evs [] (WriterApp.put1 st b) P.
Proof. intros st b P Hg. cbn [prhWriter_evs]. rewrite Hg. reflexivity. Qed.

(* the buffer's entry in the live list (cf_head-sized, as prhWriter_ev's requests) *)
Definition prhW_bufl (st : WriterApp.wst) : list Z :=
  if WriterApp.w_cap st =? 0 then [] else [WriterApp.w_cap st + cf_head].

(* the all-granted run that ends not failed moves the live list by its events exactly as its buffer moves *)
Lemma prhW_hlive_run : forall P st L,
  0 <= WriterApp.w_cap st ->
  WriterApp.w_failed (prhWriter_putN [] st P) = 0 ->
  PresetReqAt.hlive_from (prhW_bufl st ++ L) (prhWriter_evs [] st P) = prhW_bufl (prhWriter_putN [] st P) ++ L.
Proof.
  induction P as [|b P IH]; intros st L Hc0 Hf; [reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow [] st b P Hg) in Hf |- *. cbn [hd tl] in Hf |- *.
    rewrite (prhW_evs_cons_grow0 st b P Hg).
    pose proof (prhW_grow_gt st b Hc0 Hg) as Hgt.
    destruct (prhW_put1_grow_cases true st b Hg)
      as [(Ec & Hf1 & _) | [(Ec & _ & Hf1 & _ & Hcap1) | (_ & Hb & _)]].
    + exfalso. rewrite (prhW_putN_failed P [] (prhWriter_put1 true st b) ltac:(lia)) in Hf. lia.
    + rewrite (proj2 (Z.eqb_neq _ _) Ec). cbn [app].
      rewrite PresetReqAt.hlive_from_cons.
      assert (Hs : PresetReqAt.hstep (prhW_bufl st ++ L) (prhWriter_ev st b) =
                   prhW_bufl (prhWriter_put1 true st b) ++ L).
      { unfold prhW_bufl, prhWriter_ev.
        rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap (prhWriter_put1 true st b)) 0)) by lia.
        rewrite Hcap1.
        destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [E0|E0];
          cbn [app PresetReqAt.hstep PresetReqAt.rm1]; [reflexivity|].
        rewrite Z.eqb_refl. reflexivity. }
      rewrite Hs. apply IH; [lia | exact Hf].
    + discriminate Hb.
  - rewrite (prhW_putN_cons_nogrow [] st b P Hg) in Hf |- *.
    rewrite (prhW_evs_cons_nogrow0 st b P Hg).
    destruct (prhW_nogrow_f st b Hg) as (_ & Hc & _).
    assert (Hb : prhW_bufl (WriterApp.put1 st b) = prhW_bufl st) by (unfold prhW_bufl; rewrite Hc; reflexivity).
    rewrite <- Hb. apply IH; [lia | exact Hf].
Qed.

(* the all-granted run that ends not failed either made no event and kept the capacity, or grew the capacity *)
Lemma prhW_capgrow_or_nil : forall P st,
  0 <= WriterApp.w_cap st ->
  WriterApp.w_failed (prhWriter_putN [] st P) = 0 ->
  (prhWriter_evs [] st P = [] /\ WriterApp.w_cap (prhWriter_putN [] st P) = WriterApp.w_cap st) \/
  WriterApp.w_cap st < WriterApp.w_cap (prhWriter_putN [] st P).
Proof.
  induction P as [|b P IH]; intros st Hc0 Hf; [left; split; reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - right. rewrite (prhW_putN_cons_grow [] st b P Hg) in Hf |- *. cbn [hd tl] in Hf |- *.
    pose proof (prhW_grow_gt st b Hc0 Hg) as Hgt.
    destruct (prhW_put1_grow_cases true st b Hg)
      as [(Ec & Hf1 & _) | [(Ec & _ & Hf1 & _ & Hcap1) | (_ & Hb & _)]].
    + exfalso. rewrite (prhW_putN_failed P [] (prhWriter_put1 true st b) ltac:(lia)) in Hf. lia.
    + destruct (IH (prhWriter_put1 true st b) ltac:(lia) Hf) as [(_ & E) | E]; lia.
    + discriminate Hb.
  - rewrite (prhW_putN_cons_nogrow [] st b P Hg) in Hf |- *.
    rewrite (prhW_evs_cons_nogrow0 st b P Hg).
    destruct (prhW_nogrow_f st b Hg) as (_ & Hc & _).
    rewrite <- Hc. apply IH; [lia | exact Hf].
Qed.

(* a writer run under any outcomes that ends not failed is the all-granted run, with as many events *)
Lemma prhW_run_granted : forall P ok st,
  WriterApp.w_failed (prhWriter_putN ok st P) = 0 ->
  prhWriter_putN ok st P = prhWriter_putN [] st P /\
  length (prhWriter_evs ok st P) = length (prhWriter_evs [] st P).
Proof.
  intros P ok st F.
  assert (Est : prhWriter_putN ok st P = prhWriter_putN [] st P)
    by (destruct (prhW_putN_ok_or_failed P ok st) as [E|E]; [exact E | contradiction]).
  split; [exact Est|].
  pose proof (prhW_evs_len P ok st) as L1. pose proof (prhW_evs_len P [] st) as L2.
  assert (Hk : prhWriter_k ok st P = prhWriter_k [] st P) by (unfold prhWriter_k; rewrite Est; reflexivity).
  rewrite Est in L1. lia.
Qed.

(* THE CALLEE'S WINDOW: the batch kit's prh_cons_from for the pieces Q, at the exact advance after P *)
Lemma prhW_cons_mid : forall sm x os i st ok P Q R,
  prh_cons_from sm x os i (length (prhWriter_evs [] st (P ++ Q ++ R))) ->
  prh_cons_from sm x os (i + length (prhWriter_evs ok st P)) (length (prhWriter_evs [] (prhWriter_putN ok st P) Q)).
Proof.
  intros sm x os i st ok P Q R H.
  destruct (Z.eq_dec (WriterApp.w_failed (prhWriter_putN ok st P)) 0) as [F|F].
  - destruct (prhW_run_granted P ok st F) as (Est & HL). rewrite HL, Est.
    rewrite (prhWriter_evs_app0 P (Q ++ R) st), (prhWriter_evs_app0 Q R (prhWriter_putN [] st P)), !length_app in H.
    eapply prh_cons_from_sub; [|exact H]. lia.
  - rewrite (prhWriter_evs_failed Q [] _ F). cbn [length]. intros j e Hj. lia.
Qed.

(* ... and at the entry (nothing written yet) *)
Lemma prhW_cons_pre : forall sm x os i st Q R,
  prh_cons_from sm x os i (length (prhWriter_evs [] st (Q ++ R))) ->
  prh_cons_from sm x os i (length (prhWriter_evs [] st Q)).
Proof.
  intros sm x os i st Q R H. rewrite (prhWriter_evs_app0 Q R st), length_app in H.
  pose proof (prh_cons_from_sub sm x os i
    (length (prhWriter_evs [] st Q) + length (prhWriter_evs [] (prhWriter_putN [] st Q) R)) 0
    (length (prhWriter_evs [] st Q)) ltac:(lia) H) as H'.
  rewrite Nat.add_0_r in H'. exact H'.
Qed.

(* THE CALLEE'S LIVE ROOM at its own entry state, from the caller's at the caller's entry *)
Lemma prhW_live_tail : forall E0 E1 E2 (L : list Z),
  (forall j e, nth_error (E0 ++ E1 ++ E2) j = Some e ->
     fold_right Z.add 0 (PresetReqAt.hlive_from L (firstn j (E0 ++ E1 ++ E2))) + prh_ev_req e <= LIVE_MAX) ->
  forall Sc, Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) (PresetReqAt.hlive_from L E0) ->
  prh_live_evs Sc E1.
Proof.
  intros E0 E1 E2 L HL Sc HP j e Hj.
  assert (Hjl : (j < length E1)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  assert (Hn : nth_error (E0 ++ E1 ++ E2) (length E0 + j) = Some e).
  { rewrite nth_error_app2 by lia. replace (length E0 + j - length E0)%nat with j by lia.
    rewrite nth_error_app1 by lia. exact Hj. }
  pose proof (HL (length E0 + j)%nat e Hn) as H.
  rewrite firstn_app_2, firstn_app, PresetReqAt.hlive_from_app in H.
  replace (j - length E1)%nat with 0%nat in H by lia. cbn [firstn] in H. rewrite app_nil_r in H.
  unfold prh_live_at.
  rewrite (prhW_zsum_perm _ _ (PresetReqAtNoMiss.hlive_from_perm (firstn j E1) _ _ HP)). exact H.
Qed.

Lemma prhW_live_pre : forall S st Q R,
  prh_live_evs S (prhWriter_evs [] st (Q ++ R)) -> prh_live_evs S (prhWriter_evs [] st Q).
Proof.
  intros S st Q R HL. rewrite (prhWriter_evs_app0 Q R st) in HL.
  apply (prhW_live_tail [] (prhWriter_evs [] st Q) (prhWriter_evs [] (prhWriter_putN [] st Q) R)
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S))); [|rewrite PresetReqAt.hlive_from_nil; apply Permutation_refl].
  intros j e Hj. exact (HL j e Hj).
Qed.

Lemma prhW_live_mid : forall B S Sc ly lyc Lam peak buf st ok P Q R Lamc peakc bufc,
  0 <= WriterApp.w_cap st ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lamc peakc bufc (prhWriter_putN ok st P) ->
  prh_live_evs S (prhWriter_evs [] st (P ++ Q ++ R)) ->
  prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok st P) Q).
Proof.
  intros B S Sc ly lyc Lam peak buf st ok P Q R Lamc peakc bufc Hc0 HBLK HL.
  destruct (Z.eq_dec (WriterApp.w_failed (prhWriter_putN ok st P)) 0) as [F|F];
    [|rewrite (prhWriter_evs_failed Q [] _ F); intros j e He; destruct j; discriminate He].
  destruct (prhW_run_granted P ok st F) as (Est & _).
  rewrite Est in F, HBLK |- *.
  assert (HLV : forall S0 ly0, map snd (ablocks B ly0 S0) = PresetRoom.rs_live (YGcfRoom.room_of_cf S0))
    by (intros S0 ly0; unfold ablocks; rewrite map_map; reflexivity).
  (* the live list at Sc is the entry's moved by the events of P *)
  assert (HP : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
                 (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhWriter_evs [] st P))).
  { rewrite <- (HLV Sc lyc), <- (HLV S ly).
    destruct HBLK as [(Ec & _ & _ & _ & Hp) | (Lt & l1 & l2 & b1 & b2 & Hc & _ & _ & Hp)].
    - destruct (prhW_capgrow_or_nil P st Hc0 F) as [(E & _) | E]; [|lia].
      rewrite E, PresetReqAt.hlive_from_nil. apply Permutation_map. exact Hp.
    - assert (H0 : Permutation (map snd (ablocks B ly S)) (prhW_bufl st ++ map snd (b1 ++ b2))).
      { destruct Hc as [(Z0 & -> & -> & -> & ->) | (NZ & _ & EA)].
        - unfold prhW_bufl. rewrite (proj2 (Z.eqb_eq _ 0) Z0). cbn [app]. apply Permutation_refl.
        - unfold prhW_bufl. rewrite (proj2 (Z.eqb_neq _ 0) NZ). rewrite EA, !map_app. cbn [map snd app].
          apply Permutation_sym, Permutation_middle. }
      assert (H1 : Permutation (map snd (ablocks B lyc Sc))
                     (prhW_bufl (prhWriter_putN [] st P) ++ map snd (b1 ++ b2))).
      { unfold prhW_bufl. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap (prhWriter_putN [] st P)) 0)) by lia.
        eapply perm_trans; [apply Permutation_map; exact Hp|]. cbn [map snd app]. apply Permutation_refl. }
      eapply perm_trans; [exact H1|].
      rewrite <- (prhW_hlive_run P st (map snd (b1 ++ b2)) Hc0 F).
      apply PresetReqAtNoMiss.hlive_from_perm. apply Permutation_sym. exact H0. }
  rewrite (prhWriter_evs_app0 P (Q ++ R) st), (prhWriter_evs_app0 Q R (prhWriter_putN [] st P)) in HL.
  exact (prhW_live_tail (prhWriter_evs [] st P) (prhWriter_evs [] (prhWriter_putN [] st P) Q)
    (prhWriter_evs [] (prhWriter_putN [] (prhWriter_putN [] st P) Q) R)
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) HL Sc HP).
Qed.

End lv.
