(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: COPY, unchanged below this line, of lane WriteValueB's lib/B/Prog/WriteValueB_Model.v (blob 65202a3fe569,
   worktree h-rw-pre-7-bp-write-value, 2026-10-29 18:4xZ): the one #102 port of S7a_WriterRet + S7a_WriterLive both B' writer
   walks compose. *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d, twin c90d4fa54d43), lane WriteValueB
   (h-rw-pre-7): the PURE writer-model lemmas the image-B' write_value walk composes, over K0's #102 writer texts
   (walkkit-next decff67d721f, lib/A/PRH_FnWriter.v blob 2b497bc72172, PRH_Base.v blob 3004a98fe2d9). No machine
   state is stepped and no image is named here.
   PORTED from h-rw-pre-5's WalkS7a files on origin/cold/h-hpreset-7-walk-S7B 7819c4b4583 (neither file is on this
   lane's base int102 318474716583, and the lane adds only lib/B/Prog/WriteValueB*.v):
   - lib/A/Prog/S7a_WriterRet.v (blob 29e79f90789a), whole: the model's steps and the room count, the composition of
     prhWriter_ret along a run of puts (prhWriter_blk, prhWriter_ret_app), the run events (prhW_evs_len,
     prhWriter_ev_at), the position along a run (prhWriter_put_pos, prhWriter_ret_pos, _nil, _step);
   - lib/A/Prog/S7a_WriterLive.v (blob 4a32ca8f73b9), whole: the capacity grid and the live room's composition.
   CHANGES, each forced by the #102 kit and nothing else:
   - the ledger has two more cells (decff's prh_ledger .. ran most own, prhWriter_ret / prhWriter_ret_ok .. ran most
     own o buf ..): the Section c lemmas take `most own` after `ran` and pass them through unchanged (no put moves
     them: the prhWriter_ret_ok keeps both);
   - prhWriter_put_pos names tput_specX's per-arm position post, whose NULL arm is keyed on `f' = 1` since kit-oldpin
     7176c4125950 (decff keeps it); prhWriter_ret_pos_step's proof is unchanged (its NULL arm shows f' = 1 from
     failed = 1).
   Numerals: 2 ^ 64 (WORD range). No ADDRESS (the capacity grid's 4096 / 51 / 2 ^ 28 left with the batch kit removals below).
   The batch kit's REBIND (a Theorem Labs lane, 2026-10-30, the cut 7cdbb61b5fa0, PRH_FnWriter.v / PRH_Base.v of
   that commit): prh_oks has the run's requests ns and the ledger's most (PRH_Base.prh_oks .. k ns most ran ran');
   prhWriter_ret_ok has a third blocks arm (a REFUSED grow) and the refusal peak prhWriter_rpeak; put's post states
   prh_granted (K0-DEAD-PUT), and put_string's post states it too (K0-DEAD-PUTSTRING). So the walk composes ONLY
   granted runs: the outcomes of the puts so far satisfy prh_oks AND prh_granted (prhW_app_model_g), which leaves no
   refusal: ran' = ran (prhW_oks_granted_ran), the refused arm is empty and the refusal peak 0 (prhW_ret_ok_open_g /
   prhW_ret_ok_close_g, through PRH_Base.prh_refused_peak_granted). The kit's prhWriter_live / prhWriter_buf_bytes
   are removed (the per-event live room PRH_Base.prh_live_evs replaced the entry sum): the buffer bytes are this
   file's prhW_buf_bytes, and prhW_live_evs_step / prhW_cons_step give each put its batch-kit entry premises from
   put_string's. The lemmas that composed the general (refusing) run (prhWriter_ret_app and the prhWriter_ret_pos
   family) and the
   entry-sum arithmetic (prhWriter_live_mono / _arith and the capacity grid behind them) are removed with it. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBytes.
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

(* ---- The batch kit's prh_oks (PRH_Base.prh_oks ok cnt fail k ns most ran ran'), read only through these lemmas. Under
   prh_granted no outcome is a refusal (PRH_Base.prh_refused), so its g_ran_out clauses say ran' = ran, whatever the
   requests ns and the ledger's most are. ---- *)
Lemma prhW_oks_chosen : forall ok cnt fail k ns most ran ran',
  prh_oks ok cnt fail k ns most ran ran' ->
  forall i, (i < k)%nat -> cnt + Z.of_nat i = fail -> nth i ok true = false.
Proof. intros ok cnt fail k ns most ran ran' H. unfold prh_oks in H. destruct H as (A & _ & _). exact A. Qed.

Lemma prhW_granted_norefuse : forall ok cnt fail k i, prh_granted ok cnt fail k -> (i < k)%nat ->
  prh_refused ok cnt fail i = false.
Proof.
  intros ok cnt fail k i G Hi. unfold prh_refused.
  destruct (nth i ok true) eqn:E; [reflexivity|].
  rewrite (proj2 (Z.eqb_eq _ _) (G i Hi E)). reflexivity.
Qed.

Lemma prhW_oks_granted_ran : forall ok cnt fail k ns most ran ran',
  prh_oks ok cnt fail k ns most ran ran' -> prh_granted ok cnt fail k -> ran' = ran.
Proof.
  intros ok cnt fail k ns most ran ran' H G. unfold prh_oks in H.
  destruct H as (_ & [E | (_ & i & Hi & Hr & _)] & _); [exact E|].
  rewrite (prhW_granted_norefuse ok cnt fail k i G Hi) in Hr. discriminate Hr.
Qed.

Lemma prhW_oks_of_granted : forall ok cnt fail k ns most ran,
  (forall i, (i < k)%nat -> cnt + Z.of_nat i = fail -> nth i ok true = false) ->
  prh_granted ok cnt fail k -> prh_oks ok cnt fail k ns most ran ran.
Proof.
  intros ok cnt fail k ns most ran A G. unfold prh_oks.
  split; [exact A|]. split; [left; reflexivity|].
  intros i Hi Hr _. rewrite (prhW_granted_norefuse ok cnt fail k i G Hi) in Hr. discriminate Hr.
Qed.

(* the composed outcomes of two granted runs: the allocation set to fail is false, and no refusal *)
Lemma prhW_okc_granted : forall (c0 f0 c1 f1 : Z) (k1 k2 : nat) ok1 ok2,
  (forall i, (i < k1)%nat -> c0 + Z.of_nat i = f0 -> nth i ok1 true = false) ->
  prh_granted ok1 c0 f0 k1 -> prh_granted ok2 c1 f1 k2 ->
  (forall i, (i < k1 + k2)%nat -> c0 + Z.of_nat i = f0 -> nth i (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) true = false) /\
  prh_granted (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) c0 f0 (k1 + k2).
Proof.
  intros c0 f0 c1 f1 k1 k2 ok1 ok2 A1 G1 G2.
  assert (Hsplit : forall i, (i < k1 + k2)%nat -> (i < k1)%nat \/ exists j, (j < k2)%nat /\ i = (k1 + j)%nat).
  { intros i Hi. destruct (Nat.lt_ge_cases i k1) as [H|H]; [left; exact H|right].
    exists (i - k1)%nat. split; lia. }
  split.
  - intros i Hi He. destruct (Hsplit i Hi) as [Hl|(j & Hj & ->)].
    + rewrite prhW_okc_lo by exact Hl. exact (A1 i Hl He).
    + rewrite prhW_okc_hi by exact Hj.
      destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat j) f0) as [_|E1]; [reflexivity|].
      exfalso. apply E1. lia.
  - intros i Hi Hb. destruct (Hsplit i Hi) as [Hl|(j & Hj & ->)].
    + rewrite prhW_okc_lo in Hb by exact Hl. exact (G1 i Hl Hb).
    + rewrite prhW_okc_hi in Hb by exact Hj. revert Hb.
      destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat j) f0) as [E1|E1]; intros Hb; [lia|].
      destruct (Z.eqb_spec (c1 + Z.of_nat j) f1) as [E3|E3]; [discriminate Hb|].
      exfalso. exact (E3 (G2 j Hj Hb)).
Qed.

(* the model side of the composition of two GRANTED runs: one outcome list for P1 ++ P2 that ends where the two runs
   end, with the batch kit's prh_oks over the composed run's own requests (ns := prhWriter_reqs ok st (P1 ++ P2)) at the same
   most, and prh_granted. The g_ran_out cell does not move (ran2 = ran1 = ran: no refusal). *)
Lemma prhW_app_model_g : forall st P1 P2 ok1 ok2 most ran ran1 ran2,
  0 <= WriterApp.w_cnt st ->
  0 <= WriterApp.w_cnt (prhWriter_putN ok1 st P1) < 2 ^ 64 ->
  0 <= WriterApp.w_fail (prhWriter_putN ok1 st P1) < 2 ^ 64 ->
  prh_oks ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) (prhWriter_reqs ok1 st P1) most
    ran ran1 ->
  prh_granted ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) ->
  prh_oks ok2 (WriterApp.w_cnt (prhWriter_putN ok1 st P1)) (WriterApp.w_fail (prhWriter_putN ok1 st P1))
    (prhWriter_k ok2 (prhWriter_putN ok1 st P1) P2) (prhWriter_reqs ok2 (prhWriter_putN ok1 st P1) P2) most ran1 ran2 ->
  prh_granted ok2 (WriterApp.w_cnt (prhWriter_putN ok1 st P1)) (WriterApp.w_fail (prhWriter_putN ok1 st P1))
    (prhWriter_k ok2 (prhWriter_putN ok1 st P1) P2) ->
  exists ok, prhWriter_putN ok st (P1 ++ P2) = prhWriter_putN ok2 (prhWriter_putN ok1 st P1) P2 /\
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P1 ++ P2))
      (prhWriter_reqs ok st (P1 ++ P2)) most ran ran2 /\
    prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P1 ++ P2)).
Proof.
  intros st P1 P2 ok1 ok2 most ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 G1 Hok2 G2.
  pose proof (prhW_oks_granted_ran _ _ _ _ _ _ _ _ Hok1 G1) as Er1.
  pose proof (prhW_oks_granted_ran _ _ _ _ _ _ _ _ Hok2 G2) as Er2.
  pose proof (prhW_oks_chosen _ _ _ _ _ _ _ _ Hok1) as A1.
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
  assert (Hk : prhWriter_k okc st (P1 ++ P2) = (k1 + k2)%nat).
  { rewrite prhW_k_app, HkA, HA. unfold k2, prhWriter_k. rewrite Hskip. reflexivity. }
  destruct (prhW_okc_granted (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_cnt st1) (WriterApp.w_fail st1)
    k1 k2 ok1 ok2 A1 G1 G2) as (Ac & Gc).
  exists okc. split; [|rewrite Hk; split].
  - rewrite prhW_putN_app, HkA, HA. exact Hskip.
  - rewrite Er2, Er1. exact (prhW_oks_of_granted _ _ _ _ _ _ _ Ac Gc).
  - exact Gc.
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

(* ---- The batch kit: A GRANTED RUN IS THE ALL-ACCEPTING RUN. Every outcome bit it reads is true or sits at the allocation set
   to fail (prh_granted, at the run's unwrapped counter, which is below 2 ^ 64 there), whose bit the model ignores
   (prhW_putN_agree_c); so the writer state and the number of run events are the all-accepting run's ---- *)
Lemma prhW_putN_granted : forall P ok st,
  0 <= WriterApp.w_cnt st < 2 ^ 64 -> 0 <= WriterApp.w_fail st < 2 ^ 64 ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  prhWriter_putN ok st P = prhWriter_putN [] st P.
Proof.
  intros P ok st Hc Hf G. symmetry. apply prhW_putN_agree_c; [exact Hc|].
  intros i Hi Hm. destruct (nth i ok true) eqn:E; [destruct i; reflexivity|].
  exfalso. apply Hm. rewrite (G i Hi E). apply Z.mod_small. exact Hf.
Qed.

(* the live bytes of a run's removed / replaced block: one occurrence of its size leaves the sum *)
Lemma prhW_sum_rm1 : forall z l, In z l ->
  fold_right Z.add 0 (PresetReqAt.rm1 z l) = fold_right Z.add 0 l - z.
Proof.
  intros z l. induction l as [|y l IH]; intros Hin; [destruct Hin|].
  cbn [PresetReqAt.rm1]. destruct (Z.eqb_spec y z) as [E|E].
  - subst y. cbn [fold_right]. lia.
  - cbn [fold_right]. destruct Hin as [E'|Hin]; [exfalso; exact (E E')|]. rewrite (IH Hin). lia.
Qed.

(* the allocator's bytes the out struct's state holds: none without a buffer, else the buffer and its head (the
   kit's prhWriter_buf_bytes, removed at the batch kit with the entry sum it served) *)
Section ev2. Context {cp : CfParams}.
Definition prhW_buf_bytes (st : WriterApp.wst) : Z :=
  if WriterApp.w_cap st =? 0 then 0 else WriterApp.w_cap st + cf_head.

Lemma prhW_evs_len_granted : forall P ok st,
  0 <= WriterApp.w_cnt st < 2 ^ 64 -> 0 <= WriterApp.w_fail st < 2 ^ 64 ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  length (prhWriter_evs ok st P) = length (prhWriter_evs [] st P).
Proof.
  intros P ok st Hc Hf G.
  pose proof (prhW_putN_granted P ok st Hc Hf G) as Hst.
  pose proof (prhW_evs_len P ok st) as L1. pose proof (prhW_evs_len P [] st) as L2.
  assert (Hk : prhWriter_k ok st P = prhWriter_k [] st P) by (unfold prhWriter_k; rewrite Hst; reflexivity).
  rewrite Hst, Hk in L1. revert L1 L2.
  destruct ((WriterApp.w_failed st =? 0) && negb (WriterApp.w_failed (prhWriter_putN [] st P) =? 0));
    intros L1 L2; lia.
Qed.

(* THE LIVE SET ALONG THE ALL-GRANTED EVENTS OF A RUN OF PUTS (PresetReqAt.hlive_from, the live list of
   PRH_Base.prh_live_evs): its sum moves exactly with the writer's buffer, from the entry's buffer bytes to the end
   state's, provided the entry buffer's request is live. A grow from capacity 0 is HMal (newcap + head), a later one
   HRe (cap + head) (newcap + head), which frees one occurrence of the old request (prhWriter_ev); the allocation set to
   fail makes no event and leaves the capacity. *)
Lemma prhW_live_sum : forall P st l,
  (WriterApp.w_cap st <> 0 -> In (WriterApp.w_cap st + cf_head) l) ->
  fold_right Z.add 0 (PresetReqAt.hlive_from l (prhWriter_evs [] st P)) =
    fold_right Z.add 0 l - prhW_buf_bytes st + prhW_buf_bytes (prhWriter_putN [] st P).
Proof.
  induction P as [|b P IH]; intros st l Hin.
  - cbn [prhWriter_evs prhWriter_putN]. rewrite PresetReqAt.hlive_from_nil. lia.
  - cbn [prhWriter_evs prhWriter_putN hd tl].
    destruct (prhWriter_grows st b) eqn:Hg.
    + destruct (Z.eqb_spec (WriterApp.w_cnt st) (WriterApp.w_fail st)) as [Ec|Ec].
      * (* the allocation set to fail: no event, the writer failed with its capacity, no later event *)
        destruct (prhW_put1_grow_cases true st b Hg) as [(_ & Hf1 & Hcap1) | [(Hc & _) | (Hc & _)]];
          [| exfalso; exact (Hc Ec) | exfalso; exact (Hc Ec)].
        cbn [orb app].
        rewrite (prhWriter_evs_failed P [] (prhWriter_put1 true st b)) by lia.
        rewrite (prhW_putN_failed P [] (prhWriter_put1 true st b)) by lia.
        rewrite PresetReqAt.hlive_from_nil.
        assert (B1 : prhW_buf_bytes (prhWriter_put1 true st b) = prhW_buf_bytes st)
          by (unfold prhW_buf_bytes; rewrite Hcap1; reflexivity).
        rewrite B1. lia.
      * (* granted: the one event of the grow *)
        destruct (prhW_put1_grow_cases true st b Hg) as [(Hc & _) | [(_ & _ & _ & _ & Hcap1) | (_ & Hok & _)]];
          [exfalso; exact (Ec Hc) | | discriminate Hok].
        cbn [orb negb app]. rewrite PresetReqAt.hlive_from_cons.
        rewrite (IH (prhWriter_put1 true st b) (PresetReqAt.hstep l (prhWriter_ev st b))).
        -- pose proof (prhW_newcap_nz (WriterApp.w_cap st) (prhWriter_need st b)) as Hnz.
           assert (B1 : prhW_buf_bytes (prhWriter_put1 true st b) =
             WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b) + cf_head).
           { unfold prhW_buf_bytes. rewrite Hcap1, (proj2 (Z.eqb_neq _ 0) Hnz). reflexivity. }
           assert (B0 : prhW_buf_bytes st =
             if WriterApp.w_cap st =? 0 then 0 else WriterApp.w_cap st + cf_head) by reflexivity.
           rewrite B1, B0. unfold prhWriter_ev.
           destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [Hz|Hz]; cbn [PresetReqAt.hstep fold_right].
           ++ lia.
           ++ rewrite (prhW_sum_rm1 _ _ (Hin Hz)). lia.
        -- intros _. rewrite Hcap1. unfold prhWriter_ev.
           destruct (WriterApp.w_cap st =? 0); cbn [PresetReqAt.hstep]; left; reflexivity.
    + (* no grow: no event, the capacity kept *)
      destruct (prhW_nogrow_f st b Hg) as (_ & Hcap1 & _).
      rewrite (IH (WriterApp.put1 st b) l).
      * assert (B1 : prhW_buf_bytes (WriterApp.put1 st b) = prhW_buf_bytes st)
          by (unfold prhW_buf_bytes; rewrite Hcap1; reflexivity).
        rewrite B1. lia.
      * intros Hnz. rewrite Hcap1 in Hnz |- *. exact (Hin Hnz).
Qed.

(* the live bytes are the sum of the live requests (a Theorem Labs lane's PresetLiveBytes.blocks_bytes_zsum, the source
   PRH_Base.prh_live_evs's note cites) *)
Lemma prhW_live_rs : forall S, blocks_bytes S = fold_right Z.add 0 (PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
Proof. intros S. exact (PresetLiveBytes.blocks_bytes_zsum S). Qed.

(* ONE PUT's batch-kit live premise (tput_specX's prh_live_evs over its own all-granted events) from its caller's, over all
   its puts P ++ b :: rest: the put's event (at most one) is event length (prhWriter_evs [] st P) of the caller's
   run, and the live bytes there are the caller's entry live set moved by the earlier events, whose sum the state Sc
   of the call has (Hbb: its blocks moved exactly with the buffer, prhWriter_blk_bb) *)
Lemma prhW_live_evs_step : forall (Se Sc : astate) st P b rest,
  (WriterApp.w_cap st <> 0 -> In (WriterApp.w_cap st + cf_head) (PresetRoom.rs_live (YGcfRoom.room_of_cf Se))) ->
  blocks_bytes Sc - prhW_buf_bytes (prhWriter_putN [] st P) = blocks_bytes Se - prhW_buf_bytes st ->
  prh_live_evs Se (prhWriter_evs [] st (P ++ b :: rest)) ->
  prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN [] st P) [b]).
Proof.
  intros Se Sc st P b rest Hin Hbb H j e Hj.
  destruct j as [|j].
  2: { exfalso.
       assert (Hl : (Datatypes.S j < length (prhWriter_evs [] (prhWriter_putN [] st P) [b]))%nat)
         by (apply nth_error_Some; rewrite Hj; discriminate).
       revert Hl. cbn [prhWriter_evs]. destruct (prhWriter_grows (prhWriter_putN [] st P) b); [|cbn [length]; lia].
       destruct (_ || _); cbn [length app]; lia. }
  assert (EA : prhWriter_evs [] st (P ++ b :: rest) =
    prhWriter_evs [] st P ++ (prhWriter_evs [] (prhWriter_putN [] st P) [b] ++
      prhWriter_evs [] (prhWriter_putN [] (prhWriter_putN [] st P) [b]) rest)).
  { rewrite prhWriter_evs_app0. f_equal. change (b :: rest) with ([b] ++ rest). apply prhWriter_evs_app0. }
  assert (Hn : nth_error (prhWriter_evs [] st (P ++ b :: rest)) (length (prhWriter_evs [] st P)) = Some e).
  { rewrite EA, nth_error_app2 by lia. rewrite Nat.sub_diag.
    rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hj; discriminate). exact Hj. }
  pose proof (H _ _ Hn) as Hlt. unfold prh_live_at in Hlt |- *.
  rewrite EA, firstn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r in Hlt.
  rewrite (prhW_live_sum P st _ Hin), <- prhW_live_rs in Hlt.
  cbn [firstn]. rewrite PresetReqAt.hlive_from_nil, <- prhW_live_rs. lia.
Qed.

(* ONE PUT's batch-kit consumer window (tput_specX's prh_cons_from over its own all-granted events) from its caller's:
   the put's events lie inside the caller's window, after the j events of the puts before it *)
Lemma prhW_cons_step : forall sm x os i st P b rest j,
  j = length (prhWriter_evs [] st P) ->
  prh_cons_from sm x os i (length (prhWriter_evs [] st (P ++ b :: rest))) ->
  prh_cons_from sm x os (i + j) (length (prhWriter_evs [] (prhWriter_putN [] st P) [b])).
Proof.
  intros sm x os i st P b rest j Ej H. eapply (prh_cons_from_sub sm x os i _ j _); [|exact H].
  rewrite prhWriter_evs_app0, length_app. change (b :: rest) with ([b] ++ rest).
  rewrite prhWriter_evs_app0, length_app. lia.
Qed.
End ev2.

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

(* the allocator-blocks arms of prhWriter_ret_ok WITHOUT A REFUSAL (the batch kit's first and third arms, PRH_FnWriter.v at the
   cut; the refusal peak is 0 under prh_granted), named *)
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

(* The batch kit's prhWriter_ret_ok under prh_granted, opened: the refused-grow arm is empty (no refusal) and the refusal peak
   prhWriter_rpeak is 0 (PRH_Base.prh_refused_peak_granted), so with peak >= 0 (the entry ledger's) the third arm's
   peak is the granted grow's. The ONE reading of ret_ok's arms in this lane. *)
Lemma prhW_ret_ok_open_g : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md',
  prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) -> 0 <= peak ->
  exists ran' buf' Lam' peak',
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' /\
    prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
      (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own /\
    prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P).
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' H G Hp0.
  unfold prhWriter_ret_ok in H. cbv zeta in H.
  destruct H as (ran' & buf' & Lam' & peak' & K & OUT & LG & ARMS).
  exists ran', buf', Lam', peak'. split; [exact K|]. split; [exact OUT|]. split; [exact LG|].
  unfold prhWriter_rpeak in ARMS. rewrite (prh_refused_peak_granted _ _ _ _ _ G) in ARMS.
  unfold prhWriter_blk.
  destruct ARMS as [A1 | [(_ & _ & _ & (i & Hi & Hr) & _) | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hperm)]].
  - left. exact A1.
  - exfalso. rewrite (prhW_granted_norefuse ok _ _ _ i G Hi) in Hr. discriminate Hr.
  - right. split; [exact Lt|]. exists l1, l2, b1, b2. split; [exact Hc|]. split; [exact EL|].
    split; [|exact Hperm]. rewrite Ep. lia.
Qed.

(* ... and closed: a granted run's parts are the batch kit's prhWriter_ret_ok *)
Lemma prhW_ret_ok_close_g : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'
    ran' buf' Lam' peak',
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) -> 0 <= peak ->
  prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' ->
  prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) ->
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
    (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own ->
  prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P) ->
  prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ran' buf' Lam' peak' G Hp0 K OUT LG BLK.
  unfold prhWriter_ret_ok. exists ran', buf', Lam', peak'. cbv zeta.
  split; [exact K|]. split; [exact OUT|]. split; [exact LG|].
  unfold prhWriter_rpeak. rewrite (prh_refused_peak_granted _ _ _ _ _ G).
  unfold prhWriter_blk in BLK.
  destruct BLK as [A1 | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hperm)].
  - left. exact A1.
  - right; right. split; [exact Lt|]. exists l1, l2, b1, b2. split; [exact Hc|]. split; [exact EL|].
    split; [|exact Hperm]. rewrite Ep. lia.
Qed.

(* the live requests of a state are its allocator blocks' sizes *)
Lemma prhW_rs_live_ablocks : forall ly S,
  PresetRoom.rs_live (YGcfRoom.room_of_cf S) = map snd (ablocks B ly S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.

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

(* ---- the allocator's live bytes move exactly with the writer's buffer along a run of puts: the ONE copy (WalkS7a's
   indent walk, WalkS7b's write_value / put_string walks cite it) ---- *)
Lemma prhWriter_blk_bb : forall ly S Lam peak buf (st : WriterApp.wst) ly' S' Lam' peak' buf' (st' : WriterApp.wst),
  0 <= WriterApp.w_cap st ->
  prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' st' ->
  blocks_bytes S' - prhW_buf_bytes st' = blocks_bytes S - prhW_buf_bytes st.
Proof.
intros ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 st1 Hc0 [(Hc & _ & _ & _ & HP) | (Hlt & l1 & l2 & b1 & b2 & Harm & _ & _ & HP)].
- rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP).
  unfold prhW_buf_bytes. rewrite Hc. lia.
- rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP).
  rewrite bsum_cons, bsum_app. cbn [snd]. unfold prhW_buf_bytes.
  destruct Harm as [(Hz & -> & -> & -> & Hb) | (Hnz & _ & Hb)].
  + rewrite Hb, Hz, Z.eqb_refl. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0)) by lia.
    cbn [bsum fold_right snd]. cbv iota. lia.
  + rewrite Hb, bsum_app, bsum_cons. cbn [snd].
    rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0)) by lia. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st) 0)) by lia.
    cbv iota. lia.
Qed.

End c.

(* ======== S7a_WriterLive.v (blob 4a32ca8f73b9): the text-length bound along a run (the rest of that file served the
   entry-sum live room the batch kit removed) ======== *)
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
