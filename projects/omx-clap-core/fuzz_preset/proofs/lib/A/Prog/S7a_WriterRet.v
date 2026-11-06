(* fuzz_preset, program walks (slice S7a, a Theorem Labs lane; the ONE copy, imported by S7b's writer walks): the pure
   composition of the writer post along a run of puts, and the room count of such a run. No machine state is stepped
   here. THIS VERSION is on the kit's cut 7cdbb61b5fa0 (lib/A/PRH_FnWriter.v d89d3c67b78c, PRH_Base.v ef7c8ca98529):
   prh_oks reads the run's requests (prhWriter_reqs) and g_most; prhWriter_ret_ok has a refused-grow arm; and every
   writer text's post is prhWriter_ret_ok under outcomes with NO refusal (prh_granted, the DEAD family), named here
   prhWriter_retg.
   - prhWriter_blk names the two arms of prhWriter_ret_ok that a run with no refusal can take (the refused arm is
     empty under prh_granted, and the refusal peak prhWriter_rpeak is 0); prhWriter_ret_open unfolds prhWriter_retg
     to it (prhWriter_ret_ok_of_blk / prhWriter_blk_of_ret_ok at a fixed outcome list).
   - prhWriter_ret_app: a run P1 from state 0 to state 1 (opened: its outcomes ok1 with no refusal, ran1, buffer buf1,
     ledger list Lam1, peak1) followed by a run P2 from state 1 to state 2 (prhWriter_retg at state 1's writer state) is
     a run P1 ++ P2 from state 0. The outcome list of the whole run is built from ok1's first k1 bits and the second
     run's bits; at a call the model decides by the counter alone (`w_cnt =? w_fail`, the allocation set to fail), the
     bit is irrelevant, so the lemma may re-choose it (prh_oks reads the counter without the 2 ^ 64 wrap, the model
     with it). The requests compose by prhW_reqs_app, prh_granted by prhW_granted_core.
   - the room: prhWriter_ngrow_app_le and prhWriter_k_le_ngrow.
   - the run events (prhWriter_evs): prhW_evs_len counts them from the start and end state; prhWriter_ev_at gives
     the next put's event premise from a caller's entry list; prhWriter_put_pos names tput_specX's per-arm position
     post; prhWriter_ret_pos (prhWriter_ret_ok + prh_granted + the exact advance, the post of the texts that call put)
     starts with prhWriter_ret_pos_nil and grows by one put with prhWriter_ret_pos_step.
   Numerals: 2 ^ 64 (WORD range); 24 / 4 (LENGTH: the failed field of the out struct). No ADDRESS. *)
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
Import ListNotations.
Local Open Scope Z_scope.

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

(* the calls a run appends: the end state's w_calls extends the start's *)
Lemma prhW_calls_ext : forall P ok st,
  exists l, WriterApp.w_calls (prhWriter_putN ok st P) = WriterApp.w_calls st ++ l.
Proof.
  induction P as [|b P IH]; intros ok st; [exists []; rewrite app_nil_r; reflexivity|].
  destruct (prhWriter_grows st b) eqn:Hg.
  - rewrite (prhW_putN_cons_grow ok st b P Hg).
    destruct (IH (tl ok) (prhWriter_put1 (hd true ok) st b)) as (l & E).
    rewrite (prhW_put1_grow_calls (hd true ok) st b Hg) in E.
    exists ([WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)] ++ l).
    rewrite E, app_assoc. reflexivity.
  - rewrite (prhW_putN_cons_nogrow ok st b P Hg).
    destruct (IH ok (WriterApp.put1 st b)) as (l & E).
    destruct (prhW_nogrow_f st b Hg) as (_ & _ & _ & _ & Hc). rewrite Hc in E.
    exists l. exact E.
Qed.

(* THE REQUESTS OF A RUN (the batch kit's prhWriter_reqs, prh_oks's ns): one per call, read off the end state *)
Lemma prhW_reqs_len : forall P ok st, length (prhWriter_reqs ok st P) = prhWriter_k ok st P.
Proof.
  intros P ok st. unfold prhWriter_reqs, prhWriter_k.
  destruct (prhW_calls_ext P ok st) as (l & E). rewrite E, skipn_app, skipn_all, Nat.sub_diag.
  cbn [app skipn]. rewrite length_app, Nat.add_comm, Nat.add_sub. reflexivity.
Qed.

Lemma prhW_reqs_agree : forall P ok ok' st, prhWriter_putN ok' st P = prhWriter_putN ok st P ->
  prhWriter_reqs ok' st P = prhWriter_reqs ok st P.
Proof. intros P ok ok' st E. unfold prhWriter_reqs. rewrite E. reflexivity. Qed.

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

(* the requests of P1 ++ P2: P1's, then P2's from P1's end state with the outcomes left after P1's calls *)
Lemma prhW_reqs_app : forall P1 P2 ok st,
  prhWriter_reqs ok st (P1 ++ P2) =
    prhWriter_reqs ok st P1 ++ prhWriter_reqs (skipn (prhWriter_k ok st P1) ok) (prhWriter_putN ok st P1) P2.
Proof.
  intros P1 P2 ok st. unfold prhWriter_reqs. rewrite prhW_putN_app.
  pose proof (prhW_calls_le P1 ok st) as Hle.
  set (st1 := prhWriter_putN ok st P1) in *. clearbody st1.
  set (ok2 := skipn (prhWriter_k ok st P1) ok). clearbody ok2.
  destruct (prhW_calls_ext P2 ok2 st1) as (l2 & E2).
  rewrite E2, !skipn_app, skipn_all, Nat.sub_diag.
  replace (length (WriterApp.w_calls st) - length (WriterApp.w_calls st1))%nat with 0%nat
    by (symmetry; apply Nat.sub_0_le; exact Hle).
  reflexivity.
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

(* ---- THE RUN EVENTS OF A RUN OF PUTS, counted (the kit's prhWriter_evs, PRH_FnWriter.v:190-199 @d89d3c67b78c: one event
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

(* the next put's event premise (tput_specX, PRH_FnWriter.v:464-465 @d89d3c67b78c) at the exact advance after the
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

(* the next put's consumer window (tput_specX's prh_cons_from, the batch kit) at the exact advance after the puts PP under the
   outcomes ok, from the caller's window over all its puts (PRH_Base.prh_cons_from_sub) *)
Lemma prhWriter_cons_at : forall rp_sm rp_x rp_os rp_i st PP bs R ok,
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (PP ++ bs :: R))) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st PP))
    (length (prhWriter_evs [] (prhWriter_putN ok st PP) [bs])).
Proof.
  intros rp_sm rp_x rp_os rp_i st PP bs R ok HC.
  destruct (prhW_putN_ok_or_failed PP ok st) as [E|E].
  2: { rewrite (prhWriter_evs_failed [bs] [] _ E). unfold PRH_Base.prh_cons_from. intros j e Hj.
       cbn [length] in Hj. lia. }
  assert (HL : length (prhWriter_evs ok st PP) = length (prhWriter_evs [] st PP)).
  { pose proof (prhW_evs_len PP ok st) as L1. pose proof (prhW_evs_len PP [] st) as L2.
    assert (Hk : prhWriter_k ok st PP = prhWriter_k [] st PP) by (unfold prhWriter_k; rewrite E; reflexivity).
    rewrite <- E in L2. lia. }
  rewrite HL, E.
  apply (PRH_Base.prh_cons_from_sub rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (PP ++ bs :: R))));
    [|exact HC].
  rewrite prhWriter_evs_app0. change (bs :: R) with ([bs] ++ R). rewrite prhWriter_evs_app0, !length_app. lia.
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

(* the refusal bit of the composed list (the batch kit's prh_refused) is the first run's on its calls and the second run's on
   the rest *)
Lemma prhW_okc_refused_lo : forall ok1 ok2 k1 k2 c0 f0 c1 f1 i, (i < k1)%nat ->
  prh_refused (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) c0 f0 i = prh_refused ok1 c0 f0 i.
Proof. intros ok1 ok2 k1 k2 c0 f0 c1 f1 i Hi. unfold prh_refused. rewrite prhW_okc_lo by exact Hi. reflexivity. Qed.

Lemma prhW_okc_refused_hi : forall (c0 f0 c1 f1 : Z) (k1 k2 : nat) ok1 ok2 j,
  0 <= c0 -> 0 <= f1 < 2 ^ 64 ->
  (k1 = 0%nat -> c1 = c0) -> ((0 < k1)%nat -> c1 = (c0 + Z.of_nat k1) mod 2 ^ 64) ->
  ((0 < k2)%nat -> f1 = f0) -> (j < k2)%nat ->
  prh_refused (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) c0 f0 (k1 + j) = prh_refused ok2 c1 f1 j.
Proof.
  intros c0 f0 c1 f1 k1 k2 ok1 ok2 j H0 Hf Hk0 Hkp Hff Hj. unfold prh_refused.
  rewrite prhW_okc_hi by exact Hj. rewrite Nat2Z.inj_add, Z.add_assoc.
  destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat j) f0) as [E1|E1].
  - rewrite (proj2 (Z.eqb_eq _ _) (prhW_ctr c0 f0 c1 f1 k1 j H0 (proj2 Hf) (Hff ltac:(lia)) Hk0 Hkp E1)).
    destruct (nth j ok2 true); reflexivity.
  - destruct (Z.eqb_spec (c1 + Z.of_nat j) f1) as [E3|E3]; destruct (nth j ok2 true); reflexivity.
Qed.

Lemma prhW_oks_core : forall (c0 f0 c1 f1 : Z) (k1 k2 : nat) ok1 ok2 ns1 ns2 most ran ran1 ran2,
  0 <= c0 -> 0 <= f1 < 2 ^ 64 ->
  (k1 = 0%nat -> c1 = c0) -> ((0 < k1)%nat -> c1 = (c0 + Z.of_nat k1) mod 2 ^ 64) ->
  ((0 < k2)%nat -> f1 = f0) -> length ns1 = k1 ->
  prh_oks ok1 c0 f0 k1 ns1 most ran ran1 -> prh_oks ok2 c1 f1 k2 ns2 most ran1 ran2 ->
  prh_oks (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) c0 f0 (k1 + k2) (ns1 ++ ns2) most ran ran2.
Proof.
  intros c0 f0 c1 f1 k1 k2 ok1 ok2 ns1 ns2 most ran ran1 ran2 H0 Hf Hk0 Hkp Hff Hn Hok1 Hok2.
  unfold prh_oks in Hok1, Hok2 |- *.
  destruct Hok1 as (A1 & B1 & C1). destruct Hok2 as (A2 & B2 & C2).
  assert (Hsplit : forall i, (i < k1 + k2)%nat -> (i < k1)%nat \/ exists j, (j < k2)%nat /\ i = (k1 + j)%nat).
  { intros i Hi. destruct (Nat.lt_ge_cases i k1) as [H|H]; [left; exact H|right].
    exists (i - k1)%nat. split; lia. }
  pose proof (prhW_okc_refused_hi c0 f0 c1 f1 k1 k2 ok1 ok2) as RH.
  split; [|split].
  - intros i Hi He. destruct (Hsplit i Hi) as [Hl|(j & Hj & ->)].
    + rewrite prhW_okc_lo by exact Hl. exact (A1 i Hl He).
    + rewrite prhW_okc_hi by exact Hj.
      destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat j) f0) as [_|E1]; [reflexivity|].
      exfalso. apply E1. lia.
  - destruct B2 as [E2 | (E2 & j & Hj & Hr & Hm)].
    + destruct B1 as [E1 | (E1 & i & Hi & Hr & Hm)].
      * left. congruence.
      * right. split; [congruence|]. exists i. split; [lia|].
        rewrite prhW_okc_refused_lo by exact Hi. split; [exact Hr|].
        rewrite app_nth1 by lia. exact Hm.
    + right. split; [exact E2|]. exists (k1 + j)%nat. split; [lia|].
      rewrite (RH j H0 Hf Hk0 Hkp Hff Hj). split; [exact Hr|].
      rewrite app_nth2 by lia. replace (k1 + j - length ns1)%nat with j by lia. exact Hm.
  - intros i Hi Hr Hm. destruct (Hsplit i Hi) as [Hl|(j & Hj & ->)].
    + rewrite prhW_okc_refused_lo in Hr by exact Hl. rewrite app_nth1 in Hm by lia.
      pose proof (C1 i Hl Hr Hm) as R1.
      destruct B2 as [E2 | (E2 & _)]; congruence.
    + rewrite (RH j H0 Hf Hk0 Hkp Hff Hj) in Hr. rewrite app_nth2 in Hm by lia.
      replace (k1 + j - length ns1)%nat with j in Hm by lia.
      exact (C2 j Hj Hr Hm).
Qed.

(* no refusal in either run: none in the composed list (the batch kit's posts carry prh_granted, the DEAD family) *)
Lemma prhW_granted_core : forall (c0 f0 c1 f1 : Z) (k1 k2 : nat) ok1 ok2,
  0 <= c0 -> 0 <= f1 < 2 ^ 64 ->
  (k1 = 0%nat -> c1 = c0) -> ((0 < k1)%nat -> c1 = (c0 + Z.of_nat k1) mod 2 ^ 64) ->
  ((0 < k2)%nat -> f1 = f0) ->
  prh_granted ok1 c0 f0 k1 -> prh_granted ok2 c1 f1 k2 ->
  prh_granted (prhW_okc ok1 ok2 k1 k2 c0 f0 c1 f1) c0 f0 (k1 + k2).
Proof.
  intros c0 f0 c1 f1 k1 k2 ok1 ok2 H0 Hf Hk0 Hkp Hff G1 G2. unfold prh_granted in G1, G2 |- *.
  intros i Hi Hb. destruct (Nat.lt_ge_cases i k1) as [Hl|Hl].
  - rewrite prhW_okc_lo in Hb by exact Hl. exact (G1 i Hl Hb).
  - replace i with (k1 + (i - k1))%nat in Hb |- * by lia.
    rewrite prhW_okc_hi in Hb by lia. rewrite Nat2Z.inj_add, Z.add_assoc. revert Hb.
    destruct (Z.eqb_spec (c0 + Z.of_nat k1 + Z.of_nat (i - k1)) f0) as [E1|E1]; intros Hb; [exact E1|].
    revert Hb.
    destruct (Z.eqb_spec (c1 + Z.of_nat (i - k1)) f1) as [E3|E3]; intros Hb; [discriminate Hb|].
    exfalso. exact (E3 (G2 (i - k1)%nat ltac:(lia) Hb)).
Qed.

(* the model side of the composition: one outcome list for P1 ++ P2 that ends where the two runs end, with
   prh_oks (the batch kit's form, over the run's requests prhWriter_reqs) from the two runs' prh_oks, and no refusal when
   neither run has one *)
Lemma prhW_app_model : forall st P1 P2 ok1 ok2 most ran ran1 ran2,
  0 <= WriterApp.w_cnt st ->
  0 <= WriterApp.w_cnt (prhWriter_putN ok1 st P1) < 2 ^ 64 ->
  0 <= WriterApp.w_fail (prhWriter_putN ok1 st P1) < 2 ^ 64 ->
  prh_oks ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) (prhWriter_reqs ok1 st P1)
    most ran ran1 ->
  prh_oks ok2 (WriterApp.w_cnt (prhWriter_putN ok1 st P1)) (WriterApp.w_fail (prhWriter_putN ok1 st P1))
    (prhWriter_k ok2 (prhWriter_putN ok1 st P1) P2) (prhWriter_reqs ok2 (prhWriter_putN ok1 st P1) P2) most ran1 ran2 ->
  exists ok, prhWriter_putN ok st (P1 ++ P2) = prhWriter_putN ok2 (prhWriter_putN ok1 st P1) P2 /\
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P1 ++ P2))
      (prhWriter_reqs ok st (P1 ++ P2)) most ran ran2 /\
    (prh_granted ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) ->
     prh_granted ok2 (WriterApp.w_cnt (prhWriter_putN ok1 st P1)) (WriterApp.w_fail (prhWriter_putN ok1 st P1))
       (prhWriter_k ok2 (prhWriter_putN ok1 st P1) P2) ->
     prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P1 ++ P2))).
Proof.
  intros st P1 P2 ok1 ok2 most ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2.
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
  assert (Hk2 : prhWriter_k (skipn k1 okc) st1 P2 = k2) by (unfold k2, prhWriter_k; rewrite Hskip; reflexivity).
  exists okc. split; [|split].
  - rewrite prhW_putN_app, HkA, HA. exact Hskip.
  - rewrite prhW_k_app, prhW_reqs_app, HkA, HA, Hk2.
    rewrite (prhW_reqs_agree P1 ok1 okc st HA), (prhW_reqs_agree P2 ok2 (skipn k1 okc) st1 Hskip).
    unfold okc.
    exact (prhW_oks_core (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_cnt st1) (WriterApp.w_fail st1)
      k1 k2 ok1 ok2 _ _ most ran ran1 ran2 Hc0 Hf1 Hc1a Hc1b Hff (prhW_reqs_len P1 ok1 st) Hok1 Hok2).
  - intros G1 G2. rewrite prhW_k_app, HkA, HA, Hk2. unfold okc.
    exact (prhW_granted_core (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_cnt st1) (WriterApp.w_fail st1)
      k1 k2 ok1 ok2 Hc0 Hf1 Hc1a Hc1b Hff G1 G2).
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

(* the allocator-blocks arms of the batch kit's prhWriter_ret_ok (PRH_FnWriter.v d89d3c67b78c) when no grow was REFUSED: the
   capacity kept with nothing changed, or the buffer grown (its refusal peak prhWriter_rpeak is 0 then) *)
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

(* THE WRITER TEXTS' POST at the batch kit e45217a4c7ba (tput_specX / tindent_specX / tput_string_specX / twrite_value_specX,
   the DEAD family): prhWriter_ret_ok under outcomes ok with no refusal (prh_granted), named *)
Definition prhWriter_retg (ly : alayout) (S : astate) (Lam : list (Z * Z)) (peak ran most own o buf : Z)
  (st : WriterApp.wst) (P : list (list Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) : Prop :=
  exists ok, prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' /\
    prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P).

(* with no refusal the refusal peak is 0 *)
Lemma prhW_rpeak_granted : forall ok Lam st P,
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) -> prhWriter_rpeak ok Lam st P = 0.
Proof. intros ok Lam st P G. unfold prhWriter_rpeak. apply prh_refused_peak_granted. exact G. Qed.

(* prhWriter_ret_ok at a fixed outcome list with no refusal, from its granted arms and back *)
Lemma prhWriter_ret_ok_of_blk : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'
    ran' buf' Lam' peak',
  prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' ->
  prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) ->
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
    (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own ->
  prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P) ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ran' buf' Lam' peak'
    Hok Hout Hled Hblk G.
  exists ran', buf', Lam', peak'. cbv zeta.
  split; [exact Hok|]. split; [exact Hout|]. split; [exact Hled|].
  destruct Hblk as [A1 | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hp)].
  - left. exact A1.
  - right. right. split; [exact Lt|]. exists l1, l2, b1, b2. split; [exact Hc|]. split; [exact EL|].
    split; [|exact Hp].
    rewrite (prhW_rpeak_granted ok Lam st P G).
    pose proof Hled as Hb. apply prh_ledger_bounds in Hb. destruct Hb as (HL0 & _).
    rewrite EL in HL0. cbn [Ledger.lsum] in HL0. lia.
Qed.

Lemma prhWriter_blk_of_ret_ok : forall ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md',
  prhWriter_ret_ok B ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' ->
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  exists ran' buf' Lam' peak',
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' /\
    prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
      (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own /\
    prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P).
Proof.
  intros ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'
    (ran' & buf' & Lam' & peak' & Hok & Hout & Hled & ARMS) G.
  cbv zeta in Hok, Hout, Hled, ARMS.
  exists ran', buf', Lam', peak'. split; [exact Hok|]. split; [exact Hout|]. split; [exact Hled|].
  unfold prhWriter_blk.
  destruct ARMS as [A1 | [(_ & _ & _ & (i & Hi & Hr) & _) | (Lt & l1 & l2 & b1 & b2 & Hc & EL & Ep & Hp)]].
  - left. exact A1.
  - (* a refused grow: none under prh_granted *)
    exfalso. unfold prh_refused in Hr. apply andb_prop in Hr. destruct Hr as (Hr1 & Hr2).
    apply negb_true_iff in Hr1. apply negb_true_iff in Hr2. apply Z.eqb_neq in Hr2.
    exact (Hr2 (G i Hi Hr1)).
  - right. split; [exact Lt|]. exists l1, l2, b1, b2. split; [exact Hc|]. split; [exact EL|].
    split; [|exact Hp].
    rewrite (prhW_rpeak_granted ok Lam st P G) in Ep.
    pose proof Hled as Hb. apply prh_ledger_bounds in Hb. destruct Hb as (HL0 & _).
    rewrite EL in HL0. cbn [Ledger.lsum] in HL0. lia.
Qed.

Lemma prhWriter_ret_open : forall ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md',
  prhWriter_retg ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' <->
  exists ok ran' buf' Lam' peak',
    prh_oks ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) (prhWriter_reqs ok st P) most ran ran' /\
    prhWriter_out W' mem' Lam' o buf' (prhWriter_putN ok st P) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt (prhWriter_putN ok st P))
      (WriterApp.w_fail (prhWriter_putN ok st P)) ran' most own /\
    prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' (prhWriter_putN ok st P) /\
    prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P).
Proof.
  intros ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'. split.
  - intros (ok & H & G).
    destruct (prhWriter_blk_of_ret_ok ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md' H G)
      as (ran' & buf' & Lam' & peak' & Hok & Hout & Hled & Hblk).
    exists ok, ran', buf', Lam', peak'. split; [exact Hok|]. split; [exact Hout|]. split; [exact Hled|].
    split; [exact Hblk | exact G].
  - intros (ok & ran' & buf' & Lam' & peak' & Hok & Hout & Hled & Hblk & G).
    exists ok. split; [|exact G].
    exact (prhWriter_ret_ok_of_blk ok ly S Lam peak ran most own o buf st P ly' S' Hp' W' regs' mem' md'
      ran' buf' Lam' peak' Hok Hout Hled Hblk G).
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

(* two runs in a row: the first opened (outcomes ok1 with no refusal, ran1, buf1, Lam1, peak1 at state 1, whose
   ledger and writer state hold), the second the writer texts' post prhWriter_retg from state 1. The counter at
   state 0 is not negative (the state-0 ledger's prh_glob gives it): prh_oks counts cnt + i without the 2 ^ 64 wrap,
   and with a negative cnt a call the model decides by the wrapped counter could be a refusal in the second run's
   prh_oks and the allocation set to fail in the whole run's. *)
Lemma prhWriter_ret_app : forall ly S Lam peak ran most own o buf st P1 P2 ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1
  ly2 S2 Hp2 W2 regs2 mem2 md2,
  0 <= WriterApp.w_cnt st ->
  prh_oks ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) (prhWriter_reqs ok1 st P1)
    most ran ran1 ->
  prh_granted ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P1) ->
  prhWriter_out W1 mem1 Lam1 o buf1 (prhWriter_putN ok1 st P1) ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st P1))
    (WriterApp.w_fail (prhWriter_putN ok1 st P1)) ran1 most own ->
  prhWriter_blk ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 (prhWriter_putN ok1 st P1) ->
  prhWriter_retg ly1 S1 Lam1 peak1 ran1 most own o buf1 (prhWriter_putN ok1 st P1) P2 ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  prhWriter_retg ly S Lam peak ran most own o buf st (P1 ++ P2) ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
  intros ly S Lam peak ran most own o buf st P1 P2 ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1 ly2 S2 Hp2 W2 regs2 mem2 md2
    Hc0 Hok1 G1 Hout1 Hled1 Hblk1 Hret2.
  apply prhWriter_ret_open in Hret2.
  destruct Hret2 as (ok2 & ran2 & buf2 & Lam2 & peak2 & Hok2 & Hout2 & Hled2 & Hblk2 & G2).
  pose proof Hled1 as Hb1. apply prh_ledger_bounds in Hb1. destruct Hb1 as (_ & _ & Hr1 & Hf1 & _).
  pose proof Hled1 as Hnd1. apply prh_ledger_nodup in Hnd1.
  destruct (prhW_app_model st P1 P2 ok1 ok2 most ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2) as (ok & Hput & Hoks & HG).
  pose proof (prhW_cap_after P1 ok1 st) as Hcap.
  apply prhWriter_ret_open.
  exists ok, ran2, buf2, Lam2, peak2.
  rewrite Hput.
  split; [exact Hoks|]. split; [exact Hout2|]. split; [exact Hled2|].
  split; [eapply prhW_blk_trans; [exact Hnd1 | exact Hcap | exact Hblk1 | exact Hblk2]|].
  exact (HG G1 G2).
Qed.

(* the empty run: nothing changes in the model; the state may (the walk's no-put arms, e.g. indent with pretty = 0) *)
Lemma prhWriter_ret_nil : forall ly S Lam peak ran most own o buf st ly' S' Hp' W' regs' mem' md',
  prhWriter_out W' mem' Lam o buf st ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  prhWriter_retg ly S Lam peak ran most own o buf st [] ly' S' Hp' W' regs' mem' md'.
Proof.
  intros ly S Lam peak ran most own o buf st ly' S' Hp' W' regs' mem' md' Hout Hled Hperm.
  apply prhWriter_ret_open.
  exists [], ran, buf, Lam, peak.
  rewrite prhW_k_nil.
  split; [|split; [exact Hout|split; [exact Hled|split]]].
  - unfold prh_oks. split; [intros i Hi; exfalso; lia|].
    split; [left; reflexivity|]. intros i Hi; exfalso; lia.
  - unfold prhWriter_blk. left. repeat split; try reflexivity. exact Hperm.
  - intros i Hi; exfalso; lia.
Qed.
(* the writer buffer's block bytes (the body PRH_FnWriter.v carried until the batch kit e45217a4c7ba dropped it with the
   LIVE_<fn> sums; prhWriter_blk_bb states the live-bytes move with it) *)
Definition prhWriter_buf_bytes (st : WriterApp.wst) : Z :=
  if WriterApp.w_cap st =? 0 then 0 else WriterApp.w_cap st + cf_head.
(* ---- the allocator's live bytes move exactly with the writer's buffer along a run of puts: the ONE copy (WalkS7a's
   indent walk, WalkS7b's write_value / put_string walks cite it) ---- *)
Lemma prhWriter_blk_bb : forall ly S Lam peak buf (st : WriterApp.wst) ly' S' Lam' peak' buf' (st' : WriterApp.wst),
  0 <= WriterApp.w_cap st ->
  prhWriter_blk ly S Lam peak buf st ly' S' Lam' peak' buf' st' ->
  blocks_bytes S' - prhWriter_buf_bytes st' = blocks_bytes S - prhWriter_buf_bytes st.
Proof.
intros ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 st1 Hc0 [(Hc & _ & _ & _ & HP) | (Hlt & l1 & l2 & b1 & b2 & Harm & _ & _ & HP)].
- rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP).
  unfold prhWriter_buf_bytes. rewrite Hc. lia.
- rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP).
  rewrite bsum_cons, bsum_app. cbn [snd]. unfold prhWriter_buf_bytes.
  destruct Harm as [(Hz & -> & -> & -> & Hb) | (Hnz & _ & Hb)].
  + rewrite Hb, Hz, Z.eqb_refl. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0)) by lia.
    cbn [bsum fold_right snd]. cbv iota. lia.
  + rewrite Hb, bsum_app, bsum_cons. cbn [snd].
    rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0)) by lia. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st) 0)) by lia.
    cbv iota. lia.
Qed.

(* ---- THE LIVE ROOM ALONG A RUN OF PUTS (the batch kit's prh_live_evs, PRH_Base.v; it replaced the kit's entry sums LIVE_<fn>). A
   caller that holds prh_live_evs at its entry over all its puts' events gives each put's at the put's entry: the
   allocator's live bytes there are the entry's with the writer buffer's change (prhWriter_blk_bb), and the model's
   live sum after the events made so far is at least that (each grant adds its request and removes at most the
   buffer it replaces: prhW_evs_live). ---- *)
(* the model's live list sums to the allocator's live bytes (rs_live (room_of_cf S) is map snd (blocks S)) *)
Lemma prhW_live_sum : forall (S : astate),
  fold_right Z.add 0 (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) = blocks_bytes S.
Proof.
intros S. change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
unfold blocks_bytes, blocks. rewrite map_map. cbn [snd].
induction (st_chunks S) as [|k l IH]; [reflexivity|].
cbn [List.filter List.fold_right]. destruct (is_alloc k); cbn [List.map List.fold_right]; rewrite IH; reflexivity.
Qed.

Lemma prhW_live_at0 : forall (S : astate) (E : list PresetReqAt.hev), prh_live_at S E 0%nat = blocks_bytes S.
Proof.
intros S E. unfold prh_live_at, PresetReqAt.hlive_from. rewrite List.firstn_O. cbn [List.fold_left].
exact (prhW_live_sum S).
Qed.

(* removing one m (m >= 0) lowers a sum by at most m *)
Lemma prhW_sum_rm1 : forall m s, 0 <= m ->
  fold_right Z.add 0 s - m <= fold_right Z.add 0 (PresetReqAt.rm1 m s).
Proof.
intros m s Hm. induction s as [|y r IH]; cbn [PresetReqAt.rm1 fold_right]; [lia|].
destruct (Z.eqb_spec y m) as [->|_]; cbn [fold_right]; lia.
Qed.

Lemma prhW_dbl_pos : forall f c n, 0 < c -> 0 < WriterSpec.dbl f c n.
Proof.
induction f as [|f IH]; intros c n Hc; cbn [WriterSpec.dbl]; [exact Hc|].
destruct (n <=? c); [exact Hc | apply IH; lia].
Qed.

Lemma prhW_newcap_pos : forall c n, 0 <= c -> 0 < WriterSpec.newcap c n.
Proof.
intros c n Hc. unfold WriterSpec.newcap. apply prhW_dbl_pos.
destruct (Z.eqb_spec c 0); lia.
Qed.

(* the all-granted run's events raise the model's live sum by at least the writer buffer's change *)
Lemma prhW_evs_live : forall P st s, 0 <= WriterApp.w_cap st ->
  fold_right Z.add 0 s - prhWriter_buf_bytes st + prhWriter_buf_bytes (prhWriter_putN [] st P)
    <= fold_right Z.add 0 (PresetReqAt.hlive_from s (prhWriter_evs [] st P)).
Proof.
induction P as [|b P IH]; intros st s Hc0.
- cbn [prhWriter_evs prhWriter_putN]. unfold PresetReqAt.hlive_from. cbn [fold_left]. lia.
- destruct (prhWriter_grows st b) eqn:Hg.
  + rewrite (prhW_putN_cons_grow [] st b P Hg). cbn [prhWriter_evs]. rewrite Hg. cbn [hd tl negb].
    destruct (prhW_put1_grow_cases true st b Hg)
      as [(Hc & Hf & Hcap) | [(Hc & _ & Hf & _ & Hcap) | (_ & Habs & _)]]; [| | discriminate Habs].
    * (* the allocation set to fail: no event, the writer failed, the capacity kept *)
      rewrite (proj2 (Z.eqb_eq _ _) Hc). cbn [orb app].
      rewrite (prhWriter_evs_failed P [] (prhWriter_put1 true st b)) by lia.
      rewrite (prhW_putN_failed P [] (prhWriter_put1 true st b)) by lia.
      unfold prhWriter_buf_bytes. rewrite Hcap. unfold PresetReqAt.hlive_from. cbn [fold_left]. lia.
    * (* a grant: its one event *)
      rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [orb app].
      rewrite PresetReqAt.hlive_from_cons.
      pose proof (prhW_newcap_pos (WriterApp.w_cap st) (prhWriter_need st b) Hc0) as Hnc.
      assert (Hc1 : 0 <= WriterApp.w_cap (prhWriter_put1 true st b)) by (rewrite Hcap; lia).
      specialize (IH (prhWriter_put1 true st b) (PresetReqAt.hstep s (prhWriter_ev st b)) Hc1).
      enough (fold_right Z.add 0 s - prhWriter_buf_bytes st + prhWriter_buf_bytes (prhWriter_put1 true st b)
                <= fold_right Z.add 0 (PresetReqAt.hstep s (prhWriter_ev st b))) by lia.
      pose proof (@cf_head_nonneg cp) as Hh.
      unfold prhWriter_buf_bytes, prhWriter_ev. rewrite Hcap.
      rewrite (proj2 (Z.eqb_neq (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)) 0)) by lia.
      destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [E0|E0]; cbn [PresetReqAt.hstep fold_right].
      -- lia.
      -- pose proof (prhW_sum_rm1 (WriterApp.w_cap st + @cf_head cp) s ltac:(lia)). lia.
  + rewrite (prhW_putN_cons_nogrow [] st b P Hg). cbn [prhWriter_evs]. rewrite Hg.
    destruct (prhW_nogrow_f st b Hg) as (_ & Hcap & _).
    specialize (IH (WriterApp.put1 st b) s ltac:(rewrite Hcap; lia)).
    unfold prhWriter_buf_bytes in IH |- *. rewrite Hcap in IH. exact IH.
Qed.

(* one put makes at most one event *)
Lemma prhW_evs1_len : forall ok st b, (length (prhWriter_evs ok st [b]) <= 1)%nat.
Proof.
intros ok st b. cbn [prhWriter_evs]. destruct (prhWriter_grows st b); [|cbn; lia].
destruct ((WriterApp.w_cnt st =? WriterApp.w_fail st) || negb (hd true ok)); cbn; lia.
Qed.

(* THE COMPOSITION: the next put's live room at its entry S1 (after the puts PP under outcomes ok, the allocator's
   live bytes moved by the buffer's change only), from the caller's live room over all its puts at its entry S *)
Lemma prhWriter_live_evs_at : forall (S S1 : astate) st PP bs R ok,
  0 <= WriterApp.w_cap st ->
  prh_live_evs S (prhWriter_evs [] st (PP ++ bs :: R)) ->
  blocks_bytes S1 - prhWriter_buf_bytes (prhWriter_putN ok st PP) = blocks_bytes S - prhWriter_buf_bytes st ->
  prh_live_evs S1 (prhWriter_evs [] (prhWriter_putN ok st PP) [bs]).
Proof.
intros S S1 st PP bs R ok Hc0 HL Hbb.
destruct (prhW_putN_ok_or_failed PP ok st) as [E|E].
2: { rewrite (prhWriter_evs_failed [bs] [] _ E). intros j e Hj. destruct j; discriminate Hj. }
rewrite E in Hbb |- *. set (st1 := prhWriter_putN [] st PP) in *.
intros j e Hj.
assert (Hjl : (j < length (prhWriter_evs [] st1 [bs]))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hj0 : j = 0%nat) by (pose proof (prhW_evs1_len [] st1 bs) as Hl; lia).
subst j.
rewrite prhW_live_at0.
(* the caller's event at the index of this put's event *)
set (A := prhWriter_evs [] st PP).
assert (EE : prhWriter_evs [] st (PP ++ bs :: R) =
  A ++ prhWriter_evs [] st1 [bs] ++ prhWriter_evs [] (prhWriter_putN [] st1 [bs]) R).
{ unfold A, st1. rewrite prhWriter_evs_app0. f_equal.
  change (bs :: R) with ([bs] ++ R). rewrite prhWriter_evs_app0. reflexivity. }
assert (HN : nth_error (prhWriter_evs [] st (PP ++ bs :: R)) (length A + 0) = Some e).
{ rewrite EE, nth_error_app2 by lia. replace (length A + 0 - length A)%nat with 0%nat by lia.
  rewrite nth_error_app1; [exact Hj | exact Hjl]. }
pose proof (HL _ _ HN) as H1.
assert (HA : prh_live_at S (prhWriter_evs [] st (PP ++ bs :: R)) (length A + 0) =
  fold_right Z.add 0 (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) A)).
{ unfold prh_live_at. rewrite EE, Nat.add_0_r, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  reflexivity. }
rewrite HA in H1.
pose proof (prhW_evs_live PP st (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) Hc0) as H2.
rewrite prhW_live_sum in H2. fold A in H2. fold st1 in H2.
lia.
Qed.

(* ---- THE MODEL-RUN POSITION along a run of puts (the batch kit e45217a4c7ba, PRH_FnWriter.v d89d3c67b78c). prhWriter_put_pos
   names tput_specX's per-arm position post, keyed on the failed field at o + 24: f' = 0 advances by one; f' = 1 (the
   chosen failure) keeps the index with SOME history (the kit owner's ruling on a Theorem Labs lane's measurement: fuzz_realloc's NULL
   arm gives `exists hist'`).
   prhWriter_ret_pos is the post of the writer texts that call put (tindent_specX, tput_string_specX,
   twrite_value_specX): prhWriter_ret_ok under outcomes ok with no refusal (prh_granted) and the position at the
   EXACT advance rp_i + length (prhWriter_evs ok st P). prhWriter_ret_pos_nil starts a run; prhWriter_ret_pos_step
   adds one put (the put's event premise is prhWriter_ev_at). ---- *)
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
  assert (G0 : prh_granted [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st []))
    by (rewrite prhW_k_nil; intros i Hi; exfalso; lia).
  exists []. split; [|split; [exact G0|]].
  - apply (prhWriter_ret_ok_of_blk [] ly S Lam peak ran most own o buf st [] ly' S' Hp' W' regs' mem' md'
      ran buf Lam peak); [| exact Hout | exact Hled | | exact G0].
    + rewrite prhW_k_nil. unfold prh_oks. split; [intros i Hi; exfalso; lia|].
      split; [left; reflexivity|]. intros i Hi; exfalso; lia.
    + left. repeat split; try reflexivity. exact Hperm.
  - exists rp_hist. cbn [prhWriter_evs length]. rewrite Nat.add_0_r. exact Hp.
Qed.

(* one more put: the run PP so far opened (outcomes ok1 with no refusal, as prhWriter_ret_app takes it), then the
   put's text post (its per-arm position at rp_c, the advance after PP, and its prhWriter_retg over [bs]) *)
Lemma prhWriter_ret_pos_step : forall rp_sm rp_x rp_os rp_H0 rp_i rp_c hist1 ly S Lam peak ran most own o buf st PP bs
    ok1 ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1 ly2 S2 Hp2 W2 regs2 mem2 md2,
  0 <= WriterApp.w_cnt st ->
  rp_c = (rp_i + length (prhWriter_evs ok1 st PP))%nat ->
  prh_oks ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st PP) (prhWriter_reqs ok1 st PP)
    most ran ran1 ->
  prh_granted ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st PP) ->
  prhWriter_out W1 mem1 Lam1 o buf1 (prhWriter_putN ok1 st PP) ->
  prh_ledger B ly1 S1 Hp1 W1 mem1 Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st PP))
    (WriterApp.w_fail (prhWriter_putN ok1 st PP)) ran1 most own ->
  prhWriter_blk ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 (prhWriter_putN ok1 st PP) ->
  prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_c hist1 (prhWriter_putN ok1 st PP) bs o W2 mem2 S2 ->
  prhWriter_retg ly1 S1 Lam1 peak1 ran1 most own o buf1 (prhWriter_putN ok1 st PP) [bs] ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  prhWriter_ret_pos rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran most own o buf st (PP ++ [bs]) ly2 S2 Hp2 W2 regs2 mem2 md2.
Proof.
  intros rp_sm rp_x rp_os rp_H0 rp_i rp_c hist1 ly S Lam peak ran most own o buf st PP bs ok1 ran1 buf1 Lam1 peak1
    ly1 S1 Hp1 W1 mem1 ly2 S2 Hp2 W2 regs2 mem2 md2 Hc0 Hrc Hok1 G1 Hout1 Hled1 Hblk1 (HN & HG) Hret2.
  apply prhWriter_ret_open in Hret2.
  destruct Hret2 as (ok2 & ran2 & buf2 & Lam2 & peak2 & Hok2 & Hout2 & Hled2 & Hblk2 & G2).
  pose proof Hled1 as Hb1. apply prh_ledger_bounds in Hb1. destruct Hb1 as (_ & _ & Hr1 & Hf1 & _).
  pose proof Hled1 as Hnd1. apply prh_ledger_nodup in Hnd1.
  destruct (prhW_app_model st PP [bs] ok1 ok2 most ran ran1 ran2 Hc0 Hr1 Hf1 Hok1 Hok2) as (ok & Hput & Hoks & HGr).
  pose proof (prhW_cap_after PP ok1 st) as Hcap.
  exists ok. split; [|split; [exact (HGr G1 G2)|]].
  { apply (prhWriter_ret_ok_of_blk ok ly S Lam peak ran most own o buf st (PP ++ [bs]) ly2 S2 Hp2 W2 regs2 mem2 md2
      ran2 buf2 Lam2 peak2);
      [exact Hoks | rewrite Hput; exact Hout2 | rewrite Hput; exact Hled2 | rewrite Hput | exact (HGr G1 G2)].
    eapply prhW_blk_trans; [exact Hnd1 | exact Hcap | exact Hblk1 | exact Hblk2]. }
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
    + (* fuzz_realloc returned NULL (the allocation set to fail; a refusal is excluded by prh_granted): no event,
         the index kept with some history *)
      rewrite E1 in LW. cbn [andb negb Z.eqb] in LW.
      replace (rp_i + length (prhWriter_evs ok st (PP ++ [bs])))%nat
        with (rp_i + length (prhWriter_evs ok1 st PP))%nat by lia.
      apply HF. lia.
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
