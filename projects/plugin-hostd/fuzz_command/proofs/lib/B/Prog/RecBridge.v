(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from an earlier version of lib/A/Prog/sup_pin_accept_s3.v (spa_acall_one, spa_rep_add; the frame relocation for fuzz_command) for fuzz_command.asan-ubsan's program-walk kit: the step generalised from the first argument of call REC_PIN_ACCEPT to argument m of any call, in both directions, over B's representation (lib/B/Prog/CmdRep.v) and record()'s slot (lib/B/Prog/record_c.v rec_slot). *)
(* The bridge between the two forms the B statements state a recorded call in.

   - The raw form (A's arg_line, arg_i, mix_call and the inlined arg_s of the A sup_* walks): a slot c of g_rec's
     call table or record.spill, its nargs field m, and the two stores of an append (nargs := m + 1, args[m] := p).
   - The recorder-level form (B's record_c.v and arg_s_c.v, a deliberate B class by this port's decision, relayed
     2026-10-29): c = rec_slot R and `rec_repA B ly S rd (rec_record R fn A) O`, the recorder holding the call
     (fn, A) that record() started in that slot.

   Backward (recorder -> raw): `arep_bridge_slot` / `rec_bridge_slot` give the slot disjunction, nargs = length A,
   length A <= 6 and the slot's acall_at, which is what A-form callees (arg_line, mix_call) ask; `rec_slot_entry`
   gives answer's form of the slot (the call's index in the table, or the spill).
   Forward (raw -> recorder): `arep_bridge_add` / `rec_bridge_add` rebuild the recorder after an append whose two
   stores are the only change to g_rec and record.spill: rec_record R fn (A ++ [y]), owning the new block. A's
   spa_rep_add (sup_pin_accept_s3.v:76) is its case fn = REC_PIN_ACCEPT, A = []. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep record_c RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ small facts *)

Lemma bridge_aval_keep : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hlt. rewrite (Hk k Hlt). exact (H k Hlt). Qed.

Lemma bridge_snoc_split : forall {X} (l : list X) n, length l = S n -> exists l0 x, l = l0 ++ [x] /\ length l0 = n.
Proof.
intros X l n H. destruct (rev l) as [|x r] eqn:E.
- apply (f_equal (@length X)) in E. rewrite length_rev in E. cbn in E. lia.
- exists (rev r), x. split.
  + rewrite <- (rev_involutive l), E. reflexivity.
  + apply (f_equal (@length X)) in E. rewrite length_rev in E. cbn in E. rewrite length_rev. lia.
Qed.

(* one more argument for a recorded call: the slot's nargs field m + 1 and args[m] = p are the only bytes of the
   entry that change; the earlier arguments' blocks keep their bytes *)
Lemma acall_at_snoc : forall bl bl' (rd rd' : reader) c fn A P y p n,
acall_at bl rd c (fn, A) P -> (length A < 6)%nat ->
(forall i, 0 <= i < CALL_SIZE -> ~ (CALL_OFF_NARGS <= i < CALL_OFF_NARGS + 4) ->
 ~ (CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
 rd' (c + i) = rd (c + i)) ->
(forall pn, In pn P -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
In (p, n) bl' -> ~ In p (map fst P) -> p <> 0 -> Z.of_nat (length y) + 1 <= n <= LMAX + 2 ->
aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p y ->
acall_at bl' rd' c (fn, A ++ [y]) (P ++ [(p, n)]).
Proof.
intros bl bl' rd rd' c fn A P y p n (Hfn & H6 & HL & Vfn & Vna & HND & Hargs) Hm Hk HP Hpin Hpn Hp0 Hn Hna Harg Hstr.
cbn [fst snd] in Hfn, H6, HL, Vfn, Vna, Hargs.
unfold acall_at. cbn [fst snd].
split; [exact Hfn|].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app; cbn [length]; lia|].
split.
{ apply (bridge_aval_keep rd rd' _ 4 fn Vfn). intros k Hk4.
  replace (c + CALL_OFF_FN + Z.of_nat k) with (c + (CALL_OFF_FN + Z.of_nat k)) by lia.
  apply Hk; unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE; lia. }
split.
{ replace (Z.of_nat (length (A ++ [y]))) with (Z.of_nat (length A) + 1) by (rewrite length_app; cbn [length]; lia).
  exact Hna. }
split.
{ rewrite map_app. cbn [map fst]. apply NoDup_ListNoDup. apply NoDup_ListNoDup in HND.
  apply List.NoDup_app; [exact HND | constructor; [intros [] | constructor] |].
  intros a Ha Hb. destruct Hb as [<- | []]. exact (Hpn Ha). }
intros k s pn Hs Hpk.
destruct (Nat.lt_ge_cases k (length A)) as [Hlt | Hge].
- rewrite nth_error_app1 in Hs by exact Hlt. rewrite nth_error_app1 in Hpk by lia.
  destruct (Hargs k s pn Hs Hpk) as (V & Hnz & Hin & Hlen & Hst).
  assert (HPin : In pn P) by exact (nth_error_In P k Hpk).
  destruct (HP pn HPin) as [Hin' Hag].
  split.
  { apply (bridge_aval_keep rd rd' _ 8 (fst pn) V). intros j Hj.
    replace (c + CALL_OFF_ARGS + 8 * Z.of_nat k + Z.of_nat j) with (c + (CALL_OFF_ARGS + 8 * Z.of_nat k + Z.of_nat j)) by lia.
    apply Hk; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE; lia. }
  split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|].
  apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hst | exact Hag | lia | lia].
- destruct (Nat.eq_dec k (length A)) as [-> | Hne].
  + rewrite nth_error_app2 in Hs by lia. rewrite Nat.sub_diag in Hs. cbn in Hs. injection Hs as <-.
    rewrite nth_error_app2 in Hpk by lia. rewrite <- HL, Nat.sub_diag in Hpk. cbn in Hpk. injection Hpk as <-.
    cbn [fst snd]. split; [exact Harg|]. split; [exact Hp0|]. split; [exact Hpin|]. split; [exact Hn|]. exact Hstr.
  + exfalso. assert (Hk' : (length (A ++ [y]) <= k)%nat) by (rewrite length_app; cbn [length]; lia).
    apply nth_error_None in Hk'. rewrite Hk' in Hs. discriminate.
Qed.

(* the representation's fields outside the call table and the spill: kept when their bytes and the answer and reply
   blocks are kept and the model leaves them alone *)
Lemma arep_at_other : forall bl bl' (rd rd' : reader) R R' Q Q',
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
r_refuse R' = r_refuse R -> r_code R' = r_code R -> r_answer R' = r_answer R -> r_nreplies R' = r_nreplies R ->
r_reply R' = r_reply R -> r_state R' = r_state R -> r_host R' = r_host R ->
l_answer Q' = l_answer Q -> l_reply Q' = l_reply Q ->
rd_agree rd rd' A_G_REC OFF_CALLS -> rd_agree rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER) ->
(forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
ag1_calls bl' rd' A_G_REC A_REC_SPILL R' Q' ->
ag1_own A_G_REC A_REC_SPILL Q' ->
arep_at bl' rd' A_G_REC A_REC_SPILL R' Q'.
Proof.
intros bl bl' rd rd' R R' Q Q' (Hg8 & Hs8 & Hap & _ & HA & HR & HSC & _) E1 E2 E3 E4 E5 E6 E7 F1 F2 Hlo Hhi Hblk HC' HO'.
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|]. split; [exact HC'|].
split.
{ rewrite E3, F1. unfold aanswer_at in *.
  destruct (r_answer R) as [x|], (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HA as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    destruct (Hblk pn) as [Hin' Hgp]; [apply in_or_app; left; try rewrite EA; cbn [oblk In]; left; reflexivity|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V | exact Hhi | lia | unfold REC_SIZE, OFF_ANSWER; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact Hgp | lia | lia].
  - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact HA | exact Hhi | lia | unfold REC_SIZE, OFF_ANSWER; cbn; lia]. }
split.
{ rewrite E5, F2. unfold areply_at in *.
  destruct (r_reply R) as [x|], (l_reply Q) as [pr|] eqn:ER; try contradiction.
  - destruct HR as (V1 & V2 & Hnz & Hne & Hin & Hl & Hb & Hlx).
    destruct (Hblk pr) as [Hin' Hgp]; [apply in_or_app; right; try rewrite ER; cbn [oblk In]; left; reflexivity|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V1 | exact Hhi | unfold OFF_REPLY, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY; cbn; lia]|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V2 | exact Hhi | unfold OFF_REPLY_SIZE, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY_SIZE; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hl|]. split; [|exact Hlx].
    apply (abytes_atR_agree_in rd rd' (fst pr) (snd pr)); [exact Hb | exact Hgp | lia | lia].
  - destruct HR as [V1 V2].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V1 | exact Hhi | unfold OFF_REPLY, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY; cbn; lia]|].
    apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V2 | exact Hhi | unfold OFF_REPLY_SIZE, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY_SIZE; cbn; lia]. }
split; [|exact HO'].
destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rg). unfold ag1_scalars. rewrite E1, E2, E4, E6, E7.
split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_CALLS);
  [exact Vr | exact Hlo | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, OFF_CALLS; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_CALLS);
  [exact Vc | exact Hlo | unfold OFF_CODE; lia | unfold OFF_CODE, OFF_CALLS; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
  [exact Vn | exact Hhi | unfold OFF_NREPLIES, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_NREPLIES; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
  [exact Vs | exact Hhi | unfold OFF_STATE, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_STATE; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
  [exact Vh | exact Hhi | unfold OFF_HOST, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_HOST; cbn; lia]|].
exact Rg.
Qed.

(* the recorder's own blocks with one new block (p, n) added *)
Lemma ag1_own_add : forall Q Q' p n,
Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q) ->
ag1_own A_G_REC A_REC_SPILL Q -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
ag1_own A_G_REC A_REC_SPILL Q'.
Proof.
intros Q Q' p n HPerm (HND & Hown) Hpn Hpg Hps. split.
- apply NoDup_ListNoDup. apply NoDup_ListNoDup in HND.
  apply (Permutation_NoDup (Permutation_sym (Permutation_map fst HPerm))).
  cbn [map fst]. constructor; [exact Hpn | exact HND].
- intros pn Hin. assert (Hin2 : In pn ((p, n) :: lay_blocks Q)) by (eapply Permutation_in; [exact HPerm | exact Hin]).
  destruct Hin2 as [<- | Hin2]; [cbn [fst snd]; split; assumption | exact (Hown pn Hin2)].
Qed.

(* ------------------------------------------------------------------ backward: recorder -> raw *)

(* the call (fn, A) record() started is the slot's: in the table at index length (r_calls R), or the spill *)
Lemma rec_slot_entry : forall R fn A,
(exists k, nth_error (r_calls (rec_record R fn A)) k = Some (fn, A) /\
  rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (fn, A) = r_spill (rec_record R fn A)).
Proof.
intros R fn A. unfold rec_slot, rec_record. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt.
- left. exists (length (r_calls R)). cbn [r_calls set_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [r_spill set_spill]. split; reflexivity.
Qed.

Lemma arep_bridge_slot : forall bl (rd : reader) R fn A Q,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) Q ->
((exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ rec_slot R = A_REC_SPILL) /\
aval_mem rd (rec_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) /\ (length A <= 6)%nat /\
exists P, acall_at bl rd (rec_slot R) (fn, A) P /\ (forall pn, In pn P -> In pn (lay_blocks Q)).
Proof.
intros bl rd R fn A Q HA.
assert (Hc : exists P, acall_at bl rd (rec_slot R) (fn, A) P /\ (forall pn, In pn P -> In pn (lay_blocks Q))).
{ revert HA. unfold rec_record, rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; intros HA.
  - destruct HA as (_ & _ & _ & (Hlen & HlenQ & _ & Hcalls & _) & _).
    cbn [r_calls set_calls] in Hlen, HlenQ, Hcalls.
    assert (Hnl : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A))
      by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
    destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:HP.
    + destruct (Hcalls _ _ _ Hnl HP) as [HCl _]. exists P. split; [exact HCl|].
      intros pn Hpn. unfold lay_blocks. apply in_or_app. left. exact (In_concat_nth _ _ P pn HP Hpn).
    + exfalso. apply nth_error_None in HP. rewrite HlenQ, length_app in HP. cbn [length] in HP. lia.
  - destruct HA as (_ & _ & _ & (_ & _ & _ & _ & Hspill & _) & _). cbn [r_spill set_spill] in Hspill.
    exists (l_spill Q). split; [exact Hspill|].
    intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
destruct Hc as (P & HCa & HPin).
pose proof HCa as (_ & H6 & _ & _ & Vna & _). cbn [snd] in H6, Vna.
split.
{ unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; [left | right; reflexivity].
  apply Nat.ltb_lt in Elt. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity]. }
split; [exact Vna|]. split; [exact H6|]. exists P. split; [exact HCa | exact HPin].
Qed.

(* ------------------------------------------------------------------ forward: raw -> recorder *)

Lemma arep_add_calls : forall bl bl' (rd rd' : reader) R fn A Q y p n c,
(length (r_calls R) < 16)%nat -> c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
arep_at bl rd A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, A)])) Q ->
(length A < 6)%nat ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
  ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
  rd' a = rd a) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
In (p, n) bl' -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
p <> 0 -> Z.of_nat (length y) + 1 <= n <= LMAX + 2 -> Z.of_nat (length y) <= LMAX ->
aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p y ->
exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, A ++ [y])])) Q' /\
  Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q).
Proof.
intros bl bl' rd rd' R fn A Q y p n c Hlt Hc HA Hm Hkeep Hblk Hpin Hpn Hpg Hps Hp0 Hn Hly Hna Harg Hstr.
pose proof HA as (_ & _ & _ & (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf) & _ & _ & _ & HOWN).
cbn [r_calls r_spill set_calls] in Hlen, HlenQ, Hnc, Hcalls, Hspill, Hspf.
assert (HlQ : length (l_calls Q) = S (length (r_calls R))) by (rewrite HlenQ, length_app; cbn [length]; lia).
destruct (bridge_snoc_split (l_calls Q) (length (r_calls R)) HlQ) as (lc & Plast & HlcQ & Hlc).
assert (Hnl : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A))
  by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
assert (Hnq : nth_error (l_calls Q) (length (r_calls R)) = Some Plast)
  by (rewrite HlcQ, nth_error_app2 by lia; rewrite Hlc, Nat.sub_diag; reflexivity).
destruct (Hcalls _ _ _ Hnl Hnq) as [HCl HFl]. cbn [snd] in HFl. rewrite <- Hc in HCl.
assert (Elay : lay_blocks Q = (concat lc ++ Plast) ++ (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
{ unfold lay_blocks. rewrite HlcQ, concat_app. cbn [concat]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
set (Q' := RLay (lc ++ [Plast ++ [(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
assert (Eq' : lay_blocks Q' = (concat lc ++ Plast) ++ (p, n) :: (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
{ unfold lay_blocks, Q'. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r, <- !app_assoc. reflexivity. }
assert (HPerm : Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q)).
{ rewrite Eq', Elay. apply Permutation_sym, Permutation_middle. }
assert (Hout : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (c <= a < c + CALL_SIZE) -> rd' a = rd a).
{ intros a Ha Hna'. apply Hkeep; [exact Ha | |]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia. }
assert (Hslot : forall i, 0 <= i < CALL_SIZE -> ~ (CALL_OFF_NARGS <= i < CALL_OFF_NARGS + 4) ->
  ~ (CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
  rd' (c + i) = rd (c + i)).
{ intros i Hi H1 H2. apply Hkeep.
  - left. subst c. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  - lia.
  - lia. }
assert (Hlo : rd_agree rd rd' A_G_REC OFF_CALLS).
{ intros i Hi. apply Hout; [left; unfold OFF_CALLS, REC_SIZE in *; lia | subst c; unfold OFF_CALLS, CALL_SIZE in *; lia]. }
assert (Hhi : rd_agree rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER)).
{ intros i Hi. apply Hout; [left; unfold OFF_ANSWER, REC_SIZE in *; lia |].
  subst c. unfold OFF_CALLS, OFF_ANSWER, REC_SIZE, CALL_SIZE in *. lia. }
assert (HPl : forall pn, In pn Plast -> In pn (lay_blocks Q)).
{ intros pn Hpn0. rewrite Elay. apply in_or_app. left. apply in_or_app. right. exact Hpn0. }
assert (HC' : ag1_calls bl' rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, A ++ [y])])) Q').
{ unfold ag1_calls, Q'. cbn [r_calls r_spill set_calls l_calls l_spill].
  split; [rewrite length_app; cbn [length]; rewrite length_app in Hlen; cbn [length] in Hlen; lia|].
  split; [rewrite !length_app; cbn [length]; lia|].
  split.
  { replace (length (r_calls R ++ [(fn, A ++ [y])])) with (length (r_calls R ++ [(fn, A)]))
      by (rewrite !length_app; reflexivity).
    apply (aval_mem_agree_in rd rd' A_G_REC OFF_CALLS); [exact Hnc | exact Hlo | unfold OFF_NCALLS; lia |].
    unfold OFF_NCALLS, OFF_CALLS. cbn. lia. }
  split.
  { intros i ci Pi Hci HPi.
    destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hil | Hil].
    - rewrite nth_error_app1 in Hci by exact Hil. rewrite nth_error_app1 in HPi by lia.
      assert (Hc0 : nth_error (r_calls R ++ [(fn, A)]) i = Some ci) by (rewrite nth_error_app1 by exact Hil; exact Hci).
      assert (HP0 : nth_error (l_calls Q) i = Some Pi) by (rewrite HlcQ, nth_error_app1 by lia; exact HPi).
      destruct (Hcalls i ci Pi Hc0 HP0) as [HCi HFi]. split; [|exact HFi].
      apply (acall_at_agree bl bl' rd rd'); [exact HCi | |].
      + intros j Hj. apply Hout; [left; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia |].
        subst c. unfold OFF_CALLS, CALL_SIZE in *. lia.
      + intros pn Hpn0. apply Hblk. rewrite Elay. apply in_or_app. left. apply in_or_app. left.
        exact (In_concat_nth lc i Pi pn HPi Hpn0).
    - destruct (Nat.eq_dec i (length (r_calls R))) as [-> | Hne].
      + rewrite nth_error_app2 in Hci by lia. rewrite Nat.sub_diag in Hci. cbn in Hci. injection Hci as <-.
        rewrite nth_error_app2 in HPi by lia. rewrite Hlc, Nat.sub_diag in HPi. cbn in HPi. injection HPi as <-.
        split.
        * rewrite <- Hc. apply (acall_at_snoc bl bl' rd rd' c fn A Plast y p n HCl Hm Hslot).
          -- intros pn Hpn0. exact (Hblk pn (HPl pn Hpn0)).
          -- exact Hpin.
          -- intros Hin. apply Hpn. apply in_map_iff in Hin as (pn & Hpe & Hpn0).
             apply in_map_iff. exists pn. split; [exact Hpe | exact (HPl pn Hpn0)].
          -- exact Hp0.
          -- exact Hn.
          -- exact Hna.
          -- exact Harg.
          -- exact Hstr.
        * cbn [snd]. apply Forall_app. split; [exact HFl | constructor; [exact Hly | constructor]].
      + exfalso. assert (Hk' : (length (r_calls R ++ [(fn, A ++ [y])]) <= i)%nat) by (rewrite length_app; cbn [length]; lia).
        apply nth_error_None in Hk'. rewrite Hk' in Hci. discriminate. }
  split; [|exact Hspf].
  apply (acall_at_agree bl bl' rd rd'); [exact Hspill | |].
  - intros j Hj. apply Hout; [right; unfold CALL_SIZE, SC_SIZE in *; lia |].
    subst c. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *. lia.
  - intros pn Hpn0. apply Hblk. rewrite Elay. apply in_or_app. right. apply in_or_app. left. exact Hpn0. }
exists Q'. split; [|exact HPerm].
apply (arep_at_other bl bl' rd rd' _ _ Q Q' HA); try reflexivity; [exact Hlo | exact Hhi | | exact HC' |].
- intros pn Hpn0. apply Hblk. rewrite Elay. apply in_or_app. right. apply in_or_app. right. exact Hpn0.
- exact (ag1_own_add Q Q' p n HPerm HOWN Hpn Hpg Hps).
Qed.

Lemma arep_add_spill : forall bl bl' (rd rd' : reader) R fn A Q y p n,
arep_at bl rd A_G_REC A_REC_SPILL (set_spill R (fn, A)) Q ->
(length A < 6)%nat ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) ->
  ~ (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
  rd' a = rd a) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
In (p, n) bl' -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
p <> 0 -> Z.of_nat (length y) + 1 <= n <= LMAX + 2 -> Z.of_nat (length y) <= LMAX ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p y ->
exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (fn, A ++ [y])) Q' /\
  Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q).
Proof.
intros bl bl' rd rd' R fn A Q y p n HA Hm Hkeep Hblk Hpin Hpn Hpg Hps Hp0 Hn Hly Hna Harg Hstr.
pose proof HA as (_ & _ & _ & (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf) & _ & _ & _ & HOWN).
cbn [r_calls r_spill set_spill fst snd] in Hlen, HlenQ, Hnc, Hcalls, Hspill, Hspf.
assert (Elay : lay_blocks Q = (concat (l_calls Q) ++ l_spill Q) ++ (oblk (l_answer Q) ++ oblk (l_reply Q))).
{ unfold lay_blocks. rewrite <- !app_assoc. reflexivity. }
set (Q' := RLay (l_calls Q) (l_spill Q ++ [(p, n)]) (l_answer Q) (l_reply Q)).
assert (Eq' : lay_blocks Q' = (concat (l_calls Q) ++ l_spill Q) ++ (p, n) :: (oblk (l_answer Q) ++ oblk (l_reply Q))).
{ unfold lay_blocks, Q'. cbn [l_calls l_spill l_answer l_reply]. rewrite <- !app_assoc. reflexivity. }
assert (HPerm : Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q)).
{ rewrite Eq', Elay. apply Permutation_sym, Permutation_middle. }
assert (Hout : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_REC_SPILL <= a < A_REC_SPILL + CALL_SIZE) -> rd' a = rd a).
{ intros a Ha Hna'. apply Hkeep; [exact Ha | |]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia. }
assert (Hslot : forall i, 0 <= i < CALL_SIZE -> ~ (CALL_OFF_NARGS <= i < CALL_OFF_NARGS + 4) ->
  ~ (CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
  rd' (A_REC_SPILL + i) = rd (A_REC_SPILL + i)).
{ intros i Hi H1 H2. apply Hkeep.
  - right. unfold CALL_SIZE, SC_SIZE in *. lia.
  - lia.
  - lia. }
assert (Hlo : rd_agree rd rd' A_G_REC OFF_CALLS).
{ intros i Hi. apply Hout; [left; unfold OFF_CALLS, REC_SIZE in *; lia |].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *. lia. }
assert (Hhi : rd_agree rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER)).
{ intros i Hi. apply Hout; [left; unfold OFF_ANSWER, REC_SIZE in *; lia |].
  unfold A_G_REC, A_REC_SPILL, OFF_ANSWER, REC_SIZE, CALL_SIZE in *. lia. }
assert (HC' : ag1_calls bl' rd' A_G_REC A_REC_SPILL (set_spill R (fn, A ++ [y])) Q').
{ unfold ag1_calls, Q'. cbn [r_calls r_spill set_spill l_calls l_spill fst snd].
  split; [exact Hlen|]. split; [exact HlenQ|].
  split.
  { apply (aval_mem_agree_in rd rd' A_G_REC OFF_CALLS); [exact Hnc | exact Hlo | unfold OFF_NCALLS; lia |].
    unfold OFF_NCALLS, OFF_CALLS. cbn. lia. }
  split.
  { intros i ci Pi Hci HPi. destruct (Hcalls i ci Pi Hci HPi) as [HCi HFi]. split; [|exact HFi].
    assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hci; discriminate).
    apply (acall_at_agree bl bl' rd rd'); [exact HCi | |].
    - intros j Hj. apply Hout; [left; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia |].
      unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *. lia.
    - intros pn Hpn0. apply Hblk. rewrite Elay. apply in_or_app. left. apply in_or_app. left.
      exact (In_concat_nth _ i Pi pn HPi Hpn0). }
  split.
  - apply (acall_at_snoc bl bl' rd rd' A_REC_SPILL fn A (l_spill Q) y p n Hspill Hm Hslot).
    + intros pn Hpn0. apply Hblk. rewrite Elay. apply in_or_app. left. apply in_or_app. right. exact Hpn0.
    + exact Hpin.
    + intros Hin. apply Hpn. apply in_map_iff in Hin as (pn & Hpe & Hpn0).
      apply in_map_iff. exists pn. split; [exact Hpe|].
      rewrite Elay. apply in_or_app. left. apply in_or_app. right. exact Hpn0.
    + exact Hp0.
    + exact Hn.
    + exact Hna.
    + exact Harg.
    + exact Hstr.
  - apply Forall_app. split; [exact Hspf | constructor; [exact Hly | constructor]]. }
exists Q'. split; [|exact HPerm].
apply (arep_at_other bl bl' rd rd' _ _ Q Q' HA); try reflexivity; [exact Hlo | exact Hhi | | exact HC' |].
- intros pn Hpn0. apply Hblk. rewrite Elay. apply in_or_app. right. exact Hpn0.
- exact (ag1_own_add Q Q' p n HPerm HOWN Hpn Hpg Hps).
Qed.

(* the forward bridge: the raw append (nargs := m + 1, args[m] := p, every other byte of g_rec and record.spill kept,
   the recorder's blocks kept, p a new live block apart from both statics) gives the recorder holding the call with
   y appended, owning the new block *)
Lemma arep_bridge_add : forall bl bl' (rd rd' : reader) R fn A Q y p n,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) Q ->
(length A < 6)%nat ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (rec_slot R + CALL_OFF_NARGS <= a < rec_slot R + CALL_OFF_NARGS + 4) ->
  ~ (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
  rd' a = rd a) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
In (p, n) bl' -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
p <> 0 -> Z.of_nat (length y) + 1 <= n <= LMAX + 2 -> Z.of_nat (length y) <= LMAX ->
aval_mem rd' (rec_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p y ->
exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn (A ++ [y])) Q' /\
  Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q).
Proof.
intros bl bl' rd rd' R fn A Q y p n HA Hm Hkeep Hblk Hpin Hpn Hpg Hps Hp0 Hn Hly Hna Harg Hstr.
revert HA Hkeep Hna Harg. unfold rec_record, rec_slot.
destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; intros HA Hkeep Hna Harg.
- apply Nat.ltb_lt in Elt.
  exact (arep_add_calls bl bl' rd rd' R fn A Q y p n
    (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) Elt eq_refl HA Hm Hkeep Hblk Hpin Hpn
    Hpg Hps Hp0 Hn Hly Hna Harg Hstr).
- exact (arep_add_spill bl bl' rd rd' R fn A Q y p n HA Hm Hkeep Hblk Hpin Hpn Hpg Hps Hp0 Hn Hly Hna Harg Hstr).
Qed.

(* ------------------------------------------------------------------ the two directions over rec_repA *)

Section d.
Variable B : asyms.

Lemma rec_bridge_slot : forall ly S (rd : reader) R fn A O,
rec_repA B ly S rd (rec_record R fn A) O ->
((exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ rec_slot R = A_REC_SPILL) /\
aval_mem rd (rec_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) /\ (length A <= 6)%nat /\
exists P, acall_at (ablocks B ly S) rd (rec_slot R) (fn, A) P /\ (forall pn, In pn P -> In pn O).
Proof.
intros ly S rd R fn A O (Q & HA & HO).
destruct (arep_bridge_slot _ rd R fn A Q HA) as (H1 & H2 & H3 & P & H4 & H5).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists P. split; [exact H4|].
intros pn Hpn. apply HO. exact (H5 pn Hpn).
Qed.

Lemma rec_bridge_add : forall ly S ly' S' (rd rd' : reader) R fn A O y p n,
rec_repA B ly S rd (rec_record R fn A) O ->
(length A < 6)%nat ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (rec_slot R + CALL_OFF_NARGS <= a < rec_slot R + CALL_OFF_NARGS + 4) ->
  ~ (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
  rd' a = rd a) ->
(forall pn, In pn O -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn)) ->
In (p, n) (ablocks B ly' S') -> ~ In p (map fst O) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
p <> 0 -> Z.of_nat (length y) + 1 <= n <= LMAX + 2 -> Z.of_nat (length y) <= LMAX ->
aval_mem rd' (rec_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p y ->
rec_repA B ly' S' rd' (rec_record R fn (A ++ [y])) ((p, n) :: O).
Proof.
intros ly S ly' S' rd rd' R fn A O y p n (Q & HA & HO) Hm Hkeep Hblk Hpin Hpn Hpg Hps Hp0 Hn Hly Hna Harg Hstr.
assert (Hblk' : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn)).
{ intros pn Hpn0. apply Hblk. apply HO. exact Hpn0. }
assert (Hpn' : ~ In p (map fst (lay_blocks Q))).
{ intros Hin. apply Hpn. apply in_map_iff in Hin as (pn & Hpe & Hpn0).
  apply in_map_iff. exists pn. split; [exact Hpe | apply HO; exact Hpn0]. }
destruct (arep_bridge_add _ _ rd rd' R fn A Q y p n HA Hm Hkeep Hblk' Hpin Hpn' Hpg Hps Hp0 Hn Hly Hna Harg Hstr)
  as (Q' & HA' & HP).
exists Q'. split; [exact HA'|]. intros pn. split; intros Hin.
- eapply Permutation_in; [exact (Permutation_sym HP)|].
  destruct Hin as [<- | Hin]; [left; reflexivity | right; apply HO; exact Hin].
- assert (Hin2 : In pn ((p, n) :: lay_blocks Q)) by (eapply Permutation_in; [exact HP | exact Hin]).
  destruct Hin2 as [<- | Hin2]; [left; reflexivity | right; apply HO; exact Hin2].
Qed.
End d.
