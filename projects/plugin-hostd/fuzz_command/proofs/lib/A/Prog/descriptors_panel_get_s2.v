(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder-state transports copied from an earlier version of lib/A/Prog/answer_code.v (lines 222-336: aval_mem_kept .. rec_repA_kept); the model steps of record() and arg_s over arep_at for descriptors_panel_get's walk. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.
End d.

(* ---------- the model steps of record() and arg_s over arep_at ---------- *)

(* rd' agrees with rd on every byte arep_at reads (g_rec, record.spill and the recorder's blocks of Q), except the
   bytes Wr that the step wrote *)
Definition rec_rd_kept (Q : rlay) (rd rd' : reader) (Wr : Z -> Prop) : Prop :=
forall a, ((A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
           (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn)) -> ~ Wr a -> rd' a = rd a.

Ltac dpg_lia := cbv beta in *;
unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, CALL_SIZE, CALL_OFF_FN,
CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.

Lemma dpg_snoc : forall {T : Type} (l : list T), l <> [] -> exists l' a, l = l' ++ [a].
Proof.
intros T l H. destruct (rev l) as [|a r] eqn:E.
- exfalso. apply H. rewrite <- (rev_involutive l), E. reflexivity.
- exists (rev r), a. rewrite <- (rev_involutive l), E. reflexivity.
Qed.

(* the recorder's blocks lie outside g_rec and record.spill (ag1_own), so a write inside those two objects keeps them *)
Lemma dpg_rd_blk : forall bl (rd rd' : reader) R Q (Wr : Z -> Prop), arep_at bl rd A_G_REC A_REC_SPILL R Q ->
rec_rd_kept Q rd rd' Wr ->
(forall a, Wr a -> (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)) ->
forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).
Proof.
intros bl rd rd' R Q Wr HA Hk HW pn i Hpn Hi. unfold rec_rd_kept in Hk.
destruct HA as (_ & _ & _ & _ & _ & _ & _ & (_ & Hap)).
destruct (Hap pn Hpn) as [H1 H2].
apply Hk.
- right. right. exists pn. split; [exact Hpn | lia].
- intro Hw. destruct (HW _ Hw) as [Hw' | Hw']; unfold iv_apart in H1, H2; lia.
Qed.

(* answer, reply and the scalars, kept when g_rec's offsets 0..8 and 912..960 and the recorder's blocks are *)
Lemma dpg_tail_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q) /\
ag1_scalars rd' A_G_REC R.
Proof.
intros bl bl' rd rd' R Q HA HblQ Hg HbQ.
unfold lay_blocks in HblQ, HbQ.
destruct HA as (_ & _ & _ & _ & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & _).
unfold aanswer_at, areply_at, ag1_scalars in *.
unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

(* one recorded call of the table, kept when its 56 bytes and the recorder's blocks are *)
Lemma dpg_slot_kept : forall bl bl' (rd rd' : reader) R Q i c P,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall pn j, In pn (lay_blocks Q) -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
(forall j, 0 <= j < CALL_SIZE -> rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + j) =
  rd (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + j)) ->
acall_at bl' rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c).
Proof.
intros bl bl' rd rd' R Q i c P HA HblQ HbQ Hc Hp Hsl.
destruct HA as (_ & _ & _ & (_ & _ & _ & C4 & _ & _) & _).
destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact HC | | |].
- intros pn Hpn. apply HblQ. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
  split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- intros j Hj. apply Hsl. unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
- intros pn j Hpn Hj. apply HbQ; [|exact Hj]. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
  split; [exact (nth_error_In _ _ Hp) | exact Hpn].
Qed.

(* the spill call, kept when record.spill's 56 bytes and the recorder's blocks are *)
Lemma dpg_spill_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall pn j, In pn (lay_blocks Q) -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
(forall j, 0 <= j < SC_SIZE -> rd' (A_REC_SPILL + j) = rd (A_REC_SPILL + j)) ->
acall_at bl' rd' A_REC_SPILL (r_spill R) (l_spill Q) /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd (r_spill R)).
Proof.
intros bl bl' rd rd' R Q HA HblQ HbQ Hsl.
destruct HA as (_ & _ & _ & (_ & _ & _ & _ & C5 & C6) & _).
split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact C5 | | |].
- intros pn Hpn. apply HblQ. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
- intros j Hj. apply Hsl. unfold CALL_OFF_ARGS, SC_SIZE in *. lia.
- intros pn j Hpn Hj. apply HbQ; [|exact Hj]. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
Qed.

(* a call with no argument, and a call with one string argument, as acall_at reads them *)
Lemma dpg_call_nil : forall bl (rd : reader) a fn, 0 <= fn < REC_FN_COUNT ->
aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 0 -> acall_at bl rd a (fn, []) [].
Proof.
intros bl rd a fn Hfn Hf Hna. unfold acall_at. cbn [fst snd length map].
split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
split; [exact Hf|]. split; [exact Hna|]. split; [constructor|].
intros k s pn Hs _. destruct k; cbn [nth_error] in Hs; discriminate.
Qed.

Lemma dpg_call_one : forall bl (rd : reader) a fn p x, 0 <= fn < REC_FN_COUNT ->
aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 1 -> aval_mem rd (a + CALL_OFF_ARGS) 8 p ->
p <> 0 -> In (p, Z.of_nat (length x) + 1) bl -> Z.of_nat (length x) <= LMAX -> astr_atR rd p x ->
acall_at bl rd a (fn, [x]) [(p, Z.of_nat (length x) + 1)].
Proof.
intros bl rd a fn p x Hfn Hf Hna Hp Hp0 Hin HL Hs. unfold acall_at. cbn [fst snd length map].
split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
split; [exact Hf|]. split; [exact Hna|].
split; [apply (proj2 (stdpp.base.NoDup_ListNoDup _)); constructor; [intros [] | constructor]|].
intros k s pn Hk Hpn. destruct k as [|k]; [|destruct k; cbn [nth_error] in Hk; discriminate].
cbn [nth_error] in Hk, Hpn. injection Hk as <-. injection Hpn as <-. cbn [fst snd].
split; [replace (a + CALL_OFF_ARGS + 8 * Z.of_nat 0) with (a + CALL_OFF_ARGS) by lia; exact Hp|].
split; [exact Hp0|]. split; [exact Hin|]. split; [lia | exact Hs].
Qed.

(* the layout after record() into a free table slot has the same blocks *)
Lemma dpg_lay_nil : forall Q, lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q.
Proof.
intros Q. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
rewrite !app_nil_r. reflexivity.
Qed.

(* the layout after arg_s gains the argument's block *)
Lemma dpg_lay_arg_call : forall Q Ps pn, l_calls Q = Ps ++ [[]] ->
Permutation (lay_blocks (RLay (Ps ++ [[pn]]) (l_spill Q) (l_answer Q) (l_reply Q))) (pn :: lay_blocks Q).
Proof.
intros Q Ps pn HQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite HQ, !concat_app. cbn [concat].
rewrite !app_nil_r, <- app_assoc. cbn [app]. apply Permutation_sym, Permutation_middle.
Qed.

Lemma dpg_lay_arg_spill : forall Q pn, l_spill Q = [] ->
Permutation (lay_blocks (RLay (l_calls Q) [pn] (l_answer Q) (l_reply Q))) (pn :: lay_blocks Q).
Proof.
intros Q pn HS. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite HS. cbn [app].
apply Permutation_sym, Permutation_middle.
Qed.

Lemma dpg_own_add : forall gr sc Q Q' p L, Permutation (lay_blocks Q') ((p, L) :: lay_blocks Q) ->
ag1_own gr sc Q -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p L gr REC_SIZE -> iv_apart p L sc SC_SIZE -> ag1_own gr sc Q'.
Proof.
intros gr sc Q Q' p L Hperm (Hnd & Hap) Hni H1 H2. split.
- apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in Hnd.
  apply (Permutation_NoDup (Permutation_map fst (Permutation_sym Hperm))). cbn [map fst].
  constructor; [exact Hni | exact Hnd].
- intros pn Hpn. apply (Permutation_in pn Hperm) in Hpn.
  destruct Hpn as [<- | Hpn]; [exact (conj H1 H2) | exact (Hap pn Hpn)].
Qed.

Lemma arep_kept : forall bl bl' rd rd' R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
rec_rd_kept Q rd rd' (fun _ => False) -> arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA Hin Hk.
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ apply (dpg_rd_blk bl rd rd' R Q _ HA Hk). intros a []. }
unfold rec_rd_kept in Hk.
assert (Hg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [left; exact Ha | intros []]. }
assert (Hs : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [right; left; exact Ha | intros []]. }
assert (Ht : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a).
{ intros a Ha. apply Hg. dpg_lia. }
destruct (dpg_tail_kept bl bl' rd rd' R Q HA Hin Ht HbQ) as (Ta & Tr & Ts).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
unfold arep_at, ag1_calls.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact Ta|split; [exact Tr|split; [exact Ts|exact Hown]]]].
split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hg; dpg_lia]|].
split; [| apply (dpg_spill_kept bl bl' rd rd' R Q HA Hin HbQ); intros j Hj; apply Hs; lia].
intros i c P Hc Hp. apply (dpg_slot_kept bl bl' rd rd' R Q i c P HA Hin HbQ Hc Hp).
intros j Hj. apply Hg.
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)). dpg_lia.
Qed.

Lemma arep_answer_ptr : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd (A_G_REC + OFF_ANSWER) 8 (match l_answer Q with Some pn => fst pn | None => 0 end).
Proof.
intros bl rd R Q (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha.
destruct (r_answer R), (l_answer Q); try contradiction.
all: first [exact Ha | exact (proj1 Ha)].
Qed.

Lemma arep_spill_len : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
length (l_spill Q) = length (snd (r_spill R)) /\ (length (r_calls R) <= 16)%nat /\
aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))).
Proof.
intros bl rd R Q (_ & _ & _ & (C1 & _ & C3 & _ & C5 & _) & _).
destruct C5 as (_ & _ & HL & _).
split; [exact HL|]. split; [exact C1 | exact C3].
Qed.

Lemma arep_record_slot : forall bl rd rd' R Q fn,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> (length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_FN) 4 fn ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS) 4 0 ->
rec_rd_kept Q rd rd' (fun a => (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) \/
  (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) <= a <
   A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + 8)) ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, [])]))
  (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl rd rd' R Q fn HA Hn Hfn Hnc Hf Hna Hk.
pose proof (RecBLemmas.lay_blocks_in bl rd _ _ R Q HA) as Hin.
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ apply (dpg_rd_blk bl rd rd' R Q _ HA Hk). intros a Hw. left. dpg_lia. }
unfold rec_rd_kept in Hk.
assert (Hs : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [right; left; exact Ha | intro Hw; dpg_lia]. }
assert (Ht : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a).
{ intros a Ha. apply Hk; [left; dpg_lia | intro Hw; dpg_lia]. }
destruct (dpg_tail_kept bl bl rd rd' R Q HA Hin Ht HbQ) as (Ta & Tr & Ts).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
assert (Hown' : ag1_own A_G_REC A_REC_SPILL (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)))
by (unfold ag1_own; rewrite dpg_lay_nil; exact Hown).
unfold arep_at, ag1_calls.
cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact Ta|split; [exact Tr|split; [exact Ts|exact Hown']]]].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app; cbn [length]; lia|].
split.
{ replace (Z.of_nat (length (r_calls R ++ [(fn, [])]))) with (Z.of_nat (length (r_calls R)) + 1)
    by (rewrite length_app; cbn [length]; lia).
  exact Hnc. }
split; [| apply (dpg_spill_kept bl bl rd rd' R Q HA Hin HbQ); intros j Hj; apply Hs; lia].
intros i c P Hc Hp.
destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi | Hi].
- rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in Hp by lia.
  apply (dpg_slot_kept bl bl rd rd' R Q i c P HA Hin HbQ Hc Hp).
  intros j Hj. apply Hk; [left; dpg_lia | intro Hw; dpg_lia].
- assert (Hi' : i = length (r_calls R)).
  { pose proof (proj1 (nth_error_Some (r_calls R ++ [(fn, [])]) i) ltac:(rewrite Hc; discriminate)) as Hl.
    rewrite length_app in Hl. cbn [length] in Hl. lia. }
  subst i.
  rewrite nth_error_app2, Nat.sub_diag in Hc by lia. cbn [nth_error] in Hc. injection Hc as <-.
  rewrite nth_error_app2 in Hp by lia. rewrite C2, Nat.sub_diag in Hp. cbn [nth_error] in Hp. injection Hp as <-.
  split; [exact (dpg_call_nil bl rd' _ fn Hfn Hf Hna) | cbn [snd]; constructor].
Qed.

Lemma arep_record_spill : forall bl rd rd' R Q fn,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn -> aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
rec_rd_kept Q rd rd' (fun a => A_REC_SPILL <= a < A_REC_SPILL + 8) ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_spill R (fn, [])) Q.
Proof.
intros bl rd rd' R Q fn HA Hsp Hfn Hf Hna Hk.
pose proof (RecBLemmas.lay_blocks_in bl rd _ _ R Q HA) as Hin.
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ apply (dpg_rd_blk bl rd rd' R Q _ HA Hk). intros a Hw. right. dpg_lia. }
unfold rec_rd_kept in Hk.
assert (Hg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [left; exact Ha | intro Hw; dpg_lia]. }
assert (Ht : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a).
{ intros a Ha. apply Hg. dpg_lia. }
destruct (dpg_tail_kept bl bl rd rd' R Q HA Hin Ht HbQ) as (Ta & Tr & Ts).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
assert (Hl0 : l_spill Q = []).
{ destruct C5 as (_ & _ & HL & _). rewrite Hsp in HL. apply length_zero_iff_nil. exact HL. }
unfold arep_at, ag1_calls.
cbn [set_spill r_calls r_spill r_answer r_reply].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact Ta|split; [exact Tr|split; [exact Ts|exact Hown]]]].
split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hg; dpg_lia]|].
split.
- intros i c P Hc Hp. apply (dpg_slot_kept bl bl rd rd' R Q i c P HA Hin HbQ Hc Hp).
  intros j Hj. apply Hg.
  pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)). dpg_lia.
- rewrite Hl0. split; [exact (dpg_call_nil bl rd' _ fn Hfn Hf Hna) | cbn [snd]; constructor].
Qed.

Lemma arep_arg_slot : forall bl bl' rd rd' R Q cs fn p x,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> r_calls R = cs ++ [(fn, [])] ->
(forall pn, In pn bl -> In pn bl') -> In (p, Z.of_nat (length x) + 1) bl' ->
p <> 0 -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p (Z.of_nat (length x) + 1) A_G_REC REC_SIZE -> iv_apart p (Z.of_nat (length x) + 1) A_REC_SPILL SC_SIZE ->
Z.of_nat (length x) <= LMAX -> astr_atR rd' p x ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length cs) + CALL_OFF_NARGS) 4 1 ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length cs) + CALL_OFF_ARGS) 8 p ->
rec_rd_kept Q rd rd' (fun a => A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length cs) + CALL_OFF_NARGS <= a <
   A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length cs) + CALL_OFF_ARGS + 8) ->
exists Ps, l_calls Q = Ps ++ [[]] /\
arep_at bl' rd' A_G_REC A_REC_SPILL (set_calls R (cs ++ [(fn, [x])]))
  (RLay (Ps ++ [[(p, Z.of_nat (length x) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q cs fn p x HA Hcs Hbl Hpb Hp0 Hpn Hiv1 Hiv2 HLx Hstr Hna Har Hk.
pose proof (RecBLemmas.lay_blocks_in bl rd _ _ R Q HA) as Hin0.
assert (Hin : forall pn, In pn (lay_blocks Q) -> In pn bl') by (intros pn H; apply Hbl, Hin0, H).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
assert (Hn : (length cs < 16)%nat) by (pose proof C1 as E; rewrite Hcs, length_app in E; cbn [length] in E; lia).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ apply (dpg_rd_blk bl rd rd' R Q _ HA Hk). intros a Hw. left. dpg_lia. }
unfold rec_rd_kept in Hk.
assert (Hs : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [right; left; exact Ha | intro Hw; dpg_lia]. }
assert (Ht : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a).
{ intros a Ha. apply Hk; [left; dpg_lia | intro Hw; dpg_lia]. }
destruct (dpg_tail_kept bl bl' rd rd' R Q HA Hin Ht HbQ) as (Ta & Tr & Ts).
assert (Hne : l_calls Q <> []) by (intro E; rewrite E, Hcs, length_app in C2; cbn [length] in C2; lia).
destruct (dpg_snoc (l_calls Q) Hne) as (Ps & Pl & HQ).
assert (HPs : length Ps = length cs)
by (pose proof C2 as E; rewrite HQ, Hcs, !length_app in E; cbn [length] in E; lia).
assert (Hcn : nth_error (r_calls R) (length cs) = Some (fn, []))
by (rewrite Hcs, nth_error_app2, Nat.sub_diag by lia; reflexivity).
assert (Hpl : nth_error (l_calls Q) (length cs) = Some Pl)
by (rewrite HQ, nth_error_app2, HPs, Nat.sub_diag by lia; reflexivity).
destruct (C4 _ _ _ Hcn Hpl) as (HCn & _).
pose proof HCn as (Hfn & _ & HLp & Hf & _).
cbn [fst snd length] in Hfn, HLp, Hf.
apply length_zero_iff_nil in HLp. subst Pl.
exists Ps. split; [exact HQ|].
assert (Hown' : ag1_own A_G_REC A_REC_SPILL
  (RLay (Ps ++ [[(p, Z.of_nat (length x) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q))).
{ apply (dpg_own_add A_G_REC A_REC_SPILL Q _ p (Z.of_nat (length x) + 1));
    [apply dpg_lay_arg_call; exact HQ | exact Hown | exact Hpn | exact Hiv1 | exact Hiv2]. }
unfold arep_at, ag1_calls.
cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact Ta|split; [exact Tr|split; [exact Ts|exact Hown']]]].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app; cbn [length]; lia|].
split.
{ rewrite Hcs, length_app in C3. rewrite length_app. cbn [length] in C3 |- *.
  apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hk; [left; dpg_lia | intro Hw; dpg_lia]]. }
split; [| apply (dpg_spill_kept bl bl' rd rd' R Q HA Hin HbQ); intros j Hj; apply Hs; lia].
intros i c P Hc Hp.
destruct (Nat.lt_ge_cases i (length cs)) as [Hi | Hi].
- rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in Hp by lia.
  assert (Hc' : nth_error (r_calls R) i = Some c) by (rewrite Hcs, nth_error_app1 by exact Hi; exact Hc).
  assert (Hp' : nth_error (l_calls Q) i = Some P) by (rewrite HQ, nth_error_app1 by lia; exact Hp).
  apply (dpg_slot_kept bl bl' rd rd' R Q i c P HA Hin HbQ Hc' Hp').
  intros j Hj. apply Hk; [left; dpg_lia | intro Hw; dpg_lia].
- assert (Hc2 : nth_error (cs ++ [(fn, [x])]) i = Some c) by exact Hc.
  assert (Hi' : i = length cs).
  { pose proof (proj1 (nth_error_Some (cs ++ [(fn, [x])]) i) ltac:(rewrite Hc2; discriminate)) as Hl.
    rewrite length_app in Hl. cbn [length] in Hl. lia. }
  subst i.
  rewrite nth_error_app2, Nat.sub_diag in Hc2 by lia. cbn [nth_error] in Hc2. injection Hc2 as <-.
  rewrite nth_error_app2 in Hp by lia. rewrite HPs, Nat.sub_diag in Hp. cbn [nth_error] in Hp. injection Hp as <-.
  split; [| cbn [snd]; constructor; [exact HLx | constructor]].
  apply (dpg_call_one bl' rd' _ fn p x Hfn); [| exact Hna | exact Har | exact Hp0 | exact Hpb | exact HLx | exact Hstr].
  apply (aval_mem_kept rd); [exact Hf | intros k Hk'; apply Hk; [left; dpg_lia | intro Hw; dpg_lia]].
Qed.

Lemma arep_arg_spill : forall bl bl' rd rd' R Q fn p x,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> r_spill R = (fn, []) ->
(forall pn, In pn bl -> In pn bl') -> In (p, Z.of_nat (length x) + 1) bl' ->
p <> 0 -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p (Z.of_nat (length x) + 1) A_G_REC REC_SIZE -> iv_apart p (Z.of_nat (length x) + 1) A_REC_SPILL SC_SIZE ->
Z.of_nat (length x) <= LMAX -> astr_atR rd' p x ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS) 8 p ->
rec_rd_kept Q rd rd' (fun a => A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_ARGS + 8) ->
l_spill Q = [] /\
arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (fn, [x]))
  (RLay (l_calls Q) [(p, Z.of_nat (length x) + 1)] (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q fn p x HA Hsp Hbl Hpb Hp0 Hpn Hiv1 Hiv2 HLx Hstr Hna Har Hk.
pose proof (RecBLemmas.lay_blocks_in bl rd _ _ R Q HA) as Hin0.
assert (Hin : forall pn, In pn (lay_blocks Q) -> In pn bl') by (intros pn H; apply Hbl, Hin0, H).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ apply (dpg_rd_blk bl rd rd' R Q _ HA Hk). intros a Hw. right. dpg_lia. }
unfold rec_rd_kept in Hk.
assert (Hg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a).
{ intros a Ha. apply Hk; [left; exact Ha | intro Hw; dpg_lia]. }
assert (Ht : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a).
{ intros a Ha. apply Hg. dpg_lia. }
destruct (dpg_tail_kept bl bl' rd rd' R Q HA Hin Ht HbQ) as (Ta & Tr & Ts).
rewrite Hsp in C5.
pose proof C5 as (Hfn & _ & HLp & Hf & _).
cbn [fst snd length] in Hfn, HLp, Hf.
assert (Hl0 : l_spill Q = []) by (apply length_zero_iff_nil; exact HLp).
split; [exact Hl0|].
assert (Hown' : ag1_own A_G_REC A_REC_SPILL (RLay (l_calls Q) [(p, Z.of_nat (length x) + 1)] (l_answer Q) (l_reply Q))).
{ apply (dpg_own_add A_G_REC A_REC_SPILL Q _ p (Z.of_nat (length x) + 1));
    [apply dpg_lay_arg_spill; exact Hl0 | exact Hown | exact Hpn | exact Hiv1 | exact Hiv2]. }
unfold arep_at, ag1_calls.
cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact Ta|split; [exact Tr|split; [exact Ts|exact Hown']]]].
split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hg; dpg_lia]|].
split.
- intros i c P Hc Hp. apply (dpg_slot_kept bl bl' rd rd' R Q i c P HA Hin HbQ Hc Hp).
  intros j Hj. apply Hg.
  pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)). dpg_lia.
- split; [| cbn [snd]; constructor; [exact HLx | constructor]].
  apply (dpg_call_one bl' rd' _ fn p x Hfn); [| exact Hna | exact Har | exact Hp0 | exact Hpb | exact HLx | exact Hstr].
  apply (aval_mem_kept rd); [exact Hf | intros k Hk'; apply Hk; [right; left; dpg_lia | intro Hw; dpg_lia]].
Qed.
