(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder's state steps of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command):
   record() and the two argument appends over lib/A/Prog/CmdRep.v's arep_at, after fuzz_command's plain proof
   lib/Prog/RecStep.v (rec_rep_record_lt and its arg steps); rec_repA_in and rec_repA_kept are those of an earlier
   version of lib/A/Prog/answer_code.v (lines 222-333), copied word for word. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot record() fills for the state R (recorder.c:205-221): the next entry of g_rec's table, or record.spill
   when the table holds 16 calls (plain lib/Prog/RecStep.v:10-11 rec_entry) *)
Definition siv_slot (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
else A_REC_SPILL.

(* the recorder's block layout once the recorded call holds the argument blocks P: P is the new entry's list, or
   the spill's *)
Definition slot_lay (Q0 : rlay) (R : rstate) (P : list (Z * Z)) : rlay :=
if Nat.ltb (length (r_calls R)) 16 then RLay (l_calls Q0 ++ [P]) (l_spill Q0) (l_answer Q0) (l_reply Q0)
else RLay (l_calls Q0) P (l_answer Q0) (l_reply Q0).

Lemma rec_record_spill_clear : forall R x fn A, length (r_calls R) = 16%nat ->
rec_record (set_spill R (x, [])) fn A = rec_record R fn A.
Proof. intros R x fn A H. unfold rec_record. cbn [set_spill r_calls]. rewrite H. reflexivity. Qed.

Lemma siv_slot_spill_clear : forall R x, siv_slot (set_spill R x) = siv_slot R.
Proof. intros R x. reflexivity. Qed.

Lemma slot_lay_spill_clear : forall Q0 R x P, slot_lay Q0 (set_spill R x) P = slot_lay Q0 R P.
Proof. intros Q0 R x P. reflexivity. Qed.

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

Section d.
Variable B : asyms.

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
(* the arithmetic of g_rec / record.spill addresses: every offset and both base addresses as numbers *)
Ltac siv_lia := unfold REC_SIZE, SC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_OFF_FN, OFF_CALLS, CALL_SIZE, OFF_NCALLS,
  A_G_REC, A_REC_SPILL in *; lia.

(* the first components stay distinct when a block with a new start is added (plain RecStep.v:293-306) *)
Lemma siv_nodup_snoc : forall (l l' : list (Z * Z)) p k, Permutation l' (l ++ [(p, k)]) ->
NoDup (map fst l) -> ~ In p (map fst l) -> NoDup (map fst l').
Proof.
intros l l' p k HP H N. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
apply (Permutation_NoDup (Permutation_map fst (Permutation_sym HP))).
rewrite map_app. cbn [map fst].
apply (Permutation_NoDup (Permutation_cons_append (map fst l) p)).
apply NoDup_cons; [exact N | exact H].
Qed.

Lemma siv_perm_snoc_mid : forall (X Y W : list (Z * Z)) a, Permutation (X ++ (Y ++ [a]) ++ W) ((X ++ Y ++ W) ++ [a]).
Proof.
intros X Y W a. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
cbn [app]. apply Permutation_cons_append.
Qed.

(* the layout once the slot's list grows by one block (plain RecStep.v:360-375) *)
Lemma siv_lay_perm_lt : forall l0 P S ans rep pk,
Permutation (lay_blocks (RLay (l0 ++ [P ++ [pk]]) S ans rep)) (lay_blocks (RLay (l0 ++ [P]) S ans rep) ++ [pk]).
Proof.
intros l0 P S ans rep pk.
assert (E1 : lay_blocks (RLay (l0 ++ [P ++ [pk]]) S ans rep) = concat l0 ++ (P ++ [pk]) ++ S ++ oblk ans ++ oblk rep).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
assert (E2 : lay_blocks (RLay (l0 ++ [P]) S ans rep) = concat l0 ++ P ++ S ++ oblk ans ++ oblk rep).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. apply siv_perm_snoc_mid.
Qed.

Lemma siv_lay_perm_full : forall lc S ans rep pk,
Permutation (lay_blocks (RLay lc (S ++ [pk]) ans rep)) (lay_blocks (RLay lc S ans rep) ++ [pk]).
Proof. intros lc S ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply siv_perm_snoc_mid. Qed.

Lemma siv_lay_in : forall Q pn,
In pn (concat (l_calls Q)) \/ In pn (l_spill Q) \/ In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_app_iff. destruct H as [H | [H | H]].
- left. exact H.
- right. apply in_app_iff. left. exact H.
- right. apply in_app_iff. right. exact H.
Qed.

Lemma siv_lay_in_tbl : forall L0 P S qa qr pn,
In pn (concat L0) \/ In pn P \/ In pn S \/ In pn (oblk qa ++ oblk qr) -> In pn (lay_blocks (RLay (L0 ++ [P]) S qa qr)).
Proof.
intros L0 P S qa qr pn H. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
rewrite concat_app. cbn [concat]. rewrite app_nil_r.
apply in_app_iff. destruct H as [H | [H | [H | H]]].
- left. apply in_app_iff. left. exact H.
- left. apply in_app_iff. right. exact H.
- right. apply in_app_iff. left. exact H.
- right. apply in_app_iff. right. exact H.
Qed.

(* ag1_own of a layout that is the old one plus one new block *)
Lemma siv_own_snoc : forall gr sc Q Q' p k, ag1_own gr sc Q ->
Permutation (lay_blocks Q') (lay_blocks Q ++ [(p, k)]) ->
~ In p (map fst (lay_blocks Q)) -> iv_apart p k gr REC_SIZE -> iv_apart p k sc SC_SIZE ->
ag1_own gr sc Q'.
Proof.
intros gr sc Q Q' p k (Hnd & Hap) HP Hni H1 H2. split.
- exact (siv_nodup_snoc _ _ p k HP Hnd Hni).
- intros pn Hpn. apply (Permutation_in _ HP) in Hpn. apply in_app_iff in Hpn as [Hpn | [<- | []]].
  + exact (Hap pn Hpn).
  + cbn [fst snd]. split; assumption.
Qed.

(* the call record() writes: fn, nargs = 0, no argument *)
Lemma siv_acall_new0 : forall bl rd a fn, 0 <= fn < REC_FN_COUNT ->
aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 0 -> acall_at bl rd a (fn, []) [].
Proof.
intros bl rd a fn Hfn HF HN. unfold acall_at. cbn [fst snd length map].
split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
split; [exact HF|]. split; [exact HN|]. split; [constructor|].
intros k s pn Hs. destruct k; cbn in Hs; discriminate.
Qed.

(* one argument appended to a call: nargs and args[nargs] written, the new block holding the string
   (plain RecStep.v:442 call_at_arg) *)
Lemma siv_acall_arg : forall bl rd bl' rd' a fn A P p k s,
acall_at bl rd a (fn, A) P -> (length A < 6)%nat ->
(forall pn, In pn P -> In pn bl') -> In (p, k) bl' ->
(forall j, 0 <= j < CALL_OFF_ARGS + 8 * Z.of_nat (length A) -> ~ (CALL_OFF_NARGS <= j < CALL_OFF_NARGS + 4) ->
 rd' (a + j) = rd (a + j)) ->
(forall pn j, In pn P -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
aval_mem rd' (a + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (a + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p s -> p <> 0 -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> ~ In p (map fst P) ->
acall_at bl' rd' a (fn, A ++ [s]) (P ++ [(p, k)]).
Proof.
intros bl rd bl' rd' a fn A P p k s (H1 & H2 & H3 & H4 & H5 & H6 & H7) HA6 Hbl Hpk Ha Hb HN HP Hs Hp0 Hk Hni.
cbn [fst snd] in H1, H2, H3, H4, H5, H7.
unfold acall_at. cbn [fst snd].
split; [exact H1|].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, H3; reflexivity|].
split; [apply (aval_mem_kept rd); [exact H4 | intros j Hj; rewrite <- Z.add_assoc; apply Ha; unfold CALL_OFF_FN, CALL_OFF_ARGS, CALL_OFF_NARGS; lia]|].
split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact HN|].
split; [exact (siv_nodup_snoc P (P ++ [(p, k)]) p k (Permutation_refl _) H6 Hni)|].
intros k' s' pn Hs' Hpn'.
destruct (Nat.lt_ge_cases k' (length A)) as [Hk'|Hk'].
- rewrite nth_error_app1 in Hs' by exact Hk'. rewrite nth_error_app1 in Hpn' by (rewrite H3; exact Hk').
  destruct (H7 k' s' pn Hs' Hpn') as (G1 & G2 & G3 & G4 & G5).
  split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; unfold CALL_OFF_ARGS, CALL_OFF_NARGS; lia]|].
  split; [exact G2|]. split; [exact (Hbl pn (nth_error_In _ _ Hpn'))|]. split; [exact G4|].
  apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hb; [exact (nth_error_In _ _ Hpn') | lia]].
- destruct (Nat.eq_dec k' (length A)) as [->|Hne].
  + rewrite nth_error_app2 in Hs' by lia. rewrite Nat.sub_diag in Hs'. cbn in Hs'. injection Hs' as <-.
    rewrite nth_error_app2 in Hpn' by lia. rewrite H3, Nat.sub_diag in Hpn'. cbn in Hpn'. injection Hpn' as <-.
    cbn [fst snd]. split; [exact HP|]. split; [exact Hp0|]. split; [exact Hpk|]. split; [exact Hk | exact Hs].
  + exfalso. assert (N : nth_error (A ++ [s]) k' = None)
      by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    rewrite N in Hs'. discriminate.
Qed.

(* the entries of g_rec's table kept when none of their bytes and none of their blocks changed *)
Lemma siv_calls_kept : forall bl rd bl' rd' gr cs Lc,
(forall i c P, nth_error cs i = Some c -> nth_error Lc i = Some P ->
 acall_at bl rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
(forall pn, In pn (concat Lc) -> In pn bl') ->
(forall i j, (i < length cs)%nat -> 0 <= j < CALL_SIZE ->
 rd' (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + j) = rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + j)) ->
(forall pn j, In pn (concat Lc) -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
forall i c P, nth_error cs i = Some c -> nth_error Lc i = Some P ->
 acall_at bl' rd' (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c).
Proof.
intros bl rd bl' rd' gr cs Lc H Hbl Hg Hb i c P Hc HP. destruct (H i c P Hc HP) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some cs i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact HC | | |].
- intros pn Hpn. apply Hbl. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
- intros j Hj. apply Hg; [exact Hi|]. clear - Hj HL6. unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
- intros pn j Hpn Hj. apply Hb; [|exact Hj]. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
Qed.

(* the table split as its first entries and its last one *)
Lemma siv_nth_snoc_split : forall (X : nat -> rcall -> list (Z * Z) -> Prop) cs Lc c' P',
length Lc = length cs ->
(forall i c P, nth_error (cs ++ [c']) i = Some c -> nth_error (Lc ++ [P']) i = Some P -> X i c P) ->
(forall i c P, nth_error cs i = Some c -> nth_error Lc i = Some P -> X i c P) /\ X (length cs) c' P'.
Proof.
intros X cs Lc c' P' HL H. split.
- intros i c P Hc HP. pose proof (proj1 (nth_error_Some cs i) ltac:(rewrite Hc; discriminate)) as Hi.
  apply H.
  + rewrite nth_error_app1 by exact Hi. exact Hc.
  + rewrite nth_error_app1 by (rewrite HL; exact Hi). exact HP.
- apply H.
  + rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  + rewrite nth_error_app2 by lia. rewrite HL, Nat.sub_diag. reflexivity.
Qed.

(* and joined back *)
Lemma siv_calls_snoc : forall bl rd gr cs Lc c' P',
length Lc = length cs ->
(forall i c P, nth_error cs i = Some c -> nth_error Lc i = Some P ->
 acall_at bl rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
acall_at bl rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length cs)) c' P' ->
Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c') ->
forall i c P, nth_error (cs ++ [c']) i = Some c -> nth_error (Lc ++ [P']) i = Some P ->
 acall_at bl rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c).
Proof.
intros bl rd gr cs Lc c' P' HL Hold Hnew HF i c P Hc HP.
destruct (Nat.lt_ge_cases i (length cs)) as [Hi|Hi].
- rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP by (rewrite HL; exact Hi).
  exact (Hold i c P Hc HP).
- destruct (Nat.eq_dec i (length cs)) as [->|Hne].
  + rewrite nth_error_app2 in Hc by lia. rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-.
    rewrite nth_error_app2 in HP by lia. rewrite HL, Nat.sub_diag in HP. cbn in HP. injection HP as <-.
    split; [exact Hnew | exact HF].
  + exfalso. assert (N : nth_error (cs ++ [c']) i = None)
      by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    rewrite N in Hc. discriminate.
Qed.

(* the answer, the reply and the scalars kept when g_rec's bytes 0..8 and 912..960 and their blocks are *)
Lemma siv_rest_kept : forall bl rd bl' rd' gr R t qa y qr,
aanswer_at bl rd gr t qa -> areply_at bl rd gr y qr -> ag1_scalars rd gr R ->
(forall pn, In pn (oblk qa ++ oblk qr) -> In pn bl') ->
(forall pn j, In pn (oblk qa ++ oblk qr) -> 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
(forall a, gr <= a < gr + 8 \/ gr + 912 <= a < gr + 960 -> rd' a = rd a) ->
aanswer_at bl' rd' gr t qa /\ areply_at bl' rd' gr y qr /\ ag1_scalars rd' gr R.
Proof.
intros bl rd bl' rd' gr R t qa y qr Ha Hr HS Hbl Hb Hg.
unfold aanswer_at, areply_at, ag1_scalars in *.
unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
split.
{ destruct t as [x|], qa as [q|]; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    assert (Hq : In q (oblk (Some q) ++ oblk qr)) by (apply in_app_iff; left; left; reflexivity).
    split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
    split; [exact A2|]. split; [apply Hbl; exact Hq|]. split; [exact A4|].
    split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply Hb; [exact Hq | cbn [snd]; lia]] | exact A6].
  - apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct y as [x|], qr as [q|]; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    assert (Hq : In q (oblk qa ++ oblk (Some q))) by (apply in_app_iff; right; left; reflexivity).
    split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
    split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply Hbl; exact Hq|]. split; [exact A6|].
    split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply Hb; [exact Hq | lia]] | exact A8].
  - destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6).
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

(* record(fn) (recorder.c:205-221) on the recorder's representation: the slot's fn and nargs written, and, in g_rec's
   table, ncalls one more; every other byte of g_rec / record.spill and of the recorder's blocks as before. When the
   table is full the spill must already be cleared (rec_calls_free(&spill, 1) runs first). *)
Lemma siv_record_step : forall bl0 rd0 R Q0 bl rd fn,
arep_at bl0 rd0 A_G_REC A_REC_SPILL R Q0 ->
((16 <= length (r_calls R))%nat -> snd (r_spill R) = []) ->
0 <= fn < REC_FN_COUNT ->
(forall pn, In pn (lay_blocks Q0) -> In pn bl) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (siv_slot R <= a < siv_slot R + 8) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd a = rd0 a) ->
(forall pn i, In pn (lay_blocks Q0) -> 0 <= i < snd pn -> rd (fst pn + i) = rd0 (fst pn + i)) ->
aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record R fn [])))) ->
aval_mem rd (siv_slot R + CALL_OFF_FN) 4 fn -> aval_mem rd (siv_slot R + CALL_OFF_NARGS) 4 0 ->
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn []) (slot_lay Q0 R []).
Proof.
intros bl0 rd0 R Q0 bl rd fn HR Hsp Hfn Hbl Hg Hb HN HF HA.
destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & (Hnd & Hap)).
assert (Hbl1 : forall pn, In pn (concat (l_calls Q0)) -> In pn bl)
  by (intros pn Hpn; apply Hbl, siv_lay_in; left; exact Hpn).
assert (Hb1 : forall pn j, In pn (concat (l_calls Q0)) -> 0 <= j < snd pn -> rd (fst pn + j) = rd0 (fst pn + j))
  by (intros pn j Hpn Hj; apply Hb; [apply siv_lay_in; left; exact Hpn | exact Hj]).
assert (Hbl2 : forall pn, In pn (l_spill Q0) -> In pn bl)
  by (intros pn Hpn; apply Hbl, siv_lay_in; right; left; exact Hpn).
assert (Hb2 : forall pn j, In pn (l_spill Q0) -> 0 <= j < snd pn -> rd (fst pn + j) = rd0 (fst pn + j))
  by (intros pn j Hpn Hj; apply Hb; [apply siv_lay_in; right; left; exact Hpn | exact Hj]).
assert (Hbl3 : forall pn, In pn (oblk (l_answer Q0) ++ oblk (l_reply Q0)) -> In pn bl)
  by (intros pn Hpn; apply Hbl, siv_lay_in; right; right; exact Hpn).
assert (Hb3 : forall pn j, In pn (oblk (l_answer Q0) ++ oblk (l_reply Q0)) -> 0 <= j < snd pn ->
  rd (fst pn + j) = rd0 (fst pn + j))
  by (intros pn j Hpn Hj; apply Hb; [apply siv_lay_in; right; right; exact Hpn | exact Hj]).
clear Hbl Hb.
unfold siv_slot, slot_lay, rec_record in *.
destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
- (* the table's next entry *)
  apply Nat.ltb_lt in E.
  cbn [set_calls r_calls] in HN.
  assert (Hg3 : forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd a = rd0 a)
    by (intros a Hx; apply Hg; clear - Hx E; siv_lia).
  pose proof (siv_rest_kept bl0 rd0 bl rd A_G_REC R _ _ _ _ Ha Hr HS Hbl3 Hb3 Hg3) as (Ha' & Hr' & HS').
  assert (LB : lay_blocks (RLay (l_calls Q0 ++ [[]]) (l_spill Q0) (l_answer Q0) (l_reply Q0)) = lay_blocks Q0).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite !app_nil_r.
    reflexivity. }
  unfold arep_at, ag1_calls, ag1_own.
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  rewrite LB.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app, C2; reflexivity|].
    split; [exact HN|].
    split.
    - refine (siv_calls_snoc bl rd A_G_REC (r_calls R) (l_calls Q0) (fn, []) [] C2 _ _ _).
      + refine (siv_calls_kept bl0 rd0 bl rd A_G_REC (r_calls R) (l_calls Q0) C4 Hbl1 _ Hb1).
        intros i j Hi Hj. apply Hg; clear - Hi Hj E; siv_lia.
      + apply siv_acall_new0; [exact Hfn | exact HF | exact HA].
      + cbn [snd]. constructor.
    - split; [|exact C6].
      pose proof C5 as (_ & HL6 & _).
      apply (acall_at_kept bl0 _ rd0); [exact C5 | exact Hbl2 | | exact Hb2].
      intros j Hj. apply Hg; clear - Hj HL6 E; siv_lia. }
  split; [exact Ha'|]. split; [exact Hr'|]. split; [exact HS'|].
  split; [exact Hnd | exact Hap].
- (* the spill, cleared before *)
  apply Nat.ltb_ge in E.
  assert (E16 : length (r_calls R) = 16%nat) by lia.
  cbn [set_spill r_calls] in HN.
  assert (HS0 : l_spill Q0 = []).
  { pose proof C5 as (_ & _ & HL & _). rewrite (Hsp E) in HL. apply length_zero_iff_nil. exact HL. }
  assert (Hg3 : forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd a = rd0 a)
    by (intros a Hx; apply Hg; clear - Hx; siv_lia).
  pose proof (siv_rest_kept bl0 rd0 bl rd A_G_REC R _ _ _ _ Ha Hr HS Hbl3 Hb3 Hg3) as (Ha' & Hr' & HS').
  assert (LB : lay_blocks (RLay (l_calls Q0) [] (l_answer Q0) (l_reply Q0)) = lay_blocks Q0).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite HS0. reflexivity. }
  unfold arep_at, ag1_calls, ag1_own.
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  rewrite LB.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { split; [exact C1|]. split; [exact C2|]. split; [exact HN|].
    split.
    - refine (siv_calls_kept bl0 rd0 bl rd A_G_REC (r_calls R) (l_calls Q0) C4 Hbl1 _ Hb1).
      intros i j Hi Hj. apply Hg; clear - Hi Hj E16; siv_lia.
    - split; [apply siv_acall_new0; [exact Hfn | exact HF | exact HA] | cbn [snd]; constructor]. }
  split; [exact Ha'|]. split; [exact Hr'|]. split; [exact HS'|].
  split; [exact Hnd | exact Hap].
Qed.

(* the append of one argument string to the call record() just made (recorder.c:223-241, arg_s / arg_i / arg_line
   all end the same way): nargs one more, args[nargs] the new block's address, the block holding the string *)
Lemma siv_arg_step : forall bl rd R fn A Q0 P bl' rd' p k s,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) (slot_lay Q0 R P) ->
(length A < 6)%nat ->
(forall pn, In pn (lay_blocks (slot_lay Q0 R P)) -> In pn bl') -> In (p, k) bl' ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (siv_slot R + CALL_OFF_NARGS <= a < siv_slot R + CALL_OFF_NARGS + 4) ->
   ~ (siv_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < siv_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
   rd' a = rd a) ->
(forall pn i, In pn (lay_blocks (slot_lay Q0 R P)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (siv_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (siv_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p s -> p <> 0 -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> Z.of_nat (length s) <= LMAX ->
~ In p (map fst (lay_blocks (slot_lay Q0 R P))) ->
iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn (A ++ [s])) (slot_lay Q0 R (P ++ [(p, k)])).
Proof.
intros bl rd R fn A Q0 P bl' rd' p k s HR HA6 Hbl Hpk Hg Hb HN HP Hs Hp0 Hk Hsl Hni Hap1 Hap2.
unfold siv_slot, slot_lay, rec_record in *.
destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
- (* the table's last entry *)
  apply Nat.ltb_lt in E.
  destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply] in C1, C2, C3, C4, C5, C6, Ha, Hr.
  assert (HL0 : length (l_calls Q0) = length (r_calls R))
    by (rewrite !length_app in C2; cbn [length] in C2; lia).
  destruct (siv_nth_snoc_split (fun i c P' => acall_at bl rd (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P' /\
    Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) (r_calls R) (l_calls Q0) (fn, A) P HL0 C4) as [Hold Hlast].
  cbv beta in Hold, Hlast. destruct Hlast as [Hlast HlastF].
  assert (Hbl3 : forall pn, In pn (oblk (l_answer Q0) ++ oblk (l_reply Q0)) -> In pn bl')
    by (intros pn Hpn; apply Hbl, siv_lay_in_tbl; right; right; right; exact Hpn).
  assert (Hb3 : forall pn j, In pn (oblk (l_answer Q0) ++ oblk (l_reply Q0)) -> 0 <= j < snd pn ->
    rd' (fst pn + j) = rd (fst pn + j))
    by (intros pn j Hpn Hj; apply Hb; [apply siv_lay_in_tbl; right; right; right; exact Hpn | exact Hj]).
  assert (Hg3 : forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd' a = rd a)
    by (intros a Hx; apply Hg; clear - Hx E HA6; siv_lia).
  pose proof (siv_rest_kept bl rd bl' rd' A_G_REC _ _ _ _ _ Ha Hr HS Hbl3 Hb3 Hg3) as (Ha' & Hr' & HS').
  unfold arep_at, ag1_calls.
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app, HL0; reflexivity|].
    split; [rewrite length_app in C3 |- *; cbn [length] in C3 |- *;
      apply (aval_mem_kept rd); [exact C3 | intros j Hj; apply Hg; clear - Hj E HA6; siv_lia]|].
    split.
    - refine (siv_calls_snoc bl' rd' A_G_REC (r_calls R) (l_calls Q0) (fn, A ++ [s]) (P ++ [(p, k)]) HL0 _ _ _).
      + refine (siv_calls_kept bl rd bl' rd' A_G_REC (r_calls R) (l_calls Q0) Hold _ _ _).
        * intros pn Hpn. apply Hbl, siv_lay_in_tbl. left. exact Hpn.
        * intros i j Hi Hj. apply Hg; clear - Hi Hj E HA6; siv_lia.
        * intros pn j Hpn Hj. apply Hb; [apply siv_lay_in_tbl; left; exact Hpn | exact Hj].
      + refine (siv_acall_arg bl rd bl' rd' _ fn A P p k s Hlast HA6 _ Hpk _ _ HN HP Hs Hp0 Hk _).
        * intros pn Hpn. apply Hbl, siv_lay_in_tbl. right; left. exact Hpn.
        * intros j Hj Hj'. apply Hg; clear - Hj Hj' E HA6; siv_lia.
        * intros pn j Hpn Hj. apply Hb; [apply siv_lay_in_tbl; right; left; exact Hpn | exact Hj].
        * intros Hin. apply Hni. apply in_map_iff in Hin as (pn & Ep & Hpn). apply in_map_iff. exists pn.
          split; [exact Ep|]. apply siv_lay_in_tbl. right; left. exact Hpn.
      + cbn [snd] in HlastF |- *. apply Forall_app. split; [exact HlastF | constructor; [exact Hsl | constructor]].
    - split; [|exact C6].
      pose proof C5 as (_ & HL6 & _).
      refine (acall_at_kept bl bl' rd rd' _ _ _ C5 _ _ _).
      + intros pn Hpn. apply Hbl, siv_lay_in_tbl. right; right; left. exact Hpn.
      + intros j Hj. apply Hg; clear - Hj HL6 E HA6; siv_lia.
      + intros pn j Hpn Hj. apply Hb; [apply siv_lay_in_tbl; right; right; left; exact Hpn | exact Hj]. }
  split; [exact Ha'|]. split; [exact Hr'|]. split; [exact HS'|].
  exact (siv_own_snoc _ _ _ _ p k Hown (siv_lay_perm_lt _ _ _ _ _ _) Hni Hap1 Hap2).
- (* the spill *)
  apply Nat.ltb_ge in E.
  destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply] in C1, C2, C3, C4, C5, C6, Ha, Hr.
  assert (E16 : length (r_calls R) = 16%nat) by lia.
  assert (Hbl3 : forall pn, In pn (oblk (l_answer Q0) ++ oblk (l_reply Q0)) -> In pn bl')
    by (intros pn Hpn; apply Hbl, siv_lay_in; right; right; exact Hpn).
  assert (Hb3 : forall pn j, In pn (oblk (l_answer Q0) ++ oblk (l_reply Q0)) -> 0 <= j < snd pn ->
    rd' (fst pn + j) = rd (fst pn + j))
    by (intros pn j Hpn Hj; apply Hb; [apply siv_lay_in; right; right; exact Hpn | exact Hj]).
  assert (HgR : forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a)
    by (intros a Hx; apply Hg; clear - Hx HA6; siv_lia).
  assert (Hg3 : forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd' a = rd a)
    by (intros a Hx; apply HgR; clear - Hx; lia).
  pose proof (siv_rest_kept bl rd bl' rd' A_G_REC _ _ _ _ _ Ha Hr HS Hbl3 Hb3 Hg3) as (Ha' & Hr' & HS').
  unfold arep_at, ag1_calls.
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { split; [exact C1|]. split; [exact C2|].
    split; [apply (aval_mem_kept rd); [exact C3 | intros j Hj; apply HgR; clear - Hj; unfold OFF_NCALLS; lia]|].
    split.
    - refine (siv_calls_kept bl rd bl' rd' A_G_REC (r_calls R) (l_calls Q0) C4 _ _ _).
      + intros pn Hpn. apply Hbl, siv_lay_in. left. exact Hpn.
      + intros i j Hi Hj. apply HgR. clear - Hi Hj E16. unfold OFF_CALLS, CALL_SIZE in *. lia.
      + intros pn j Hpn Hj. apply Hb; [apply siv_lay_in; left; exact Hpn | exact Hj].
    - split.
      + refine (siv_acall_arg bl rd bl' rd' A_REC_SPILL fn A P p k s C5 HA6 _ Hpk _ _ HN HP Hs Hp0 Hk _).
        * intros pn Hpn. apply Hbl, siv_lay_in. right; left. exact Hpn.
        * intros j Hj Hj'. apply Hg; clear - Hj Hj' HA6; siv_lia.
        * intros pn j Hpn Hj. apply Hb; [apply siv_lay_in; right; left; exact Hpn | exact Hj].
        * intros Hin. apply Hni. apply in_map_iff in Hin as (pn & Ep & Hpn). apply in_map_iff. exists pn.
          split; [exact Ep|]. apply siv_lay_in. right; left. exact Hpn.
      + cbn [snd] in C6 |- *. apply Forall_app. split; [exact C6 | constructor; [exact Hsl | constructor]]. }
  split; [exact Ha'|]. split; [exact Hr'|]. split; [exact HS'|].
  exact (siv_own_snoc _ _ _ _ p k Hown (siv_lay_perm_full _ _ _ _ _) Hni Hap1 Hap2).
Qed.
