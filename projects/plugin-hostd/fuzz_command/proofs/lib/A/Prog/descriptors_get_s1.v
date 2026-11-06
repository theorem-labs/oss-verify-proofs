(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder model steps of descriptors_get's ASan walk (plugin-hostd/fuzz_command),
   after fuzz_command's plain lib/Prog/RecStep.v (rec_rep_record_lt, rep_at_record_full, rec_rep_arg) over the reader
   form of lib/A/Prog/CmdRep.v; aval_mem_kept, rabytes_kept, rastr_kept and acall_at_kept as in the answer_code walk
   (lib/A/Prog/answer_code.v). *)

(* What the inlined record(FN) and arg_s(c, s) of a recorder entry leave in g_rec / record.spill (recorder.c:205-227):
   the call (FN, [s]) at the slot the entry picked, its one argument a fresh block holding s. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

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
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk;
  change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk;
  change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

(* the call (fn, [s]) at a: its function, one argument, the argument's pointer, and the argument's block *)
Lemma acall_one : forall bl (rd : reader) a fn s p k,
0 <= fn < REC_FN_COUNT ->
aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 1 -> aval_mem rd (a + CALL_OFF_ARGS) 8 p ->
p <> 0 -> In (p, k) bl -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> astr_atR rd p s ->
acall_at bl rd a (fn, [s]) [(p, k)].
Proof.
intros bl rd a fn s p k Hfn HF HN HA Hp Hin Hk Hs. unfold acall_at. cbn [fst snd length].
refine (conj Hfn (conj _ (conj eq_refl (conj HF (conj HN (conj _ _)))))).
- cbn. lia.
- cbn [map fst]. apply NoDup_ListNoDup. apply List.NoDup_cons; [cbn; tauto | apply List.NoDup_nil].
- intros j s' pn Hs' Hpn. destruct j as [|j]; [|destruct j; discriminate Hs'].
  cbn in Hs', Hpn. injection Hs' as <-. injection Hpn as <-. cbn [fst snd].
  rewrite Z.mul_0_r, Z.add_0_r. auto.
Qed.

(* the owner list of the recorder after the new call: the old one with the argument's block at the end *)
Lemma nodup_snoc_fst : forall (l : list (Z * Z)) p k, NoDup (map fst l) -> ~ In p (map fst l) ->
NoDup (map fst (l ++ [(p, k)])).
Proof.
intros l p k H N. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. rewrite map_app. cbn [map fst].
apply (Permutation_NoDup (Permutation_cons_append (map fst l) p)). constructor; assumption.
Qed.

Lemma lay_slot_perm : forall l0 S ans rep pk,
Permutation (lay_blocks (RLay (l0 ++ [[pk]]) S ans rep)) (lay_blocks (RLay l0 S ans rep) ++ [pk]).
Proof.
intros l0 S ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
rewrite concat_app. cbn [concat]. rewrite app_nil_r. rewrite <- !app_assoc.
apply Permutation_app_head. cbn [app]. rewrite !app_assoc. apply Permutation_cons_append.
Qed.

Lemma lay_spill_perm : forall l0 ans rep pk,
Permutation (lay_blocks (RLay l0 [pk] ans rep)) (lay_blocks (RLay l0 [] ans rep) ++ [pk]).
Proof.
intros l0 ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply app].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. rewrite !app_assoc. apply Permutation_cons_append.
Qed.

Lemma nodup_fst_perm : forall l l' : list (Z * Z), Permutation l l' -> NoDup (map fst l) -> NoDup (map fst l').
Proof.
intros l l' HP H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
exact (Permutation_NoDup (Permutation_map fst HP) H).
Qed.

(* the recorder's state after record(fn) and arg_s(c, s) (recorder.c:205-227): the model's rec_record R fn [s],
   from the state R before the call, the slot c the call used and the bytes the call wrote *)
Lemma arep_record_arg : forall bl bl' (rd rd' : reader) R Q fn s p k c,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
0 <= fn < REC_FN_COUNT ->
((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) \/
(length (r_calls R) = 16%nat /\ c = A_REC_SPILL /\ l_spill Q = []) ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record R fn [s])))) ->
aval_mem rd' (c + CALL_OFF_FN) 4 fn -> aval_mem rd' (c + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (c + CALL_OFF_ARGS) 8 p ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 16) -> rd' a = rd a) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
p <> 0 -> In (p, k) bl' -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> astr_atR rd' p s -> Z.of_nat (length s) <= LMAX ->
~ In p (map fst (lay_blocks Q)) -> iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn [s]) Q' /\
  Permutation (lay_blocks Q') (lay_blocks Q ++ [(p, k)]).
Proof.
intros bl bl' rd rd' R Q fn s p k c HA Hfn Hc HN HF HNa HAr Hk Hbl Hb Hp0 Hpk Hkn Hs Hsl Hpn Hag Has.
pose proof (acall_one bl' rd' c fn s p k Hfn HF HNa HAr Hp0 Hpk Hkn Hs) as Hnew.
assert (HF1 : Forall (fun s0 => Z.of_nat (length s0) <= LMAX) (snd (fn, [s]))) by (cbn; constructor; [exact Hsl | constructor]).
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & (O1 & O2)).
assert (HgQ : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  ~ (c <= a < c + 16) -> rd' a = rd a) by (intros a Ha1 Ha2 Ha3; apply Hk; [left; exact Ha1 | exact Ha2 | exact Ha3]).
assert (HbQ : forall pn, In pn (lay_blocks Q) -> forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn Hin i Hi; exact (Hb pn i Hin Hi)).
unfold lay_blocks in Hbl, HbQ, Hpn, O1, O2.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE,
  OFF_HOST, CALL_SIZE, REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL in *.
assert (Hcr : (0x5e3740 + 16 <= c /\ c + 56 <= 0x5e3740 + 912) \/ c = 0x5e3be0)
  by (destruct Hc as [(Hlt0 & ->) | (_ & -> & _)]; [left; lia | right; reflexivity]).
(* the parts of the recorder the call does not touch *)
assert (KA : aanswer_at bl' rd' 0x5e3740 (r_answer R) (l_answer Q)).
{ unfold aanswer_at in *. unfold OFF_ANSWER in *. destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
      by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
    split; [apply (aval_mem_kept rd); [exact A1 | intros j Hj; apply HgQ; destruct Hcr as [Hcr | ->]; lia]|].
    split; [exact A2|]. split; [apply Hbl; exact Hq|]. split; [exact A4|].
    split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply (HbQ q Hq); lia] | exact A6].
  - apply (aval_mem_kept rd); [exact Ha | intros j Hj; apply HgQ; destruct Hcr as [Hcr | ->]; lia]. }
assert (KR : areply_at bl' rd' 0x5e3740 (r_reply R) (l_reply Q)).
{ unfold areply_at in *. unfold OFF_REPLY, OFF_REPLY_SIZE in *. destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
      by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
    split; [apply (aval_mem_kept rd); [exact A1 | intros j Hj; apply HgQ; destruct Hcr as [Hcr | ->]; lia]|].
    split; [apply (aval_mem_kept rd); [exact A2 | intros j Hj; apply HgQ; destruct Hcr as [Hcr | ->]; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply Hbl; exact Hq|]. split; [exact A6|].
    split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply (HbQ q Hq); lia] | exact A8].
  - destruct Hr as [A1 A2].
    split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros j Hj; apply HgQ; destruct Hcr as [Hcr | ->]; lia]. }
assert (KS : ag1_scalars rd' 0x5e3740 R).
{ unfold ag1_scalars in *. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ S6))))); apply (aval_mem_kept rd);
  first [exact S1 | exact S2 | exact S3 | exact S4 | exact S5 | intros j Hj; apply HgQ; destruct Hcr as [Hcr | ->]; lia]. }
(* an old call of g_rec's table, below the new slot (or anywhere in the table on the spill arm) *)
assert (KC : forall i c0 P, nth_error (r_calls R) i = Some c0 -> nth_error (l_calls Q) i = Some P ->
  acall_at bl' rd' (0x5e3740 + 16 + 56 * Z.of_nat i) c0 P).
{ intros i c0 P Hc0 HP. destruct (C4 i c0 P Hc0 HP) as [HC _].
  pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc0; discriminate)) as Hi.
  pose proof HC as (_ & HL6 & _).
  apply (acall_at_kept bl _ rd); [exact HC | | |].
  - intros pn Hin. apply Hbl. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hin].
  - intros j Hj. unfold CALL_OFF_ARGS in Hj. rewrite <- Z.add_assoc. apply HgQ.
    + split; [lia|]. assert (Hi16 : (i < 16)%nat) by lia. lia.
    + lia.
    + destruct Hc as [(Hlt & ->) | (_ & -> & _)]; [|lia]. lia.
  - intros pn j Hin Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat.
    exists P. split; [exact (nth_error_In _ _ HP) | exact Hin]. }
destruct Hc as [(Hlt & Hce) | (H16 & Hce & Hsp)].
- (* g_rec's table had room: the call is the next entry of the table *)
  exists (RLay (l_calls Q ++ [[(p, k)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  rewrite (rec_record_calls R fn [s] Hlt) in HN |- *.
  split; [| apply lay_slot_perm].
  unfold arep_at, ag1_calls, ag1_own. cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app, C2; reflexivity|].
    split; [exact HN|].
    split.
    - intros i c0 P Hc0 HP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      + rewrite nth_error_app1 in Hc0 by exact Hi. rewrite nth_error_app1 in HP by (rewrite C2; exact Hi).
        split; [exact (KC i c0 P Hc0 HP) | exact (proj2 (C4 i c0 P Hc0 HP))].
      + destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        * rewrite nth_error_app2 in Hc0 by lia. rewrite Nat.sub_diag in Hc0. cbn in Hc0. injection Hc0 as <-.
          rewrite nth_error_app2 in HP by lia. rewrite C2, Nat.sub_diag in HP. cbn in HP. injection HP as <-.
          split; [|exact HF1]. subst c. exact Hnew.
        * exfalso. assert (N : nth_error (r_calls R ++ [(fn, [s])]) i = None)
            by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
          rewrite N in Hc0. discriminate.
    - split; [|exact C6].
      pose proof C5 as (_ & HL6 & _).
      apply (acall_at_kept bl _ rd); [exact C5 | | |].
      + intros pn Hin. apply Hbl. apply in_app_iff. right. apply in_app_iff. left. exact Hin.
      + intros j Hj. unfold CALL_OFF_ARGS in Hj. apply Hk; [right; lia | lia | subst c; lia].
      + intros pn j Hin Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
  split; [exact KA|]. split; [exact KR|]. split; [exact KS|].
  pose proof (lay_slot_perm (l_calls Q) (l_spill Q) (l_answer Q) (l_reply Q) (p, k)) as HPm.
  unfold lay_blocks in HPm. cbn [l_calls l_spill l_answer l_reply] in HPm.
  split.
  + apply (nodup_fst_perm _ _ (Permutation_sym HPm)). apply nodup_snoc_fst; [exact O1 | exact Hpn].
  + intros pn Hin. apply (Permutation_in _ HPm) in Hin. apply in_app_iff in Hin as [Hin | [<- | []]].
    * exact (O2 pn Hin).
    * cbn [fst snd]. unfold REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL in Hag, Has. split; [exact Hag | exact Has].
- (* the table was full: the call goes to record.spill *)
  exists (RLay (l_calls Q) [(p, k)] (l_answer Q) (l_reply Q)).
  rewrite (rec_record_spill R fn [s] H16) in HN |- *.
  split.
  2: { pose proof (lay_spill_perm (l_calls Q) (l_answer Q) (l_reply Q) (p, k)) as HPm.
       unfold lay_blocks in HPm |- *. rewrite Hsp. exact HPm. }
  unfold arep_at, ag1_calls, ag1_own. cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { split; [exact C1|]. split; [exact C2|]. split; [exact HN|].
    split.
    - intros i c0 P Hc0 HP. split; [exact (KC i c0 P Hc0 HP) | exact (proj2 (C4 i c0 P Hc0 HP))].
    - split; [subst c; exact Hnew | exact HF1]. }
  split; [exact KA|]. split; [exact KR|]. split; [exact KS|].
  pose proof (lay_spill_perm (l_calls Q) (l_answer Q) (l_reply Q) (p, k)) as HPm.
  unfold lay_blocks in HPm. cbn [l_calls l_spill l_answer l_reply] in HPm. rewrite Hsp in O1, O2, Hpn.
  split.
  + apply (nodup_fst_perm _ _ (Permutation_sym HPm)). apply nodup_snoc_fst; [exact O1 | exact Hpn].
  + intros pn Hin. apply (Permutation_in _ HPm) in Hin. apply in_app_iff in Hin as [Hin | [<- | []]].
    * exact (O2 pn Hin).
    * cbn [fst snd]. unfold REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL in Hag, Has. split; [exact Hag | exact Has].
Qed.
