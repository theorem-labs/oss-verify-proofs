(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder-state steps of sup_instance_info's ASan walk (plugin-hostd/fuzz_command): what record() and the one arg_i of the call do to lib/A/Prog/CmdRep.v's rec_repA, after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the object facts a walk carries across a call); the transport lemmas follow lib/A/Prog/answer_code.v's acall_at_kept / rec_repA_kept. *)

(* The recorder's representation (CmdRep.v rec_repA) across the steps of sup_instance_info (recorder.c:395-401):
   - a write outside g_rec, record.spill and the recorder's own blocks keeps it (`sii_rec_repA_kept`);
   - record() then arg_i on a free slot of g_rec's table (`sii_arep_slot`) or on record.spill whose arguments
     rec_calls_free has just released (`sii_arep_spill`) gives the representation of rec_record R fn [s]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma sii_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma sii_aval_eq : forall (rd rd' : reader) a n v, aval_mem rd a n v -> aval_mem rd' a n v ->
forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k).
Proof. intros rd rd' a n v H H' k Hk. rewrite (H' k Hk), (H k Hk). reflexivity. Qed.

Lemma sii_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma sii_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (sii_abytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.

Lemma sii_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
pose proof (Nat2Z.is_nonneg (length (snd c))) as Hl0.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (sii_aval_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; lia]|].
split; [apply (sii_aval_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (sii_aval_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (sii_astr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

(* a call with one argument, the shape record() + arg_i leave in a slot *)
Lemma sii_acall1 : forall bl (rd : reader) a fn s p k,
0 <= fn < REC_FN_COUNT ->
aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 1 ->
aval_mem rd (a + CALL_OFF_ARGS + 8 * Z.of_nat 0) 8 p -> p <> 0 -> In (p, k) bl ->
Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> astr_atR rd p s ->
acall_at bl rd a (fn, [s]) [(p, k)].
Proof.
intros bl rd a fn s p k Hfn HF HN HP Hp0 Hin Hk HS.
unfold acall_at. cbn [fst snd].
refine (conj Hfn (conj _ (conj _ (conj HF (conj HN (conj _ _)))))).
- cbn [length]. lia.
- reflexivity.
- apply (proj2 (stdpp.base.NoDup_ListNoDup _)). cbn [map]. apply List.NoDup_cons; [exact (fun H => H) | apply List.NoDup_nil].
- intros j s' pn Hs Hpn. destruct j as [|j]; [|destruct j; discriminate].
  cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
  split; [exact HP|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hk | exact HS].
Qed.

Section m.
Variable B : asyms.

Lemma sii_lay_in_calls : forall Q P pn i, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q P pn i Hi Hpn. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ Hi) | exact Hpn].
Qed.

Lemma sii_lay_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact H. Qed.

Lemma sii_lay_in_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_app_iff. right. apply in_app_iff. right.
apply in_app_iff. left. left. reflexivity.
Qed.

Lemma sii_lay_in_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_app_iff. right. apply in_app_iff. right.
apply in_app_iff. right. left. reflexivity.
Qed.

Lemma sii_rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HA & HO) pn Hpn. apply (lay_blocks_in _ rd A_G_REC A_REC_SPILL R Q HA). apply HO. exact Hpn. Qed.

(* the scalar fields, the answer and the reply survive a write that keeps g_rec's bytes from OFF_ANSWER on and
   the first 8, and every block the recorder owns *)
Lemma sii_arep_tail_kept : forall bl bl2 (rd rd2 : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, A_G_REC <= a < A_G_REC + OFF_NCALLS -> rd2 a = rd a) ->
(forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE -> rd2 a = rd a) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl2) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd2 (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl2 rd2 A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl2 rd2 A_G_REC (r_reply R) (l_reply Q) /\
ag1_scalars rd2 A_G_REC R.
Proof.
intros bl bl2 rd rd2 R Q HA Hlo Hhi Hbl Hb.
destruct HA as (_ & _ & _ & _ & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & _).
unfold aanswer_at, areply_at, ag1_scalars in *.
unfold OFF_NCALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|] eqn:Eq; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (sii_lay_in_answer Q q Eq) as Hq.
    split; [apply (sii_aval_kept rd); [exact A1 | intros k Hk; apply Hhi; lia]|].
    split; [exact A2|]. split; [apply Hbl; exact Hq|]. split; [exact A4|].
    split; [apply (sii_astr_kept rd); [exact A5 | intros i Hi; apply Hb; [exact Hq | lia]] | exact A6].
  - apply (sii_aval_kept rd); [exact Ha | intros k Hk; apply Hhi; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|] eqn:Eq; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (sii_lay_in_reply Q q Eq) as Hq.
    split; [apply (sii_aval_kept rd); [exact A1 | intros k Hk; apply Hhi; lia]|].
    split; [apply (sii_aval_kept rd); [exact A2 | intros k Hk; apply Hhi; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply Hbl; exact Hq|]. split; [exact A6|].
    split; [apply (sii_abytes_kept rd); [exact A7 | intros i Hi; apply Hb; [exact Hq | lia]] | exact A8].
  - destruct Hr as [A1 A2]. split; apply (sii_aval_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hhi; lia]. }
split; [apply (sii_aval_kept rd); [exact S1 | intros k Hk; apply Hlo; lia]|].
split; [apply (sii_aval_kept rd); [exact S2 | intros k Hk; apply Hlo; lia]|].
split; [apply (sii_aval_kept rd); [exact S3 | intros k Hk; apply Hhi; lia]|].
split; [apply (sii_aval_kept rd); [exact S4 | intros k Hk; apply Hhi; lia]|].
split; [apply (sii_aval_kept rd); [exact S5 | intros k Hk; apply Hhi; lia]|].
exact S6.
Qed.

(* a write outside g_rec, record.spill and the recorder's own blocks keeps the representation *)
Lemma sii_arep_kept : forall bl bl' (rd rd' : reader) R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA HblQ Hg Hs HbQ.
destruct (sii_arep_tail_kept _ _ rd rd' R Q HA
  ltac:(intros a Ha; apply Hg; unfold OFF_NCALLS, REC_SIZE in *; lia)
  ltac:(intros a Ha; apply Hg; unfold OFF_ANSWER, REC_SIZE in *; lia) HblQ HbQ) as (TA & TR & TS).
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & Hown).
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact TA|]; split; [exact TR|]; split; [exact TS | exact Hown]].
split; [exact C1|]. split; [exact C2|].
split; [apply (sii_aval_kept rd); [exact C3 | intros k Hk; apply Hg; unfold OFF_NCALLS, REC_SIZE; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
  pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
  pose proof HC as (_ & HL6 & _).
  apply (sii_acall_kept bl _ rd); [exact HC | | |].
  + intros pn Hpn. apply HblQ. exact (sii_lay_in_calls Q P pn i Hp Hpn).
  + intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  + intros pn j Hpn Hj. apply HbQ; [exact (sii_lay_in_calls Q P pn i Hp Hpn) | exact Hj].
- split; [|exact C6].
  pose proof C5 as (_ & HL6 & _).
  apply (sii_acall_kept bl _ rd); [exact C5 | | |].
  + intros pn Hpn. apply HblQ. exact (sii_lay_in_spill Q pn Hpn).
  + intros j Hj. apply Hs. unfold CALL_OFF_ARGS, SC_SIZE in *. lia.
  + intros pn j Hpn Hj. apply HbQ; [exact (sii_lay_in_spill Q pn Hpn) | exact Hj].
Qed.

Lemma sii_rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
apply (sii_arep_kept _ _ rd rd' R Q HA); [intros pn Hpn; apply Hbl, HO, Hpn | exact Hg | exact Hs |].
intros [p n] i Hpn Hi. apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi).
Qed.

Lemma sii_nodup_cons_perm : forall (l l' : list (Z * Z)) x, Permutation l' (x :: l) ->
NoDup (map fst l) -> ~ In (fst x) (map fst l) -> NoDup (map fst l').
Proof.
intros l l' x HP Hnd Hn. apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in Hnd.
apply (Permutation_NoDup (l := map fst (x :: l))).
- apply Permutation_map. apply Permutation_sym. exact HP.
- cbn [map]. apply List.NoDup_cons; [exact Hn | exact Hnd].
Qed.

(* record() on a free slot of g_rec's table, then arg_i with the call's one argument s in the fresh block (p, k) *)
Lemma sii_arep_slot : forall bl rd bl2 (rd2 : reader) R Q c fn s p k,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(length (r_calls R) < 16)%nat ->
c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
   ~ (c <= a < c + 16) -> rd2 a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd2 a = rd a) ->
aval_mem rd2 (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd2 (c + CALL_OFF_FN) 4 fn -> aval_mem rd2 (c + CALL_OFF_NARGS) 4 1 ->
aval_mem rd2 (c + CALL_OFF_ARGS + 8 * Z.of_nat 0) 8 p ->
0 <= fn < REC_FN_COUNT -> p <> 0 -> Z.of_nat (length s) <= LMAX -> k = Z.of_nat (length s) + 1 ->
astr_atR rd2 p s ->
(forall pn, In pn (lay_blocks Q) -> In pn bl2) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd2 (fst pn + i) = rd (fst pn + i)) ->
In (p, k) bl2 -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
arep_at bl2 rd2 A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, [s])]))
  (RLay (l_calls Q ++ [[(p, k)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl rd bl2 rd2 R Q c fn s p k HA Hn Hc Hg Hs HN HF HNA HP Hfn Hp0 Hls Hk HS Hbl Hb Hin Hfr Hap1 Hap2.
set (n := length (r_calls R)) in *.
destruct (sii_arep_tail_kept _ _ rd rd2 R Q HA
  ltac:(intros a Ha; apply Hg; unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia)
  ltac:(intros a Ha; apply Hg; unfold OFF_ANSWER, OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia) Hbl Hb) as (TA & TR & TS).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & (Hnd & Hapo)).
unfold arep_at. cbn [r_calls r_spill r_answer r_reply set_calls l_calls l_spill l_answer l_reply].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact TA|]; split; [exact TR|]; split; [exact TS|]].
- unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
  rewrite !length_app. cbn [length]. fold n.
  split; [lia|]. split; [rewrite C2; reflexivity|].
  split; [rewrite Nat2Z.inj_add; exact HN|].
  split.
  + intros i c' P Hc' HP'.
    destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
    * rewrite nth_error_app1 in Hc' by exact Hi.
      rewrite nth_error_app1 in HP' by (rewrite C2; exact Hi).
      destruct (C4 i c' P Hc' HP') as [HC HFo]. split; [|exact HFo].
      apply (sii_acall_kept bl _ rd); [exact HC | | |].
      -- intros pn Hpn. apply Hbl. exact (sii_lay_in_calls Q P pn i HP' Hpn).
      -- pose proof HC as (_ & HL6 & _).
         intros j Hj. rewrite <- !Z.add_assoc. apply Hg; unfold CALL_OFF_ARGS, OFF_CALLS, OFF_NCALLS, CALL_SIZE, REC_SIZE in *; lia.
      -- intros pn j Hpn Hj. apply Hb; [exact (sii_lay_in_calls Q P pn i HP' Hpn) | exact Hj].
    * rewrite nth_error_app2 in Hc' by exact Hi.
      rewrite nth_error_app2 in HP' by (rewrite C2; exact Hi).
      rewrite C2 in HP'. fold n in Hc', HP'.
      destruct (i - n)%nat as [|j] eqn:Hj; [|destruct j; discriminate].
      cbn in Hc', HP'. injection Hc' as <-. injection HP' as <-.
      assert (Ei : i = n) by lia. subst i.
      split; [|constructor; [lia | constructor]].
      rewrite <- Hc. apply (sii_acall1 bl2 rd2 c fn s p k Hfn HF HNA HP Hp0 Hin ltac:(unfold LMAX in *; lia) HS).
  + split; [|exact C6].
    pose proof C5 as (_ & HL6 & _).
    apply (sii_acall_kept bl _ rd); [exact C5 | | |].
    * intros pn Hpn. apply Hbl. exact (sii_lay_in_spill Q pn Hpn).
    * intros j Hj. apply Hs. unfold CALL_OFF_ARGS, SC_SIZE in *. lia.
    * intros pn j Hpn Hj. apply Hb; [exact (sii_lay_in_spill Q pn Hpn) | exact Hj].
- assert (HPL : Permutation (lay_blocks (RLay (l_calls Q ++ [[(p, k)]]) (l_spill Q) (l_answer Q) (l_reply Q)))
                  ((p, k) :: lay_blocks Q)).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
    rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  unfold ag1_own. split.
  + exact (sii_nodup_cons_perm (lay_blocks Q) _ (p, k) HPL Hnd Hfr).
  + intros pn Hpn. apply (Permutation_in _ HPL) in Hpn. destruct Hpn as [<- | Hpn].
    * split; [exact Hap1 | exact Hap2].
    * exact (Hapo pn Hpn).
Qed.

(* record() on record.spill after rec_calls_free released its arguments, then arg_i *)
Lemma sii_arep_spill : forall bl rd bl2 (rd2 : reader) R Q fn s p k,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> snd (r_spill R) = [] ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd2 a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 16) -> rd2 a = rd a) ->
aval_mem rd2 (A_REC_SPILL + CALL_OFF_FN) 4 fn -> aval_mem rd2 (A_REC_SPILL + CALL_OFF_NARGS) 4 1 ->
aval_mem rd2 (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat 0) 8 p ->
0 <= fn < REC_FN_COUNT -> p <> 0 -> Z.of_nat (length s) <= LMAX -> k = Z.of_nat (length s) + 1 ->
astr_atR rd2 p s ->
(forall pn, In pn (lay_blocks Q) -> In pn bl2) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd2 (fst pn + i) = rd (fst pn + i)) ->
In (p, k) bl2 -> ~ In p (map fst (lay_blocks Q)) ->
iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
arep_at bl2 rd2 A_G_REC A_REC_SPILL (set_spill R (fn, [s])) (RLay (l_calls Q) [(p, k)] (l_answer Q) (l_reply Q)).
Proof.
intros bl rd bl2 rd2 R Q fn s p k HA Hsp Hg Hs HF HNA HP Hfn Hp0 Hls Hk HS Hbl Hb Hin Hfr Hap1 Hap2.
destruct (sii_arep_tail_kept _ _ rd rd2 R Q HA
  ltac:(intros a Ha; apply Hg; unfold OFF_NCALLS, REC_SIZE in *; lia)
  ltac:(intros a Ha; apply Hg; unfold OFF_ANSWER, REC_SIZE in *; lia) Hbl Hb) as (TA & TR & TS).
pose proof HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & _ & _ & _ & (Hnd & Hapo)).
assert (Hl0 : l_spill Q = []).
{ pose proof C5 as (_ & _ & HL & _). rewrite Hsp in HL. destruct (l_spill Q); [reflexivity | discriminate]. }
unfold arep_at. cbn [r_calls r_spill r_answer r_reply set_spill l_calls l_spill l_answer l_reply].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split; [|split; [exact TA|]; split; [exact TR|]; split; [exact TS|]].
- unfold ag1_calls. cbn [r_calls r_spill set_spill l_calls l_spill].
  split; [exact C1|]. split; [exact C2|].
  split; [apply (sii_aval_kept rd); [exact C3 | intros j Hj; apply Hg; unfold OFF_NCALLS, REC_SIZE; lia]|].
  split.
  + intros i c' P Hc' HP'. destruct (C4 i c' P Hc' HP') as [HC HFo]. split; [|exact HFo].
    pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc'; discriminate)) as Hi.
    pose proof HC as (_ & HL6 & _).
    apply (sii_acall_kept bl _ rd); [exact HC | | |].
    * intros pn Hpn. apply Hbl. exact (sii_lay_in_calls Q P pn i HP' Hpn).
    * intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    * intros pn j Hpn Hj. apply Hb; [exact (sii_lay_in_calls Q P pn i HP' Hpn) | exact Hj].
  + split; [|constructor; [lia | constructor]].
    apply (sii_acall1 bl2 rd2 A_REC_SPILL fn s p k Hfn HF HNA HP Hp0 Hin ltac:(unfold LMAX in *; lia) HS).
- assert (HPL : Permutation (lay_blocks (RLay (l_calls Q) [(p, k)] (l_answer Q) (l_reply Q))) ((p, k) :: lay_blocks Q)).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite Hl0. cbn [app].
    apply Permutation_sym. apply Permutation_middle. }
  unfold ag1_own. split.
  + exact (sii_nodup_cons_perm (lay_blocks Q) _ (p, k) HPL Hnd Hfr).
  + intros pn Hpn. apply (Permutation_in _ HPL) in Hpn. destruct Hpn as [<- | Hpn].
    * split; [exact Hap1 | exact Hap2].
    * exact (Hapo pn Hpn).
Qed.
End m.
