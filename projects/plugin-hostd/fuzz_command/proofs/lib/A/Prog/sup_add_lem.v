(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of pins_clear (plugin-hostd/fuzz_command, entry 0x8ccb4), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACke.v (the instantiation of the cgif_close walk) over
   fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_clear.v, with its module paths and module names changed; 915 of its 942 lines of code are new or changed and 55 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command: the lemmas more than one stage uses.

   The recorder's representation (lib/A/Prog/CmdRep.v rec_repA) across the walk's stores and its callees'
   journals, the string arguments carried from the entry to the call of xstrdup, the read-only facts carried along
   the journal, and the frame chain at a call. The stages are sup_add_s1.v .. sup_add_s7.v; the vocabulary is
   sup_add_s0.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

(* a byte of g_rec or of record.spill *)
Definition in_rec (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

(* ---- list and byte facts (NoDup is stdpp's, as in CmdRep.v; the proofs go through List.NoDup) ---- *)
Lemma lem_nodup_snoc : forall {T : Type} (l : list T) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
intros T l x H Hx. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H.
apply NoDup_app; [exact H | constructor; [intros []|constructor] |].
intros a Ha [E|[]]. subst a. exact (Hx Ha).
Qed.
Lemma lem_own_snoc : forall (A1 P A2 : list (Z * Z)) x,
  NoDup (map fst (A1 ++ P ++ A2)) -> ~ In (fst x) (map fst (A1 ++ P ++ A2)) ->
  NoDup (map fst (A1 ++ (P ++ [x]) ++ A2)).
Proof.
intros A1 P A2 x H Hx. apply NoDup_ListNoDup.
apply (Permutation_NoDup (l := map fst ((A1 ++ P ++ A2) ++ [x]))).
- apply Permutation_map. rewrite <- !app_assoc. do 2 apply Permutation_app_head. apply Permutation_app_comm.
- apply NoDup_ListNoDup. rewrite map_app. apply lem_nodup_snoc; assumption.
Qed.
Lemma lem_fst_unique : forall (L : list (Z * Z)) p n m, NoDup (map fst L) -> In (p, n) L -> In (p, m) L -> n = m.
Proof.
induction L as [|[q k] L IH]; intros p n m H H1 H2; [destruct H1|].
apply NoDup_ListNoDup in H. cbn in H. inversion H as [|? ? Hq HL]; subst.
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- congruence.
- exfalso. injection E1 as <- <-. apply Hq. exact (in_map fst L (q, m) H2).
- exfalso. injection E2 as <- <-. apply Hq. exact (in_map fst L (q, n) H1).
- exact (IH p n m (proj2 (NoDup_ListNoDup _) HL) H1 H2).
Qed.
Lemma lem_unowned : forall (L : list (Z * Z)) lo hi,
  forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
  forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
induction L as [|r L IH]; intros lo hi H a Ha HE; [inversion HE|].
cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
apply Exists_cons in HE as [Hr|Hr].
- unfold in_zr in Hr. apply orb_true_iff in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
- exact (IH lo hi H2 a Ha Hr).
Qed.
Lemma lem_in_z : forall (x : Z) l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.
Lemma lem_no0 : forall (l : list byte), forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
induction l as [|b l IH]; intros H Hin; [destruct Hin|].
cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
destruct Hin as [E|Hin]; [|exact (IH H2 Hin)].
subst b. vm_compute in H1. discriminate.
Qed.
Lemma lem_req_pos : forall n, 1 <= n -> req_size n = n.
Proof. intros n H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma lem_rdword_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hv. unfold rdword.
pose proof (H 0%nat ltac:(lia)) as E0. pose proof (H 1%nat ltac:(lia)) as E1.
pose proof (H 2%nat ltac:(lia)) as E2. pose proof (H 3%nat ltac:(lia)) as E3.
pose proof (H 4%nat ltac:(lia)) as E4. pose proof (H 5%nat ltac:(lia)) as E5.
pose proof (H 6%nat ltac:(lia)) as E6. pose proof (H 7%nat ltac:(lia)) as E7.
change (a + Z.of_nat 0) with (a + 0) in E0. change (a + Z.of_nat 1) with (a + 1) in E1.
change (a + Z.of_nat 2) with (a + 2) in E2. change (a + Z.of_nat 3) with (a + 3) in E3.
change (a + Z.of_nat 4) with (a + 4) in E4. change (a + Z.of_nat 5) with (a + 5) in E5.
change (a + Z.of_nat 6) with (a + 6) in E6. change (a + Z.of_nat 7) with (a + 7) in E7.
rewrite Z.add_0_r in E0.
rewrite E0, E1, E2, E3, E4, E5, E6, E7. f_equal. exact (YG0s.le_bytes8 v Hv).
Qed.
Lemma lem_aval_keep : forall (rd rd' : reader) a (n : nat) v lo hi,
  aval_mem rd a n v -> lo <= a -> a + Z.of_nat n <= hi -> (forall x, lo <= x < hi -> rd' x = rd x) ->
  aval_mem rd' a n v.
Proof. intros rd rd' a n v lo hi H H1 H2 K k Hk. rewrite K by lia. exact (H k Hk). Qed.
Lemma lem_abytes_keep : forall (rd rd' : reader) p l,
  abytes_atR rd p l -> (forall i, 0 <= i < Z.of_nat (length l) -> rd' (p + i) = rd (p + i)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma lem_astr_keep : forall (rd rd' : reader) p s,
  astr_atR rd p s -> (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] K. split; [|exact H2]. apply (lem_abytes_keep rd); [exact H1|].
intros i Hi. apply K. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

(* ---- the recorder's layout, piece by piece ---- *)
Lemma lem_acall_keep : forall bl bl' (rd rd' : reader) a c P,
  acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) K KP.
unfold acall_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
- apply (lem_aval_keep rd _ _ _ _ a (a + 56)); [exact H4|lia|lia|exact K].
- apply (lem_aval_keep rd _ _ _ _ a (a + 56)); [exact H5|lia|lia|exact K].
- intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  destruct (KP pn (nth_error_In P k Ep)) as [Kin Kp].
  refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
  + apply (lem_aval_keep rd _ _ _ _ a (a + 56)); [exact G1|lia|lia|exact K].
  + apply (lem_astr_keep rd); [exact G5|]. intros i Hi. apply Kp. lia.
Qed.
Lemma lem_acall_blocks : forall bl (rd : reader) a c P, acall_at bl rd a c P ->
  forall pn, In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) pn Hpn.
destruct (In_nth_error P pn Hpn) as [k Ek].
assert (Hk : (k < length (snd c))%nat) by (rewrite <- H3; apply nth_error_Some; rewrite Ek; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
destruct (H7 k s pn Es Ek) as (_ & _ & G3 & G4 & _). split; [exact G3|lia].
Qed.
Lemma lem_lay_in : forall bl (rd : reader) gr sc R Q, arep_at bl rd gr sc R Q ->
  forall pn, In pn (lay_blocks Q) -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HAn & HRp & _ & _) pn Hpn.
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
unfold lay_blocks in Hpn. rewrite !in_app_iff in Hpn. destruct Hpn as [Hc|[Hs|[Ha|Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as [i Ei].
  assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  exact (lem_acall_blocks _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) pn Hin).
- exact (lem_acall_blocks _ _ _ _ _ C5 pn Hs).
- revert HAn. unfold aanswer_at. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [q|];
  cbn [oblk In] in Ha; intros HAn; try contradiction.
  destruct Ha as [<-|[]]. destruct HAn as (_ & _ & G3 & G4 & _). split; [exact G3|lia].
- revert HRp. unfold areply_at. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [q|];
  cbn [oblk In] in Hr; intros HRp; try contradiction.
  destruct Hr as [<-|[]]. destruct HRp as (_ & _ & _ & G4 & G5 & G6 & _). split; [exact G5|].
  destruct x as [|b x]; [contradiction|]. cbn [length] in G6. lia.
Qed.
Lemma lem_ans_keep : forall bl bl' (rd rd' : reader) gr t q,
  aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H K KP. unfold aanswer_at in *.
destruct t as [x|]; destruct q as [pn|]; try contradiction.
- destruct H as (N1 & N2 & N3 & N4 & N5 & N6). destruct (KP pn (or_introl eq_refl)) as [Kin Kp].
  refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
  + apply (lem_aval_keep rd _ _ _ _ (gr + OFF_ANSWER) (gr + OFF_ANSWER + 8)); [exact N1|lia|lia|exact K].
  + apply (lem_astr_keep rd); [exact N5|]. intros i Hi. apply Kp. lia.
- apply (lem_aval_keep rd _ _ _ _ (gr + OFF_ANSWER) (gr + OFF_ANSWER + 8)); [exact H|lia|lia|exact K].
Qed.
Lemma lem_rep_keep : forall bl bl' (rd rd' : reader) gr y q,
  areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H K KP. unfold areply_at in *. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
destruct y as [x|]; destruct q as [pn|]; try contradiction.
- destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). destruct (KP pn (or_introl eq_refl)) as [Kin Kp].
  refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
  + apply (lem_aval_keep rd _ _ _ _ (gr + 928) (gr + 936 + 8)); [exact P1|lia|lia|exact K].
  + apply (lem_aval_keep rd _ _ _ _ (gr + 928) (gr + 936 + 8)); [exact P2|lia|lia|exact K].
  + apply (lem_abytes_keep rd); [exact P7|]. intros i Hi. apply Kp. lia.
- destruct H as [P1 P2]. split.
  + apply (lem_aval_keep rd _ _ _ _ (gr + 928) (gr + 936 + 8)); [exact P1|lia|lia|exact K].
  + apply (lem_aval_keep rd _ _ _ _ (gr + 928) (gr + 936 + 8)); [exact P2|lia|lia|exact K].
Qed.
Lemma lem_sc_keep : forall (rd rd' : reader) gr R h,
  ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + OFF_NREPLIES <= x < gr + OFF_NREPLIES + 4 \/
     gr + OFF_HOST <= x < gr + OFF_HOST + 8 -> rd' x = rd x) ->
  aval_mem rd' (gr + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
  ag1_scalars rd' gr (set_state R h).
Proof.
intros rd rd' gr R h (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10) K Hs Hh.
unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_state].
unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
refine (conj _ (conj _ (conj _ (conj Hs (conj _ (conj X6 (conj X7 (conj X8 (conj Hh X10))))))))).
- apply (lem_aval_keep rd _ _ _ _ (gr + 0) (gr + 0 + 4)); [exact X1|lia|lia|intros x Hx; apply K; lia].
- apply (lem_aval_keep rd _ _ _ _ (gr + 4) (gr + 4 + 4)); [exact X2|lia|lia|intros x Hx; apply K; lia].
- apply (lem_aval_keep rd _ _ _ _ (gr + 920) (gr + 920 + 4)); [exact X3|lia|lia|intros x Hx; apply K; lia].
- apply (lem_aval_keep rd _ _ _ _ (gr + 952) (gr + 952 + 8)); [exact X5|lia|lia|intros x Hx; apply K; lia].
Qed.
Lemma lem_set_state_id : forall R, set_state R (r_state R) = R.
Proof. intros R. destruct R. reflexivity. Qed.
Lemma lem_O_kept : forall (O L bl' : list (Z * Z)) (rd rd' : reader),
  (forall pn, In pn O <-> In pn L) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  (forall pn, In pn O -> In pn bl') ->
  forall pn, In pn L -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).
Proof.
intros O L bl' rd rd' HO KB KL [p n] Hpn. apply HO in Hpn.
split; [exact (KL _ Hpn)|]. intros i Hi. exact (KB p n i Hpn Hi).
Qed.
(* answer, reply and scalars, when the bytes from g_rec.answer to the end of g_rec and the first two words stay *)
Lemma lem_tail_keep : forall bl bl' (rd rd' : reader) R Q,
  aanswer_at bl rd A_G_REC (r_answer R) (l_answer Q) -> areply_at bl rd A_G_REC (r_reply R) (l_reply Q) ->
  ag1_scalars rd A_G_REC R ->
  (forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= x < A_G_REC + REC_SIZE -> rd' x = rd x) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q) /\
  ag1_scalars rd' A_G_REC R.
Proof.
intros bl bl' rd rd' R Q HAn HRp HX K KQ.
pose proof HX as (_ & _ & _ & X4 & _ & _ & _ & _ & X9 & _).
split; [|split].
- apply (lem_ans_keep bl _ rd); [exact HAn| |].
  + intros x Hx. apply K. right. unfold OFF_ANSWER, REC_SIZE in *. lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    exact Hpn.
- apply (lem_rep_keep bl _ rd); [exact HRp| |].
  + intros x Hx. apply K. right. unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
    exact Hpn.
- exact (lem_sc_keep rd rd' A_G_REC R (r_state R) HX
    ltac:(intros x Hx; apply K; unfold OFF_ANSWER, OFF_NREPLIES, OFF_HOST, REC_SIZE in *; lia)
    ltac:(apply (lem_aval_keep rd _ _ _ _ (A_G_REC + OFF_STATE) (A_G_REC + OFF_STATE + 8));
          [exact X4|lia|lia|intros x Hx; apply K; unfold OFF_ANSWER, OFF_STATE, REC_SIZE in *; lia]) X9).
Qed.
(* the whole representation, with g_rec.state set to h and every other byte of g_rec and record.spill kept *)
Lemma lem_arep_state : forall bl bl' (rd rd' : reader) R Q h,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, in_rec a -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_state R h) Q.
Proof.
intros bl bl' rd rd' R Q h (Hg8 & Hs8 & Hap & HC & HAn & HRp & HX & HW) K KQ Hs Hh.
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
refine (conj Hg8 (conj Hs8 (conj Hap (conj _ (conj _ (conj _ (conj _ HW))))))).
- unfold ag1_calls. cbn [r_calls r_spill set_state].
  refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
  + apply (lem_aval_keep rd _ _ _ _ (A_G_REC + OFF_NCALLS) (A_G_REC + OFF_NCALLS + 4)); [exact C3|lia|lia|].
    intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_NCALLS, OFF_STATE in *; lia.
  + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (lem_acall_keep bl _ rd); [exact Hc| |].
    * intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, OFF_STATE in *; lia.
    * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; left. apply in_concat. exists P.
      split; [eapply nth_error_In; exact EP|exact Hpn].
  + apply (lem_acall_keep bl _ rd); [exact C5| |].
    * intros x Hx. apply K; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, CALL_SIZE, OFF_STATE in *; lia.
    * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hpn.
- cbn [r_answer set_state]. apply (lem_ans_keep bl _ rd); [exact HAn| |].
  + intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_ANSWER, OFF_STATE in *; lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    exact Hpn.
- cbn [r_reply set_state]. apply (lem_rep_keep bl _ rd); [exact HRp| |].
  + intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_REPLY, OFF_REPLY_SIZE, OFF_STATE in *; lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
    exact Hpn.
- apply (lem_sc_keep rd); [exact HX| |exact Hs|exact Hh].
  intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_NREPLIES, OFF_HOST, OFF_STATE in *; lia.
Qed.
(* a slot that gets one more argument *)
Lemma lem_acall_snoc : forall bl bl' (rd rd' : reader) a fn A P s p n,
  acall_at bl rd a (fn, A) P -> (length A < 6)%nat ->
  (forall x, a <= x < a + CALL_SIZE -> ~ (a + CALL_OFF_NARGS <= x < a + CALL_OFF_NARGS + 4) ->
     ~ (a + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= x < a + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aval_mem rd' (a + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (a + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  In (p, n) bl' -> p <> 0 -> n = Z.of_nat (length s) + 1 -> Z.of_nat (length s) <= LMAX ->
  astr_atR rd' p s -> ~ In p (map fst P) ->
  acall_at bl' rd' a (fn, A ++ [s]) (P ++ [(p, n)]).
Proof.
intros bl bl' rd rd' a fn A P s p n (H1 & H2 & H3 & H4 & H5 & H6 & H7) HlA K KP Hna Harg Hin Hp0 Hn HLs Hstr Hfr.
cbn [fst snd] in *. unfold acall_at. cbn [fst snd].
unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
split; [exact H1|]. split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, H3; reflexivity|].
split; [apply (lem_aval_keep rd _ _ _ _ a (a + 4)); [exact H4|lia|lia|intros x Hx; apply K; lia]|].
split; [rewrite length_app; cbn [length];
  replace (Z.of_nat (length A + 1)) with (Z.of_nat (length A) + 1) by lia; exact Hna|].
split; [rewrite map_app; apply lem_nodup_snoc; [exact H6|exact Hfr]|].
intros k s0 pn Es Ep. destruct (Nat.lt_ge_cases k (length A)) as [Hk|Hk].
- rewrite nth_error_app1 in Es by exact Hk. rewrite nth_error_app1 in Ep by lia.
  destruct (H7 k s0 pn Es Ep) as (G1 & G2 & G3 & G4 & G5). destruct (KP pn (nth_error_In P k Ep)) as [Kin Kp].
  split; [apply (lem_aval_keep rd _ _ _ _ (a + 8 + 8 * Z.of_nat k) (a + 8 + 8 * Z.of_nat k + 8));
    [exact G1|lia|lia|intros x Hx; apply K; lia]|].
  split; [exact G2|]. split; [exact Kin|]. split; [exact G4|].
  apply (lem_astr_keep rd); [exact G5|]. intros i Hi. apply Kp. lia.
- destruct (Nat.eq_dec k (length A)) as [->|Hne].
  + rewrite nth_error_app2, Nat.sub_diag in Es by lia. cbn in Es. injection Es as <-.
    rewrite nth_error_app2 in Ep by lia. rewrite H3, Nat.sub_diag in Ep. cbn in Ep. injection Ep as <-.
    cbn [fst snd]. split; [exact Harg|]. split; [exact Hp0|]. split; [exact Hin|]. split; [lia|exact Hstr].
  + exfalso. assert (E : nth_error (A ++ [s]) k = None) by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    congruence.
Qed.
(* the owned blocks and the block list after one more argument block *)
Lemma lem_own_mem : forall (O : list (Z * Z)) Q Q' A1 P A2 p n,
  (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
  lay_blocks Q = A1 ++ P ++ A2 -> lay_blocks Q' = A1 ++ (P ++ [(p, n)]) ++ A2 ->
  ag1_own A_G_REC A_REC_SPILL Q -> ~ In p (map fst (lay_blocks Q)) ->
  iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
  ag1_own A_G_REC A_REC_SPILL Q' /\ (forall pn, In pn (O ++ [(p, n)]) <-> In pn (lay_blocks Q')).
Proof.
intros O Q Q' A1 P A2 p n HO EL EL' [W1 W2] Hfr Hap1 Hap2. split.
- unfold ag1_own. rewrite EL'. split.
  + apply lem_own_snoc; rewrite <- EL; assumption.
  + intros pn Hpn. rewrite !in_app_iff in Hpn. cbn [In] in Hpn.
    destruct Hpn as [H|[[H|[H|[]]]|H]].
    * apply W2. rewrite EL. apply in_or_app; left; exact H.
    * apply W2. rewrite EL. apply in_or_app; right; apply in_or_app; left; exact H.
    * subst pn. cbn [fst snd]. exact (conj Hap1 Hap2).
    * apply W2. rewrite EL. apply in_or_app; right; apply in_or_app; right; exact H.
- intros pn. specialize (HO pn). rewrite EL in HO. rewrite EL'. rewrite !in_app_iff in *. cbn [In] in *. tauto.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
(* the record fact a heap string's word tail needs (a statement CmdRecFacts.v proves), CmdRecImg.v's lemma by exact *)
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
(* every lemma of this Section takes all of its variables and hypotheses (B HB LAWS, and in Section e2 below IMG),
   the argument list the stages are written against, whatever its proof uses *)
Local Set Default Proof Using "All".

(* ---- the program's statics ---- *)
Lemma sa_HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a Ha. rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. unfold cmd_PG in Ha.
apply inFP_cons in Ha as [H|Ha]; [apply Exists_cons_hd; unfold in_zr, A_G_REC in *; cbn [fst snd]; lia|].
apply inFP_cons in Ha as [H|Ha]; [apply Exists_cons_tl, Exists_cons_hd; unfold in_zr, A_REC_SPILL in *; cbn [fst snd]; lia|].
apply inFP_cons in Ha as [H|Ha]; [do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr, A_G_QUITTING in *; cbn [fst snd]; lia|].
exfalso. exact (inFP_nil a Ha).
Qed.
Lemma sa_prog_unowned : forall a, inFP cmd_PG a ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO. unfold cmd_PG in Ha.
apply inFP_cons in Ha as [H|Ha].
{ split; [apply (lem_unowned _ A_G_REC (A_G_REC + 960)); [vm_compute; reflexivity|lia]|unfold A_G_REC in H; lia]. }
apply inFP_cons in Ha as [H|Ha].
{ split; [apply (lem_unowned _ A_REC_SPILL (A_REC_SPILL + 56)); [vm_compute; reflexivity|lia]|unfold A_REC_SPILL in H; lia]. }
apply inFP_cons in Ha as [H|Ha].
{ split; [apply (lem_unowned _ A_G_QUITTING (A_G_QUITTING + 4)); [vm_compute; reflexivity|lia]|unfold A_G_QUITTING in H; lia]. }
exfalso. exact (inFP_nil a Ha).
Qed.

(* ---- the recorder's representation ---- *)
(* kept: the bytes of g_rec, record.spill and the recorder's blocks unchanged, its blocks still live *)
Lemma rec_repA_kept : forall ly S rd ly' S' (rd' : reader) R O,
  rec_repA B ly S rd R O ->
  (forall a, in_rec a -> rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) KG KB KL.
exists Q. split; [|exact HO].
pose proof HA as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & X4 & _ & _ & _ & _ & X9 & _) & _).
rewrite <- (lem_set_state_id R).
apply (lem_arep_state (ablocks B ly S) _ rd); [exact HA| | | |exact X9].
- intros a Ha _. exact (KG a Ha).
- exact (lem_O_kept O (lay_blocks Q) _ rd rd' HO KB KL).
- apply (lem_aval_keep rd _ _ _ _ (A_G_REC + OFF_STATE) (A_G_REC + OFF_STATE + 8)); [exact X4|lia|lia|].
  intros x Hx. apply KG. unfold in_rec, A_G_REC, REC_SIZE, OFF_STATE in *. lia.
Qed.
(* record() on the table arm: ncalls := n + 1, then the slot's fn := REC_ADD and nargs := 0 *)
Lemma rec_repA_record_table : forall ly S rd ly' S' (rd' : reader) R O,
  rec_repA B ly S rd R O -> (length (r_calls R) < 16)%nat ->
  let c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) in
  (forall a, in_rec a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 8) ->
     rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 REC_ADD -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  rec_repA B ly' S' rd' (rec_record R REC_ADD []) O.
Proof.
intros ly S rd ly' S' rd' R O HR Hlt. cbv zeta. intros K KB KL Hnc Hfn Hna.
destruct HR as (Q & HA & HO).
pose proof (lem_O_kept O (lay_blocks Q) _ rd rd' HO KB KL) as KQ.
rewrite (rec_record_calls R REC_ADD [] Hlt).
assert (EL : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite !app_nil_r. reflexivity. }
exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
split; [|intros pn; rewrite EL; exact (HO pn)].
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
destruct (lem_tail_keep (ablocks B ly S) (ablocks B ly' S') rd rd' R Q HAn HRp HX) as (T1 & T2 & T3).
{ intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; lia. }
{ exact KQ. }
refine (conj Hg8 (conj Hs8 (conj Hap (conj _ (conj T1 (conj T2 (conj T3 _))))))).
2: { unfold ag1_own. rewrite EL. exact HW. }
unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, C2; reflexivity|].
split.
{ rewrite length_app. cbn [length].
  replace (Z.of_nat (length (r_calls R) + 1)) with (Z.of_nat (length (r_calls R)) + 1) by lia. exact Hnc. }
split.
2: { split; [|exact C6]. apply (lem_acall_keep (ablocks B ly S) _ rd); [exact C5| |].
  - intros x Hx. apply K; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hpn. }
intros i c P Ec EP.
destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
- rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by lia.
  destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  apply (lem_acall_keep (ablocks B ly S) _ rd); [exact Hc| |].
  + intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; left. apply in_concat. exists P.
    split; [eapply nth_error_In; exact EP|exact Hpn].
- destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
  + rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
    rewrite nth_error_app2 in EP by lia. rewrite C2, Nat.sub_diag in EP. cbn in EP. injection EP as <-.
    split; [|constructor].
    unfold acall_at. cbn [fst snd length].
    refine (conj _ (conj _ (conj eq_refl (conj Hfn (conj Hna (conj NoDup_nil_2 _)))))).
    * unfold REC_ADD, REC_FN_COUNT. lia.
    * lia.
    * intros k s pn Es. destruct k; discriminate.
  + exfalso. assert (E : nth_error (r_calls R ++ [(REC_ADD, [])]) i = None)
      by (apply nth_error_None; rewrite length_app; cbn [length]; lia). congruence.
Qed.
(* record() on the spill arm, after rec_calls_free(&record.spill, 1) cleared the spill's arguments: fn := REC_ADD *)
Lemma rec_repA_spill_fn : forall ly S rd ly' S' (rd' : reader) R O f,
  rec_repA B ly S rd (set_spill R (f, [])) O -> length (r_calls R) = 16%nat ->
  (forall a, in_rec a -> ~ (A_REC_SPILL + CALL_OFF_FN <= a < A_REC_SPILL + CALL_OFF_FN + 4) -> rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 REC_ADD ->
  rec_repA B ly' S' rd' (rec_record R REC_ADD []) O.
Proof.
intros ly S rd ly' S' rd' R O f (Q & HA & HO) Heq K KB KL Hfn.
pose proof (lem_O_kept O (lay_blocks Q) _ rd rd' HO KB KL) as KQ.
rewrite (rec_record_spill R REC_ADD [] Heq).
exists Q. split; [|exact HO].
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
destruct (lem_tail_keep (ablocks B ly S) (ablocks B ly' S') rd rd' (set_spill R (f, [])) Q HAn HRp HX)
  as (T1 & T2 & T3).
{ intros x Hx. apply K; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, CALL_OFF_FN, OFF_ANSWER in *; lia. }
{ exact KQ. }
refine (conj Hg8 (conj Hs8 (conj Hap (conj _ (conj T1 (conj T2 (conj T3 HW))))))).
unfold ag1_calls. cbn [r_calls r_spill set_spill] in *.
refine (conj C1 (conj C2 (conj _ (conj _ (conj _ (Forall_nil _)))))).
- apply (lem_aval_keep rd _ _ _ _ (A_G_REC + OFF_NCALLS) (A_G_REC + OFF_NCALLS + 4)); [exact C3|lia|lia|].
  intros x Hx. apply K; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, CALL_OFF_FN in *; lia.
- intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (lem_acall_keep (ablocks B ly S) _ rd); [exact Hc| |].
  + intros x Hx. apply K; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_FN in *; lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; left. apply in_concat. exists P.
    split; [eapply nth_error_In; exact EP|exact Hpn].
- destruct C5 as (F1 & F2 & F3 & F4 & F5 & F6 & F7). cbn [fst snd length] in F3, F5.
  unfold acall_at. cbn [fst snd length].
  refine (conj _ (conj _ (conj F3 (conj Hfn (conj _ (conj F6 _)))))).
  + unfold REC_ADD, REC_FN_COUNT. lia.
  + lia.
  + apply (lem_aval_keep rd _ _ _ _ (A_REC_SPILL + CALL_OFF_NARGS) (A_REC_SPILL + CALL_OFF_NARGS + 4)); [exact F5|lia|lia|].
    intros x Hx. apply K; unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, CALL_OFF_NARGS, CALL_OFF_FN in *; lia.
  + intros k s pn Es. destruct k; discriminate.
Qed.
(* arg_s / arg_i: the slot's args[k] := p (a fresh block holding s), nargs := k + 1 *)
Lemma rec_repA_append : forall ly S rd ly' S' (rd' : reader) R A O s p n,
  rec_repA B ly S rd (rec_record R REC_ADD A) O -> (length A < 6)%nat ->
  let c := sa_c R in let k := Z.of_nat (length A) in
  (forall a, in_rec a -> ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * k <= a < c + CALL_OFF_ARGS + 8 * k + 8) -> rd' a = rd a) ->
  (forall p0 n0 i, In (p0, n0) O -> 0 <= i < n0 -> rd' (p0 + i) = rd (p0 + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (k + 1) -> aval_mem rd' (c + CALL_OFF_ARGS + 8 * k) 8 p ->
  In (p, n) (ablocks B ly' S') -> p <> 0 -> n = Z.of_nat (length s) + 1 -> Z.of_nat (length s) <= LMAX ->
  astr_atR rd' p s -> ~ In p (map fst O) ->
  iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
  rec_repA B ly' S' rd' (rec_record R REC_ADD (A ++ [s])) (O ++ [(p, n)]).
Proof.
intros ly S rd ly' S' rd' R A O s p n HR HlA. cbv zeta.
intros K KB KL Hna Harg Hin Hp0 Hn HLs Hstr Hfr Hap1 Hap2.
destruct HR as (Q & HA & HO).
pose proof (lem_O_kept O (lay_blocks Q) _ rd rd' HO KB KL) as KQ.
assert (Hfr' : ~ In p (map fst (lay_blocks Q))).
{ intros H. apply in_map_iff in H as ([p' n'] & E & Hy). cbn in E. subst p'. apply Hfr. apply HO in Hy.
  exact (in_map fst O (p, n') Hy). }
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
- (* the table arm *)
  assert (Ec : sa_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
  { unfold sa_c. rewrite (proj2 (Nat.ltb_lt _ _) Hlt). reflexivity. }
  rewrite Ec in K, Hna, Harg.
  rewrite (rec_record_calls R REC_ADD A Hlt) in HA. rewrite (rec_record_calls R REC_ADD (A ++ [s]) Hlt).
  destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). cbn [r_calls r_spill set_calls] in C1, C2, C3, C4, C5, C6.
  assert (HQne : l_calls Q <> []).
  { intros E. rewrite E, length_app in C2. cbn [length] in C2. lia. }
  destruct (@exists_last _ (l_calls Q) HQne) as (Lc & P & EQ).
  assert (HLc : length Lc = length (r_calls R)).
  { rewrite EQ, !length_app in C2. cbn [length] in C2. lia. }
  assert (Ex : nth_error (r_calls R ++ [(REC_ADD, A)]) (length (r_calls R)) = Some (REC_ADD, A)).
  { rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  assert (EP : nth_error (l_calls Q) (length (r_calls R)) = Some P).
  { rewrite EQ, nth_error_app2, HLc, Nat.sub_diag by lia. reflexivity. }
  destruct (C4 _ _ _ Ex EP) as [HcP HLA]. cbn [snd] in HLA.
  assert (EL : lay_blocks Q = concat Lc ++ P ++ (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
  { unfold lay_blocks. rewrite EQ, concat_app. cbn [concat]. rewrite app_nil_r, <- app_assoc. reflexivity. }
  assert (EL' : lay_blocks (RLay (Lc ++ [P ++ [(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)) =
    concat Lc ++ (P ++ [(p, n)]) ++ (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite app_nil_r, <- app_assoc. reflexivity. }
  destruct (lem_own_mem O Q _ _ _ _ p n HO EL EL' HW Hfr' Hap1 Hap2) as [HW' HO'].
  exists (RLay (Lc ++ [P ++ [(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)). split; [|exact HO'].
  destruct (lem_tail_keep (ablocks B ly S) (ablocks B ly' S') rd rd' (set_calls R (r_calls R ++ [(REC_ADD, A)])) Q
    HAn HRp HX) as (T1 & T2 & T3).
  { intros x Hx. apply K;
      unfold in_rec, A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, OFF_ANSWER in *; lia. }
  { exact KQ. }
  refine (conj Hg8 (conj Hs8 (conj Hap (conj _ (conj T1 (conj T2 (conj T3 HW'))))))).
  unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app, HLc; reflexivity|].
  split.
  { rewrite length_app in C3 |- *. cbn [length] in C3 |- *.
    apply (lem_aval_keep rd _ _ _ _ (A_G_REC + OFF_NCALLS) (A_G_REC + OFF_NCALLS + 4)); [exact C3|lia|lia|].
    intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  split.
  2: { split; [|exact C6]. apply (lem_acall_keep (ablocks B ly S) _ rd); [exact C5| |].
    - intros x Hx. apply K;
        unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
    - intros pn Hpn. apply KQ. rewrite EL. apply in_or_app; right; apply in_or_app; right.
      apply in_or_app; left; exact Hpn. }
  intros i c0 P0 Ec0 EP0.
  destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
  + rewrite nth_error_app1 in Ec0 by exact Hi. rewrite nth_error_app1 in EP0 by lia.
    assert (Ec1 : nth_error (r_calls R ++ [(REC_ADD, A)]) i = Some c0) by (rewrite nth_error_app1 by exact Hi; exact Ec0).
    assert (EP1 : nth_error (l_calls Q) i = Some P0) by (rewrite EQ, nth_error_app1 by lia; exact EP0).
    destruct (C4 i c0 P0 Ec1 EP1) as [Hc HL]. split; [|exact HL].
    apply (lem_acall_keep (ablocks B ly S) _ rd); [exact Hc| |].
    * intros x Hx. apply K; unfold in_rec, A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
    * intros pn Hpn. apply KQ. rewrite EL. apply in_or_app; left. apply in_concat. exists P0.
      split; [eapply nth_error_In; exact EP0|exact Hpn].
  + destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
    * rewrite nth_error_app2, Nat.sub_diag in Ec0 by lia. cbn in Ec0. injection Ec0 as <-.
      rewrite nth_error_app2 in EP0 by lia. rewrite HLc, Nat.sub_diag in EP0. cbn in EP0. injection EP0 as <-.
      split; [|cbn [snd]; apply Forall_app; split; [exact HLA|constructor; [exact HLs|constructor]]].
      apply (lem_acall_snoc (ablocks B ly S) _ rd); try assumption.
      -- intros x Hx Hx1 Hx2. apply K; [unfold in_rec, A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia|exact Hx1|exact Hx2].
      -- intros pn Hpn. apply KQ. rewrite EL. apply in_or_app; right; apply in_or_app; left; exact Hpn.
      -- intros H. apply Hfr'. rewrite EL, !map_app. apply in_or_app; right; apply in_or_app; left; exact H.
    * exfalso. assert (E : nth_error (r_calls R ++ [(REC_ADD, A ++ [s])]) i = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia). congruence.
- (* the spill arm *)
  assert (Heq : length (r_calls R) = 16%nat).
  { destruct HA as (_ & _ & _ & (C1 & _) & _). unfold rec_record in C1.
    rewrite (proj2 (Nat.ltb_ge _ _) Hge) in C1. cbn [r_calls set_spill] in C1. lia. }
  assert (Ec : sa_c R = A_REC_SPILL).
  { unfold sa_c. rewrite (proj2 (Nat.ltb_ge _ _) Hge). reflexivity. }
  rewrite Ec in K, Hna, Harg.
  rewrite (rec_record_spill R REC_ADD A Heq) in HA. rewrite (rec_record_spill R REC_ADD (A ++ [s]) Heq).
  destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). cbn [r_calls r_spill set_spill snd] in C1, C2, C3, C4, C5, C6.
  assert (EL : lay_blocks Q = concat (l_calls Q) ++ l_spill Q ++ (oblk (l_answer Q) ++ oblk (l_reply Q)))
    by reflexivity.
  assert (EL' : lay_blocks (RLay (l_calls Q) (l_spill Q ++ [(p, n)]) (l_answer Q) (l_reply Q)) =
    concat (l_calls Q) ++ (l_spill Q ++ [(p, n)]) ++ (oblk (l_answer Q) ++ oblk (l_reply Q))) by reflexivity.
  destruct (lem_own_mem O Q _ _ _ _ p n HO EL EL' HW Hfr' Hap1 Hap2) as [HW' HO'].
  exists (RLay (l_calls Q) (l_spill Q ++ [(p, n)]) (l_answer Q) (l_reply Q)). split; [|exact HO'].
  destruct (lem_tail_keep (ablocks B ly S) (ablocks B ly' S') rd rd' (set_spill R (REC_ADD, A)) Q HAn HRp HX)
    as (T1 & T2 & T3).
  { intros x Hx. apply K;
      unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, OFF_ANSWER in *; lia. }
  { exact KQ. }
  refine (conj Hg8 (conj Hs8 (conj Hap (conj _ (conj T1 (conj T2 (conj T3 HW'))))))).
  unfold ag1_calls. cbn [r_calls r_spill set_spill l_calls l_spill snd].
  refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
  + apply (lem_aval_keep rd _ _ _ _ (A_G_REC + OFF_NCALLS) (A_G_REC + OFF_NCALLS + 4)); [exact C3|lia|lia|].
    intros x Hx. apply K;
      unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
  + intros i c0 P0 Ec0 EP0. destruct (C4 i c0 P0 Ec0 EP0) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec0; discriminate).
    apply (lem_acall_keep (ablocks B ly S) _ rd); [exact Hc| |].
    * intros x Hx. apply K;
        unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
    * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; left. apply in_concat. exists P0.
      split; [eapply nth_error_In; exact EP0|exact Hpn].
  + apply (lem_acall_snoc (ablocks B ly S) _ rd); try assumption.
    * intros x Hx Hx1 Hx2. apply K; [unfold in_rec, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia|exact Hx1|exact Hx2].
    * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hpn.
    * intros H. apply Hfr'. rewrite EL, !map_app. apply in_or_app; right; apply in_or_app; left; exact H.
  + apply Forall_app. split; [exact C6|constructor; [exact HLs|constructor]].
Qed.
(* g_rec.state := h *)
Lemma rec_repA_set_state : forall ly S rd (rd' : reader) R O h,
  rec_repA B ly S rd R O ->
  (forall a, in_rec a -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
  rec_repA B ly S rd' (set_state R h) O.
Proof.
intros ly S rd rd' R O h (Q & HA & HO) K KB Hs Hh.
exists Q. split; [|exact HO].
apply (lem_arep_state (ablocks B ly S) _ rd); [exact HA|exact K| |exact Hs|exact Hh].
apply (lem_O_kept O (lay_blocks Q) (ablocks B ly S) rd rd' HO KB).
intros pn Hpn. apply HO in Hpn. exact (proj1 (lem_lay_in _ _ _ _ _ _ HA pn Hpn)).
Qed.
(* the call record() made, as mix_call's statement asks it *)
Lemma rec_repA_last_call : forall ly S rd R A O,
  rec_repA B ly S rd (rec_record R REC_ADD A) O ->
  exists P, acall_at (ablocks B ly S) rd (sa_c R) (REC_ADD, A) P /\ (forall pn, In pn P -> In pn O).
Proof.
intros ly S rd R A O (Q & HA & HO).
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
- rewrite (rec_record_calls R REC_ADD A Hlt) in HA.
  destruct HA as (_ & _ & _ & HC & _). destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  cbn [r_calls set_calls] in C1, C2, C3, C4.
  assert (Ec : sa_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
  { unfold sa_c. rewrite (proj2 (Nat.ltb_lt _ _) Hlt). reflexivity. }
  rewrite Ec.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP;
    [|exfalso; apply nth_error_None in EP; rewrite C2, length_app in EP; cbn [length] in EP; lia].
  assert (Ex : nth_error (r_calls R ++ [(REC_ADD, A)]) (length (r_calls R)) = Some (REC_ADD, A))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  exists P. split; [exact (proj1 (C4 _ _ _ Ex EP))|].
  intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app; left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact EP|exact Hpn].
- unfold rec_record in HA. rewrite (proj2 (Nat.ltb_ge _ _) Hge) in HA.
  destruct HA as (_ & _ & _ & HC & _). destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  cbn [r_spill set_spill] in C5.
  assert (Ec : sa_c R = A_REC_SPILL).
  { unfold sa_c. rewrite (proj2 (Nat.ltb_ge _ _) Hge). reflexivity. }
  rewrite Ec. exists (l_spill Q). split; [exact C5|].
  intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hpn.
Qed.
(* the scalar fields and the answer word *)
Lemma rec_repA_fields : forall ly S rd R O,
  rec_repA B ly S rd R O ->
  aval_mem rd (A_G_REC + OFF_REFUSE) 4 (r_refuse R) /\ -2 ^ 31 <= r_refuse R < 2 ^ 31 /\
  aval_mem rd (A_G_REC + OFF_STATE) 8 (r_state R) /\ 0 <= r_state R < 2 ^ 64 /\
  aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))) /\ (length (r_calls R) <= 16)%nat /\
  (exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists n, In (old, n) O)) /\
  (forall p n m, In (p, n) O -> In (p, m) O -> n = m) /\
  (forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn /\
     iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE).
Proof.
intros ly S rd R O (Q & HA & HO).
pose proof (lem_lay_in _ _ _ _ _ _ HA) as HL.
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10). destruct HW as [W1 W2].
refine (conj X1 (conj X6 (conj X4 (conj X9 (conj C3 (conj C1 (conj _ (conj _ _)))))))).
- revert HAn. unfold aanswer_at. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [[q m]|] eqn:Eq;
  intros HAn; try contradiction.
  + exists q. split; [exact (proj1 HAn)|]. right. exists m. apply HO. unfold lay_blocks. rewrite Eq.
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; left. left; reflexivity.
  + exists 0. split; [exact HAn|left; reflexivity].
- intros p n m H1 H2. apply HO in H1, H2. exact (lem_fst_unique _ p n m W1 H1 H2).
- intros pn Hpn. apply HO in Hpn. destruct (HL pn Hpn) as [G1 G2]. destruct (W2 pn Hpn) as [G3 G4].
  exact (conj G1 (conj G2 (conj G3 G4))).
Qed.

(* ---- read-only facts along the journal ---- *)
(* a byte of a live block is off the image *)
Lemma lem_blk_off : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> a < 0x10000 \/ 0x606000 <= a.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Ha)))))
  as [Hz _].
pose proof (pa_img_cover ly S md (proj1 (proj2 HAR))) as [C1 C2].
unfold in_zr in Hz. lia.
Qed.

(* the uri at the entry (sa_uri: Some u in a live block apart from the recorder's) as astr_argA's block arm *)
Lemma sa_uri_argA : forall ly S (W : world SEGS) mem md O pu uri (ro : Z -> Prop), AR SEGS B ly S W mem md ->
  sa_uri B ly S (rdW W mem) O pu uri -> exists u, uri = Some u /\ astr_argA B ly S (rdW W mem) ro O pu (Some u).
Proof.
intros ly S W mem md O pu uri ro HAR HU. destruct uri as [u|]; [|destruct HU].
exists u. split; [reflexivity|].
destruct HU as (Hblk & Hap & Hstr & Hn). pose proof Hblk as (b & kk & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS ly S W mem md b kk HAR Hbin) as (_ & H4 & _).
unfold astr_argA. cbv beta iota zeta.
refine (conj _ (conj Hstr (conj Hn (or_introl (conj Hblk Hap))))). lia.
Qed.

(* ---- the image facts (CmdRecFacts.v's cmd_img_facts fields and lemmas, by exact from IMG) ---- *)
Section e2.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.

Lemma lem_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs|exact Hr] | exact (cif_relro_img a Hr)]. Qed.
Lemma sa_aro_kept : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O HAR HJ HREP HR a Hro Ho He.
pose proof (rec_repA_fields ly S (rdW W mem) R O HREP) as (_ & _ & _ & _ & _ & _ & _ & _ & HOb).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (lem_ro_img a Hro) as Himg.
pose proof (pa_img_range a Himg) as Hrng.
rewrite (F3 a Himg Ho He); [exact (HR a Hro Ho He)|].
apply fp_spares_closed.
- unfold sa_FP.
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_NCALLS; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_CALLS; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_STATE; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_REC_SPILL; lia|].
  apply sink_closed_ablocks_fp. apply Forall_forall. intros [q m] Hqm.
  destruct (HOb (q, m) Hqm) as (Hin & _).
  destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & H4 & _). cbn [fst]. lia.
- unfold sa_FP. intros H.
  apply inFP_cons in H as [H|H]; [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; left; unfold A_G_REC, OFF_NCALLS in *; lia|exact Hro]|].
  apply inFP_cons in H as [H|H]; [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; left; unfold A_G_REC, OFF_CALLS, OFF_ANSWER in *; lia|exact Hro]|].
  apply inFP_cons in H as [H|H]; [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; left; unfold A_G_REC, OFF_STATE in *; lia|exact Hro]|].
  apply inFP_cons in H as [H|H];
    [apply (cif_prog_not_ro a); [unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left; unfold A_REC_SPILL, SC_SIZE in *; lia|exact Hro]|].
  destruct H as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
  cbn [fst snd] in Hr1, Hr2. destruct (HOb (q, m) Hqm) as (Hin & _).
  pose proof (lem_blk_off ly S W mem md q m a HAR Hin ltac:(lia)) as Hoff. lia.
Qed.
(* the read-only view rt_rom_view (RtDefs.v:145): every byte of a read-only segment is in in_roP's first arm *)
Lemma sa_rom_view : forall (W : world SEGS) mem,
  arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof using Type.
intros W mem HR a Ha Ho He. apply HR; [left; exact Ha | exact Ho | exact He].
Qed.

(* ---- the string arguments at the call of xstrdup ---- *)
(* a string the caller handed over (astr_argA at the entry), at a later state of the walk: xstrdup's string premise
   (xstrdup_c.v:76-79), left arm, and its word tail; the read-only arm's record checks hold at every state *)
Lemma sa_str_ready : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O p x,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
  astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x) /\
  atail_vis SEGS Wc memc (p + Z.of_nat (length x)).
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k R O p x HAR HJ HREP HR0 HS HR1 HLIVE.
pose proof (rec_repA_fields ly S (rdW W mem) R O HREP) as (_ & _ & _ & _ & _ & _ & _ & _ & HOb).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct HS as (Hp0 & Hstr & Hn & [(Hblk & Hap) | (Hro & Hca & Hch & Hend)]).
- (* in a live block apart from the recorder's *)
  destruct Hblk as (b & kk & Hbin & Hb1 & Hb2).
  assert (Hnot : ~ In (b, kk) O).
  { intros H. pose proof (proj1 (Forall_forall _ _) Hap (b, kk) H) as Hiv. cbn [fst snd] in Hiv.
    unfold iv_apart in Hiv. lia. }
  pose proof (HLIVE (b, kk) Hbin Hnot) as HL1.
  assert (Hkk : req_size kk = kk) by (apply lem_req_pos; lia).
  assert (KP : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW Wc memc (p + i) = rdW W mem (p + i)).
  { intros i Hi. replace (p + i) with (b + (p + i - b)) by lia.
    apply (F2 b kk (p + i - b) Hbin HL1); [rewrite Hkk; lia|].
    replace (b + (p + i - b)) with (p + i) by lia.
    pose proof (lem_blk_off lyc Sc Wc memc mdc b kk (p + i) HARc HL1 ltac:(rewrite Hkk; lia)) as Hoff.
    unfold sa_FP. intros H.
    apply inFP_cons in H as [H|H]; [unfold A_G_REC, OFF_NCALLS in H; lia|].
    apply inFP_cons in H as [H|H]; [unfold A_G_REC, OFF_CALLS, OFF_ANSWER in H; lia|].
    apply inFP_cons in H as [H|H]; [unfold A_G_REC, OFF_STATE in H; lia|].
    apply inFP_cons in H as [H|H]; [unfold A_REC_SPILL, SC_SIZE in H; lia|].
    destruct H as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
    cbn [fst snd] in Hr1, Hr2. destruct (HOb (q, m) Hqm) as (_ & Hm & _).
    rewrite (lem_req_pos m Hm) in Hr2.
    pose proof (proj1 (Forall_forall _ _) Hap (q, m) Hqm) as Hiv. cbn [fst snd] in Hiv. unfold iv_apart in Hiv. lia. }
  split.
  + unfold astr_argA. cbv beta iota zeta.
    refine (conj Hp0 (conj (lem_astr_keep _ _ _ _ Hstr KP) (conj Hn (or_introl (conj _ (Forall_nil _)))))).
    exact (ex_intro _ b (ex_intro _ kk (conj HL1 (conj Hb1 Hb2)))).
  + apply (cmd_heap_tail_vis lyc Sc Wc memc mdc b kk); [exact HARc|exact HL1|rewrite Hkk; lia].
- (* read-only: the bytes are the image's at both states; the record's checks hold at every state *)
  assert (KP : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW Wc memc (p + i) = rdW W mem (p + i)).
  { intros i Hi. destruct (Hro i Hi) as (H1 & H2 & H3). rewrite (HR1 _ H1 H2 H3), (HR0 _ H1 H2 H3). reflexivity. }
  split.
  + unfold astr_argA. cbv beta iota zeta.
    exact (conj Hp0 (conj (lem_astr_keep _ _ _ _ Hstr KP) (conj Hn (or_intror (conj Hro (conj Hca (conj Hch Hend))))))).
  + exact (cmd_tail_vis_at lyc Sc Wc memc mdc _ HARc Hend).
Qed.

(* the image's shadow bytes the allocator record names: a registered object's own shadow cells, and the
   zero-shadow ranges *)
Lemma lem_shcell : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
  AF0x.cell_lookup Tfib_const_shadow (ANum a) = Some (z1 (ANum a) v) -> 0 <= v < 256 ->
  rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR E Hv.
pose proof (am_const B ly S _ (proj1 HAR)) as HC. rewrite (ts_const B HB ly) in HC.
assert (Hin : In (z1 (ANum a) v) (Tfib_const ly)).
{ unfold Tfib_const. apply in_or_app; right; apply in_or_app; right. exact (AF0x.cell_lookup_In _ _ _ E). }
assert (H0 : rdW W mem (a + Z.of_nat 0) = Some (le_byte v 1 0))
  by exact (proj1 (Forall_forall _ _) HC _ Hin 0%nat (Nat.lt_0_succ 0)).
rewrite Z.add_0_r in H0. rewrite H0. f_equal. unfold le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256.
rewrite (Z.mod_small (v mod 256) 256) by (apply Z.mod_pos_bound; lia). rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma lem_zsh : forall ly S (W : world SEGS) mem md r s, AR SEGS B ly S W mem md ->
  In r Tfib_zero_shadow -> fst r mod 8 = 0 -> fst r <= 8 * (s - SHADOW_OFF) -> 8 * (s - SHADOW_OFF) + 8 <= fst r + snd r ->
  rdW W mem s = Some 0.
Proof.
intros ly S W mem md r s HAR Hin H1 H2 H3.
pose proof (cmd_zshadow_sub SEGS B LAWS HB ly S W mem md r (8 * (s - SHADOW_OFF)) 8 HAR Hin H1
  ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia) H2 H3
  0 ltac:(rewrite Z.div_same by lia; lia)) as Z0.
unfold shadow_of_addr in Z0.
replace (SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8 + 0) with s in Z0 by (rewrite Z.mul_comm, Z.div_mul by lia; lia).
exact Z0.
Qed.
Definition lem_zvisb (s : Z) : bool :=
  existsb (fun r => (fst r mod 8 =? 0) && (fst r <=? 8 * (s - SHADOW_OFF)) && (8 * (s - SHADOW_OFF) + 8 <=? fst r + snd r))
    Tfib_zero_shadow.
Definition lem_visb (s : Z) : bool :=
  match AF0x.cell_lookup Tfib_const_shadow (ANum s) with
  | Some (ACell (ANum s') 1 (AV (ANum v))) => (s' =? s) && (0 <=? v) && (v <? 256)
  | _ => lem_zvisb s
  end.
Lemma lem_zvis : forall ly S (W : world SEGS) mem md s, AR SEGS B ly S W mem md -> lem_zvisb s = true ->
  rdW W mem s <> None.
Proof.
intros ly S W mem md s HAR H. unfold lem_zvisb in H. apply existsb_exists in H as (r & Hr & Hb).
apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
rewrite (lem_zsh ly S W mem md r s HAR Hr H1 H2 H3). discriminate.
Qed.
Lemma lem_visb_ok : forall ly S (W : world SEGS) mem md s, AR SEGS B ly S W mem md -> lem_visb s = true ->
  rdW W mem s <> None.
Proof.
intros ly S W mem md s HAR H. unfold lem_visb in H.
destruct (AF0x.cell_lookup Tfib_const_shadow (ANum s)) as [[ca cw cv]|] eqn:E; [|exact (lem_zvis ly S W mem md s HAR H)].
destruct ca as [s'| | | | | | | | | | | | | | | | | |]; try exact (lem_zvis ly S W mem md s HAR H).
destruct cw as [|[|cw]]; try exact (lem_zvis ly S W mem md s HAR H).
destruct cv as [e|mask v]; try exact (lem_zvis ly S W mem md s HAR H).
destruct e as [v| | | | | | | | | | | | | | | | | |]; try exact (lem_zvis ly S W mem md s HAR H).
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst s'.
rewrite (lem_shcell ly S W mem md s v HAR E ltac:(lia)). discriminate.
Qed.
Lemma lem_word_vis : forall ly S (W : world SEGS) mem md s0, AR SEGS B ly S W mem md ->
  forallb (fun i => lem_visb (s0 + Z.of_nat i)) (seq 0 8) = true ->
  forall i, 0 <= i < 8 -> rdW W mem (s0 + i) <> None.
Proof.
intros ly S W mem md s0 HAR H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
exact (lem_visb_ok ly S W mem md _ HAR H).
Qed.
(* a literal of the image: the read-only arm of astr_argA, whose record checks are computed *)
Lemma lem_lit : forall ly S (W : world SEGS) mem md p x n,
  AR SEGS B ly S W mem md -> n = Z.of_nat (length x) + 1 ->
  abytes_atR (rdW W mem) p (x ++ [Z_to_bv 8 0]) ->
  forallb (fun b => negb (bv_unsigned b =? 0)) x = true ->
  (forall i, 0 <= i < n -> in_roP SEGS RLO RHI (p + i)) ->
  forallb (fun r => (p + n <=? fst r) || (fst r + snd r <=? p)) Tfib_owned_static = true ->
  p + n <= TFIB_ERRNO -> p <> 0 -> n < 8 ->
  cmd_addr_b p n = true -> cmd_hull_b p n = true -> In (p + Z.of_nat (length x)) cmd_ro_ends ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some x) /\ atail_vis SEGS W mem (p + Z.of_nat (length x)).
Proof.
intros ly S W mem md p x n HAR En Hby Hno Hro How Herr Hp0 H8 Ha Hh He. subst n.
split; [|exact (cmd_tail_vis_at ly S W mem md _ HAR He)].
unfold astr_argA. cbv beta iota zeta.
refine (conj Hp0 (conj (conj Hby (lem_no0 x Hno)) (conj _ (or_intror (conj _ (conj Ha (conj Hh He))))))).
- unfold LMAX. lia.
- intros i Hi. refine (conj (Hro i Hi) (conj _ _)).
  + rewrite (ts_owned B HB). exact (lem_unowned _ p (p + (Z.of_nat (length x) + 1)) How (p + i) ltac:(lia)).
  + rewrite (ts_errno B HB). lia.
Qed.
(* picks the conjunct of H that is the goal *)
Ltac lem_pick H :=
  match goal with |- ?G =>
    let rec go h :=
      lazymatch type of h with
      | G /\ _ => exact (proj1 h)
      | _ /\ _ => go constr:(proj2 h)
      | G => exact h
      end in
    go H
  end.
(* sup_add's own defaults "(null)" (0x22480, .str.47) and "-" (0x21d40, .str.3), at any state *)
Lemma sa_lit_ready : forall ly S (W : world SEGS) mem md p x,
  AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
  (p, x) = (0x22480, bstr "(null)"%string) \/ (p, x) = (0x21d40, bstr "-"%string) ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some x) /\
  atail_vis SEGS W mem (p + Z.of_nat (length x)).
Proof.
intros ly S W mem md p x HAR [Hby _] Hpx.
pose proof cmd_ro_in_img as Hin.
unfold cmd_ro_bytes in Hby. unfold cmd_ro_in in Hin.
destruct Hpx as [E|E]; injection E as -> ->.
- apply (lem_lit ly S W mem md 0x22480 (bstr "(null)"%string) 7 HAR).
  + vm_compute. reflexivity.
  + change (bstr "(null)"%string ++ [Z_to_bv 8 0]) with RO_lit_22480. lem_pick Hby.
  + vm_compute. reflexivity.
  + lem_pick Hin.
  + vm_compute. reflexivity.
  + unfold TFIB_ERRNO. lia.
  + lia.
  + lia.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + apply lem_in_z; vm_compute; reflexivity.
- apply (lem_lit ly S W mem md 0x21d40 (bstr "-"%string) 2 HAR).
  + vm_compute. reflexivity.
  + change (bstr "-"%string ++ [Z_to_bv 8 0]) with RO_lit_21d40. lem_pick Hby.
  + vm_compute. reflexivity.
  + lem_pick Hin.
  + vm_compute. reflexivity.
  + unfold TFIB_ERRNO. lia.
  + lia.
  + lia.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + apply lem_in_z; vm_compute; reflexivity.
Qed.
End e2.

(* ---- the frame chain at a call: sup_add's frame record (ra at sp0 - 8, the caller's s0 at sp0 - 16) ---- *)
Lemma sa_achain : forall ly S W (regs : bvmap 5 word) mem md ch R O own lyc Sc Wc memc mdc k,
  afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch ->
  rec_repA B ly S (rdW W mem) R O ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  sa_frame (rdW Wc memc) (spZ regs) regs ->
  exists ch1, achain lyc (rdW Wc memc) (sa_s1 (spZ regs)) (spZ regs) ch1.
Proof.
intros ly S W regs mem md ch R O own lyc Sc Wc memc mdc k HPRE HREP HJ HFR.
pose proof HPRE as (HAR & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _ & Htop1 & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof (rec_repA_fields ly S (rdW W mem) R O HREP) as (_ & _ & _ & _ & _ & _ & _ & _ & HOb).
pose proof asan_consts as (AC1 & _).
assert (Etop : ly_top lyc = ly_top ly) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt|Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) (raZ regs) ch (sa_s1 (spZ regs))).
  + exact Hch.
  + lia.
  + intros a Ha. apply F1; [lia|lia|].
    unfold sa_FP. intros H.
    apply inFP_cons in H as [H|H]; [unfold A_G_REC, OFF_NCALLS in H; lia|].
    apply inFP_cons in H as [H|H]; [unfold A_G_REC, OFF_CALLS, OFF_ANSWER in H; lia|].
    apply inFP_cons in H as [H|H]; [unfold A_G_REC, OFF_STATE in H; lia|].
    apply inFP_cons in H as [H|H]; [unfold A_REC_SPILL, SC_SIZE in H; lia|].
    destruct H as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
    cbn [fst snd] in Hr1, Hr2. destruct (HOb (q, m) Hqm) as (Hin & _).
    destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & _ & Hc & _). lia.
  + pose proof (HFR 0%nat 1 eq_refl) as H0. replace (spZ regs - 8 - 8 * Z.of_nat 0) with (spZ regs - 8) in H0 by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hb. unfold bv_modulus in Hb. cbn [Z.of_N] in Hb.
    apply lem_rdword_aval; [exact H0|unfold raZ; lia].
  + pose proof (HFR 1%nat 8 eq_refl) as H1. replace (spZ regs - 8 - 8 * Z.of_nat 1) with (spZ regs - 16) in H1 by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hb. unfold bv_modulus in Hb. cbn [Z.of_N] in Hb.
    apply lem_rdword_aval; [exact H1|unfold s0Z; lia].
  + exact Hra4.
  + lia.
  + Z.div_mod_to_equations. lia.
  + exact Hlt.
  + unfold sa_s1. pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)). lia.
- exists []. left. split; [right; left; rewrite Etop; lia|reflexivity].
Qed.
End e.
End f.
End d.
