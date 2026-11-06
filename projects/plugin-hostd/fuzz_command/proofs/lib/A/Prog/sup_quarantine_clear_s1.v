(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reset (plugin-hostd/fuzz_command, entry 0x8b6d8, 91
   instructions), copied from earlier versions of lib/A/Prog/sup_quarantine_clear_s1.v .. _s3.v (one commit, and a
   later one for the entry segment srs_SA: sup_reset's listing is sup_quarantine_clear's
   instruction for instruction, with FN 10 for 11 and the verb .str.8 0x21dc0 for .str.9 0x21e00, both 16 bytes),
   from lib/A/Prog/sup_worker_list.v and RecBTemplate.v (the
   recorder template), from an earlier version of lib/A/Prog/sup_instance_info.v (the walk of record()'s
   two arms to the join), and from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. AChc.v (the segment walk of
   cgif_close: a seed per segment, paj_run_tok steps, cl_callS at each program call). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reset.v; 91 of its 356 lines of code are new or changed and 2521 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the recorder's model steps for the ASan walk of sup_quarantine_clear
   (plugin-hostd/fuzz_command), after lib/Prog/RecStep.v (rec_rep_record_lt :63, rep_at_record_full :395,
   rep_at_arg_lt :487, rep_at_arg_full :582) over lib/A/Prog/CmdRep.v's reader form. *)

(* The recorder's representation (lib/A/Prog/CmdRep.v arep_at / rec_repA) across the inlined record(FN) and one
   inlined arg_s of the recording functions of recorder.c:379-569: the slot of g_rec's call table (or record.spill
   when the table is full) gets the function, one argument count and one argument pointer, and the argument block
   joins the recorder's own blocks. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot record() fills: the next entry of g_rec's call table, or record.spill when the table holds 16 calls
   (recorder.c:205-221) *)
Definition sqc_slot (R : rstate) : Z :=
  if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
  else A_REC_SPILL.

(* helpers: the reader forms of lib/A/Prog/CmdRep.v read only the bytes they name *)
Lemma sqc_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma sqc_aval_eq : forall rd a b n v, aval_mem rd a n v -> a = b -> aval_mem rd b n v.
Proof. intros rd a b n v H E. subst b. exact H. Qed.

Lemma sqc_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma sqc_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (sqc_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma sqc_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (sqc_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (sqc_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (sqc_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (sqc_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma sqc_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (sqc_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (sqc_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (sqc_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma sqc_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H KA KP.
  destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
    unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
    + apply (sqc_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sqc_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (sqc_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (sqc_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sqc_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma sqc_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (sqc_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma sqc_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma sqc_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma sqc_in_answer : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H.
Qed.

Lemma sqc_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* every block of the recorder has a positive size *)
Lemma sqc_call_blocks : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ 0 < snd pn.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
Qed.

Lemma sqc_blocks_pos : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> 0 < snd pn.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & _ & _) Hin.
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn).
    destruct (In_nth_error _ _ HP') as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (C4 i c P Ec Ei) as [Hc _]. exact (proj2 (sqc_call_blocks _ _ _ _ _ _ Hc Hpn)).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (proj2 (sqc_call_blocks _ _ _ _ _ _ C5 Hin))|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [qn|];
        cbn [aanswer_at oblk In]; intros HA Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & _ & N4 & _). lia.
    + revert HP Hin. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [qn|];
        cbn [areply_at oblk In]; intros HP Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & P4 & _ & P6 & _).
      destruct x as [|b x]; [exfalso; apply P4; reflexivity|]. cbn [length] in P6. lia.
Qed.

Lemma sqc_fresh : forall bl rd gr sc R Q (O : list (Z * Z)) p n, arep_at bl rd gr sc R Q ->
  (forall qn, In qn O <-> In qn (lay_blocks Q)) -> 0 < n ->
  Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O -> ~ In p (map fst (lay_blocks Q)).
Proof.
  intros bl rd gr sc R Q O p n HR HO Hn HF Hq. apply in_map_iff in Hq as (qn & E & Hq).
  pose proof (sqc_blocks_pos _ _ _ _ _ _ _ HR Hq) as Hpos. apply HO in Hq.
  rewrite Forall_forall in HF. specialize (HF qn Hq). cbv beta in HF. unfold iv_apart in HF. lia.
Qed.

Lemma sqc_nodup_add : forall (l l' : list (Z * Z)) pn, Permutation l' (pn :: l) -> NoDup (map fst l) ->
  ~ In (fst pn) (map fst l) -> NoDup (map fst l').
Proof.
  intros l l' pn HP H Hn. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  apply (Permutation_NoDup (Permutation_map fst (Permutation_sym HP))). cbn [map]. constructor; assumption.
Qed.

Lemma sqc_nodup1 : forall pn : Z * Z, NoDup (map fst [pn]).
Proof.
  intros pn. apply (sqc_nodup_add [] [pn] pn); [apply Permutation_refl | cbn [map]; constructor | cbn; intros []].
Qed.

Lemma sqc_lay_slot : forall Q pn,
  Permutation (lay_blocks (RLay (l_calls Q ++ [[pn]]) (l_spill Q) (l_answer Q) (l_reply Q))) (pn :: lay_blocks Q).
Proof.
  intros Q pn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma sqc_lay_spill : forall Q pn, l_spill Q = [] ->
  Permutation (lay_blocks (RLay (l_calls Q) [pn] (l_answer Q) (l_reply Q))) (pn :: lay_blocks Q).
Proof.
  intros Q pn E. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite E. cbn [app].
  apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma sqc_O_perm : forall (O L L' : list (Z * Z)) pn, Permutation L' (pn :: L) ->
  (forall qn, In qn O <-> In qn L) -> forall qn, In qn (pn :: O) <-> In qn L'.
Proof.
  intros O L L' pn HP HO qn. split.
  - intros Hq. apply (Permutation_in _ (Permutation_sym HP)).
    destruct Hq as [<-|Hq]; [left; reflexivity | right; apply HO; exact Hq].
  - intros Hq. apply (Permutation_in _ HP) in Hq.
    destruct Hq as [<-|Hq]; [left; reflexivity | right; apply HO; exact Hq].
Qed.

Lemma sqc_own_add : forall gr sc Q Q' pn, Permutation (lay_blocks Q') (pn :: lay_blocks Q) ->
  ag1_own gr sc Q -> ~ In (fst pn) (map fst (lay_blocks Q)) ->
  iv_apart (fst pn) (snd pn) gr REC_SIZE -> iv_apart (fst pn) (snd pn) sc SC_SIZE -> ag1_own gr sc Q'.
Proof.
  intros gr sc Q Q' pn HP [HND HAP] Hfr H1 H2. split.
  - exact (sqc_nodup_add _ _ pn HP HND Hfr).
  - intros qn Hq. apply (Permutation_in _ HP) in Hq.
    destruct Hq as [<-|Hq]; [split; assumption | exact (HAP qn Hq)].
Qed.

Lemma sqc_call_new : forall bl rd a fn s p, 0 <= fn < REC_FN_COUNT -> Z.of_nat (length s) <= LMAX ->
  aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 1 ->
  aval_mem rd (a + CALL_OFF_ARGS) 8 p ->
  p <> 0 -> In (p, Z.of_nat (length s) + 1) bl -> astr_atR rd p s ->
  acall_at bl rd a (fn, [s]) [(p, Z.of_nat (length s) + 1)].
Proof.
  intros bl rd a fn s p Hfn Hls BF BA BP Hp0 Hin Hs. unfold acall_at. cbn [fst snd length].
  split; [exact Hfn|]. split; [lia|]. split; [reflexivity|]. split; [exact BF|]. split; [exact BA|].
  split; [apply sqc_nodup1|].
  intros k s' pn Es Ep.
  assert (Hk : (k < length [s])%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. cbn in Es, Ep. injection Es as <-. injection Ep as <-.
  cbn [fst snd]. split; [apply (sqc_aval_eq _ _ _ _ _ BP); lia|].
  split; [exact Hp0|]. split; [exact Hin|]. split; [lia | exact Hs].
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma sqc_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE) \/ (sc <= a < sc + SC_SIZE) \/
             (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW) KL K.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
             forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
  { intros pn Hpn. split; [exact (KL pn Hpn)|]. intros x Hx. apply K. right. right. exists pn.
    split; [exact Hpn | exact Hx]. }
  assert (KR : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; left; exact Hx).
  unfold REC_SIZE, SC_SIZE in KR, KS.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj _ (conj _ (conj _ HW))))))).
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (sqc_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (sqc_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (sqc_in_calls Q i P pn EP Hpn).
    + apply (sqc_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply sqc_in_spill. exact Hpn.
  - apply (sqc_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply sqc_in_answer. exact Hpn.
  - apply (sqc_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply sqc_in_reply. exact Hpn.
  - apply (sqc_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

Section d.
Variable B : asyms.

Lemma sqc_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (sqc_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* record(fn) and one arg_s: the slot holds fn, one argument, the argument's copy p; the argument block joins the
   recorder's own blocks. On the spill arm (16 calls) record() has already freed the spill's arguments. *)
Lemma sqc_rec_repA_record1 : forall ly S rd ly1 S1 rd1 R O fn s p,
  rec_repA B ly S rd R O ->
  (length (r_calls R) = 16%nat -> snd (r_spill R) = []) ->
  0 <= fn < REC_FN_COUNT ->
  Z.of_nat (length s) <= LMAX ->
  aval_mem rd1 (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record R fn [s])))) ->
  aval_mem rd1 (sqc_slot R + CALL_OFF_FN) 4 fn ->
  aval_mem rd1 (sqc_slot R + CALL_OFF_NARGS) 4 1 ->
  aval_mem rd1 (sqc_slot R + CALL_OFF_ARGS) 8 p ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (sqc_slot R <= a < sqc_slot R + 16) ->
     rd1 a = rd a) ->
  (forall pn i, In pn O -> 0 <= i < snd pn -> rd1 (fst pn + i) = rd (fst pn + i)) ->
  (forall pn, In pn O -> In pn (ablocks B ly1 S1)) ->
  In (p, Z.of_nat (length s) + 1) (ablocks B ly1 S1) ->
  Forall (fun qk => iv_apart p (Z.of_nat (length s) + 1) (fst qk) (snd qk)) O ->
  iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
  iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
  p <> 0 -> astr_atR rd1 p s ->
  rec_repA B ly1 S1 rd1 (rec_record R fn [s]) ((p, Z.of_nat (length s) + 1) :: O).
Proof.
  intros ly S rd ly1 S1 rd1 R O fn s p (Q & HR & HO) Hsp Hfn Hls BN BF BA BP KG KB KO Hin HF Ha1 Ha2 Hp0 Hs.
  assert (Hn0 : 0 < Z.of_nat (length s) + 1) by lia.
  pose proof (sqc_fresh _ _ _ _ _ _ _ _ _ HR HO Hn0 HF) as Hfr.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly1 S1) /\
             forall x, fst pn <= x < fst pn + snd pn -> rd1 x = rd x).
  { intros pn Hpn. apply HO in Hpn. split; [exact (KO pn Hpn)|].
    intros x Hx. replace x with (fst pn + (x - fst pn)) by lia. apply KB; [exact Hpn | lia]. }
  pose proof HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW).
  assert (GS : A_G_REC + REC_SIZE <= A_REC_SPILL) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE; lia).
  assert (SL : (A_G_REC + OFF_CALLS <= sqc_slot R /\ sqc_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/
               sqc_slot R = A_REC_SPILL).
  { unfold sqc_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L];
      [left; unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER; lia | right; reflexivity]. }
  assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd1 x = rd x).
  { intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; lia. }
  assert (RA : aanswer_at (ablocks B ly1 S1) rd1 A_G_REC (r_answer R) (l_answer Q)).
  { apply (sqc_answer_keep (ablocks B ly S) _ rd); [exact HA | |].
    - intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    - intros pn Hpn. apply KQ. apply sqc_in_answer. exact Hpn. }
  assert (RP : areply_at (ablocks B ly1 S1) rd1 A_G_REC (r_reply R) (l_reply Q)).
  { apply (sqc_reply_keep (ablocks B ly S) _ rd); [exact HP | |].
    - intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    - intros pn Hpn. apply KQ. apply sqc_in_reply. exact Hpn. }
  assert (RX : ag1_scalars rd1 A_G_REC R).
  { apply (sqc_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia. }
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
  - (* the slot arm: entry length (r_calls R) of g_rec's call table *)
    assert (ES : sqc_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
    { unfold sqc_slot. rewrite (proj2 (Nat.ltb_lt _ _) Hn). reflexivity. }
    rewrite ES in BF, BA, BP, KG. clear SL.
    rewrite (rec_record_calls R fn [s] Hn) in BN |- *.
    pose proof (sqc_lay_slot Q (p, Z.of_nat (length s) + 1)) as PERM.
    unfold rec_repA.
    exists (RLay (l_calls Q ++ [[(p, Z.of_nat (length s) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
    split; [|exact (sqc_O_perm O (lay_blocks Q) _ _ PERM HO)].
    unfold arep_at, ag1_calls.
    cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
    refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX _))))))).
    + refine (conj _ (conj _ (conj BN (conj _ (conj _ C6))))).
      * rewrite length_app. cbn [length]. lia.
      * rewrite !length_app, C2. reflexivity.
      * intros i c P Ec EP.
        destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
        -- rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
           destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
           apply (sqc_call_keep (ablocks B ly S) _ rd); [exact Hc | |].
           ++ intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
           ++ intros pn Hpn. apply KQ. exact (sqc_in_calls Q i P pn EP Hpn).
        -- destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
           ++ rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
              rewrite nth_error_app2, C2, Nat.sub_diag in EP by lia. cbn in EP. injection EP as <-.
              split; [exact (sqc_call_new _ _ _ fn s p Hfn Hls BF BA BP Hp0 Hin Hs)|].
              cbn [snd]. constructor; [exact Hls | constructor].
           ++ exfalso. assert (N : nth_error (r_calls R ++ [(fn, [s])]) i = None)
                by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
              rewrite N in Ec. discriminate.
      * apply (sqc_call_keep (ablocks B ly S) _ rd); [exact C5 | |].
        -- intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. apply sqc_in_spill. exact Hpn.
    + exact (sqc_own_add _ _ Q _ (p, Z.of_nat (length s) + 1) PERM HW Hfr Ha1 Ha2).
  - (* the spill arm: record.spill, whose arguments record() has already freed *)
    assert (H16 : length (r_calls R) = 16%nat) by lia.
    assert (ES : sqc_slot R = A_REC_SPILL) by (unfold sqc_slot; rewrite H16; reflexivity).
    rewrite ES in BF, BA, BP, KG. clear SL.
    rewrite (rec_record_spill R fn [s] H16) in BN |- *.
    assert (LS : l_spill Q = []).
    { pose proof C5 as (_ & _ & L & _). rewrite (Hsp H16) in L. apply length_zero_iff_nil. exact L. }
    pose proof (sqc_lay_spill Q (p, Z.of_nat (length s) + 1) LS) as PERM.
    unfold rec_repA.
    exists (RLay (l_calls Q) [(p, Z.of_nat (length s) + 1)] (l_answer Q) (l_reply Q)).
    split; [|exact (sqc_O_perm O (lay_blocks Q) _ _ PERM HO)].
    unfold arep_at, ag1_calls.
    cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply fst snd].
    refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX _))))))).
    + refine (conj C1 (conj C2 (conj BN (conj _ (conj _ _))))).
      * intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
        assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
        apply (sqc_call_keep (ablocks B ly S) _ rd); [exact Hc | |].
        -- intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. exact (sqc_in_calls Q i P pn EP Hpn).
      * exact (sqc_call_new _ _ _ fn s p Hfn Hls BF BA BP Hp0 Hin Hs).
      * constructor; [exact Hls | constructor].
    + exact (sqc_own_add _ _ Q _ (p, Z.of_nat (length s) + 1) PERM HW Hfr Ha1 Ha2).
Qed.
End d.

(* the spill arm: record() of the full table after rec_calls_free emptied the spill *)
Lemma sqc_rec_record_set_spill : forall R x fn A, length (r_calls R) = 16%nat ->
  rec_record (set_spill R x) fn A = rec_record R fn A.
Proof.
  intros R x fn A H. rewrite (rec_record_spill R fn A H). rewrite rec_record_spill by exact H. reflexivity.
Qed.
