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
Definition srs_slot (R : rstate) : Z :=
  if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
  else A_REC_SPILL.

(* helpers: the reader forms of lib/A/Prog/CmdRep.v read only the bytes they name *)
Lemma srs_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma srs_aval_eq : forall rd a b n v, aval_mem rd a n v -> a = b -> aval_mem rd b n v.
Proof. intros rd a b n v H E. subst b. exact H. Qed.

Lemma srs_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma srs_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (srs_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma srs_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (srs_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (srs_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (srs_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (srs_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma srs_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (srs_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (srs_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (srs_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma srs_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
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
    + apply (srs_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (srs_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (srs_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (srs_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (srs_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma srs_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (srs_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma srs_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma srs_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma srs_in_answer : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H.
Qed.

Lemma srs_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* every block of the recorder has a positive size *)
Lemma srs_call_blocks : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ 0 < snd pn.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
Qed.

Lemma srs_blocks_pos : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> 0 < snd pn.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & _ & _) Hin.
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn).
    destruct (In_nth_error _ _ HP') as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (C4 i c P Ec Ei) as [Hc _]. exact (proj2 (srs_call_blocks _ _ _ _ _ _ Hc Hpn)).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (proj2 (srs_call_blocks _ _ _ _ _ _ C5 Hin))|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [qn|];
        cbn [aanswer_at oblk In]; intros HA Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & _ & N4 & _). lia.
    + revert HP Hin. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [qn|];
        cbn [areply_at oblk In]; intros HP Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & P4 & _ & P6 & _).
      destruct x as [|b x]; [exfalso; apply P4; reflexivity|]. cbn [length] in P6. lia.
Qed.

Lemma srs_fresh : forall bl rd gr sc R Q (O : list (Z * Z)) p n, arep_at bl rd gr sc R Q ->
  (forall qn, In qn O <-> In qn (lay_blocks Q)) -> 0 < n ->
  Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O -> ~ In p (map fst (lay_blocks Q)).
Proof.
  intros bl rd gr sc R Q O p n HR HO Hn HF Hq. apply in_map_iff in Hq as (qn & E & Hq).
  pose proof (srs_blocks_pos _ _ _ _ _ _ _ HR Hq) as Hpos. apply HO in Hq.
  rewrite Forall_forall in HF. specialize (HF qn Hq). cbv beta in HF. unfold iv_apart in HF. lia.
Qed.

Lemma srs_nodup_add : forall (l l' : list (Z * Z)) pn, Permutation l' (pn :: l) -> NoDup (map fst l) ->
  ~ In (fst pn) (map fst l) -> NoDup (map fst l').
Proof.
  intros l l' pn HP H Hn. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  apply (Permutation_NoDup (Permutation_map fst (Permutation_sym HP))). cbn [map]. constructor; assumption.
Qed.

Lemma srs_nodup1 : forall pn : Z * Z, NoDup (map fst [pn]).
Proof.
  intros pn. apply (srs_nodup_add [] [pn] pn); [apply Permutation_refl | cbn [map]; constructor | cbn; intros []].
Qed.

Lemma srs_lay_slot : forall Q pn,
  Permutation (lay_blocks (RLay (l_calls Q ++ [[pn]]) (l_spill Q) (l_answer Q) (l_reply Q))) (pn :: lay_blocks Q).
Proof.
  intros Q pn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma srs_lay_spill : forall Q pn, l_spill Q = [] ->
  Permutation (lay_blocks (RLay (l_calls Q) [pn] (l_answer Q) (l_reply Q))) (pn :: lay_blocks Q).
Proof.
  intros Q pn E. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite E. cbn [app].
  apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma srs_O_perm : forall (O L L' : list (Z * Z)) pn, Permutation L' (pn :: L) ->
  (forall qn, In qn O <-> In qn L) -> forall qn, In qn (pn :: O) <-> In qn L'.
Proof.
  intros O L L' pn HP HO qn. split.
  - intros Hq. apply (Permutation_in _ (Permutation_sym HP)).
    destruct Hq as [<-|Hq]; [left; reflexivity | right; apply HO; exact Hq].
  - intros Hq. apply (Permutation_in _ HP) in Hq.
    destruct Hq as [<-|Hq]; [left; reflexivity | right; apply HO; exact Hq].
Qed.

Lemma srs_own_add : forall gr sc Q Q' pn, Permutation (lay_blocks Q') (pn :: lay_blocks Q) ->
  ag1_own gr sc Q -> ~ In (fst pn) (map fst (lay_blocks Q)) ->
  iv_apart (fst pn) (snd pn) gr REC_SIZE -> iv_apart (fst pn) (snd pn) sc SC_SIZE -> ag1_own gr sc Q'.
Proof.
  intros gr sc Q Q' pn HP [HND HAP] Hfr H1 H2. split.
  - exact (srs_nodup_add _ _ pn HP HND Hfr).
  - intros qn Hq. apply (Permutation_in _ HP) in Hq.
    destruct Hq as [<-|Hq]; [split; assumption | exact (HAP qn Hq)].
Qed.

Lemma srs_call_new : forall bl rd a fn s p, 0 <= fn < REC_FN_COUNT -> Z.of_nat (length s) <= LMAX ->
  aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 1 ->
  aval_mem rd (a + CALL_OFF_ARGS) 8 p ->
  p <> 0 -> In (p, Z.of_nat (length s) + 1) bl -> astr_atR rd p s ->
  acall_at bl rd a (fn, [s]) [(p, Z.of_nat (length s) + 1)].
Proof.
  intros bl rd a fn s p Hfn Hls BF BA BP Hp0 Hin Hs. unfold acall_at. cbn [fst snd length].
  split; [exact Hfn|]. split; [lia|]. split; [reflexivity|]. split; [exact BF|]. split; [exact BA|].
  split; [apply srs_nodup1|].
  intros k s' pn Es Ep.
  assert (Hk : (k < length [s])%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. cbn in Es, Ep. injection Es as <-. injection Ep as <-.
  cbn [fst snd]. split; [apply (srs_aval_eq _ _ _ _ _ BP); lia|].
  split; [exact Hp0|]. split; [exact Hin|]. split; [lia | exact Hs].
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma srs_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
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
    + apply (srs_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (srs_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (srs_in_calls Q i P pn EP Hpn).
    + apply (srs_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply srs_in_spill. exact Hpn.
  - apply (srs_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply srs_in_answer. exact Hpn.
  - apply (srs_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply srs_in_reply. exact Hpn.
  - apply (srs_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

Section d.
Variable B : asyms.

Lemma srs_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (srs_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* record(fn) and one arg_s: the slot holds fn, one argument, the argument's copy p; the argument block joins the
   recorder's own blocks. On the spill arm (16 calls) record() has already freed the spill's arguments. *)
Lemma srs_rec_repA_record1 : forall ly S rd ly1 S1 rd1 R O fn s p,
  rec_repA B ly S rd R O ->
  (length (r_calls R) = 16%nat -> snd (r_spill R) = []) ->
  0 <= fn < REC_FN_COUNT ->
  Z.of_nat (length s) <= LMAX ->
  aval_mem rd1 (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record R fn [s])))) ->
  aval_mem rd1 (srs_slot R + CALL_OFF_FN) 4 fn ->
  aval_mem rd1 (srs_slot R + CALL_OFF_NARGS) 4 1 ->
  aval_mem rd1 (srs_slot R + CALL_OFF_ARGS) 8 p ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (srs_slot R <= a < srs_slot R + 16) ->
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
  pose proof (srs_fresh _ _ _ _ _ _ _ _ _ HR HO Hn0 HF) as Hfr.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly1 S1) /\
             forall x, fst pn <= x < fst pn + snd pn -> rd1 x = rd x).
  { intros pn Hpn. apply HO in Hpn. split; [exact (KO pn Hpn)|].
    intros x Hx. replace x with (fst pn + (x - fst pn)) by lia. apply KB; [exact Hpn | lia]. }
  pose proof HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW).
  assert (GS : A_G_REC + REC_SIZE <= A_REC_SPILL) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE; lia).
  assert (SL : (A_G_REC + OFF_CALLS <= srs_slot R /\ srs_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/
               srs_slot R = A_REC_SPILL).
  { unfold srs_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L];
      [left; unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER; lia | right; reflexivity]. }
  assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd1 x = rd x).
  { intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, OFF_ANSWER in *; lia. }
  assert (RA : aanswer_at (ablocks B ly1 S1) rd1 A_G_REC (r_answer R) (l_answer Q)).
  { apply (srs_answer_keep (ablocks B ly S) _ rd); [exact HA | |].
    - intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    - intros pn Hpn. apply KQ. apply srs_in_answer. exact Hpn. }
  assert (RP : areply_at (ablocks B ly1 S1) rd1 A_G_REC (r_reply R) (l_reply Q)).
  { apply (srs_reply_keep (ablocks B ly S) _ rd); [exact HP | |].
    - intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    - intros pn Hpn. apply KQ. apply srs_in_reply. exact Hpn. }
  assert (RX : ag1_scalars rd1 A_G_REC R).
  { apply (srs_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia. }
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
  - (* the slot arm: entry length (r_calls R) of g_rec's call table *)
    assert (ES : srs_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
    { unfold srs_slot. rewrite (proj2 (Nat.ltb_lt _ _) Hn). reflexivity. }
    rewrite ES in BF, BA, BP, KG. clear SL.
    rewrite (rec_record_calls R fn [s] Hn) in BN |- *.
    pose proof (srs_lay_slot Q (p, Z.of_nat (length s) + 1)) as PERM.
    unfold rec_repA.
    exists (RLay (l_calls Q ++ [[(p, Z.of_nat (length s) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
    split; [|exact (srs_O_perm O (lay_blocks Q) _ _ PERM HO)].
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
           apply (srs_call_keep (ablocks B ly S) _ rd); [exact Hc | |].
           ++ intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
           ++ intros pn Hpn. apply KQ. exact (srs_in_calls Q i P pn EP Hpn).
        -- destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
           ++ rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
              rewrite nth_error_app2, C2, Nat.sub_diag in EP by lia. cbn in EP. injection EP as <-.
              split; [exact (srs_call_new _ _ _ fn s p Hfn Hls BF BA BP Hp0 Hin Hs)|].
              cbn [snd]. constructor; [exact Hls | constructor].
           ++ exfalso. assert (N : nth_error (r_calls R ++ [(fn, [s])]) i = None)
                by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
              rewrite N in Ec. discriminate.
      * apply (srs_call_keep (ablocks B ly S) _ rd); [exact C5 | |].
        -- intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. apply srs_in_spill. exact Hpn.
    + exact (srs_own_add _ _ Q _ (p, Z.of_nat (length s) + 1) PERM HW Hfr Ha1 Ha2).
  - (* the spill arm: record.spill, whose arguments record() has already freed *)
    assert (H16 : length (r_calls R) = 16%nat) by lia.
    assert (ES : srs_slot R = A_REC_SPILL) by (unfold srs_slot; rewrite H16; reflexivity).
    rewrite ES in BF, BA, BP, KG. clear SL.
    rewrite (rec_record_spill R fn [s] H16) in BN |- *.
    assert (LS : l_spill Q = []).
    { pose proof C5 as (_ & _ & L & _). rewrite (Hsp H16) in L. apply length_zero_iff_nil. exact L. }
    pose proof (srs_lay_spill Q (p, Z.of_nat (length s) + 1) LS) as PERM.
    unfold rec_repA.
    exists (RLay (l_calls Q) [(p, Z.of_nat (length s) + 1)] (l_answer Q) (l_reply Q)).
    split; [|exact (srs_O_perm O (lay_blocks Q) _ _ PERM HO)].
    unfold arep_at, ag1_calls.
    cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply fst snd].
    refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX _))))))).
    + refine (conj C1 (conj C2 (conj BN (conj _ (conj _ _))))).
      * intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
        assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
        apply (srs_call_keep (ablocks B ly S) _ rd); [exact Hc | |].
        -- intros x Hx. apply KG; unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. exact (srs_in_calls Q i P pn EP Hpn).
      * exact (srs_call_new _ _ _ fn s p Hfn Hls BF BA BP Hp0 Hin Hs).
      * constructor; [exact Hls | constructor].
    + exact (srs_own_add _ _ Q _ (p, Z.of_nat (length s) + 1) PERM HW Hfr Ha1 Ha2).
Qed.
End d.

(* the spill arm: record() of the full table after rec_calls_free emptied the spill *)
Lemma srs_rec_record_set_spill : forall R x fn A, length (r_calls R) = 16%nat ->
  rec_record (set_spill R x) fn A = rec_record R fn A.
Proof.
  intros R x fn A H. rewrite (rec_record_spill R fn A H). rewrite rec_record_spill by exact H. reflexivity.
Qed.

(* sup_reset (recorder.c:403-409, entry BASE + AF_sup_reset = 0x8b6d8, 91 instructions):
   the symbolic states its walk starts from. Atoms above the 32 registers: 32 the shadow base, 33 the call count
   g_rec.ncalls had at the entry, 34 the slot record() fills (g_rec.calls[n], or record.spill when n = 16), 35..40
   the entry values of ra, s0, s1, s2, s3, s4, which the 48-byte frame holds. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
(* recb_PG, the program's writable statics as as_prog_static lists them (base, length) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the walk's points in the listing *)
Definition SRS_E : Z := AF_sup_reset.
Definition SRS_RETR : Z := AF_sup_reset + 0x54.  (* after the call of rec_calls_free (0x8b72c) *)
Definition SRS_JOIN : Z := AF_sup_reset + 0x74.  (* the two arms of record() meet (0x8b74c) *)
Definition SRS_RETX : Z := AF_sup_reset + 0xb8.  (* after the call of xstrdup (0x8b790) *)
Definition SRS_RETS : Z := AF_sup_reset + 0xfc.  (* after the call of rec_shape_of (0x8b7d4) *)
Definition SRS_FRAME : Z := 48.
(* the function the call records (REC_RESET, the `li a0,10` before the store to c->fn) *)
Definition SRS_FN : Z := 10.

(* atoms *)
Definition SRS_SB : nat := 32.
Definition SRS_N : nat := 33.
Definition SRS_C : nat := 34.
Definition srs_saved : list Z := [1; 8; 9; 18; 19; 20].
Definition srs_extra (regs0 : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs0 (Z_to_bv 5 r)) srs_saved.
Definition srs_Bx : sv := SOff SRS_SB 0.
Definition srs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition srs_SH : list shent := [mkSHE SRS_C 0 CALL_SIZE].
(* the listing's object atoms: g_rec, record.spill *)
Definition SRS_GREC : nat := A_OBJ 44.
Definition SRS_SPILL : nat := A_OBJ 51.
Definition srs_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SRS_SB, mkAF SB SB 0); (SRS_N, mkAF 0 16 0);
         (SRS_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (SRS_GREC, mkAF A_G_REC A_G_REC 3); (SRS_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].

(* regions: the frame at the entry (written by the prologue), g_rec.ncalls, the frame after the prologue (it holds
   the entry's ra, s0..s4), and the slot *)
Definition srs_stack0 : YP09.region := YP09.mkRegion (Some 2%nat) (- SRS_FRAME) 0 (- SRS_FRAME) 0 [].
Definition srs_ncalls : YP09.region :=
YP09.mkRegion (Some SRS_GREC) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff SRS_N 0))].
Definition srs_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 SRS_FRAME 0 0
  (map (fun j => YP09.mkChunk (40 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 6)).
(* the slot: its 56 bytes, of which the walk writes fn, nargs and args[0] (the first 16) *)
Definition srs_slotR (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some SRS_C) 0 CALL_SIZE 0 16 cs.

Definition srs_ssA : sstate :=
mkSS SRS_E sr_atoms [srs_stack0; got_regionP; bcell_regionP SRS_SB; srs_ncalls] None srs_facts.
(* at the join: s0 the slot, s3 the shadow base *)
Definition srs_regsC : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 8 (SOff SRS_C 0)) 19 (SOff SRS_SB 0).
Definition srs_ssC (pc : Z) : sstate := mkSS pc srs_regsC [srs_frame; srs_slotR []] None srs_facts.

(* the slot record() picked: an entry of g_rec's table, or record.spill *)
Definition srs_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.
(* the zero-shadow ranges of the record that hold g_rec and record.spill (AF0m.v:4649, :4650) *)
Definition SRS_ZSH_REC : Z * Z := (0xada00, 0x5e3b00 - 0xada00).
Definition SRS_ZSH_SPILL : Z * Z := (0x5e3be0, 0x5e3c18 - 0x5e3be0).

Lemma srs_slot_bounds : forall c, srs_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL).
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
[split; [lia | split; [exact H3 | left; lia]] | split; [lia | split; [reflexivity | right; reflexivity]]].
Qed.

Lemma srs_in_PG_slot : forall c a, srs_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. destruct (srs_slot_bounds c Hc) as (Hb & _ & [Hh | ->]).
- apply recb_grec_in. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- apply recb_spill_in. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the 48-byte frame holds the entry's ra, s0, s1, s2, s3, s4 at sp1 + 40, 32, 24, 16, 8, 0 *)
Definition srs_frame_at (m : word -> option byte) (sp1 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error srs_saved j = Some r ->
val_mem SEGS m (sp1 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* every atom of the walk's environment: the registers of the current state, then the extra atoms *)
Definition srs_E (regs1 regs0 : bvmap 5 word) (n c : Z) : env := Eimg (Ereg regs1 (srs_extra regs0 n c)).

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma srs_grec_val : VAL SRS_GREC = A_G_REC.
Proof. unfold SRS_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma srs_spill_val : VAL SRS_SPILL = A_REC_SPILL.
Proof. unfold SRS_SPILL. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma srs_zsh_rec_in : In SRS_ZSH_REC Tfib_zero_shadow.
Proof. unfold SRS_ZSH_REC, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.

Lemma srs_zsh_spill_in : In SRS_ZSH_SPILL Tfib_zero_shadow.
Proof. unfold SRS_ZSH_SPILL, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.

Lemma srs_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> srs_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(H1 & H2 & _) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md SRS_ZSH_REC c CALL_SIZE HAR srs_zsh_rec_in);
  unfold SRS_ZSH_REC; cbn [fst snd]; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; first [reflexivity | lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md SRS_ZSH_SPILL A_REC_SPILL CALL_SIZE HAR srs_zsh_spill_in);
  unfold SRS_ZSH_SPILL; cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; first [reflexivity | lia].
Qed.

Lemma srs_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma srs_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma srs_E_reg : forall regs1 regs0 n c k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (srs_E regs1 regs0 n c) k = getr regs1 r.
Proof.
intros regs1 regs0 n c k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold srs_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.

Lemma srs_E_extra : forall regs1 regs0 n c j, (j < 9)%nat ->
ew (srs_E regs1 regs0 n c) (32 + j) = nth j (srs_extra regs0 n c) (Z_to_bv 64 0).
Proof.
intros regs1 regs0 n c j Hj. unfold srs_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma srs_E_extra_at : forall regs1 regs0 n c k, (32 <= k < 41)%nat ->
ew (srs_E regs1 regs0 n c) k = nth (k - 32) (srs_extra regs0 n c) (Z_to_bv 64 0).
Proof.
intros regs1 regs0 n c k Hk. replace k with (32 + (k - 32))%nat at 1 by lia. apply srs_E_extra. lia.
Qed.

Lemma srs_E_img : forall regs1 regs0 n c, img_env VAL A_LIM (srs_E regs1 regs0 n c).
Proof. intros. unfold srs_E. apply Eimg_env. Qed.

Lemma srs_E_grec : forall regs1 regs0 n c, ew (srs_E regs1 regs0 n c) SRS_GREC = Z_to_bv 64 A_G_REC.
Proof.
intros. rewrite (img_env_atomP (srs_E regs1 regs0 n c) SRS_GREC (srs_E_img regs1 regs0 n c)
  ltac:(unfold SRS_GREC, A_OBJ, A_TEXT, A_LIM; lia)), srs_grec_val. reflexivity.
Qed.

Lemma srs_E_spill : forall regs1 regs0 n c, ew (srs_E regs1 regs0 n c) SRS_SPILL = Z_to_bv 64 A_REC_SPILL.
Proof.
intros. rewrite (img_env_atomP (srs_E regs1 regs0 n c) SRS_SPILL (srs_E_img regs1 regs0 n c)
  ltac:(unfold SRS_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), srs_spill_val. reflexivity.
Qed.

Lemma srs_facts_ok : forall regs1 regs0 n c,
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 -> bv_unsigned (getr regs1 2) mod 16 = 0 -> 0 <= n <= 16 -> srs_slot_ok c ->
facts_ok (srs_E regs1 regs0 n c) srs_facts.
Proof.
intros regs1 regs0 n c Hsp Hsp16 Hn Hc.
destruct (srs_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (E := srs_E regs1 regs0 n c).
assert (E2 : ew E 2 = Z_to_bv 64 (bv_unsigned (getr regs1 2))) by (subst E; rewrite (srs_E_reg _ _ _ _ 2 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
assert (ESB : ew E SRS_SB = Z_to_bv 64 SB) by (subst E; exact (srs_E_extra regs1 regs0 n c 0 ltac:(lia))).
assert (EN : ew E SRS_N = Z_to_bv 64 n) by (subst E; exact (srs_E_extra regs1 regs0 n c 1 ltac:(lia))).
assert (EC : ew E SRS_C = Z_to_bv 64 c) by (subst E; exact (srs_E_extra regs1 regs0 n c 2 ltac:(lia))).
pose proof (srs_E_grec regs1 regs0 n c) as EG. pose proof (srs_E_spill regs1 regs0 n c) as ES. fold E in EG, ES.
unfold facts_ok, srs_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
- apply (srs_afact E 2%nat (bv_unsigned (getr regs1 2))); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
- apply (srs_afact E SRS_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (srs_afact E SRS_N n); [exact EN | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
- apply (srs_afact E SRS_C c); [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hcb
  | change (2 ^ 3) with 8; exact Hc8 | lia].
- apply (srs_afact E SRS_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia
  | change (2 ^ 3) with 8; unfold A_G_REC; reflexivity | lia].
- apply (srs_afact E SRS_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia
  | change (2 ^ 3) with 8; unfold A_REC_SPILL; reflexivity | lia].
Qed.

Lemma srs_sh_ok : forall ly S W mem md regs1 regs0 n c,
AR SEGS B ly S W mem md -> srs_slot_ok c ->
sh_ok SEGS srs_Bx srs_SH (srs_E regs1 regs0 n c) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 regs0 n c HAR Hc.
destruct (srs_slot_bounds c Hc) as (Hcb & Hc8 & _).
assert (ESB : ew (srs_E regs1 regs0 n c) SRS_SB = Z_to_bv 64 SB) by exact (srs_E_extra regs1 regs0 n c 0 ltac:(lia)).
assert (EC : ew (srs_E regs1 regs0 n c) SRS_C = Z_to_bv 64 c) by exact (srs_E_extra regs1 regs0 n c 2 ltac:(lia)).
unfold sh_ok, srs_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem (srs_E regs1 regs0 n c) srs_Bx SRS_C c CALL_SIZE c 0 CALL_SIZE).
- exact (srs_slot_addressable ly S W mem md c HAR Hc).
- unfold srs_Bx. apply srs_U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply srs_U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* the seed of a walk segment after the prologue: the frame (its saved registers) and the slot *)
Lemma srs_seed : forall pc sregs cs W1 (regs1 regs0 : bvmap 5 word) mem1 ly1 S1 md1 n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 - SRS_FRAME -> bv_unsigned (getr regs1 2) mod 16 = 0 ->
0 <= n <= 16 -> srs_slot_ok c ->
regs_ok (srs_E regs1 regs0 n c) sregs regs1 ->
srs_frame_at (mrestrict (w_H W1) mem1) (bv_unsigned (getr regs1 2)) regs0 ->
regions_wf [srs_frame; srs_slotR cs] = true ->
Forall (YP09.chunk_ok SEGS (srs_E regs1 regs0 n c) (mrestrict (w_H W1) mem1) c) cs ->
st_ok_pi SEGS VAL (srs_E regs1 regs0 n c) (mkSS pc sregs [srs_frame; srs_slotR cs] None srs_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS srs_Bx srs_SH (srs_E regs1 regs0 n c) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs cs W1 regs1 regs0 mem1 ly1 S1 md1 n c HAR Hsp Hsp16 Hn Hc HREG HFR Hwf HCS.
destruct (srs_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (sp1 := bv_unsigned (getr regs1 2)) in *.
set (E := srs_E regs1 regs0 n c) in *.
assert (E2 : bv_unsigned (ew E 2) = sp1) by (subst E sp1; rewrite (srs_E_reg _ _ _ _ 2 2%bv eq_refl); reflexivity).
assert (EC : ew E SRS_C = Z_to_bv 64 c) by (subst E; exact (srs_E_extra regs1 regs0 n c 2 ltac:(lia))).
assert (UC : bv_unsigned (ew E SRS_C) = c) by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split; [| exact (srs_sh_ok ly1 S1 W1 mem1 md1 regs1 regs0 n c HAR Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- exact Hwf.
- unfold srs_frame, srs_slotR. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. unfold SRS_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
    let j := eval compute in (k - 35)%nat in let r := eval compute in (nth j srs_saved 0) in
    apply (chunk_ok_val SEGS E _ sp1 off 8 (SOff k 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r))));
    [ cbn [sv_denot]; rewrite Z.add_0_r; subst E;
      rewrite (srs_E_extra_at regs1 regs0 n c k ltac:(lia)); cbn [Nat.sub nth srs_extra srs_saved map app];
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; cbn; lia
    | cbn; lia
    | replace (sp1 + off) with (sp1 + 40 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
  + rewrite UC. split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_REC_SPILL, CALL_SIZE in *; lia|].
    split; [| exact HCS].
    intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1 _ HAR). apply (srs_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia].
- apply pairwise_disjoint_of_extents. unfold srs_frame, srs_slotR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, UC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SRS_FRAME, CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
- apply (srs_facts_ok regs1 regs0 n c); [unfold SRS_FRAME in Hsp; fold sp1; lia | exact Hsp16 | exact Hn | exact Hc].
Qed.

(* the seed at the entry: the frame the prologue writes, the two words of the shadow base, and g_rec.ncalls *)
Lemma srs_seed_entry : forall W (regs : bvmap 5 word) mem ly S md n c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - SRS_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 -> srs_slot_ok c ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (srs_E regs regs n c) srs_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SRS_E)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md n c HAR Hsp Hsp16 Hpres Hn Hc HNC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := srs_E regs regs n c).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (srs_E_reg _ _ _ _ 2 2%bv eq_refl); reflexivity).
assert (ESB : ew E SRS_SB = Z_to_bv 64 SB) by (subst E; exact (srs_E_extra regs regs n c 0 ltac:(lia))).
assert (EN : ew E SRS_N = Z_to_bv 64 n) by (subst E; exact (srs_E_extra regs regs n c 1 ltac:(lia))).
assert (EG : ew E SRS_GREC = Z_to_bv 64 A_G_REC) by (subst E; apply srs_E_grec).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold srs_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold srs_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold srs_ssA. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- subst E. unfold srs_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold srs_stack0, got_regionP, bcell_regionP, srs_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. unfold SRS_FRAME in *. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 srs_Bx SB);
    [cbn [sv_denot srs_Bx]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB SRS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply recb_grec_in.
      unfold OFF_NCALLS, REC_SIZE in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff SRS_N 0) n);
    [cbn [sv_denot]; rewrite EN, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | zside | zside | exact HNC].
- apply pairwise_disjoint_of_extents.
  unfold srs_stack0, got_regionP, bcell_regionP, srs_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB SRS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SRS_FRAME, A_G_REC, OFF_NCALLS in *.
  rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)).
  let v0 := eval vm_compute in (nth 0 cmd_objs 0) in change (nth 0 cmd_objs 0) with v0.
  let v12 := eval vm_compute in (nth 12 cmd_objs 0) in change (nth 12 cmd_objs 0) with v12.
  repeat split; lia.
- exact (srs_facts_ok regs regs n c ltac:(unfold spZ in Hsp; lia) Hsp16 Hn Hc).
Qed.

End e.
End f.
End d.

(* sup_reset (recorder.c:403-409; BASE + AF_sup_reset = 0x8b6d8, 91 instructions):
   - the entry segment: the 48-byte frame, the shadow base (the word at the GOT cell 0xa63f0), g_rec.ncalls; if the
     table holds 16 calls, record.spill is the slot and rec_calls_free(spill, 1) frees its arguments (0x8b728),
     else g_rec.ncalls := n + 1 and the slot is g_rec.calls[n];
   - from the join (0x8b74c): two inline checks (the 4-byte stores of c->fn := 10 and c->nargs := 0: a load of the
     shadow byte at (c >> 3) + 0x7fff8000 and a compare, whose error path is not reached because the slot lies in
     g_rec or record.spill, which the record marks usable), the default "(null)" for a NULL argument, the call of
     xstrdup (0x8b78c);
   - after it: two more checks (the load of c->nargs and the 8-byte store of c->args[0]), c->nargs := 1,
     c->args[0] := the copy, the call of rec_shape_of("supervisor_reset", 16) (0x8b7d0);
   - after it: the frame is released and the function tail-jumps to answer(c, shape, 1) (0x8b7fc), which runs at
     this function's entry stack pointer and returns to its caller. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c mix_call_c hand_back_c answer_c sup_reset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas .
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecRo CmdRecRest.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition SRS_STK : Z := SUP_RESET_STK.
Lemma SRS_STK_val : SRS_STK = 16592.
Proof. reflexivity. Qed.
(* the bytes the call may write outside its frame: g_rec, record.spill, the recorder's blocks *)
Definition srs_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the default argument "(null)" (.str.47, 0x22480) and the verb "supervisor_reset" (.str.8, 0x21dc0) *)
Definition srs_null : list byte := bstr "(null)"%string.
Definition srs_verb : list byte := bstr "supervisor_reset"%string.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees (sup_reset_c.v:67-70) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the premise a statement revision deleted from every statement, carried as ONE named hypothesis by every walk
   that hands an image literal to astr_argA's read-only arm (decided 2026-10-29): in_roP's relro
   arm cannot give it, since CMD_RLO = 0xa5740 lies above the literals *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI).
(* the walk hypotheses, with cgif's names *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the program's statics (the recorder walks' shared names, RecBTemplate.v forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the per-binary record facts (one name and form for every walk; CmdRecFacts.v is to prove each): the
   read-only bytes the program loads are those of the image wherever
   arodata_okP holds, arodata_okP survives every journal whose footprint is off the read-only range (CmdBase.v's
   arodata_ok_journalP with RRO), and the read-only range is image bytes outside the program's statics *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the image facts of the binary (the kit's CmdRecBase.cmd_img_facts; RecBClosed closes it by cmd_img_facts_tfib):
   the relro range lies in the image (CmdRecRo.RELRO_IMG) *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the statement's post (sup_reset_c.v:100-119) word for word *)
Definition srs_Q (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z)) (which : option (list byte))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_reset_m R which = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESET R which /\
 mo_le MT S S' (XM_SUP_RESET MT R which).

(* the statement's premises (sup_reset_c.v:74-95) word for word *)
Definition srs_pre ly S W (regs : bvmap 5 word) mem md ch (pw : Z) (which : option (list byte)) (R : rstate)
  (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SRS_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
0 <= pw < 2 ^ 64 /\
getr regs 10 = w64 pw /\
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw which /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_RESET R <= EV_MAX /\
blocks_bytes S + LIVE_SUP_RESET R which <= LIVE_MAX /\
mo_ok MT S (XM_SUP_RESET MT R which) /\
(forall x, which = Some x -> atail_vis SEGS W mem (pw + Z.of_nat (length x))).

(* the walk's statement: the statement with G1 (the post's freshness conjunct) and G2 (the premise) *)
Definition tsrs_spec_g : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pw : Z) (which : option (list byte)) (R : rstate) (O : list (Z * Z)),
srs_pre ly S W regs mem md ch pw which R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_reset) regs mem md)
(apost_baseF SEGS B SRS_STK (srs_FP O) regs ly S W mem md (EV_SUP_RESET R) (srs_Q ly S R O which)).


(* ---------- the walk's invariant between its segments ---------- *)

(* the journal from the entry, the frame, and the recorder's state at a base point (the entry, or after record()'s
   rec_calls_free on the spill arm), with the blocks the walk freed so far (F, the spill's arguments) *)
Definition srs_mid ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
  lyc Sc (Wc : world SEGS) memc mdc (k : Z) lyB SBa (WB : world SEGS) memB (R0 : rstate) (O0 F : list (Z * Z)) : Prop :=
ajournal SEGS B SRS_STK (spZ regs) (srs_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
k = Z.of_nat (length F) /\
srs_frame_at (mrestrict (w_H Wc) memc) (spZ regs - SRS_FRAME) regs /\
rec_repA B lyB SBa (rdW WB memB) R0 O0 /\
(length (r_calls R0) = 16%nat -> snd (r_spill R0) = []) /\
length (r_calls R0) = length (r_calls R) /\
(forall A, rec_record R0 SRS_FN A = rec_record R SRS_FN A) /\
(forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc memc (fst pn + i) = rdW WB memB (fst pn + i)) /\
(forall pn, In pn O0 -> In pn (ablocks B lyc Sc)) /\
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) /\
(forall pn, In pn F -> In pn O) /\
(forall pn, In pn O0 <-> In pn O /\ ~ In pn F) /\
Z.of_nat (length F) = rec_spill_frees R /\
mo_le MT S Sc (Z.of_nat (length F) * mo_free MT).

(* g_rec and record.spill equal the base's, but for g_rec.ncalls and the first x bytes of the slot c *)
Definition srs_recmem (rd rdB : reader) (c x : Z) : Prop :=
forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + x) -> rd a = rdB a.

Definition srs_ncalls_ok (rd : reader) (R0 : rstate) : Prop :=
aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record R0 SRS_FN [[]])))).

(* ---------- small facts ---------- *)

Lemma srs_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma srs_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. intros i Hi.
rewrite (Hk (Z.of_nat i)) by (rewrite length_app in Hi; cbn [length] in Hi; lia). exact (H1 i Hi).
Qed.

Lemma srs_alu_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma srs_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. symmetry. apply unsigned_lit_small. lia.
Qed.

(* s4 after the prologue's checks: the shadow byte's address of c->nargs *)
Definition srs_shx4 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff SRS_C 4) (SLit 3)) (SOff SRS_SB 0).
Lemma srs_shx4_denot : forall E c, ew E SRS_C = Z_to_bv 64 c -> ew E SRS_SB = Z_to_bv 64 SB -> 0 <= c < 2 ^ 40 ->
sv_denot E srs_shx4 = Z_to_bv 64 (SB + (c + 4) / 8).
Proof.
intros E c Hc Hsb Hr. unfold srs_shx4. cbn [sv_denot]. rewrite Hc, Hsb.
rewrite !unsigned_lit_small by (unfold SB; lia). rewrite Z.add_0_r.
rewrite srs_srl3 by lia. rewrite srs_alu_add. f_equal. lia.
Qed.

Definition srs_regsD : list sv := Eval vm_compute in sr_set (sr_set srs_regsC 18 (SOff SRS_C 4)) 20 srs_shx4.

Lemma srs_slot_ok_of : forall R0, (length (r_calls R0) <= 16)%nat -> srs_slot_ok (srs_slot R0).
Proof.
intros R0 H. unfold srs_slot. destruct (Nat.ltb_spec (length (r_calls R0)) 16) as [L|L].
- left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
  rewrite Z.add_mod by lia. replace (56 * Z.of_nat (length (r_calls R0))) with (8 * (7 * Z.of_nat (length (r_calls R0)))) by lia.
  rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- right. reflexivity.
Qed.

(* ---------- the footprint, the read-only range, the program's statics ---------- *)

Lemma srs_inFP_cases : forall O a, inFP (srs_FP O) a ->
Exists (in_zr a) recb_PG \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold srs_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply recb_grec_in. exact Ha.
- left. apply recb_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

(* arodata_okP along the walk's journal: the walk's footprint (g_rec, record.spill, the recorder's blocks) is off
   the read-only range *)
Lemma srs_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B SRS_STK sp (srs_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp HAR HO HJ HR.
apply (arodata_ok_journalP SEGS RLO RHI (CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG) (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact HR].
intros a Hro Hfp. destruct (srs_inFP_cases O a Hfp) as [HP | (b & n & Hin & Ha)].
- exact (proj2 (cmd_ro_prog_apart a Hro) HP).
- pose proof (HO _ Hin) as Hin'.
  apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ n (conj Hin' Ha)))))).
  exact (proj1 (cmd_ro_prog_apart a Hro)).
Qed.

Lemma srs_bsum_nonneg : forall ly S (W : world SEGS) mem md L, AR SEGS B ly S W mem md ->
(forall pn, In pn L -> In pn (ablocks B ly S)) -> 0 <= bsum L.
Proof.
intros ly S W mem md L HAR HL. induction L as [|[b m] L IH]; [unfold bsum; cbn; lia|].
rewrite bsum_cons. cbn [snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HL (b, m) (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hm).
assert (IH' := IH (fun pn Hpn => HL pn (or_intror Hpn))). lia.
Qed.

(* ---------- what a callee's journal keeps ---------- *)

Lemma srs_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma srs_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) recb_PG ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (recb_prog_unowned_m B HB cmd_prog_img a HP) as (H1 & H2 & H3). exact (srs_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma srs_keep_stack : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
(forall b, inFP FP1 b -> b < alloc_ceiling) -> alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Ha Hw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hw | intros Hf; specialize (HF a Hf); lia].
Qed.

Lemma srs_val_kept : forall (W W' : world SEGS) m m' a n v,
val_mem SEGS (mrestrict (w_H W) m) a n v ->
(forall k, (k < n)%nat -> rdW W' m' (a + Z.of_nat k) = rdW W m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hv Hk. apply val_mem_view. apply (srs_aval_kept (rdW W m)); [|exact Hk].
exact (aval_mem_view SEGS (w_H W) m a n v Hv).
Qed.

(* a byte of the slot: the walk may write it (awr_byte's program-static disjunct) *)
Lemma srs_awr_slot : forall STK sp O bl0 blc fr0 ly own c a, srs_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp (srs_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own c a Hc Ha. pose proof (srs_in_PG_slot c a Hc Ha) as HP.
right; right; right; right; left. split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct (srs_slot_bounds c Hc) as (Hcb & _ & [Hh | ->]).
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity|]. cbn [fst snd].
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity|]. cbn [fst snd].
  unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma srs_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

Lemma srs_blk_noprog : forall ly S (W : world SEGS) mem md b m a, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ Exists (in_zr a) recb_PG.
Proof. intros ly S W mem md b m a HAR Hin Ha HP. exact (recb_heap_noimg_m B ly S W mem md b m a HAR Hin Ha (cmd_prog_img a HP)). Qed.

Lemma srs_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

(* two live blocks that differ are apart *)
Lemma srs_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:103-105) *)
Lemma srs_answer_slot : forall R0 x,
(exists k, nth_error (r_calls (rec_record R0 SRS_FN [x])) k = Some (SRS_FN, [x]) /\
   srs_slot R0 = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(srs_slot R0 = A_REC_SPILL /\ (SRS_FN, [x]) = r_spill (rec_record R0 SRS_FN [x])).
Proof.
intros R0 x. unfold srs_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R0)) 16) as [L|L].
- left. exists (length (r_calls R0)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

Lemma srs_ncalls_len : forall R0 A A', length (r_calls (rec_record R0 SRS_FN A)) = length (r_calls (rec_record R0 SRS_FN A')).
Proof.
intros R0 A A'. unfold rec_record. destruct (Nat.ltb (length (r_calls R0)) 16); cbn [set_calls set_spill r_calls];
[rewrite !length_app; reflexivity | reflexivity].
Qed.

Definition srs_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma srs_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd (A_G_REC + OFF_ANSWER) 8 (srs_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold srs_old. split.
- unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
  [exact (proj1 HA) | exact HA].
- intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  left. reflexivity.
Qed.

(* the callee-saved registers, one by one *)
Lemma srs_pres : forall (r1 r2 : bvmap 5 word),
(forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r2 (Z_to_bv 5 n) = getr r1 (Z_to_bv 5 n)) ->
aregs_preserved r1 r2.
Proof.
intros r1 r2 H r Hr. apply H. unfold acallee_saved in Hr. cbn [In].
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [tauto | tauto | tauto | tauto | tauto |].
assert (H0 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct H0 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; tauto.
Qed.

Lemma srs_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain ly' (rdW W' mem') sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ HF Hc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly (rdW W mem) (rdW W' mem') sp0 v ch sp0 Hc); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
Qed.

Lemma srs_heap_apart : forall ly S (W : world SEGS) mem md b m lo len,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart b m lo len.
Proof.
intros ly S W mem md b m lo len HAR Hin Hlen Himg. unfold iv_apart.
destruct (srs_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & Hm & Hmr & Hr1).
destruct (Z_le_gt_dec (b + m) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) b) as [H'|H']; [right; exact H'|]. exfalso.
apply (recb_heap_noimg_m B ly S W mem md b m (Z.max b lo) HAR Hin); [lia | apply Himg; lia].
Qed.

Lemma srs_pres' : forall (r1 r2 : bvmap 5 word),
getr r2 2%bv = getr r1 2%bv -> getr r2 3%bv = getr r1 3%bv -> getr r2 4%bv = getr r1 4%bv ->
getr r2 8%bv = getr r1 8%bv -> getr r2 9%bv = getr r1 9%bv -> getr r2 18%bv = getr r1 18%bv ->
getr r2 19%bv = getr r1 19%bv -> getr r2 20%bv = getr r1 20%bv -> getr r2 21%bv = getr r1 21%bv ->
getr r2 22%bv = getr r1 22%bv -> getr r2 23%bv = getr r1 23%bv -> getr r2 24%bv = getr r1 24%bv ->
getr r2 25%bv = getr r1 25%bv -> getr r2 26%bv = getr r1 26%bv -> getr r2 27%bv = getr r1 27%bv ->
aregs_preserved r1 r2.
Proof.
intros r1 r2 X2 X3 X4 X8 X9 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27. apply srs_pres. intros n Hn. cbn [In] in Hn.
repeat (destruct Hn as [<- | Hn]; [assumption|]). destruct Hn.
Qed.

(* answer's post (answer_c.v:114-127) at the call's values *)
Definition srs_ansQ (lyA : alayout) (SA : astate) (R1 : rstate) (e : rcall) (shp : list byte) (O1 : list (Z * Z))
  (old : Z) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let t := snd (rec_answer R1 e shp true) in
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 /\ p1 <> p2 /\
 ~ In (p1, n) (ablocks B lyA SA) /\ ~ In (p2, n) (ablocks B lyA SA) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B lyA SA) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 rec_repA B ly' S' (rdW W' mem') (fst (rec_answer R1 e shp true)) O' /\
 (forall pn, In pn O' <-> (In pn O1 /\ fst pn <> old) \/ pn = (p1, n)) /\
 astr_atR (rdW W' mem') p2 t /\
 mo_le MT SA S' (XM_ANSWER MT t).

(* after a symbolic run the model term grows (measured 2026-10-28): name it *)
Ltac srs_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.
Lemma rec_repA_pos : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> 0 < snd pn.
Proof. intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. exact (srs_blocks_pos _ _ _ _ _ _ pn HA Hpn). Qed.

(* a live block is listed once *)
Lemma srs_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (L1 ++ L2) -> In pn L1 -> In pn L2 -> False.
Proof.
intros ly S W mem md L1 L2 pn HAR HP H1 H2.
pose proof H1 as H1'.
apply in_split in H1 as (a1 & b1 & ->). apply in_split in H2 as (a2 & b2 & ->).
assert (HP' : Permutation (ablocks B ly S) (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2))).
{ eapply Permutation_trans; [exact HP|].
  rewrite <- app_assoc. cbn [app].
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  replace (a1 ++ b1 ++ a2 ++ pn :: b2) with ((a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite <- !app_assoc. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP') as D.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1').
destruct pn as [b m].
destruct (srs_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* the head of a permutation of the live blocks is apart from every other entry *)
Lemma srs_head_apart : forall ly S (W : world SEGS) mem md x L y, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (x :: L) -> In y L ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
intros ly S W mem md x L y HAR HP Hy. apply in_split in Hy as (a & b & ->).
assert (HP' : Permutation (ablocks B ly S) (x :: y :: a ++ b)).
{ eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x y _ HAR HP') as D. unfold zdisjoint, block_rng in D.
cbn [fst snd] in D. exact D.
Qed.

Lemma srs_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* the bytes answer may write: g_rec.answer, g_rec.state, and the old answer's block, which the recorder owns *)
Lemma srs_awr_ans : forall STK sp O bl0 blc fr0 ly own (O1 : list (Z * Z)) old a,
(forall pn, In pn O1 -> fst pn = old -> In pn O /\ In pn blc) ->
inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
  ablocks_fp (filter (fun pn => fst pn =? old) O1)) a ->
awr_byte SEGS B STK sp (srs_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own O1 old a HO (r & Hr & Hra).
assert (HG : A_G_REC <= a < A_G_REC + REC_SIZE -> awr_byte SEGS B STK sp (srs_FP O) bl0 blc fr0 ly own a).
{ intros Ha. pose proof (recb_grec_in a Ha) as HP.
  right; right; right; right; left. split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
  exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. }
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra.
- apply HG. unfold OFF_ANSWER, REC_SIZE in *. lia.
- apply HG. unfold OFF_STATE, REC_SIZE in *. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin).
  apply srs_in_filter in Hin. destruct Hin as [Hin Hf]. cbn [fst snd] in *. destruct (HO (b, n) Hin Hf) as [HOb Hblc].
  right; left. split.
  + exists (b, b + req_size n). split; [|cbn [fst snd]; lia].
    unfold srs_FP. right; right. unfold ablocks_fp. apply in_map_iff. exists (b, n). split; [reflexivity | exact HOb].
  + exists b, n. split; [exact Hblc | lia].
Qed.

Lemma srs_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (srs_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO (r & Hr & Ha). pose proof asan_consts as (C1 & _).
unfold srs_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  destruct (srs_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (_ & Hb & _). lia.
Qed.

(* a byte range none of whose bytes the runtime owns and which is not the errno cell, decided on the record's
   lists (AF0m's Tfib_owned_static, TFIB_ERRNO) *)
Lemma srs_unowned_rng : forall lo n,
forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) Tfib_owned_static = true ->
((TFIB_ERRNO + 4 <=? lo) || (lo + n <=? TFIB_ERRNO)) = true ->
forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros lo n Hf He a Ha. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros Hex. apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in Hf. specialize (Hf r Hr).
  unfold in_zr in Hz. apply orb_true_iff in Hf as [Hf | Hf]; apply Z.leb_le in Hf; lia.
- apply orb_true_iff in He as [He | He]; apply Z.leb_le in He; lia.
Qed.

(* the bytes of a string argument decide astr_argA's reader part: its other three parts name no reader *)
Lemma srs_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [exact (srs_astr_kept rd rd' p v Hs K)|]. split; [exact Hl | exact Hr].
Qed.

(* a string argument's bytes are addresses of the machine: a block's, or the image's *)
Lemma srs_argA_range : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v, AR SEGS B ly1 S1 W1 mem1 md1 ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v HAR H i Hi. cbn [astr_argA] in H.
destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (srs_blk_bounds ly1 S1 W1 mem1 md1 b m HAR Hin) as (Hb & Hc & _ & Hmr & _).
  pose proof asan_consts as (C1 & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

Lemma srs_bytes_prefix : forall (rd : reader) a l l2, abytes_atR rd a (l ++ l2) -> abytes_atR rd a l.
Proof. intros rd a l l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity. Qed.

Lemma srs_bytes_eq : forall (rd : reader) a l l', abytes_atR rd a l -> map bv_unsigned l = map bv_unsigned l' ->
abytes_atR rd a l'.
Proof.
intros rd a l l' H E i Hi.
assert (Hl : length l = length l') by (rewrite <- (length_map bv_unsigned l), E, length_map; reflexivity).
rewrite (H i) by lia. f_equal.
rewrite <- (map_nth bv_unsigned l (Z_to_bv 8 0) i), <- (map_nth bv_unsigned l' (Z_to_bv 8 0) i), E. reflexivity.
Qed.

Lemma srs_no_zero : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate.
Qed.

(* the verb literal 0x21dc0 ("supervisor_reset", 16 bytes and its NUL) as rec_shape_of's pre asks it: astr_argA's
   read-only arm, whose read-only bytes come from CMD_RO_IN and whose record facts are decided here *)
Lemma srs_verb_argA : forall ly1 S1 (W1 : world SEGS) mem1 O1,
cmd_ro_ok (rdW W1 mem1) ->
abytes_atR (rdW W1 mem1) 0x21dc0 srs_verb /\
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 0x21dc0 (Some srs_verb).
Proof.
intros ly1 S1 W1 mem1 O1 HROd.
assert (HL : abytes_atR (rdW W1 mem1) 0x21dc0 RO_lit_21dc0).
{ destruct HROd as [HRB _]. unfold cmd_ro_bytes in HRB.
  repeat match type of HRB with
  | abytes_atR _ 0x21dc0 _ /\ _ => exact (proj1 HRB)
  | _ /\ _ => apply proj2 in HRB
  end. }
assert (HVS : astr_atR (rdW W1 mem1) 0x21dc0 srs_verb).
{ split; [apply (srs_bytes_eq _ _ _ _ HL); vm_compute; reflexivity|].
  apply srs_no_zero. vm_compute. reflexivity. }
split; [exact (srs_bytes_prefix _ _ _ _ (proj1 HVS))|].
cbn [astr_argA]. split; [lia|]. split; [exact HVS|]. split; [vm_compute; congruence|].
right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
- intros i Hi. change (Z.of_nat (length srs_verb) + 1) with 17 in Hi. split.
  + assert (HRI : forall j, 0 <= j < 17 -> in_roP SEGS RLO RHI (0x21dc0 + j)).
    { clear - CMD_RO_IN. pose proof CMD_RO_IN as HROIN. unfold cmd_ro_in in HROIN.
      repeat match type of HROIN with
      | (forall j, 0 <= j < 17 -> _ (0x21dc0 + j)) /\ _ => exact (proj1 HROIN)
      | _ /\ _ => apply proj2 in HROIN
      end. }
    exact (HRI i Hi).
  + apply (srs_unowned_rng 0x21dc0 17); [vm_compute; reflexivity | vm_compute; reflexivity | lia].
- change (0x21dc0 + Z.of_nat (length srs_verb)) with 0x21dd0. unfold cmd_ro_ends.
  repeat first [left; reflexivity | right].
Qed.

(* the start of a block the recorder owns is the start of no other live block *)
Lemma srs_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (recb_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (srs_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (srs_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (srs_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* one register of a seed's regs_ok: the slot, its nargs field, the shadow base, s4, or a register of its own *)
Ltac srs_reg1 E34 E32 G8 G18 G19 G20 :=
lazymatch goal with |- getr ?rg ?r = sv_denot ?E (sr_get ?a ?r) =>
  let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v end;
first
[ let G := fresh in pose proof G20 as G; rewrite <- (srs_shx4_denot _ _ E34 E32) in G by lia; exact G
| cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; exact G8
| cbn [sv_denot]; rewrite E34, unsigned_lit_small by lia; exact G18
| cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact G19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [ symmetry; apply srs_E_reg; reflexivity | symmetry; apply getr_zero | reflexivity ] ].
Ltac srs_regs_ok E34 E32 G8 G18 G19 G20 :=
apply regs_ok_by_cases; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [all_regs In] in Hr;
repeat (destruct Hr as [<- | Hr]; [srs_reg1 E34 E32 G8 G18 G19 G20 | ]); try (destruct Hr; fail).
(* the writes of a segment after the prologue: the frame is read-only, the slot's first 16 bytes are g_rec's or
   record.spill's *)
Ltac srs_awr UC Hc :=
lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end;
apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|];
eapply awr_ok_cons_gen; [reflexivity | exact UC | | apply awr_ok_nil];
cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
apply (srs_awr_slot _ _ _ _ _ _ _ _ _ a Hc); unfold CALL_SIZE; lia.

(* ---------- after the prologue: from the call of xstrdup to the end ---------- *)
(* the walk from the call of xstrdup (0x8b78c) on: the state there, against the entry and the base *)
Definition srs_SX_spec : Prop := forall ly S W regs mem md ch pw which R O Q lyc Sc Wc memT mdT k lyB SBa WB memB R0 O0 F
  (regsT : bvmap 5 word) sx,
srs_pre ly S W regs mem md ch pw which R O ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q -> (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
srs_mid ly S W regs mem md R O lyc Sc Wc memT mdT k lyB SBa WB memB R0 O0 F ->
srs_recmem (rdW Wc memT) (rdW WB memB) (srs_slot R0) 8 ->
srs_ncalls_ok (rdW Wc memT) R0 ->
aval_mem (rdW Wc memT) (srs_slot R0 + CALL_OFF_FN) 4 SRS_FN ->
aval_mem (rdW Wc memT) (srs_slot R0 + CALL_OFF_NARGS) 4 0 ->
getr regsT 1 = w64 (BASE + SRS_RETX) -> getr regsT 2 = w64 (spZ regs - SRS_FRAME) ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 8 = w64 (srs_slot R0) -> getr regsT 18 = w64 (srs_slot R0 + 4) -> getr regsT 19 = w64 SB ->
getr regsT 20 = w64 (SB + (srs_slot R0 + 4) / 8) -> getr regsT 10 = w64 sx ->
(forall r, 21 <= r <= 27 -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
astr_argA B lyc Sc (rdW Wc memT) (in_roP SEGS RLO RHI) [] sx (Some (sarg which)) ->
atail_vis SEGS Wc memT (sx + Z.of_nat (length (sarg which))) ->
SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS_xstrdup)) memT (seg_rom SEGS)) mdT)
(apost_baseF SEGS B SRS_STK (srs_FP O) regs ly S W mem md (EV_SUP_RESET R) (srs_Q ly S R O which)).

Lemma srs_SX : srs_SX_spec.
Proof.
intros ly S W regs mem md ch pw which R O Q lyc Sc Wc memT mdT k lyB SBa WB memB R0 O0 F regsT sx
  PRE HQ HOQ MID RM NC VFN VNA R1 R2 R3 R4 R8 R18 R19 R20 R10 RS7 HSTR HTAIL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & HRND & HROD & HRO & HPW & H10 & HARG & HREP & HFR8 & HEV & HLIVE & HMOK & HG2).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk & HFRM & HREPB & HSP0 & HLEN0 & HREC0 & HKO0 & HIO0 & HPERM & HFO & HO0 & HFN & MLE).
pose proof (proj1 HJ) as HARc.
set (sp0 := spZ regs) in *.
set (c := srs_slot R0) in *.
set (x := sarg which) in *.
assert (HST : SRS_STK = 16592) by reflexivity.
assert (Hn16 : (length (r_calls R0) <= 16)%nat).
{ destruct HREPB as (QB & (_ & _ & _ & (G1 & _) & _) & _). exact G1. }
assert (Hc : srs_slot_ok c) by exact (srs_slot_ok_of R0 Hn16).
destruct (srs_slot_bounds c Hc) as (Hcb & Hc8 & Hch').
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
(* the call of xstrdup (0x8b78c) *)
assert (Ssp : spZ regsT = sp0 + -48) by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small; unfold SRS_FRAME; lia).
rewrite (SIGP CS_xstrdup ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_xstrdup) with (BASE + AF_xstrdup).
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsT memT _ SRS_STK sp0 (srs_FP O) ly S W mem md [] lyc Sc mdT k XSTRDUP_STK [] EV_XSTRDUP
    (-48) (w64 (BASE + SRS_RETX)) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
      getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
      Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B lyc Sc) /\
      Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
      astr_atR (rdW W2 mem2) p x /\ astr_atR (rdW W2 mem2) sx x /\
      blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP x /\
      mo_le MT Sc S2 (XM_XSTRDUP MT x)) HJ Ssp).
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - rewrite HST. unfold XSTRDUP_STK, ASTACK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold w64. apply ret_ok_codeptr_v; [unfold SRS_RETX, AF_sup_reset; lia | reflexivity].
  - unfold w64, SRS_RETX, AF_sup_reset. pose proof HBASE as (HB0 & HB1 & _).
    rewrite unsigned_lit_small; lia.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64.
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TXSTRDUP fx lyc Sc Wc regsT memT mdT [] sx x HPRE1).
      * exact (srs_aro ly S W mem md O lyc Sc Wc memT mdT [] k sp0 HAR HOin HJ HROD).
      * exact R10.
      * left. exact HSTR.
      * exact HTAIL.
      * pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
        unfold EV_SUP_RESET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia.
      * rewrite (blocks_bytes_bsum B lyc Sc). rewrite (blocks_bytes_bsum B ly S) in HLIVE.
        rewrite (bsum_perm _ _ HPERM), bsum_app in HLIVE.
        assert (HF0 : 0 <= bsum F).
        { apply (srs_bsum_nonneg ly S W mem md F HAR). intros pn Hpn.
          apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. exact Hpn. }
        unfold LIVE_SUP_RESET, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. fold x in HLIVE. lia.
      * apply (mo_ok_le MT MTL Sc (XM_XSTRDUP MT x) (XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_reset_m R which)))).
        -- apply (mo_ok_step MT MTL S Sc (Z.of_nat (length F) * mo_free MT)); [|exact MLE].
           unfold XM_SUP_RESET in HMOK. rewrite <- HFN in HMOK. fold x in HMOK.
           replace (Z.of_nat (length F) * mo_free MT + (XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_reset_m R which))))
             with (Z.of_nat (length F) * mo_free MT + XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_reset_m R which))) by lia.
           exact HMOK.
        -- unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
           pose proof (mo_free_nonneg MT MTL) as Hf.
           pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_reset_m R which))) + 1) ltac:(lia)) as Hm.
           lia.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite R1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
      destruct HQ3 as (pq & A1 & A2 & A3 & A4 & _ & A6 & A7 & A8 & A9).
      exact (ex_intro _ pq (conj A1 (conj A2 (conj A3 (conj A4 (conj A6 (conj A7 (conj A8 A9)))))))).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (p & Hp10 & Hp4096 & Hperm2 & Hfresh2 & Hpstr & Hsstr & HBB2 & MLE2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hceil0 : alloc_ceiling <= sp0 - 48) by (rewrite HST in Hslo; lia).
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsT rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (KST2 : forall a, sp0 - 48 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memT a).
{ intros a Ha. apply (srs_keep_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2);
  [intros b Hb; exfalso; exact (inFP_nil b Hb) | lia | lia]. }
assert (KPG2 : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc memT a).
{ intros a HP. apply (srs_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2); [constructor | intros Hf; exact (inFP_nil a Hf) | exact HP]. }
assert (HFRM2 : srs_frame_at (mrestrict (w_H W2) mem2) (sp0 - SRS_FRAME) regs).
{ intros j r Hjr. apply (srs_val_kept Wc W2 memT mem2); [exact (HFRM j r Hjr)|].
  intros kk Hkk. apply KST2. assert (Hj : (j < 6)%nat) by (change 6%nat with (length srs_saved); apply nth_error_Some; rewrite Hjr; discriminate).
  unfold SRS_FRAME. lia. }
assert (VFN2 : aval_mem (rdW W2 mem2) (c + CALL_OFF_FN) 4 SRS_FN).
{ apply (srs_aval_kept (rdW Wc memT)); [exact VFN|]. intros kk Hkk. apply KPG2. apply (srs_in_PG_slot c); [exact Hc|].
  unfold CALL_OFF_FN, CALL_SIZE. lia. }
assert (VNA2 : aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 0).
{ apply (srs_aval_kept (rdW Wc memT)); [exact VNA|]. intros kk Hkk. apply KPG2. apply (srs_in_PG_slot c); [exact Hc|].
  unfold CALL_OFF_NARGS, CALL_SIZE. lia. }
set (nn := Z.of_nat (length (r_calls R0))).
assert (Hnn : 0 <= nn <= 16) by (subst nn; lia).
assert (Q2 : getr regs2 2 = w64 (sp0 - 48)) by (rewrite (CS2 2%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); rewrite R2; reflexivity).
assert (Q2u : bv_unsigned (getr regs2 2) = sp0 - 48) by (rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (E34 : ew (srs_E regs2 regs nn c) 34 = Z_to_bv 64 c)
  by (rewrite (srs_E_extra_at regs2 regs nn c 34 ltac:(lia)); reflexivity).
assert (E32 : ew (srs_E regs2 regs nn c) 32 = Z_to_bv 64 SB)
  by (rewrite (srs_E_extra_at regs2 regs nn c 32 ltac:(lia)); reflexivity).
assert (G8 : getr regs2 8 = Z_to_bv 64 c) by (rewrite (CS2 8%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R8).
assert (G18 : getr regs2 18 = Z_to_bv 64 (c + 4)) by (rewrite (CS2 18%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R18).
assert (G19 : getr regs2 19 = Z_to_bv 64 SB) by (rewrite (CS2 19%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R19).
assert (G20 : getr regs2 20 = Z_to_bv 64 (SB + (c + 4) / 8)) by (rewrite (CS2 20%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R20).
assert (Hcr : 0 <= c < 2 ^ 40) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb; lia).
destruct (srs_seed B HB VOBJS cmd_prog_writable SRS_RETX srs_regsD
  [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 10))] W2 regs2 regs mem2 ly2 S2 md2 nn c HAR2)
  as [HS SHOK].
{ rewrite Q2u. unfold SRS_FRAME. lia. }
{ rewrite Q2u. replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
{ exact Hnn. }
{ exact Hc. }
{ srs_regs_ok E34 E32 G8 G18 G19 G20. }
{ rewrite Q2u. exact HFRM2. }
{ vm_compute. reflexivity. }
{ constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS _ _ c 4 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    apply val_mem_view. exact VNA2.
  - apply (chunk_ok_val SEGS _ _ c 0 4 (SLit 10) 10); [reflexivity | cbn; lia | cbn; lia |].
    apply val_mem_view. exact VFN2. }
pose proof (srs_E_img regs2 regs nn c) as HEI.
assert (UC : bv_unsigned (ew (srs_E regs2 regs nn c) SRS_C) = c) by (unfold SRS_C; rewrite E34; apply unsigned_lit_small; lia).
remember (srs_E regs2 regs nn c) as E eqn:HE.
unfold w64. change (BASE + SRS_RETX) with (BASE + SRS_RETX).
(* 0x8b790 .. 0x8b7d0: the two checks after the call, c->nargs := 1, c->args[0] := the copy, the call of rec_shape_of *)
paj_run_tok RUN HS HJ2 SHOK srs_Bspan.
{ srs_awr UC Hc. }
pmkst HS. srs_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs2 rr)
  by (intros kk rr Hkk; rewrite HE; apply srs_E_reg; exact Hkk).
assert (V305 : ew E 305 = Z_to_bv 64 0x21dc0).
{ pose proof (HEI 305%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H305.
  change (VAL 305%nat) with (VAL (A_OBJ 64)) in H305. rewrite (VOBJS 64%nat ltac:(vm_compute; lia)) in H305.
  apply bv_eq. rewrite H305. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = w64 (BASE + SRS_RETS)) by (rewrite P1; reflexivity).
assert (Q2s : spZ (ms_regs ms) = sp0 + -48)
  by (unfold spZ; rewrite P2, (EE 2%nat 2%bv eq_refl), Q2; unfold w64; rewrite unsigned_lit_small; lia).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite P3, (EE 3%nat 3%bv eq_refl), (CS2 3%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite P4, (EE 4%nat 4%bv eq_refl), (CS2 4%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R4).
assert (Q10 : getr (ms_regs ms) 10 = w64 0x21dc0) by (rewrite P10, V305; reflexivity).
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat (length srs_verb))) by (rewrite P11; reflexivity).
assert (Q8 : s0Z (ms_regs ms) = c) by (unfold s0Z; rewrite P8, E34; apply unsigned_lit_small; lia).
pose proof (proj1 HJ2) as HARd.
assert (HAROd : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms)))
  by exact (srs_aro ly S W mem md O ly2 S2 W2 (ms_mem ms) _ [] _ sp0 HAR HOin HJ2 HROD).
assert (HROd : cmd_ro_ok (rdW W2 (ms_mem ms))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARd HAROd).
(* what run D wrote: the slot's fn, nargs and args[0]; every other byte is kept *)
assert (UC34 : bv_unsigned (ew E 34) = c) by exact UC.
assert (Usp2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (EE 2%nat 2%bv eq_refl), Q2; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRD end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c <= a < c + 16) HFRD
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?UC34 in Hrr; lia|]);
        destruct Hin)) as KD.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) srs_frame) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H W2) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRgD;
  cbn [ms_mem restrict mkst] in HRgD end.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 0 4%N (SLit 10) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VFND.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 4 4%N (SLit 1) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VNAD.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 8 8%N (SOff 10 0) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VA0D.
(* the call of rec_shape_of("supervisor_reset", 16) (0x8b7d0) *)
rewrite (SIGP CS_rec_shape_of ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_rec_shape_of) with (BASE + AF_rec_shape_of).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 (ms_regs ms) (ms_mem ms) _ SRS_STK sp0 (srs_FP O) ly S W mem md [] ly2 S2 _ _
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (w64 (BASE + SRS_RETS))
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      (exists q, getr regs3 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
       forall O1, astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O1 q (Some (shape_of srs_verb))) /\
      Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2) HJ2 Q2s).
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite HST. unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - unfold w64. apply ret_ok_codeptr_v; [unfold SRS_RETS, AF_sup_reset; lia | reflexivity].
  - unfold w64, SRS_RETS, AF_sup_reset. pose proof HBASE as (HB0 & HB1 & _).
    rewrite unsigned_lit_small; lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TREC_SHAPE_OF fx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ 0x21dc0 srs_verb HPRE1 HAROd Q10 ltac:(lia) Q11
        ltac:(vm_compute; reflexivity) HROd VOBJS).
      * intros _. destruct (srs_verb_argA ly2 S2 W2 (ms_mem ms) [] HROd) as (HVB & HVA).
        split; [exact HVB | right; exact HVA].
      * pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
        unfold EV_REC_SHAPE_OF, EV_SUP_RESET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite Q1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
      exact HQ3.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 &
  ((q & Hq10 & Hq64 & HqA) & Hperm3 & Ely3 & ES3)).
pose proof (proj1 HJ3) as HAR3.
(* back at 0x8b7d4: the frame is kept, the rest of the state is the callee's *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros a Ha.
  - apply (mbyte_of_aview SEGS).
    apply (srs_keep_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [intros b Hb; exfalso; exact (inFP_nil b Hb) | lia | lia].
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (A58 : ew E3 52 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (SHOK3 : sh_ok SEGS srs_Bx [] E3 (mrestrict (w_H W3) mem3)) by (unfold sh_ok; constructor).
(* 0x8b7d4 .. 0x8b7fc: a2 := 1, a1 := the shape, a0 := c, the frame's registers back, sp += 48, j answer *)
paj_run_tok RUN HS HJ3 SHOK3 srs_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]. apply awr_ok_nil. }
pmkst HS. srs_md.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
(* run E kept every byte *)
lazymatch goal with HFx : frame_of E3 _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRE end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFRE
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KE.
pose proof (proj1 HJ3) as HARA.
(* the registers at the jump to answer: the entry's callee-saved registers and sp, ra, a0 = c, a1 = the shape, a2 = 1 *)
assert (OE : forall n, (n < 48)%nat -> ew E3 n = ew (srs_E regs2 regs nn c) n)
  by (intros n Hn; rewrite OLD3 by exact Hn; rewrite HE; reflexivity).
assert (CSr : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> acallee_saved (bv_unsigned rr) ->
  ew E3 n = getr regsT rr).
{ intros n rr Hn Hcs. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite OE by lia. rewrite (srs_E_reg regs2 regs nn c n rr Hn). apply CS2. exact Hcs. }
assert (A1 : getr (ms_regs ms0) 1 = getr regs 1).
{ rewrite T1, OE by lia. rewrite (srs_E_extra_at regs2 regs nn c 35 ltac:(lia)). reflexivity. }
assert (X2 : getr (ms_regs ms0) 2%bv = getr regs 2%bv).
{ rewrite T2, OE by lia. rewrite (srs_E_reg regs2 regs nn c 2 2%bv eq_refl), Q2. unfold w64.
  rewrite unsigned_lit_small by lia. replace (sp0 - 48 + 48) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (X3 : getr (ms_regs ms0) 3%bv = getr regs 3%bv).
{ rewrite T3. rewrite (CSr 3%nat 3%bv eq_refl) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia). rewrite R3, Hgp. reflexivity. }
assert (X4 : getr (ms_regs ms0) 4%bv = getr regs 4%bv).
{ rewrite T4. rewrite (CSr 4%nat 4%bv eq_refl) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia). rewrite R4, Htp. reflexivity. }
assert (X8 : getr (ms_regs ms0) 8%bv = getr regs 8%bv)
  by (rewrite T8, OE by lia; rewrite (srs_E_extra_at regs2 regs nn c 36 ltac:(lia)); reflexivity).
assert (X9 : getr (ms_regs ms0) 9%bv = getr regs 9%bv)
  by (rewrite T9, OE by lia; rewrite (srs_E_extra_at regs2 regs nn c 37 ltac:(lia)); reflexivity).
assert (X18 : getr (ms_regs ms0) 18%bv = getr regs 18%bv)
  by (rewrite T18, OE by lia; rewrite (srs_E_extra_at regs2 regs nn c 38 ltac:(lia)); reflexivity).
assert (X19 : getr (ms_regs ms0) 19%bv = getr regs 19%bv)
  by (rewrite T19, OE by lia; rewrite (srs_E_extra_at regs2 regs nn c 39 ltac:(lia)); reflexivity).
assert (X20 : getr (ms_regs ms0) 20%bv = getr regs 20%bv)
  by (rewrite T20, OE by lia; rewrite (srs_E_extra_at regs2 regs nn c 40 ltac:(lia)); reflexivity).
assert (XH : forall (rr : bv 5) n, Z.of_nat n = bv_unsigned rr -> 21 <= bv_unsigned rr <= 27 ->
  ew E3 n = getr regs rr).
{ intros rr n Hn Hr. rewrite (CSr n rr Hn) by (unfold acallee_saved; lia).
  rewrite <- (Z_to_bv_bv_unsigned 5 rr). apply RS7. exact Hr. }
assert (X21 : getr (ms_regs ms0) 21%bv = getr regs 21%bv) by (rewrite T21; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X22 : getr (ms_regs ms0) 22%bv = getr regs 22%bv) by (rewrite T22; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X23 : getr (ms_regs ms0) 23%bv = getr regs 23%bv) by (rewrite T23; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X24 : getr (ms_regs ms0) 24%bv = getr regs 24%bv) by (rewrite T24; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X25 : getr (ms_regs ms0) 25%bv = getr regs 25%bv) by (rewrite T25; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X26 : getr (ms_regs ms0) 26%bv = getr regs 26%bv) by (rewrite T26; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X27 : getr (ms_regs ms0) 27%bv = getr regs 27%bv) by (rewrite T27; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (HPA : aregs_preserved regs (ms_regs ms0))
  by exact (srs_pres' regs (ms_regs ms0) X2 X3 X4 X8 X9 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27).
(* ---- the memory at the jump, against the call of xstrdup and the base ---- *)
assert (HRK3 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms0) a = rdW W3 mem3 a)
  by (intros a Ha; exact (KE a Ha (fun H => H))).
assert (KAP : forall a, Exists (in_zr a) recb_PG -> ~ (c <= a < c + 16) -> rdW W3 (ms_mem ms0) a = rdW Wc memT a).
{ intros a HP Hs. pose proof (pa_img_range a (cmd_prog_img a HP)) as Hr.
  rewrite HRK3 by lia.
  rewrite (srs_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [| constructor | intros Hf; exact (inFP_nil a Hf) | exact HP].
  rewrite (KD a ltac:(lia) Hs). exact (KPG2 a HP). }
assert (KAS : forall a, c <= a < c + 16 -> rdW W3 (ms_mem ms0) a = rdW W2 (ms_mem ms) a).
{ intros a Ha. pose proof (srs_in_PG_slot c a Hc ltac:(unfold CALL_SIZE; lia)) as HP.
  pose proof (pa_img_range a (cmd_prog_img a HP)) as Hr. rewrite HRK3 by lia.
  apply (srs_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [constructor | intros Hf; exact (inFP_nil a Hf) | exact HP]. }
assert (KAB2 : forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  rdW W3 (ms_mem ms0) (b + i) = rdW W2 mem2 (b + i)).
{ intros b m i Hin Hi. destruct (srs_blk_bounds ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (Hb0 & Hb1 & _).
  pose proof asan_consts as (CC1 & _). rewrite HRK3 by lia.
  rewrite (srs_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m i HJc3 Hin
    ltac:(apply (Permutation_in _ (Permutation_sym Hperm3)); exact Hin) Hi ltac:(intros Hf; exact (inFP_nil _ Hf))).
  apply KD; [lia|]. intros Hs. apply (srs_blk_noprog ly2 S2 W2 mem2 md2 b m (b + i) HAR2 Hin ltac:(lia)).
  apply (srs_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia]. }
assert (KABT : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
  rdW W3 (ms_mem ms0) (b + i) = rdW Wc memT (b + i)).
{ intros b m i Hin Hi.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hin).
  rewrite (KAB2 b m i Hin2 Hi).
  exact (srs_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m i HJc2 Hin Hin2 Hi ltac:(intros Hf; exact (inFP_nil _ Hf))). }
assert (HIN3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm3)). apply (Permutation_in _ (Permutation_sym Hperm2)).
  right. exact Hpn. }
assert (HPIN3 : In (p, LIVE_XSTRDUP x) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). apply (Permutation_in _ (Permutation_sym Hperm2)). left. reflexivity. }
assert (HPIN2 : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); left; reflexivity).
assert (Hxlen : Z.of_nat (length x) + 1 <= LMAX + 1) by (destruct HSTR as (_ & _ & H & _); exact H).
(* the slot's fields at the jump *)
change (N.to_nat 4) with 4%nat in VFND, VNAD. change (N.to_nat 8) with 8%nat in VA0D.
replace (bv_unsigned (sv_denot E (SLit 10)) mod 2 ^ (8 * Z.of_N 4)) with 10 in VFND by (vm_compute; reflexivity).
replace (bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VNAD by (vm_compute; reflexivity).
assert (Hpr : p < 2 ^ 64).
{ destruct (srs_blk_bounds ly2 S2 W2 mem2 md2 p _ HAR2 HPIN2) as (_ & Hb1 & _ & _ & Hr1). pose proof asan_consts as (CC1 & _). lia. }
replace (bv_unsigned (sv_denot E (SOff 10 0)) mod 2 ^ (8 * Z.of_N 8)) with p in VA0D
  by (cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Hp10, Z.add_0_r, Z_to_bv_bv_unsigned; unfold w64;
      rewrite unsigned_lit_small by lia; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite Z.mod_small by lia; reflexivity).
assert (VFNA : aval_mem (rdW W3 (ms_mem ms0)) (srs_slot R0 + CALL_OFF_FN) 4 SRS_FN).
{ apply (srs_aval_kept (rdW W2 (ms_mem ms))); [exact (aval_mem_view SEGS _ _ _ _ _ VFND)|].
  intros kk Hkk. apply KAS. unfold CALL_OFF_FN. lia. }
assert (VNAA : aval_mem (rdW W3 (ms_mem ms0)) (srs_slot R0 + CALL_OFF_NARGS) 4 1).
{ apply (srs_aval_kept (rdW W2 (ms_mem ms))); [exact (aval_mem_view SEGS _ _ _ _ _ VNAD)|].
  intros kk Hkk. apply KAS. unfold CALL_OFF_NARGS. lia. }
assert (VA0A : aval_mem (rdW W3 (ms_mem ms0)) (srs_slot R0 + CALL_OFF_ARGS) 8 p).
{ apply (srs_aval_kept (rdW W2 (ms_mem ms))); [exact (aval_mem_view SEGS _ _ _ _ _ VA0D)|].
  intros kk Hkk. apply KAS. unfold CALL_OFF_ARGS. lia. }
(* record(10) and arg_s, over the base *)
assert (HREP1 : rec_repA B ly3 S3 (rdW W3 (ms_mem ms0)) (rec_record R0 SRS_FN [x]) ((p, Z.of_nat (length x) + 1) :: O0)).
{ apply (srs_rec_repA_record1 B lyB SBa (rdW WB memB) ly3 S3 (rdW W3 (ms_mem ms0)) R0 O0 SRS_FN x p HREPB HSP0).
  - unfold SRS_FN, REC_FN_COUNT. lia.
  - unfold LMAX in *. lia.
  - rewrite (srs_ncalls_len R0 [x] [[]]). apply (srs_aval_kept (rdW Wc memT)); [exact NC|].
    intros kk Hkk. apply KAP; [apply recb_grec_in; unfold OFF_NCALLS, REC_SIZE; lia|].
    unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *. lia.
  - exact VFNA.
  - exact VNAA.
  - exact VA0A.
  - intros a Hin Hnc Hns. rewrite (KAP a); [| destruct Hin as [Hin | Hin]; [apply recb_grec_in | apply recb_spill_in]; exact Hin | exact Hns].
    apply RM; [exact Hin | exact Hnc | lia].
  - intros [b m] i Hpn Hi. cbn [fst snd] in *. pose proof (HIO0 _ Hpn) as Hin.
    destruct (srs_blk_bounds lyc Sc Wc memT mdT b m HARc Hin) as (_ & _ & _ & Hmr & _).
    rewrite (KABT b m i Hin ltac:(lia)). exact (HKO0 (b, m) i Hpn Hi).
  - intros pn Hpn. apply HIN3. apply HIO0. exact Hpn.
  - exact HPIN3.
  - rewrite Forall_forall. intros qk Hqk. rewrite Forall_forall in Hfresh2. apply Hfresh2. apply HIO0. exact Hqk.
  - apply (srs_heap_apart ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) A_G_REC REC_SIZE HAR2 HPIN2); [unfold REC_SIZE; lia|].
    intros a Ha. apply cmd_prog_img. apply recb_grec_in. exact Ha.
  - apply (srs_heap_apart ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) A_REC_SPILL SC_SIZE HAR2 HPIN2); [unfold SC_SIZE; lia|].
    intros a Ha. apply cmd_prog_img. apply recb_spill_in. exact Ha.
  - lia.
  - apply (srs_astr_kept (rdW W2 mem2)); [exact Hpstr|]. intros i Hi.
    destruct (srs_blk_bounds ly2 S2 W2 mem2 md2 p _ HAR2 HPIN2) as (_ & _ & _ & Hmr & _). unfold LIVE_XSTRDUP in Hmr.
    exact (KAB2 p (LIVE_XSTRDUP x) i HPIN2 ltac:(unfold LIVE_XSTRDUP; lia)). }
(* the old answer: the base layout's answer block, one of O0, its address still in g_rec.answer *)
pose proof HREPB as (QB & HQB & HOQB).
destruct (srs_old_at _ _ _ _ HQB) as [HOLDB HOLDBin].
assert (HOLD : aval_mem (rdW W3 (ms_mem ms0)) (A_G_REC + OFF_ANSWER) 8 (srs_old QB)).
{ apply (srs_aval_kept (rdW WB memB)); [exact HOLDB|]. intros kk Hkk.
  assert (Hcs : c + 16 <= A_G_REC + OFF_ANSWER \/ A_REC_SPILL <= c).
  { destruct Hch' as [Hh | ->]; [left | right; lia]. unfold srs_slot in *.
    unfold c, srs_slot in Hh |- *. destruct (Nat.ltb_spec (length (r_calls R0)) 16) as [L|L];
      unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER, REC_SIZE, A_REC_SPILL in *; lia. }
  rewrite (KAP (A_G_REC + OFF_ANSWER + Z.of_nat kk)); [| apply recb_grec_in; unfold OFF_ANSWER, REC_SIZE; lia | unfold A_G_REC, A_REC_SPILL, OFF_ANSWER in *; lia].
  apply RM; [left; unfold OFF_ANSWER, REC_SIZE; lia | unfold OFF_NCALLS, OFF_ANSWER; lia | unfold A_G_REC, A_REC_SPILL, OFF_ANSWER in *; lia]. }
assert (HOLD0 : forall pn, In pn ((p, Z.of_nat (length x) + 1) :: O0) -> fst pn = srs_old QB -> In pn O0).
{ intros pn [<- | Hpn] Hf; [|exact Hpn]. exfalso. cbn [fst] in Hf.
  unfold srs_old in Hf. destruct (l_answer QB) as [an|] eqn:Ean.
  - pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. destruct an as [a1 a2]. cbn [fst] in Hf. subst a1.
    rewrite Forall_forall in Hfresh2.
    pose proof (Hfresh2 (p, a2) (HIO0 _ Han)) as Hap. cbn [fst snd] in Hap. unfold iv_apart, LIVE_XSTRDUP in Hap.
    pose proof (rec_repA_pos lyB SBa (rdW WB memB) R0 O0 HREPB (p, a2) Han) as Hpos. cbn [snd] in Hpos. lia.
  - lia. }
assert (HO1in : forall pn, In pn ((p, Z.of_nat (length x) + 1) :: O0) -> In pn (ablocks B ly3 S3)).
{ intros pn [<- | Hpn]; [exact HPIN3 | apply HIN3; apply HIO0; exact Hpn]. }
(* ---- the tail jump into answer (0x8b7fc): answer runs at the entry's sp and returns to the entry's ra ---- *)
pose proof (proj1 HJ3) as HARJ.
assert (HM : sup_reset_m R which = rec_answer (rec_record R0 SRS_FN [x]) (SRS_FN, [x]) (shape_of srs_verb) true).
{ unfold sup_reset_m, rec_stub. rewrite HREC0. reflexivity. }
assert (SPA : spZ (ms_regs ms0) = sp0) by (unfold spZ at 1; rewrite X2; reflexivity).
assert (HAS : ANSWER_STK = 16592) by reflexivity.
assert (HFPlow : forall a, inFP (srs_FP O) a -> a < alloc_ceiling)
  by (intros a Ha; exact (srs_FP_low ly S W mem md O a HAR HOin Ha)).
assert (HchA : achain ly3 (rdW W3 (ms_mem ms0)) (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) ch).
{ rewrite SPA. unfold s0Z at 1. rewrite X8. exact (srs_achain_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HFPlow Hch). }
assert (HPREA : afn_pre SEGS B ANSWER_STK ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) mdv0 ch).
{ apply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms0) ANSWER_STK 0 ch HJ3).
  - rewrite SPA. lia.
  - reflexivity.
  - lia.
  - rewrite HAS. lia.
  - rewrite HAS, HST. lia.
  - rewrite A1. exact Hra.
  - unfold raZ. rewrite A1. exact Hra4.
  - rewrite X3. exact Hgp.
  - rewrite X4. exact Htp.
  - exact HchA. }
pose proof HJ3 as (_ & _ & _ & _ & _ & HfrJ & HnevJ & _).
assert (HRAJ : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms0)))
  by exact (srs_aro ly S W mem md O ly3 S3 W3 (ms_mem ms0) mdv0 [] _ sp0 HAR HOin HJ3 HROD).
pose proof (proj1 HJc3) as HAR3m.
assert (Hold64 : 0 <= srs_old QB < 2 ^ 64).
{ unfold srs_old. destruct (l_answer QB) as [an|] eqn:Ean; [|lia].
  pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. pose proof (HIO0 _ Han) as Hc'. destruct an as [a1 a2].
  destruct (srs_blk_bounds lyc Sc Wc memT mdT a1 a2 HARc Hc') as (Hb0 & Hb1 & _ & _ & Hr1).
  pose proof asan_consts as (CC1 & _). cbn [fst]. lia. }
(* the meter up to the jump: rec_shape_of changed no allocator state (its post gives S3 = S2) *)
assert (M3 : mo_le MT S2 S3 0) by (rewrite ES3; exact (mo_le_refl MT MTL S2)).
assert (MLEJ : mo_le MT S S3 (Z.of_nat (length F) * mo_free MT + XM_XSTRDUP MT x + 0))
  by exact (mle_station MT S S2 S3 _ 0 MTL (mle_station MT S Sc S2 _ _ MTL MLE MLE2) M3).
assert (HXA : 0 <= XM_ANSWER MT (snd (rec_answer (rec_record R0 SRS_FN [x]) (SRS_FN, [x]) (shape_of srs_verb) true))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (rec_answer (rec_record R0 SRS_FN [x]) (SRS_FN, [x]) (shape_of srs_verb) true))) + 1) ltac:(lia)).
  lia. }
rewrite (SIGP CS_answer ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_answer) with (BASE + AF_answer).
eapply SRr_mono.
{ apply (TANSWER fx ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) mdv0 ch (srs_slot R0) q (srs_old QB) (SRS_FN, [x])
    (shape_of srs_verb) true (rec_record R0 SRS_FN [x]) ((p, Z.of_nat (length x) + 1) :: O0) HPREA).
  - exact HRND.
  - rewrite HfrJ. cbn [app]. exact HFR8.
  - exact HRAJ.
  - exact (cmd_ro_ok_of_aro _ _ _ _ _ HARJ HRAJ).
  - rewrite T10, OE by lia. rewrite <- HE. exact E34.
  - clear - Hcb. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. lia.
  - rewrite T11, A58. exact Hq10.
  - exact Hq64.
  - rewrite T12. reflexivity.
  - exact HREP1.
  - exact HOLD.
  - exact Hold64.
  - intros _. split.
    + apply (srs_argA_kept _ _ (rdW W3 mem3)); [exact (HqA _)|]. intros i Hi. apply HRK3.
      exact (srs_argA_range ly3 S3 W3 mem3 md3 _ q _ HAR3m (HqA []) i Hi).
    + unfold fits. vm_compute. congruence.
  - intros _ _. exact (srs_answer_slot R0 x).
  - unfold EV_SUP_RESET, EV_XSTRDUP, EV_REC_SHAPE_OF in *. lia.
  - rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ Hperm3), (bsum_perm _ _ Hperm2), bsum_cons. cbn [snd].
    rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPERM), bsum_app in HLIVE.
    unfold LIVE_SUP_RESET in HLIVE. rewrite HM in HLIVE. fold x in HLIVE.
    pose proof (srs_bsum_nonneg ly S W mem md F HAR
      ltac:(intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hpn)).
    lia.
  - apply (mok_station MT S S3 _ _ _ MTL HMOK MLEJ HXA).
    unfold XM_SUP_RESET. rewrite HM. fold x. rewrite <- HFN. lia. }
cbv beta. intros W4 c4 _ (fx1 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfx1 & Hfx2 & HJ4 & HP4 & HQ4).
cbv zeta in HQ4.
destruct HQ4 as (p1 & p2 & O' & Hp2 & Hp2a & Hp12 & Hfr12 & Hbl & HrepF & HO' & Hstr & HBB4 & Hmle).
set (t := snd (rec_answer (rec_record R0 SRS_FN [x]) (SRS_FN, [x]) (shape_of srs_verb) true)) in *.
set (nT := Z.of_nat (length t) + 1) in *.
set (old := srs_old QB) in *.
pose proof (proj1 HJ4) as HAR4.
(* the old answer's start is no other live block's *)
assert (HOLDs : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros pn Hpn HnO Hf. unfold old, srs_old in Hf. destruct (l_answer QB) as [an|] eqn:Ean.
  - pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. apply HO0 in Han as [HanO _].
    apply HnO. rewrite (srs_same_start ly S W mem md pn an HAR Hpn (HOin _ HanO) Hf). exact HanO.
  - destruct pn as [b m]. destruct (srs_blk_bounds ly S W mem md b m HAR Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
(* a block of the entry is one of the call of xstrdup's, or one rec_calls_free freed (one of O) *)
assert (HSc : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B lyc Sc) \/ In pn F).
{ intros pn Hpn. apply in_app_or. exact (Permutation_in _ HPERM Hpn). }
assert (HFnot : forall pn, In pn F -> ~ In pn (ablocks B lyc Sc)).
{ intros pn HFi HSc'. exact (srs_dup_false ly S W mem md (ablocks B lyc Sc) F pn HAR HPERM HSc' HFi). }
(* a block live at the entry with the old answer's start is the old answer, one of O *)
assert (HOLDin' : forall pn, In pn (ablocks B ly S) -> fst pn = old -> In pn O).
{ intros pn Hpn Hf. unfold old, srs_old in Hf. destruct (l_answer QB) as [an|] eqn:Ean.
  - pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. apply HO0 in Han as [HanO _].
    rewrite (srs_same_start ly S W mem md pn an HAR Hpn (HOin _ HanO) Hf). exact HanO.
  - destruct pn as [b m]. destruct (srs_blk_bounds ly S W mem md b m HAR Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
(* a block live at the entry and still at the jump that is one of answer's two copies is the old answer *)
assert (HnewS' : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly3 S3) -> (pn = (p1, nT) \/ pn = (p2, nT)) ->
  In pn O).
{ intros pn Hpn H3 Heq. destruct (Z.eq_dec (fst pn) old) as [Ho | Ho]; [exact (HOLDin' pn Hpn Ho)|].
  exfalso. destruct (Hfr12 pn H3 Ho) as [N1 N2]. destruct Heq as [Heq | Heq]; [exact (N1 Heq) | exact (N2 Heq)]. }
assert (HxF : forall n, In (p, n) (ablocks B lyc Sc) -> False).
{ intros n Hin. pose proof (srs_head_apart ly2 S2 W2 mem2 md2 _ _ (p, n) HAR2 Hperm2 Hin) as D. cbn [fst snd] in D.
  destruct (srs_blk_bounds lyc Sc Wc memT mdT p n HARc Hin) as (_ & _ & _ & _ & Hnr1).
  destruct (srs_blk_bounds ly2 S2 W2 mem2 md2 p _ HAR2 HPIN2) as (_ & _ & _ & _ & HL1). lia. }
unfold apost_baseF. exists fx1, ly4, S4, regs4, mem4, md4.
split; [rewrite A1; reflexivity|].
split; [exact Hfx1|]. split; [exact Hfx2|].
split.
{ assert (HJF : ajournal SEGS B SRS_STK sp0 (srs_FP O) ly S W mem md ([] ++ []) ly4 S4 W4 mem4 md4
    ((k + EV_XSTRDUP + EV_REC_SHAPE_OF) + EV_ANSWER)).
  { eapply ajournal_sub_wide.
    all: try first [exact LAWS | exact Hsegs | exact HJ3 | exact HJ4].
    all: lazymatch goal with
    | |- forall a, inFP _ a -> awr_byte _ _ _ _ _ _ _ _ _ _ a =>
        intros a Ha; eapply srs_awr_ans; [|exact Ha];
        intros pn Hpn Hf; pose proof (HOLD0 pn Hpn Hf) as H0; split; [exact (proj1 (proj1 (HO0 pn) H0)) | exact (HO1in pn Hpn)]
    | |- forall a, inFP _ a -> _ => intros a _ Ha Hn; exfalso; apply Hn; rewrite SPA, HAS; rewrite HST in Ha; exact Ha
    | |- _ => rewrite ?SPA, ?HAS, ?HST; lia
    end. }
  cbn [app] in HJF. apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF).
  unfold EV_SUP_RESET, EV_XSTRDUP, EV_REC_SHAPE_OF. rewrite Hk, HFN. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPA HP4)|].
exists (fst (rec_answer (rec_record R0 SRS_FN [x]) (SRS_FN, [x]) (shape_of srs_verb) true)), t, p2, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact Hp2|]. split; [exact Hp2a|]. split; [exact HrepF|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[Hpn1 _] | ->].
  - destruct Hpn1 as [<- | H0]; [|left; exact (proj1 (proj1 (HO0 pn) H0))].
    destruct (in_dec recb_pair_dec (p, Z.of_nat (length x) + 1) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
    destruct (HSc _ Hin) as [H | H]; [exfalso; exact (HxF _ H) | exact (HFO _ H)].
  - destruct (in_dec recb_pair_dec (p1, nT) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
    destruct (HSc _ Hin) as [H | H]; [exact (HnewS' _ Hin (HIN3 _ H) (or_introl eq_refl)) | exact (HFO _ H)]. }
split; [apply Hbl; right; right; reflexivity|].
split.
{ intros pn Hpn HnO Heq. apply HnO. destruct (HSc pn Hpn) as [H | H];
  [exact (HnewS' pn Hpn (HIN3 _ H) (or_intror Heq)) | exact (HFO _ H)]. }
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hf & Hpn).
  pose proof HrepF as (QF & HQF & HOQF). pose proof (lay_blocks_in _ _ _ _ _ _ HQF pn (proj1 (HOQF pn) Hpn)) as Hpn4.
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq4.
  pose proof (srs_same_start ly4 S4 W4 mem4 md4 pn (p2, nT) HAR4 Hpn4 Hq4 Hf) as ->.
  apply HO' in Hpn as [[Hpn1 Hfo] | Heq];
  [exact (proj2 (Hfr12 _ (HO1in _ Hpn1) Hfo) eq_refl) | injection Heq as Heq; exact (Hp12 (eq_sym Heq))]. }
split; [exact Hstr|].
split.
{ intros pn Hpn HnO.
  assert (H3 : In pn (ablocks B ly3 S3)).
  { destruct (HSc pn Hpn) as [H | H]; [exact (HIN3 _ H) | exfalso; exact (HnO (HFO _ H))]. }
  assert (H4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact H3 | exact (HOLDs pn Hpn HnO)]).
  split; [exact H4|].
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq4.
  destruct pn as [b m]. cbn [fst snd].
  assert (Hne : (b, m) <> (p2, nT)) by exact (proj2 (Hfr12 (b, m) H3 (HOLDs (b, m) Hpn HnO))).
  destruct (srs_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 H4) as (_ & _ & Hm0 & Hmr & _).
  destruct (srs_blk_bounds ly4 S4 W4 mem4 md4 p2 nT HAR4 Hq4) as (_ & _ & Hn0 & Hnr & _).
  unfold iv_apart. destruct (srs_blk_apart ly4 S4 W4 mem4 md4 b m p2 nT HAR4 H4 Hq4 Hne); lia. }
split.
{ intros pn Hpn. apply Hbl in Hpn as [[H3 Hf] | [-> | ->]].
  - apply (Permutation_in _ Hperm3), (Permutation_in _ Hperm2) in H3. destruct H3 as [<- | H3].
    + right; left. apply HO'. left. split; [left; unfold LIVE_XSTRDUP; reflexivity | exact Hf].
    + destruct (in_dec recb_pair_dec pn O0) as [H0 | H0n].
      * right; left. apply HO'. left. split; [right; exact H0 | exact Hf].
      * left. split.
        -- apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact H3.
        -- intros HinO. destruct (in_dec recb_pair_dec pn F) as [HFi | HFn]; [exact (HFnot _ HFi H3)|].
           apply H0n. apply HO0. split; [exact HinO | exact HFn].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ assert (BBc : blocks_bytes Sc <= blocks_bytes S).
  { rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPERM), bsum_app.
    pose proof (srs_bsum_nonneg ly S W mem md F HAR
      ltac:(intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hpn)).
    lia. }
  rewrite ES3 in HBB4. unfold LIVE_SUP_RESET. rewrite HM. fold x. fold t. lia. }
apply (mle_weaken MT S S4 _ _ MTL (mle_station MT S S3 S4 _ _ MTL MLEJ Hmle)).
unfold XM_SUP_RESET. rewrite HM. fold x. rewrite <- HFN. unfold t. lia.
Qed.

End e.
End f.
End d.


(* ---------------------------------------------------------------------------------------------------------
   The entry segment (0x8b6d8 .. the call of xstrdup 0x8b78c) and the member's theorem.
   --------------------------------------------------------------------------------------------------------- *)

Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees (sup_reset_c.v:67-70) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the premise a statement revision deleted from every statement, carried as ONE named hypothesis by every walk
   that hands an image literal to astr_argA's read-only arm (decided 2026-10-29) *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI).
(* the walk hypotheses, with cgif's names *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the program's statics (the recorder walks' shared names, RecBTemplate.v forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the per-binary record facts (one name and form for every walk; CmdRecFacts.v is to prove each): the
   read-only bytes the program loads are those of the image wherever
   arodata_okP holds, arodata_okP survives every journal whose footprint is off the read-only range (CmdBase.v's
   arodata_ok_journalP with RRO), a string's word tail survives a callee that keeps its bytes, and the read-only
   range is image bytes outside the program's statics *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_atail_kept : forall ly S W mem md ly' S' W' mem' md' p n e,
AR SEGS B ly S W mem md -> AR SEGS B ly' S' W' mem' md' ->
((In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= e < p + n) \/
 (in_roP SEGS RLO RHI e /\ ~ Exists (in_zr e) (as_owned_static B))) ->
atail_vis SEGS W mem e -> atail_vis SEGS W' mem' e.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the image facts of the binary (the kit's CmdRecBase.cmd_img_facts; RecBClosed closes it by cmd_img_facts_tfib) *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* ---------- small facts of the entry segment ---------- *)

Lemma srs_awr_grec : forall STK sp O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (srs_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. pose proof (recb_grec_in a Ha) as HP.
right; right; right; right; left.
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma srs_sh_ok_E : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> srs_slot_ok c ->
ew E SRS_SB = Z_to_bv 64 SB -> ew E SRS_C = Z_to_bv 64 c ->
sh_ok SEGS srs_Bx srs_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hc ESB EC.
destruct (srs_slot_bounds c Hc) as (Hcb & Hc8 & _).
unfold sh_ok, srs_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E srs_Bx SRS_C c CALL_SIZE c 0 CALL_SIZE).
- exact (srs_slot_addressable B HB ly S W mem md c HAR Hc).
- unfold srs_Bx. apply U_atom; [exact ESB | cbv [SB SHADOW_OFF]; lia].
- apply U_atom; [exact EC | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* the slot the table arm computes: g_rec + 16 + 56 * ncalls, as the executor folds the two shifts and the
   subtraction (slli 6 / slli 3 / sub) into one multiplication *)
Lemma srs_mul56 : forall n, 0 <= n < 16 ->
mul_div M_MUL (Z_to_bv 64 n) (Z_to_bv 64 56) = Z_to_bv 64 (n * 56).
Proof.
intros n Hn.
assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15) by lia.
repeat (destruct Hc as [-> | Hc]); [..| subst n]; apply bv_eq; vm_compute; reflexivity.
Qed.

(* an 8-byte word that the run did not write keeps the visibility of a string's terminator word *)
Lemma srs_atail_word_kept : forall (W : world SEGS) m m' e c,
c mod 8 = 0 -> ~ (c <= e < c + 8) -> 0 <= e < 2 ^ 64 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW W m' a = rdW W m a) ->
atail_vis SEGS W m e -> atail_vis SEGS W m' e.
Proof.
intros W m m' e c Hc8 Hne He HK HT a Ha.
assert (Hw : ~ (c <= a < c + 8)).
{ intros Hin.
  assert (Hq1 : a / 8 = e / 8).
  { symmetry. apply (Z.div_unique a 8 (e / 8) (a - 8 * (e / 8))); [|lia].
    pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia. }
  assert (Hq2 : a / 8 = c / 8).
  { symmetry. apply (Z.div_unique a 8 (c / 8) (a - 8 * (c / 8))); [|lia].
    pose proof (Z.div_mod c 8 ltac:(lia)). lia. }
  pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  pose proof (Z.div_mod c 8 ltac:(lia)). lia. }
assert (Har : 0 <= a < 2 ^ 64).
{ pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)).
  assert (e / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite (HK a Har Hw). exact (HT a Ha).
Qed.

(* a string argument has no byte in the slot: the slot lies in a program static, the string in a live block or in
   the read-only image, neither of which holds one *)
Lemma srs_argA_off_slot : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v c,
AR SEGS B ly1 S1 W1 mem1 md1 -> astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
(forall a, c <= a < c + 8 -> Exists (in_zr a) recb_PG) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> ~ (c <= p + i < c + 8).
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v c HAR H Hc i Hi Hs. pose proof (Hc _ Hs) as HP. cbn [astr_argA] in H.
destruct H as (_ & _ & _ & [((b & m & Hin & Hb1 & Hb2) & _) | (Hro & _)]).
- destruct (srs_blk_bounds B ly1 S1 W1 mem1 md1 b m HAR Hin) as (_ & _ & Hm0 & Hmr & _).
  exact (srs_blk_noprog B cmd_prog_img ly1 S1 W1 mem1 md1 b m (p + i) HAR Hin ltac:(lia) HP).
- destruct (Hro i Hi) as (Hr & _). exact (proj2 (cmd_ro_prog_apart _ Hr) HP).
Qed.

(* the string argument across a step that keeps the recorder's own blocks' bytes and the read-only image: what
   record() does to it (the frame, g_rec.ncalls, the slot, and the spill's argument blocks) *)
Lemma srs_arg_kept : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O pw x,
AR SEGS B ly S W mem md -> AR SEGS B lyc Sc Wc memc mdc ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k -> rdW Wc memc a = rdW W mem a) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw (Some x) ->
atail_vis SEGS W mem (pw + Z.of_nat (length x)) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] pw (Some x) /\
atail_vis SEGS Wc memc (pw + Z.of_nat (length x)).
Proof.
intros ly S W mem md lyc Sc Wc memc mdc O pw x HAR HARc HRO HROc Hblk Hbytes HA HT.
cbn [astr_argA] in HA |- *.
destruct HA as (Hp0 & HS & Hlen & [((b & k & Hbk & Hble & Hhi) & Hap) | (Hro & Hra & Hhv)]).
- assert (HnO : ~ In (b, k) O).
  { intros Hin. rewrite Forall_forall in Hap. pose proof (Hap (b, k) Hin) as Hd. cbn [fst snd] in Hd.
    unfold iv_apart in Hd. lia. }
  assert (HK : forall a, b <= a < b + k -> rdW Wc memc a = rdW W mem a)
    by (intros a Ha; exact (Hbytes b k a Hbk HnO Ha)).
  split.
  + split; [exact Hp0|]. split.
    * apply (srs_astr_kept (rdW W mem)); [exact HS|]. intros i Hi. apply HK. lia.
    * split; [exact Hlen|]. left. split; [|apply Forall_nil].
      exists b, k. split; [exact (Hblk (b, k) Hbk HnO) | split; [exact Hble | exact Hhi]].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc b k (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | left; split; [exact Hbk | split; [exact (Hblk (b, k) Hbk HnO) | lia]] | exact HT].
- split.
  + split; [exact Hp0|]. split.
    * apply (srs_astr_kept (rdW W mem)); [exact HS|]. intros i Hi.
      destruct (Hro i ltac:(lia)) as (Hr & Ho & He). rewrite (HROc _ Hr Ho He), (HRO _ Hr Ho He). reflexivity.
    * split; [exact Hlen|]. right. split; [exact Hro|]. split; [exact Hra | exact Hhv].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc 0 0 (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | right | exact HT].
    destruct (Hro (Z.of_nat (length x)) ltac:(lia)) as (Hr & Ho & _). split; [exact Hr | exact Ho].
Qed.

(* the walk's tactics again: an Ltac of a closed section is out of scope here *)
Ltac srs2_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.
Ltac srs2_reg1 E34 E32 G8 G18 G19 G20 :=
lazymatch goal with |- getr ?rg ?r = sv_denot ?E (sr_get ?a ?r) =>
  let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v end;
first
[ let G := fresh in pose proof G20 as G; rewrite <- (srs_shx4_denot _ _ E34 E32) in G by lia; exact G
| cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; exact G8
| cbn [sv_denot]; rewrite E34, unsigned_lit_small by lia; exact G18
| cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact G19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [ symmetry; apply srs_E_reg; reflexivity | symmetry; apply getr_zero | reflexivity ] ].
Ltac srs2_regs_ok E34 E32 G8 G18 G19 G20 :=
apply regs_ok_by_cases; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [all_regs In] in Hr;
repeat (destruct Hr as [<- | Hr]; [srs2_reg1 E34 E32 G8 G18 G19 G20 | ]); try (destruct Hr; fail).
Ltac srs2_awr UC Hc :=
lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end;
apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|];
eapply awr_ok_cons_gen; [reflexivity | exact UC | | apply awr_ok_nil];
cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
apply (srs_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ _ a Hc); unfold CALL_SIZE; lia.

(* ---------- the seed of the join segment: the slot's write window is its first 8 bytes ---------- *)
(* the slot as the segment from the join writes it: c->fn and c->nargs (the 8 bytes record() fills); c->args[0]
   is written after xstrdup returns, in the segment lib/A/Prog/sup_reset.v's srs_SX walks *)
Definition srs_slot8 (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some SRS_C) 0 CALL_SIZE 0 8 cs.

Lemma srs_seed8 : forall pc sregs cs W1 (regs1 regs0 : bvmap 5 word) mem1 ly1 S1 md1 n c,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 - SRS_FRAME -> bv_unsigned (getr regs1 2) mod 16 = 0 ->
0 <= n <= 16 -> srs_slot_ok c ->
regs_ok (srs_E regs1 regs0 n c) sregs regs1 ->
srs_frame_at (mrestrict (w_H W1) mem1) (bv_unsigned (getr regs1 2)) regs0 ->
regions_wf [srs_frame; srs_slot8 cs] = true ->
Forall (YP09.chunk_ok SEGS (srs_E regs1 regs0 n c) (mrestrict (w_H W1) mem1) c) cs ->
st_ok_pi SEGS VAL (srs_E regs1 regs0 n c) (mkSS pc sregs [srs_frame; srs_slot8 cs] None srs_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS srs_Bx srs_SH (srs_E regs1 regs0 n c) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs cs W1 regs1 regs0 mem1 ly1 S1 md1 n c HAR Hsp Hsp16 Hn Hc HREG HFR Hwf HCS.
destruct (srs_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (sp1 := bv_unsigned (getr regs1 2)) in *.
set (E := srs_E regs1 regs0 n c) in *.
assert (E2 : bv_unsigned (ew E 2) = sp1) by (subst E sp1; rewrite (srs_E_reg _ _ _ _ 2 2%bv eq_refl); reflexivity).
assert (EC : ew E SRS_C = Z_to_bv 64 c) by (subst E; exact (srs_E_extra regs1 regs0 n c 2 ltac:(lia))).
assert (UC : bv_unsigned (ew E SRS_C) = c)
  by (rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split; [| exact (srs_sh_ok B HB ly1 S1 W1 mem1 md1 regs1 regs0 n c HAR Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- exact Hwf.
- unfold srs_frame, srs_slot8. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. unfold SRS_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
    let j := eval compute in (k - 35)%nat in let r := eval compute in (nth j srs_saved 0) in
    apply (chunk_ok_val SEGS E _ sp1 off 8 (SOff k 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r))));
    [ cbn [sv_denot]; rewrite Z.add_0_r; subst E;
      rewrite (srs_E_extra_at regs1 regs0 n c k ltac:(lia)); cbn [Nat.sub nth srs_extra srs_saved map app];
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as HR;
      change (bv_modulus 64) with (2 ^ 64) in HR; cbn; lia
    | cbn; lia
    | replace (sp1 + off) with (sp1 + 40 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
  + rewrite UC. split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold A_REC_SPILL, CALL_SIZE in *; lia|].
    split; [| exact HCS].
    intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1 _ HAR).
    apply (srs_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia].
- apply pairwise_disjoint_of_extents. unfold srs_frame, srs_slot8, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, UC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SRS_FRAME, CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
- apply (srs_facts_ok VOBJS regs1 regs0 n c);
  [unfold SRS_FRAME in Hsp; fold sp1; lia | exact Hsp16 | exact Hn | exact Hc].
Qed.

(* the default "(null)" (.str.47, 0x22480) as xstrdup's pre asks it: astr_argA's read-only arm, whose read-only
   bytes come from CMD_RO_IN and whose record facts are decided here, and the word tail of its terminator *)
Lemma srs_null_argA : forall ly1 S1 (W1 : world SEGS) mem1 O1, cmd_ro_ok (rdW W1 mem1) ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 0x22480 (Some srs_null) /\
atail_vis SEGS W1 mem1 (0x22480 + Z.of_nat (length srs_null)).
Proof.
intros ly1 S1 W1 mem1 O1 HROd.
assert (Hend : In (0x22480 + Z.of_nat (length srs_null)) cmd_ro_ends).
{ change (0x22480 + Z.of_nat (length srs_null)) with 0x22486. unfold cmd_ro_ends.
  repeat first [left; reflexivity | right]. }
assert (HL : abytes_atR (rdW W1 mem1) 0x22480 RO_lit_22480).
{ destruct HROd as [HRB _]. unfold cmd_ro_bytes in HRB.
  repeat match type of HRB with
  | abytes_atR _ 0x22480 _ /\ _ => exact (proj1 HRB)
  | _ /\ _ => apply proj2 in HRB
  end. }
assert (HVS : astr_atR (rdW W1 mem1) 0x22480 srs_null).
{ split; [apply (srs_bytes_eq _ _ _ _ HL); vm_compute; reflexivity|].
  apply srs_no_zero. vm_compute. reflexivity. }
split; [|exact (CmdRecRest.cmd_tail_vis SEGS B LAWS HB W1 mem1 _ HROd Hend)].
cbn [astr_argA]. split; [lia|]. split; [exact HVS|]. split; [vm_compute; congruence|].
right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | exact Hend]]].
intros i Hi. change (Z.of_nat (length srs_null) + 1) with 7 in Hi. split.
- assert (HRI : forall j, 0 <= j < 7 -> in_roP SEGS RLO RHI (0x22480 + j)).
  { clear - CMD_RO_IN. pose proof CMD_RO_IN as HROIN. unfold cmd_ro_in in HROIN.
    repeat match type of HROIN with
    | (forall j, 0 <= j < 7 -> _ (0x22480 + j)) /\ _ => exact (proj1 HROIN)
    | _ /\ _ => apply proj2 in HROIN
    end. }
  exact (HRI i Hi).
- apply (srs_unowned_rng B HB 0x22480 7); [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

(* the seven callee-saved registers above s4, which neither arm touches *)
Lemma srs_r7 : forall (r1 r2 : bvmap 5 word),
getr r1 21%bv = getr r2 21%bv -> getr r1 22%bv = getr r2 22%bv -> getr r1 23%bv = getr r2 23%bv ->
getr r1 24%bv = getr r2 24%bv -> getr r1 25%bv = getr r2 25%bv -> getr r1 26%bv = getr r2 26%bv ->
getr r1 27%bv = getr r2 27%bv -> forall r, 21 <= r <= 27 -> getr r1 (Z_to_bv 5 r) = getr r2 (Z_to_bv 5 r).
Proof.
intros r1 r2 H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hc : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; assumption.
Qed.

(* ---------- the join of record()'s two arms (0x8b74c) to the call of xstrdup (0x8b78c) ---------- *)
Definition srs_join_spec : Prop := forall ly S W regs mem md ch pw which R O Q
  lyc Sc Wc memJ mdJ k lyB SBa WB memB R0 O0 F (regsJ : bvmap 5 word),
srs_pre B MT ly S W regs mem md ch pw which R O ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
srs_mid B MT ly S W regs mem md R O lyc Sc Wc memJ mdJ k lyB SBa WB memB R0 O0 F ->
srs_recmem (rdW Wc memJ) (rdW WB memB) (srs_slot R0) 0 ->
srs_ncalls_ok (rdW Wc memJ) R0 ->
getr regsJ 2 = w64 (spZ regs - SRS_FRAME) ->
getr regsJ 3 = w64 (as_gp B) -> getr regsJ 4 = w64 (as_tp B) ->
getr regsJ 8 = w64 (srs_slot R0) -> getr regsJ 9 = w64 pw -> getr regsJ 19 = w64 SB ->
getr regsJ 21 = getr regs 21 -> getr regsJ 22 = getr regs 22 -> getr regsJ 23 = getr regs 23 ->
getr regsJ 24 = getr regs 24 -> getr regsJ 25 = getr regs 25 -> getr regsJ 26 = getr regs 26 ->
getr regsJ 27 = getr regs 27 ->
(forall x, which = Some x ->
   astr_argA B lyc Sc (rdW Wc memJ) (in_roP SEGS RLO RHI) [] pw (Some x) /\
   atail_vis SEGS Wc memJ (pw + Z.of_nat (length x))) ->
SRr SEGS Wc (mkCfg (mkst regsJ (Z_to_bv 64 (BASE + SRS_JOIN)) memJ (seg_rom SEGS)) mdJ)
(apost_baseF SEGS B SRS_STK (srs_FP O) regs ly S W mem md (EV_SUP_RESET R) (srs_Q B MT ly S R O which)).

Lemma srs_join : srs_SX_spec B MT -> srs_join_spec.
Proof.
intros HX. unfold srs_join_spec.
intros ly S W regs mem md ch pw which R O Q lyc Sc Wc memJ mdJ k lyB SBa WB memB R0 O0 F regsJ
  PRE HQ HOQ MID RM NC R2 R3 R4 R8 R9 R19 R21 R22 R23 R24 R25 R26 R27 HARG.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & HRND & HROD & HRO & Hpwr & H10 & HA & HREP & HFR8 & HEV & HLIVE & HMOK & HG2).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk & HFRM & HREPB & HSP0 & HLEN0 & HREC0 & HKO0 & HIO0 & HPERM & HFO & HO0 & HFN & MLE).
pose proof (proj1 HJ) as HARc.
set (sp0 := spZ regs) in *.
set (c := srs_slot R0) in *.
assert (HST : SRS_STK = 16592) by reflexivity.
assert (Hn16 : (length (r_calls R0) <= 16)%nat)
  by (destruct HREPB as (QB & (_ & _ & _ & (GG1 & _) & _) & _); exact GG1).
assert (Hsl : srs_slot_ok c) by exact (srs_slot_ok_of R0 Hn16).
destruct (srs_slot_bounds c Hsl) as (Hcb & Hc8 & Hch').
set (nn := Z.of_nat (length (r_calls R0))) in *.
assert (Hnn : 0 <= nn <= 16) by (subst nn; lia).
assert (R2u : bv_unsigned (getr regsJ 2) = sp0 - SRS_FRAME)
  by (rewrite R2; unfold w64; apply unsigned_lit_small; unfold SRS_FRAME; lia).
assert (Hcr : 0 <= c < 2 ^ 40).
{ pose proof Hcb as Hx. cbv [A_G_REC A_REC_SPILL OFF_CALLS] in Hx. lia. }
(* pw is an address of the machine: the statement's own premise *)
(* the environment of the join segment *)
assert (E34 : ew (srs_E regsJ regs nn c) 34 = Z_to_bv 64 c)
  by (rewrite (srs_E_extra_at regsJ regs nn c 34 ltac:(lia)); reflexivity).
assert (E32 : ew (srs_E regsJ regs nn c) 32 = Z_to_bv 64 SB)
  by (rewrite (srs_E_extra_at regsJ regs nn c 32 ltac:(lia)); reflexivity).
assert (E9 : ew (srs_E regsJ regs nn c) 9 = Z_to_bv 64 pw)
  by (rewrite (srs_E_reg regsJ regs nn c 9%nat 9%bv eq_refl); exact R9).
assert (E3r : ew (srs_E regsJ regs nn c) 3 = getr regsJ 3) by (apply srs_E_reg; reflexivity).
assert (E4r : ew (srs_E regsJ regs nn c) 4 = getr regsJ 4) by (apply srs_E_reg; reflexivity).
assert (E21 : ew (srs_E regsJ regs nn c) 21 = getr regsJ 21) by (apply srs_E_reg; reflexivity).
assert (E22 : ew (srs_E regsJ regs nn c) 22 = getr regsJ 22) by (apply srs_E_reg; reflexivity).
assert (E23 : ew (srs_E regsJ regs nn c) 23 = getr regsJ 23) by (apply srs_E_reg; reflexivity).
assert (E24 : ew (srs_E regsJ regs nn c) 24 = getr regsJ 24) by (apply srs_E_reg; reflexivity).
assert (E25 : ew (srs_E regsJ regs nn c) 25 = getr regsJ 25) by (apply srs_E_reg; reflexivity).
assert (E26 : ew (srs_E regsJ regs nn c) 26 = getr regsJ 26) by (apply srs_E_reg; reflexivity).
assert (E27 : ew (srs_E regsJ regs nn c) 27 = getr regsJ 27) by (apply srs_E_reg; reflexivity).
assert (Usp : bv_unsigned (ew (srs_E regsJ regs nn c) 2) = sp0 - SRS_FRAME)
  by (rewrite (srs_E_reg regsJ regs nn c 2%nat 2%bv eq_refl); exact R2u).
assert (E293 : ew (srs_E regsJ regs nn c) 293 = Z_to_bv 64 0x22480).
{ pose proof (srs_E_img regsJ regs nn c 293%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H293.
  change (VAL 293%nat) with (VAL (A_OBJ 52)) in H293.
  rewrite (VOBJS 52%nat ltac:(vm_compute; lia)) in H293.
  apply bv_eq. rewrite H293. rewrite unsigned_lit_small by lia.
  vm_compute. reflexivity. }
assert (G8 : getr regsJ 8 = Z_to_bv 64 c) by exact R8.
assert (G19 : getr regsJ 19 = Z_to_bv 64 SB) by exact R19.
assert (UC : bv_unsigned (ew (srs_E regsJ regs nn c) SRS_C) = c).
{ change SRS_C with 34%nat. rewrite E34. apply unsigned_lit_small. lia. }
assert (UC34 : bv_unsigned (ew (srs_E regsJ regs nn c) 34) = c) by exact UC.
pose proof (srs_E_img regsJ regs nn c) as HEI.
destruct (srs_seed8 SRS_JOIN srs_regsC [] Wc regsJ regs memJ lyc Sc mdJ nn c HARc
  ltac:(rewrite R2u; unfold SRS_FRAME; lia)
  ltac:(rewrite R2u; replace (sp0 - SRS_FRAME) with (sp0 + (-3) * 16) by (unfold SRS_FRAME; lia);
        rewrite Z_mod_plus_full; exact Hal16)
  Hnn Hsl
  ltac:(srs2_regs_ok E34 E32 G8 G8 G19 G8)
  ltac:(rewrite R2u; exact HFRM)
  ltac:(vm_compute; reflexivity)
  ltac:(apply Forall_nil)) as [HS SHOK].
set (E := srs_E regsJ regs nn c) in *.
(* the bytes the whole segment writes: the slot's first 8 bytes *)
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
(* 0x8b74c .. 0x8b778: the two inline checks, c->fn := 10, c->nargs := 0 *)
paj_run_tok RUN HS HJ SHOK srs_Bspan.
{ srs2_awr UC Hsl. }
srs2_md.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms) a = rdW Wc memJ a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memJ (ms_mem ms) (fun a => c <= a < c + 8) HFr).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UC34 in Hrr; lia|]).
  destruct Hin. }
(* the state at the branch: the slot's first 8 bytes are the walk's, every other byte is the join's *)
assert (Hceil0 : alloc_ceiling <= sp0 - 48) by (rewrite HST in Hslo; lia).
assert (Hcimg : forall a, c <= a < c + 8 -> Exists (in_zr a) recb_PG)
  by (intros a Ha; apply (srs_in_PG_slot c a Hsl); unfold CALL_SIZE; lia).
assert (Hcb8 : c + 8 <= alloc_ceiling) by (unfold A_REC_SPILL in Hcb; lia).
assert (RM1 : srs_recmem (rdW Wc (ms_mem ms)) (rdW WB memB) c 8).
{ intros a Ha Hn Hs. rewrite (KEEP1 a ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia) Hs).
  exact (RM a Ha Hn ltac:(lia)). }
assert (NC1 : srs_ncalls_ok (rdW Wc (ms_mem ms)) R0).
{ apply (srs_aval_kept (rdW Wc memJ)); [exact NC|]. intros kk Hkk. apply KEEP1;
  unfold A_G_REC, OFF_NCALLS, OFF_CALLS, A_REC_SPILL in *; lia. }
assert (FRM1 : srs_frame_at (mrestrict (w_H Wc) (ms_mem ms)) (sp0 - SRS_FRAME) regs).
{ intros j r Hjr. apply (srs_val_kept Wc Wc memJ (ms_mem ms)); [exact (HFRM j r Hjr)|].
  assert (Hj : (j < 6)%nat) by (change 6%nat with (length srs_saved); apply nth_error_Some; rewrite Hjr; discriminate).
  intros kk Hkk. apply KEEP1; unfold SRS_FRAME in *; lia. }
assert (KO1 : forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc (ms_mem ms) (fst pn + i) = rdW WB memB (fst pn + i)).
{ intros [b m] i Hpn Hi. cbn [fst snd] in *.
  destruct (srs_blk_bounds B lyc Sc Wc memJ mdJ b m HARc (HIO0 _ Hpn)) as (Hb0 & Hb1 & Hm0 & Hmr & _).
  rewrite KEEP1; [exact (HKO0 (b, m) i Hpn Hi) | lia |].
  intros Hs. apply (srs_blk_noprog B cmd_prog_img lyc Sc Wc memJ mdJ b m (b + i) HARc (HIO0 _ Hpn) ltac:(lia)).
  exact (Hcimg _ Hs). }
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regsJ rr)
  by (intros kk rr Hkk; apply srs_E_reg; exact Hkk).
clearbody E.
psrr_branch_tok RUN BR HS SHOK srs_Bspan.
- (* s1 <> 0, the taken arm (0x8b788): a0 := s1 = pw, the caller's own string *)
  assert (Hpw0 : pw <> 0).
  { rewrite branch_ne_U, (U_atom E 9%nat pw E9 Hpwr) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. intros Hz. apply Hc. rewrite Hz. reflexivity. }
  destruct which as [xx|]; [|exfalso; cbn [astr_argA] in HA; exact (Hpw0 HA)].
  destruct (HARG xx eq_refl) as (HSTRJ & HTAILJ).
  paj_run_tok RUN HS HJ SHOK srs_Bspan.
  { srs2_awr UC Hsl. }
  pmkst HS. srs2_md.
  lazymatch goal with HFx : frame_of E _ (mrestrict _ (ms_mem ms)) (mrestrict _ _) |- _ => rename HFx into HFrA end.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (Q1 : getr (ms_regs ms0) 1 = w64 (BASE + SRS_RETX)) by (rewrite P1; reflexivity).
  assert (Q2 : getr (ms_regs ms0) 2 = w64 (sp0 - SRS_FRAME)) by (rewrite P2, (EE 2%nat 2%bv eq_refl); exact R2).
  assert (Q3 : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3).
  assert (Q4 : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4).
  assert (Q8 : getr (ms_regs ms0) 8 = w64 c) by (rewrite P8, E34; reflexivity).
  assert (Q10 : getr (ms_regs ms0) 10 = w64 pw) by (rewrite P10, E9; reflexivity).
  assert (Q18 : getr (ms_regs ms0) 18 = w64 (c + 4))
    by (rewrite P18; cbn [sv_denot]; rewrite ?E34; unfold w64; rewrite ?unsigned_lit_small by lia; reflexivity).
  assert (Q19 : getr (ms_regs ms0) 19 = w64 SB) by (rewrite P19, E32; reflexivity).
  assert (Q20 : getr (ms_regs ms0) 20 = w64 (SB + (c + 4) / 8)).
  { rewrite P20. unfold w64. rewrite <- (srs_shx4_denot E c E34 E32 Hcr). unfold srs_shx4. cbn [sv_denot].
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
  assert (RS7 : forall r, 21 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { apply srs_r7;
    [ rewrite P21, (EE 21%nat 21%bv eq_refl); exact R21 | rewrite P22, (EE 22%nat 22%bv eq_refl); exact R22
    | rewrite P23, (EE 23%nat 23%bv eq_refl); exact R23 | rewrite P24, (EE 24%nat 24%bv eq_refl); exact R24
    | rewrite P25, (EE 25%nat 25%bv eq_refl); exact R25 | rewrite P26, (EE 26%nat 26%bv eq_refl); exact R26
    | rewrite P27, (EE 27%nat 27%bv eq_refl); exact R27 ]. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun a => c <= a < c + 8) HFrA).
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UC34 in Hrr; lia|]).
    destruct Hin. }
  assert (RM2 : srs_recmem (rdW Wc (ms_mem ms0)) (rdW WB memB) c 8).
  { intros a Ha Hn Hs. rewrite (KEEP2 a ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia) Hs).
    exact (RM1 a Ha Hn Hs). }
  assert (NC2 : srs_ncalls_ok (rdW Wc (ms_mem ms0)) R0).
  { apply (srs_aval_kept (rdW Wc (ms_mem ms))); [exact NC1|]. intros kk Hkk. apply KEEP2;
    unfold A_G_REC, OFF_NCALLS, OFF_CALLS, A_REC_SPILL in *; lia. }
  assert (FRM2 : srs_frame_at (mrestrict (w_H Wc) (ms_mem ms0)) (sp0 - SRS_FRAME) regs).
  { intros j r Hjr. apply (srs_val_kept Wc Wc (ms_mem ms) (ms_mem ms0)); [exact (FRM1 j r Hjr)|].
    assert (Hj : (j < 6)%nat) by (change 6%nat with (length srs_saved); apply nth_error_Some; rewrite Hjr; discriminate).
    intros kk Hkk. apply KEEP2; unfold SRS_FRAME in *; lia. }
  assert (KO2 : forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc (ms_mem ms0) (fst pn + i) = rdW WB memB (fst pn + i)).
  { intros [b m] i Hpn Hi. cbn [fst snd] in *.
    destruct (srs_blk_bounds B lyc Sc Wc memJ mdJ b m HARc (HIO0 _ Hpn)) as (Hb0 & Hb1 & Hm0 & Hmr & _).
    rewrite KEEP2; [exact (KO1 (b, m) i Hpn Hi) | lia |].
    intros Hs. apply (srs_blk_noprog B cmd_prog_img lyc Sc Wc memJ mdJ b m (b + i) HARc (HIO0 _ Hpn) ltac:(lia)).
    exact (Hcimg _ Hs). }
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) srs_frame) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 r HSt ltac:(vm_compute; reflexivity)) as HRgD;
    cbn [ms_mem restrict mkst] in HRgD end.
  pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 0 4%N (SLit 10) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VFND.
  pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 4 4%N (SLit 0) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VNAD.
  change (N.to_nat 4) with 4%nat in VFND, VNAD.
  replace (bv_unsigned (sv_denot E (SLit 10)) mod 2 ^ (8 * Z.of_N 4)) with 10 in VFND by (vm_compute; reflexivity).
  replace (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VNAD by (vm_compute; reflexivity).
  pose proof (aval_mem_view SEGS _ _ _ _ _ VFND) as VFN2. pose proof (aval_mem_view SEGS _ _ _ _ _ VNAD) as VNA2.
  assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms0) a = rdW Wc memJ a)
    by (intros a Ha Hs; rewrite (KEEP2 a Ha Hs); exact (KEEP1 a Ha Hs)).
  assert (HSTR2 : astr_argA B lyc Sc (rdW Wc (ms_mem ms0)) (in_roP SEGS RLO RHI) [] pw (Some xx)).
  { apply (srs_argA_kept B _ _ (rdW Wc memJ)); [exact HSTRJ|]. intros i Hi. apply KEEPJ.
    - exact (srs_argA_range B cmd_ro_prog_apart lyc Sc Wc memJ mdJ [] pw xx HARc HSTRJ i Hi).
    - exact (srs_argA_off_slot lyc Sc Wc memJ mdJ [] pw xx c HARc HSTRJ Hcimg i Hi). }
  assert (HTAIL2 : atail_vis SEGS Wc (ms_mem ms0) (pw + Z.of_nat (length xx))).
  { apply (srs_atail_word_kept Wc memJ (ms_mem ms0) _ c Hc8).
    - exact (srs_argA_off_slot lyc Sc Wc memJ mdJ [] pw xx c HARc HSTRJ Hcimg (Z.of_nat (length xx)) ltac:(lia)).
    - exact (srs_argA_range B cmd_ro_prog_apart lyc Sc Wc memJ mdJ [] pw xx HARc HSTRJ (Z.of_nat (length xx))
        ltac:(lia)).
    - exact KEEPJ.
    - exact HTAILJ. }
  exact (HX ly S W regs mem md ch pw (Some xx) R O Q lyc Sc Wc (ms_mem ms0) _ k lyB SBa WB memB R0 O0 F
    (ms_regs ms0) pw PRE HQ HOQ
    (conj HJ (conj Hk (conj FRM2 (conj HREPB (conj HSP0 (conj HLEN0 (conj HREC0 (conj KO2 (conj HIO0
      (conj HPERM (conj HFO (conj HO0 (conj HFN MLE)))))))))))))
    RM2 NC2 VFN2 VNA2 Q1 Q2 Q3 Q4 Q8 Q18 Q19 Q20 Q10 RS7 HSTR2 HTAIL2).
- (* s1 = 0 (0x8b780): s1 := "(null)" (0x22480), a0 := s1 *)
  assert (Hpw0 : pw = 0).
  { rewrite branch_ne_U, (U_atom E 9%nat pw E9 Hpwr) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. rewrite Hc. reflexivity. }
  destruct which as [xx|]; [exfalso; cbn [astr_argA] in HA; destruct HA as (HA0 & _); exact (HA0 Hpw0)|].
  paj_run_tok RUN HS HJ SHOK srs_Bspan.
  { srs2_awr UC Hsl. }
  pmkst HS. srs2_md.
  lazymatch goal with HFx : frame_of E _ (mrestrict _ (ms_mem ms)) (mrestrict _ _) |- _ => rename HFx into HFrA end.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (Q1 : getr (ms_regs ms0) 1 = w64 (BASE + SRS_RETX)) by (rewrite P1; reflexivity).
  assert (Q2 : getr (ms_regs ms0) 2 = w64 (sp0 - SRS_FRAME)) by (rewrite P2, (EE 2%nat 2%bv eq_refl); exact R2).
  assert (Q3 : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3).
  assert (Q4 : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4).
  assert (Q8 : getr (ms_regs ms0) 8 = w64 c) by (rewrite P8, E34; reflexivity).
  assert (Q10 : getr (ms_regs ms0) 10 = w64 0x22480) by (rewrite P10, E293; reflexivity).
  assert (Q18 : getr (ms_regs ms0) 18 = w64 (c + 4))
    by (rewrite P18; cbn [sv_denot]; rewrite ?E34; unfold w64; rewrite ?unsigned_lit_small by lia; reflexivity).
  assert (Q19 : getr (ms_regs ms0) 19 = w64 SB) by (rewrite P19, E32; reflexivity).
  assert (Q20 : getr (ms_regs ms0) 20 = w64 (SB + (c + 4) / 8)).
  { rewrite P20. unfold w64. rewrite <- (srs_shx4_denot E c E34 E32 Hcr). unfold srs_shx4. cbn [sv_denot].
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
  assert (RS7 : forall r, 21 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { apply srs_r7;
    [ rewrite P21, (EE 21%nat 21%bv eq_refl); exact R21 | rewrite P22, (EE 22%nat 22%bv eq_refl); exact R22
    | rewrite P23, (EE 23%nat 23%bv eq_refl); exact R23 | rewrite P24, (EE 24%nat 24%bv eq_refl); exact R24
    | rewrite P25, (EE 25%nat 25%bv eq_refl); exact R25 | rewrite P26, (EE 26%nat 26%bv eq_refl); exact R26
    | rewrite P27, (EE 27%nat 27%bv eq_refl); exact R27 ]. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun a => c <= a < c + 8) HFrA).
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UC34 in Hrr; lia|]).
    destruct Hin. }
  assert (RM2 : srs_recmem (rdW Wc (ms_mem ms0)) (rdW WB memB) c 8).
  { intros a Ha Hn Hs. rewrite (KEEP2 a ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia) Hs).
    exact (RM1 a Ha Hn Hs). }
  assert (NC2 : srs_ncalls_ok (rdW Wc (ms_mem ms0)) R0).
  { apply (srs_aval_kept (rdW Wc (ms_mem ms))); [exact NC1|]. intros kk Hkk. apply KEEP2;
    unfold A_G_REC, OFF_NCALLS, OFF_CALLS, A_REC_SPILL in *; lia. }
  assert (FRM2 : srs_frame_at (mrestrict (w_H Wc) (ms_mem ms0)) (sp0 - SRS_FRAME) regs).
  { intros j r Hjr. apply (srs_val_kept Wc Wc (ms_mem ms) (ms_mem ms0)); [exact (FRM1 j r Hjr)|].
    assert (Hj : (j < 6)%nat) by (change 6%nat with (length srs_saved); apply nth_error_Some; rewrite Hjr; discriminate).
    intros kk Hkk. apply KEEP2; unfold SRS_FRAME in *; lia. }
  assert (KO2 : forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc (ms_mem ms0) (fst pn + i) = rdW WB memB (fst pn + i)).
  { intros [b m] i Hpn Hi. cbn [fst snd] in *.
    destruct (srs_blk_bounds B lyc Sc Wc memJ mdJ b m HARc (HIO0 _ Hpn)) as (Hb0 & Hb1 & Hm0 & Hmr & _).
    rewrite KEEP2; [exact (KO1 (b, m) i Hpn Hi) | lia |].
    intros Hs. apply (srs_blk_noprog B cmd_prog_img lyc Sc Wc memJ mdJ b m (b + i) HARc (HIO0 _ Hpn) ltac:(lia)).
    exact (Hcimg _ Hs). }
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) srs_frame) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 r HSt ltac:(vm_compute; reflexivity)) as HRgD;
    cbn [ms_mem restrict mkst] in HRgD end.
  pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 0 4%N (SLit 10) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VFND.
  pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 4 4%N (SLit 0) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VNAD.
  change (N.to_nat 4) with 4%nat in VFND, VNAD.
  replace (bv_unsigned (sv_denot E (SLit 10)) mod 2 ^ (8 * Z.of_N 4)) with 10 in VFND by (vm_compute; reflexivity).
  replace (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VNAD by (vm_compute; reflexivity).
  pose proof (aval_mem_view SEGS _ _ _ _ _ VFND) as VFN2. pose proof (aval_mem_view SEGS _ _ _ _ _ VNAD) as VNA2.
  pose proof (proj1 HJ) as HARn.
  assert (HROn : cmd_ro_ok (rdW Wc (ms_mem ms0))).
  { apply (cmd_ro_ok_of_aro _ _ _ _ _ HARn).
    exact (srs_aro B HB RRO cmd_ro_prog_apart IMG ly S W mem md O lyc Sc Wc (ms_mem ms0) _ [] k sp0
      HAR HOin HJ HROD). }
  destruct (srs_null_argA lyc Sc Wc (ms_mem ms0) [] HROn) as (HSTRN & HTAILN).
  exact (HX ly S W regs mem md ch pw None R O Q lyc Sc Wc (ms_mem ms0) _ k lyB SBa WB memB R0 O0 F
    (ms_regs ms0) 0x22480 PRE HQ HOQ
    (conj HJ (conj Hk (conj FRM2 (conj HREPB (conj HSP0 (conj HLEN0 (conj HREC0 (conj KO2 (conj HIO0
      (conj HPERM (conj HFO (conj HO0 (conj HFN MLE)))))))))))))
    RM2 NC2 VFN2 VNA2 Q1 Q2 Q3 Q4 Q8 Q18 Q19 Q20 Q10 RS7 HSTRN HTAILN).
Qed.

(* ---------- the entry segment: the prologue, record(10) on both arms, to the join (0x8b74c) ----------
   ported from an earlier version of lib/A/Prog/sup_quarantine_clear_s3.v:1476-1938 (the same
   91 instructions at 0x8b844; FN 11 there, 10 here), with the string argument carried as astr_argA + its word tail
   (srs_arg_kept) instead of that statement's block form *)
Lemma srs_aval_same : forall (rd rd' : reader) a n v, aval_mem rd a n v -> aval_mem rd' a n v ->
forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k).
Proof. intros rd rd' a n v H H' k Hk. rewrite (H k Hk), (H' k Hk). reflexivity. Qed.

Lemma srs_nodup_app_r : forall {X : Type} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|].
cbn in H. apply List.NoDup_cons_iff in H as [_ H]. exact (IH l2 H).
Qed.

Ltac srs_fr_val3 OLD3 EE r :=
  cbn [sv_denot]; rewrite (OLD3 r) by lia; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z.add_0_r; reflexivity.

(* the slot record() picks in g_rec's table, as the listing computes it (0x8b738 .. 0x8b748) *)
Lemma srs_slot_word : forall n, 0 <= n < 16 ->
alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 n) (Z_to_bv 64 56)) (Z_to_bv 64 16)) (Z_to_bv 64 A_G_REC) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros n Hn.
assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15) by lia.
repeat (destruct Hc as [-> | Hc]); [..| subst n]; apply bv_eq; vm_compute; reflexivity.
Qed.

(* the value a register held at the entry, as the frame stores it *)
Ltac srs_fr_val EE r :=
  cbn [sv_denot]; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z.add_0_r; reflexivity.
Ltac srs_fr_rng regs r :=
  let Hb := fresh "Hrng" in
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb;
  cbn; lia.

(* the entry (0x8b6d8): the frame, the shadow base, g_rec.ncalls, the test of a full table *)
Lemma srs_SA : srs_SX_spec B MT -> tsrs_spec_g B MT.
Proof.
intros HSX ly S W regs mem md ch pw which R O PRE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & HRND & HROD & HRO & Hpw & H10 & HARG & HREP & HFR8 & HEV & HLIVE & HMOK & HG2).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SRS_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
pose proof HREP as (Q & HQ & HOQ).
pose proof HQ as (_ & _ & _ & (HC1 & HC2 & HNC & HC4 & HC5 & HC6) & _).
set (nn := Z.of_nat (length (r_calls R))) in *.
assert (Hnn : 0 <= nn <= 16) by (subst nn; lia).
set (c := srs_slot R).
assert (Hc : srs_slot_ok c) by exact (srs_slot_ok_of R HC1).
assert (HNCv : val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + OFF_NCALLS) 4 nn) by exact (val_mem_view SEGS _ _ _ _ _ HNC).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (fold sp0; rewrite HST in Hslo; lia).
assert (Hp48 : forall a, spZ regs - SRS_FRAME <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; fold sp0 in Ha |- *; rewrite HST; unfold SRS_FRAME in Ha; lia).
pose proof (srs_seed_entry B TL VOBJS cmd_prog_writable W regs mem ly S md nn c HAR Hsp Hal16 Hp48 Hnn Hc HNCv) as HS.
assert (SHOK : sh_ok SEGS srs_Bx [] (srs_E regs regs nn c) (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
pose proof (ajournal_init SEGS B SRS_STK (srs_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (E34 : ew (srs_E regs regs nn c) 34 = Z_to_bv 64 c) by (rewrite (srs_E_extra_at regs regs nn c 34 ltac:(lia)); reflexivity).
assert (E33 : ew (srs_E regs regs nn c) 33 = Z_to_bv 64 nn) by (rewrite (srs_E_extra_at regs regs nn c 33 ltac:(lia)); reflexivity).
assert (E32 : ew (srs_E regs regs nn c) 32 = Z_to_bv 64 SB) by (rewrite (srs_E_extra_at regs regs nn c 32 ltac:(lia)); reflexivity).
set (E := srs_E regs regs nn c) in *.
assert (HEI : img_env VAL A_LIM E) by exact (srs_E_img regs regs nn c).
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs rr)
  by (intros kk rr Hkk; exact (srs_E_reg regs regs nn c kk rr Hkk)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U44 : bv_unsigned (ew E SRS_GREC) = A_G_REC)
  by (pose proof (srs_E_grec VOBJS regs regs nn c) as Hg; change (ew E SRS_GREC = Z_to_bv 64 A_G_REC) in Hg;
      rewrite Hg; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U33 : U E (SOff 33 0) = nn) by (apply U_atom; [exact E33 | lia]).
unfold cfg_at.
(* 0x8b6d8 .. 0x8b714: the frame, the shadow base, g_rec.ncalls, then the test of a full table *)
paj_run_tok RUN HS HJ SHOK srs_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SRS_GREC); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
  assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
  right; right; right; right; left.
  split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
  unfold srs_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
psrr_branch_tok RUN BR HS SHOK srs_Bspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
all: rewrite branch_ne_U, U33 in Hbr; change (U E (SLit 16)) with 16 in Hbr.
- (* g_rec.ncalls <> 16: the slot arm, 0x8b730 .. 0x8b748 *)
  apply negb_true_iff, Z.eqb_neq in Hbr.
  assert (Hn16 : (length (r_calls R) < 16)%nat) by (subst nn; lia).
  paj_run_to_tok RUNTO HS HJ SHOK srs_Bspan SRS_JOIN.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SRS_GREC); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
    assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
    right; right; right; right; left.
    split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
    unfold srs_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  assert (E285 : ew E 285 = Z_to_bv 64 A_G_REC).
  { pose proof (srs_E_grec VOBJS regs regs nn c) as Hg. exact Hg. }
  assert (U285 : bv_unsigned (ew E 285) = A_G_REC) by exact U44.
  assert (G2 : getr (ms_regs ms) 2 = w64 (spZ regs - SRS_FRAME)) by (rewrite P2, Usp; unfold w64, SRS_FRAME; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
  assert (G8 : getr (ms_regs ms) 8 = w64 (srs_slot R)).
  { rewrite P8, E33, E285. unfold srs_slot. rewrite (proj2 (Nat.ltb_lt _ _) Hn16). apply srs_slot_word. subst nn; lia. }
  assert (G9 : getr (ms_regs ms) 9 = w64 pw) by (rewrite P9, (EE 10%nat 10%bv eq_refl); exact H10).
  assert (G19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite P19; exact E32).
  assert (GH : forall r, 21 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (H7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct H7 as [-> | H7]); [..| subst r];
    rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) srs_frame) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) srs_frame) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 0 r0 HSt ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 3 r3 HSt ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR0, HR3 end.
  assert (HFRm : srs_frame_at (mrestrict (w_H W) (ms_mem ms)) (spZ regs - SRS_FRAME) regs).
  { intros j r Hjr.
    unfold srs_saved in Hjr. destruct j as [|[|[|[|[|[|j]]]]]]; cbn in Hjr; try (destruct j; discriminate); injection Hjr as <-.
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 0) with (sp0 + -8) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) _ HR0 Usp ltac:(cbn; tauto));
      [srs_fr_val EE 1%nat | srs_fr_rng regs 1 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 1) with (sp0 + -16) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) _ HR0 Usp ltac:(cbn; tauto));
      [srs_fr_val EE 8%nat | srs_fr_rng regs 8 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 2) with (sp0 + -24) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) _ HR0 Usp ltac:(cbn; tauto));
      [srs_fr_val EE 9%nat | srs_fr_rng regs 9 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 3) with (sp0 + -32) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-32) 8 (SOff 18 0) _ HR0 Usp ltac:(cbn; tauto));
      [srs_fr_val EE 18%nat | srs_fr_rng regs 18 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 4) with (sp0 + -40) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-40) 8 (SOff 19 0) _ HR0 Usp ltac:(cbn; tauto));
      [srs_fr_val EE 19%nat | srs_fr_rng regs 19 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 5) with (sp0 + -48) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-48) 8 (SOff 20 0) _ HR0 Usp ltac:(cbn; tauto));
      [srs_fr_val EE 20%nat | srs_fr_rng regs 20 | cbn; lia]. }
  assert (HNC1 : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (nn + 1)).
  { apply aval_mem_view. unfold OFF_NCALLS.
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (nn + 1) HR3 U285 ltac:(cbn; tauto));
    [cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia]. }
  assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
     rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. transitivity (rdW W (ms_mem ms0) a).
    - apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms0) (ms_mem ms)
        (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr); [|exact Ha | tauto].
      intros b wlo whi a' Hin Hrr. vm_compute in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]).
      destruct Hin.
    - apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms0)
        (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0); [|exact Ha | tauto].
      intros b wlo whi a' Hin Hrr. vm_compute in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]).
      destruct Hin. }
  assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
  { intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
  assert (HARGJ : forall x, which = Some x ->
     astr_argA B ly S (rdW W (ms_mem ms)) (in_roP SEGS RLO RHI) [] pw (Some x) /\
     atail_vis SEGS W (ms_mem ms) (pw + Z.of_nat (length x))).
  { intros x Hx. rewrite Hx in HARG. pose proof (proj1 HJ) as HARm.
    apply (srs_arg_kept ly S W mem md ly S W (ms_mem ms) _ O pw x HAR HARm HROD
      (srs_aro B HB RRO cmd_ro_prog_apart IMG ly S W mem md O ly S W (ms_mem ms) _ [] 0 sp0 HAR HOin HJ HROD)
      (fun pn Hpn _ => Hpn)).
    - intros b k a Hbk _ Ha.
      destruct (srs_blk_bounds B ly S W mem md b k HAR Hbk) as (Hb & Hbc & _ & Hmr & _).
      apply KEEPJ; [lia | rewrite HST in Hslo; lia |].
      intros Hg. apply (srs_blk_noprog B cmd_prog_img ly S W mem md b k a HAR Hbk); [lia|].
      apply recb_grec_in. unfold A_G_REC, REC_SIZE in *. lia.
    - exact HARG.
    - exact (HG2 x Hx). }
  rewrite HST in Hslo.
  refine (srs_join HSX ly S W regs mem md ch pw which R O Q ly S W (ms_mem ms) _ 0 ly S W mem R O [] (ms_regs ms)
    PRE HQ HOQ _ _ _ G2 G3 G4 G8 G9 G19 (GH 21 ltac:(lia)) (GH 22 ltac:(lia)) (GH 23 ltac:(lia))
    (GH 24 ltac:(lia)) (GH 25 ltac:(lia)) (GH 26 ltac:(lia)) (GH 27 ltac:(lia)) HARGJ).
  + split; [exact HJ|]. split; [reflexivity|]. split; [exact HFRm|]. split; [exact HREP|].
    split; [intros Hl; lia|]. split; [reflexivity|]. split; [intros A; reflexivity|].
    split.
    { intros [b m] i Hpn Hi. cbn [fst snd] in *.
      destruct (srs_blk_bounds B ly S W mem md b m HAR (HOin _ Hpn)) as (Hb & Hbc & _ & Hmr & _).
      apply KEEPJ; [lia | lia |].
      intros Hg. apply (srs_blk_noprog B cmd_prog_img ly S W mem md b m (b + i) HAR (HOin _ Hpn)); [lia|].
      apply recb_grec_in. unfold A_G_REC, REC_SIZE in *. lia. }
    split; [exact HOin|]. split; [rewrite app_nil_r; reflexivity|]. split; [intros pn []|].
    split; [intros pn; split; [intros H; split; [exact H | intros []] | intros [H _]; exact H]|].
    split; [unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hn16); reflexivity|].
    cbn [length Z.of_nat]. rewrite Z.mul_0_l. exact (mo_le_refl MT MTL S).
  + intros a Ha Hnc _. apply KEEPJ; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia | | exact Hnc].
    unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
  + unfold srs_ncalls_ok, rec_record. rewrite (proj2 (Nat.ltb_lt _ _) Hn16). cbn [r_calls set_calls].
    rewrite length_app. cbn [length]. replace (Z.of_nat (length (r_calls R) + 1)) with (nn + 1) by (subst nn; lia).
    exact HNC1.
- (* g_rec.ncalls = 16: the spill arm, 0x8b718 .. 0x8b728 *)
  apply negb_false_iff, Z.eqb_eq in Hbr.
  paj_run_tok RUN HS HJ SHOK srs_Bspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SRS_GREC); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
    assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
    right; right; right; right; left.
    split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
    unfold srs_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pmkst HS.
  assert (HL : length (r_calls R) = 16%nat) by (subst nn; lia).
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  assert (U285 : bv_unsigned (ew E 285) = A_G_REC) by exact U44.
  assert (E292 : forall E', img_env VAL A_LIM E' -> ew E' 292 = Z_to_bv 64 A_REC_SPILL).
  { intros E' HE'. apply bv_eq. change 292%nat with (A_OBJ 51).
    rewrite (HE' (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (srs_spill_val VOBJS : VAL (A_OBJ 51) = A_REC_SPILL).
    rewrite unsigned_lit_small; unfold A_REC_SPILL; lia. }
  assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
  { intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
  (* g_rec.ncalls at the call: still 16 *)
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) srs_frame) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 3 r3 HSt ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR3 end.
  assert (HNCc : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 nn).
  { apply aval_mem_view. unfold OFF_NCALLS.
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) nn HR3 U285 ltac:(cbn; tauto));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
  (* the two runs write only the frame: g_rec.ncalls keeps its value *)
  assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1.
    destruct (Z_lt_le_dec a (A_G_REC + 8)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (A_G_REC + 12)) as [Hhi|Hhi]].
    2: { replace a with (A_G_REC + OFF_NCALLS + Z.of_nat (Z.to_nat (a - (A_G_REC + 8)))) by (unfold OFF_NCALLS; lia).
         exact (srs_aval_same _ _ _ _ _ HNC HNCc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)). }
    all: transitivity (rdW W (ms_mem ms0) a).
    all: try (apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms0) (ms_mem ms)
           (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr); [|exact Ha | lia];
         intros b wlo whi a' Hin Hrr; vm_compute in Hin;
         repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]);
         destruct Hin).
    all: apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms0)
           (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0); [|exact Ha | lia];
         intros b wlo whi a' Hin Hrr; vm_compute in Hin;
         repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]);
         destruct Hin. }
  rewrite HST in Hslo.
  assert (HAc : arep_at (ablocks B ly S) (rdW W (ms_mem ms)) A_G_REC A_REC_SPILL R Q).
  { apply (srs_arep_at_ext _ _ (rdW W mem) _ _ _ R Q HQ).
    - intros pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn Hpn).
    - intros a [Ha | [Ha | ([pb pm] & Hpn & Ha)]].
      + apply KEEPC; unfold A_G_REC, REC_SIZE in *; lia.
      + apply KEEPC; unfold A_REC_SPILL, SC_SIZE in *; lia.
      + cbn [fst snd] in Ha. pose proof (lay_blocks_in _ _ _ _ _ _ HQ (pb, pm) Hpn) as Hin.
        destruct (srs_blk_bounds B ly S W mem md pb pm HAR Hin) as (Hb & Hbc & _ & Hmr & _). apply KEEPC; lia. }
  pose proof HAc as (_ & _ & _ & (_ & _ & _ & _ & HC5c & _) & _ & _ & _ & (HNDq & _)).
  pose proof HC5c as (_ & G6 & GL & _ & GN & GNd & G7).
  (* rec_calls_free(&record.spill, 1) *)
  assert (FR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
  assert (HspT : spZ (ms_regs ms) = sp0 + -48) by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia).
  assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
  assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
  assert (P10' : getr (ms_regs ms) 10 = w64 A_REC_SPILL) by (rewrite P10; exact (E292 E HEI)).
  assert (P11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length [l_spill Q]))) by (rewrite P11; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
  assert (Hch1 : achain ly (rdW W (ms_mem ms)) (sp0 + -48) (s0Z (ms_regs ms)) []).
  { left. split; [|reflexivity]. left. unfold s0Z. rewrite P8, (E292 E HEI), unsigned_lit_small by (unfold A_REC_SPILL; lia).
    unfold A_REC_SPILL. lia. }
  assert (RSF : rec_spill_frees R = Z.of_nat (length (l_spill Q))).
  { unfold rec_spill_frees. rewrite HL. cbn [Nat.ltb Nat.leb]. rewrite GL. reflexivity. }
  assert (EVC : EV_REC_CALLS_FREE [l_spill Q] = Z.of_nat (length (l_spill Q)))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (XMC : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT)
    by (unfold XM_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r, RSF; reflexivity).
  assert (XX0 : 0 <= XM_XSTRDUP MT (sarg which)) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
  assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
  { intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
  assert (HEc : st_nev S + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
  { rewrite EVC, <- RSF. unfold EV_SUP_RESET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia. }
  assert (HMOKc : mo_ok MT S (XM_REC_CALLS_FREE MT [l_spill Q])).
  { rewrite XMC. apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_RESET.
    pose proof (XN0 (snd (sup_reset_m R which))). lia. }
  assert (HHOME : rcf_home B ly S W (ms_mem ms) A_REC_SPILL (CALL_SIZE * Z.of_nat (length [l_spill Q]))).
  { unfold rcf_home. right; left. cbn [length Z.of_nat]. unfold CALL_SIZE, SC_SIZE. lia. }
  assert (HENT : forall i P, nth_error [l_spill Q] i = Some P ->
     (length P <= 6)%nat /\ aval_mem (rdW W (ms_mem ms)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
     forall a pn, nth_error P a = Some pn ->
       aval_mem (rdW W (ms_mem ms)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
       In pn (ablocks B ly S)).
  { intros i P Hi. destruct i as [|i]; [|destruct i; discriminate]. cbn in Hi. injection Hi as <-.
    cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
    split; [rewrite GL; exact G6|]. split; [rewrite GL; exact GN|].
    intros a pn Hpn.
    destruct (nth_error (snd (r_spill R)) a) as [s'|] eqn:Hs.
    - destruct (G7 a s' pn Hs Hpn) as (V1 & _ & V3 & _). split; [exact V1 | exact V3].
    - exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) a) ltac:(rewrite Hpn; discriminate)). lia. }
  assert (HND : NoDup (map fst (concat [l_spill Q]))) by (cbn [concat]; rewrite app_nil_r; exact GNd).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms)))
    by exact (srs_aro B HB RRO cmd_ro_prog_apart IMG ly S W mem md O ly S W (ms_mem ms) _ [] 0 sp0 HAR HOin HJ HROD).
  assert (HspillO : forall pn, In pn (l_spill Q) -> In pn O)
    by (intros pn Hpn; apply HOQ; unfold lay_blocks; apply in_app_iff; right; apply in_app_iff; left; exact Hpn).
  assert (HFP1 : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a ->
     (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
     (exists b m, In (b, m) (l_spill Q) /\ b <= a < b + req_size m)).
  { intros a Ha. unfold rcf_fp in Ha. cbn [length seq map app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
    - left. cbn [Z.of_nat] in Ha. lia.
    - right. destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba). cbn [concat] in Hbm. rewrite app_nil_r in Hbm.
      exists b, m. split; [exact Hbm | exact Hba]. }
  assert (HFP1s : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> a < sp0 - SRS_STK).
  { intros a Ha. rewrite HST. destruct (HFP1 a Ha) as [Ha' | (b & m & Hbm & Hba)]; [unfold A_REC_SPILL, CALL_OFF_NARGS in Ha'; lia|].
    destruct (srs_blk_bounds B ly S W mem md b m HAR (HOin _ (HspillO _ Hbm))) as (_ & Hbc & _). lia. }
  rewrite (SIGP CS_rec_calls_free ltac:(vm_compute; tauto)).
  change (pa_val A_TEXT + cmd_af CS_rec_calls_free) with (BASE + AF_rec_calls_free).
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ SRS_STK sp0 (srs_FP O) ly S W mem md [] ly S _ 0
      REC_CALLS_FREE_STK _ (EV_REC_CALLS_FREE [l_spill Q]) (-48) (getr (ms_regs ms) 1) [] _ HJ HspT eq_refl ltac:(lia)
      ltac:(rewrite FR; lia) ltac:(rewrite FR, HST; lia) P3' P4' eq_refl HraT Hra4T Hch1).
    - intros HPRE1. exact (TRCF fx ly S W (ms_regs ms) (ms_mem ms) _ [] A_REC_SPILL [l_spill Q] HPRE1 HRODc P10' P11'
        ltac:(cbn; lia) HHOME ltac:(unfold A_REC_SPILL; reflexivity) HENT HND HEc HMOKc).
    - intros a Ha. destruct (HFP1 a Ha) as [Ha' | (b & m & Hbm & Hba)].
      + right; right; right; right; left.
        assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_spill_in; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *; lia).
        split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
        unfold srs_FP. apply inFP_cons. right. apply inFP_cons. left. unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *. lia.
      + right; left. split.
        * unfold srs_FP. apply inFP_cons. right. apply inFP_cons. right.
          replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact (HspillO _ Hbm) | lia].
        * exists b, m. split; [exact (HOin _ (HspillO _ Hbm)) | exact Hba].
    - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFP1s a Ha). lia. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
  destruct HK2 as (HPermF & _ & _ & _ & _ & HRspill & _ & _ & MLEF).
  rewrite P1.
  (* back at 0x8b72c *)
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B);
    [exact HJc2 | exact HJ2 | exact Usp | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. pose proof (HFP1s a HFa). rewrite HST in *. cbn in Ha. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
  assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD3 : forall m, (m < 48)%nat -> ew E3 m = ew E m) by (intros m Hm; rewrite HE3; apply YN3v.ew_havoc_old; exact Hm).
  clear HE3.
  assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS srs_Bx [] E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; constructor).
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  (* 0x8b72c: j 0x8b74c *)
  paj_run_to_tok RUNTO HS HJ2 SHOK3 srs_Bspan SRS_JOIN.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp3 | cbn; rewrite HST; lia | cbn; lia |].
    apply (awr_ok_nil SEGS B). }
  pmkst HS.
  pose proof (proj1 HJ2) as HAR2.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  assert (G2 : getr (ms_regs ms) 2 = w64 (spZ regs - SRS_FRAME)) by (rewrite Q2, Usp3; unfold w64, SRS_FRAME; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
  { rewrite Q3. rewrite (OLD3 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp. }
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
  { rewrite Q4. rewrite (OLD3 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp. }
  set (R0 := set_spill R (fst (r_spill R), [])).
  assert (G8 : getr (ms_regs ms) 8 = w64 (srs_slot R0)).
  { rewrite Q8, (E292 E3 HEI3). unfold srs_slot, R0. cbn [set_spill r_calls]. rewrite HL. reflexivity. }
  assert (G9 : getr (ms_regs ms) 9 = w64 pw).
  { rewrite Q9. rewrite (OLD3 10%nat) by lia. rewrite (EE 10%nat 10%bv eq_refl). exact H10. }
  assert (G19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite Q19; rewrite (OLD3 32%nat) by lia; exact E32).
  assert (GH : forall r, 21 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (H7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct H7 as [-> | H7]); [..| subst r];
    rewrite (st_ok_restrict_reg SEGS (w_H W2) E3 _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => rewrite (OLD3 m) by lia; exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
  pose proof HS as HSt2. unfold st_ok_pi, abs_ss in HSt2.
  lazymatch type of HSt2 with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) srs_frame) in
    pose proof (st_ok_region_nth E3 ssx (restrict (w_H W2) msx) 0 r0 HSt2 ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  assert (HFRm : srs_frame_at (mrestrict (w_H W2) (ms_mem ms)) (spZ regs - SRS_FRAME) regs).
  { intros j r Hjr.
    unfold srs_saved in Hjr. destruct j as [|[|[|[|[|[|j]]]]]]; cbn in Hjr; try (destruct j; discriminate); injection Hjr as <-.
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 0) with (sp0 + -8) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [srs_fr_val3 OLD3 EE 1%nat | srs_fr_rng regs 1 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 1) with (sp0 + -16) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [srs_fr_val3 OLD3 EE 8%nat | srs_fr_rng regs 8 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 2) with (sp0 + -24) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [srs_fr_val3 OLD3 EE 9%nat | srs_fr_rng regs 9 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 3) with (sp0 + -32) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-32) 8 (SOff 18 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [srs_fr_val3 OLD3 EE 18%nat | srs_fr_rng regs 18 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 4) with (sp0 + -40) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-40) 8 (SOff 19 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [srs_fr_val3 OLD3 EE 19%nat | srs_fr_rng regs 19 | cbn; lia].
    - replace (spZ regs - SRS_FRAME + 40 - 8 * Z.of_nat 5) with (sp0 + -48) by (unfold SRS_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-48) 8 (SOff 20 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [srs_fr_val3 OLD3 EE 20%nat | srs_fr_rng regs 20 | cbn; lia]. }
  (* the jump writes nothing outside the frame *)
  assert (KEEPJ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
  { intros a Ha H1.
    apply (kept_of_frame (segs := SEGS) E3 _ (w_H W2) mem2 (ms_mem ms) (fun a => sp0 - 48 <= a < sp0) HFr); [|exact Ha | exact H1].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]).
    destruct Hin. }
  set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
  pose proof (HRspill R Q HAc eq_refl eq_refl) as HRF.
  pose proof (proj1 HJc2) as HAR2c.
  assert (HRJ : rec_repA B ly2 S2 (rdW W2 (ms_mem ms)) R0 O1).
  { apply (srs_rec_repA_ext B ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HRF).
    - intros pn Hpn. destruct HRF as (QF & HQF & HOQF). exact (lay_blocks_in _ _ _ _ _ _ HQF pn (proj1 (HOQF pn) Hpn)).
    - intros a [Ha | [Ha | ([pb pm] & Hpn & Ha)]].
      + apply KEEPJ2; unfold A_G_REC, REC_SIZE in *; lia.
      + apply KEEPJ2; unfold A_REC_SPILL, SC_SIZE in *; lia.
      + cbn [fst snd] in Ha. destruct HRF as (QF & HQF & HOQF).
        pose proof (lay_blocks_in _ _ _ _ _ _ HQF (pb, pm) (proj1 (HOQF _) Hpn)) as Hin.
        destruct (srs_blk_bounds B ly2 S2 W2 mem2 md2 pb pm HAR2c Hin) as (Hb & Hbc & _ & Hmr & _). apply KEEPJ2; lia. }
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HNDq.
  pose proof HNDq as NDq'. unfold lay_blocks in NDq'. rewrite !map_app in NDq'.
  assert (JB2 : forall pn, In pn O1 <-> In pn O /\ ~ In pn (l_spill Q)).
  { intros pn. rewrite (HOQ pn). subst O1. unfold lay_blocks. rewrite !in_app_iff. split.
    - intros H. split; [tauto|]. intros Hs. destruct H as [Hcl | Har].
      + exact (list_nodup_app_disj _ _ (fst pn) NDq' (in_map fst _ _ Hcl) (in_or_app _ _ _ (or_introl (in_map fst _ _ Hs)))).
      + pose proof (srs_nodup_app_r _ _ NDq') as NDr.
        apply (list_nodup_app_disj _ _ (fst pn) NDr (in_map fst _ _ Hs)).
        destruct Har as [Ha | Hr]; apply in_or_app; [left | right]; apply in_map; assumption.
    - intros [H Hs]. tauto. }
  assert (FPpos : Forall (fun r => 0 < fst r) (rcf_fp A_REC_SPILL [l_spill Q])).
  { unfold rcf_fp. apply Forall_app. split.
    - cbn. constructor; [cbn; unfold A_REC_SPILL, CALL_OFF_NARGS; lia | constructor].
    - unfold ablocks_fp. rewrite Forall_map. apply Forall_forall. intros [b m] Hbm. cbn [concat] in Hbm. rewrite app_nil_r in Hbm.
      destruct (srs_blk_bounds B ly S W mem md b m HAR (HOin _ (HspillO _ Hbm))) as (Hb & _). cbn. lia. }
  assert (NC2 : aval_mem (rdW W2 mem2) (A_G_REC + OFF_NCALLS) 4 nn).
  { apply (srs_aval_kept (rdW W (ms_mem ms1))); [exact HNCc|]. intros kk Hkk.
    assert (HPG : Exists (in_zr (A_G_REC + OFF_NCALLS + Z.of_nat kk)) recb_PG)
      by (apply recb_grec_in; unfold A_G_REC, OFF_NCALLS, REC_SIZE; lia).
    apply (srs_keep_prog B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A_G_REC + OFF_NCALLS + Z.of_nat kk) HJc2 FPpos); [|exact HPG].
    intros Hf. destruct (HFP1 _ Hf) as [Ha' | (b & m & Hbm & Hba)]; [unfold A_REC_SPILL, A_G_REC, OFF_NCALLS, CALL_OFF_NARGS in *; lia|].
    exact (srs_blk_noprog B cmd_prog_img ly S W mem md b m _ HAR (HOin _ (HspillO _ Hbm)) Hba HPG). }
  assert (HARGJ : forall x, which = Some x ->
     astr_argA B ly2 S2 (rdW W2 (ms_mem ms)) (in_roP SEGS RLO RHI) [] pw (Some x) /\
     atail_vis SEGS W2 (ms_mem ms) (pw + Z.of_nat (length x))).
  { intros x Hx. rewrite Hx in HARG. pose proof (proj1 HJ2) as HARm.
    assert (Hlive2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
    { intros pn Hpn HnO. pose proof HPermF as HP'. cbn [concat] in HP'. rewrite app_nil_r in HP'.
      apply (Permutation_in _ HP') in Hpn. apply in_app_or in Hpn as [H | H]; [exact H|].
      exfalso. exact (HnO (HspillO _ H)). }
    apply (srs_arg_kept ly S W mem md ly2 S2 W2 (ms_mem ms) _ O pw x HAR HARm HROD
      (srs_aro B HB RRO cmd_ro_prog_apart IMG ly S W mem md O ly2 S2 W2 (ms_mem ms) _ [] _ sp0 HAR HOin HJ2 HROD) Hlive2).
    - intros b k a Hbk HnO Ha. pose proof (Hlive2 _ Hbk HnO) as Hbk2.
      destruct (srs_blk_bounds B ly S W mem md b k HAR Hbk) as (Hb & Hbc & Hk0 & Hkr & _).
      rewrite (KEEPJ2 a ltac:(lia) ltac:(lia)).
      replace a with (b + (a - b)) by lia.
      rewrite (srs_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJc2 Hbk Hbk2 ltac:(lia)).
      + apply KEEPC; lia.
      + intros Hf. destruct (HFP1 _ Hf) as [Ha' | (b' & m' & Hbm & Hba)].
        * apply (srs_blk_noprog B cmd_prog_img ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
          apply recb_spill_in. unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *. lia.
        * apply HnO. assert (Hin' : In (b', m') (ablocks B ly S)) by exact (HOin _ (HspillO _ Hbm)).
          destruct (recb_pair_dec (b, k) (b', m')) as [Eq | Hne]; [rewrite Eq; exact (HspillO _ Hbm)|].
          exfalso. destruct (srs_blk_bounds B ly S W mem md b' m' HAR Hin') as (_ & _ & _ & Hmr' & _).
          destruct (srs_blk_apart B ly S W mem md b k b' m' HAR Hbk Hin' Hne); lia.
    - exact HARG.
    - exact (HG2 x Hx). }
  refine (srs_join HSX ly S W regs mem md ch pw which R O Q ly2 S2 W2 (ms_mem ms) _
    (0 + EV_REC_CALLS_FREE [l_spill Q]) ly2 S2 W2 (ms_mem ms) R0 O1 (l_spill Q) (ms_regs ms) PRE HQ HOQ _ _ _
    G2 G3 G4 G8 G9 G19 (GH 21 ltac:(lia)) (GH 22 ltac:(lia)) (GH 23 ltac:(lia))
    (GH 24 ltac:(lia)) (GH 25 ltac:(lia)) (GH 26 ltac:(lia)) (GH 27 ltac:(lia)) HARGJ).
  + split; [exact HJ2|]. split; [rewrite EVC; lia|]. split; [exact HFRm|]. split; [exact HRJ|].
    split; [intros _; reflexivity|]. split; [reflexivity|].
    split; [intros A; exact (srs_rec_record_set_spill R _ SRS_FN A HL)|].
    split; [intros; reflexivity|].
    split; [intros pn Hpn; destruct HRJ as (QJ & HQJ & HOQJ); exact (lay_blocks_in _ _ _ _ _ _ HQJ pn (proj1 (HOQJ pn) Hpn))|].
    split; [cbn [concat] in HPermF; rewrite app_nil_r in HPermF; exact HPermF|].
    split; [exact HspillO|]. split; [exact JB2|]. split; [symmetry; exact RSF|].
    rewrite <- RSF, <- XMC. exact MLEF.
  + intros a _ _ _. reflexivity.
  + unfold srs_ncalls_ok. apply (srs_aval_kept (rdW W2 mem2)).
    * replace (Z.of_nat (length (r_calls (rec_record R0 SRS_FN [[]])))) with nn; [exact NC2|].
      subst nn. unfold rec_record, R0. cbn [set_spill r_calls]. rewrite HL. cbn [Nat.ltb Nat.leb set_spill r_calls].
      rewrite ?HL. reflexivity.
    * intros kk Hkk. apply KEEPJ2; unfold A_G_REC, OFF_NCALLS in *; lia.
Qed.

(* the statement (sup_reset_c.v:74-119) exactly, from the two parts of the walk *)
Theorem tsup_reset_holds : tsup_reset_spec B MT.
Proof.
intros ly S W regs mem md ch pw which R O H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
exact (srs_SA (srs_SX B MT TXSTRDUP TREC_SHAPE_OF TANSWER VOBJS CMD_RO_IN HB MTL SIGP cmd_prog_img cmd_prog_writable
  RRO cmd_ro_ok_of_aro cmd_ro_prog_apart IMG) ly S W regs mem md ch pw which R O
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H6 (conj H5 (conj H7 (conj H9 (conj H10 (conj H11 (conj H12
    (conj H13 H8))))))))))))).
Qed.

End e2.
End f2.
End d2.
