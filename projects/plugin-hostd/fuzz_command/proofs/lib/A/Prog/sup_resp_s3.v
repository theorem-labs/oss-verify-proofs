(* sup_resp's walk on the ASan build of plugin-hostd/fuzz_command, part 3: the recorder's representation `rec_repA`
   (lib/A/Prog/CmdRep.v:154) carried across a change of reader and of block list.

   Every byte arep_at reads lies in one of three places: the record [gr, gr + REC_SIZE) (the scalar fields and the
   16 call slots, each slot CALL_SIZE bytes wide), the spill slot [sc, sc + SC_SIZE), or a block (p, n) of the block
   list (the argument strings, the answer text, the reply bytes). So a reader that agrees with the old one on those
   three places, and a block list that keeps every old block, keep the representation. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
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
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Open Scope Z_scope.

(* the three byte vocabularies, under agreement of the two readers on the range they read *)
Lemma s3_aval : forall (rd rd' : reader) a n v,
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HE H k Hk. rewrite HE by lia. exact (H k Hk). Qed.

Lemma s3_bytes : forall (rd rd' : reader) p l,
  (forall x, p <= x < p + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd p l -> abytes_atR rd' p l.
Proof. intros rd rd' p l HE H i Hi. rewrite HE by lia. exact (H i Hi). Qed.

Lemma s3_str : forall (rd rd' : reader) p s,
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s HE [H1 H2]. split; [|exact H2].
apply (s3_bytes rd); [|exact H1].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply HE. lia.
Qed.

(* one call slot: its fields lie in [a, a + CALL_SIZE) (the arguments k < length (snd c) <= 6 end at offset
   8 + 8 * 6 = CALL_SIZE), its argument strings in their blocks *)
Lemma s3_call : forall (bl bl' : list (Z * Z)) (rd rd' : reader) a c P,
  (forall pn, In pn bl -> In pn bl') ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall p n x, In (p, n) bl -> p <= x < p + n -> rd' x = rd x) ->
  acall_at bl rd a c P -> acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P Hbl Ha Hb (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold CALL_SIZE in Ha.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (s3_aval rd); [intros x Hx; apply Ha; unfold CALL_OFF_FN in Hx; lia | exact H4]|].
split; [apply (s3_aval rd); [intros x Hx; apply Ha; unfold CALL_OFF_NARGS in Hx; lia | exact H5]|].
split; [exact H6|].
intros k s [p n] Hs Hp.
destruct (H7 k s (p, n) Hs Hp) as (G1 & G2 & G3 & G4 & G5).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
cbn [fst snd] in *.
split; [apply (s3_aval rd); [intros x Hx; apply Ha; unfold CALL_OFF_ARGS in Hx; lia | exact G1]|].
split; [exact G2|]. split; [exact (Hbl _ G3)|]. split; [exact G4|].
apply (s3_str rd); [intros x Hx; apply (Hb p n); [exact G3 | lia] | exact G5].
Qed.

(* the call table: slot i < length (r_calls R) <= 16 ends at OFF_CALLS + CALL_SIZE * 16 = OFF_ANSWER <= REC_SIZE *)
Lemma s3_calls : forall (bl bl' : list (Z * Z)) (rd rd' : reader) gr sc R Q,
  (forall pn, In pn bl -> In pn bl') ->
  (forall a, gr <= a < gr + REC_SIZE -> rd' a = rd a) ->
  (forall a, sc <= a < sc + SC_SIZE -> rd' a = rd a) ->
  (forall p n a, In (p, n) bl -> p <= a < p + n -> rd' a = rd a) ->
  ag1_calls bl rd gr sc R Q -> ag1_calls bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q Hbl Hg Hs Hb (H1 & H2 & H3 & H4 & H5 & H6).
unfold REC_SIZE in Hg. unfold SC_SIZE in Hs.
split; [exact H1|]. split; [exact H2|].
split; [apply (s3_aval rd); [intros x Hx; apply Hg; unfold OFF_NCALLS in Hx; lia | exact H3]|].
split.
- intros i c P Hc HP. destruct (H4 i c P Hc HP) as [G1 G2]. split; [|exact G2].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  apply (s3_call bl bl' rd rd'); [exact Hbl | | exact Hb | exact G1].
  intros x Hx. apply Hg. unfold OFF_CALLS, CALL_SIZE in Hx. lia.
- split; [|exact H6]. apply (s3_call bl bl' rd rd'); [exact Hbl | | exact Hb | exact H5].
  intros x Hx. apply Hs. unfold CALL_SIZE in Hx. lia.
Qed.

Lemma s3_answer : forall (bl bl' : list (Z * Z)) (rd rd' : reader) gr t q,
  (forall pn, In pn bl -> In pn bl') ->
  (forall a, gr <= a < gr + REC_SIZE -> rd' a = rd a) ->
  (forall p n a, In (p, n) bl -> p <= a < p + n -> rd' a = rd a) ->
  aanswer_at bl rd gr t q -> aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q Hbl Hg Hb H. unfold REC_SIZE in Hg.
destruct t as [x|], q as [[p n]|]; unfold aanswer_at in H |- *; try contradiction.
- destruct H as (G1 & G2 & G3 & G4 & G5 & G6). cbn [fst snd] in *.
  split; [apply (s3_aval rd); [intros a Ha; apply Hg; unfold OFF_ANSWER in Ha; lia | exact G1]|].
  split; [exact G2|]. split; [exact (Hbl _ G3)|]. split; [exact G4|].
  split; [|exact G6]. apply (s3_str rd); [intros a Ha; apply (Hb p n); [exact G3 | lia] | exact G5].
- apply (s3_aval rd); [intros a Ha; apply Hg; unfold OFF_ANSWER in Ha; lia | exact H].
Qed.

Lemma s3_reply : forall (bl bl' : list (Z * Z)) (rd rd' : reader) gr y q,
  (forall pn, In pn bl -> In pn bl') ->
  (forall a, gr <= a < gr + REC_SIZE -> rd' a = rd a) ->
  (forall p n a, In (p, n) bl -> p <= a < p + n -> rd' a = rd a) ->
  areply_at bl rd gr y q -> areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q Hbl Hg Hb H. unfold REC_SIZE in Hg.
destruct y as [x|], q as [[p n]|]; unfold areply_at in H |- *; try contradiction.
- destruct H as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). cbn [fst snd] in *.
  split; [apply (s3_aval rd); [intros a Ha; apply Hg; unfold OFF_REPLY in Ha; lia | exact G1]|].
  split; [apply (s3_aval rd); [intros a Ha; apply Hg; unfold OFF_REPLY_SIZE in Ha; lia | exact G2]|].
  split; [exact G3|]. split; [exact G4|]. split; [exact (Hbl _ G5)|]. split; [exact G6|].
  split; [|exact G8]. apply (s3_bytes rd); [intros a Ha; apply (Hb p n); [exact G5 | lia] | exact G7].
- destruct H as [G1 G2]. split.
  + apply (s3_aval rd); [intros a Ha; apply Hg; unfold OFF_REPLY in Ha; lia | exact G1].
  + apply (s3_aval rd); [intros a Ha; apply Hg; unfold OFF_REPLY_SIZE in Ha; lia | exact G2].
Qed.

Lemma s3_scalars : forall (rd rd' : reader) gr R,
  (forall a, gr <= a < gr + REC_SIZE -> rd' a = rd a) ->
  ag1_scalars rd gr R -> ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R Hg H. unfold ag1_scalars in H |- *.
unfold REC_SIZE in Hg. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in H |- *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
split; [apply (s3_aval rd); [intros a Ha; apply Hg; lia | exact H1]|].
split; [apply (s3_aval rd); [intros a Ha; apply Hg; lia | exact H2]|].
split; [apply (s3_aval rd); [intros a Ha; apply Hg; lia | exact H3]|].
split; [apply (s3_aval rd); [intros a Ha; apply Hg; lia | exact H4]|].
split; [apply (s3_aval rd); [intros a Ha; apply Hg; lia | exact H5]|].
exact H6.
Qed.

Lemma arep_at_kept : forall (bl bl' : list (Z * Z)) (rd rd' : reader) gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn bl -> In pn bl') ->
  (forall a, gr <= a < gr + REC_SIZE -> rd' a = rd a) ->
  (forall a, sc <= a < sc + SC_SIZE -> rd' a = rd a) ->
  (forall p n a, In (p, n) bl -> p <= a < p + n -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hbl Hg Hs Hb.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (s3_calls bl bl' rd rd' gr sc R Q Hbl Hg Hs Hb H4)|].
split; [exact (s3_answer bl bl' rd rd' gr _ _ Hbl Hg Hb H5)|].
split; [exact (s3_reply bl bl' rd rd' gr _ _ Hbl Hg Hb H6)|].
split; [exact (s3_scalars rd rd' gr R Hg H7)|].
exact H8.
Qed.

Section d.
Variable B : asyms.

Lemma rec_repA_kept : forall ly S ly' S' (rd rd' : reader) R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
  (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
  (forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O [Q [HA HO]] Hbl Hg Hs Hb.
exists Q. split; [|exact HO].
exact (arep_at_kept _ _ rd rd' _ _ R Q HA Hbl Hg Hs Hb).
Qed.
End d.
