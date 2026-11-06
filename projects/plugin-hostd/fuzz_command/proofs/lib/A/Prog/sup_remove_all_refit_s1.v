(* Pure lemmas for sup_remove_all's walk (plugin-hostd/fuzz_command, ASan build) about the recorder's in-memory
   representation arep_at (lib/A/Prog/CmdRep.v) over a reader, with no machine semantics: the representation of
   the model state after record(REC_REMOVE_ALL, []) when the call table has room (arep_append: the new slot and
   the ncalls cell written) and when the table is full and the spill takes the call (arep_spill_set: the spill's
   fn and nargs written, its argument list already empty); the representation read through a reader that agrees
   below a bound LIM above every live block and the recorder's two objects (arep_kept); the old value of the
   answer cell (arep_answer_cell); and the model facts the walk rewrites with (sup_remove_all_m as rec_answer of
   rec_record, rec_record in its two cases, the lay blocks of the appended layout). The s1_* lemmas are the
   frame facts these are built from. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Local Ltac nums := unfold REC_SIZE, SC_SIZE, CALL_SIZE, OFF_REFUSE, OFF_CODE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER,
  OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS, iv_apart in *.

(* frame facts: a field, a byte string, a string read through a reader that agrees on the bytes read *)
Lemma s1_aval_frame : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. unfold aval_mem. intros rd rd' a n v H HK k Hk. rewrite HK by lia. exact (H k Hk). Qed.

Lemma s1_bytes_frame : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. unfold abytes_atR. intros rd rd' a l H HK i Hi. rewrite HK by lia. exact (H i Hi). Qed.

Lemma s1_str_frame : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
unfold astr_atR. intros rd rd' p s [H1 H2] HK. split; [|exact H2].
apply (s1_bytes_frame rd); [exact H1|]. intros x Hx. apply HK. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* a call slot: its 56 bytes and the blocks of its arguments *)
Lemma s1_call_frame : forall bl rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl rd' a c P.
Proof.
unfold acall_at. intros bl rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) HK HB.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (s1_aval_frame rd); [exact H4|]; intros x Hx; apply HK; nums; lia|].
split; [apply (s1_aval_frame rd); [exact H5|]; intros x Hx; apply HK; nums; lia|].
split; [exact H6|].
intros k s pn Hs Hp. destruct (H7 k s pn Hs Hp) as (G1 & G2 & G3 & G4 & G5).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
assert (Hin : In pn P) by (eapply nth_error_In; exact Hp).
split; [apply (s1_aval_frame rd); [exact G1|]; intros x Hx; apply HK; nums; lia|].
split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
apply (s1_str_frame rd); [exact G5|]. intros x Hx. apply (HB pn Hin G3). lia.
Qed.

Lemma s1_answer_frame : forall bl rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl rd' gr t q.
Proof.
unfold aanswer_at. intros bl rd rd' gr [x|] [pn|] H HK HB; cbv beta iota in H |- *; try contradiction.
- destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
  split; [apply (s1_aval_frame rd); [exact H1|]; intros y Hy; apply HK; lia|].
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|exact H6].
  apply (s1_str_frame rd); [exact H5|]. intros y Hy. apply (HB pn (or_introl eq_refl) H3). lia.
- apply (s1_aval_frame rd); [exact H|]. intros y Hy. apply HK. lia.
Qed.

Lemma s1_reply_frame : forall bl rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl rd' gr y q.
Proof.
unfold areply_at. intros bl rd rd' gr [x|] [pn|] H HK HB; cbv beta iota in H |- *; try contradiction.
- destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  split; [apply (s1_aval_frame rd); [exact H1|]; intros z Hz; apply HK; nums; lia|].
  split; [apply (s1_aval_frame rd); [exact H2|]; intros z Hz; apply HK; nums; lia|].
  split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [|exact H8].
  apply (s1_bytes_frame rd); [exact H7|]. intros z Hz. apply (HB pn (or_introl eq_refl) H5). lia.
- destruct H as [H1 H2]. split.
  + apply (s1_aval_frame rd); [exact H1|]. intros z Hz. apply HK. nums. lia.
  + apply (s1_aval_frame rd); [exact H2|]. intros z Hz. apply HK. nums. lia.
Qed.

(* the blocks of a layout's parts are lay blocks *)
Lemma s1_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn HP Hp. unfold lay_blocks. apply in_or_app; left. apply in_concat. exists P.
split; [eapply nth_error_In; exact HP | exact Hp].
Qed.

Lemma s1_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn Hp. unfold lay_blocks. apply in_or_app; right. apply in_or_app; left. exact Hp. Qed.

Lemma s1_in_answer : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn Hp. unfold lay_blocks. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hp.
Qed.

Lemma s1_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn Hp. unfold lay_blocks. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hp.
Qed.

(* the answer, the reply and the scalars: the fixed fields of g_rec outside ncalls and the call table *)
Lemma s1_rest_frame : forall bl rd rd' gr R Q,
  aanswer_at bl rd gr (r_answer R) (l_answer Q) -> areply_at bl rd gr (r_reply R) (l_reply Q) -> ag1_scalars rd gr R ->
  (forall x, (gr <= x < gr + 8 \/ gr + OFF_ANSWER <= x < gr + REC_SIZE) -> rd' x = rd x) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl rd' gr (r_answer R) (l_answer Q) /\ areply_at bl rd' gr (r_reply R) (l_reply Q) /\ ag1_scalars rd' gr R.
Proof.
intros bl rd rd' gr R Q HA HR HS HK HB. split; [|split].
- apply (s1_answer_frame bl rd); [exact HA | intros x Hx; apply HK; nums; lia |].
  intros pn Hp Hb x Hx. exact (HB pn (s1_in_answer Q pn Hp) Hb x Hx).
- apply (s1_reply_frame bl rd); [exact HR | intros x Hx; apply HK; nums; lia |].
  intros pn Hp Hb x Hx. exact (HB pn (s1_in_reply Q pn Hp) Hb x Hx).
- unfold ag1_scalars in *. destruct HS as (S1 & S2 & S3 & S4 & S5 & S6).
  split; [apply (s1_aval_frame rd); [exact S1|]; intros x Hx; apply HK; nums; lia|].
  split; [apply (s1_aval_frame rd); [exact S2|]; intros x Hx; apply HK; nums; lia|].
  split; [apply (s1_aval_frame rd); [exact S3|]; intros x Hx; apply HK; nums; lia|].
  split; [apply (s1_aval_frame rd); [exact S4|]; intros x Hx; apply HK; nums; lia|].
  split; [apply (s1_aval_frame rd); [exact S5|]; intros x Hx; apply HK; nums; lia|].
  exact S6.
Qed.

(* the call table's slots, kept by a reader that agrees on the table's used part and the argument blocks *)
Lemma s1_slots_frame : forall bl rd rd' gr R Q,
  (forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
    acall_at bl rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
  (forall x, gr + OFF_CALLS <= x < gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) -> rd' x = rd x) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  (forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
    acall_at bl rd' (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
Proof.
intros bl rd rd' gr R Q H HK HB i c P Hc HP. destruct (H i c P Hc HP) as [H1 H2]. split; [|exact H2].
assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
apply (s1_call_frame bl rd); [exact H1 | |].
- intros x Hx. apply HK. nums. lia.
- intros pn Hp Hb x Hx. exact (HB pn (s1_in_calls Q i P pn HP Hp) Hb x Hx).
Qed.

Lemma s1_lay_append : forall Q,
  lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q.
Proof.
intros Q. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat app].
rewrite app_nil_r. reflexivity.
Qed.

Lemma s1_record_room : forall R fn A, (length (r_calls R) < 16)%nat ->
  rec_record R fn A = set_calls R (r_calls R ++ [(fn, A)]).
Proof. intros R fn A H. unfold rec_record. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

(* the three representation lemmas, with the bound LIM and its two hypotheses as arguments *)
Lemma s1_kept : forall bl LIM,
  (forall p k, In (p, k) bl -> 0 <= p /\ p + k <= LIM) -> A_REC_SPILL + SC_SIZE <= LIM ->
  forall rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, 0 <= a < LIM -> rd' a = rd a) ->
  arep_at bl rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl LIM BL RL rd rd' R Q H HK. assert (G0 : 0 <= A_G_REC) by (unfold A_G_REC; lia).
destruct H as (M1 & M2 & M3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & HS & HO).
assert (E : A_G_REC + REC_SIZE <= A_REC_SPILL) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE; lia).
assert (HB : forall pn, In pn (lay_blocks Q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros [p k] _ Hb x Hx. cbn [fst snd] in Hx. pose proof (BL p k Hb). apply HK. lia. }
assert (HKr : forall x, (A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= x < A_G_REC + REC_SIZE) -> rd' x = rd x).
{ intros x Hx. apply HK. nums. lia. }
assert (HKs : forall x, A_G_REC + OFF_CALLS <= x < A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  rd' x = rd x) by (intros x Hx; apply HK; nums; lia).
destruct (s1_rest_frame bl rd rd' A_G_REC R Q HA HR HS HKr HB) as (HA' & HR' & HS').
unfold arep_at, ag1_calls. split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
split; [|split; [exact HA'|split; [exact HR'|split; [exact HS'|exact HO]]]].
split; [exact C1|]. split; [exact C2|].
split; [apply (s1_aval_frame rd); [exact C3|]; intros x Hx; apply HK; nums; lia|].
split; [exact (s1_slots_frame bl rd rd' A_G_REC R Q C4 HKs HB)|].
split; [|exact C6].
apply (s1_call_frame bl rd); [exact C5 | intros x Hx; apply HK; nums; lia |].
intros pn Hp Hb x Hx. exact (HB pn (s1_in_spill Q pn Hp) Hb x Hx).
Qed.

Lemma s1_spill_set : forall bl LIM,
  (forall p k, In (p, k) bl -> 0 <= p /\ p + k <= LIM) -> A_REC_SPILL + SC_SIZE <= LIM ->
  forall rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  snd (r_spill R) = [] ->
  (forall a, 0 <= a < LIM -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 REC_REMOVE_ALL ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  arep_at bl rd' A_G_REC A_REC_SPILL (set_spill R (REC_REMOVE_ALL, [])) Q.
Proof.
intros bl LIM BL RL rd rd' R Q H Hs HK Hfn Hna. assert (G0 : 0 <= A_G_REC) by (unfold A_G_REC; lia).
destruct H as (M1 & M2 & M3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & HS & HO).
assert (E : A_G_REC + REC_SIZE <= A_REC_SPILL) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE; lia).
assert (HB : forall pn, In pn (lay_blocks Q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros [p k] Hl Hb x Hx. pose proof (BL p k Hb). destruct HO as [_ HO]. destruct (HO (p, k) Hl) as [_ A2].
  cbn [fst snd] in *. apply HK; nums; lia. }
assert (HKr : forall x, (A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= x < A_G_REC + REC_SIZE) -> rd' x = rd x).
{ intros x Hx. apply HK; nums; lia. }
assert (HKs : forall x, A_G_REC + OFF_CALLS <= x < A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  rd' x = rd x) by (intros x Hx; apply HK; nums; lia).
destruct (s1_rest_frame bl rd rd' A_G_REC R Q HA HR HS HKr HB) as (HA' & HR' & HS').
destruct C5 as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
unfold arep_at, ag1_calls, set_spill. cbn [r_refuse r_code r_calls r_spill r_answer r_nreplies r_reply r_state r_host].
split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
split; [|split; [exact HA'|split; [exact HR'|split; [exact HS'|exact HO]]]].
split; [exact C1|]. split; [exact C2|].
split; [apply (s1_aval_frame rd); [exact C3|]; intros x Hx; apply HK; nums; lia|].
split; [exact (s1_slots_frame bl rd rd' A_G_REC R Q C4 HKs HB)|].
split; [|cbn [snd]; constructor].
unfold acall_at. cbn [fst snd length].
split; [unfold REC_REMOVE_ALL, REC_FN_COUNT; lia|]. split; [lia|]. split; [rewrite P3, Hs; reflexivity|].
split; [exact Hfn|]. split; [exact Hna|]. split; [exact P6|].
intros k s pn Hk. destruct k; discriminate Hk.
Qed.

Lemma s1_append : forall bl LIM,
  (forall p k, In (p, k) bl -> 0 <= p /\ p + k <= LIM) -> A_REC_SPILL + SC_SIZE <= LIM ->
  forall rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (length (r_calls R) < 16)%nat ->
  let c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) in
  (forall a, 0 <= a < LIM -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 8) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 REC_REMOVE_ALL ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R REC_REMOVE_ALL [])
    (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl LIM BL RL rd rd' R Q H Hn. cbv zeta. intros HK Hnc Hfn Hna. assert (G0 : 0 <= A_G_REC) by (unfold A_G_REC; lia).
destruct H as (M1 & M2 & M3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & HS & HO).
assert (E : A_G_REC + REC_SIZE <= A_REC_SPILL) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE; lia).
assert (HB : forall pn, In pn (lay_blocks Q) -> In pn bl -> forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros [p k] Hl Hb x Hx. pose proof (BL p k Hb). destruct HO as [_ HO]. destruct (HO (p, k) Hl) as [A1 _].
  cbn [fst snd] in *. apply HK; nums; lia. }
assert (HKr : forall x, (A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + OFF_ANSWER <= x < A_G_REC + REC_SIZE) -> rd' x = rd x).
{ intros x Hx. apply HK; nums; lia. }
assert (HKs : forall x, A_G_REC + OFF_CALLS <= x < A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  rd' x = rd x) by (intros x Hx; apply HK; nums; lia).
destruct (s1_rest_frame bl rd rd' A_G_REC R Q HA HR HS HKr HB) as (HA' & HR' & HS').
rewrite (s1_record_room R REC_REMOVE_ALL [] Hn).
unfold arep_at, ag1_calls, ag1_own, set_calls.
cbn [r_refuse r_code r_calls r_spill r_answer r_nreplies r_reply r_state r_host l_calls l_spill l_answer l_reply].
split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
split; [|split; [exact HA'|split; [exact HR'|split; [exact HS'|rewrite s1_lay_append; exact HO]]]].
rewrite !length_app. cbn [length].
split; [lia|]. split; [rewrite C2; reflexivity|].
split; [rewrite Nat2Z.inj_add; exact Hnc|].
split.
{ intros i c0 P Hc HP. destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hc by exact Hlt. rewrite nth_error_app1 in HP by lia.
    exact (s1_slots_frame bl rd rd' A_G_REC R Q C4 HKs HB i c0 P Hc HP).
  - assert (Hi : i = length (r_calls R)).
    { assert (Hl : (i < length (r_calls R ++ [(REC_REMOVE_ALL, [])]))%nat)
        by (apply nth_error_Some; rewrite Hc; discriminate).
      rewrite length_app in Hl. cbn [length] in Hl. lia. }
    subst i. rewrite nth_error_app2 in Hc by lia. rewrite Nat.sub_diag in Hc. cbn [nth_error] in Hc.
    injection Hc as Hc. subst c0.
    rewrite nth_error_app2 in HP by lia. rewrite C2, Nat.sub_diag in HP. cbn [nth_error] in HP.
    injection HP as HP. subst P.
    split; [|cbn [snd]; constructor].
    unfold acall_at. cbn [fst snd length map].
    split; [unfold REC_REMOVE_ALL, REC_FN_COUNT; lia|]. split; [lia|]. split; [reflexivity|].
    split; [exact Hfn|]. split; [exact Hna|]. split; [constructor|].
    intros k s pn Hk. destruct k; discriminate Hk. }
split; [|exact C6].
apply (s1_call_frame bl rd); [exact C5 | intros x Hx; apply HK; nums; lia |].
intros pn Hp Hb x Hx. exact (HB pn (s1_in_spill Q pn Hp) Hb x Hx).
Qed.

Section s.
Variable bl : list (Z * Z).
Variable LIM : Z.
(* every live block lies below LIM; the recorder's objects too *)
Hypothesis BL : forall p k, In (p, k) bl -> 0 <= p /\ p + k <= LIM.
Hypothesis RLIM : A_REC_SPILL + SC_SIZE <= LIM.

(* the call table holds n < 16 calls: record() appends (3, []) in slot n and sets ncalls to n + 1 *)
Lemma arep_append : forall rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (length (r_calls R) < 16)%nat ->
  let c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) in
  (forall a, 0 <= a < LIM -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 8) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 REC_REMOVE_ALL ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R REC_REMOVE_ALL [])
    (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof. exact (s1_append bl LIM BL RLIM). Qed.

(* the spill holds no arguments: record() writes (3, []) there *)
Lemma arep_spill_set : forall rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  snd (r_spill R) = [] ->
  (forall a, 0 <= a < LIM -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 REC_REMOVE_ALL ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  arep_at bl rd' A_G_REC A_REC_SPILL (set_spill R (REC_REMOVE_ALL, [])) Q.
Proof. exact (s1_spill_set bl LIM BL RLIM). Qed.

(* the recorder's state read through a reader that agrees below LIM *)
Lemma arep_kept : forall rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, 0 <= a < LIM -> rd' a = rd a) ->
  arep_at bl rd' A_G_REC A_REC_SPILL R Q.
Proof. exact (s1_kept bl LIM BL RLIM). Qed.
End s.

(* the answer cell: 0, or the start of the answer's block *)
Lemma arep_answer_cell : forall bl rd R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\
    ((l_answer Q = None /\ old = 0) \/ (exists pn, l_answer Q = Some pn /\ old = fst pn)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold aanswer_at in HA.
destruct (r_answer R) as [x|] eqn:E1; destruct (l_answer Q) as [pn|] eqn:E2; rewrite ?E1, ?E2 in HA;
  cbv beta iota in HA; try contradiction.
- exists (fst pn). split; [exact (proj1 HA)|]. right. exists pn. split; reflexivity.
- exists 0. split; [exact HA|]. left. split; reflexivity.
Qed.

Lemma lay_blocks_append : forall Q,
  forall pn, In pn (lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q))) <-> In pn (lay_blocks Q).
Proof. intros Q pn. rewrite s1_lay_append. split; intros H; exact H. Qed.

Lemma sup_remove_all_m_eq : forall R,
  sup_remove_all_m R = rec_answer (rec_record R REC_REMOVE_ALL []) (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true.
Proof. intros R. unfold sup_remove_all_m, rec_stub. reflexivity. Qed.

Lemma rec_record_full : forall R, (16 <= length (r_calls R))%nat ->
  rec_record R REC_REMOVE_ALL [] = set_spill (set_spill R (fst (r_spill R), [])) (REC_REMOVE_ALL, []).
Proof. intros R H. unfold rec_record. rewrite (proj2 (Nat.ltb_ge _ _) H). reflexivity. Qed.

Lemma rec_record_append_nth : forall R, (length (r_calls R) < 16)%nat ->
  nth_error (r_calls (rec_record R REC_REMOVE_ALL [])) (length (r_calls R)) = Some (REC_REMOVE_ALL, []) /\
  r_refuse (rec_record R REC_REMOVE_ALL []) = r_refuse R.
Proof.
intros R H. rewrite (s1_record_room R REC_REMOVE_ALL [] H). unfold set_calls. cbn [r_calls r_refuse].
split; [|reflexivity]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
