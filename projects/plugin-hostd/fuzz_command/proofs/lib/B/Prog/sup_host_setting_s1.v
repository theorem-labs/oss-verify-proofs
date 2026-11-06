(* The recorder's facts of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command): the B twin of the ASan
   walk's lib/A/Prog/sup_host_setting_s1.v (a working branch e323bbe76d2), over B's rec_repA
   (lib/B/Prog/CmdRep.v, the A form at B's addresses). B calls record() and arg_s() (their statements give rec_repA
   after each step), so only the parts the B walk needs are kept: reads kept (hs_aval_kept .. hs_rec_kept), the
   host-settings digest store (hs_rec_host, recorder.c:376), and what the walk reads of a recorder (the call count,
   the host digest, the last call for mix_call's pre, the owned blocks). The slot is record_c.v's rec_slot. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the bytes of the recorder's two statics *)
Definition hs_in_rec (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).

(* a byte of one of the blocks in O *)
Definition hs_in_own (O : list (Z * Z)) (a : Z) : Prop := exists pn, In pn O /\ fst pn <= a < fst pn + snd pn.

Lemma hs_slot_bounds : forall R,
A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\ rec_slot R mod 8 = 0 /\
((rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ rec_slot R = A_REC_SPILL).
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE, OFF_ANSWER.
  split; [lia|]. split; [lia|]. split; [|left; lia].
  replace (6173376 + 16 + 56 * Z.of_nat (length (r_calls R))) with ((771674 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia.
  apply Z.mod_mul. lia.
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE. split; [lia|]. split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.
(* ---------- reads kept: a field, a byte string and a C string read through a reader that agrees on their bytes ---------- *)
Lemma hs_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.

Lemma hs_bytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite Hk by lia. exact (H i Hi). Qed.

Lemma hs_str_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall x, a <= x < a + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (hs_bytes_kept rd); [exact H1|].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hk. lia.
Qed.

(* the range tactic: every address fact of the recorder's layout, as numbers *)
Ltac hs_rng := unfold hs_in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER,
  OFF_REPLY, OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, CALL_SIZE, CALL_OFF_FN,
  CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.

(* a call kept: its 56 bytes and the bytes of its argument blocks are kept, and its blocks stay live *)
Lemma hs_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl -> In pn bl') ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (hs_aval_kept rd); [exact H4 | intros x Hx; apply Ha; unfold CALL_OFF_FN, CALL_SIZE in *; lia]|].
split; [apply (hs_aval_kept rd); [exact H5 | intros x Hx; apply Ha; unfold CALL_OFF_NARGS, CALL_SIZE in *; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
split; [apply (hs_aval_kept rd); [exact G1 | intros x Hx; apply Ha; unfold CALL_OFF_ARGS, CALL_SIZE in *; lia]|].
split; [exact G2|]. split; [exact (Hbl pn (nth_error_In _ _ Hpn) G3)|]. split; [exact G4|].
apply (hs_str_kept rd); [exact G5 | intros x Hx; apply (Hp pn); [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

Lemma hs_answer_kept : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, In pn (oblk q) -> In pn bl -> In pn bl') ->
(forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
(forall pn x, In pn (oblk q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Hbl Ha Hp. unfold aanswer_at in *.
destruct t as [y|], q as [pn|]; try contradiction.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6).
  split; [apply (hs_aval_kept rd); [exact A1 | intros z Hz; apply Ha; lia]|].
  split; [exact A2|]. split; [exact (Hbl pn (or_introl eq_refl) A3)|]. split; [exact A4|].
  split; [apply (hs_str_kept rd); [exact A5 | intros z Hz; apply (Hp pn); [left; reflexivity | lia]] | exact A6].
- apply (hs_aval_kept rd); [exact H | intros z Hz; apply Ha; lia].
Qed.

Lemma hs_reply_kept : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, In pn (oblk q) -> In pn bl -> In pn bl') ->
(forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
(forall pn x, In pn (oblk q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Hbl Ha Hp. unfold areply_at in *. unfold OFF_REPLY_SIZE.
destruct y as [w|], q as [pn|]; try contradiction.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  split; [apply (hs_aval_kept rd); [exact A1 | intros z Hz; apply Ha; lia]|].
  split; [apply (hs_aval_kept rd); [exact A2 | intros z Hz; apply Ha; unfold OFF_REPLY in *; lia]|].
  split; [exact A3|]. split; [exact A4|]. split; [exact (Hbl pn (or_introl eq_refl) A5)|]. split; [exact A6|].
  split; [apply (hs_bytes_kept rd); [exact A7 | intros z Hz; apply (Hp pn); [left; reflexivity | lia]] | exact A8].
- destruct H as [A1 A2].
  split; [apply (hs_aval_kept rd); [exact A1 | intros z Hz; apply Ha; lia]|].
  apply (hs_aval_kept rd); [exact A2 | intros z Hz; apply Ha; unfold OFF_REPLY in *; lia].
Qed.

Lemma hs_scalars_kept : forall (rd rd' : reader) gr R, ag1_scalars rd gr R ->
(forall x, (gr <= x < gr + 8) \/ (gr + OFF_NREPLIES <= x < gr + OFF_NREPLIES + 4) \/
  (gr + OFF_STATE <= x < gr + OFF_HOST + 8) -> rd' x = rd x) ->
ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R (S1 & S2 & S3 & S4 & S5 & S6) Hk. unfold ag1_scalars.
unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
refine (conj _ (conj _ (conj _ (conj _ (conj _ S6))))); apply (hs_aval_kept rd);
first [exact S1 | exact S2 | exact S3 | exact S4 | exact S5 | intros x Hx; apply Hk; lia].
Qed.

(* where the blocks of a layout come from *)
Lemma hs_lay_call : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn HP Hin. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ HP) | exact Hin].
Qed.
Lemma hs_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact H. Qed.
Lemma hs_lay_rep : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact H.
Qed.

(* the calls of g_rec's table kept, each through its own 56 bytes *)
Lemma hs_table_kept : forall bl bl' (rd rd' : reader) R Q,
(forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
  acall_at bl rd (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall i x, (i < length (r_calls R))%nat ->
  A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i <= x < A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
  acall_at bl' rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c).
Proof.
intros bl bl' rd rd' R Q C4 Hbl Hk Hp i c P Hc HP.
destruct (C4 i c P Hc HP) as [HC HF]. split; [|exact HF].
assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
apply (hs_acall_kept bl _ rd _ _ _ _ HC).
- intros pn Hin Hb. exact (Hbl pn (hs_lay_call Q i P pn HP Hin) Hb).
- intros x Hx. exact (Hk i x Hi Hx).
- intros pn x Hin Hx. exact (Hp pn x (hs_lay_call Q i P pn HP Hin) Hx).
Qed.

Lemma hs_calls_kept : forall bl bl' (rd rd' : reader) R Q, ag1_calls bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall x, (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_ANSWER) \/ (A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE) -> rd' x = rd x) ->
(forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
ag1_calls bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q (C1 & C2 & C3 & C4 & C5 & C6) Hbl Hk Hp.
unfold ag1_calls. split; [exact C1|]. split; [exact C2|].
split; [apply (hs_aval_kept rd); [exact C3 | intros x Hx; apply Hk; left; unfold OFF_NCALLS, OFF_ANSWER in *; lia]|].
split; [|split; [|exact C6]].
- refine (hs_table_kept bl bl' rd rd' R Q C4 Hbl _ Hp).
  intros i x Hi Hx. apply Hk. left. unfold OFF_NCALLS, OFF_ANSWER, OFF_CALLS, CALL_SIZE in *. lia.
- apply (hs_acall_kept bl _ rd _ _ _ _ C5).
  + intros pn Hin Hb. exact (Hbl pn (hs_lay_spill Q pn Hin) Hb).
  + intros x Hx. apply Hk. right. unfold CALL_SIZE, SC_SIZE in *. lia.
  + intros pn x Hin Hx. exact (Hp pn x (hs_lay_spill Q pn Hin) Hx).
Qed.

(* a byte of an owned block is no byte of the recorder's statics *)
Lemma hs_own_out : forall Q pn x, ag1_own A_G_REC A_REC_SPILL Q -> In pn (lay_blocks Q) ->
fst pn <= x < fst pn + snd pn -> ~ hs_in_rec x.
Proof.
intros Q pn x [_ HO] Hin Hx. destruct (HO pn Hin) as [H1 H2]. unfold iv_apart, hs_in_rec in *. lia.
Qed.

(* every block of a layout is live and at least one byte long *)
Lemma hs_acall_blocks : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) pn Hin.
destruct (In_nth_error _ _ Hin) as [k Hk].
assert (Hk2 : (k < length (snd c))%nat) by (rewrite <- H3; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (H7 k s pn Hs Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
Qed.

Lemma hs_lay_info : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
forall pn, In pn (lay_blocks Q) -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & _ & _) pn Hin.
unfold lay_blocks in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_concat in Hin as (P & HP & Hin).
  destruct (In_nth_error _ _ HP) as [i Hi].
  assert (Hi2 : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  exact (hs_acall_blocks _ _ _ _ _ (proj1 (C4 i c P Hc Hi)) pn Hin).
- apply in_app_iff in Hin as [Hin|Hin]; [exact (hs_acall_blocks _ _ _ _ _ C5 pn Hin)|].
  apply in_app_iff in Hin as [Hin|Hin].
  + unfold aanswer_at in HA. destruct (r_answer R) as [x|], (l_answer Q) as [q|]; cbn in Hin; try contradiction.
    destruct Hin as [<- | []]. destruct HA as (_ & _ & A3 & A4 & _). split; [exact A3 | lia].
  + unfold areply_at in HR. destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn in Hin; try contradiction.
    destruct Hin as [<- | []]. destruct HR as (_ & _ & _ & A4 & A5 & A6 & _). split; [exact A5|].
    destruct x as [|b x]; [exfalso; apply A4; reflexivity|]. cbn [length] in A6. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma hs_rec_kept : forall ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall a, hs_in_rec a \/ hs_in_own O a -> rd' a = rd a) ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O [Q [HA HQ]] Hk Hbl. unfold rec_repA. exists Q. split; [|exact HQ].
destruct HA as (G1 & G2 & G3 & HC & HAn & HR & HS & HO).
assert (Hb : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S) -> In pn (ablocks B ly' S'))
  by (intros pn H _; apply Hbl, HQ, H).
assert (Hp : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x)
  by (intros pn x H Hx; apply Hk; right; unfold hs_in_own; exists pn; split; [apply HQ, H | exact Hx]).
assert (Hr : forall x, hs_in_rec x -> rd' x = rd x) by (intros x Hx; apply Hk; left; exact Hx).
clear Hk Hbl.
unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
refine (conj _ (conj _ (conj _ (conj _ HO)))).
- refine (hs_calls_kept _ _ rd rd' R Q HC Hb _ Hp). intros x Hx. apply Hr. hs_rng.
- refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (CmdRecAns.rca_in_answer Q pn H)) _
    (fun pn x H => Hp pn x (CmdRecAns.rca_in_answer Q pn H))).
  intros x Hx. apply Hr. hs_rng.
- refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
  intros x Hx. apply Hr. hs_rng.
- refine (hs_scalars_kept rd rd' A_G_REC R HS _). intros x Hx. apply Hr. hs_rng.
Qed.
(* the host-settings digest: g_rec.host_settings := h *)
Lemma hs_rec_host : forall ly S (rd rd' : reader) R O h,
rec_repA B ly S rd R O -> 0 <= h < 2 ^ 64 ->
aval_mem rd' (A_G_REC + OFF_HOST) 8 h ->
(forall a, hs_in_rec a \/ hs_in_own O a -> ~ (A_G_REC + OFF_HOST <= a < A_G_REC + OFF_HOST + 8) -> rd' a = rd a) ->
rec_repA B ly S rd' (set_host R h) O.
Proof.
intros ly S rd rd' R O h [Q [HA HQ]] Hh Hv Hk0. unfold rec_repA. exists Q. split; [|exact HQ].
assert (Hk : forall x, hs_in_rec x -> ~ (A_G_REC + OFF_HOST <= x < A_G_REC + OFF_HOST + 8) -> rd' x = rd x)
  by (intros x Hx; apply Hk0; left; exact Hx).
destruct HA as (G1 & G2 & G3 & HC & HAn & HR & HS & HO).
assert (Hb : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S) -> In pn (ablocks B ly S))
  by (intros pn _ H; exact H).
assert (Hp : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros pn x H Hx. pose proof (hs_own_out Q pn x HO H Hx) as N.
  apply Hk0; [right; unfold hs_in_own; exists pn; split; [apply HQ, H | exact Hx] | intros Hy; apply N; hs_rng]. }
unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
refine (conj _ (conj _ (conj _ (conj _ HO)))).
- change (ag1_calls (ablocks B ly S) rd' A_G_REC A_REC_SPILL R Q).
  refine (hs_calls_kept _ _ rd rd' R Q HC Hb _ Hp). intros x Hx. apply Hk; hs_rng.
- cbn [set_host r_answer].
  refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (CmdRecAns.rca_in_answer Q pn H)) _
    (fun pn x H => Hp pn x (CmdRecAns.rca_in_answer Q pn H))).
  intros x Hx. apply Hk; hs_rng.
- cbn [set_host r_reply].
  refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
  intros x Hx. apply Hk; hs_rng.
- unfold ag1_scalars in *. cbn [set_host r_refuse r_code r_nreplies r_state r_host].
  destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  refine (conj _ (conj _ (conj _ (conj _ (conj Hv (conj S6 (conj S7 (conj S8 (conj S9 Hh))))))))).
  + apply (hs_aval_kept rd); [exact S1 | intros x Hx; apply Hk; hs_rng].
  + apply (hs_aval_kept rd); [exact S2 | intros x Hx; apply Hk; hs_rng].
  + apply (hs_aval_kept rd); [exact S3 | intros x Hx; apply Hk; hs_rng].
  + apply (hs_aval_kept rd); [exact S4 | intros x Hx; apply Hk; hs_rng].
Qed.

(* what the walk reads of a recorder: the call count, the host digest, and the last call (mix_call's pre) *)
Lemma hs_rec_ncalls : forall ly S rd R O,
rec_repA B ly S rd R O ->
(length (r_calls R) <= 16)%nat /\ aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))).
Proof.
intros ly S rd R O [Q [(_ & _ & _ & (C1 & _ & C3 & _) & _) _]]. split; [exact C1 | exact C3].
Qed.

Lemma hs_rec_hostval : forall ly S rd R O,
rec_repA B ly S rd R O -> aval_mem rd (A_G_REC + OFF_HOST) 8 (r_host R) /\ 0 <= r_host R < 2 ^ 64.
Proof.
intros ly S rd R O [Q [(_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & S5 & _ & _ & _ & _ & S10) & _) _]].
split; [exact S5 | exact S10].
Qed.

Lemma hs_rec_last : forall ly S rd R A O,
rec_repA B ly S rd (rec_record R REC_HOST_SETTING A) O ->
exists P, acall_at (ablocks B ly S) rd (rec_slot R) (REC_HOST_SETTING, A) P /\ (forall pn, In pn P -> In pn O).
Proof.
intros ly S rd R A O [Q [HA HQ]].
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
- rewrite (rec_record_calls R REC_HOST_SETTING A Hlt) in C2, C4. cbn [set_calls r_calls] in C2, C4.
  rewrite length_app in C2. cbn [length] in C2.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
  assert (Hc : nth_error (r_calls R ++ [(REC_HOST_SETTING, A)]) (length (r_calls R)) = Some (REC_HOST_SETTING, A))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  destruct (C4 _ _ _ Hc HP) as [HC _].
  exists P. split; [exact HC|].
  intros pn Hin. apply HQ. exact (hs_lay_call Q _ P pn HP Hin).
- assert (E : Nat.ltb (length (r_calls R)) 16 = false) by (apply Nat.ltb_ge; exact Hge).
  unfold rec_record in C5. rewrite E in C5. cbn [set_spill r_spill] in C5.
  exists (l_spill Q). split; [exact C5|].
  intros pn Hin. apply HQ. exact (hs_lay_spill Q pn Hin).
Qed.

(* the owned blocks are live and apart from the recorder's statics *)
Lemma hs_rec_own : forall ly S rd R O,
rec_repA B ly S rd R O ->
forall pn, In pn O -> In pn (ablocks B ly S) /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\
  iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
intros ly S rd R O [Q [HA HQ]] pn Hin. apply HQ in Hin.
destruct (hs_lay_info _ _ _ _ _ _ HA pn Hin) as [Hb _].
destruct HA as (_ & _ & _ & _ & _ & _ & _ & (_ & HO)). destruct (HO pn Hin) as [H1 H2].
split; [exact Hb|]. split; [exact H1 | exact H2].
Qed.
(* the recorder's owned blocks are a set: the order of O does not matter *)
Lemma hs_rec_perm : forall ly S rd R O O', rec_repA B ly S rd R O -> (forall pn, In pn O <-> In pn O') ->
rec_repA B ly S rd R O'.
Proof.
intros ly S rd R O O' [Q [HA HQ]] HO. exists Q. split; [exact HA|]. intros pn. rewrite <- HO. exact (HQ pn).
Qed.
End d.
