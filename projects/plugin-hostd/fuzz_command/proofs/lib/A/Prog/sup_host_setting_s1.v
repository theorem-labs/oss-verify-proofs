(* The recorder's model steps of sup_host_setting's ASan walk (plugin-hostd/fuzz_command): what the inlined
   record() (recorder.c:205-221) and each appended argument (arg_line, arg_i, the inlined arg_s) do to
   `rec_repA` (lib/A/Prog/CmdRep.v), and the host-settings digest store of recorder.c:376.

   - hs_slot R: the slot record() picks for the next call: g_rec.calls[ncalls] while the table holds fewer than
     16 calls, else record.spill (RecModel.v:38-39 `rec_record`).
   - hs_rec_kept: the recorder is kept when the bytes of g_rec, record.spill and the owned blocks are kept and the
     owned blocks stay live.
   - hs_rec_join_slot / hs_rec_join_spill: after record()'s ncalls store (table arm) or after rec_calls_free on the
     spill (spill arm), the stores c->fn := 6, c->nargs := 0 give the recorder of `rec_record R 6 []`
     (`rec_repJ`: the recorder up to those two stores).
   - hs_rec_arg: c->nargs := m + 1 and c->args[m] := p, p a fresh block holding s, append s.
   - hs_rec_host: g_rec.host_settings := h.
   Each step is the plain proof's model step (the sinvT lemmas of lib/Prog/sup_host_setting.v) over the ASan reader. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot the next recorded call takes *)
Definition hs_slot (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
else A_REC_SPILL.

(* the bytes of the recorder's two statics *)
Definition hs_in_rec (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).

(* a byte of one of the blocks in O *)
Definition hs_in_own (O : list (Z * Z)) (a : Z) : Prop := exists pn, In pn O /\ fst pn <= a < fst pn + snd pn.

Lemma hs_slot_bounds : forall R,
A_G_REC + OFF_CALLS <= hs_slot R /\ hs_slot R + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\ hs_slot R mod 8 = 0 /\
((hs_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ hs_slot R = A_REC_SPILL).
Proof.
intros R. unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE, OFF_ANSWER.
  split; [lia|]. split; [lia|]. split; [|left; lia].
  replace (6174528 + 16 + 56 * Z.of_nat (length (r_calls R))) with ((771818 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia.
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
Lemma hs_lay_ans : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact H.
Qed.
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

(* the call record() leaves before its first argument: fn 6, no arguments *)
Lemma hs_acall_empty : forall bl (rd : reader) a,
aval_mem rd a 4 REC_HOST_SETTING -> aval_mem rd (a + CALL_OFF_NARGS) 4 0 ->
acall_at bl rd a (REC_HOST_SETTING, []) [].
Proof.
intros bl rd a HF HN. unfold acall_at. cbn [fst snd length].
split; [unfold REC_HOST_SETTING, REC_FN_COUNT; lia|]. split; [lia|]. split; [reflexivity|].
split; [unfold CALL_OFF_FN; rewrite Z.add_0_r; exact HF|]. split; [exact HN|].
split; [constructor|]. intros k s pn Hs. destruct k; cbn in Hs; discriminate Hs.
Qed.

(* NoDup here is stdpp's (stdpp.base.NoDup, over its list membership ∈); the two memberships agree *)
Lemma hs_elem_In : forall (T : Type) (x : T) (l : list T), x ∈ l -> In x l.
Proof.
intros T x l H. induction l as [|y t IH]; [inversion H|].
inversion H; subst; [left; reflexivity | right; apply IH; assumption].
Qed.

Lemma hs_In_elem : forall (T : Type) (x : T) (l : list T), In x l -> x ∈ l.
Proof.
intros T x l H. induction l as [|y t IH]; [destruct H|].
destruct H as [<- | H]; [constructor | constructor; apply IH; exact H].
Qed.

Lemma hs_nodup_snoc : forall (T : Type) (l : list T) a, NoDup l -> ~ In a l -> NoDup (l ++ [a]).
Proof.
intros T l. induction l as [|b t IH]; cbn [app]; intros a Hnd Hn.
- constructor; [intros Hin; apply hs_elem_In in Hin; destruct Hin | constructor].
- inversion Hnd as [|b' t' Hb Ht]; subst. constructor.
  + intros Hin. apply hs_elem_In in Hin. apply in_app_iff in Hin as [Hin | [<- | []]];
      [exact (Hb (hs_In_elem _ _ _ Hin)) | apply Hn; left; reflexivity].
  + apply IH; [exact Ht | intros Hin; apply Hn; right; exact Hin].
Qed.

Lemma hs_nodup_perm : forall (T : Type) (l l' : list T), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
intros T l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' HP1 IH1 HP2 IH2]; intros H.
- exact H.
- inversion H as [|x' t Hx Ht]; subst. constructor.
  + intros Hin. apply Hx. apply hs_In_elem. apply (Permutation_in _ (Permutation_sym HP)). apply hs_elem_In. exact Hin.
  + apply IH. exact Ht.
- inversion H as [|y' t Hy Ht]; subst. inversion Ht as [|x' t' Hx Ht']; subst.
  constructor; [|constructor].
  + intros Hin. apply hs_elem_In in Hin. destruct Hin as [<- | Hin].
    * apply Hy. apply hs_In_elem. left. reflexivity.
    * apply Hx. apply hs_In_elem. exact Hin.
  + intros Hin. apply Hy. apply hs_In_elem. right. apply hs_elem_In. exact Hin.
  + exact Ht'.
- apply IH2. apply IH1. exact H.
Qed.

(* one argument appended to a call: nargs := m + 1 and args[m] := p, p a fresh live block holding s *)
Lemma hs_acall_snoc : forall bl bl' (rd rd' : reader) a fn As P s p n,
acall_at bl rd a (fn, As) P -> (length As < 6)%nat ->
aval_mem rd' (a + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
aval_mem rd' (a + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
(forall x, a <= x < a + CALL_OFF_NARGS -> rd' x = rd x) ->
(forall x, a + CALL_OFF_ARGS <= x < a + CALL_OFF_ARGS + 8 * Z.of_nat (length As) -> rd' x = rd x) ->
(forall pn, In pn P -> In pn bl -> In pn bl') ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
~ In p (map fst P) -> p <> 0 -> In (p, n) bl' -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> astr_atR rd' p s ->
acall_at bl' rd' a (fn, As ++ [s]) (P ++ [(p, n)]).
Proof.
intros bl bl' rd rd' a fn As P s p n (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hm HN HA Hk1 Hk2 Hbl Hp Hpn Hp0 Hin Hn Hs.
cbn [fst snd] in H1, H2, H3, H4, H5, H7.
unfold acall_at. cbn [fst snd]. rewrite !length_app. cbn [length].
split; [exact H1|]. split; [lia|]. split; [lia|].
split; [apply (hs_aval_kept rd); [exact H4 | intros x Hx; apply Hk1; unfold CALL_OFF_FN, CALL_OFF_NARGS in *; lia]|].
split; [replace (Z.of_nat (length As + 1)) with (Z.of_nat (length As) + 1) by lia; exact HN|].
split.
{ rewrite map_app. cbn [map fst]. exact (hs_nodup_snoc _ _ _ H6 Hpn). }
intros k s0 pn Hs0 Hpn0.
destruct (Nat.lt_ge_cases k (length As)) as [Hk|Hk].
- rewrite nth_error_app1 in Hs0 by exact Hk. rewrite nth_error_app1 in Hpn0 by lia.
  destruct (H7 k s0 pn Hs0 Hpn0) as (G1 & G2 & G3 & G4 & G5).
  split; [apply (hs_aval_kept rd); [exact G1 | intros x Hx; apply Hk2; lia]|].
  split; [exact G2|]. split; [exact (Hbl pn (nth_error_In _ _ Hpn0) G3)|]. split; [exact G4|].
  apply (hs_str_kept rd); [exact G5 | intros x Hx; apply (Hp pn); [exact (nth_error_In _ _ Hpn0) | lia]].
- destruct (Nat.eq_dec k (length As)) as [->|Hne].
  + rewrite nth_error_app2, Nat.sub_diag in Hs0 by lia. cbn [nth_error] in Hs0. injection Hs0 as <-.
    rewrite nth_error_app2 in Hpn0 by lia. rewrite H3, Nat.sub_diag in Hpn0. cbn [nth_error] in Hpn0.
    injection Hpn0 as <-. cbn [fst snd].
    split; [exact HA|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hn | exact Hs].
  + exfalso. assert (N : nth_error (As ++ [s]) k = None) by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    rewrite N in Hs0. discriminate.
Qed.

(* a list of length n + 1 is its first n elements and its last *)
Lemma hs_split_last : forall (T : Type) (l : list T) n x, length l = S n -> nth_error l n = Some x -> l = firstn n l ++ [x].
Proof.
intros T l. induction l as [|y l IH]; intros n x Hl Hx; [cbn in Hl; discriminate Hl|].
destruct n as [|n].
- destruct l as [|z l]; [|exfalso; cbn in Hl; lia]. cbn in Hx. injection Hx as ->. reflexivity.
- cbn in Hl, Hx |- *. f_equal. apply IH; [lia | exact Hx].
Qed.

(* the layouts after one more block *)
Lemma hs_lay_nil : forall Q, lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q.
Proof.
intros Q. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat app].
rewrite app_nil_r. reflexivity.
Qed.

Lemma hs_perm_call : forall Q L0 P pk, l_calls Q = L0 ++ [P] ->
Permutation (lay_blocks (RLay (L0 ++ [P ++ [pk]]) (l_spill Q) (l_answer Q) (l_reply Q))) (lay_blocks Q ++ [pk]).
Proof.
intros Q L0 P pk HQc. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite HQc.
rewrite !concat_app. cbn [concat]. rewrite !app_nil_r. rewrite <- !app_assoc.
apply Permutation_app_head. apply Permutation_app_head. cbn [app]. rewrite !app_assoc. apply Permutation_cons_append.
Qed.

Lemma hs_perm_spill : forall Q pk,
Permutation (lay_blocks (RLay (l_calls Q) (l_spill Q ++ [pk]) (l_answer Q) (l_reply Q))) (lay_blocks Q ++ [pk]).
Proof.
intros Q pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite <- !app_assoc.
apply Permutation_app_head. apply Permutation_app_head. cbn [app]. rewrite !app_assoc. apply Permutation_cons_append.
Qed.

Lemma hs_own_snoc : forall Q Q' O p n,
Permutation (lay_blocks Q') (lay_blocks Q ++ [(p, n)]) ->
ag1_own A_G_REC A_REC_SPILL Q -> (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
~ In p (map fst (lay_blocks Q)) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
ag1_own A_G_REC A_REC_SPILL Q' /\ (forall pn, In pn (O ++ [(p, n)]) <-> In pn (lay_blocks Q')).
Proof.
intros Q Q' O p n HPm [O1 O2] HQ Hpn Hag Has. split; [split|].
- apply (hs_nodup_perm _ _ _ (Permutation_map fst (Permutation_sym HPm))).
  rewrite map_app. cbn [map fst]. exact (hs_nodup_snoc _ _ _ O1 Hpn).
- intros pn Hin. apply (Permutation_in _ HPm) in Hin. apply in_app_iff in Hin as [Hin | [<- | []]].
  + exact (O2 pn Hin).
  + split; [exact Hag | exact Has].
- intros pn. rewrite in_app_iff. split.
  + intros [Hin | [<- | []]].
    * apply (Permutation_in _ (Permutation_sym HPm)). apply in_app_iff. left. apply HQ, Hin.
    * apply (Permutation_in _ (Permutation_sym HPm)). apply in_app_iff. right. left. reflexivity.
  + intros Hin. apply (Permutation_in _ HPm) in Hin. apply in_app_iff in Hin as [Hin | Hin]; [left; apply HQ, Hin | right; exact Hin].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the recorder after record(), up to its two stores c->fn := 6 and c->nargs := 0 *)
Definition rec_repJ (ly : alayout) (S : astate) (rd : reader) (R : rstate) (O : list (Z * Z)) : Prop :=
forall rd' : reader,
(forall a, hs_in_rec a \/ hs_in_own O a -> ~ (hs_slot R <= a < hs_slot R + 8) -> rd' a = rd a) ->
aval_mem rd' (hs_slot R) 4 REC_HOST_SETTING -> aval_mem rd' (hs_slot R + CALL_OFF_NARGS) 4 0 ->
rec_repA B ly S rd' (rec_record R REC_HOST_SETTING []) O.

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
- refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (hs_lay_ans Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_ans Q pn H))).
  intros x Hx. apply Hr. hs_rng.
- refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
  intros x Hx. apply Hr. hs_rng.
- refine (hs_scalars_kept rd rd' A_G_REC R HS _). intros x Hx. apply Hr. hs_rng.
Qed.

(* the table arm: g_rec.ncalls := n + 1, then the two stores to g_rec.calls[n] *)
Lemma hs_rec_join_slot : forall ly S (rd rd1 : reader) R O,
rec_repA B ly S rd R O -> (length (r_calls R) < 16)%nat ->
aval_mem rd1 (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
(forall a, hs_in_rec a \/ hs_in_own O a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd1 a = rd a) ->
rec_repJ ly S rd1 R O.
Proof.
intros ly S rd rd1 R O [Q [HA HQ]] Hlt HN Hk1. unfold rec_repJ. intros rd' Hk' HF HNa.
assert (Hsl : hs_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
  by (unfold hs_slot; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
rewrite Hsl in Hk', HF, HNa.
assert (Hk : forall x, hs_in_rec x -> ~ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4) ->
  ~ (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) <= x <
     A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + 8) -> rd' x = rd x)
  by (intros x Hx N1 N2; rewrite (Hk' x (or_introl Hx) N2); exact (Hk1 x (or_introl Hx) N1)).
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HAn & HR & HS & HO).
assert (Hp : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros pn x H Hx. pose proof (hs_own_out Q pn x HO H Hx) as N.
  assert (Ho : hs_in_rec x \/ hs_in_own O x) by (right; unfold hs_in_own; exists pn; split; [apply HQ, H | exact Hx]).
  rewrite (Hk' x Ho) by (intros Hy; apply N; hs_rng). apply (Hk1 x Ho). intros Hy; apply N; hs_rng. }
assert (Hb : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S) -> In pn (ablocks B ly S))
  by (intros pn _ H; exact H).
unfold rec_repA. exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
rewrite (hs_lay_nil Q). split; [|exact HQ].
rewrite (rec_record_calls R REC_HOST_SETTING [] Hlt).
unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
refine (conj _ (conj _ (conj _ (conj _ _)))).
- unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
  rewrite !length_app. cbn [length].
  split; [lia|]. split; [lia|].
  split.
  { replace (Z.of_nat (length (r_calls R) + 1)) with (Z.of_nat (length (r_calls R)) + 1) by lia.
    apply (hs_aval_kept rd1); [exact HN|]. intros x Hx. apply Hk'; [left|]; hs_rng. }
  split.
  { intros i c P Hc HP.
    destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
    - rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP by lia.
      destruct (C4 i c P Hc HP) as [HC HFa]. split; [|exact HFa].
      apply (hs_acall_kept _ _ rd _ _ _ _ HC).
      + intros pn _ H. exact H.
      + intros x Hx. apply Hk; hs_rng.
      + intros pn x Hin Hx. exact (Hp pn x (hs_lay_call Q i P pn HP Hin) Hx).
    - destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
      + rewrite nth_error_app2, Nat.sub_diag in Hc by lia. cbn [nth_error] in Hc. injection Hc as <-.
        rewrite nth_error_app2 in HP by lia. rewrite C2, Nat.sub_diag in HP. cbn [nth_error] in HP. injection HP as <-.
        split; [exact (hs_acall_empty _ rd' _ HF HNa) | cbn [snd]; constructor].
      + exfalso. assert (N : nth_error (r_calls R ++ [(REC_HOST_SETTING, [])]) i = None)
          by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
        rewrite N in Hc. discriminate. }
  split; [|exact C6].
  apply (hs_acall_kept _ _ rd _ _ _ _ C5).
  + intros pn _ H. exact H.
  + intros x Hx. apply Hk; hs_rng.
  + intros pn x Hin Hx. exact (Hp pn x (hs_lay_spill Q pn Hin) Hx).
- cbn [set_calls r_answer l_answer].
  refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (hs_lay_ans Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_ans Q pn H))).
  intros x Hx. apply Hk; hs_rng.
- cbn [set_calls r_reply l_reply].
  refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
  intros x Hx. apply Hk; hs_rng.
- refine (hs_scalars_kept rd rd' A_G_REC R HS _). intros x Hx. apply Hk; hs_rng.
- unfold ag1_own. rewrite (hs_lay_nil Q). exact HO.
Qed.

(* the spill arm: rec_calls_free emptied the spill (rec_calls_free_c.v:106-109), then the two stores to record.spill *)
Lemma hs_rec_join_spill : forall ly S (rd : reader) R O,
rec_repA B ly S rd (set_spill R (fst (r_spill R), [])) O -> length (r_calls R) = 16%nat ->
rec_repJ ly S rd R O.
Proof.
intros ly S rd R O [Q [HA HQ]] H16. unfold rec_repJ. intros rd' Hk0 HF HNa.
assert (Hsl : hs_slot R = A_REC_SPILL) by (unfold hs_slot; rewrite H16; reflexivity).
rewrite Hsl in Hk0, HF, HNa.
assert (Hk : forall x, hs_in_rec x -> ~ (A_REC_SPILL <= x < A_REC_SPILL + 8) -> rd' x = rd x)
  by (intros x Hx; apply Hk0; left; exact Hx).
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HAn & HR & HS & HO).
cbn [set_spill r_calls r_spill r_answer r_reply] in C1, C2, C3, C4, C5, C6, HAn, HR.
change (ag1_scalars rd A_G_REC R) in HS.
assert (Hsp : l_spill Q = []).
{ destruct C5 as (_ & _ & H3 & _). cbn [snd length] in H3.
  destruct (l_spill Q); [reflexivity | cbn [length] in H3; discriminate H3]. }
assert (Hp : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros pn x H Hx. pose proof (hs_own_out Q pn x HO H Hx) as N.
  apply Hk0; [right; unfold hs_in_own; exists pn; split; [apply HQ, H | exact Hx] | intros Hy; apply N; hs_rng]. }
assert (Hb : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S) -> In pn (ablocks B ly S))
  by (intros pn _ H; exact H).
unfold rec_repA. exists Q. split; [|exact HQ].
rewrite (rec_record_spill R REC_HOST_SETTING [] H16).
unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
refine (conj _ (conj _ (conj _ (conj _ HO)))).
- unfold ag1_calls. cbn [set_spill r_calls r_spill].
  split; [exact C1|]. split; [exact C2|].
  split; [apply (hs_aval_kept rd); [exact C3 | intros x Hx; apply Hk; hs_rng]|].
  split.
  + refine (hs_table_kept _ _ rd rd' R Q C4 Hb _ Hp). intros i x Hi Hx. apply Hk; hs_rng.
  + rewrite Hsp. split; [exact (hs_acall_empty _ rd' _ HF HNa) | cbn [snd]; constructor].
- cbn [set_spill r_answer].
  refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (hs_lay_ans Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_ans Q pn H))).
  intros x Hx. apply Hk; hs_rng.
- cbn [set_spill r_reply].
  refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
  intros x Hx. apply Hk; hs_rng.
- refine (hs_scalars_kept rd rd' A_G_REC R HS _). intros x Hx. apply Hk; hs_rng.
Qed.

(* one argument appended: c->nargs := m + 1, c->args[m] := p, p a live block holding s, apart from the recorder *)
Lemma hs_rec_arg : forall ly S ly' S' (rd rd' : reader) R As O p n s,
rec_repA B ly S rd (rec_record R REC_HOST_SETTING As) O -> (length As < 6)%nat ->
aval_mem rd' (hs_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
aval_mem rd' (hs_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
(forall a, hs_in_rec a \/ hs_in_own O a ->
 ~ (hs_slot R + CALL_OFF_NARGS <= a < hs_slot R + CALL_OFF_NARGS + 4) ->
 ~ (hs_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < hs_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
 rd' a = rd a) ->
p <> 0 -> astr_atR rd' p s -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> Z.of_nat (length s) <= LMAX ->
In (p, n) (ablocks B ly' S') ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
rec_repA B ly' S' rd' (rec_record R REC_HOST_SETTING (As ++ [s])) (O ++ [(p, n)]).
Proof.
intros ly S ly' S' rd rd' R As O p n s [Q [HA HQ]] HAs HNa HAr Hk Hp0 Hs Hn Hsl Hin Hbl' Hap Hag Has.
pose proof (hs_lay_info _ _ _ _ _ _ HA) as HLI.
destruct (hs_slot_bounds R) as (B1 & B2 & _ & B4).
assert (Hpn : ~ In p (map fst (lay_blocks Q))).
{ intros Hm. apply in_map_iff in Hm as ([q k] & Hq & Hm). cbn [fst] in Hq. subst q.
  destruct (HLI (p, k) Hm) as [_ Hk1]. cbn [snd] in Hk1.
  rewrite Forall_forall in Hap. pose proof (Hap (p, k) (proj2 (HQ (p, k)) Hm)) as Hpk.
  unfold iv_apart in Hpk. cbn [fst snd] in Hpk. lia. }
assert (Hb : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S) -> In pn (ablocks B ly' S'))
  by (intros pn H _; apply Hbl', HQ, H).
assert (Hkr : forall x, hs_in_rec x -> ~ (hs_slot R + CALL_OFF_NARGS <= x < hs_slot R + CALL_OFF_NARGS + 4) ->
  ~ (hs_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= x <
     hs_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) -> rd' x = rd x)
  by (intros x Hx; apply Hk; left; exact Hx).
destruct HA as (G1 & G2 & G3 & HC & HAn & HR & HS & HO).
assert (Hp : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros pn x H Hx. pose proof (hs_own_out Q pn x HO H Hx) as N.
  apply Hk; [right; unfold hs_in_own; exists pn; split; [apply HQ, H | exact Hx] | |]; intros Hy; apply N; hs_rng. }
clear Hk.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
- (* the table arm: the call is g_rec.calls[n], n = length (r_calls R) *)
  assert (Hsl0 : hs_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold hs_slot; apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity).
  assert (Hrr : forall A, rec_record R REC_HOST_SETTING A = set_calls R (r_calls R ++ [(REC_HOST_SETTING, A)]))
    by (intros A; exact (rec_record_calls R REC_HOST_SETTING A Hlt)).
  rewrite Hsl0 in HNa, HAr, Hkr. clear B1 B2 B4.
  rewrite Hrr in HC, HAn, HR, HS.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  cbn [set_calls r_calls r_spill r_answer r_reply] in C1, C2, C3, C4, C5, C6, HAn, HR.
  change (ag1_scalars rd A_G_REC R) in HS.
  rewrite length_app in C1, C2, C3. cbn [length] in C1, C2, C3.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
  assert (HcL : nth_error (r_calls R ++ [(REC_HOST_SETTING, As)]) (length (r_calls R)) = Some (REC_HOST_SETTING, As))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  destruct (C4 _ _ _ HcL HP) as [HCold HFold].
  assert (HQc : exists L0, l_calls Q = L0 ++ [P])
    by (exists (firstn (length (r_calls R)) (l_calls Q)); apply hs_split_last; [lia | exact HP]).
  destruct HQc as [L0 HQc].
  assert (HL0 : length L0 = length (r_calls R)) by (rewrite HQc, length_app in C2; cbn [length] in C2; lia).
  pose proof (hs_perm_call Q L0 P (p, n) HQc) as HPm.
  destruct (hs_own_snoc Q _ O p n HPm HO HQ Hpn Hag Has) as [HO2 HQ2].
  unfold rec_repA. exists (RLay (L0 ++ [P ++ [(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  split; [|exact HQ2].
  rewrite Hrr.
  unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  refine (conj _ (conj _ (conj _ (conj _ HO2)))).
  + unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    rewrite !length_app. cbn [length].
    split; [lia|]. split; [lia|].
    split; [apply (hs_aval_kept rd); [exact C3 | intros x Hx; apply Hkr; hs_rng]|].
    split.
    { intros i c P0 Hc HP0.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      - rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP0 by lia.
        assert (Hc' : nth_error (r_calls R ++ [(REC_HOST_SETTING, As)]) i = Some c)
          by (rewrite nth_error_app1 by exact Hi; exact Hc).
        assert (HP0' : nth_error (l_calls Q) i = Some P0) by (rewrite HQc, nth_error_app1 by lia; exact HP0).
        destruct (C4 i c P0 Hc' HP0') as [HC0 HF0]. split; [|exact HF0].
        apply (hs_acall_kept _ _ rd _ _ _ _ HC0).
        + intros pn H Hb0. exact (Hb pn (hs_lay_call Q i P0 pn HP0' H) Hb0).
        + intros x Hx. apply Hkr; hs_rng.
        + intros pn x H Hx. exact (Hp pn x (hs_lay_call Q i P0 pn HP0' H) Hx).
      - destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        + rewrite nth_error_app2, Nat.sub_diag in Hc by lia. cbn [nth_error] in Hc. injection Hc as <-.
          rewrite nth_error_app2 in HP0 by lia. rewrite HL0, Nat.sub_diag in HP0. cbn [nth_error] in HP0.
          injection HP0 as <-.
          split.
          * refine (hs_acall_snoc _ _ rd rd' _ _ _ _ _ _ _ HCold HAs HNa HAr _ _ _ _ _ Hp0 Hin Hn Hs).
            -- intros x Hx. apply Hkr; hs_rng.
            -- intros x Hx. apply Hkr; hs_rng.
            -- intros pn H Hb0. exact (Hb pn (hs_lay_call Q _ P pn HP H) Hb0).
            -- intros pn x H Hx. exact (Hp pn x (hs_lay_call Q _ P pn HP H) Hx).
            -- intros Hm. apply Hpn. apply in_map_iff in Hm as (pn & Hq & Hm).
               apply in_map_iff. exists pn. split; [exact Hq | exact (hs_lay_call Q _ P pn HP Hm)].
          * cbn [snd]. apply Forall_app. split; [exact HFold | constructor; [exact Hsl | constructor]].
        + exfalso. assert (N : nth_error (r_calls R ++ [(REC_HOST_SETTING, As ++ [s])]) i = None)
            by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
          rewrite N in Hc. discriminate. }
    split; [|exact C6].
    apply (hs_acall_kept _ _ rd _ _ _ _ C5).
    * intros pn H Hb0. exact (Hb pn (hs_lay_spill Q pn H) Hb0).
    * intros x Hx. apply Hkr; hs_rng.
    * intros pn x H Hx. exact (Hp pn x (hs_lay_spill Q pn H) Hx).
  + cbn [set_calls r_answer l_answer].
    refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (hs_lay_ans Q pn H)) _
      (fun pn x H => Hp pn x (hs_lay_ans Q pn H))).
    intros x Hx. apply Hkr; hs_rng.
  + cbn [set_calls r_reply l_reply].
    refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
      (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
    intros x Hx. apply Hkr; hs_rng.
  + refine (hs_scalars_kept rd rd' A_G_REC R HS _). intros x Hx. apply Hkr; hs_rng.
- (* the spill arm: the call is record.spill *)
  assert (E : Nat.ltb (length (r_calls R)) 16 = false) by (apply Nat.ltb_ge; exact Hge).
  assert (Hsl0 : hs_slot R = A_REC_SPILL) by (unfold hs_slot; rewrite E; reflexivity).
  assert (Hrr : forall A, rec_record R REC_HOST_SETTING A = set_spill R (REC_HOST_SETTING, A))
    by (intros A; unfold rec_record; rewrite E; reflexivity).
  rewrite Hsl0 in HNa, HAr, Hkr. clear B1 B2 B4.
  rewrite Hrr in HC, HAn, HR, HS.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  cbn [set_spill r_calls r_spill r_answer r_reply] in C1, C2, C3, C4, C5, C6, HAn, HR.
  change (ag1_scalars rd A_G_REC R) in HS.
  pose proof (hs_perm_spill Q (p, n)) as HPm.
  destruct (hs_own_snoc Q _ O p n HPm HO HQ Hpn Hag Has) as [HO2 HQ2].
  unfold rec_repA. exists (RLay (l_calls Q) (l_spill Q ++ [(p, n)]) (l_answer Q) (l_reply Q)).
  split; [|exact HQ2].
  rewrite Hrr.
  unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  refine (conj _ (conj _ (conj _ (conj _ HO2)))).
  + unfold ag1_calls. cbn [set_spill r_calls r_spill l_calls l_spill].
    split; [exact C1|]. split; [exact C2|].
    split; [apply (hs_aval_kept rd); [exact C3 | intros x Hx; apply Hkr; hs_rng]|].
    split.
    * refine (hs_table_kept _ _ rd rd' R Q C4 Hb _ Hp). intros i x Hi Hx. apply Hkr; hs_rng.
    * split.
      -- refine (hs_acall_snoc _ _ rd rd' _ _ _ _ _ _ _ C5 HAs HNa HAr _ _ _ _ _ Hp0 Hin Hn Hs).
         ++ intros x Hx. apply Hkr; hs_rng.
         ++ intros x Hx. apply Hkr; hs_rng.
         ++ intros pn H Hb0. exact (Hb pn (hs_lay_spill Q pn H) Hb0).
         ++ intros pn x H Hx. exact (Hp pn x (hs_lay_spill Q pn H) Hx).
         ++ intros Hm. apply Hpn. apply in_map_iff in Hm as (pn & Hq & Hm).
            apply in_map_iff. exists pn. split; [exact Hq | exact (hs_lay_spill Q pn Hm)].
      -- cbn [snd]. apply Forall_app. split; [exact C6 | constructor; [exact Hsl | constructor]].
  + cbn [set_spill r_answer l_answer].
    refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (hs_lay_ans Q pn H)) _
      (fun pn x H => Hp pn x (hs_lay_ans Q pn H))).
    intros x Hx. apply Hkr; hs_rng.
  + cbn [set_spill r_reply l_reply].
    refine (hs_reply_kept _ _ rd rd' _ _ _ HR (fun pn H => Hb pn (hs_lay_rep Q pn H)) _
      (fun pn x H => Hp pn x (hs_lay_rep Q pn H))).
    intros x Hx. apply Hkr; hs_rng.
  + refine (hs_scalars_kept rd rd' A_G_REC R HS _). intros x Hx. apply Hkr; hs_rng.
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
  refine (hs_answer_kept _ _ rd rd' _ _ _ HAn (fun pn H => Hb pn (hs_lay_ans Q pn H)) _
    (fun pn x H => Hp pn x (hs_lay_ans Q pn H))).
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
exists P, acall_at (ablocks B ly S) rd (hs_slot R) (REC_HOST_SETTING, A) P /\ (forall pn, In pn P -> In pn O).
Proof.
intros ly S rd R A O [Q [HA HQ]].
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
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

(* the spill arm's rec_calls_free call: the spill's argument blocks, as rec_calls_free_c.v:80-87 asks them *)
Lemma hs_rec_spill_args : forall ly S rd R O,
rec_repA B ly S rd R O ->
exists Q, arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)) /\
  (length (l_spill Q) <= 6)%nat /\ length (l_spill Q) = length (snd (r_spill R)) /\
  aval_mem rd (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length (l_spill Q))) /\
  (forall a pn, nth_error (l_spill Q) a = Some pn ->
    aval_mem rd (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\ In pn (ablocks B ly S)) /\
  NoDup (map fst (l_spill Q)) /\
  (forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn O) /\
  (forall pn, In pn O -> In pn (l_spill Q) \/ In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
Proof.
intros ly S rd R O [Q [HA HQ]]. exists Q. split; [exact HA|]. split; [exact HQ|].
pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & C5 & _) & _).
destruct C5 as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
split; [lia|]. split; [exact H3|]. split; [rewrite H3; exact H5|].
split.
- intros a pn Hpn.
  assert (Ha : (a < length (snd (r_spill R)))%nat) by (rewrite <- H3; apply nth_error_Some; rewrite Hpn; discriminate).
  destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
  destruct (H7 a s pn Hs Hpn) as (G1 & _ & G3 & _). split; [exact G1 | exact G3].
- split; [exact H6|]. split.
  + intros pn Hin. apply HQ. unfold lay_blocks. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff;
      [left; exact Hin | right; apply in_app_iff; right; exact Hin].
  + intros pn Hin. apply HQ in Hin. unfold lay_blocks in Hin. apply in_app_iff in Hin as [Hin|Hin];
      [right; apply in_app_iff; left; exact Hin|].
    apply in_app_iff in Hin as [Hin|Hin]; [left; exact Hin | right; apply in_app_iff; right; exact Hin].
Qed.
End d.
