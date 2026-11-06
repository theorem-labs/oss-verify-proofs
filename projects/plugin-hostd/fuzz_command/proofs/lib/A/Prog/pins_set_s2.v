(* The recorder's representation (lib/A/Prog/CmdRep.v) through pins_set's call: record() puts the new call into
   g_rec.calls[ncalls] or record.spill, arg_s stores its arguments, mix_call's digest goes to g_rec.state.

   `arep_kept`: the representation survives any change of memory outside g_rec, record.spill and the recorder's
   own blocks, as long as those blocks stay live.
   `arep_put`: from a representation of R and memory that keeps every recorded byte except g_rec.ncalls and the new
   slot, a slot that holds the call (fn, A) gives the representation of rec_record R fn A (RecModel.v:38-39).
   `arep_set_state`: g_rec.state replaced (RecModel.v:29-30, rec_mix). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma ps_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma ps_aval_mem_in : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk. apply (ps_aval_mem_kept rd); [exact H|]. intros k Hk'. apply Hk. lia. Qed.

Lemma ps_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi). Qed.

Lemma ps_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall x, a <= x < a + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (ps_abytes_kept rd); [exact H1|].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hk. lia.
Qed.

Lemma ps_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *.
split; [apply (ps_aval_mem_in rd); [exact H4 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [apply (ps_aval_mem_in rd); [exact H5 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
assert (HIn : In pn P) by exact (nth_error_In _ _ Hpn).
split; [apply (ps_aval_mem_in rd); [exact G1 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [exact G2|]. split; [exact (Hbl pn HIn)|]. split; [exact G4|].
apply (ps_astr_kept rd); [exact G5 | intros x Hx; apply (Hp pn x HIn); lia].
Qed.

Definition in_lblk (l : list (Z * Z)) (x : Z) : Prop := exists pn, In pn l /\ fst pn <= x < fst pn + snd pn.

Lemma in_lblk_sub : forall l l' x, (forall pn, In pn l -> In pn l') -> in_lblk l x -> in_lblk l' x.
Proof. intros l l' x H (pn & Hin & Hx). exists pn. split; [exact (H pn Hin) | exact Hx]. Qed.

Lemma ps_lay_calls_in : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ Hi) | exact Hpn].
Qed.
Lemma ps_lay_spill_in : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma ps_lay_ans_in : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
rewrite H. left. reflexivity.
Qed.
Lemma ps_lay_rep_in : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
rewrite H. left. reflexivity.
Qed.

Lemma ps_answer_kept : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
(forall pn x, q = Some pn -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Hbl Ha Hp. unfold aanswer_at in *.
destruct t as [x|], q as [pn|]; try contradiction.
- destruct H as (V & Hnz & Hin & Hlen & Hstr & Hlx).
  split; [apply (ps_aval_mem_in rd); [exact V | intros y Hy; apply Ha; cbn in Hy; lia]|].
  split; [exact Hnz|]. split; [exact (Hbl pn eq_refl)|]. split; [exact Hlen|]. split; [|exact Hlx].
  apply (ps_astr_kept rd); [exact Hstr | intros y Hy; apply (Hp pn y eq_refl); lia].
- apply (ps_aval_mem_in rd); [exact H | intros y Hy; apply Ha; cbn in Hy; lia].
Qed.

Lemma ps_reply_kept : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
(forall pn x, q = Some pn -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Hbl Ha Hp. unfold areply_at in *. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
destruct y as [x|], q as [pn|]; try contradiction.
- destruct H as (V & Vs & Hnz & Hne & Hin & Hlen & Hb & Hlx).
  split; [apply (ps_aval_mem_in rd); [exact V | intros z Hz; apply Ha; cbn in Hz; lia]|].
  split; [apply (ps_aval_mem_in rd); [exact Vs | intros z Hz; apply Ha; cbn in Hz; lia]|].
  split; [exact Hnz|]. split; [exact Hne|]. split; [exact (Hbl pn eq_refl)|]. split; [exact Hlen|]. split; [|exact Hlx].
  apply (ps_abytes_kept rd); [exact Hb | intros z Hz; apply (Hp pn z eq_refl); lia].
- destruct H as [V Vs].
  split; (apply (ps_aval_mem_in rd); [first [exact V | exact Vs] | intros z Hz; apply Ha; cbn in Hz; lia]).
Qed.

Lemma ps_scalars_kept : forall (rd rd' : reader) gr R, ag1_scalars rd gr R ->
(forall x, (gr <= x < gr + 8 \/ gr + OFF_NREPLIES <= x < gr + OFF_NREPLIES + 4 \/ gr + OFF_STATE <= x < gr + OFF_STATE + 16) ->
  rd' x = rd x) ->
ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh) Ha.
unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
repeat split; try lia;
  (apply (ps_aval_mem_in rd); [eassumption | intros z Hz; apply Ha; cbn in Hz; lia]).
Qed.

(* the bytes the representation reads *)
Definition rep_bytes (gr sc : Z) (Q : rlay) (x : Z) : Prop :=
(gr <= x < gr + REC_SIZE) \/ (sc <= x < sc + SC_SIZE) \/ in_lblk (lay_blocks Q) x.

Lemma arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall x, rep_bytes A_G_REC A_REC_SPILL Q x -> rd' x = rd x) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN) Hk Hbl.
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply Hk; left; exact Hx).
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply Hk; right; left; exact Hx).
assert (KB : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x)
  by (intros pn x Hpn Hx; apply Hk; right; right; exists pn; split; [exact Hpn | exact Hx]).
unfold REC_SIZE, SC_SIZE in KG, KS.
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
  split; [exact Hlen|]. split; [exact HlenQ|].
  split; [apply (ps_aval_mem_in rd); [exact Hnc | intros x Hx; apply KG; unfold OFF_NCALLS in Hx; cbn in Hx; lia]|].
  split.
  { intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (ps_acall_kept bl bl' rd rd' _ c P Hca).
    - intros pn Hpn. apply Hbl. exact (ps_lay_calls_in Q i P pn HP Hpn).
    - intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE in *. lia.
    - intros pn x Hpn Hx. exact (KB pn x (ps_lay_calls_in Q i P pn HP Hpn) Hx). }
  split; [|exact Hspf].
  apply (ps_acall_kept bl bl' rd rd' _ _ _ Hspill).
  - intros pn Hpn. apply Hbl. exact (ps_lay_spill_in Q pn Hpn).
  - intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
  - intros pn x Hpn Hx. exact (KB pn x (ps_lay_spill_in Q pn Hpn) Hx). }
split.
{ apply (ps_answer_kept bl bl' rd rd' _ _ _ HA).
  - intros pn Hq. apply Hbl. exact (ps_lay_ans_in Q pn Hq).
  - intros x Hx. apply KG. unfold OFF_ANSWER in Hx. lia.
  - intros pn x Hq Hx. exact (KB pn x (ps_lay_ans_in Q pn Hq) Hx). }
split.
{ apply (ps_reply_kept bl bl' rd rd' _ _ _ HR).
  - intros pn Hq. apply Hbl. exact (ps_lay_rep_in Q pn Hq).
  - intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
  - intros pn x Hq Hx. exact (KB pn x (ps_lay_rep_in Q pn Hq) Hx). }
split; [|exact HOWN].
apply (ps_scalars_kept rd); [exact HSC|]. intros x Hx. apply KG. unfold OFF_NREPLIES, OFF_STATE in Hx. lia.
Qed.

(* the layout after record() puts the call's argument blocks P into the slot *)
Definition qput (n : nat) (Q : rlay) (P : list (Z * Z)) : rlay :=
if Nat.ltb n 16 then RLay (l_calls Q ++ [P]) (l_spill Q) (l_answer Q) (l_reply Q)
else RLay (l_calls Q) P (l_answer Q) (l_reply Q).

(* the slot record() writes, and the bytes outside it that the base representation reads *)
Definition ps_slot_of (n : Z) : Z := if n =? 16 then A_REC_SPILL else A_G_REC + OFF_CALLS + CALL_SIZE * n.
Definition put_prot (n : Z) (Q : rlay) (x : Z) : Prop :=
(A_G_REC <= x < A_G_REC + REC_SIZE /\ ~ (n < 16 /\ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4 \/
   ps_slot_of n <= x < ps_slot_of n + CALL_SIZE))) \/
(A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE /\ n < 16) \/ in_lblk (lay_blocks Q) x.

Ltac perm_tail :=
lazymatch goal with |- Permutation (?P ++ ?X) _ =>
apply (Permutation_trans (Permutation_app_comm P X)); rewrite <- !app_assoc; apply Permutation_refl end.

Lemma lay_blocks_qput_slot : forall n Q P, (n < 16)%nat ->
Permutation (lay_blocks (qput n Q P)) (lay_blocks Q ++ P).
Proof.
intros n Q P Hn. unfold qput. replace (Nat.ltb n 16) with true by (symmetry; apply Nat.ltb_lt; exact Hn).
unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
rewrite <- !app_assoc. apply Permutation_app_head. perm_tail.
Qed.

Lemma lay_blocks_qput_spill : forall n Q P, (16 <= n)%nat ->
lay_blocks (qput n Q P) = concat (l_calls Q) ++ P ++ oblk (l_answer Q) ++ oblk (l_reply Q).
Proof.
intros n Q P Hn. unfold qput. replace (Nat.ltb n 16) with false by (symmetry; apply Nat.ltb_ge; exact Hn).
reflexivity.
Qed.

Lemma arep_put : forall bl0 bl (rd0 rd : reader) R Q fn A P n,
arep_at bl0 rd0 A_G_REC A_REC_SPILL R Q ->
n = Z.of_nat (length (r_calls R)) ->
(forall x, put_prot n Q x -> rd x = rd0 x) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl) ->
(16 <= n -> l_spill Q = []) ->
(n < 16 -> aval_mem rd (A_G_REC + OFF_NCALLS) 4 (n + 1)) ->
acall_at bl rd (ps_slot_of n) (fn, A) P ->
Forall (fun s => Z.of_nat (length s) <= LMAX) A ->
(forall pn, In pn P -> iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE) ->
(forall pn, In pn P -> ~ In (fst pn) (map fst (lay_blocks Q))) ->
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) (qput (length (r_calls R)) Q P).
Proof.
intros bl0 bl rd0 rd R Q fn A P n (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN) En Hk Hbl' Hsp0 HNC Hslot HAF Hapart Hfresh.
destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
destruct HOWN as [HND HOA].
assert (KB : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd x = rd0 x)
  by (intros pn x Hpn Hx; apply Hk; right; right; exists pn; split; [exact Hpn | exact Hx]).
pose proof Hslot as (_ & _ & _ & _ & _ & HNDP & _).
assert (HNDQ : NoDup (map fst (lay_blocks Q))) by exact HND.
unfold rec_record.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hn16 | Hn16].
- (* the slot g_rec.calls[n] *)
  assert (Hn : n < 16) by lia.
  assert (Hsl : ps_slot_of n = A_G_REC + OFF_CALLS + CALL_SIZE * n)
    by (unfold ps_slot_of; replace (n =? 16) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4) ->
    ~ (A_G_REC + OFF_CALLS + CALL_SIZE * n <= x < A_G_REC + OFF_CALLS + CALL_SIZE * n + CALL_SIZE) -> rd x = rd0 x).
  { intros x H1 H2 H3. apply Hk. left. split; [exact H1|]. rewrite Hsl. intros [_ [H4|H4]]; [exact (H2 H4) | exact (H3 H4)]. }
  assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd x = rd0 x)
    by (intros x Hx; apply Hk; right; left; split; [exact Hx | exact Hn]).
  unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in KG, KS.
  pose proof (lay_blocks_qput_slot _ Q P Hn16) as HPq.
  unfold qput in HPq |- *. replace (Nat.ltb (length (r_calls R)) 16) with true in HPq |- * by (symmetry; apply Nat.ltb_lt; exact Hn16).
  split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
  split.
  { unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
    rewrite !length_app. cbn [length].
    split; [lia|]. split; [lia|].
    split; [rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; rewrite <- En; exact (HNC Hn)|].
    split.
    { intros i c P' Hc HP'.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi | Hi].
      - rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP' by lia.
        destruct (Hcalls i c P' Hc HP') as [Hca Hf]. split; [|exact Hf].
        apply (ps_acall_kept bl0 bl rd0 rd _ c P' Hca).
        + intros pn Hpn. apply Hbl'. exact (ps_lay_calls_in Q i P' pn HP' Hpn).
        + intros x Hx. apply KG; unfold OFF_CALLS, CALL_SIZE, OFF_NCALLS, REC_SIZE in *; lia.
        + intros pn x Hpn Hx. exact (KB pn x (ps_lay_calls_in Q i P' pn HP' Hpn) Hx).
      - rewrite nth_error_app2 in Hc by exact Hi. rewrite nth_error_app2 in HP' by lia.
        rewrite HlenQ in HP'.
        remember (i - length (r_calls R))%nat as m eqn:Em in Hc, HP'.
        destruct m as [|m]; [| destruct m; discriminate Hc].
        assert (Ei : Z.of_nat i = n) by (rewrite En; lia).
        cbn [nth_error] in Hc, HP'. injection Hc as <-. injection HP' as <-.
        rewrite Ei, <- Hsl. split; [exact Hslot | exact HAF]. }
    split; [|exact Hspf].
    apply (ps_acall_kept bl0 bl rd0 rd _ _ _ Hspill).
    - intros pn Hpn. apply Hbl'. exact (ps_lay_spill_in Q pn Hpn).
    - intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
    - intros pn x Hpn Hx. exact (KB pn x (ps_lay_spill_in Q pn Hpn) Hx). }
  split.
  { cbn [r_answer set_calls l_answer].
    apply (ps_answer_kept bl0 bl rd0 rd _ _ _ HA).
    - intros pn Hq. apply Hbl'. exact (ps_lay_ans_in Q pn Hq).
    - intros x Hx. apply KG; unfold OFF_ANSWER, OFF_CALLS, CALL_SIZE, OFF_NCALLS in *; lia.
    - intros pn x Hq Hx. exact (KB pn x (ps_lay_ans_in Q pn Hq) Hx). }
  split.
  { cbn [r_reply set_calls l_reply].
    apply (ps_reply_kept bl0 bl rd0 rd _ _ _ HR).
    - intros pn Hq. apply Hbl'. exact (ps_lay_rep_in Q pn Hq).
    - intros x Hx. apply KG; unfold OFF_REPLY, OFF_REPLY_SIZE, OFF_CALLS, CALL_SIZE, OFF_NCALLS in *; lia.
    - intros pn x Hq Hx. exact (KB pn x (ps_lay_rep_in Q pn Hq) Hx). }
  split.
  { change (ag1_scalars rd A_G_REC (set_calls R (r_calls R ++ [(fn, A)]))) with (ag1_scalars rd A_G_REC R).
    apply (ps_scalars_kept rd0); [exact HSC|]. intros x Hx. apply KG; unfold OFF_NREPLIES, OFF_STATE, OFF_CALLS, CALL_SIZE, OFF_NCALLS in *; lia. }
  { unfold ag1_own. split.
    - apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_sym (Permutation_map fst HPq))).
      rewrite map_app. apply List.NoDup_app; [exact (proj1 (NoDup_ListNoDup _) HNDQ) | exact (proj1 (NoDup_ListNoDup _) HNDP) |].
      intros a Ha Hb. apply in_map_iff in Hb as (pn & <- & Hpn). exact (Hfresh pn Hpn Ha).
    - intros pn Hpn. apply (Permutation_in _ HPq) in Hpn.
      apply in_app_or in Hpn as [Hpn | Hpn]; [exact (HOA pn Hpn) | exact (Hapart pn Hpn)]. }
- (* record.spill *)
  assert (Hn : n = 16) by lia.
  assert (Hsl : ps_slot_of n = A_REC_SPILL) by (rewrite Hn; reflexivity).
  assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd x = rd0 x)
    by (intros x Hx; apply Hk; left; split; [exact Hx | lia]).
  pose proof (Hsp0 ltac:(lia)) as Hsp.
  unfold REC_SIZE in KG.
  assert (HPq : Permutation (lay_blocks (qput (length (r_calls R)) Q P)) (lay_blocks Q ++ P)).
  { rewrite (lay_blocks_qput_spill _ Q P Hn16). unfold lay_blocks. rewrite Hsp. cbn [app].
    rewrite <- !app_assoc. apply Permutation_app_head. perm_tail. }
  unfold qput in HPq |- *. replace (Nat.ltb (length (r_calls R)) 16) with false in HPq |- * by (symmetry; apply Nat.ltb_ge; exact Hn16).
  split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
  split.
  { unfold ag1_calls. cbn [r_calls r_spill set_spill l_calls l_spill].
    split; [exact Hlen|]. split; [exact HlenQ|].
    split; [apply (ps_aval_mem_in rd0); [exact Hnc | intros x Hx; apply KG; unfold OFF_NCALLS in Hx; cbn in Hx; lia]|].
    split.
    { intros i c P' Hc HP'. destruct (Hcalls i c P' Hc HP') as [Hca Hf]. split; [|exact Hf].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
      apply (ps_acall_kept bl0 bl rd0 rd _ c P' Hca).
      + intros pn Hpn. apply Hbl'. exact (ps_lay_calls_in Q i P' pn HP' Hpn).
      + intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE in *. lia.
      + intros pn x Hpn Hx. exact (KB pn x (ps_lay_calls_in Q i P' pn HP' Hpn) Hx). }
    split; [rewrite <- Hsl; exact Hslot | exact HAF]. }
  split.
  { cbn [r_answer set_spill l_answer].
    apply (ps_answer_kept bl0 bl rd0 rd _ _ _ HA).
    - intros pn Hq. apply Hbl'. exact (ps_lay_ans_in Q pn Hq).
    - intros x Hx. apply KG. unfold OFF_ANSWER in Hx. lia.
    - intros pn x Hq Hx. exact (KB pn x (ps_lay_ans_in Q pn Hq) Hx). }
  split.
  { cbn [r_reply set_spill l_reply].
    apply (ps_reply_kept bl0 bl rd0 rd _ _ _ HR).
    - intros pn Hq. apply Hbl'. exact (ps_lay_rep_in Q pn Hq).
    - intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
    - intros pn x Hq Hx. exact (KB pn x (ps_lay_rep_in Q pn Hq) Hx). }
  split.
  { change (ag1_scalars rd A_G_REC (set_spill R (fn, A))) with (ag1_scalars rd A_G_REC R).
    apply (ps_scalars_kept rd0); [exact HSC|]. intros x Hx. apply KG. unfold OFF_NREPLIES, OFF_STATE in Hx. lia. }
  { unfold ag1_own. split.
    - apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_sym (Permutation_map fst HPq))).
      rewrite map_app. apply List.NoDup_app; [exact (proj1 (NoDup_ListNoDup _) HNDQ) | exact (proj1 (NoDup_ListNoDup _) HNDP) |].
      intros a Ha Hb. apply in_map_iff in Hb as (pn & <- & Hpn). exact (Hfresh pn Hpn Ha).
    - intros pn Hpn. apply (Permutation_in _ HPq) in Hpn.
      apply in_app_or in Hpn as [Hpn | Hpn]; [exact (HOA pn Hpn) | exact (Hapart pn Hpn)]. }
Qed.

(* mix_call's digest stored to g_rec.state (RecModel.v:41, rec_mix) *)
Lemma arep_set_state : forall bl (rd rd' : reader) R Q h,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall x, rep_bytes A_G_REC A_REC_SPILL Q x -> ~ (A_G_REC + OFF_STATE <= x < A_G_REC + OFF_STATE + 8) -> rd' x = rd x) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_state R h) Q.
Proof.
intros bl rd rd' R Q h HA0 Hk Hst Hh.
pose proof HA0 as (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN).
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_STATE <= x < A_G_REC + OFF_STATE + 8) -> rd' x = rd x)
  by (intros x Hx Hn; apply Hk; [left; exact Hx | exact Hn]).
assert (KB : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros pn x Hpn Hx. apply Hk; [right; right; exists pn; split; [exact Hpn | exact Hx]|].
  pose proof (proj2 HOWN pn Hpn) as [D _]. unfold iv_apart, REC_SIZE, OFF_STATE in *. lia. }
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
{ intros x Hx. apply Hk; [right; left; exact Hx | unfold A_REC_SPILL, A_G_REC, SC_SIZE, OFF_STATE in *; lia]. }
unfold REC_SIZE, OFF_STATE in KG.
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
split.
{ change (ag1_calls bl rd' A_G_REC A_REC_SPILL (set_state R h) Q) with (ag1_calls bl rd' A_G_REC A_REC_SPILL R Q).
  split; [exact Hlen|]. split; [exact HlenQ|].
  split; [apply (ps_aval_mem_in rd); [exact Hnc | intros x Hx; apply KG; unfold OFF_NCALLS in *; cbn in Hx; lia]|].
  split.
  { intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (ps_acall_kept bl bl rd rd' _ c P Hca).
    - exact (acall_at_in bl rd _ c P Hca).
    - intros x Hx. apply KG; unfold OFF_CALLS, CALL_SIZE in *; lia.
    - intros pn x Hpn Hx. exact (KB pn x (ps_lay_calls_in Q i P pn HP Hpn) Hx). }
  split; [|exact Hspf].
  apply (ps_acall_kept bl bl rd rd' _ _ _ Hspill); [exact (acall_at_in bl rd _ _ _ Hspill) | |].
  - intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
  - intros pn x Hpn Hx. exact (KB pn x (ps_lay_spill_in Q pn Hpn) Hx). }
split.
{ cbn [r_answer set_state].
  apply (ps_answer_kept bl bl rd rd' _ _ _ HA).
  - intros pn Hq. destruct (r_answer R), (l_answer Q); cbn in HA; try contradiction; try discriminate.
    injection Hq as <-. exact (proj1 (proj2 (proj2 HA))).
  - intros x Hx. apply KG; unfold OFF_ANSWER in Hx; lia.
  - intros pn x Hq Hx. exact (KB pn x (ps_lay_ans_in Q pn Hq) Hx). }
split.
{ cbn [r_reply set_state].
  apply (ps_reply_kept bl bl rd rd' _ _ _ HR).
  - intros pn Hq. destruct (r_reply R), (l_reply Q); cbn in HR; try contradiction; try discriminate.
    injection Hq as <-. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
  - intros x Hx. apply KG; unfold OFF_REPLY, OFF_REPLY_SIZE in Hx; lia.
  - intros pn x Hq Hx. exact (KB pn x (ps_lay_rep_in Q pn Hq) Hx). }
split; [|exact HOWN].
destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh).
unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_state].
unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_HOST in *.
split; [apply (ps_aval_mem_in rd); [exact Vr | intros x Hx; apply KG; cbn in Hx; lia]|].
split; [apply (ps_aval_mem_in rd); [exact Vc | intros x Hx; apply KG; cbn in Hx; lia]|].
split; [apply (ps_aval_mem_in rd); [exact Vn | intros x Hx; apply KG; cbn in Hx; lia]|].
split; [exact Hst|].
split; [apply (ps_aval_mem_in rd); [exact Vh | intros x Hx; apply KG; cbn in Hx; lia]|].
repeat split; lia.
Qed.
