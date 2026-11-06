(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder's model steps for the walk of sup_after_reply on plugin-hostd/fuzz_command.asan: record() into a new slot or into record.spill, and the append of one argument, over CmdRep.v's reader form; ported from fuzz_command's plain lib/Prog/RecStep.v (rec_rep_record_lt, rep_at_record_full, call_at_arg, rep_at_arg_lt, rep_at_arg_full, rec_rep_arg); the frame lemmas aval_mem_kept .. rec_repA_kept copied from the answer_code walk (lib/A/Prog/answer_code.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot record() picks for the next call (plain lib/Prog/RecStep.v:10-11 rec_entry at g_rec / record.spill) *)
Definition sar_entry (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
else A_REC_SPILL.

(* a byte of g_rec or record.spill *)
Definition in_rec (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

(* every recorder block is live in bl' and holds the same bytes in rd' as in rd *)
Definition blocks_keptA (bl' : list (Z * Z)) (rd rd' : reader) (L : list (Z * Z)) : Prop :=
forall pn, In pn L -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)
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
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

(* ---------- helpers of the model steps (plain lib/Prog/RecStep.v:10-26, 287-386 and 442-485, over the reader) ---------- *)
Local Ltac sar_num :=
  unfold in_rec, iv_apart, REC_SIZE, SC_SIZE, OFF_REFUSE, OFF_CODE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER,
    OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS,
    CALL_OFF_ARGS, A_G_REC, A_REC_SPILL in *; lia.

Lemma sar_record_lt_eq : forall R fn As, (length (r_calls R) < 16)%nat ->
rec_record R fn As = set_calls R (r_calls R ++ [(fn, As)]).
Proof. intros R fn As H. unfold rec_record. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma sar_record_full_eq : forall R fn As, length (r_calls R) = 16%nat -> rec_record R fn As = set_spill R (fn, As).
Proof. intros R fn As H. unfold rec_record. rewrite H. reflexivity. Qed.

Lemma sar_entry_lt : forall R, (length (r_calls R) < 16)%nat ->
sar_entry R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)).
Proof. intros R H. unfold sar_entry. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma sar_entry_full : forall R, length (r_calls R) = 16%nat -> sar_entry R = A_REC_SPILL.
Proof. intros R H. unfold sar_entry. rewrite H. reflexivity. Qed.

Lemma sar_listnodup_snoc : forall (l : list Z) a, List.NoDup l -> ~ In a l -> List.NoDup (l ++ [a]).
Proof.
intros l a H N. eapply Permutation_NoDup; [apply Permutation_cons_append | constructor; [exact N | exact H]].
Qed.

Lemma sar_nodup_fst_snoc : forall (l : list (Z * Z)) p k, NoDup (map fst l) -> ~ In p (map fst l) ->
NoDup (map fst (l ++ [(p, k)])).
Proof.
intros l p k H N. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H. rewrite map_app. cbn [map fst].
exact (sar_listnodup_snoc _ p H N).
Qed.

Lemma sar_nodup_fst_perm : forall l l' : list (Z * Z), Permutation l l' -> NoDup (map fst l) -> NoDup (map fst l').
Proof.
intros l l' HP H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
exact (Permutation_NoDup (Permutation_map fst HP) H).
Qed.

Lemma sar_perm_snoc_mid : forall (X Y W : list (Z * Z)) a, Permutation (X ++ (Y ++ [a]) ++ W) ((X ++ Y ++ W) ++ [a]).
Proof.
intros X Y W a. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
cbn [app]. apply Permutation_cons_append.
Qed.

Lemma sar_lay_perm_lt : forall l0 P S ans rep pk,
Permutation (lay_blocks (RLay (l0 ++ [P ++ [pk]]) S ans rep)) (lay_blocks (RLay (l0 ++ [P]) S ans rep) ++ [pk]).
Proof.
intros l0 P S ans rep pk.
assert (E1 : lay_blocks (RLay (l0 ++ [P ++ [pk]]) S ans rep) = concat l0 ++ (P ++ [pk]) ++ S ++ oblk ans ++ oblk rep).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
assert (E2 : lay_blocks (RLay (l0 ++ [P]) S ans rep) = concat l0 ++ P ++ S ++ oblk ans ++ oblk rep).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. apply sar_perm_snoc_mid.
Qed.

Lemma sar_lay_perm_full : forall lc S ans rep pk,
Permutation (lay_blocks (RLay lc (S ++ [pk]) ans rep)) (lay_blocks (RLay lc S ans rep) ++ [pk]).
Proof. intros lc S ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply sar_perm_snoc_mid. Qed.

Lemma sar_perm_iff : forall (l l' : list (Z * Z)) pk, Permutation l' (l ++ [pk]) ->
forall pn, In pn l' <-> In pn l \/ pn = pk.
Proof.
intros l l' pk HP pn. split; intros H.
- apply (Permutation_in _ HP) in H. apply in_app_or in H as [H|[E|[]]]; [left; exact H | right; symmetry; exact E].
- apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app.
  destruct H as [H|E]; [left; exact H | right; left; symmetry; exact E].
Qed.

(* the answer, the reply and the scalars of g_rec survive a write outside g_rec's first 8 and last 48 bytes and
   outside their blocks (plain rep_rest_keep, RecStep.v:191-263) *)
Lemma sar_rest_kept : forall bl bl' (rd rd' : reader) gr R R' ans rep,
aanswer_at bl rd gr (r_answer R) ans -> areply_at bl rd gr (r_reply R) rep -> ag1_scalars rd gr R ->
r_answer R' = r_answer R -> r_reply R' = r_reply R -> r_refuse R' = r_refuse R -> r_code R' = r_code R ->
r_nreplies R' = r_nreplies R -> r_state R' = r_state R -> r_host R' = r_host R ->
(forall a, gr <= a < gr + 8 \/ gr + 912 <= a < gr + 960 -> rd' a = rd a) ->
(forall pn, In pn (oblk ans ++ oblk rep) -> In pn bl' /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' gr (r_answer R') ans /\ areply_at bl' rd' gr (r_reply R') rep /\ ag1_scalars rd' gr R'.
Proof.
intros bl bl' rd rd' gr R R' ans rep HA HP HX E1 E2 E3 E4 E5 E6 E7 KR KO.
unfold ag1_scalars in *. rewrite E1, E2, E3, E4, E5, E6, E7.
unfold aanswer_at, areply_at in *.
unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
split; [|split].
- revert HA KO. destruct (r_answer R) as [x|], ans as [q|]; intros HA KO; try contradiction.
  + destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    destruct (KO q ltac:(cbn; left; reflexivity)) as [Kin Kp].
    split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply KR; lia]|].
    split; [exact A2|]. split; [exact Kin|]. split; [exact A4|].
    split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply Kp; lia] | exact A6].
  + apply (aval_mem_kept rd); [exact HA | intros k Hk; apply KR; lia].
- revert HP KO. destruct (r_reply R) as [y|], rep as [q|]; intros HP KO; try contradiction.
  + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KO q ltac:(apply in_or_app; right; cbn; left; reflexivity)) as [Kin Kp].
    split; [apply (aval_mem_kept rd); [exact P1 | intros k Hk; apply KR; lia]|].
    split; [apply (aval_mem_kept rd); [exact P2 | intros k Hk; apply KR; lia]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|].
    split; [apply (rabytes_kept rd); [exact P7 | intros i Hi; apply Kp; lia] | exact P8].
  + destruct HP as [P1 P2].
    split; [apply (aval_mem_kept rd); [exact P1 | intros k Hk; apply KR; lia]|].
    apply (aval_mem_kept rd); [exact P2 | intros k Hk; apply KR; lia].
- destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  split; [apply (aval_mem_kept rd); [exact X1 | intros k Hk; apply KR; lia]|].
  split; [apply (aval_mem_kept rd); [exact X2 | intros k Hk; apply KR; lia]|].
  split; [apply (aval_mem_kept rd); [exact X3 | intros k Hk; apply KR; lia]|].
  split; [apply (aval_mem_kept rd); [exact X4 | intros k Hk; apply KR; lia]|].
  split; [apply (aval_mem_kept rd); [exact X5 | intros k Hk; apply KR; lia]|].
  exact X6.
Qed.

(* one more argument in a call slot at e (plain call_at_arg, RecStep.v:442-485) *)
Lemma sar_call_arg : forall bl bl' (rd rd' : reader) e fn As P x p k,
acall_at bl rd e (fn, As) P -> (length As < 6)%nat ->
aval_mem rd' (e + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
aval_mem rd' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
(forall a, e <= a < e + CALL_SIZE -> ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
   ~ (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
   rd' a = rd a) ->
(forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
~ In p (map fst P) -> p <> 0 -> In (p, k) bl' -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
astr_atR rd' p x ->
acall_at bl' rd' e (fn, As ++ [x]) (P ++ [(p, k)]).
Proof.
intros bl bl' rd rd' e fn As P x p k (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) H6 BN BS K KP Hfr Hp0 Hin Hsz Hx.
cbn [fst snd] in Hfn, Hn, Hl, Hb0, Hb1, Hk.
unfold acall_at. cbn [fst snd].
unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
split; [exact Hfn|]. split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, Hl; reflexivity|].
split; [apply (aval_mem_kept rd); [exact Hb0 | intros j Hj; apply K; lia]|].
split; [rewrite length_app, Nat2Z.inj_add; exact BN|].
split; [exact (sar_nodup_fst_snoc P p k Hnd Hfr)|].
intros j s pn Es Ep.
destruct (Nat.lt_ge_cases j (length As)) as [Hj|Hj].
- rewrite nth_error_app1 in Es by exact Hj. rewrite nth_error_app1 in Ep by lia.
  destruct (Hk j s pn Es Ep) as (Hs & Hq0 & Hq & Hqs & Hstr).
  destruct (KP pn (nth_error_In _ _ Ep)) as [Kin Kp].
  split; [apply (aval_mem_kept rd); [exact Hs | intros i Hi; apply K; lia]|].
  split; [exact Hq0|]. split; [exact Kin|]. split; [exact Hqs|].
  apply (rastr_kept rd); [exact Hstr | intros i Hi; apply Kp; lia].
- destruct (Nat.eq_dec j (length As)) as [->|Hne].
  + rewrite nth_error_app2, Nat.sub_diag in Es by lia. cbn in Es. injection Es as <-.
    rewrite nth_error_app2, Hl, Nat.sub_diag in Ep by lia. cbn in Ep. injection Ep as <-.
    cbn [fst snd]. split; [exact BS|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hsz | exact Hx].
  + exfalso. assert (N : nth_error (As ++ [x]) j = None)
      by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    rewrite N in Es. discriminate.
Qed.

(* ---------- the model steps (plain lib/Prog/RecStep.v, over the reader) ---------- *)
(* record() into a new slot of g_rec's table: ncalls + 1, fn and nargs = 0 written, every other recorder byte and
   block kept (plain rec_rep_record_lt, RecStep.v:63-178) *)
Lemma sar_rep_record_lt : forall bl bl' (rd rd' : reader) R Q fn,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd' (sar_entry R + CALL_OFF_FN) 4 fn ->
aval_mem rd' (sar_entry R + CALL_OFF_NARGS) 4 0 ->
(forall a, in_rec a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
   ~ (sar_entry R <= a < sar_entry R + 8) -> rd' a = rd a) ->
blocks_keptA bl' rd rd' (lay_blocks Q) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn [])
  (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' R Q fn HR Hn Hfn BN BF BA KG KB.
unfold blocks_keptA in KB.
rewrite (sar_entry_lt R Hn) in BF, BA, KG.
rewrite (sar_record_lt_eq R fn [] Hn).
assert (LB : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite !app_nil_r. reflexivity. }
destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW).
assert (KR : forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd' a = rd a)
  by (intros a Ha; apply KG; sar_num).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\
          forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (sar_rest_kept bl bl' rd rd' A_G_REC R (set_calls R (r_calls R ++ [(fn, [])])) (l_answer Q) (l_reply Q)
  HA HP HX eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl KR KO) as (RA & RP & RX).
unfold arep_at.
refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX _))))))).
2: { unfold ag1_own. rewrite LB. exact HW. }
unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
- rewrite length_app. cbn [length]. lia.
- rewrite !length_app, C2. reflexivity.
- replace (Z.of_nat (length (r_calls R ++ [(fn, [])]))) with (Z.of_nat (length (r_calls R)) + 1)
    by (rewrite length_app; cbn [length]; lia).
  exact BN.
- intros i c P Ec EP.
  destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
  + rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by lia.
    destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    pose proof Hc as (_ & H6 & _).
    assert (HPQ : forall pn, In pn P -> In pn (lay_blocks Q)).
    { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
      split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
    apply (acall_at_kept bl bl' rd rd' _ c P Hc).
    * intros pn Hpn. exact (proj1 (KB pn (HPQ pn Hpn))).
    * intros j Hj. apply KG; sar_num.
    * intros pn j Hpn Hj. exact (proj2 (KB pn (HPQ pn Hpn)) j Hj).
  + destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
    * rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
      rewrite nth_error_app2, C2, Nat.sub_diag in EP by lia. cbn in EP. injection EP as <-.
      split; [|constructor].
      unfold acall_at. cbn [fst snd length].
      split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
      split; [exact BF|]. split; [exact BA|]. split; [constructor|].
      intros k s pn Es. destruct k; discriminate.
    * exfalso. assert (N : nth_error (r_calls R ++ [(fn, [])]) i = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
      rewrite N in Ec. discriminate.
- pose proof C5 as (_ & H6 & _).
  assert (HPQ : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  apply (acall_at_kept bl bl' rd rd' _ _ _ C5).
  + intros pn Hpn. exact (proj1 (KB pn (HPQ pn Hpn))).
  + intros j Hj. apply KG; sar_num.
  + intros pn j Hpn Hj. exact (proj2 (KB pn (HPQ pn Hpn)) j Hj).
Qed.

(* record() into record.spill once the table holds 16 calls and the spill's arguments are freed: fn and nargs = 0
   written, every other recorder byte and block kept (plain rep_at_record_full, RecStep.v:395-440) *)
Lemma sar_rep_record_full : forall bl bl' (rd rd' : reader) R Q fn,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
length (r_calls R) = 16%nat -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
(forall a, in_rec a -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
blocks_keptA bl' rd rd' (lay_blocks Q) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn []) Q.
Proof.
intros bl bl' rd rd' R Q fn HR Hn Hsp Hfn BF BA KG KB.
unfold blocks_keptA in KB.
rewrite (sar_record_full_eq R fn [] Hn).
destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW).
assert (KR : forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) by (intros a Ha; apply KG; sar_num).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\
          forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (sar_rest_kept bl bl' rd rd' A_G_REC R (set_spill R (fn, [])) (l_answer Q) (l_reply Q) HA HP HX
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(intros a Ha; apply KR; lia) KO) as (RA & RP & RX).
assert (ES : l_spill Q = []).
{ pose proof C5 as (_ & _ & HL & _). rewrite Hsp in HL. apply length_zero_iff_nil. exact HL. }
unfold arep_at.
refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX HW))))))).
unfold ag1_calls. cbn [set_spill r_calls r_spill fst snd].
refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
- apply (aval_mem_kept rd); [exact C3 | intros j Hj; apply KR; sar_num].
- intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  pose proof Hc as (_ & H6 & _).
  assert (HPQ : forall pn, In pn P -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
    split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
  apply (acall_at_kept bl bl' rd rd' _ c P Hc).
  + intros pn Hpn. exact (proj1 (KB pn (HPQ pn Hpn))).
  + intros j Hj. apply KR. sar_num.
  + intros pn j Hpn Hj. exact (proj2 (KB pn (HPQ pn Hpn)) j Hj).
- rewrite ES. unfold acall_at. cbn [fst snd length].
  split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
  split; [exact BF|]. split; [exact BA|]. split; [constructor|].
  intros k s pn Es. destruct k; discriminate.
- constructor.
Qed.

(* one more argument x of the call record() made: nargs + 1, args[nargs] := p, p a fresh live block of k bytes
   holding x and its terminator (plain rec_rep_arg, RecStep.v:650-699) *)
Lemma sar_rep_arg : forall bl bl' (rd rd' : reader) R fn As Q x p k,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn As) Q ->
(length (r_calls R) <= 16)%nat -> (length As < 6)%nat ->
aval_mem rd' (sar_entry R + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
aval_mem rd' (sar_entry R + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
(forall a, in_rec a ->
   ~ (sar_entry R + CALL_OFF_NARGS <= a < sar_entry R + CALL_OFF_NARGS + 4) ->
   ~ (sar_entry R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
      sar_entry R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
   rd' a = rd a) ->
blocks_keptA bl' rd rd' (lay_blocks Q) ->
~ In p (map fst (lay_blocks Q)) -> p <> 0 -> In (p, k) bl' ->
astr_atR rd' p x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn (As ++ [x])) Q' /\
  (forall pn, In pn (lay_blocks Q') <-> In pn (lay_blocks Q) \/ pn = (p, k)).
Proof.
intros bl bl' rd rd' R fn As Q x p k HR Hn16 H6 BN BS KG KB Hfr Hp0 Hin Hx Hlx Hsz Ha1 Ha2.
unfold blocks_keptA in KB.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
- (* a new slot of g_rec's table (plain rep_at_arg_lt, RecStep.v:487-580) *)
  rewrite (sar_entry_lt R Hn) in BN, BS, KG.
  rewrite (sar_record_lt_eq R fn As Hn) in HR. rewrite (sar_record_lt_eq R fn (As ++ [x]) Hn).
  destruct Q as [lc ls la lr].
  destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & (HND & HAP)).
  cbn [set_calls r_calls r_spill l_calls l_spill] in C1, C2, C3, C4, C5, C6.
  assert (NE : lc <> []) by (intros E; rewrite E, length_app in C2; cbn [length] in C2; lia).
  destruct (exists_last NE) as (l0 & P & E). subst lc.
  assert (L0 : length l0 = length (r_calls R)) by (rewrite !length_app in C2; cbn [length] in C2; lia).
  assert (MB : forall pn, In pn P -> In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. left.
    rewrite concat_app. apply in_or_app. right. cbn [concat]. rewrite app_nil_r. exact Hpn. }
  assert (KP : forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KB; apply MB; exact Hpn).
  assert (HfrP : ~ In p (map fst P)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & Eq & Hq). apply in_map_iff. exists pn.
    split; [exact Eq | apply MB; exact Hq]. }
  assert (Ee : nth_error (r_calls R ++ [(fn, As)]) (length (r_calls R)) = Some (fn, As))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (Ep : nth_error (l0 ++ [P]) (length (r_calls R)) = Some P)
    by (rewrite nth_error_app2, L0, Nat.sub_diag by lia; reflexivity).
  destruct (C4 _ _ _ Ee Ep) as [CE CL].
  assert (KR : forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd' a = rd a)
    by (intros a Ha; apply KG; sar_num).
  assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (sar_rest_kept bl bl' rd rd' A_G_REC (set_calls R (r_calls R ++ [(fn, As)]))
    (set_calls R (r_calls R ++ [(fn, As ++ [x])])) la lr HA HP HX
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl KR KO) as (RA & RP & RX).
  exists (RLay (l0 ++ [P ++ [(p, k)]]) ls la lr).
  pose proof (sar_lay_perm_lt l0 P ls la lr (p, k)) as PERM.
  split; [|exact (sar_perm_iff _ _ (p, k) PERM)].
  unfold arep_at.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX _))))))).
  + unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    * rewrite length_app. cbn [length]. lia.
    * rewrite !length_app. cbn [length]. lia.
    * replace (Z.of_nat (length (r_calls R ++ [(fn, As ++ [x])])))
        with (Z.of_nat (length (r_calls R ++ [(fn, As)]))) by (rewrite !length_app; cbn [length]; reflexivity).
      apply (aval_mem_kept rd); [exact C3 | intros j Hj; apply KG; sar_num].
    * intros i c P' Ec EP'.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      -- assert (Ec0 : nth_error (r_calls R ++ [(fn, As)]) i = Some c)
           by (rewrite nth_error_app1 in Ec |- * by exact Hi; exact Ec).
         assert (EP0 : nth_error (l0 ++ [P]) i = Some P')
           by (rewrite nth_error_app1 in EP' |- * by lia; exact EP').
         destruct (C4 i c P' Ec0 EP0) as [Hc HL]. split; [|exact HL].
         pose proof Hc as (_ & H6c & _).
         assert (HPQ : forall pn, In pn P' -> In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr))).
         { intros pn Hpn. unfold lay_blocks. cbn [l_calls]. apply in_or_app. left. apply in_concat.
           exists P'. split; [exact (nth_error_In _ _ EP0) | exact Hpn]. }
         apply (acall_at_kept bl bl' rd rd' _ c P' Hc).
         ++ intros pn Hpn. exact (proj1 (KB pn (HPQ pn Hpn))).
         ++ intros j Hj. apply KG; sar_num.
         ++ intros pn j Hpn Hj. exact (proj2 (KB pn (HPQ pn Hpn)) j Hj).
      -- destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
         ++ rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
            rewrite nth_error_app2, L0, Nat.sub_diag in EP' by lia. cbn in EP'. injection EP' as <-.
            split; [|cbn [snd]; apply Forall_app; split; [exact CL | constructor; [exact Hlx | constructor]]].
            apply (sar_call_arg bl bl' rd rd' _ fn As P x p k CE H6 BN BS);
              [| exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
            intros a Ha H1 H2. apply KG; [sar_num | exact H1 | exact H2].
         ++ exfalso. assert (N : nth_error (r_calls R ++ [(fn, As ++ [x])]) i = None)
              by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
            rewrite N in Ec. discriminate.
    * pose proof C5 as (_ & H6s & _).
      assert (HPQ : forall pn, In pn ls -> In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr))).
      { intros pn Hpn. unfold lay_blocks. cbn [l_spill]. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
      apply (acall_at_kept bl bl' rd rd' _ _ _ C5).
      ++ intros pn Hpn. exact (proj1 (KB pn (HPQ pn Hpn))).
      ++ intros j Hj. apply KG; sar_num.
      ++ intros pn j Hpn Hj. exact (proj2 (KB pn (HPQ pn Hpn)) j Hj).
  + unfold ag1_own. split.
    * apply (sar_nodup_fst_perm _ _ (Permutation_sym PERM)). apply sar_nodup_fst_snoc; [exact HND | exact Hfr].
    * intros pn Hpn. apply (Permutation_in _ PERM) in Hpn.
      apply in_app_or in Hpn as [Hpn|[<-|[]]]; [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
- (* record.spill (plain rep_at_arg_full, RecStep.v:582-648) *)
  assert (Hn' : length (r_calls R) = 16%nat) by lia.
  rewrite (sar_entry_full R Hn') in BN, BS, KG.
  rewrite (sar_record_full_eq R fn As Hn') in HR. rewrite (sar_record_full_eq R fn (As ++ [x]) Hn').
  destruct Q as [lc ls la lr].
  destruct HR as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & (HND & HAP)).
  cbn [set_spill r_calls r_spill l_calls l_spill fst snd] in C1, C2, C3, C4, C5, C6.
  assert (MB : forall pn, In pn ls -> In pn (lay_blocks (RLay lc ls la lr))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. right.
    apply in_or_app. left. exact Hpn. }
  assert (KP : forall pn, In pn ls -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KB; apply MB; exact Hpn).
  assert (HfrP : ~ In p (map fst ls)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & Eq & Hq). apply in_map_iff. exists pn.
    split; [exact Eq | apply MB; exact Hq]. }
  assert (KR : forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) by (intros a Ha; apply KG; sar_num).
  assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (sar_rest_kept bl bl' rd rd' A_G_REC (set_spill R (fn, As)) (set_spill R (fn, As ++ [x])) la lr HA HP HX
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(intros a Ha; apply KR; lia) KO) as (RA & RP & RX).
  exists (RLay lc (ls ++ [(p, k)]) la lr).
  pose proof (sar_lay_perm_full lc ls la lr (p, k)) as PERM.
  split; [|exact (sar_perm_iff _ _ (p, k) PERM)].
  unfold arep_at.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj RA (conj RP (conj RX _))))))).
  + unfold ag1_calls. cbn [set_spill r_calls r_spill l_calls l_spill fst snd].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
    * apply (aval_mem_kept rd); [exact C3 | intros j Hj; apply KR; sar_num].
    * intros i c P' Ec EP'. destruct (C4 i c P' Ec EP') as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      pose proof Hc as (_ & H6c & _).
      assert (HPQ : forall pn, In pn P' -> In pn (lay_blocks (RLay lc ls la lr))).
      { intros pn Hpn. unfold lay_blocks. cbn [l_calls]. apply in_or_app. left. apply in_concat.
        exists P'. split; [exact (nth_error_In _ _ EP') | exact Hpn]. }
      apply (acall_at_kept bl bl' rd rd' _ c P' Hc).
      ++ intros pn Hpn. exact (proj1 (KB pn (HPQ pn Hpn))).
      ++ intros j Hj. apply KR. sar_num.
      ++ intros pn j Hpn Hj. exact (proj2 (KB pn (HPQ pn Hpn)) j Hj).
    * apply (sar_call_arg bl bl' rd rd' A_REC_SPILL fn As ls x p k C5 H6 BN BS);
        [| exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
      intros a Ha H1 H2. apply KG; [sar_num | exact H1 | exact H2].
    * apply Forall_app. split; [exact C6 | constructor; [exact Hlx | constructor]].
  + unfold ag1_own. split.
    * apply (sar_nodup_fst_perm _ _ (Permutation_sym PERM)). apply sar_nodup_fst_snoc; [exact HND | exact Hfr].
    * intros pn Hpn. apply (Permutation_in _ PERM) in Hpn.
      apply in_app_or in Hpn as [Hpn|[<-|[]]]; [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

(* the recorder's state survives a change that keeps g_rec, record.spill and its own blocks (the answer_code walk's
   rec_repA_kept, over arep_at) *)
Lemma sar_arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall a, in_rec a -> rd' a = rd a) ->
(forall p n i, In (p, n) (lay_blocks Q) -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA HblQ Hgs Hb.
assert (Hg : forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) by (intros a Ha; apply Hgs; left; exact Ha).
assert (Hs : forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) by (intros a Ha; apply Hgs; right; exact Ha).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros [p n] i Hpn Hi; exact (Hb p n i Hpn Hi)).
clear Hgs Hb. unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

(* every block of the recorder's layout holds at least one byte *)
Lemma sar_lay_pos : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
forall pn, In pn (lay_blocks Q) -> 1 <= snd pn.
Proof.
intros bl rd R Q HA pn Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
    apply In_nth_error in Hin as (k & Hk).
    destruct (nth_error (snd c) k) as [s|] eqn:Hs.
    * destruct (H7 k s pn Hs Hk) as (_ & _ & _ & Hsz & _). lia.
    * exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
  + exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
  destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
  + destruct (H7 k s pn Hs Hk) as (_ & _ & _ & Hsz & _). lia.
  + exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
  destruct Hpn as [<- | []]. destruct Ha as (_ & _ & _ & Hsz & _). lia.
- unfold areply_at in Hr. destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
  destruct Hpn as [<- | []]. destruct Hr as (_ & _ & _ & Hne & _ & Hsz & _).
  destruct x as [|b x]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hsz. lia.
Qed.

Section d.
Variable B : asyms.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
End d.
