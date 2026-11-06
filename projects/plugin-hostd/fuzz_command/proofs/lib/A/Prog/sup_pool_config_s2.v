(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder's model steps for the walk of sup_after_reply on plugin-hostd/fuzz_command.asan: record() into a new slot or into record.spill, and the append of one argument, over CmdRep.v's reader form; ported from fuzz_command's plain lib/Prog/RecStep.v (rec_rep_record_lt, rep_at_record_full, call_at_arg, rep_at_arg_lt, rep_at_arg_full, rec_rep_arg); the frame lemmas aval_mem_kept .. rec_repA_kept copied from the answer_code walk (lib/A/Prog/answer_code.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_after_reply_s1.v, with its module names changed; 545 of its 609 lines of code are new or changed and 489 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the recorder-model steps of sup_pool_config's ASan walk (plugin-hostd/fuzz_command):
   record() and the argument appends over lib/A/Prog/CmdRep.v's rec_repA, in the form of the plain proof's
   rec_repA steps (lib/Prog/RecInv.v), for the walk lib/A/Prog/sup_pool_config.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
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
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot record() picks for the next call: g_rec.calls[n] while the table holds n < 16 calls, else record.spill *)
Definition spc_slot (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) else A_REC_SPILL.

(* the model of sup_pool_config is the recorder stub over record(REC_POOL_CONFIG) with its two arguments *)
Lemma spc_model : forall R name max,
sup_pool_config_m R name max =
rec_answer (rec_record R 14 [sarg name; dec max]) (14, [sarg name; dec max]) (shape_of (bstr "pool_config"%string)) true.
Proof. intros R name max. unfold sup_pool_config_m, rec_stub, daemon_shape, REC_POOL_CONFIG. reflexivity. Qed.

Lemma spc_slot_answer : forall R FN A, (length (r_calls R) <= 16)%nat ->
(exists k, nth_error (r_calls (rec_record R FN A)) k = Some (FN, A) /\
   spc_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(spc_slot R = A_REC_SPILL /\ (FN, A) = r_spill (rec_record R FN A)).
Proof.
intros R FN A Hle. unfold spc_slot, rec_record.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
- left. exists (length (r_calls R)). split; [|reflexivity].
  cbn [set_calls r_calls]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
- right. split; reflexivity.
Qed.

(* ---------- list facts (`NoDup` is stdpp's, as in CmdRep's ag1_own; the proofs go through List.NoDup) ---------- *)
Lemma spc_nodup_ins : forall (X Y : list Z) x, NoDup (X ++ Y) -> ~ In x (X ++ Y) -> NoDup (X ++ x :: Y).
Proof.
intros X Y x H Hx. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. revert H Hx.
induction X as [|y X IH]; intros H Hx; cbn [app] in *.
- apply List.NoDup_cons; [exact Hx | exact H].
- apply List.NoDup_cons_iff in H. destruct H as [Hy Hd]. apply List.NoDup_cons.
  + intros Hi. apply in_app_or in Hi. destruct Hi as [Hi|[Hi|Hi]].
    * apply Hy. apply in_or_app. left. exact Hi.
    * apply Hx. left. symmetry. exact Hi.
    * apply Hy. apply in_or_app. right. exact Hi.
  + apply IH; [exact Hd | intros Hi; apply Hx; right; exact Hi].
Qed.

Lemma spc_nodup_snoc : forall (P : list (Z * Z)) p n, NoDup (map fst P) -> ~ In p (map fst P) ->
NoDup (map fst (P ++ [(p, n)])).
Proof.
intros P p n H Hn. rewrite map_app. cbn [map fst].
pose proof (spc_nodup_ins (map fst P) [] p) as G. rewrite app_nil_r in G. exact (G H Hn).
Qed.

Lemma spc_nodup_mid : forall (X Y W : list (Z * Z)) p n, NoDup (map fst (X ++ Y ++ W)) -> ~ In p (map fst (X ++ Y ++ W)) ->
NoDup (map fst (X ++ (Y ++ [(p, n)]) ++ W)).
Proof.
intros X Y W p n H Hn.
replace (map fst (X ++ (Y ++ [(p, n)]) ++ W)) with ((map fst X ++ map fst Y) ++ p :: map fst W)
  by (rewrite !map_app, <- !app_assoc; reflexivity).
rewrite !map_app in H, Hn. rewrite app_assoc in H, Hn.
exact (spc_nodup_ins _ _ p H Hn).
Qed.

Lemma spc_in_mid : forall (X Y W : list (Z * Z)) pk pn, In pn (X ++ (Y ++ [pk]) ++ W) -> In pn (X ++ Y ++ W) \/ pn = pk.
Proof.
intros X Y W pk pn H. apply in_app_or in H. destruct H as [H|H]; [left; apply in_or_app; left; exact H|].
apply in_app_or in H. destruct H as [H|H].
- apply in_app_or in H. destruct H as [H|[H|[]]].
  + left. apply in_or_app. right. apply in_or_app. left. exact H.
  + right. symmetry. exact H.
- left. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

Lemma spc_iff_mid : forall (O X Y W : list (Z * Z)) pk, (forall pn, In pn O <-> In pn (X ++ Y ++ W)) ->
forall pn, In pn (O ++ [pk]) <-> In pn (X ++ (Y ++ [pk]) ++ W).
Proof.
intros O X Y W pk HO pn. split; intros H.
- apply in_app_or in H. destruct H as [H|[H|[]]].
  + apply (proj1 (HO pn)) in H. apply in_app_or in H. destruct H as [H|H]; apply in_or_app; [left; exact H|right].
    apply in_app_or in H. destruct H as [H|H]; apply in_or_app; [left; apply in_or_app; left; exact H | right; exact H].
  + subst pn. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
- destruct (spc_in_mid X Y W pk pn H) as [H1|H1].
  + apply in_or_app. left. apply (proj2 (HO pn)). exact H1.
  + subst pn. apply in_or_app. right. left. reflexivity.
Qed.

Lemma spc_notin_iff : forall (O L : list (Z * Z)) p, (forall pn, In pn O <-> In pn L) -> ~ In p (map fst O) ->
~ In p (map fst L).
Proof.
intros O L p HO Hn Hi. apply Hn. apply in_map_iff in Hi. destruct Hi as (pn & E & Hpn).
apply in_map_iff. exists pn. split; [exact E | apply (proj2 (HO pn)); exact Hpn].
Qed.

(* the layout with one more block after the last call's (or the spill's) argument blocks *)
Lemma spc_lay_last : forall l0 P ls la lr,
lay_blocks (RLay (l0 ++ [P]) ls la lr) = concat l0 ++ P ++ (ls ++ oblk la ++ oblk lr).
Proof.
intros l0 P ls la lr. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
rewrite concat_app. cbn [concat]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* ---------- reader facts kept ---------- *)
Lemma spc_aval_in : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma spc_bytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma spc_str_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (spc_bytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.

(* ---------- one call of the table ---------- *)
Lemma spc_call_block : forall bl (rd : reader) e c P pn, acall_at bl rd e c P -> In pn P -> In pn bl /\ 0 < snd pn.
Proof.
intros bl rd e c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
destruct (In_nth_error P pn Hin) as [k Ek].
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
destruct (Hk k s pn Es Ek) as (_ & _ & H3 & H4 & _). split; [exact H3 | lia].
Qed.

Lemma spc_call_kept : forall bl bl' (rd rd' : reader) e c P, acall_at bl rd e c P ->
(forall x, e <= x < e + 56 -> rd' x = rd x) ->
(forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' e c P.
Proof.
intros bl bl' rd rd' e c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) K KP.
unfold acall_at.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (spc_aval_in rd); [exact H4 | intros x Hx; apply K; unfold CALL_OFF_FN in Hx; lia]|].
split; [apply (spc_aval_in rd); [exact H5 | intros x Hx; apply K; unfold CALL_OFF_NARGS in Hx; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
destruct (KP pn (nth_error_In _ _ Hpn)) as [Kin Kb].
split; [apply (spc_aval_in rd); [exact G1 | intros x Hx; apply K; unfold CALL_OFF_ARGS in Hx; lia]|].
split; [exact G2|]. split; [exact Kin|]. split; [exact G4|].
apply (spc_str_kept rd); [exact G5 | intros i Hi; apply Kb; lia].
Qed.

(* a call record() just made: fn written, nargs 0, no argument *)
Lemma spc_call_new : forall bl (rd : reader) e fn P, 0 <= fn < REC_FN_COUNT -> length P = 0%nat ->
NoDup (map fst P) -> aval_mem rd (e + CALL_OFF_FN) 4 fn -> aval_mem rd (e + CALL_OFF_NARGS) 4 0 ->
acall_at bl rd e (fn, []) P.
Proof.
intros bl rd e fn P Hfn HP Hnd BF BA. unfold acall_at. cbn [fst snd length].
split; [exact Hfn|]. split; [lia|]. split; [exact HP|]. split; [exact BF|]. split; [exact BA|].
split; [exact Hnd|]. intros k s pn Hs. destruct k; discriminate.
Qed.

(* one more argument s of a call, in the fresh block (p, n): nargs and args[|A|] written, the rest of the call kept *)
Lemma spc_call_arg : forall bl bl' (rd rd' : reader) e fn A P s p n,
acall_at bl rd e (fn, A) P -> (length A < 6)%nat ->
aval_mem rd' (e + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
(forall x, e <= x < e + 56 -> ~ (e + 4 <= x < e + 4 + 4) ->
   ~ (e + 8 + 8 * Z.of_nat (length A) <= x < e + 8 + 8 * Z.of_nat (length A) + 8) -> rd' x = rd x) ->
(forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
~ In p (map fst P) -> p <> 0 -> In (p, n) bl' -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> astr_atR rd' p s ->
acall_at bl' rd' e (fn, A ++ [s]) (P ++ [(p, n)]).
Proof.
intros bl bl' rd rd' e fn A P s p n (H1 & H2 & H3 & H4 & H5 & H6 & H7) H6' BN BS K KP Hfr Hp0 Hin Hsz Hx.
cbn [fst snd] in H1, H2, H3, H4, H5, H7.
unfold acall_at. cbn [fst snd].
unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
split; [exact H1|]. split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, H3; reflexivity|].
split; [apply (spc_aval_in rd); [exact H4 | intros x Hx'; apply K; lia]|].
split; [rewrite length_app, Nat2Z.inj_add; exact BN|].
split; [exact (spc_nodup_snoc P p n H6 Hfr)|].
intros j t pn Es Ep.
destruct (Nat.lt_ge_cases j (length A)) as [Hj|Hj].
- rewrite nth_error_app1 in Es by exact Hj. rewrite nth_error_app1 in Ep by (rewrite H3; exact Hj).
  destruct (H7 j t pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
  destruct (KP pn (nth_error_In _ _ Ep)) as [Kin Kb].
  split; [apply (spc_aval_in rd); [exact G1 | intros x Hx'; apply K; lia]|].
  split; [exact G2|]. split; [exact Kin|]. split; [exact G4|].
  apply (spc_str_kept rd); [exact G5 | intros i Hi; apply Kb; lia].
- destruct (Nat.eq_dec j (length A)) as [->|Hne].
  + rewrite nth_error_app2, Nat.sub_diag in Es by lia. cbn in Es. injection Es as <-.
    rewrite nth_error_app2 in Ep by (rewrite H3; lia). rewrite H3, Nat.sub_diag in Ep. cbn in Ep.
    injection Ep as <-. cbn [fst snd].
    split; [exact BS|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hsz|]. exact Hx.
  + exfalso. assert (N : nth_error (A ++ [s]) j = None)
      by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    rewrite N in Es. discriminate.
Qed.

(* ---------- the answer, the reply and the scalars of g_rec ---------- *)
Lemma spc_rest_keep : forall bl bl' (rd rd' : reader) R Q,
aanswer_at bl rd A_G_REC (r_answer R) (l_answer Q) -> areply_at bl rd A_G_REC (r_reply R) (l_reply Q) ->
ag1_scalars rd A_G_REC R ->
(forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x) ->
(forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q) /\
ag1_scalars rd' A_G_REC R.
Proof.
intros bl bl' rd rd' R Q HA HP HX KR KQ.
split; [|split].
- unfold aanswer_at in *. unfold OFF_ANSWER in *.
  revert HA KQ. destruct (r_answer R) as [t|], (l_answer Q) as [[p k]|]; intros HA KQ; try contradiction.
  + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6). cbn [fst snd] in *.
    destruct (KQ (p, k) ltac:(apply in_or_app; left; cbn; left; reflexivity)) as [Kin Kp]. cbn [fst snd] in Kp.
    split; [apply (spc_aval_in rd); [exact N1 | intros x Hx; apply KR; right; lia]|].
    split; [exact N2|]. split; [exact Kin|]. split; [exact N4|].
    split; [apply (spc_str_kept rd); [exact N5 | intros i Hi; apply Kp; lia] | exact N6].
  + apply (spc_aval_in rd); [exact HA | intros x Hx; apply KR; right; lia].
- unfold areply_at in *. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  revert HP KQ. destruct (r_reply R) as [y|], (l_reply Q) as [[p k]|]; intros HP KQ; try contradiction.
  + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
    destruct (KQ (p, k) ltac:(apply in_or_app; right; cbn; left; reflexivity)) as [Kin Kp]. cbn [fst snd] in Kp.
    split; [apply (spc_aval_in rd); [exact P1 | intros x Hx; apply KR; right; lia]|].
    split; [apply (spc_aval_in rd); [exact P2 | intros x Hx; apply KR; right; lia]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|].
    split; [apply (spc_bytes_kept rd); [exact P7 | intros i Hi; apply Kp; lia] | exact P8].
  + destruct HP as [P1 P2].
    split; [apply (spc_aval_in rd); [exact P1 | intros x Hx; apply KR; right; lia]|].
    apply (spc_aval_in rd); [exact P2 | intros x Hx; apply KR; right; lia].
- unfold ag1_scalars in *. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  split; [apply (spc_aval_in rd); [exact X1 | intros x Hx; apply KR; left; lia]|].
  split; [apply (spc_aval_in rd); [exact X2 | intros x Hx; apply KR; left; lia]|].
  split; [apply (spc_aval_in rd); [exact X3 | intros x Hx; apply KR; right; lia]|].
  split; [apply (spc_aval_in rd); [exact X4 | intros x Hx; apply KR; right; lia]|].
  split; [apply (spc_aval_in rd); [exact X5 | intros x Hx; apply KR; right; lia]|].
  exact X6.
Qed.

(* ---------- the recorder's whole state ---------- *)
Lemma spc_lay_block : forall bl (rd : reader) R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
forall pn, In pn (lay_blocks Q) -> In pn bl /\ 0 < snd pn.
Proof.
intros bl rd R Q (_ & _ & _ & (C1 & C2 & _ & C4 & C5 & _) & Ha & Hr & _ & _) pn Hpn.
unfold lay_blocks in Hpn.
apply in_app_or in Hpn. destruct Hpn as [Hpn | Hpn].
- apply in_concat in Hpn. destruct Hpn as (P & HP & Hin). apply In_nth_error in HP. destruct HP as (i & Hi).
  assert (Hil : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  exact (spc_call_block bl rd _ c P pn (proj1 (C4 i c P Hc Hi)) Hin).
- apply in_app_or in Hpn. destruct Hpn as [Hpn | Hpn]; [exact (spc_call_block bl rd _ _ _ pn C5 Hpn)|].
  apply in_app_or in Hpn. destruct Hpn as [Hpn | Hpn].
  + unfold aanswer_at in Ha.
    destruct (r_answer R) as [x|], (l_answer Q) as [q|]; cbn [oblk In] in Hpn, Ha; try contradiction.
    destruct Hpn as [<- | []]. destruct Ha as (_ & _ & A3 & A4 & _). split; [exact A3 | lia].
  + unfold areply_at in Hr.
    destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn [oblk In] in Hpn, Hr; try contradiction.
    destruct Hpn as [<- | []]. destruct Hr as (_ & _ & _ & A4 & A5 & A6 & _). split; [exact A5|].
    destruct x as [|b x]; [exfalso; exact (A4 eq_refl)|]. cbn [length] in A6. lia.
Qed.

(* every byte of g_rec and record.spill and of the recorder's blocks kept *)
Lemma spc_arep_keep : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HW) KQ Hg Hs.
unfold REC_SIZE, SC_SIZE in Hg, Hs.
assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x)
  by (intros x Hx; apply Hg; lia).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (spc_rest_keep bl bl' rd rd' R Q Ha Hr HX KR KO) as (RA & RP & RX).
unfold arep_at, ag1_calls.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX | exact HW]. }
split; [exact C1|]. split; [exact C2|].
split; [apply (spc_aval_in rd); [exact C3 | intros x Hx; apply Hg; unfold OFF_NCALLS in Hx; lia]|].
split.
{ intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (spc_call_kept bl bl' rd rd' _ c P Hc).
  - intros x Hx. apply Hg. unfold OFF_CALLS, CALL_SIZE in Hx. lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
    split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
split; [|exact C6].
apply (spc_call_kept bl bl' rd rd' _ _ _ C5).
- intros x Hx. apply Hs. lia.
- intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
Qed.

(* one more argument of the last call of g_rec's table *)
Lemma spc_arep_arg_lt : forall bl bl' (rd rd' : reader) R FN A l0 P ls la lr s p n e,
arep_at bl rd A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(FN, A)])) (RLay (l0 ++ [P]) ls la lr) ->
(length (r_calls R) < 16)%nat -> (length A < 6)%nat ->
e = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
   ~ (e + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < e + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
   rd' a = rd a) ->
(forall pn, In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr)) -> In pn bl' /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (e + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> p <> 0 ->
In (p, n) bl' -> iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
~ In p (map fst (lay_blocks (RLay (l0 ++ [P]) ls la lr))) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(FN, A ++ [s])])) (RLay (l0 ++ [P ++ [(p, n)]]) ls la lr).
Proof.
intros bl bl' rd rd' R FN A l0 P ls la lr s p n e HA Hn H6 Ee KG KB BN BS Hx Hlx Hsz Hp0 Hin Ha1 Ha2 Hfr.
subst e.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HND & HAP).
cbn [set_calls r_calls r_spill l_calls l_spill] in C1, C2, C3, C4, C5, C6.
assert (MB : forall pn, In pn P -> In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr))).
{ intros pn Hpn. rewrite spc_lay_last. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
assert (KP : forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn Hpn; apply KB; apply MB; exact Hpn).
assert (HfrP : ~ In p (map fst P)).
{ intros Hq. apply Hfr. apply in_map_iff in Hq. destruct Hq as (pn & E & Hq). apply in_map_iff. exists pn.
  split; [exact E | apply MB; exact Hq]. }
assert (L0 : length l0 = length (r_calls R)) by (rewrite !length_app in C2; cbn [length] in C2; lia).
assert (Ee : nth_error (r_calls R ++ [(FN, A)]) (length (r_calls R)) = Some (FN, A))
  by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
assert (Ep : nth_error (l0 ++ [P]) (length (r_calls R)) = Some P)
  by (rewrite nth_error_app2, L0, Nat.sub_diag by lia; reflexivity).
destruct (C4 _ _ _ Ee Ep) as [CE CL].
unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
unfold iv_apart in G3.
assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x).
{ intros x Hx'. apply KG; [left; lia | lia | lia]. }
assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn bl' /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KB. rewrite spc_lay_last. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. right. exact Hpn. }
destruct (spc_rest_keep bl bl' rd rd' R (RLay (l0 ++ [P]) ls la lr) Ha Hr HX KR KO) as (RA & RP & RX).
unfold arep_at, ag1_calls, ag1_own.
cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX|].
  rewrite (spc_lay_last l0 P) in HND, HAP, Hfr. rewrite (spc_lay_last l0 (P ++ [(p, n)])).
  split; [exact (spc_nodup_mid _ _ _ p n HND Hfr)|].
  intros pn Hpn. destruct (spc_in_mid _ _ _ _ _ Hpn) as [Hq | ->];
    [exact (HAP pn Hq) | cbn [fst snd]; split; assumption]. }
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app; cbn [length]; lia|].
split.
{ rewrite length_app in C3 |- *. cbn [length] in C3 |- *.
  apply (spc_aval_in rd); [exact C3 | intros x Hx'; apply KG; [left; lia | lia | lia]]. }
split.
{ intros i c P' Ec EP'.
  destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
  - assert (Ec0 : nth_error (r_calls R ++ [(FN, A)]) i = Some c)
      by (rewrite nth_error_app1 in Ec |- * by exact Hi; exact Ec).
    assert (EP1 : nth_error l0 i = Some P') by (rewrite nth_error_app1 in EP' by lia; exact EP').
    assert (EP0 : nth_error (l0 ++ [P]) i = Some P') by (rewrite nth_error_app1 by lia; exact EP1).
    destruct (C4 i c P' Ec0 EP0) as [Hc HL]. split; [|exact HL].
    apply (spc_call_kept bl bl' rd rd' _ c P' Hc).
    + intros x Hx'. apply KG; [left; lia | lia | lia].
    + intros pn Hpn. apply KB. rewrite spc_lay_last. apply in_or_app. left. apply in_concat. exists P'.
      split; [exact (nth_error_In _ _ EP1) | exact Hpn].
  - destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
    + rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
      rewrite nth_error_app2, L0, Nat.sub_diag in EP' by lia. cbn in EP'. injection EP' as <-.
      split; [|apply Forall_app; split; [exact CL | constructor; [exact Hlx | constructor]]].
      apply (spc_call_arg bl bl' rd rd' _ FN A P s p n CE H6 BN BS);
        [| exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
      intros x Hx' H1 H2. apply KG; [left; lia | exact H1 | exact H2].
    + exfalso. assert (N : nth_error (r_calls R ++ [(FN, A ++ [s])]) i = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
      rewrite N in Ec. discriminate. }
split; [|exact C6].
apply (spc_call_kept bl bl' rd rd' _ _ _ C5).
- intros x Hx'. apply KG; [right; lia | lia | lia].
- intros pn Hpn. apply KB. rewrite spc_lay_last. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. left. exact Hpn.
Qed.

(* one more argument of the call in record.spill *)
Lemma spc_arep_arg_full : forall bl bl' (rd rd' : reader) R FN A lc ls la lr s p n,
arep_at bl rd A_G_REC A_REC_SPILL (set_spill R (FN, A)) (RLay lc ls la lr) ->
(length A < 6)%nat ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) ->
   ~ (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a <
      A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
   rd' a = rd a) ->
(forall pn, In pn (lay_blocks (RLay lc ls la lr)) -> In pn bl' /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> p <> 0 ->
In (p, n) bl' -> iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
~ In p (map fst (lay_blocks (RLay lc ls la lr))) ->
arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (FN, A ++ [s])) (RLay lc (ls ++ [(p, n)]) la lr).
Proof.
intros bl bl' rd rd' R FN A lc ls la lr s p n HA H6 KG KB BN BS Hx Hlx Hsz Hp0 Hin Ha1 Ha2 Hfr.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HND & HAP).
cbn [set_spill r_calls r_spill l_calls l_spill] in C1, C2, C3, C4, C5, C6.
assert (MB : forall pn, In pn ls -> In pn (lay_blocks (RLay lc ls la lr))).
{ intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. right.
  apply in_or_app. left. exact Hpn. }
assert (KP : forall pn, In pn ls -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn Hpn; apply KB; apply MB; exact Hpn).
assert (HfrP : ~ In p (map fst ls)).
{ intros Hq. apply Hfr. apply in_map_iff in Hq. destruct Hq as (pn & E & Hq). apply in_map_iff. exists pn.
  split; [exact E | apply MB; exact Hq]. }
unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
unfold iv_apart in G3.
assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x).
{ intros x Hx'. apply KG; [left; lia | lia | lia]. }
assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn bl' /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. right.
  apply in_or_app. right. exact Hpn. }
destruct (spc_rest_keep bl bl' rd rd' R (RLay lc ls la lr) Ha Hr HX KR KO) as (RA & RP & RX).
unfold arep_at, ag1_calls, ag1_own.
cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply fst snd].
unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX|].
  unfold lay_blocks in HND, HAP, Hfr |- *. cbn [l_calls l_spill l_answer l_reply] in HND, HAP, Hfr |- *.
  split; [exact (spc_nodup_mid _ _ _ p n HND Hfr)|].
  intros pn Hpn. destruct (spc_in_mid _ _ _ _ _ Hpn) as [Hq | ->];
    [exact (HAP pn Hq) | cbn [fst snd]; split; assumption]. }
split; [exact C1|]. split; [exact C2|].
split; [apply (spc_aval_in rd); [exact C3 | intros x Hx'; apply KG; [left; lia | lia | lia]]|].
split.
{ intros i c P' Ec EP'. destruct (C4 i c P' Ec EP') as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (spc_call_kept bl bl' rd rd' _ c P' Hc).
  - intros x Hx'. apply KG; [left; lia | lia | lia].
  - intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. left.
    apply in_concat. exists P'. split; [exact (nth_error_In _ _ EP') | exact Hpn]. }
split.
{ apply (spc_call_arg bl bl' rd rd' _ FN A ls s p n C5 H6 BN BS);
    [| exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
  intros x Hx' H1 H2. apply KG; [right; lia | exact H1 | exact H2]. }
apply Forall_app. split; [exact C6 | constructor; [exact Hlx | constructor]].
Qed.

Section d.
Variable B : asyms.

(* the recorder's facts the walk reads off rec_repA *)
Lemma spc_rep_ncalls : forall ly S rd R O, rec_repA B ly S rd R O ->
aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))) /\ (length (r_calls R) <= 16)%nat.
Proof.
intros ly S rd R O (Q & (_ & _ & _ & (C1 & _ & C3 & _) & _) & _). split; [exact C3 | exact C1].
Qed.

Lemma spc_rep_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. exact (proj1 (spc_lay_block _ rd R Q HA pn (proj1 (HO pn) Hpn))).
Qed.

Lemma spc_rep_own : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O ->
0 < snd pn /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply (proj1 (HO pn)) in Hpn.
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & HW).
destruct (HW pn Hpn) as [W1 W2].
split; [exact (proj2 (spc_lay_block _ rd R Q HA pn Hpn)) | split; [exact W1 | exact W2]].
Qed.

Lemma spc_rep_answer_old : forall ly S rd R O, rec_repA B ly S rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists n, In (old, n) O).
Proof.
intros ly S rd R O (Q & (_ & _ & _ & _ & Ha & _) & HO).
unfold aanswer_at in Ha. destruct (r_answer R) as [x|], (l_answer Q) as [[p k]|] eqn:EA; try contradiction.
- exists p. split; [exact (proj1 Ha)|]. right. exists k. apply (proj2 (HO (p, k))).
  unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  left. reflexivity.
- exists 0. split; [exact Ha | left; reflexivity].
Qed.

(* a recorder state survives every write outside g_rec, record.spill and its own blocks *)
Lemma spc_rep_keep : forall ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
apply (spc_arep_keep _ _ rd rd' R Q HA); [|exact Hg | exact Hs].
intros pn Hpn. apply (proj2 (HO pn)) in Hpn. split; [exact (Hbl pn Hpn) | intros i Hi; exact (Hb pn i Hpn Hi)].
Qed.

(* record(FN) on a table of fewer than 16 calls: ncalls := n + 1, the new slot gets fn := FN and nargs := 0 *)
Lemma spc_rep_slot : forall ly S ly' S' (rd rd' : reader) R O FN,
rec_repA B ly S rd R O -> (length (r_calls R) < 16)%nat -> 0 <= FN < REC_FN_COUNT ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
   ~ (spc_slot R <= a < spc_slot R + 8) -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd' (spc_slot R + CALL_OFF_FN) 4 FN -> aval_mem rd' (spc_slot R + CALL_OFF_NARGS) 4 0 ->
rec_repA B ly' S' rd' (rec_record R FN []) O.
Proof.
intros ly S ly' S' rd rd' R O FN (Q & HA & HO) Hn Hfn Hbl KG KS KB BN BF BA.
assert (Es : spc_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
  by (unfold spc_slot; destruct (Nat.ltb_spec (length (r_calls R)) 16); [reflexivity | lia]).
rewrite Es in KG, BF, BA. clear Es.
rewrite (rec_record_calls R FN [] Hn).
assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply (proj2 (HO pn)) in Hpn. split; [exact (Hbl pn Hpn) | intros i Hi; exact (KB pn i Hpn Hi)]. }
assert (LB : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite !app_nil_r. reflexivity. }
exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
split; [|rewrite LB; exact HO].
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HW).
unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *.
assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x)
  by (intros x Hx; apply KG; lia).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn (ablocks B ly' S') /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (spc_rest_keep _ _ rd rd' R Q Ha Hr HX KR KO) as (RA & RP & RX).
unfold arep_at, ag1_calls.
cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX|]. unfold ag1_own in *. rewrite LB. exact HW. }
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, C2; reflexivity|].
split; [rewrite length_app, Nat2Z.inj_add; exact BN|].
split.
{ intros i c P Ec EP.
  destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
  - rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
    destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    apply (spc_call_kept _ _ rd rd' _ c P Hc).
    + intros x Hx. apply KG; lia.
    + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
      split; [exact (nth_error_In _ _ EP) | exact Hpn].
  - destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
    + rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
      rewrite nth_error_app2 in EP by (rewrite C2; lia). rewrite C2, Nat.sub_diag in EP. cbn in EP.
      injection EP as <-.
      split; [|constructor].
      apply spc_call_new; [exact Hfn | reflexivity | constructor | exact BF | exact BA].
    + exfalso. assert (N : nth_error (r_calls R ++ [(FN, [])]) i = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
      rewrite N in Ec. discriminate. }
split; [|exact C6].
apply (spc_call_kept _ _ rd rd' _ _ _ C5).
- intros x Hx. apply KS. lia.
- intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
Qed.

(* record(FN) on a full table, after rec_calls_free emptied the spill: the spill gets fn := FN and nargs := 0 *)
Lemma spc_rep_spill : forall ly S ly' S' (rd rd' : reader) R O FN,
rec_repA B ly S rd (set_spill R (fst (r_spill R), [])) O -> length (r_calls R) = 16%nat -> 0 <= FN < REC_FN_COUNT ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 FN -> aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
rec_repA B ly' S' rd' (rec_record R FN []) O.
Proof.
intros ly S ly' S' rd rd' R O FN (Q & HA & HO) Hn Hfn Hbl KG KS KB BF BA.
rewrite (rec_record_spill R FN [] Hn).
assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply (proj2 (HO pn)) in Hpn. split; [exact (Hbl pn Hpn) | intros i Hi; exact (KB pn i Hpn Hi)]. }
exists Q. split; [|exact HO].
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HX & HW).
unfold REC_SIZE, SC_SIZE in KG, KS.
assert (KR : forall x, A_G_REC <= x < A_G_REC + 8 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x)
  by (intros x Hx; apply KG; lia).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn (ablocks B ly' S') /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (spc_rest_keep _ _ rd rd' R Q Ha Hr HX KR KO) as (RA & RP & RX).
cbn [set_spill r_calls r_spill fst snd] in C1, C2, C3, C4, C5, C6.
unfold arep_at, ag1_calls.
cbn [set_spill r_calls r_spill r_answer r_reply fst snd].
unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
2: { split; [exact RA|]. split; [exact RP|]. split; [exact RX | exact HW]. }
split; [exact C1|]. split; [exact C2|].
split; [apply (spc_aval_in rd); [exact C3 | intros x Hx; apply KG; lia]|].
split.
{ intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (spc_call_kept _ _ rd rd' _ c P Hc).
  - intros x Hx. apply KG. lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
    split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
split; [|constructor].
destruct C5 as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
apply spc_call_new; [exact Hfn | exact D3 | exact D6 | exact BF | exact BA].
Qed.

(* one more argument s of the call record() just made: nargs := |A| + 1, args[|A|] := p, p a fresh block holding s *)
Lemma spc_rep_arg : forall ly S ly' S' (rd rd' : reader) R O FN A p s n,
rec_repA B ly S rd (rec_record R FN A) O -> (length (r_calls R) <= 16)%nat -> (length A < 6)%nat ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) -> In (p, n) (ablocks B ly' S') ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (spc_slot R + CALL_OFF_NARGS <= a < spc_slot R + CALL_OFF_NARGS + 4) ->
   ~ (spc_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < spc_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
   rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (spc_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (spc_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> p <> 0 ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE -> ~ In p (map fst O) ->
rec_repA B ly' S' rd' (rec_record R FN (A ++ [s])) (O ++ [(p, n)]).
Proof.
intros ly S ly' S' rd rd' R O FN A p s n (Q & HA & HO) Hle H6 Hbl Hin KG KB BN BS Hx Hlx Hsz Hp0 Ha1 Ha2 Hfr.
assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply (proj2 (HO pn)) in Hpn. split; [exact (Hbl pn Hpn) | intros i Hi; exact (KB pn i Hpn Hi)]. }
pose proof (spc_notin_iff O (lay_blocks Q) p HO Hfr) as Hfr'.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
- assert (Es : spc_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold spc_slot; destruct (Nat.ltb_spec (length (r_calls R)) 16); [reflexivity | lia]).
  rewrite Es in KG, BN, BS.
  rewrite (rec_record_calls R FN A Hn) in HA. rewrite (rec_record_calls R FN (A ++ [s]) Hn).
  destruct Q as [lc ls la lr].
  pose proof HA as (_ & _ & _ & (_ & C2 & _) & _).
  cbn [set_calls r_calls l_calls] in C2. rewrite length_app in C2. cbn [length] in C2.
  assert (NE : lc <> []) by (intros E; rewrite E in C2; cbn in C2; lia).
  destruct (exists_last NE) as (l0 & P & E). subst lc.
  exists (RLay (l0 ++ [P ++ [(p, n)]]) ls la lr). split.
  + exact (spc_arep_arg_lt _ _ rd rd' R FN A l0 P ls la lr s p n _ HA Hn H6 eq_refl KG KQ BN BS Hx Hlx Hsz Hp0 Hin
      Ha1 Ha2 Hfr').
  + intros pn. rewrite (spc_lay_last l0 (P ++ [(p, n)])). rewrite (spc_lay_last l0 P) in HO.
    exact (spc_iff_mid O _ _ _ (p, n) HO pn).
- assert (Hn16 : length (r_calls R) = 16%nat) by lia.
  assert (Es : spc_slot R = A_REC_SPILL) by (unfold spc_slot; rewrite Hn16; reflexivity).
  rewrite Es in KG, BN, BS.
  rewrite (rec_record_spill R FN A Hn16) in HA. rewrite (rec_record_spill R FN (A ++ [s]) Hn16).
  destruct Q as [lc ls la lr].
  exists (RLay lc (ls ++ [(p, n)]) la lr). split.
  + exact (spc_arep_arg_full _ _ rd rd' R FN A lc ls la lr s p n HA H6 KG KQ BN BS Hx Hlx Hsz Hp0 Hin Ha1 Ha2 Hfr').
  + intros pn. exact (spc_iff_mid O (concat lc) ls (oblk la ++ oblk lr) (p, n) HO pn).
Qed.

End d.
