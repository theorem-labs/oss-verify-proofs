(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder step of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command): the
   inlined arg_s adds its copy to the call record() made, after fuzz_command's plain lib/Prog/RecInv.v (rep_at) over
   the ASan reader (lib/A/Prog/CmdRep.v). *)

(* After record(13) the recorder holds rec_record R 13 [] (a slot with no argument); arg_s stores the copy p of the
   argument x into args[0] and sets nargs to 1. The representation then holds rec_record R 13 [x], and the recorder
   owns its blocks and the copy's block. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot the inlined record() picks for the recorder state R (RecModel.v:38-39 rec_record) *)
Definition spa_slot_of (R : rstate) (c : Z) : Prop :=
((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) \/
((16 <= length (r_calls R))%nat /\ c = A_REC_SPILL).

Lemma acall_at_nil_args : forall bl rd a fn P, acall_at bl rd a (fn, []) P -> P = [].
Proof. intros bl rd a fn P (_ & _ & HL & _). destruct P; [reflexivity | discriminate HL]. Qed.

(* the entry with one argument: the copy p of x, its nargs field 1, its fn field kept *)
Lemma spa_acall_one : forall bl bl' (rd rd' : reader) c fn x p,
acall_at bl rd c (fn, []) [] ->
(forall i, 0 <= i < CALL_OFF_NARGS -> rd' (c + i) = rd (c + i)) ->
aval_mem rd' (c + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (c + CALL_OFF_ARGS) 8 p ->
p <> 0 -> In (p, Z.of_nat (length x) + 1) bl' -> Z.of_nat (length x) <= LMAX -> astr_atR rd' p x ->
acall_at bl' rd' c (fn, [x]) [(p, Z.of_nat (length x) + 1)].
Proof.
intros bl bl' rd rd' c fn x p (H0 & _ & _ & H3 & _) Hfn Hna Harg Hp0 Hin Hlx Hstr.
unfold acall_at. cbn [fst snd length].
split; [exact H0|]. split; [lia|]. split; [reflexivity|].
split; [apply (aval_mem_agree_in rd rd' c CALL_OFF_NARGS); [exact H3 | intros i Hi; exact (Hfn i Hi) | unfold CALL_OFF_FN; lia
  | unfold CALL_OFF_FN, CALL_OFF_NARGS; cbn; lia]|].
split; [exact Hna|]. split.
{ cbn [map fst]. apply NoDup_ListNoDup. apply List.NoDup_cons; [intros Hf; destruct Hf | apply List.NoDup_nil]. }
intros k s pn Hs Hpn. destruct k as [|k]; [|destruct k; discriminate Hs].
cbn in Hs, Hpn. injection Hs as <-. injection Hpn as <-. cbn [fst snd].
split; [replace (c + CALL_OFF_ARGS + 8 * Z.of_nat 0) with (c + CALL_OFF_ARGS) by lia; exact Harg|].
split; [exact Hp0|]. split; [exact Hin|]. split; [unfold LMAX in *; lia|]. exact Hstr.
Qed.

Lemma concat_snoc_nil : forall {X} (l : list (list X)), concat (l ++ [[]]) = concat l.
Proof. intros X l. rewrite concat_app. cbn. rewrite !app_nil_r. reflexivity. Qed.

Lemma firstn_snoc : forall {X} (l : list X) n, length l = S n -> exists y, l = firstn n l ++ [y].
Proof.
intros X l n Hl. destruct (nth_error l n) as [y|] eqn:Hy.
- exists y. rewrite <- (firstn_skipn n l) at 1. f_equal.
  destruct (skipn n l) as [|z t] eqn:Hs.
  + exfalso. pose proof (f_equal (@length X) Hs) as H. rewrite length_skipn in H. cbn in H. lia.
  + assert (Ht : t = []) by (pose proof (f_equal (@length X) Hs) as H; rewrite length_skipn in H; cbn in H;
      destruct t; [reflexivity | cbn in H; lia]). subst t.
    rewrite <- (firstn_skipn n l) in Hy. rewrite Hs, nth_error_app2 in Hy by (rewrite length_firstn; lia).
    rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hy by lia. cbn in Hy. injection Hy as ->. reflexivity.
- exfalso. apply nth_error_None in Hy. lia.
Qed.

Lemma spa_nodup_insert : forall (A B : list Z) x, List.NoDup (A ++ B) -> ~ In x (A ++ B) -> List.NoDup (A ++ x :: B).
Proof.
intros A B x HND Hx. apply (Permutation_NoDup (Permutation_middle A B x)). constructor; assumption.
Qed.

Section e.
(* the representation after arg_s: the slot c of the call record() made gets the copy p of x *)
Lemma spa_rep_add : forall bl bl' (rd rd' : reader) R c x p O1,
spa_slot_of R c ->
(exists Q, arep_at bl rd A_G_REC A_REC_SPILL (rec_record R REC_PIN_ACCEPT []) Q /\ (forall pn, In pn O1 <-> In pn (lay_blocks Q))) ->
(forall pn, In pn O1 -> In pn bl') ->
(forall pn, In pn O1 -> fst pn <> p) ->
In (p, Z.of_nat (length x) + 1) bl' ->
iv_apart p (Z.of_nat (length x) + 1) A_G_REC REC_SIZE -> iv_apart p (Z.of_nat (length x) + 1) A_REC_SPILL SC_SIZE ->
p <> 0 -> Z.of_nat (length x) <= LMAX ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_ARGS + 8) -> rd' a = rd a) ->
(forall pn i, In pn O1 -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (c + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (c + CALL_OFF_ARGS) 8 p -> astr_atR rd' p x ->
exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R REC_PIN_ACCEPT [x]) Q' /\
  (forall pn, In pn (O1 ++ [(p, Z.of_nat (length x) + 1)]) <-> In pn (lay_blocks Q')).
Proof.
intros bl bl' rd rd' R c x p O1 Hslot (Q & HA & HOQ) HOin HOp Hpin Hpg Hps Hp0 Hlx Hrd Hblk Hna Harg Hstr.
set (n := Z.of_nat (length x) + 1) in *.
destruct HA as (Hg8 & Hs8 & Hap & (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf) & HANS & HREP & HSC & (HND & Hown)).
assert (HlQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn) /\ fst pn <> p).
{ intros pn Hpn. apply HOQ in Hpn. split; [exact (HOin pn Hpn)|]. split; [|exact (HOp pn Hpn)].
  intros i Hi. exact (Hblk pn i Hpn Hi). }
assert (Hgr : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_ARGS + 8) -> rd' a = rd a)
  by (intros a Ha Hn; apply Hrd; [left; exact Ha | exact Hn]).
assert (Hsp : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_ARGS + 8) -> rd' a = rd a)
  by (intros a Ha Hn; apply Hrd; [right; exact Ha | exact Hn]).
unfold rec_record in *.
destruct Hslot as [(Hlt & Hc) | (Hge & Hc)].
- (* a new slot of g_rec.calls, index len *)
  replace (Nat.ltb (length (r_calls R)) 16) with true in * by (symmetry; apply Nat.ltb_lt; exact Hlt).
  cbn [r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host set_calls] in *.
  rewrite length_app in Hlen, HlenQ, Hnc. cbn [length] in Hlen, HlenQ, Hnc. rewrite Nat.add_1_r in HlenQ.
  set (len := length (r_calls R)) in *.
  destruct (firstn_snoc (l_calls Q) len HlenQ) as (Plast & HlcQ).
  assert (Hnlast : nth_error (r_calls R ++ [(REC_PIN_ACCEPT, [])]) len = Some (REC_PIN_ACCEPT, []))
    by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  assert (HnQ : nth_error (l_calls Q) len = Some Plast)
    by (rewrite HlcQ, nth_error_app2 by (rewrite length_firstn; lia); rewrite length_firstn, Nat.min_l, Nat.sub_diag by lia; reflexivity).
  destruct (Hcalls len _ Plast Hnlast HnQ) as [HCl _].
  pose proof (acall_at_nil_args _ _ _ _ _ HCl) as ->.
  set (lc := firstn len (l_calls Q)) in *.
  assert (Hlc : length lc = len) by (unfold lc; rewrite length_firstn; lia).
  exists (RLay (lc ++ [[(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  assert (Hlay : forall pn, In pn (lay_blocks Q) <-> In pn (concat lc ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
  { intros pn. unfold lay_blocks. rewrite HlcQ, concat_snoc_nil. reflexivity. }
  split.
  + unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
    split.
    { unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
      rewrite length_app. cbn [length]. split; [lia|]. split; [rewrite length_app, Hlc; cbn; lia|].
      split.
      { apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NCALLS) 4 (A_G_REC + OFF_NCALLS) 4); [exact Hnc | | lia | cbn; lia].
        intros i Hi. apply Hgr; [unfold OFF_NCALLS, REC_SIZE; lia|]. subst c. unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS. lia. }
      split.
      { intros i cl P Hci HPi.
        destruct (Nat.lt_ge_cases i len) as [Hil | Hil].
        - assert (Hc0 : nth_error (r_calls R ++ [(REC_PIN_ACCEPT, [])]) i = Some cl) by (rewrite nth_error_app1 by lia; rewrite nth_error_app1 in Hci by lia; exact Hci).
          assert (HP0 : nth_error (l_calls Q) i = Some P)
            by (rewrite nth_error_app1 in HPi by (rewrite Hlc; lia); rewrite HlcQ, nth_error_app1 by (rewrite Hlc; lia); exact HPi).
          destruct (Hcalls i cl P Hc0 HP0) as [HCi HFi]. split; [|exact HFi].
          apply (acall_at_agree bl bl' rd rd'); [exact HCi | |].
          + intros j Hj. apply Hgr; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
            subst c. unfold OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia.
          + intros pn Hpn. destruct (HlQ pn) as (H1 & H2 & _); [|split; assumption].
            apply Hlay. apply in_or_app. left. exact (In_concat_nth lc i P pn ltac:(rewrite nth_error_app1 in HPi by (rewrite Hlc; lia); exact HPi) Hpn).
        - assert (Hi : i = len).
          { pose proof (proj1 (nth_error_Some _ i) ltac:(rewrite Hci; discriminate)) as Hlti. rewrite length_app in Hlti. cbn [length] in Hlti. lia. }
          subst i. rewrite nth_error_app2 in Hci by lia. rewrite Nat.sub_diag in Hci. cbn in Hci. injection Hci as <-.
          rewrite nth_error_app2 in HPi by (rewrite Hlc; lia).
          rewrite Hlc, Nat.sub_diag in HPi. cbn in HPi. injection HPi as <-.
          split; [|constructor; [cbn; lia | constructor]].
          rewrite <- Hc. apply (spa_acall_one bl bl' rd rd' c REC_PIN_ACCEPT x p).
          + rewrite Hc. exact HCl.
          + intros i Hi. apply Hgr; [subst c; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_NARGS in *; nia|].
            unfold CALL_OFF_NARGS in *. lia.
          + exact Hna.
          + exact Harg.
          + exact Hp0.
          + exact Hpin.
          + exact Hlx.
          + exact Hstr. }
      split; [|exact Hspf].
      apply (acall_at_agree bl bl' rd rd'); [exact Hspill | |].
      - intros j Hj. apply Hsp; [unfold CALL_SIZE, SC_SIZE in *; lia|].
        subst c. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia.
      - intros pn Hpn. destruct (HlQ pn) as (H1 & H2 & _); [|split; assumption].
        apply Hlay. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
    split.
    { cbn [r_answer set_calls l_answer]. unfold aanswer_at in *.
      destruct (r_answer R) as [xa|], (l_answer Q) as [pa|] eqn:EA; try contradiction.
      - destruct HANS as (V & Hnz & Hin & Hl & Hs & Hlx').
        assert (Hpa : In pa (lay_blocks Q)) by (apply Hlay; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        destruct (HlQ pa Hpa) as (Hin' & Hgp & _).
        split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact V | | lia | cbn; lia]|].
        { intros i Hi. apply Hgr; [unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia|].
          subst c. unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia. }
        split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hl|]. split; [|exact Hlx'].
        apply (astr_atR_agree_in rd rd' (fst pa) (snd pa)); [exact Hs | exact Hgp | lia | lia].
      - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact HANS | | lia | cbn; lia].
        intros i Hi. apply Hgr; [unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia|].
        subst c. unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia. }
    split.
    { cbn [r_reply set_calls l_reply]. unfold areply_at in *.
      destruct (r_reply R) as [xr|], (l_reply Q) as [pr|] eqn:ER; try contradiction.
      - destruct HREP as (V1 & V2 & Hnz & Hne & Hin & Hl & Hb & Hlx').
        assert (Hpr : In pr (lay_blocks Q)) by (apply Hlay; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
        destruct (HlQ pr Hpr) as (Hin' & Hgp & _).
        split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | | lia | cbn; lia]|].
        { intros i Hi. apply Hgr; [unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia|].
          subst c. unfold OFF_CALLS, CALL_SIZE, OFF_REPLY, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia. }
        split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | | unfold OFF_REPLY_SIZE, OFF_REPLY; lia | unfold OFF_REPLY_SIZE, OFF_REPLY; cbn; lia]|].
        { intros i Hi. apply Hgr; [unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia|].
          subst c. unfold OFF_CALLS, CALL_SIZE, OFF_REPLY, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia. }
        split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hl|]. split; [|exact Hlx'].
        apply (abytes_atR_agree_in rd rd' (fst pr) (snd pr)); [exact Hb | exact Hgp | lia | lia].
      - destruct HREP as [V1 V2].
        split; apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); try first [exact V1 | exact V2];
          try (unfold OFF_REPLY_SIZE, OFF_REPLY; cbn; lia);
          intros i Hi; apply Hgr; (try (unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia));
          subst c; unfold OFF_CALLS, CALL_SIZE, OFF_REPLY, CALL_OFF_NARGS, CALL_OFF_ARGS in *; nia. }
    split.
    { destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rg). unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_calls].
      assert (HA0 : forall o w v, 0 <= o -> o + Z.of_nat w <= REC_SIZE -> (o + Z.of_nat w <= OFF_CALLS \/ OFF_ANSWER <= o) ->
        aval_mem rd (A_G_REC + o) w v -> aval_mem rd' (A_G_REC + o) w v).
      { intros o w v Ho Hw Hd Hv. apply (aval_mem_agree_in rd rd' (A_G_REC + o) (Z.of_nat w)); [exact Hv | | lia | lia].
        intros i Hi. apply Hgr; [unfold REC_SIZE in *; lia|].
        subst c. unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER, CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SIZE in *. nia. }
      split; [apply HA0; [unfold OFF_REFUSE; lia | unfold OFF_REFUSE, REC_SIZE; cbn; lia | unfold OFF_REFUSE, OFF_CALLS; cbn; lia | exact Vr]|].
      split; [apply HA0; [unfold OFF_CODE; lia | unfold OFF_CODE, REC_SIZE; cbn; lia | unfold OFF_CODE, OFF_CALLS; cbn; lia | exact Vc]|].
      split; [apply HA0; [unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia | unfold OFF_NREPLIES, OFF_ANSWER; lia | exact Vn]|].
      split; [apply HA0; [unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; cbn; lia | unfold OFF_STATE, OFF_ANSWER; lia | exact Vs]|].
      split; [apply HA0; [unfold OFF_HOST; lia | unfold OFF_HOST, REC_SIZE; cbn; lia | unfold OFF_HOST, OFF_ANSWER; lia | exact Vh]|].
      exact Rg. }
    { unfold ag1_own. cbn [lay_blocks l_calls l_spill l_answer l_reply] in *.
      assert (Elay : lay_blocks (RLay (lc ++ [[(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)) =
        concat lc ++ (p, n) :: l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))
        by (unfold lay_blocks; cbn [l_calls l_spill l_answer l_reply]; rewrite concat_app; cbn [concat]; rewrite ?app_nil_r; rewrite <- app_assoc; reflexivity).
      assert (Eold : lay_blocks Q = concat lc ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))
        by (unfold lay_blocks; rewrite HlcQ, concat_snoc_nil; reflexivity).
      rewrite Elay. rewrite Eold in HND, Hown.
      split.
      - rewrite map_app in HND |- *. cbn [map]. apply NoDup_ListNoDup in HND. apply NoDup_ListNoDup.
        apply spa_nodup_insert; [exact HND|].
        intros Hin. apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as (pn & Hpe & Hpn).
        * refine (proj2 (proj2 (HlQ pn _)) Hpe). rewrite Eold. apply in_or_app. left. exact Hpn.
        * refine (proj2 (proj2 (HlQ pn _)) Hpe). rewrite Eold. apply in_or_app. right. exact Hpn.
      - intros pn Hpn. apply in_app_or in Hpn as [Hpn | [<- | Hpn]].
        + apply Hown. apply in_or_app. left. exact Hpn.
        + split; assumption.
        + apply Hown. apply in_or_app. right. exact Hpn. }
  + intros pn. rewrite in_app_iff. cbn [In].
    unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
    rewrite HOQ, Hlay. rewrite !in_app_iff. cbn [In]. tauto.
- (* the spill slot *)
  replace (Nat.ltb (length (r_calls R)) 16) with false in * by (symmetry; apply Nat.ltb_ge; exact Hge).
  cbn [r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host set_spill] in *.
  pose proof (acall_at_nil_args _ _ _ _ _ Hspill) as HsQ.
  exists (RLay (l_calls Q) [(p, n)] (l_answer Q) (l_reply Q)).
  assert (Hlay : forall pn, In pn (lay_blocks Q) <-> In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
  { intros pn. unfold lay_blocks. rewrite HsQ. reflexivity. }
  split.
  + unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
    split.
    { unfold ag1_calls. cbn [r_calls r_spill set_spill l_calls l_spill].
      split; [exact Hlen|]. split; [exact HlenQ|].
      split.
      { apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_NCALLS) 4 (A_G_REC + OFF_NCALLS) 4); [exact Hnc | | lia | cbn; lia].
        intros i Hi. apply Hgr; [unfold OFF_NCALLS, REC_SIZE; lia|]. subst c. unfold OFF_NCALLS, A_G_REC, A_REC_SPILL, CALL_OFF_NARGS, CALL_OFF_ARGS. lia. }
      split.
      { intros i cl P Hci HPi. destruct (Hcalls i cl P Hci HPi) as [HCi HFi]. split; [|exact HFi].
        assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hci; discriminate).
        apply (acall_at_agree bl bl' rd rd'); [exact HCi | |].
        - intros j Hj. apply Hgr; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
          subst c. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. nia.
        - intros pn Hpn. destruct (HlQ pn) as (H1 & H2 & _); [|split; assumption].
          apply Hlay. apply in_or_app. left. exact (In_concat_nth _ i P pn HPi Hpn). }
      split; [|constructor; [cbn; lia | constructor]].
      rewrite <- Hc. apply (spa_acall_one bl bl' rd rd' c REC_PIN_ACCEPT x p).
      - rewrite Hc, <- HsQ. exact Hspill.
      - intros i Hi. apply Hsp; [subst c; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *; lia|].
        unfold CALL_OFF_NARGS in *. lia.
      - exact Hna.
      - exact Harg.
      - exact Hp0.
      - exact Hpin.
      - exact Hlx.
      - exact Hstr. }
    split.
    { cbn [r_answer set_spill l_answer]. unfold aanswer_at in *.
      destruct (r_answer R) as [xa|], (l_answer Q) as [pa|] eqn:EA; try contradiction.
      - destruct HANS as (V & Hnz & Hin & Hl & Hs & Hlx').
        assert (Hpa : In pa (lay_blocks Q)) by (apply Hlay; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        destruct (HlQ pa Hpa) as (Hin' & Hgp & _).
        split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact V | | lia | cbn; lia]|].
        { intros i Hi. apply Hgr; [unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia|].
          subst c. unfold A_G_REC, A_REC_SPILL, OFF_ANSWER, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia. }
        split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hl|]. split; [|exact Hlx'].
        apply (astr_atR_agree_in rd rd' (fst pa) (snd pa)); [exact Hs | exact Hgp | lia | lia].
      - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) 8); [exact HANS | | lia | cbn; lia].
        intros i Hi. apply Hgr; [unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia|].
        subst c. unfold A_G_REC, A_REC_SPILL, OFF_ANSWER, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia. }
    split.
    { cbn [r_reply set_spill l_reply]. unfold areply_at in *.
      destruct (r_reply R) as [xr|], (l_reply Q) as [pr|] eqn:ER; try contradiction.
      - destruct HREP as (V1 & V2 & Hnz & Hne & Hin & Hl & Hb & Hlx').
        assert (Hpr : In pr (lay_blocks Q)) by (apply Hlay; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
        destruct (HlQ pr Hpr) as (Hin' & Hgp & _).
        split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V1 | | lia | cbn; lia]|].
        { intros i Hi. apply Hgr; [unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia|].
          subst c. unfold A_G_REC, A_REC_SPILL, OFF_REPLY, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia. }
        split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); [exact V2 | | unfold OFF_REPLY_SIZE, OFF_REPLY; lia | unfold OFF_REPLY_SIZE, OFF_REPLY; cbn; lia]|].
        { intros i Hi. apply Hgr; [unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia|].
          subst c. unfold A_G_REC, A_REC_SPILL, OFF_REPLY, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia. }
        split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hl|]. split; [|exact Hlx'].
        apply (abytes_atR_agree_in rd rd' (fst pr) (snd pr)); [exact Hb | exact Hgp | lia | lia].
      - destruct HREP as [V1 V2].
        split; apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_REPLY) 16); try first [exact V1 | exact V2];
          try (unfold OFF_REPLY_SIZE, OFF_REPLY; cbn; lia);
          intros i Hi; apply Hgr; (try (unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia));
          subst c; unfold A_G_REC, A_REC_SPILL, OFF_REPLY, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
    split.
    { destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rg). unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_spill].
      assert (HA0 : forall o w v, 0 <= o -> o + Z.of_nat w <= REC_SIZE ->
        aval_mem rd (A_G_REC + o) w v -> aval_mem rd' (A_G_REC + o) w v).
      { intros o w v Ho Hw Hv. apply (aval_mem_agree_in rd rd' (A_G_REC + o) (Z.of_nat w)); [exact Hv | | lia | lia].
        intros i Hi. apply Hgr; [unfold REC_SIZE in *; lia|].
        subst c. unfold A_G_REC, A_REC_SPILL, CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SIZE in *. lia. }
      split; [apply HA0; [unfold OFF_REFUSE; lia | unfold OFF_REFUSE, REC_SIZE; cbn; lia | exact Vr]|].
      split; [apply HA0; [unfold OFF_CODE; lia | unfold OFF_CODE, REC_SIZE; cbn; lia | exact Vc]|].
      split; [apply HA0; [unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia | exact Vn]|].
      split; [apply HA0; [unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; cbn; lia | exact Vs]|].
      split; [apply HA0; [unfold OFF_HOST; lia | unfold OFF_HOST, REC_SIZE; cbn; lia | exact Vh]|].
      exact Rg. }
    { unfold ag1_own. cbn [lay_blocks l_calls l_spill l_answer l_reply] in *.
      assert (Elay : lay_blocks (RLay (l_calls Q) [(p, n)] (l_answer Q) (l_reply Q)) =
        concat (l_calls Q) ++ (p, n) :: oblk (l_answer Q) ++ oblk (l_reply Q)) by reflexivity.
      assert (Eold : lay_blocks Q = concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))
        by (unfold lay_blocks; rewrite HsQ; reflexivity).
      rewrite Elay. rewrite Eold in HND, Hown.
      split.
      - rewrite map_app in HND |- *. cbn [map]. apply NoDup_ListNoDup in HND. apply NoDup_ListNoDup.
        apply spa_nodup_insert; [exact HND|].
        intros Hin. apply in_app_or in Hin as [Hin | Hin]; apply in_map_iff in Hin as (pn & Hpe & Hpn).
        * refine (proj2 (proj2 (HlQ pn _)) Hpe). rewrite Eold. apply in_or_app. left. exact Hpn.
        * refine (proj2 (proj2 (HlQ pn _)) Hpe). rewrite Eold. apply in_or_app. right. exact Hpn.
      - intros pn Hpn. apply in_app_or in Hpn as [Hpn | [<- | Hpn]].
        + apply Hown. apply in_or_app. left. exact Hpn.
        + split; assumption.
        + apply Hown. apply in_or_app. right. exact Hpn. }
  + intros pn. rewrite in_app_iff. cbn [In].
    unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    rewrite HOQ, Hlay. rewrite !in_app_iff. cbn [In]. tauto.
Qed.
End e.
