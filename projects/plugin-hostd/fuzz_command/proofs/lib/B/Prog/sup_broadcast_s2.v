(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder facts of the sup_broadcast walk on fuzz_command.asan-ubsan, over
   readers and block lists only, made from a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast_s2.v at a5a5ff08765): every
   block the representation names is a live block of at least one byte, the old answer g_rec.answer holds, and the
   block bookkeeping of the call's post-condition. On B the recorder after record() is record_c.v's post
   (rec_repA (rec_record R fn []) O' with O' = O less the freed F) and after arg_line RecBridge.v's rec_bridge_add
   ((p, n) :: O'), so the A walk's sb_rep_slot / sb_rep_spill are not needed; the block bookkeeping is the A walk's
   sb_post_blocks in those forms, with the conclusions in the B statement's forms (sup_broadcast_c.v:117, :124). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRep RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every block of the recorder's layout has at least one byte (A: sup_broadcast_s2.v lay_blocks_pos) *)
Lemma sbb_lay_blocks_pos : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> 0 < snd pn.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _) Hin.
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  destruct HC as (C1 & C2 & _ & C4 & _).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
  destruct (Hargs k s pn Hs Hk) as (_ & _ & _ & A4 & _). lia.
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
    destruct (Hargs k s pn Hs Hk) as (_ & _ & _ & A4 & _). lia.
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in HA. destruct (l_answer Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R); [|contradiction]. destruct HA as (_ & _ & _ & A4 & _). lia.
    * unfold areply_at in HR. destruct (l_reply Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R) as [x|]; [|contradiction]. destruct HR as (_ & _ & _ & A4 & _ & A6 & _).
      destruct x as [|b x]; [contradiction|]. cbn [length] in A6. lia.
Qed.

(* decidable equality of blocks (A: sup_broadcast_s2.v zz_eq_dec) *)
Lemma sbb_zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof.
intros [a b] [c d]. destruct (Z.eq_dec a c) as [Ea | Na].
- destruct (Z.eq_dec b d) as [Eb | Nb].
  + left. subst. reflexivity.
  + right. intros E. injection E as _ E. exact (Nb E).
- right. intros E. injection E as E _. exact (Na E).
Qed.

(* two blocks of a list without repeated starts that have the same start are the same block *)
Lemma sbb_nodup_fst_same : forall (l : list (Z * Z)) x y, List.NoDup (map fst l) -> In x l -> In y l -> fst x = fst y -> x = y.
Proof.
intros l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct Hx as [<- | Hx], Hy as [<- | Hy].
- reflexivity.
- exfalso. apply NI. rewrite E. apply List.in_map. exact Hy.
- exfalso. apply NI. rewrite <- E. apply List.in_map. exact Hx.
- exact (IH x y ND Hx Hy E).
Qed.

Lemma sbb_nodup_fst_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (map fst (l1 ++ l2)) -> In x l1 -> In x l2 -> False.
Proof.
intros l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn [app map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct H1 as [<- | H1].
- apply NI. apply List.in_map. apply in_or_app. right. exact H2.
- exact (IH l2 x ND H1 H2).
Qed.

(* the block bookkeeping of the post-condition. bl0: the blocks at the entry, O the recorder's; record() frees F
   (none in the table arm) leaving bl1, and the recorder then owns O1 = O less F (record_c.v:112-117); arg_line adds
   (p, k) giving bl2 and the recorder owns (p, k) :: O1 (RecBridge.v rec_bridge_add); answer frees the old answer
   (start old) and adds its two copies (p1, n) and (p2, n) giving bl3, and the recorder owns O3 (answer_c.v:146-151).
   The conclusions are the B statement's (sup_broadcast_c.v:117, :120-121, :124-125) *)
Lemma sbb_post_blocks : forall (bl0 bl1 bl2 bl3 O F O1 O3 : list (Z * Z)) (p k p1 p2 n old : Z),
List.NoDup (map fst bl0) -> List.NoDup (map fst bl2) -> List.NoDup (map fst bl3) ->
(forall pn, In pn O -> In pn bl0) ->
Permutation bl0 (bl1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
(forall pn, In pn O1 -> In pn bl1) ->
Permutation bl2 ((p, k) :: bl1) -> Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl1 -> 0 < k ->
(forall pn, In pn bl3 <-> (In pn bl2 /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn bl2 -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
(forall pn, In pn O3 <-> (In pn ((p, k) :: O1) /\ fst pn <> old) \/ pn = (p1, n)) ->
(old = 0 \/ exists ko, In (old, ko) ((p, k) :: O1)) ->
(forall pn, In pn bl0 -> fst pn <> 0) ->
(forall pn, In pn O3 -> In pn bl3) ->
(forall pn, In pn O3 -> In pn bl0 -> In pn O) /\
(forall pn, In pn bl3 -> (In pn bl0 /\ ~ In pn O) \/ In pn O3 \/ pn = (p2, n)) /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl3) /\
In (p2, n) bl3 /\ (In (p2, n) bl0 -> In (p2, n) O) /\
~ In p2 (map fst O3).
Proof.
intros bl0 bl1 bl2 bl3 O F O1 O3 p k p1 p2 n old ND0 ND2 ND3 HO0 HP0 HFO HO1 HM1 HP2 HAp Hk
  H3 Hn Hp12 HO' Hold Hnz HO'3.
assert (HMO : forall pn, In pn O1 -> In pn O) by (intros pn H; exact (proj1 (proj1 (HO1 pn) H))).
assert (HOMF : forall pn, In pn O -> In pn O1 \/ In pn F).
{ intros pn H. destruct (in_dec sbb_zz_eq_dec pn F) as [HF | HF]; [right; exact HF | left; apply HO1; split; assumption]. }
assert (Hb0 : forall pn, In pn bl0 -> In pn bl1 \/ In pn F).
{ intros pn H. apply in_app_or. exact (Permutation_in _ HP0 H). }
assert (Hb1 : forall pn, In pn bl1 -> In pn bl0).
{ intros pn H. apply (Permutation_in _ (Permutation_sym HP0)). apply in_or_app. left. exact H. }
assert (Hb12 : forall pn, In pn bl1 -> In pn bl2).
{ intros pn H. apply (Permutation_in _ (Permutation_sym HP2)). right. exact H. }
assert (HM2 : forall pn, In pn O1 -> In pn bl2) by (intros pn H; exact (Hb12 pn (HM1 pn H))).
assert (Hpk2 : In (p, k) bl2).
{ apply (Permutation_in _ (Permutation_sym HP2)). left. reflexivity. }
assert (Hb2 : forall pn, In pn bl2 -> pn = (p, k) \/ In pn bl1).
{ intros pn H. apply (Permutation_in _ HP2) in H. destruct H as [<- | H]; [left; reflexivity | right; exact H]. }
assert (ND01 : List.NoDup (map fst (bl1 ++ F))).
{ eapply Permutation_NoDup; [apply Permutation_map; exact HP0 | exact ND0]. }
assert (Hdisj : forall pn, In pn bl1 -> In pn F -> False).
{ intros pn H1 H2. exact (sbb_nodup_fst_disj bl1 F pn ND01 H1 H2). }
assert (Hpk1 : ~ In (p, k) bl1).
{ intros H. rewrite List.Forall_forall in HAp. specialize (HAp _ H). cbn [fst snd] in HAp. unfold iv_apart in HAp. lia. }
assert (HOx : forall pn, In pn bl0 -> fst pn = old -> In pn O).
{ intros pn H E. destruct Hold as [Ho | (ko & Hko)].
  - exfalso. exact (Hnz pn H (eq_trans E Ho)).
  - destruct Hko as [Epk | Hko].
    + injection Epk as Ep _. destruct (Hb0 pn H) as [H1 | HF]; [exfalso | exact (HFO pn HF)].
      assert (Epn : pn = (p, k))
        by (apply (sbb_nodup_fst_same bl2); [exact ND2 | exact (Hb12 pn H1) | exact Hpk2 | cbn [fst]; congruence]).
      subst pn. exact (Hpk1 H1).
    + assert (Hko0 : In (old, ko) bl0) by (apply HO0; apply HMO; exact Hko).
      rewrite (sbb_nodup_fst_same bl0 pn (old, ko) ND0 H Hko0 E). apply HMO. exact Hko. }
assert (D1 : forall pn, In pn O3 -> In pn O \/ ~ In pn bl0).
{ intros pn H. apply HO' in H. destruct H as [(H & _) | ->].
  - destruct H as [<- | H].
    + destruct (in_dec sbb_zz_eq_dec (p, k) bl0) as [Hin | Hnin]; [|right; exact Hnin].
      left. destruct (Hb0 _ Hin) as [H1 | HF]; [exfalso; exact (Hpk1 H1) | exact (HFO _ HF)].
    + left. apply HMO. exact H.
  - destruct (in_dec sbb_zz_eq_dec (p1, n) bl0) as [Hin | Hnin]; [|right; exact Hnin].
    left. destruct (Z.eq_dec p1 old) as [E | E]; [exact (HOx _ Hin E)|].
    destruct (Hb0 _ Hin) as [H1 | HF]; [exfalso; exact (proj1 (Hn _ (Hb12 _ H1) E) eq_refl) | exact (HFO _ HF)]. }
assert (D5 : forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)).
{ intros pn H HnO Epn. destruct (Hb0 _ H) as [H1 | HF]; [|exact (HnO (HFO _ HF))].
  assert (E : fst pn <> old) by (intros E; exact (HnO (HOx pn H E))).
  exact (proj2 (Hn pn (Hb12 _ H1) E) Epn). }
split.
{ intros pn H Hb. destruct (D1 pn H) as [HO | Hnb]; [exact HO | exfalso; exact (Hnb Hb)]. }
split.
{ intros pn H. apply H3 in H. destruct H as [(H & Hne) | [-> | ->]].
  - apply Hb2 in H as [-> | H].
    + right. left. apply HO'. left. split; [left; reflexivity | exact Hne].
    + destruct (in_dec sbb_zz_eq_dec pn O) as [HinO | HnO].
      * apply HOMF in HinO as [HM | HF].
        -- right. left. apply HO'. left. split; [right; exact HM | exact Hne].
        -- exfalso. exact (Hdisj pn H HF).
      * left. split; [apply Hb1; exact H | exact HnO].
  - right. left. apply HO'. right. reflexivity.
  - right. right. reflexivity. }
split.
{ intros pn H HnO. apply H3. left. split.
  - destruct (Hb0 pn H) as [H1 | HF]; [exact (Hb12 pn H1) | exfalso; exact (HnO (HFO pn HF))].
  - intros E. exact (HnO (HOx pn H E)). }
split; [apply H3; right; right; reflexivity|].
split.
{ intros H. destruct (in_dec sbb_zz_eq_dec (p2, n) O) as [HO | HnO]; [exact HO|].
  exfalso. exact (D5 (p2, n) H HnO eq_refl). }
intros H. apply List.in_map_iff in H as (pn & Ep & Hpn).
assert (E : pn = (p2, n)).
{ apply (sbb_nodup_fst_same bl3); [exact ND3 | exact (HO'3 pn Hpn) | apply H3; right; right; reflexivity | exact Ep]. }
subst pn. apply HO' in Hpn as [(Hm & Hne) | E].
- cbn [fst] in Hne. destruct Hm as [E | Hm].
  + injection E as Epp Ekk. subst p k. exact (proj2 (Hn _ Hpk2 Hne) eq_refl).
  + exact (proj2 (Hn _ (HM2 _ Hm) Hne) eq_refl).
- exact (Hp12 (eq_sym (f_equal fst E))).
Qed.

Section d.
Variable B : asyms.

(* every block the representation names is a live block of at least one byte *)
Lemma sbb_rep_pos : forall ly S (rd : reader) R O pn, rec_repA B ly S rd R O -> In pn O -> 0 < snd pn /\ In pn (ablocks B ly S).
Proof.
intros ly S rd R O pn (Q & HA & HO) Hin. apply HO in Hin. split.
- exact (sbb_lay_blocks_pos _ _ _ _ _ _ _ HA Hin).
- exact (lay_blocks_in _ _ _ _ _ _ HA pn Hin).
Qed.

(* the old answer: the value g_rec.answer holds, 0 or the start of one of the recorder's blocks *)
Lemma sbb_rep_old : forall ly S (rd : reader) R O, rec_repA B ly S rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists ko, In (old, ko) O).
Proof.
intros ly S rd R O (Q & HA & HO).
pose proof HA as (_ & _ & _ & _ & HAn & _).
unfold aanswer_at in HAn. destruct (r_answer R) as [x|] eqn:Ea, (l_answer Q) as [[q m]|] eqn:Eq; try contradiction.
- exists q. split; [exact (proj1 HAn)|]. right. exists m. apply HO.
  unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Eq. left. reflexivity.
- exists 0. split; [exact HAn | left; reflexivity].
Qed.
End d.
