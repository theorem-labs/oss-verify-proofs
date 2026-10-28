(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Record oent := OE { oe_a : Z; oe_k : Z; oe_kn : Z; oe_ks : list byte; oe_v : Z }.
Definition ohd (es : list oent) : Z := match es with [] => 0 | e :: _ => oe_a e end.

Lemma ohd_skipn_map : forall (A : Type) (f : A -> oent) (l : list A) j,
ohd (skipn j (map f l)) = match nth_error l j with Some x => oe_a (f x) | None => 0 end.
Proof. intros A f l. induction l as [|x l IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
Lemma ohd_skipn : forall l n, ohd (skipn n l) = match nth_error l n with Some x => oe_a x | None => 0 end.
Proof. intros l. induction l as [|x l IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).
Notation jvalx := (jval segs fn).

Definition otab (m : word -> option byte) (BS : list blk) (t : Z) (es : list oent) : Prop :=
inside_blocks BS t 16 /\ rw_cells m (t + 8) [C8 (wz (ohd es))] /\
forall j e, nth_error es j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ inside_blocks BS (oe_a e) 32 /\
(exists pad : word, rw_cells m (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
cstr segs m (oe_k e) (oe_kn e) (oe_ks e) /\ In (oe_k e, oe_kn e) BS /\ oe_kn e <= 2^31.

#[using="Type"] Lemma otab_agree : forall m m' BS BS' t es,
otab m BS t es -> agree_on segs BS' m m' -> incl BS BS' -> otab m' BS t es.
Proof.
intros m m' BS BS' t es (IB & HD & ENT) AG INCL. split; [exact IB|]. split.
- eapply (rw_cells_agree segs); [exact HD | exact AG |]. destruct IB as (a & k & Hin & H1 & H2). exists a, k. split; [apply INCL; exact Hin | cbn; lia].
- intros j e Hj. destruct (ENT j e Hj) as (A0 & AL8 & IBe & (pad & RW) & CS & INk & KN).
split; [exact A0|]. split; [exact AL8|]. split; [exact IBe|]. split; [| split; [| split; [exact INk | exact KN]]].
+ exists pad. eapply (rw_cells_agree segs); [exact RW | exact AG | eapply inside_blocks_incl; [exact IBe | exact INCL]].
+ eapply (cstr_agree segs); [exact CS | exact AG | apply INCL; exact INk | destruct CS as (L & _); lia].
Qed.

#[using="Type"] Lemma lhtab_otab : forall m TBS t kvs,
lhtab2 segs fn m TBS t kvs -> (forall a n, In (a, n) TBS -> 0 < a /\ a mod 16 = 0) ->
exists es, otab m TBS t es /\ kvs = map (fun e => (oe_k e, oe_v e)) es.
Proof.
intros m TBS t kvs (tbl & size & es & svs & Hkvs & E & OPEN) POS.
destruct OPEN as (HDR & SL & (LK1 & LK2 & ND & LK4) & KEYS & _ & _ & Hlen).
set (f := fun e : lent => OE (ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (le_ks e) (le_v e)).
exists (map f es). split; [| rewrite Hkvs, map_map; apply map_ext; intros e; reflexivity].
assert (Htbl : 0 < tbl /\ tbl mod 16 = 0) by (apply (POS tbl (40 * size)); rewrite E; right; left; reflexivity).
split; [| split].
- exists t, 56. split; [rewrite E; left; reflexivity | lia].
- unfold lh_hdrf in HDR.
apply (proj1 (rw_cells_app segs m t [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 (Z.of_nat (length es)))] _)) in HDR as [_ H].
apply (proj1 (rw_cells_app segs m _ [C8 (Z_to_bv 64 (hd_of tbl es))] _)) in H as [H _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
replace (ohd (map f es)) with (hd_of tbl es) by (destruct es; reflexivity). exact H.
- intros j e Hj. rewrite nth_error_map in Hj. destruct (nth_error es j) as [e0|] eqn:Hj0; [| discriminate Hj]. cbn in Hj. injection Hj as <-.
cbn [oe_a oe_k oe_kn oe_ks oe_v f].
assert (Hin : In e0 es) by (eapply nth_error_In; exact Hj0).
destruct (LK1 j e0 Hj0) as (sv & Hsv & Ek & Ekc & Ev & Enx & Epv).
pose proof (nth_error_lt _ _ _ Hsv) as Hix.
destruct (LK4 e0 Hin) as (Hk0 & _ & Hkn & _).
split; [unfold ent_addr; lia|]. split.
{ unfold ent_addr. destruct Htbl as [_ Hal]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq].
replace (tbl + 40 * Z.of_nat (le_ix e0)) with ((q * 2 + 5 * Z.of_nat (le_ix e0)) * 8) by lia. apply Z.mod_mul. lia. }
split.
{ exists tbl, (40 * size). split; [rewrite E; right; left; reflexivity | unfold ent_addr; rewrite <- Hlen; split; [lia | nia]]. }
split.
{ exists (Z_to_bv 64 (sv_pad sv)). pose proof (SL (le_ix e0) sv Hsv) as H. unfold slot_cells in H.
rewrite Ek, Ekc, Ev, Enx in H.
apply (proj1 (rw_cells_app segs m _ [C8 (wz (le_k e0)); C4 (wz 0); C4 (wz (sv_pad sv)); C8 (wz (le_v e0)); C8 (wz (nx_of tbl es j))] [C8 (wz (sv_pv sv))])) in H as [H _].
unfold nx_of in H.
replace (ohd (skipn (S j) (map f es))) with (match nth_error es (S j) with Some e' => ent_addr tbl (le_ix e') | None => 0 end); [exact H|].
rewrite (ohd_skipn_map lent f es (S j)). destruct (nth_error es (S j)); reflexivity. }
split; [exact (proj1 (Forall_forall _ _) KEYS e0 Hin)|].
split; [| exact Hkn].
rewrite E. right. right. rewrite in_map_iff. exists e0. split; [reflexivity | exact Hin].
Qed.

#[using="Type"] Lemma lhtab_tbl_in : forall m TBS t kvs, lhtab2 segs fn m TBS t kvs -> In (t, 56) TBS.
Proof. intros m TBS t kvs (tbl & size & es & svs & _ & E & _). rewrite E. left. reflexivity. Qed.

#[using="Type"] Lemma kids_okv_nth : forall m kids kvs KBS i k,
kids_okv segs fn m kids kvs KBS -> nth_error kids i = Some k ->
exists kk v bs, nth_error kvs i = Some (kk, v) /\ nth_error KBS i = Some bs /\
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros kvs KBS i k KOK Hn; [destruct i; discriminate Hn|].
destruct kvs as [|[kk0 v0] kvs]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
rewrite kids_okv_cons in KOK. destruct KOK as [H0 KOK].
destruct i as [|i]; cbn in Hn |- *.
- injection Hn as ->. exists kk0, v0, bs0. auto.
- eapply IH; eassumption.
Qed.

Definition kid_ok (m : word -> option byte) (k : option jshape) (v : Z) (bs : list blk) : Prop :=
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end.

Definition obj_view (kids : list (option jshape)) (m : word -> option byte) (BS : list blk) (p rc : Z)
(pb0 : Z) (PBS : list blk) (t : Z) (TBS : list blk) (es : list oent) (KBS : list (list blk)) : Prop :=
BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS /\
opt_pbuf segs m PBS pb0 /\
rw_cells m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb0 0 0 ++ [C8 (wz t)]) /\
lhtab2 segs fn m TBS t (map (fun e => (oe_k e, oe_v e)) es) /\
otab m TBS t es /\
length es = length kids /\ length KBS = length kids /\
(forall j k, nth_error kids j = Some k -> exists e bs, nth_error es j = Some e /\ nth_error KBS j = Some bs /\ kid_ok m k (oe_v e) bs).

#[using="Type"] Lemma kids_okv_of_nth : forall m kids (es : list oent) KBS,
length es = length kids -> length KBS = length kids ->
(forall j k, nth_error kids j = Some k -> exists e bs, nth_error es j = Some e /\ nth_error KBS j = Some bs /\ kid_ok m k (oe_v e) bs) ->
kids_okv segs fn m kids (map (fun e => (oe_k e, oe_v e)) es) KBS.
Proof.
intros m kids. induction kids as [|k kids IH]; intros [|e es] [|bs KBS] LE LK H; cbn in LE, LK; try lia.
- reflexivity.
- cbn [map]. rewrite kids_okv_cons. split.
+ destruct (H 0%nat k eq_refl) as (e' & bs' & E1 & E2 & OK). cbn in E1, E2. injection E1 as <-. injection E2 as <-. exact OK.
+ apply IH; [lia | lia |]. intros j k' Hj. exact (H (S j) k' Hj).
Qed.

#[using="Type"] Lemma jval_obj_view : forall kids m BS p rc,
jvalx (Sobj kids) m BS p rc -> (forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0) ->
exists pb0 PBS t TBS es KBS, obj_view kids m BS p rc pb0 PBS t TBS es KBS.
Proof.
intros kids m BS p rc J POS.
destruct (proj1 (jval_split segs fn (Sobj kids) m BS p rc) J) as (pb0 & PBS & REST & EBS & OPB & JN).
destruct JN as (t & TBS & kvs & KBS & ER & HDR & LH & L1 & L2 & KOK).
destruct (lhtab_otab m TBS t kvs LH) as (es & OT & Ekvs).
{ intros a n Hin. apply (POS a n). rewrite EBS, ER. apply in_or_app. left. right. apply in_or_app. left. exact Hin. }
subst kvs. exists pb0, PBS, t, TBS, es, KBS.
split; [rewrite EBS, ER; reflexivity|]. split; [exact OPB|]. split; [exact HDR|]. split; [exact LH|]. split; [exact OT|].
rewrite length_map in L1. split; [exact L1|]. split; [exact L2|].
intros j k Hj. destruct (kids_okv_nth m kids _ KBS j k KOK Hj) as (kk & v & bs & E1 & E2 & OK).
rewrite nth_error_map in E1. destruct (nth_error es j) as [e|] eqn:He; [| discriminate E1]. cbn in E1. injection E1 as E1a E1b.
exists e, bs. split; [reflexivity|]. split; [exact E2|]. unfold kid_ok. rewrite E1b. exact OK.
Qed.

#[using="Type"] Lemma obj_view_jval : forall kids m BS p rc pb0 PBS t TBS es KBS,
obj_view kids m BS p rc pb0 PBS t TBS es KBS -> jvalx (Sobj kids) m BS p rc.
Proof.
intros kids m BS p rc pb0 PBS t TBS es KBS (EBS & OPB & HDR & LH & OT & LE & LK & KIDS).
apply (proj2 (jval_split segs fn (Sobj kids) m BS p rc)). exists pb0, PBS, ((p, 48) :: TBS ++ concat KBS).
split; [exact EBS|]. split; [exact OPB|]. cbn [jnode]. exists t, TBS, (map (fun e => (oe_k e, oe_v e)) es), KBS.
split; [reflexivity|]. split; [exact HDR|]. split; [exact LH|]. rewrite length_map. split; [exact LE|]. split; [exact LK|].
apply kids_okv_of_nth; assumption.
Qed.

Definition obj_others (p : Z) (TBS : list blk) (KBS : list (list blk)) (j : nat) (PBS : list blk) : list blk :=
((p, 48) :: TBS ++ concat (lupd KBS j [])) ++ PBS.

#[using="Type"] Lemma obj_view_agree : forall kids m m' BS p rc pb0 PBS t TBS es KBS,
obj_view kids m BS p rc pb0 PBS t TBS es KBS -> agree_on segs BS m m' ->
obj_view kids m' BS p rc pb0 PBS t TBS es KBS.
Proof.
intros kids m m' BS p rc pb0 PBS t TBS es KBS (EBS & OPB & HDR & LH & OT & LE & LK & KIDS) AG.
split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; rewrite EBS; apply in_or_app; right; exact Hb]. }
split.
{ eapply rw_cells_agree; [exact HDR | exact AG | exists p, 48; split; [rewrite EBS; apply in_or_app; left; left; reflexivity | cbn; lia]]. }
split.
{ eapply lhtab2_agree; [exact LH | exact AG | intros b Hb; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
split.
{ eapply otab_agree; [exact OT | exact AG | intros b Hb; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
split; [exact LE|]. split; [exact LK|].
intros i k Hi. destruct (KIDS i k Hi) as (ei & bsi & E1 & E2 & OK). exists ei, bsi. split; [exact E1|]. split; [exact E2|].
destruct k as [si|]; cbn [kid_ok] in OK |- *; [| exact OK].
destruct OK as [NZ Ji]. split; [exact NZ|]. eapply jval_agree; [exact Ji | exact AG |].
intros b Hb. rewrite EBS. apply in_or_app. left. right. apply in_or_app. right. apply in_concat. exists bsi.
split; [eapply nth_error_In; exact E2 | exact Hb].
Qed.

#[using="Type"] Lemma obj_view_head : forall kids m BS p rc pb0 PBS t TBS es KBS,
obj_view kids m BS p rc pb0 PBS t TBS es KBS -> rw_cells m (t + 8) [C8 (wz (ohd es))].
Proof. intros until KBS. intros (_ & _ & _ & _ & (_ & HD & _) & _). exact HD. Qed.

#[using="Type"] Lemma obj_view_tbl : forall kids m BS p rc pb0 PBS t TBS es KBS,
obj_view kids m BS p rc pb0 PBS t TBS es KBS -> In (t, 56) TBS /\ In (t, 56) BS.
Proof.
intros until KBS. intros (EBS & _ & _ & LH & _). pose proof (lhtab_tbl_in _ _ _ _ LH) as H.
split; [exact H|]. rewrite EBS. apply in_or_app. left. right. apply in_or_app. left. exact H.
Qed.
#[using="Type"] Lemma obj_view_entry : forall kids m BS p rc pb0 PBS t TBS es KBS j e,
obj_view kids m BS p rc pb0 PBS t TBS es KBS -> nth_error es j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ inside_blocks TBS (oe_a e) 32 /\
(exists pad : word, rw_cells m (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
exists k bs, nth_error kids j = Some k /\ nth_error KBS j = Some bs /\ kid_ok m k (oe_v e) bs.
Proof.
intros until e. intros (EBS & _ & _ & _ & (_ & _ & ENT) & LE & LK & KIDS) He.
destruct (ENT j e He) as (A0 & AL8 & IB & RW & _). split; [exact A0|]. split; [exact AL8|]. split; [exact IB|]. split; [exact RW|].
destruct (nth_error kids j) as [k|] eqn:Hk.
- destruct (KIDS j k Hk) as (e' & bs & E1 & E2 & OK). rewrite He in E1. injection E1 as <-. exists k, bs. auto.
- exfalso. apply nth_error_None in Hk. pose proof (nth_error_Some_length He). lia.
Qed.
End WithSegs.
