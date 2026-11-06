(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Notation wz := (Z_to_bv 64) (only parsing).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition jtype (s : jshape) : Z :=
match s with
| Sbool => JT_BOOLEAN | Sdouble _ => JT_DOUBLE | Sint => JT_INT | Sstr _ => JT_STRING
| Sobj _ => JT_OBJECT | Sarr _ => JT_ARRAY
end.

#[using="Type"] Lemma jtype_range : forall s, 0 <= jtype s <= 6.
Proof. destruct s; cbn; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY; lia. Qed.

Fixpoint others (p : Z) (BS : list blk) : list blk :=
match BS with
| [] => []
| b :: BS' => if Z.eqb (blk_addr b) p then others p BS' else b :: others p BS'
end.

#[using="Type"] Lemma in_others_iff : forall p BS b, In b (others p BS) <-> In b BS /\ blk_addr b <> p.
Proof.
intros p BS b. induction BS as [|x BS IH]; cbn; [tauto|].
destruct (Z.eqb_spec (blk_addr x) p) as [E|NE]; cbn; rewrite IH; intuition (subst; auto; try congruence).
Qed.

#[using="Type"] Lemma in_others : forall p BS a n, In (a, n) BS -> a <> p -> In (a, n) (others p BS).
Proof. intros p BS a n H Hne. apply in_others_iff. split; [exact H | exact Hne]. Qed.

#[using="Type"] Lemma others_incl : forall p BS, incl (others p BS) BS.
Proof. intros p BS b Hb. apply in_others_iff in Hb as [Hb _]. exact Hb. Qed.

#[using="Type"] Lemma nodup_tail_ne : forall p n (TL : list blk) a k,
List.NoDup (map blk_addr ((p, n) :: TL)) -> In (a, k) TL -> a <> p.
Proof.
intros p n TL a k ND Hin ->. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. exact (in_map blk_addr _ _ Hin).
Qed.

#[using="Type"] Lemma nodup_map_app_comm : forall (X Y : list blk), List.NoDup (map blk_addr (X ++ Y)) -> List.NoDup (map blk_addr (Y ++ X)).
Proof.
intros X Y ND. rewrite map_app in *. eapply (Permutation.Permutation_NoDup); [apply Permutation.Permutation_app_comm | exact ND].
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

#[using="Type"] Lemma incl_others_tail : forall p n TL PBS (bs : list blk),
List.NoDup (map blk_addr (((p, n) :: TL) ++ PBS)) ->
incl bs (TL ++ PBS) -> incl bs (others p (((p, n) :: TL) ++ PBS)).
Proof.
intros p n TL PBS bs ND Hi [a k] Hb. apply in_others.
- cbn. right. exact (Hi _ Hb).
- cbn [app] in ND. eapply (nodup_tail_ne p n (TL ++ PBS)); [exact ND | exact (Hi _ Hb)].
Qed.

#[using="Type"] Lemma jval_hdr : forall s m BS p rc,
jval segs fn s m BS p rc -> List.NoDup (map blk_addr BS) ->
exists n tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells (jtype s) rc tojs pb udel ud ++ rest)) = n /\ 48 <= n /\
rw_cells segs m p (jhdr_cells (jtype s) rc tojs pb udel ud ++ rest) /\
(forall m' rc',
rw_cells segs m' p (jhdr_cells (jtype s) rc' tojs pb udel ud ++ rest) ->
agree_on segs (others p BS) m m' ->
jval segs fn s m' BS p rc').
Proof.
intros s m BS p rc J ND.
destruct s as [|u| |h|kids|kids]; destruct J as (pb & PBS & REST & EBS & OPB & J).
-
destruct J as (b & junk & ER & H). subst REST BS.
exists 48, (fn_bool_to_json_string fn), pb, 0, 0, [C4 (wz b); CB 4 junk]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, [(p, 48)]. split; [reflexivity|]. split.
+ eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 48 [] PBS); [exact ND | intros x Hx; exact Hx]].
+ exists b, junk. split; [reflexivity | exact H'].
-
destruct u.
+ destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST BS.
exists 48, (fn_ud_to_json_string fn), pb, (fn_free_userdata fn), ud, [C8 bits]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, [(p, 48); (ud, udn)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 48 [(ud, udn)] PBS); [exact ND | intros x Hx; apply in_or_app; right; exact Hx]].
* exists bits, ud, udn, uds. split; [reflexivity|]. split; [exact HU|]. split; [exact H'|].
eapply cstr_agree; [exact HC | exact AG | | destruct HC as (HC1 & _); lia].
eapply (incl_others_tail p 48 [(ud, udn)] PBS); [exact ND | intros x Hx; exact Hx | cbn; left; reflexivity].
+ destruct J as (bits & ER & HS & H). subst REST BS.
exists 48, (fn_dbl_to_json_string fn), pb, 0, 0, [C8 bits]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, [(p, 48)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 48 [] PBS); [exact ND | intros x Hx; exact Hx]].
* exists bits. split; [reflexivity|]. split; [exact HS | exact H'].
-
destruct J as (cty & v & junk & ER & HC & H). subst REST BS.
exists 56, (fn_int_to_json_string fn), pb, 0, 0, [C4 (wz cty); CB 4 junk; C8 v]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, [(p, 56)]. split; [reflexivity|]. split.
+ eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 56 [] PBS); [exact ND | intros x Hx; exact Hx]].
+ exists cty, v, junk. split; [reflexivity|]. split; [exact HC | exact H'].
-
destruct h.
+ destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD). subst REST BS.
exists 56, (fn_str_to_json_string fn), pb, 0, 0, [C8 (wz len); C8 (wz pd)]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, [(p, 56); (pd, pdn)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 56 [(pd, pdn)] PBS); [exact ND | intros x Hx; apply in_or_app; right; exact Hx]].
* exists len, pd, pdn, str, junk2. split; [reflexivity|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split; [exact H'|].
eapply rw_cells_agree; [exact HD | exact AG |].
exists pd, pdn. split; [| destruct HD as [[Hwf' _] _]; cbn in Hwf'; cbn [cells_size csize]; lia].
eapply (incl_others_tail p 56 [(pd, pdn)] PBS); [exact ND | intros x Hx; exact Hx | cbn; left; reflexivity].
+ destruct J as (len & str & junk & ER & HL & HS & H). subst REST BS.
exists (str_objsize len), (fn_str_to_json_string fn), pb, 0, 0, [C8 (wz len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)]. cbn [jtype].
split; [left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells]; unfold str_objsize in *; lia|].
split; [unfold str_objsize; lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, [(p, str_objsize len)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p (str_objsize len) [] PBS); [exact ND | intros x Hx; exact Hx]].
* exists len, str, junk. split; [reflexivity|]. split; [exact HL|]. split; [exact HS | exact H'].
-
destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). subst REST BS.
exists 48, (fn_obj_to_json_string fn), pb, 0, 0, [C8 (wz t)]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, ((p, 48) :: TBS ++ concat KBS). split; [reflexivity|]. split.
+ eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 48 (TBS ++ concat KBS) PBS); [exact ND | intros x Hx; apply in_or_app; right; exact Hx]].
+ exists t, TBS, kvs, KBS. split; [reflexivity|]. split; [exact H'|]. split; [| split; [exact L1 | split; [exact L2 |]]].
* eapply lhtab2_agree; [exact HT | exact AG |].
eapply (incl_others_tail p 48 (TBS ++ concat KBS) PBS); [exact ND | intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx].
* assert (HiK : incl (concat KBS) (others p (((p, 48) :: TBS ++ concat KBS) ++ PBS))).
{ eapply (incl_others_tail p 48 (TBS ++ concat KBS) PBS); [exact ND | intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx]. }
clear H H' HT L1 L2 OPB ND.
set (OBS := others p _) in AG, HiK. clearbody OBS.
revert kvs KBS KIDS HiK. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS HiK; try exact KIDS.
cbn [concat] in HiK. destruct KIDS as [K1 K2]. split.
-- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
-- apply IH; [exact K2 | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
-
destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). subst REST BS.
exists 48, (fn_arr_to_json_string fn), pb, 0, 0, [C8 (wz a)]. cbn [jtype].
split; [left; reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact H|].
intros m' rc' H' AG. exists pb, PBS, ((p, 48) :: ABS ++ concat KBS). split; [reflexivity|]. split.
+ eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail p 48 (ABS ++ concat KBS) PBS); [exact ND | intros x Hx; apply in_or_app; right; exact Hx]].
+ exists a, ABS, ps, KBS. split; [reflexivity|]. split; [exact H'|]. split; [| split; [exact L1 | split; [exact L2 |]]].
* eapply alist_agree; [exact HA | exact AG |].
eapply (incl_others_tail p 48 (ABS ++ concat KBS) PBS); [exact ND | intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx].
* assert (HiK : incl (concat KBS) (others p (((p, 48) :: ABS ++ concat KBS) ++ PBS))).
{ eapply (incl_others_tail p 48 (ABS ++ concat KBS) PBS); [exact ND | intros x Hx; apply in_or_app; left; apply in_or_app; right; exact Hx]. }
clear H H' HA L1 L2 OPB ND.
set (OBS := others p _) in AG, HiK. clearbody OBS.
revert ps KBS KIDS HiK. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS HiK; try exact KIDS.
cbn [concat] in HiK. destruct KIDS as [K1 K2]. split.
-- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
-- apply IH; [exact K2 | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma agree_others_of_munch : forall p n BS W m m',
In (p, n) BS ->
(forall a k a' k', In (a, k) BS -> In (a', k') BS -> a <> a' -> a + k <= a' \/ a' + k' <= a) ->
(forall a k, In (a, k) BS -> 0 <= k) ->
munch W m m' -> wmono segs m m' ->
Forall (fun iv => p <= fst iv /\ snd iv <= p + n) W ->
agree_on segs (others p BS) m m'.
Proof.
intros p n BS W m m' Hp DISJ POS MU WM HW.
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. apply in_others_iff in Hin as [Hin NE]. cbn in NE.
pose proof (DISJ _ _ _ _ Hin Hp NE) as D. pose proof (POS _ _ Hin) as K0. pose proof (POS _ _ Hp) as N0.
clear - HW D K0 N0. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd] in H1. cbn [disjoint_from]. split; [lia | apply IH; exact HW].
Qed.

#[using="Type"] Lemma agree_others_gen : forall p BS W m m',
munch W m m' -> wmono segs m m' ->
(forall a k, In (a, k) BS -> a <> p -> disjoint_from W a k) ->
agree_on segs (others p BS) m m'.
Proof.
intros p BS W m m' MU WM HD. eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. apply in_others_iff in Hin as [Hin NE]. cbn in NE. exact (HD a k Hin NE).
Qed.

End WithSegs.

End RC__1.
