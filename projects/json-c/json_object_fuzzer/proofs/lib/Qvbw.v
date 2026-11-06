(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Fixpoint akids (m : word -> option byte) (ks : list (option jshape)) (vs : list Z) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', v :: vs', bs :: bss' =>
match k with
| None => v = 0 /\ bs = []
| Some s' => v <> 0 /\ jval segs fn s' m bs v 1
end /\ akids m ks' vs' bss'
| _, _, _ => False
end.

Fixpoint okids (m : word -> option byte) (ks : list (option jshape)) (kvs : list (Z * Z)) (bss : list (list blk)) {struct ks} : Prop :=
match ks, kvs, bss with
| [], [], [] => True
| k :: ks', (_, v) :: vs', bs :: bss' =>
match k with
| None => v = 0 /\ bs = []
| Some s' => v <> 0 /\ jval segs fn s' m bs v 1
end /\ okids m ks' vs' bss'
| _, _, _ => False
end.

#[using="Type"] Lemma sarr_open : forall kids m BS p rc,
jval segs fn (Sarr kids) m BS p rc ->
exists pb PBS a AL ps KBS,
BS = ((p, 48) :: AL ++ concat KBS) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb 0 0 ++ [C8 (Z_to_bv 64 a)]) /\
alist segs fn m AL a ps /\ length ps = length kids /\ length KBS = length kids /\ akids m kids ps KBS.
Proof.
intros kids m BS p rc (pb & PBS & REST & EBS & OPB & a & AL & ps & KBS & ER & H & HA & L1 & L2 & KIDS).
subst REST. exists pb, PBS, a, AL, ps, KBS. repeat (split; [assumption|]).
clear - KIDS. revert ps KBS KIDS. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS; try exact KIDS.
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma sarr_close : forall kids m BS p rc pb PBS a AL ps KBS,
BS = ((p, 48) :: AL ++ concat KBS) ++ PBS -> opt_pbuf segs m PBS pb ->
rw_cells segs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb 0 0 ++ [C8 (Z_to_bv 64 a)]) ->
alist segs fn m AL a ps -> length ps = length kids -> length KBS = length kids -> akids m kids ps KBS ->
jval segs fn (Sarr kids) m BS p rc.
Proof.
intros kids m BS p rc pb PBS a AL ps KBS EBS OPB H HA L1 L2 KIDS.
cbn [jval]. exists pb, PBS, ((p, 48) :: AL ++ concat KBS). split; [exact EBS|]. split; [exact OPB|].
exists a, AL, ps, KBS. repeat (split; [first [reflexivity | assumption] |]).
clear - KIDS. revert ps KBS KIDS. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS; try exact KIDS.
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma sobj_open : forall kids m BS p rc,
jval segs fn (Sobj kids) m BS p rc ->
exists pb PBS t TBS kvs KBS,
BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb 0 0 ++ [C8 (Z_to_bv 64 t)]) /\
lhtab2 segs fn m TBS t kvs /\ length kvs = length kids /\ length KBS = length kids /\ okids m kids kvs KBS.
Proof.
intros kids m BS p rc (pb & PBS & REST & EBS & OPB & t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS).
subst REST. exists pb, PBS, t, TBS, kvs, KBS. repeat (split; [assumption|]).
clear - KIDS. revert kvs KBS KIDS. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS; try exact KIDS.
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma sobj_close : forall kids m BS p rc pb PBS t TBS kvs KBS,
BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS -> opt_pbuf segs m PBS pb ->
rw_cells segs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb 0 0 ++ [C8 (Z_to_bv 64 t)]) ->
lhtab2 segs fn m TBS t kvs -> length kvs = length kids -> length KBS = length kids -> okids m kids kvs KBS ->
jval segs fn (Sobj kids) m BS p rc.
Proof.
intros kids m BS p rc pb PBS t TBS kvs KBS EBS OPB H HT L1 L2 KIDS.
cbn [jval]. exists pb, PBS, ((p, 48) :: TBS ++ concat KBS). split; [exact EBS|]. split; [exact OPB|].
exists t, TBS, kvs, KBS. repeat (split; [first [reflexivity | assumption] |]).
clear - KIDS. revert kvs KBS KIDS. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS; try exact KIDS.
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma akids_agree : forall BSa m m' ks vs bss,
akids m ks vs bss -> agree_on segs BSa m m' -> incl (concat bss) BSa -> akids m' ks vs bss.
Proof.
intros BSa m m' ks; induction ks as [|k ks IH]; intros [|v vs] [|bs bss] KIDS AG Hi; try exact KIDS.
cbn [concat] in Hi. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply Hi; apply in_or_app; left; exact Hb].
- eapply IH; [exact K2 | exact AG | intros b Hb; apply Hi; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma okids_agree : forall BSa m m' ks kvs bss,
okids m ks kvs bss -> agree_on segs BSa m m' -> incl (concat bss) BSa -> okids m' ks kvs bss.
Proof.
intros BSa m m' ks; induction ks as [|k ks IH]; intros [|[kk v] kvs] [|bs bss] KIDS AG Hi; try exact KIDS.
cbn [concat] in Hi. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply Hi; apply in_or_app; left; exact Hb].
- eapply IH; [exact K2 | exact AG | intros b Hb; apply Hi; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma akids_app1 : forall m ks vs bss k v bs,
akids m ks vs bss -> akids m [k] [v] [bs] -> akids m (ks ++ [k]) (vs ++ [v]) (bss ++ [bs]).
Proof.
intros m ks; induction ks as [|k0 ks IH]; intros [|v0 vs] [|bs0 bss] k v bs KIDS ONE; try (exact ONE); try (destruct KIDS; fail); cbn in KIDS |- *; try tauto.
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; assumption].
Qed.

#[using="Type"] Lemma okids_app1 : forall m ks kvs bss k kv bs,
okids m ks kvs bss -> okids m [k] [kv] [bs] -> okids m (ks ++ [k]) (kvs ++ [kv]) (bss ++ [bs]).
Proof.
intros m ks; induction ks as [|k0 ks IH]; intros [|[kk0 v0] kvs] [|bs0 bss] k kv bs KIDS ONE; try (exact ONE); cbn in KIDS |- *; try tauto.
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; assumption].
Qed.

#[using="Type"] Lemma akids_one : forall m s bs v, jopt segs fn s m bs v -> akids m [s] [v] [bs].
Proof. intros m [s'|] bs v J; cbn in J |- *; tauto. Qed.
#[using="Type"] Lemma okids_one : forall m s bs kk v, jopt segs fn s m bs v -> okids m [s] [(kk, v)] [bs].
Proof. intros m [s'|] bs kk v J; cbn in J |- *; tauto. Qed.

#[using="Type"] Lemma akids_length : forall m ks vs bss, akids m ks vs bss -> length vs = length ks /\ length bss = length ks.
Proof.
intros m ks; induction ks as [|k ks IH]; intros [|v vs] [|bs bss] KIDS; try (destruct KIDS; fail); [split; reflexivity|].
destruct KIDS as [_ K2]. destruct (IH _ _ K2) as [E1 E2]. cbn. rewrite E1, E2. split; reflexivity.
Qed.
#[using="Type"] Lemma okids_length : forall m ks kvs bss, okids m ks kvs bss -> length kvs = length ks /\ length bss = length ks.
Proof.
intros m ks; induction ks as [|k ks IH]; intros [|[kk v] kvs] [|bs bss] KIDS; try (destruct KIDS; fail); [split; reflexivity|].
destruct KIDS as [_ K2]. destruct (IH _ _ K2) as [E1 E2]. cbn. rewrite E1, E2. split; reflexivity.
Qed.

#[using="Type"] Lemma akids_app : forall m ks1 vs1 bss1 ks2 vs2 bss2,
akids m ks1 vs1 bss1 -> akids m ks2 vs2 bss2 -> akids m (ks1 ++ ks2) (vs1 ++ vs2) (bss1 ++ bss2).
Proof.
intros m ks1; induction ks1 as [|k ks1 IH]; intros [|v vs1] [|bs bss1] ks2 vs2 bss2 K1 K2; try (destruct K1; fail); [exact K2|].
destruct K1 as [K11 K12]. cbn. split; [exact K11 | apply IH; assumption].
Qed.
#[using="Type"] Lemma okids_app : forall m ks1 kvs1 bss1 ks2 kvs2 bss2,
okids m ks1 kvs1 bss1 -> okids m ks2 kvs2 bss2 -> okids m (ks1 ++ ks2) (kvs1 ++ kvs2) (bss1 ++ bss2).
Proof.
intros m ks1; induction ks1 as [|k ks1 IH]; intros [|[kk v] kvs1] [|bs bss1] ks2 kvs2 bss2 K1 K2; try (destruct K1; fail); [exact K2|].
destruct K1 as [K11 K12]. cbn. split; [exact K11 | apply IH; assumption].
Qed.

#[using="Type"] Lemma akids_app_inv : forall m ks1 vs1 bss1 ks2 vs2 bss2,
length vs1 = length ks1 -> length bss1 = length ks1 ->
akids m (ks1 ++ ks2) (vs1 ++ vs2) (bss1 ++ bss2) -> akids m ks1 vs1 bss1 /\ akids m ks2 vs2 bss2.
Proof.
intros m ks1; induction ks1 as [|k ks1 IH]; intros [|v vs1] [|bs bss1] ks2 vs2 bss2 L1 L2 K; cbn in L1, L2; try lia.
- split; [exact I | exact K].
- destruct K as [K1 K2]. destruct (IH vs1 bss1 ks2 vs2 bss2 ltac:(lia) ltac:(lia) K2) as [K3 K4].
split; [split; [exact K1 | exact K3] | exact K4].
Qed.
#[using="Type"] Lemma okids_app_inv : forall m ks1 kvs1 bss1 ks2 kvs2 bss2,
length kvs1 = length ks1 -> length bss1 = length ks1 ->
okids m (ks1 ++ ks2) (kvs1 ++ kvs2) (bss1 ++ bss2) -> okids m ks1 kvs1 bss1 /\ okids m ks2 kvs2 bss2.
Proof.
intros m ks1; induction ks1 as [|k ks1 IH]; intros [|[kk v] kvs1] [|bs bss1] ks2 kvs2 bss2 L1 L2 K; cbn in L1, L2; try lia.
- split; [exact I | exact K].
- destruct K as [K1 K2]. destruct (IH kvs1 bss1 ks2 kvs2 bss2 ltac:(lia) ltac:(lia) K2) as [K3 K4].
split; [split; [exact K1 | exact K3] | exact K4].
Qed.

#[using="Type"] Lemma okids_nth : forall m ks kvs bss j kk v,
okids m ks kvs bss -> nth_error kvs j = Some (kk, v) ->
exists k bs, nth_error ks j = Some k /\ nth_error bss j = Some bs /\ jopt segs fn k m bs v.
Proof.
intros m ks; induction ks as [|k0 ks IH]; intros [|[kk0 v0] kvs] [|bs0 bss] j kk v KIDS Hj; try (destruct KIDS; fail); [destruct j; discriminate|].
destruct KIDS as [K1 K2]. destruct j as [|j].
- cbn in Hj. injection Hj as -> ->. exists k0, bs0. split; [reflexivity|]. split; [reflexivity|]. destruct k0; exact K1.
- cbn in Hj. destruct (IH kvs bss j kk v K2 Hj) as (k & bs & H1 & H2 & H3). exists k, bs. cbn. auto.
Qed.

#[using="Type"] Lemma nth_error_split3 : forall (X : Type) (l : list X) j x,
nth_error l j = Some x -> l = firstn j l ++ x :: skipn (S j) l /\ length (firstn j l) = j.
Proof.
intros X l; induction l as [|y l IH]; intros [|j] x H; cbn in H; try discriminate.
- injection H as ->. split; reflexivity.
- destruct (IH j x H) as [E L]. cbn. rewrite <- E. split; [reflexivity | rewrite L; reflexivity].
Qed.

#[using="Type"] Lemma concat_mid : forall (bss1 bss2 : list (list blk)) (bs : list blk),
concat (bss1 ++ bs :: bss2) = concat bss1 ++ bs ++ concat bss2.
Proof. intros. rewrite concat_app. cbn. reflexivity. Qed.

#[using="Type"] Lemma jval_root_in : forall s m BS p rc, jval segs fn s m BS p rc -> exists n, In (p, n) BS /\ 48 <= n.
Proof.
intros s m BS p rc J.
destruct s as [|u| |h|kids|kids]; destruct J as (pb & PBS & REST & EBS & OPB & J); subst BS.
- destruct J as (b & junk & -> & _). exists 48. split; [apply in_or_app; left; left; reflexivity | lia].
- destruct u.
+ destruct J as (bits & ud & udn & uds & -> & _). exists 48. split; [apply in_or_app; left; left; reflexivity | lia].
+ destruct J as (bits & -> & _). exists 48. split; [apply in_or_app; left; left; reflexivity | lia].
- destruct J as (cty & v & junk & -> & _). exists 56. split; [apply in_or_app; left; left; reflexivity | lia].
- destruct h.
+ destruct J as (len & pd & pdn & str & junk2 & -> & _). exists 56. split; [apply in_or_app; left; left; reflexivity | lia].
+ destruct J as (len & str & junk & -> & _). exists (str_objsize len). split; [apply in_or_app; left; left; reflexivity | unfold str_objsize; lia].
- destruct J as (t & TBS & kvs & KBS & -> & _). exists 48. split; [apply in_or_app; left; left; reflexivity | lia].
- destruct J as (a & ABS & ps & KBS & -> & _). exists 48. split; [apply in_or_app; left; left; reflexivity | lia].
Qed.

#[using="Type"] Lemma jopt_val : forall L (HIx : heap_iface L) A LBall m md s bs v,
HEAP L HIx A LBall m md -> incl bs LBall -> jopt segs fn s m bs v -> 0 <= v /\ v + 1 <= alloc_ceiling.
Proof.
intros L HIx A LBall m md [s'|] bs v HP Hi J; cbn in J.
- destruct J as [Hv J]. destruct (jval_root_in _ _ _ _ _ J) as (n & Hin & Hn).
pose proof (heap_blk L HIx _ _ _ _ v n HP (Hi _ Hin)) as (_ & _ & Hlo & Hhi & _). lia.
- destruct J as [-> _]. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
Qed.

#[using="Type"] Lemma akids_vals : forall L (HIx : heap_iface L) A LBall m md ks vs bss,
HEAP L HIx A LBall m md -> incl (concat bss) LBall ->
akids m ks vs bss -> Forall (fun v => 0 <= v /\ v + 1 <= alloc_ceiling) vs.
Proof.
intros L HIx A LBall m md ks; induction ks as [|k ks IH]; intros [|v vs] [|bs bss] HP Hi KIDS; try (destruct KIDS; fail); [apply Forall_nil|].
cbn [concat] in Hi. destruct KIDS as [K1 K2]. apply Forall_cons.
- eapply (jopt_val L HIx) with (s := k) (bs := bs); [exact HP | intros b Hb; apply Hi; apply in_or_app; left; exact Hb | destruct k; exact K1].
- eapply IH; [exact HP | intros b Hb; apply Hi; apply in_or_app; right; exact Hb | exact K2].
Qed.

#[using="Type"] Lemma bytes_at_prefix : forall m a l1 l2, bytes_at segs m a (l1 ++ l2) -> bytes_at segs m a l1.
Proof.
intros m a l1 l2 (H0 & H1 & HB). rewrite length_app in H1. split; [exact H0|]. split; [lia|].
intros i Hi. rewrite (HB i ltac:(rewrite length_app; lia)). rewrite nth_error_app1 by exact Hi. reflexivity.
Qed.

#[using="Type"] Lemma cstr_bytes : forall m a n s, cstr segs m a n s -> bytes_at segs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s.
Proof.
intros m a n s (CL & CNZ & junk & [[Hwf HB] _]). split.
- cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
replace (s ++ [Z_to_bv 8 0] ++ junk) with ((s ++ [Z_to_bv 8 0]) ++ junk) in HB by (rewrite <- app_assoc; reflexivity).
eapply bytes_at_prefix. exact HB.
- intros X. rewrite Forall_forall in CNZ. apply (CNZ _ X). reflexivity.
Qed.

End WithSegs.

End RC__1.
