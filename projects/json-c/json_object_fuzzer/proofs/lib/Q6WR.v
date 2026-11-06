(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QKQo Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QKQo.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section BlkWrite.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Notation segs := (hl_segs L).

#[using="Type"] Lemma blk_write_heap : forall A x n REST m m2 md W,
HEAP L HIx A ((x, n) :: REST) m md -> munch W m m2 -> wmono segs m m2 -> mem_inv segs m2 ->
Forall (fun iv => x <= fst iv /\ snd iv <= x + n) W ->
HEAP L HIx A ((x, n) :: REST) m2 md.
Proof.
intros A x n REST m m2 md W HP MU WM MI HW.
eapply (heap_frame L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok L HIx _ _ _ _ _ _ HP MU).
clear -HW. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd]. right; left. exists x, n. split; [left; reflexivity | lia].
Qed.

#[using="Type"] Lemma blk_write_agree : forall A x n REST m m2 md W,
HEAP L HIx A ((x, n) :: REST) m md -> munch W m m2 -> wmono segs m m2 ->
Forall (fun iv => x <= fst iv /\ snd iv <= x + n) W ->
agree_on segs REST m m2.
Proof.
intros A x n REST m m2 md W HP MU WM HW.
eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin.
assert (Hne : x <> a).
{ intros <-. exact (nodup_prefix_suffix [(x, n)] REST x n k (heap_blk_nodup L HIx _ _ _ _ HP) ltac:(left; reflexivity) Hin). }
pose proof (heap_blk_disjoint L HIx _ _ _ _ x n a k HP ltac:(left; reflexivity) ltac:(right; exact Hin) Hne) as D.
pose proof (heap_blk L HIx _ _ _ _ a k HP ltac:(right; exact Hin)) as (Hk & _).
clear -HW D Hk. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2. cbn. split; [lia | apply IH; exact HW].
Qed.

#[using="Type"] Lemma blk_write_pres : forall A x n REST m m2 md W LB SP,
HEAP L HIx A ((x, n) :: REST) m md -> munch W m m2 -> wmono segs m m2 ->
Forall (fun iv => x <= fst iv /\ snd iv <= x + n) W ->
(forall b, In b LB -> In b REST) -> alloc_ceiling <= SP ->
heap_pres L LB SP m m2.
Proof.
intros A x n REST m m2 md W LB SP HP MU WM HW SUB HSP.
eapply (heap_pres_of_munch L LB SP); [exact MU | exact WM |].
eapply (client_outside L HIx); [exact HP | intros b Hb; right; exact (SUB b Hb) | exact HSP |].
pose proof (heap_blk L HIx _ _ _ _ x n HP ltac:(left; reflexivity)) as (_ & _ & _ & Hhi & _).
clear -HW SUB HP Hhi. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd]. right; left. exists x, n.
split; [left; reflexivity|]. split; [| lia].
intros Hin. exact (nodup_prefix_suffix [(x, n)] REST x n n (heap_blk_nodup L HIx _ _ _ _ HP) ltac:(left; reflexivity) (SUB _ Hin)).
Qed.

#[using="Type"] Lemma blk_write : forall A x n REST m m2 md W LB SP,
HEAP L HIx A ((x, n) :: REST) m md -> munch W m m2 -> wmono segs m m2 -> mem_inv segs m2 ->
Forall (fun iv => x <= fst iv /\ snd iv <= x + n) W ->
(forall b, In b LB -> In b REST) -> alloc_ceiling <= SP ->
HEAP L HIx A ((x, n) :: REST) m2 md /\ agree_on segs REST m m2 /\ heap_pres L LB SP m m2.
Proof.
intros. split; [| split]; [eapply blk_write_heap | eapply blk_write_agree | eapply blk_write_pres]; eassumption.
Qed.

#[using="Type"] Lemma blk_write_in : forall A LL x n m m2 md W,
HEAP L HIx A LL m md -> In (x, n) LL -> munch W m m2 -> wmono segs m m2 -> mem_inv segs m2 ->
Forall (fun iv => x <= fst iv /\ snd iv <= x + n) W ->
HEAP L HIx A LL m2 md /\ agree_on segs (others x LL) m m2.
Proof.
intros A LL x n m m2 md W HP Hin MU WM MI HW. split.
- eapply (heap_frame L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok L HIx _ _ _ _ _ _ HP MU).
clear -HW Hin. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd]. right; left. exists x, n. split; [exact Hin | lia].
- eapply (agree_others_of_munch segs); [exact Hin | | | exact MU | exact WM | exact HW].
+ intros a k a' k' H1 H2 NE. exact (heap_blk_disjoint L HIx _ _ _ _ _ _ _ _ HP H1 H2 NE).
+ intros a k H1. exact (proj1 (heap_blk L HIx _ _ _ _ _ _ HP H1)).
Qed.

#[using="Type"] Lemma blk_write_in_pres : forall A LL x n m m2 md W LB SP,
HEAP L HIx A LL m md -> In (x, n) LL -> munch W m m2 -> wmono segs m m2 ->
Forall (fun iv => x <= fst iv /\ snd iv <= x + n) W ->
(forall b, In b LB -> In b LL) -> (forall k, ~ In (x, k) LB) -> alloc_ceiling <= SP ->
heap_pres L LB SP m m2.
Proof.
intros A LL x n m m2 md W LB SP HP Hin MU WM HW SUB NX HSP.
eapply (heap_pres_of_munch L LB SP); [exact MU | exact WM |].
eapply (client_outside L HIx); [exact HP | intros b Hb; exact (SUB b Hb) | exact HSP |].
clear -HW Hin NX. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd]. right; left. exists x, n.
split; [exact Hin|]. split; [apply NX | lia].
Qed.

#[using="Type"] Lemma in_app_r : forall (P LB : list blk) b, In b LB -> In b (P ++ LB).
Proof. intros. apply in_or_app. right. assumption. Qed.
#[using="Type"] Lemma in_app_l : forall (P LB : list blk) b, In b P -> In b (P ++ LB).
Proof. intros. apply in_or_app. left. assumption. Qed.
End BlkWrite.
End RC__1.

Ltac in_elem := first [ left; reflexivity | apply in_or_app; left; in_elem | apply in_or_app; right; in_elem | right; in_elem ].

Ltac in_sub Hb :=
first [ exact Hb
| apply in_or_app; right; in_sub Hb | apply in_or_app; left; in_sub Hb | right; in_sub Hb
| lazymatch type of Hb with
| In _ (_ :: _) => destruct Hb as [<- | Hb]; [in_elem | in_sub Hb]
| In _ (_ ++ _) => apply in_app_or in Hb; destruct Hb as [Hb | Hb]; in_sub Hb
| In _ [] => destruct Hb
end ].
End Mq0.

From Stdlib Require Import ZArith List Lia Bool Permutation.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma snoc_inv_gen : forall {A} (l : list A), l = [] \/ exists l' x, l = l' ++ [x].
Proof.
intros A l. induction l as [|y l IH]; [left; reflexivity | right].
destruct IH as [-> | (l' & x & ->)]; [exists [], y; reflexivity | exists (y :: l'), x; reflexivity].
Qed.

Lemma app_inj_last : forall {A} (l1 l2 : list A) x y, l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y.
Proof.
intros A l1 l2 x y H. apply (f_equal (@rev A)) in H. rewrite !rev_app_distr in H. cbn in H.
injection H as E1 E2. split; [| exact E1]. apply (f_equal (@rev A)) in E2. rewrite !rev_involutive in E2. exact E2.
Qed.

Lemma concat_snoc : forall {A} (l : list (list A)) x, concat (l ++ [x]) = concat l ++ x.
Proof. intros. rewrite concat_app. cbn. rewrite app_nil_r. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation wz := (Z_to_bv 64) (only parsing).

Fixpoint okids (m : word -> option byte) (ks : list (option jshape)) (vs : list Z) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', v :: vs', bs :: bss' =>
match k with
| None => v = 0 /\ bs = []
| Some s => v <> 0 /\ jval segs fn s m bs v 1
end /\ okids m ks' vs' bss'
| _, _, _ => False
end.

#[using="Type"] Lemma okids_len : forall m ks vs bss, okids m ks vs bss -> length vs = length ks /\ length bss = length ks.
Proof.
intros m ks. induction ks as [|k ks IH]; intros [|v vs] [|bs bss] H; cbn in H; try contradiction; [split; reflexivity|].
destruct H as [_ H]. destruct (IH vs bss H) as [E1 E2]. cbn. rewrite E1, E2. split; reflexivity.
Qed.

#[using="Type"] Lemma okids_nil_inv : forall m vs bss, okids m [] vs bss -> vs = [] /\ bss = [].
Proof. intros m [|v vs] [|bs bss] H; cbn in H; try contradiction. split; reflexivity. Qed.

#[using="Type"] Lemma okids_snoc : forall m ks vs bss k v bs,
okids m ks vs bss ->
match k with None => v = 0 /\ bs = [] | Some s => v <> 0 /\ jval segs fn s m bs v 1 end ->
okids m (ks ++ [k]) (vs ++ [v]) (bss ++ [bs]).
Proof.
intros m ks. induction ks as [|k0 ks IH]; intros [|v0 vs] [|bs0 bss] k v bs H Hk; cbn in H; try contradiction.
- cbn. split; [exact Hk | exact I].
- destruct H as [H1 H2]. cbn. split; [exact H1 | apply IH; assumption].
Qed.

#[using="Type"] Lemma okids_snoc_inv : forall m ks k vs bss,
okids m (ks ++ [k]) vs bss ->
exists vs1 v bss1 bs, vs = vs1 ++ [v] /\ bss = bss1 ++ [bs] /\ okids m ks vs1 bss1 /\
match k with None => v = 0 /\ bs = [] | Some s => v <> 0 /\ jval segs fn s m bs v 1 end.
Proof.
intros m ks. induction ks as [|k0 ks IH]; intros k [|v0 vs] [|bs0 bss] H; cbn in H; try contradiction.
- destruct H as [Hk H]. destruct vs; destruct bss; try contradiction.
exists [], v0, [], bs0. repeat split; try reflexivity. exact Hk.
- destruct H as [H1 H2]. destruct (IH k vs bss H2) as (vs1 & v & bss1 & bs & -> & -> & H3 & H4).
exists (v0 :: vs1), v, (bs0 :: bss1), bs. repeat split; try reflexivity; try assumption.
Qed.

#[using="Type"] Lemma okids_agree : forall BS m m' ks vs bss,
okids m ks vs bss -> agree_on segs BS m m' -> incl (concat bss) BS -> okids m' ks vs bss.
Proof.
intros BS m m' ks. induction ks as [|k ks IH]; intros [|v vs] [|bs bss] H AG Hi; cbn in H; try contradiction; [exact I|].
destruct H as [H1 H2]. cbn in Hi. split.
- destruct k as [s|]; [| exact H1]. destruct H1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply Hi; apply in_or_app; left; exact Hb].
- apply IH; [exact H2 | exact AG | intros b Hb; apply Hi; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma okids_vals_none : forall m ks vs bss, okids m ks vs bss -> (forall k, In k ks -> k = None) ->
Forall (fun v => v = 0) vs /\ concat bss = [].
Proof.
intros m ks. induction ks as [|k ks IH]; intros [|v vs] [|bs bss] H HN; cbn in H; try contradiction.
- split; [apply Forall_nil | reflexivity].
- destruct H as [H1 H2]. rewrite (HN k ltac:(left; reflexivity)) in H1. destruct H1 as [-> ->].
destruct (IH vs bss H2 ltac:(intros k' Hk'; apply HN; right; exact Hk')) as [F E].
split; [apply Forall_cons; [reflexivity | exact F] | cbn; exact E].
Qed.

#[using="Type"] Lemma jval_obj_open : forall kids m BS p rc,
jval segs fn (Sobj kids) m BS p rc ->
exists pb PBS t TBS kvs KBS,
BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb 0 0 ++ [C8 (wz t)]) /\
lhtab2 segs fn m TBS t kvs /\ okids m kids (map snd kvs) KBS.
Proof.
intros kids m BS p rc J.
destruct J as (pb & PBS & REST & EBS & OPB & t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). subst REST.
exists pb, PBS, t, TBS, kvs, KBS. split; [exact EBS|]. split; [exact OPB|]. split; [exact H|]. split; [exact HT|].
clear EBS OPB H HT L1 L2. revert kvs KBS KIDS.
induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS; try exact KIDS.
destruct KIDS as [K1 K2]. cbn. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma jval_obj_close : forall kids m BS p rc pb PBS t TBS kvs KBS,
BS = ((p, 48) :: TBS ++ concat KBS) ++ PBS -> opt_pbuf segs m PBS pb ->
rw_cells segs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb 0 0 ++ [C8 (wz t)]) ->
lhtab2 segs fn m TBS t kvs -> okids m kids (map snd kvs) KBS ->
jval segs fn (Sobj kids) m BS p rc.
Proof.
intros kids m BS p rc pb PBS t TBS kvs KBS EBS OPB H HT KIDS.
pose proof (okids_len _ _ _ _ KIDS) as [L1 L2]. rewrite length_map in L1.
exists pb, PBS, ((p, 48) :: TBS ++ concat KBS). split; [exact EBS|]. split; [exact OPB|].
exists t, TBS, kvs, KBS. split; [reflexivity|]. split; [exact H|]. split; [exact HT|]. split; [exact L1|]. split; [exact L2|].
clear EBS OPB H HT L1 L2. revert kvs KBS KIDS.
induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS; cbn in KIDS; try contradiction; [exact I|].
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma jval_arr_open : forall kids m BS p rc,
jval segs fn (Sarr kids) m BS p rc ->
exists pb PBS a ABS ps KBS,
BS = ((p, 48) :: ABS ++ concat KBS) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb 0 0 ++ [C8 (wz a)]) /\
alist segs fn m ABS a ps /\ okids m kids ps KBS.
Proof.
intros kids m BS p rc J.
destruct J as (pb & PBS & REST & EBS & OPB & a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). subst REST.
exists pb, PBS, a, ABS, ps, KBS. split; [exact EBS|]. split; [exact OPB|]. split; [exact H|]. split; [exact HA|].
clear EBS OPB H HA L1 L2. revert ps KBS KIDS.
induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS; try exact KIDS.
destruct KIDS as [K1 K2]. cbn. split; [exact K1 | apply IH; exact K2].
Qed.

#[using="Type"] Lemma jval_arr_close : forall kids m BS p rc pb PBS a ABS ps KBS,
BS = ((p, 48) :: ABS ++ concat KBS) ++ PBS -> opt_pbuf segs m PBS pb ->
rw_cells segs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb 0 0 ++ [C8 (wz a)]) ->
alist segs fn m ABS a ps -> okids m kids ps KBS ->
jval segs fn (Sarr kids) m BS p rc.
Proof.
intros kids m BS p rc pb PBS a ABS ps KBS EBS OPB H HA KIDS.
pose proof (okids_len _ _ _ _ KIDS) as [L1 L2].
exists pb, PBS, ((p, 48) :: ABS ++ concat KBS). split; [exact EBS|]. split; [exact OPB|].
exists a, ABS, ps, KBS. split; [reflexivity|]. split; [exact H|]. split; [exact HA|]. split; [exact L1|]. split; [exact L2|].
clear EBS OPB H HA L1 L2. revert ps KBS KIDS.
induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS; cbn in KIDS; try contradiction; [exact I|].
destruct KIDS as [K1 K2]. split; [exact K1 | apply IH; exact K2].
Qed.

Definition zobj (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat)
(t tbl size : Z) (es : list lent) (svs : list slotv) (XBS : list blk) : Prop :=
exists pb PBS KBS esk esz,
es = esk ++ esz /\ length esz = nz /\ Forall (fun e => le_v e = 0) esz /\
XBS = ((x, 48) :: lh_blocks t tbl size es ++ concat KBS) ++ PBS /\
opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\
okids m kids (map le_v esk) KBS.

Definition zarr (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat)
(a arr size : Z) (XBS : list blk) : Prop :=
exists pb PBS KBS ps,
XBS = ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS) ++ PBS /\
opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz a)]) /\
alist segs fn m [(a, 32); (arr, 8 * size)] a (ps ++ repeat 0 nz) /\
okids m kids ps KBS.

Definition zobjc m x q kids XBS : Prop := exists t tbl size es svs, zobj m x q kids 0 t tbl size es svs XBS.
Definition zarrc m x q kids XBS : Prop := exists a arr size, zarr m x q kids 0 a arr size XBS.

Definition zomb (s : jshape) m x XBS : Prop :=
match s with
| Sobj kids => kids <> [] /\ zobjc m x 0 kids XBS
| Sarr kids => kids <> [] /\ zarrc m x 0 kids XBS
| _ => False
end.

#[using="Type"] Lemma zobj_agree : forall BS m m' x q kids nz t tbl size es svs XBS,
zobj m x q kids nz t tbl size es svs XBS -> agree_on segs BS m m' -> incl XBS BS ->
zobj m' x q kids nz t tbl size es svs XBS.
Proof.
intros BS m m' x q kids nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) AG Hi.
exists pb, PBS, KBS, esk, esz. split; [exact Ees|]. split; [exact Lz|]. split; [exact Fz|]. split; [exact EX|].
subst XBS. split; [| split; [| split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; apply Hi; apply in_or_app; right; exact Hb].
- eapply rw_cells_agree; [exact HDR | exact AG | exists x, 48; split; [apply Hi; left; reflexivity | cbn; lia]].
- eapply lh_open_agree; [exact OPEN | exact AG | intros b Hb; apply Hi; apply in_or_app; left; right; apply in_or_app; left; exact Hb].
- eapply okids_agree; [exact OK | exact AG | intros b Hb; apply Hi; apply in_or_app; left; right; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma zarr_agree : forall BS m m' x q kids nz a arr size XBS,
zarr m x q kids nz a arr size XBS -> agree_on segs BS m m' -> incl XBS BS ->
zarr m' x q kids nz a arr size XBS.
Proof.
intros BS m m' x q kids nz a arr size XBS (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK) AG Hi.
exists pb, PBS, KBS, ps. split; [exact EX|]. subst XBS. split; [| split; [| split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; apply Hi; apply in_or_app; right; exact Hb].
- eapply rw_cells_agree; [exact HDR | exact AG | exists x, 48; split; [apply Hi; left; reflexivity | cbn; lia]].
- eapply alist_agree; [exact AL | exact AG | intros b Hb; apply Hi; apply in_or_app; left; right; apply in_or_app; left; exact Hb].
- eapply okids_agree; [exact OK | exact AG | intros b Hb; apply Hi; apply in_or_app; left; right; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma zobjc_agree : forall BS m m' x q kids XBS,
zobjc m x q kids XBS -> agree_on segs BS m m' -> incl XBS BS -> zobjc m' x q kids XBS.
Proof. intros BS m m' x q kids XBS (t & tbl & size & es & svs & Z1) AG Hi. exists t, tbl, size, es, svs. eapply zobj_agree; eauto. Qed.
#[using="Type"] Lemma zarrc_agree : forall BS m m' x q kids XBS,
zarrc m x q kids XBS -> agree_on segs BS m m' -> incl XBS BS -> zarrc m' x q kids XBS.
Proof. intros BS m m' x q kids XBS (a & arr & size & Z1) AG Hi. exists a, arr, size. eapply zarr_agree; eauto. Qed.

#[using="Type"] Lemma zobj_vals : forall m x q kids nz t tbl size es svs XBS,
zobj m x q kids nz t tbl size es svs XBS -> length es = (length kids + nz)%nat.
Proof.
intros m x q kids nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & -> & Lz & _ & _ & _ & _ & _ & OK).
pose proof (okids_len _ _ _ _ OK) as [L1 _]. rewrite length_map in L1. rewrite length_app. lia.
Qed.

End WithSegs.
