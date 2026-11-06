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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.
Import ListNotations.
Open Scope Z_scope.

Lemma upd_app_len' : forall {X} (a b : list X) x y, upd (a ++ x :: b) (length a) y = a ++ y :: b.
Proof. intros X a. induction a as [|z a IH]; intros b x y; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nth_error_app_len : forall {X} (a b : list X) x, nth_error (a ++ x :: b) (length a) = Some x.
Proof. intros. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma firstn_app_len : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn. apply app_nil_r. Qed.

Lemma al_nth_app_len : forall (ps1 : list Z) v rest, al_nth ((ps1 ++ [v]) ++ rest) (Z.of_nat (length ps1)) = v.
Proof.
intros. unfold al_nth. rewrite Nat2Z.id, <- app_assoc. cbn.
rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma Forall_repeat0 : forall n, Forall (fun p : Z => p = 0) (repeat 0 n).
Proof. induction n; cbn; constructor; auto. Qed.

Ltac hperm := unfold lh_blocks, kblk, blk; perm.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation wz := (Z_to_bv 64) (only parsing).

#[using="Type"] Lemma zobjc_hdr : forall m x q kids XBS,
zobjc segs fn m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q' ++ [C8 (wz cf)]) ->
agree_on segs (others x XBS) m m' -> zobjc segs fn m' x q' kids XBS).
Proof.
intros m x q kids XBS (t & tbl & size & es & svs & pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) ND.
exists pb, t. split; [rewrite EX; left; reflexivity|]. split; [exact HDR|].
intros m' q' HDR' AG. exists t, tbl, size, es, svs, pb, PBS, KBS, esk, esz.
split; [exact Ees|]. split; [exact Lz|]. split; [exact Fz|]. split; [exact EX|]. rewrite EX in ND, AG.
split; [| split; [exact HDR' | split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply lh_open_agree; [exact OPEN | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]].
- eapply okids_agree; [exact OK | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb]].
Qed.

#[using="Type"] Lemma zarrc_hdr : forall m x q kids XBS,
zarrc segs fn m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q' ++ [C8 (wz cf)]) ->
agree_on segs (others x XBS) m m' -> zarrc segs fn m' x q' kids XBS).
Proof.
intros m x q kids XBS (a & arr & size & pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK) ND.
exists pb, a. split; [rewrite EX; left; reflexivity|]. split; [exact HDR|].
intros m' q' HDR' AG. exists a, arr, size, pb, PBS, KBS, ps.
split; [exact EX|]. rewrite EX in ND, AG.
split; [| split; [exact HDR' | split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply alist_agree; [exact AL | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]].
- eapply okids_agree; [exact OK | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb]].
Qed.

#[using="Type"] Lemma zobj_last : forall m x q kids k nz t tbl size es svs XBS,
zobj segs fn m x q (kids ++ [k]) nz t tbl size es svs XBS ->
exists pb PBS KBS1 bs esk1 e esz,
es = esk1 ++ e :: esz /\ length esk1 = length kids /\ length esz = nz /\ Forall (fun e => le_v e = 0) esz /\
XBS = ((x, 48) :: lh_blocks t tbl size es ++ (concat KBS1 ++ bs)) ++ PBS /\
opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\
okids segs fn m kids (map le_v esk1) KBS1 /\
match k with None => le_v e = 0 /\ bs = [] | Some c => le_v e <> 0 /\ jval segs fn c m bs (le_v e) 1 end.
Proof.
intros m x q kids k nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2]. rewrite length_map, length_app in L1. cbn in L1.
destruct (snoc_inv_gen esk) as [-> | (esk1 & e & ->)]; [cbn in L1; lia|].
rewrite map_app in OK. cbn [map] in OK.
destruct (okids_snoc_inv _ _ _ _ _ _ _ OK) as (vs1 & v & KBS1 & bs & Evs & -> & OK1 & Hk).
apply app_inj_last in Evs as [<- <-].
exists pb, PBS, KBS1, bs, esk1, e, esz.
rewrite length_app in L1. cbn in L1.
split; [rewrite Ees, <- app_assoc; reflexivity|]. split; [lia|]. split; [exact Lz|]. split; [exact Fz|].
split; [rewrite EX, concat_snoc; reflexivity|].
split; [exact OPB|]. split; [exact HDR|]. split; [exact OPEN|]. split; [exact OK1 | exact Hk].
Qed.

#[using="Type"] Lemma zobj_last_close : forall m m' x q kids nz t tbl size esk1 e esz svs' pb PBS KBS1,
length esz = nz -> Forall (fun e => le_v e = 0) esz ->
opt_pbuf segs m PBS pb ->
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) ->
okids segs fn m kids (map le_v esk1) KBS1 ->
lh_open segs fn m' t tbl size (esk1 ++ with_v e 0 :: esz) svs' ->
agree_on segs ((x, 48) :: concat KBS1 ++ PBS) m m' ->
zobj segs fn m' x q kids (S nz) t tbl size (esk1 ++ with_v e 0 :: esz) svs'
(((x, 48) :: lh_blocks t tbl size (esk1 ++ with_v e 0 :: esz) ++ concat KBS1) ++ PBS).
Proof.
intros m m' x q kids nz t tbl size esk1 e esz svs' pb PBS KBS1 Lz Fz OPB HDR OK OPEN AG.
exists pb, PBS, KBS1, esk1, (with_v e 0 :: esz).
split; [reflexivity|]. split; [cbn; lia|]. split; [apply Forall_cons; [reflexivity | exact Fz]|]. split; [reflexivity|].
split; [| split; [| split; [exact OPEN|]]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; right; apply in_or_app; right; exact Hb].
- eapply rw_cells_agree; [exact HDR | exact AG | exists x, 48; split; [left; reflexivity | cbn; lia]].
- eapply okids_agree; [exact OK | exact AG | intros b Hb; right; apply in_or_app; left; exact Hb].
Qed.

#[using="Type"] Lemma zobj_nil_vals : forall m x q nz t tbl size es svs XBS,
zobj segs fn m x q [] nz t tbl size es svs XBS -> forall e, In e es -> le_v e = 0.
Proof.
intros m x q nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) e He.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1. destruct esk; [| cbn in L1; discriminate].
subst es. cbn in He. exact (proj1 (Forall_forall _ _) Fz e He).
Qed.

#[using="Type"] Lemma zarr_last : forall m x q kids k nz a arr size XBS,
zarr segs fn m x q (kids ++ [k]) nz a arr size XBS ->
exists pb PBS KBS1 bs ps1 v,
XBS = ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ (concat KBS1 ++ bs)) ++ PBS /\
opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz a)]) /\
alist segs fn m [(a, 32); (arr, 8 * size)] a ((ps1 ++ [v]) ++ repeat 0 nz) /\ length ps1 = length kids /\
okids segs fn m kids ps1 KBS1 /\
match k with None => v = 0 /\ bs = [] | Some c => v <> 0 /\ jval segs fn c m bs v 1 end.
Proof.
intros m x q kids k nz a arr size XBS (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
destruct (okids_snoc_inv _ _ _ _ _ _ _ OK) as (ps1 & v & KBS1 & bs & -> & -> & OK1 & Hk).
pose proof (okids_len _ _ _ _ _ _ OK1) as [L1 _].
exists pb, PBS, KBS1, bs, ps1, v.
split; [rewrite EX, concat_snoc; reflexivity|]. split; [exact OPB|]. split; [exact HDR|]. split; [exact AL|].
split; [exact L1|]. split; [exact OK1 | exact Hk].
Qed.

#[using="Type"] Lemma zarr_last_close : forall m m' x q kids nz a arr size ps1 pb PBS KBS1,
opt_pbuf segs m PBS pb ->
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz a)]) ->
okids segs fn m kids ps1 KBS1 ->
alist segs fn m' [(a, 32); (arr, 8 * size)] a ((ps1 ++ [0]) ++ repeat 0 nz) ->
agree_on segs ((x, 48) :: concat KBS1 ++ PBS) m m' ->
zarr segs fn m' x q kids (S nz) a arr size (((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS1) ++ PBS).
Proof.
intros m m' x q kids nz a arr size ps1 pb PBS KBS1 OPB HDR OK AL AG.
exists pb, PBS, KBS1, ps1. split; [reflexivity|].
split; [| split; [| split; [rewrite <- app_assoc in AL; cbn [app] in AL; exact AL | ]]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; right; apply in_or_app; right; exact Hb].
- eapply rw_cells_agree; [exact HDR | exact AG | exists x, 48; split; [left; reflexivity | cbn; lia]].
- eapply okids_agree; [exact OK | exact AG | intros b Hb; right; apply in_or_app; left; exact Hb].
Qed.

#[using="Type"] Lemma zarr_nil_vals : forall m x q nz a arr size XBS,
zarr segs fn m x q [] nz a arr size XBS ->
exists pb PBS, XBS = [(x, 48); (a, 32); (arr, 8 * size)] ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz a)]) /\
alist segs fn m [(a, 32); (arr, 8 * size)] a (repeat 0 nz).
Proof.
intros m x q nz a arr size XBS (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
destruct (okids_nil_inv _ _ _ _ _ OK) as [-> ->]. exists pb, PBS. cbn [concat app] in EX.
split; [exact EX|]. split; [exact OPB|]. split; [exact HDR | exact AL].
Qed.

#[using="Type"] Lemma zobj_nil_shape : forall m x q nz t tbl size es svs XBS,
zobj segs fn m x q [] nz t tbl size es svs XBS ->
exists pb PBS, XBS = ((x, 48) :: lh_blocks t tbl size es) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\ (forall e, In e es -> le_v e = 0) /\ length es = nz.
Proof.
intros m x q nz t tbl size es svs XBS Z0. pose proof (zobj_nil_vals _ _ _ _ _ _ _ _ _ _ Z0) as VZ.
destruct Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
destruct (okids_nil_inv _ _ _ _ _ OK) as [E1 ->]. destruct esk; [| cbn in E1; discriminate]. subst es.
exists pb, PBS. cbn [concat app] in EX. rewrite app_nil_r in EX.
split; [exact EX|]. split; [exact OPB|]. split; [exact HDR|]. split; [exact OPEN|]. split; [exact VZ | cbn; exact Lz].
Qed.

End WithSegs.
