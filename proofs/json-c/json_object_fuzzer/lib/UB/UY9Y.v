(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7zy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7zy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTEu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QId5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QId5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULch.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3rf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3rf.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SER_GETSTR : Z := 0x265bc.

#[using="Type"] Lemma agree_of_munchX : forall BS W m m',
munch W m m' -> wmono rsegs m m' -> (forall a k x, In (a, k) BS -> a <= x < a + k -> outside W x) -> agree_on rsegs BS m m'.
Proof.
intros BS W m m' MU WM HO x Hx (b & Hb & Hr). destruct b as [a k]. cbn in Hr. split.
- apply MU. rewrite wa_unsigned by lia. exact (HO a k x Hb Hr).
- apply WM.
Qed.

#[using="Type"] Lemma hdr_set_pb : forall m m' p (c1 c2 c3 c5 c6 : cell) (pb0 pb : Z) cs,
csize c1 = 4%nat -> csize c2 = 4%nat -> csize c3 = 8%nat ->
rw_cells rsegs m p ([c1; c2; c3; C8 (wz pb0); c5; c6] ++ cs) ->
munch [(p + 16, p + 24)] m m' -> wmono rsegs m m' -> rw_cells rsegs m' (p + 16) [C8 (wz pb)] ->
rw_cells rsegs m' p ([c1; c2; c3; C8 (wz pb); c5; c6] ++ cs).
Proof.
intros m m' p c1 c2 c3 c5 c6 pb0 pb cs S1 S2 S3 H MU WM H16.
apply (proj1 (rw_cells_app rsegs m p [c1; c2; c3] _)) in H as [HA H]. cbn [cells_size Nat.add] in H. rewrite S1, S2, S3 in H. cbn in H.
apply (proj1 (rw_cells_app rsegs m (p + Z.of_nat 16) [C8 (wz pb0)] _)) in H as [_ HB]. cbn [cells_size csize Nat.add] in HB.
apply (proj2 (rw_cells_app rsegs m' p [c1; c2; c3] _)). split.
- eapply rw_cells_transport; [exact HA | exact MU | exact WM | cbn [cells_size Nat.add disjoint_from]; rewrite S1, S2, S3; cbn; lia].
- cbn [cells_size Nat.add]. rewrite S1, S2, S3. change (4 + (4 + (8 + 0)))%nat with 16%nat.
apply (proj2 (rw_cells_app rsegs m' (p + Z.of_nat 16) [C8 (wz pb)] _)). split.
+ replace (p + Z.of_nat 16) with (p + 16) by lia. exact H16.
+ cbn [cells_size csize Nat.add]. eapply rw_cells_transport; [exact HB | exact MU | exact WM | cbn [disjoint_from]; lia].
Qed.

Section Node.
Variable fn : fnaddrs.

#[using="Type"] Lemma kids_okv_agree : forall m m' BS kids kvs KBS,
kids_okv rsegs fn m kids kvs KBS -> agree_on rsegs BS m m' -> incl (concat KBS) BS -> kids_okv rsegs fn m' kids kvs KBS.
Proof.
intros m m' BS kids. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS AG HiK; try exact KIDS.
rewrite kids_okv_cons in KIDS |- *. cbn in HiK. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
- apply IH; [exact K2 | exact AG | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.
#[using="Type"] Lemma kids_okp_agree : forall m m' BS kids ps KBS,
kids_okp rsegs fn m kids ps KBS -> agree_on rsegs BS m m' -> incl (concat KBS) BS -> kids_okp rsegs fn m' kids ps KBS.
Proof.
intros m m' BS kids. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS AG HiK; try exact KIDS.
rewrite kids_okp_cons in KIDS |- *. cbn in HiK. destruct KIDS as [K1 K2]. split.
- destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
- apply IH; [exact K2 | exact AG | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma jnode_agree : forall s m m' BS REST p rc pb0,
jnode rsegs fn s m REST p rc pb0 -> agree_on rsegs BS m m' -> incl REST BS -> jnode rsegs fn s m' REST p rc pb0.
Proof.
intros s m m' BS REST p rc pb0 J AG Hi. destruct s as [|[|]| |[|]|kids|kids]; cbn in J |- *.
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. split.
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply cstr_agree; [exact HC | exact AG | apply Hi; rewrite ER; right; left; reflexivity | destruct HC as (HC1 & _); lia].
- destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD).
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [apply Hi; rewrite ER; right; left; reflexivity |]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
- destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, (str_objsize len); split; [apply Hi; rewrite ER; left; reflexivity |]].
cbn [cells_size csize]. unfold str_objsize. lia.
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply lhtab2_agree; [exact HT | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; left; exact Hb].
+ eapply kids_okv_agree; [exact KIDS | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply Hi; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply alist_agree; [exact HA | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; left; exact Hb].
+ eapply kids_okp_agree; [exact KIDS | exact AG | intros b Hb; apply Hi; rewrite ER; right; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma jnode_set_pb : forall s m m' REST p rc pb0 pb,
jnode rsegs fn s m REST p rc pb0 ->
munch [(p + 16, p + 24)] m m' -> wmono rsegs m m' -> rw_cells rsegs m' (p + 16) [C8 (wz pb)] ->
(forall a k, In (a, k) (tl REST) -> a + k <= p + 16 \/ p + 24 <= a) ->
jnode rsegs fn s m' REST p rc pb.
Proof.
intros s m m' REST p rc pb0 pb J MU WM H16 DISJ.
assert (AGx : forall rest, (forall a k, In (a, k) rest -> a + k <= p + 16 \/ p + 24 <= a) -> agree_on rsegs rest m m').
{ intros rest D. eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx. cbn. pose proof (D a k Hin). lia. }
destruct s as [|[|]| |[|]|kids|kids]; cbn in J |- *; unfold jhdr_cells in *.
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|]. cbn [app] in H |- *.
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. rewrite ER in DISJ. cbn [tl] in DISJ. split.
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply cstr_agree; [exact HC | apply (AGx _ DISJ) | left; reflexivity | destruct HC as (HC1 & _); lia].
- destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD). rewrite ER in DISJ. cbn [tl] in DISJ.
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply rw_cells_agree; [exact HD | apply (AGx _ DISJ) | exists pd, pdn; split; [left; reflexivity|]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
- destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_; _]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS. rewrite ER in DISJ. cbn [tl] in DISJ.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply lhtab2_agree; [exact HT | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; left; exact Hb].
+ eapply kids_okv_agree; [exact KIDS | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS. rewrite ER in DISJ. cbn [tl] in DISJ.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply (hdr_set_pb m m' p _ _ _ _ _ pb0 pb [_]); [reflexivity | reflexivity | reflexivity | exact H | exact MU | exact WM | exact H16].
+ eapply alist_agree; [exact HA | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; left; exact Hb].
+ eapply kids_okp_agree; [exact KIDS | apply (AGx _ DISJ) | intros b Hb; apply in_or_app; right; exact Hb].
Qed.
End Node.

Section Top.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).

#[using="Type"] Lemma rest_sep : forall A pb buf cap REST LB m md a k,
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB) m md -> In (a, k) REST ->
(a + k <= pb \/ pb + 16 <= a) /\ (a + k <= buf \/ buf + cap <= a) /\ 0 < a /\ a + k <= alloc_ceiling.
Proof.
intros A pb buf cap REST LB m md a k HP Hin.
assert (HinL : In (a, k) ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB)) by (right; right; apply in_or_app; left; exact Hin).
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn [map blk_addr] in ND.
assert (Ha : In a (map blk_addr (REST ++ LB))) by (rewrite in_map_iff; exists (a, k); split; [reflexivity | apply in_or_app; left; exact Hin]).
inversion ND as [|x l Hpb ND1]; subst. inversion ND1 as [|y l' Hbuf ND2]; subst.
assert (N1 : pb <> a) by (intros ->; apply Hpb; right; exact Ha).
assert (N2 : buf <> a) by (intros ->; apply Hbuf; exact Ha).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP ltac:(left; reflexivity) HinL N1) as D1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP ltac:(right; left; reflexivity) HinL N2) as D2.
pose proof (heap_blk S4L HIx _ _ _ _ a k HP HinL) as (_ & _ & Hlo & Hhi & _).
split; [lia|]. split; [lia|]. split; [exact Hlo | exact Hhi].
Qed.

Definition tojs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (s : jshape) (p rc : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word) (errv' : word) (BS' : list blk),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' ERRNO [C4 errv'] /\
HEAPx A' (BS' ++ LB) m' md' /\
jval rsegs S4F s m' BS' p rc.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB REST : list blk) (lo p rc fl : Z) (s : jshape) (T : TSet).
Let usp := bv_unsigned sp.
Hypothesis LBS : lb_small (REST ++ LB).
Hypothesis FL : flags_ok fl.
Hypothesis SD : sdepth s <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - 32 - ser_budget s.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.
Hypothesis K : forall ms' md', tojs_post ra sp gp (wz TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo s p rc ms' md' ->
realizes rsegs (mkCfg ms' md') T.

Definition top_mem (pb : Z) (m : word -> option byte) (md : Model) : Prop :=
exists (A : AS S4L HIx) (buf cap bpos : Z) (content : list byte) (errv : word) (j0 : list byte),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB) m md /\
pbuf_core rsegs m pb buf bpos cap content /\
jnode rsegs S4F s m REST p rc pb /\
rw_cells rsegs m (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra] /\
rw_cells rsegs m ERRNO [C4 errv] /\
stk rsegs m lo (usp + -32) /\
heap_pres S4L LB usp m0 m /\ model_vm_only md0 md.

#[using="ra sp usp"] Lemma rest_tl_sep : forall A L1 L2 n rest m md a k,
HEAPx A (L1 ++ ((p, n) :: rest) ++ L2) m md -> In (a, k) rest -> a + k <= p \/ p + n <= a.
Proof.
intros A L1 L2 n rest m md a k HP Hin.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr app] in ND. inversion ND as [|x l Hp ND1]; subst.
assert (N1 : a <> p).
{ intros ->. apply Hp. rewrite map_app. apply in_or_app. left. rewrite in_map_iff. exists (p, k). split; [reflexivity | exact Hin]. }
assert (I1 : In (p, n) (L1 ++ ((p, n) :: rest) ++ L2)) by (apply in_or_app; right; left; reflexivity).
assert (I2 : In (a, k) (L1 ++ ((p, n) :: rest) ++ L2)) by (apply in_or_app; right; right; apply in_or_app; left; exact Hin).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP I2 I1 N1). lia.
Qed.

End Top.

Definition jty (s : jshape) : Z :=
match s with Sbool => JT_BOOLEAN | Sdouble _ => JT_DOUBLE | Sint => JT_INT | Sstr _ => JT_STRING | Sobj _ => JT_OBJECT | Sarr _ => JT_ARRAY end.

#[using="Type"] Lemma jty_range : forall s, 0 <= jty s <= 6.
Proof. destruct s; cbn; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY; lia. Qed.

#[using="Type"] Lemma jnode_hdrT : forall fn s m REST p rc pb0, jnode rsegs fn s m REST p rc pb0 ->
exists n udel ud cs rest, REST = (p, n) :: rest /\ 48 <= n /\
rw_cells rsegs m p ([C4 (wz (jty s)); C4 (wz rc); C8 (wz (fn_ofF fn s)); C8 (wz pb0); C8 (wz udel); C8 (wz ud)] ++ cs).
Proof.
intros fn s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn in J.
- destruct J as (b & junk & -> & H). exists 48, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & ud & udn & uds & -> & _ & H & _). exists 48, (fn_free_userdata fn), ud. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & -> & _ & H). exists 48, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (cty & v & junk & -> & _ & H). exists 56, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), 0, 0. eexists. exists []. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct J as (t & TBS & kvs & KBS & -> & H & _). exists 48, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (a & ABS & ps & KBS & -> & H & _). exists 48, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
Qed.

Section TopG.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB REST : list blk) (lo p rc : Z) (s : jshape) (T : TSet).
Let usp := bv_unsigned sp.
Hypothesis SD : sdepth s <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - 16 - ser_budget s.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.
Hypothesis K : forall ms' md', tojs_post HIx ra sp gp (wz TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo s p rc ms' md' ->
realizes rsegs (mkCfg ms' md') T.

Definition topg_mem (pb : Z) (m : word -> option byte) (md : Model) : Prop :=
exists (A : AS S4L HIx) (buf cap bpos : Z) (content : list byte) (errv : word),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB) m md /\
pbuf_core rsegs m pb buf bpos cap content /\
jnode rsegs S4F s m REST p rc pb /\
rw_cells rsegs m (usp + -16) [C8 s0; C8 ra] /\
rw_cells rsegs m ERRNO [C4 errv] /\
stk rsegs m lo (usp + -16) /\
heap_pres S4L LB usp m0 m /\ model_vm_only md0 md.

#[using="Type"] Lemma not_oldG : forall A P m md a n k, HEAPx A (P ++ LB) m md -> In (a, n) P -> ~ In (a, k) LB.
Proof. intros A P m md a n k HP Hin. eapply nodup_prefix_suffix; [exact (heap_blk_nodup S4L HIx _ _ _ _ HP) | exact Hin]. Qed.

#[using="RC__ ra"] Lemma factsG : 0 <= usp < 2^64 /\ 0 <= sdepth s /\ flags_ok 1.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof (sdepth_nonneg s).
split; [unfold usp; lia|]. split; [lia|]. split; [lia | reflexivity].
Qed.

#[using="fc LOS K"] Lemma topg_finish : forall pb m md (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
topg_mem pb m md -> fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until fc'. intros (A & buf & cap & bpos & content & errv & HP & PB & JN & FR & ERR & ST & HPR & VM) FS' FR'.
pose proof factsG as (SPR & SD0 & _). pose proof LOS as LOS'. unfold ser_budget in LOS'.
apply K. unfold tojs_post.
exists m, A, a0, errv, (REST ++ [(pb, PB_SZ); (buf, cap)]).
split; [apply ret_statew_intro; [exact FS' | intros _; exact FR']|].
split; [exact VM|].
split. { unfold usp in *. release_frame FR ST (bv_unsigned sp). exact ST. }
split; [exact HPR|]. split; [exact ERR|]. split.
- eapply (heap_perm S4L HIx); [exact HP|].
change ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB) with ([(pb, PB_SZ); (buf, cap)] ++ (REST ++ LB)).
rewrite <- (app_assoc REST). apply Permutation_app_swap_app.
- apply (proj2 (jval_split rsegs S4F s m _ p rc)). exists pb, [(pb, PB_SZ); (buf, cap)], REST.
split; [reflexivity|]. split; [| exact JN].
right. pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & _ & Hlo & _).
split; [lia|]. exists buf, bpos, cap, content. split; [reflexivity | exact PB].
Qed.




#[using="fc LO LOS K"] Lemma gs_d5bc : forall pb m md (t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
topg_mem pb m md -> fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR (wz 0x26624) (wz (usp + -16)) gp (wz TP) t0 t1 t2 (wz p) s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (wz 0x26624) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until fc'. intros TM FS' FR'. pose proof TM as TM'.
destruct TM as (A & buf & cap & bpos & content & errv & HP & PB & JN & FR & ERR & ST & HPR & VM).
pose proof factsG as (SPR & SD0 & _). pose proof LOS as LOS'. unfold ser_budget in LOS'.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in HDR as [HDR _].
assert (INp : In (p, n) ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB)) by (right; right; apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF).
unfold TP, ERRNO in *. unfold usp in *. unfold_consts.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
destruct (Z_lt_le_dec (bv_signed r) 0) as [NEG|NNEG].
- symb_run 5%nat (@nil Z) [true].
step. fold_mkR. apply evt_RZ_done.
replace (Z_to_bv 64 (bv_unsigned sp + -16 + 16)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
eapply (topg_finish pb); [exact TM' | | exact FR']. assumption.
- symb_run 11%nat (@nil Z) [false; false; false].
2:{ sc_cbn. rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. cbn -[Z_to_bv bv_unsigned Z.land]. rewrite bv_and_unsigned, !unsigned_lit by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. clear - Hal. Z.div_mod_to_equations. lia. }
step. fold_mkR. apply evt_RZ_done.
replace (Z_to_bv 64 (bv_unsigned sp + -16 + 16)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
eapply (topg_finish pb); [exact TM' | | exact FR']. assumption.
Qed.

#[using="MEMMOVE HEXP HT63 HGOT fc SD LO LOS SPA HT K"] Lemma gs_d5a0 : forall pb m md (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
topg_mem pb m md -> fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (usp + -16)) gp (wz TP) t0 t1 t2 (wz p) s1 (wz pb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (wz 0x26608) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until fc'. intros TM FS' FR'.
destruct TM as (A & buf & cap & bpos & content & errv & HP & PB & JN & FR & ERR & ST & HPR & VM).
pose proof factsG as (SPR & SD0 & FL1). pose proof LOS as LOS'. unfold ser_budget in LOS'.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in HDR as [HDR _]. rewrite (fn_of_S4F s) in HDR.
pose proof (fn_of_range s) as FNR. pose proof (fn_of_even s) as FNE.
assert (INp : In (p, n) ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB)) by (right; right; apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
destruct (rest_sep HIx _ _ _ _ _ _ _ _ p n HP ltac:(rewrite ER; left; reflexivity)) as (Dp1 & Dp2 & _).
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hpbbuf.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb PB_SZ buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hpbbuf) as Hdisj.
pose proof PB as PB'. destruct PB as (Hbp & Hcap & Hln & PBS & PBUF).
unfold TP, ERRNO in *. unfold usp in *. unfold_consts.
pose proof (munch_refl [(buf, buf + 1); (pb + 8, pb + 12)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
symb_run 1%nat [PBRESET] (@nil bool).
call (printbuf_reset_P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m pb buf bpos cap content);
[exact PB' | lia | lia | exact Hal | lia | lia | exact Hdisj | exact MI |].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
match goal with H : pbuf_core rsegs m1 _ _ _ _ _ |- _ => rename H into PB1 end.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: REST ++ LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (AG1 : agree_on rsegs REST m m1).
{ eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx.
destruct (rest_sep HIx _ _ _ _ _ _ _ _ a k HP Hin) as (D1 & D2 & _). cbn. lia. }
assert (JN1 : jnode rsegs S4F s m1 REST p rc pb) by (eapply jnode_agree; [exact JN | exact AG1 | apply incl_refl]).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; apply in_or_app; right; exact Hbb | unfold_consts; lia |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; right; left;
[ exists buf, cap; split; [right; left; reflexivity|]; split; [eapply (not_oldG _ ((pb, PB_SZ) :: (buf, cap) :: REST)); [exact HP | right; left; reflexivity] | lia]
| exists pb, PB_SZ; split; [left; reflexivity|]; split; [eapply (not_oldG _ ((pb, PB_SZ) :: (buf, cap) :: REST)); [exact HP | left; reflexivity] | lia] ]. }
clear MU WM.
symb_run 5%nat (@nil Z) (@nil bool).
step. replace (ret_pc (Z_to_bv 64 (fn_of s))) with (Z_to_bv 64 (fn_of s)) by (symmetry; apply ret_pc_even; [lia | exact FNE]).
fold_mkR. apply evt_RZ_done.
pose proof (serval HIx MEMMOVE HEXP HT63 HGOT s) as SPEC. unfold ser_spec in SPEC.
eapply SPEC with (A := A) (LB := REST ++ LB) (buf := buf) (bpos := 0) (cap := cap) (lo := lo) (errv := errv)
(REST := REST) (p := p) (rc := rc) (pb0 := pb) (lv := 0) (fl := 1); clear SPEC.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia.
- exact HP1.
- exact PB1.
- exact JN1.
- intros b Hb. apply in_or_app. left. exact Hb.
- exact I.
- exact FL1.
- lia.
- lia.
- assumption.
- exact LO.
- lia.
- replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16 * 1) by lia. rewrite <- Zminus_mod_idemp_l, SPA. reflexivity.
- lia.
- assumption.
- reflexivity.
- rewrite unsigned_lit by lia. reflexivity.
- exact FR'.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' (m5 & A5 & r5 & errv5 & buf5 & cap5 & bpos5 & content5 & RS & VM5 & ST5 & HPR5 & ERR5 & HP5 & PB5).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & -> & FS5 & FR5).
rewrite unsigned_lit in ST5, HPR5 by lia.
replace (ret_pc (Z_to_bv 64 157220)) with (Z_to_bv 64 157220) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply (gs_d5bc pb); [| eapply fsaved_trans; [exact FS' | exact FS5] | exact (FR5 FR')].
exists A5, buf5, cap5, bpos5, content5, errv5.
split; [exact HP5|]. split; [exact PB5|].
split. { eapply jnode_agree; [exact JN1 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
split. { eapply (heap_pres_rw_cells S4L); [exact HPR5 | eassumption | left; cbn; lia]. }
split; [exact ERR5|]. split; [exact ST5|].
split; [| eapply model_vm_only_trans; [exact VM | exact VM5]].
eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPR1|].
eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; right; exact Hb].
Qed.

#[using="MEMMOVE HEXP HT63 HGOT SD LO LOS SPA HT FRM K"] Lemma gs_entry : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m md A PBS pb0 errv,
HEAPx A ((REST ++ PBS) ++ LB) m md ->
opt_pbuf rsegs m PBS pb0 -> jnode rsegs S4F s m REST p rc pb0 -> jty s <> JT_STRING ->
stk rsegs m lo usp -> rw_cells rsegs m ERRNO [C4 errv] ->
heap_pres S4L LB usp m0 m -> model_vm_only md0 md ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SER_GETSTR) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP OPB JN NS ST ERR HPR0 VM0.
pose proof factsG as (SPR & SD0 & FL1). pose proof LOS as LOS'. unfold ser_budget in LOS'.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (jnode_hdrT S4F _ _ _ _ _ _ JN) as (n & udel & ud & cs & rest & ER & Hn & HDR).
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in HDR as [HDR _]. rewrite (fn_of_S4F s) in HDR.
pose proof (fn_of_range s) as FNR.
pose proof (jty_range s) as Rty. unfold JT_STRING in NS.
assert (INp : In (p, n) ((REST ++ PBS) ++ LB)) by (apply in_or_app; left; apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP INp) as (_ & Hpal & Hplo & Hphi & _).
assert (DISJ : forall a k, In (a, k) (tl REST) -> a + k <= p + 16 \/ p + 24 <= a).
{ intros a k Hin. rewrite ER in Hin. cbn [tl] in Hin. rewrite ER, <- app_assoc in HP.
pose proof (rest_tl_sep HIx ra sp p A [] (PBS ++ LB) n rest m md a k HP Hin). lia. }
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP INp) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold TP, ERRNO, SER_GETSTR in *. unfold usp in *. unfold_consts. assert (Rp : 1 <= p < 140737488355328) by lia.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 16%nat ST.
destruct OPB as [[Epb0 EPBS] | [Hpb0 PBW]].
-
subst pb0 PBS. rewrite app_nil_r in HP, INp.
symb_run 14%nat [PBNEW] [false; true].
2:{ sc_cbn. den_norm. unfold bv_eqb; cbn [negb]. rewrite ext_val_sx_id by (cbn; rewrite ?u64_of_Z by lia; lia). rewrite ?u64_of_Z by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6.
destruct (Z.eqb_spec (jty s) 6); [lia | reflexivity]. }
2:{ sc_cbn. rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. cbn -[Z_to_bv bv_unsigned Z.land]. rewrite bv_and_unsigned, !unsigned_lit by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. clear - Hpal. Z.div_mod_to_equations. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A (REST ++ LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply heap_pres_trans; [exact HPR0|]. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; apply in_or_app; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
assert (AG1 : agree_on rsegs REST m m1).
{ eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx.
assert (HinL : In (a, k) (REST ++ LB)) by (apply in_or_app; left; exact Hin).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP HinL) as (_ & _ & _ & Hkhi & _). cbn. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi. lia. }
assert (JN1 : jnode rsegs S4F s m1 REST p rc 0) by (eapply jnode_agree; [exact JN | exact AG1 | apply incl_refl]).
clear MU WM AG1.
apply evt_RZ_done.
eapply (printbuf_new_cps HIx) with (A := A) (LB := REST ++ LB) (lo := lo) (errv := errv).
all: rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia.
+ exact HP1.
+ exact ST.
+ exact LO.
+ lia.
+ replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16 * 1) by lia. rewrite <- Zminus_mod_idemp_l, SPA. reflexivity.
+ lia.
+ exact ERR.
+ reflexivity.
+ rewrite unsigned_lit by lia. reflexivity.
+ intros ms2 md2 (m2 & A2 & r & errv2 & RS & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FR2).
rewrite (unsigned_lit (bv_unsigned sp + -16)) in ST2, HPR2 by lia. change (490496 - 164) with 490332 in ERR2.
replace (ret_pc (Z_to_bv 64 157184)) with (Z_to_bv 64 157184) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HDR2 : rw_cells rsegs m2 p [C4 (Z_to_bv 64 (jty s)); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_of s)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 udel); C8 (Z_to_bv 64 ud)]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR2 | exact HDR |]. right; right. exists (p, n). split; [apply in_or_app; left; rewrite ER; left; reflexivity | cbn; lia]. }
assert (FR2' : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
{ eapply (heap_pres_rw_cells S4L); [exact HPR2 | eassumption | left; cbn; lia]. }
assert (JN2 : jnode rsegs S4F s m2 REST p rc 0).
{ eapply jnode_agree; [exact JN1 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPR02 : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; exact Hb]. }
clear dependent m1.
pose proof (munch_refl [(p + 16, p + 24)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
destruct OUT as [[-> HP2] | (Hr & BS0 & PBF & HP2)].
* pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
apply rz_evt; [exact MOK2|].
symb_run 5%nat (@nil Z) (@nil bool).
step. fold_mkR. apply evt_RZ_done.
replace (Z_to_bv 64 (bv_unsigned sp + -16 + 16)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
match goal with H : rw_cells rsegs m3 p _ |- _ => rename H into HDR3 end.
apply K. unfold tojs_post.
exists m3, A2, (Z_to_bv 64 0), errv2, REST.
split; [apply ret_statew_intro; [exact FS2 | intros _; exact (FR2 FRM)]|].
split; [eapply model_vm_only_trans; [exact VM0 | exact VM2]|].
split. { match goal with H : stk rsegs m3 _ _ |- _ => rename H into ST3 end.
match goal with H : rw_cells rsegs m3 (bv_unsigned sp + -16) _ |- _ => release_frame H ST3 (bv_unsigned sp) end. exact ST3. }
split. { eapply heap_pres_trans; [exact HPR02|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; right; exact Hbb | unfold_consts; lia |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; right; left.
exists p, n. split; [apply in_or_app; left; rewrite ER; left; reflexivity|]. split; [eapply (not_oldG _ REST); [exact HP2 | rewrite ER; left; reflexivity] | lia]. }
split; [assumption|].
split. { eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI3]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU).
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; right; left; exists p, n; split; [apply in_or_app; left; rewrite ER; left; reflexivity | lia]. }
apply (proj2 (jval_split rsegs S4F s m3 _ p rc)). exists 0, [], REST. split; [rewrite app_nil_r; reflexivity|]. split; [left; split; reflexivity|].
eapply jnode_set_pb; [exact JN2 | exact MU | exact WM | | exact DISJ].
apply (proj1 (rw_cells_app rsegs m3 p [_; _; _] _)) in HDR3 as [_ H]. apply (proj1 (rw_cells_app rsegs m3 _ [_] _)) in H as [H _].
cbn [cells_size csize Nat.add] in H. replace (p + Z.of_nat 16) with (p + 16) in H by lia. exact H.
* destruct PBF as (buf & bpos & size & pre & post & -> & Lpre & PBc).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
cbn [app] in HP2.
pose proof (heap_blk S4L HIx _ _ _ _ r PB_SZ HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf size HP2 ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
destruct (rest_sep HIx _ _ _ _ _ _ _ _ p n HP2 ltac:(rewrite ER; left; reflexivity)) as (Dp1 & Dp2 & _).
pose proof PBc as PBc'. destruct PBc as (Hbp & Hcap & Hln & PBS2 & PBUF2).
unfold_consts. assert (Rr : 1 <= r < 140737488355328) by lia.
apply rz_evt; [exact MOK2|].
symb_run 2%nat [0x26608]%Z (@nil bool).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
match goal with H : rw_cells rsegs m3 p _ |- _ => rename H into HDR3 end.
apply evt_RZ_done. eapply (gs_d5a0 r); [| exact FS2 | exact (FR2 FRM)].
exists A2, buf, size, bpos, (pre ++ [Z_to_bv 8 0] ++ post), errv2.
split. { eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI3]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU).
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; right; left; exists p, n; split; [right; right; apply in_or_app; left; rewrite ER; left; reflexivity | lia]. }
split. { split; [exact Hbp|]. split; [exact Hcap|]. split; [exact Hln|]. split; assumption. }
split. { eapply jnode_set_pb; [exact JN2 | exact MU | exact WM | | exact DISJ].
apply (proj1 (rw_cells_app rsegs m3 p [_; _; _] _)) in HDR3 as [_ H]. apply (proj1 (rw_cells_app rsegs m3 _ [_] _)) in H as [H _].
cbn [cells_size csize Nat.add] in H. replace (p + Z.of_nat 16) with (p + 16) in H by lia. exact H. }
split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [| eapply model_vm_only_trans; [exact VM0 | exact VM2]].
eapply heap_pres_trans; [exact HPR02|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; right; right; apply in_or_app; right; exact Hbb | unfold_consts; lia |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; right; left.
exists p, n. split; [right; right; apply in_or_app; left; rewrite ER; left; reflexivity|]. split; [eapply (not_oldG _ ((r, PB_SZ) :: (buf, size) :: REST)); [exact HP2 | right; right; rewrite ER; left; reflexivity] | lia].
- destruct PBW as (buf & bpos & cap & content & -> & PB).
rewrite <- app_assoc in HP. cbn [app] in HP.
assert (HPp : HEAPx A ((pb0, PB_SZ) :: (buf, cap) :: REST ++ LB) m md).
{ eapply (heap_perm S4L HIx); [exact HP|]. exact (Permutation_app_swap_app REST [(pb0, PB_SZ); (buf, cap)] LB). }
pose proof (heap_blk S4L HIx _ _ _ _ pb0 PB_SZ HPp ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HPp ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof PB as PB'. destruct PB as (Hbp & Hcap & Hln & PBS2 & PBUF2).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
assert (Rpb : 1 <= pb0 < 140737488355328) by lia.
symb_run 13%nat [0x26608]%Z [false; true].
2:{ sc_cbn. den_norm. unfold bv_eqb; cbn [negb]. rewrite ext_val_sx_id by (cbn; rewrite ?u64_of_Z by lia; lia). rewrite ?u64_of_Z by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6.
destruct (Z.eqb_spec (jty s) 6); [lia | reflexivity]. }
2:{ sc_cbn. rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. cbn -[Z_to_bv bv_unsigned Z.land]. rewrite bv_and_unsigned, !unsigned_lit by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. clear - Hpal. Z.div_mod_to_equations. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
apply evt_RZ_done. eapply (gs_d5a0 pb0); [| apply fsaved_refl | exact FRM].
exists A, buf, cap, bpos, content, errv.
split; [heap_now S4L HIx HPp MU WM MI1|].
split. { split; [exact Hbp|]. split; [exact Hcap|]. split; [exact Hln|]. split; assumption. }
split. { eapply jnode_agree; [exact JN | | apply incl_refl]. eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx.
destruct (rest_sep HIx _ _ _ _ _ _ _ _ a k HPp Hin) as (_ & _ & _ & Hkhi). cbn. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi. lia. }
split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [| exact VM0].
eapply heap_pres_trans; [exact HPR0|]. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HPp | intros bb Hbb; right; right; apply in_or_app; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HPp.
Qed.

#[using="LO LOS HT FRM K"] Lemma gs_string : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m md A PBS pb0 errv (h : bool),
s = Sstr h ->
HEAPx A ((REST ++ PBS) ++ LB) m md ->
opt_pbuf rsegs m PBS pb0 -> jnode rsegs S4F s m REST p rc pb0 ->
stk rsegs m lo usp -> rw_cells rsegs m ERRNO [C4 errv] ->
heap_pres S4L LB usp m0 m -> model_vm_only md0 md ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SER_GETSTR) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until h. intros Es HP OPB JN ST ERR HPR0 VM0.
pose proof factsG as (SPR & SD0 & FL1). pose proof LOS as LOS'. unfold ser_budget in LOS'.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
assert (INp : In (p, n) ((REST ++ PBS) ++ LB)) by (apply in_or_app; left; apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP INp) as (_ & Hpal & Hplo & Hphi & _).
assert (BLK : forall a k, In (a, k) ((REST ++ PBS) ++ LB) -> a + k <= alloc_ceiling).
{ intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP Hin) as (_ & _ & _ & Hhi & _). exact Hhi. }
pose proof JN as JN0. rewrite Es in JN. cbn in JN.
assert (FIN : forall m1 (a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) jk,
munch [(lo, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -16) jk -> cells_size jk = 16%nat -> stk rsegs m1 lo (bv_unsigned sp + -16) ->
evt rsegs (RZ rsegs md T)
(MS (mkR ra sp gp (wz TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m1 (seg_rom rsegs))).
{ intros m1 a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jk MU WM MI1 FR Hjk ST1.
apply evt_RZ_done.
assert (AG : agree_on rsegs ((REST ++ PBS) ++ LB) m m1).
{ eapply agree_of_munchX; [exact MU | exact WM |]. intros a k x Hin Hx. cbn. pose proof (BLK a k Hin). unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
apply K. unfold tojs_post. exists m1, A, a0', errv, (REST ++ PBS).
split; [apply ret_statew_intro; [apply fsaved_refl | intros _; exact FRM]|].
split; [exact VM0|].
split. { unfold usp in *. eapply stk_release in FR; [| exact ST1 | lia]. rewrite Hjk in FR. replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR by lia. exact FR. }
split. { unfold usp in *. eapply heap_pres_trans; [exact HPR0|]. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; apply in_or_app; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold ERRNO; unfold usp in *; unfold_consts; lia]. }
split; [heap_now S4L HIx HP MU WM MI1|].
apply (proj2 (jval_split rsegs S4F s m1 _ p rc)). exists pb0, PBS, REST. split; [reflexivity|]. split.
+ eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb].
+ eapply jnode_agree; [exact JN0 | exact AG | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP INp) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold TP, ERRNO, SER_GETSTR in *. unfold usp in *. unfold_consts. assert (Rp : 1 <= p < 140737488355328) by lia.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 16%nat ST.
destruct h.
- destruct JN as (len & pd & pdn & str & junk2 & ER2 & Hlen & SL & Hpdn & NODE & DATA). unfold jhdr_cells in NODE. cbn [app] in NODE. unfold JT_STRING in NODE.
assert (Rlen : -2147483648 < len < 0) by lia.
symb_run 24%nat (@nil Z) [false; false].
2:{ sc_cbn. rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. cbn -[Z_to_bv bv_unsigned Z.land]. rewrite bv_and_unsigned, !unsigned_lit by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. clear - Hpal. Z.div_mod_to_equations. lia. }
step. fold_mkR. eapply FIN; [exact MU | exact WM | assumption | exact FR | reflexivity | exact ST].
- destruct JN as (len & str & junk1 & ER2 & Hlen & SL & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE. unfold JT_STRING in NODE.
unfold str_objsize in NODE. assert (Rlen : 0 <= len < 2147483648) by lia.
symb_run 22%nat (@nil Z) [false].
2:{ sc_cbn. rewrite (proj2 (Fs.bv_eqb_eq _ _)); [reflexivity|]. apply bv_eq. cbn -[Z_to_bv bv_unsigned Z.land]. rewrite bv_and_unsigned, !unsigned_lit by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. clear - Hpal. Z.div_mod_to_equations. lia. }
step. fold_mkR. eapply FIN; [exact MU | exact WM | assumption | exact FR | reflexivity | exact ST].
Qed.
End TopG.

Section ExportG.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).



#[using="MEMMOVE HEXP HT63 HGOT"] Theorem get_string_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (s : jshape) (p rc lo : Z) (errv : word),
HEAP S4L HIx A (BS ++ LB) m md ->
jval rsegs S4F s m BS p rc ->
sdepth s <= 1000 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - ser_budget s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m ERRNO [C4 errv] ->
tp = wz TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p ->
(forall ms' md', tojs_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo s p rc ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SER_GETSTR) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP J SD ST LO LOS SPA HT ERR -> RA FRM -> K.
destruct (proj1 (jval_split rsegs S4F s m BS p rc) J) as (pb0 & PBS & REST & -> & OPB & JN).
destruct s as [|u| |h|kids|kids] eqn:Es; rewrite <- Es in *.
4: { eapply (gs_string HIx); try eassumption; first [exact I | apply heap_pres_refl | apply model_vm_only_refl]. }
all: eapply (gs_entry HIx MEMMOVE HEXP HT63 HGOT); try eassumption; first [exact I | apply heap_pres_refl | apply model_vm_only_refl | rewrite Es; cbn; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY; lia].
Qed.

#[using="Type"] Theorem get_string_null :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet) (A : AS S4L HIx) (LB : list blk) (lo : Z),
HEAP S4L HIx A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hi_top S4L HIx ->
(forall m1 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> HEAP S4L HIx A LB m1 md -> stk rsegs m1 lo (bv_unsigned sp) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m1 (seg_rom rsegs)) md) T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SER_GETSTR) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until lo. intros HP ST LO LOS SPA HT K.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold SER_GETSTR. word_range sp SPR. unfold_consts.
pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 16%nat ST.
symb_run 12%nat (@nil Z) (@nil bool).
step. fold_mkR. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
try replace (Z_to_bv 64 (bv_unsigned sp + -16 + 16)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply K.
- replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. exact MU.
- exact WM.
- heap_now S4L HIx HP MU WM MI1.
-
eapply stk_release in FR; [| exact ST | lia]. cbn [cells_size csize Nat.add] in FR.
replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR by lia. exact FR.
Qed.
End ExportG.

End RC__1.
