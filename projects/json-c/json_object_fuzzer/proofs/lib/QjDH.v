(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup QCcH QfLs Q0Ek Qtgi Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup.
Import QCcH QfLs Q0Ek Qtgi.
Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma kdepth_in : forall kids s, In (Some s) kids -> sdepth s <= kdepth kids.
Proof.
induction kids as [|o kids IH]; intros s Hin; [destruct Hin|].
rewrite kdepth_cons. destruct Hin as [->|Hin].
- pose proof (kdepth_nonneg kids). lia.
- specialize (IH s Hin). destruct o as [s'|]; [pose proof (sdepth_nonneg s')|]; lia.
Qed.

#[using="Type"] Lemma jshape_ind2 : forall (P : jshape -> Prop),
P Sbool -> (forall u, P (Sdouble u)) -> P Sint -> (forall h, P (Sstr h)) ->
(forall kids, (forall s, In (Some s) kids -> P s) -> P (Sobj kids)) ->
(forall kids, (forall s, In (Some s) kids -> P s) -> P (Sarr kids)) ->
forall s, P s.
Proof.
intros P Hb Hd Hi Hs Ho Ha s.
assert (GEN : forall n t, sdepth t < Z.of_nat n -> P t).
{ induction n as [|n IH]; intros t Ht; [pose proof (sdepth_nonneg t); lia|].
destruct t as [|u| |h|kids|kids]; auto.
- apply Ho. intros s' Hin. apply IH. pose proof (kdepth_in _ _ Hin). rewrite sdepth_obj in Ht. lia.
- apply Ha. intros s' Hin. apply IH. pose proof (kdepth_in _ _ Hin). rewrite sdepth_arr in Ht. lia. }
apply (GEN (S (Z.to_nat (sdepth s)))). pose proof (sdepth_nonneg s). lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Definition agree_on (BS : list blk) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> in_block BS a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma agree_on_refl : forall BS m, agree_on BS m m.
Proof. intros BS m a _ _. split; [reflexivity | tauto]. Qed.

#[using="Type"] Lemma agree_on_trans : forall BS m1 m2 m3, agree_on BS m1 m2 -> agree_on BS m2 m3 -> agree_on BS m1 m3.
Proof.
intros BS m1 m2 m3 H12 H23 a Ha Hin. destruct (H12 a Ha Hin) as [E1 W1]. destruct (H23 a Ha Hin) as [E2 W2].
split; [congruence | auto].
Qed.

#[using="Type"] Lemma agree_on_incl : forall BS BS' m m', agree_on BS m m' -> incl BS' BS -> agree_on BS' m m'.
Proof.
intros BS BS' m m' H Hincl a Ha (b & Hb & Hr). apply H; [exact Ha|]. exists b. split; [apply Hincl; exact Hb | exact Hr].
Qed.

#[using="Type"] Lemma agree_of_munch : forall BS W m m',
munch W m m' -> wmono segs m m' ->
(forall a n, In (a, n) BS -> disjoint_from W a n) ->
agree_on BS m m'.
Proof.
intros BS W m m' MU WM HD a Ha ([ba bn] & Hb & Hr). cbn in Hr. split.
- apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact (HD _ _ Hb) | lia].
- apply WM.
Qed.

#[using="Type"] Lemma agree_of_heap_pres : forall L LB SP BS m m',
heap_pres L LB SP m m' -> hl_segs L = segs -> incl BS LB -> agree_on BS m m'.
Proof.
intros L LB SP BS m m' HP E Hincl a Ha (b & Hb & Hr). rewrite <- E.
exact (HP a Ha ltac:(right; right; exists b; split; [apply Hincl; exact Hb | exact Hr])).
Qed.

#[using="Type"] Lemma agree_of_heap_presx : forall L X LB SP BS m m',
heap_presx L X LB SP m m' -> hl_segs L = segs -> incl BS LB -> agree_on BS m m'.
Proof.
intros L X LB SP BS m m' HP E Hincl a Ha (b & Hb & Hr). rewrite <- E.
exact (HP a Ha ltac:(right; right; exists b; split; [apply Hincl; exact Hb | exact Hr])).
Qed.

Definition inside_blocks (BS : list blk) (A n : Z) : Prop :=
exists a k, In (a, k) BS /\ a <= A /\ A + n <= a + k.

#[using="Type"] Lemma inside_blocks_incl : forall BS BS' A n, inside_blocks BS A n -> incl BS BS' -> inside_blocks BS' A n.
Proof. intros BS BS' A n (a & k & H & H1 & H2) Hi. exists a, k. auto. Qed.

#[using="Type"] Lemma bytes_at_agree : forall BS m m' A bs,
bytes_at segs m A bs -> agree_on BS m m' -> inside_blocks BS A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof.
intros BS m m' A bs (H0 & H1 & HB) AG (a & k & Hin & Ha & Hk). split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (AG (A + Z.of_nat i) ltac:(lia) ltac:(exists (a, k); split; [exact Hin| cbn; lia])) as [E _].
rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma wr_at_agree : forall BS m m' A n,
wr_at segs m A n -> agree_on BS m m' -> inside_blocks BS A n -> wr_at segs m' A n.
Proof.
intros BS m m' A n (H0 & H1 & HW) AG (a & k & Hin & Ha & Hk). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (AG (A + i) ltac:(lia) ltac:(exists (a, k); split; [exact Hin| cbn; lia])) as [_ W].
apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rw_cells_agree : forall BS m m' A cs,
rw_cells segs m A cs -> agree_on BS m m' -> inside_blocks BS A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
intros BS m m' A cs [[Hwf HB] HW] AG HI. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HI.
- eapply wr_at_agree; eauto.
Qed.

#[using="Type"] Lemma cstr_agree : forall BS m m' a n s,
cstr segs m a n s -> agree_on BS m m' -> In (a, n) BS -> 0 <= n -> cstr segs m' a n s.
Proof.
intros BS m m' a n s (H1 & H2 & junk & H3) AG Hin Hn. split; [exact H1|]. split; [exact H2|]. exists junk.
eapply rw_cells_agree; [exact H3 | exact AG |]. exists a, n. split; [exact Hin|].
destruct H3 as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
Qed.

#[using="Type"] Lemma pbuf_core_agree : forall BS m m' pb buf bpos size content,
pbuf_core segs m pb buf bpos size content -> agree_on BS m m' ->
In (pb, 16) BS -> In (buf, size) BS ->
pbuf_core segs m' pb buf bpos size content.
Proof.
intros BS m m' pb buf bpos size content (H1 & H2 & H3 & H4 & H5) AG Hpb Hbuf.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
- eapply rw_cells_agree; [exact H4 | exact AG | exists pb, 16; split; [exact Hpb | cbn; lia]].
- eapply rw_cells_agree; [exact H5 | exact AG | exists buf, size; split; [exact Hbuf | cbn; lia]].
Qed.

#[using="Type"] Lemma pbuf_agree : forall BS m m' PBS pb,
pbuf segs m PBS pb -> agree_on BS m m' -> incl PBS BS -> pbuf segs m' PBS pb.
Proof.
intros BS m m' PBS pb (buf & bpos & size & pre & post & E & L & C) AG Hi. subst PBS.
exists buf, bpos, size, pre, post. split; [reflexivity|]. split; [exact L|].
eapply pbuf_core_agree; [exact C | exact AG | apply Hi; left; reflexivity | apply Hi; right; left; reflexivity].
Qed.

#[using="Type"] Lemma pbufw_agree : forall BS m m' PBS pb,
pbufw segs m PBS pb -> agree_on BS m m' -> incl PBS BS -> pbufw segs m' PBS pb.
Proof.
intros BS m m' PBS pb (buf & bpos & size & content & E & C) AG Hi. subst PBS.
exists buf, bpos, size, content. split; [reflexivity|].
eapply pbuf_core_agree; [exact C | exact AG | apply Hi; left; reflexivity | apply Hi; right; left; reflexivity].
Qed.

#[using="Type"] Lemma opt_pbuf_agree : forall BS m m' PBS pb,
opt_pbuf segs m PBS pb -> agree_on BS m m' -> incl PBS BS -> opt_pbuf segs m' PBS pb.
Proof.
intros BS m m' PBS pb [H|[Hp H]] AG Hi; [left; exact H | right]. split; [exact Hp|]. eapply pbufw_agree; eauto.
Qed.

#[using="Type"] Lemma alist_agree : forall BS m m' ABS a ps,
alist segs fn m ABS a ps -> agree_on BS m m' -> incl ABS BS -> alist segs fn m' ABS a ps.
Proof.
intros BS m m' ABS a ps (arr & size & junk & E & H1 & H2 & H3 & H4) AG Hi. subst ABS.
exists arr, size, junk. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split.
- eapply rw_cells_agree; [exact H3 | exact AG | exists a, 32; split; [apply Hi; left; reflexivity | cbn; lia]].
- eapply rw_cells_agree; [exact H4 | exact AG | exists arr, (8 * size); split; [apply Hi; right; left; reflexivity |]].
destruct H4 as [[Hwf _] _]. apply cells_wf_app in Hwf as [_ Hwf]. cbn in Hwf. destruct Hwf as [Hwf _].
rewrite cells_size_app. cbn [cells_size csize]. rewrite Nat.add_0_r.
assert (LM : forall l : list Z, cells_size (map (fun p : Z => C8 (Z_to_bv 64 p)) l) = (8 * length l)%nat)
by (induction l as [|x l IHl]; [reflexivity | cbn [map cells_size csize length]; rewrite IHl; lia]).
rewrite LM. lia.
Qed.

#[using="Type"] Lemma slot_cells_size : forall s, cells_size (slot_cells s) = 40%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma lh_openf_agree : forall BS m m' ffn t tbl size es svs,
lh_openf segs fn ffn m t tbl size es svs -> agree_on BS m m' -> incl (lh_blocks t tbl size es) BS ->
lh_openf segs fn ffn m' t tbl size es svs.
Proof.
intros BS m m' ffn t tbl size es svs (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen) AG Hi.
split; [| split; [| split; [exact LINK | split; [| split; [exact Hsz | split; [exact Hcnt | exact Hlen]]]]]].
- unfold lh_hdrf in *. eapply rw_cells_agree; [exact HDR | exact AG |]. exists t, 56. split; [apply Hi; left; reflexivity | cbn; lia].
- intros i s E. pose proof (proj1 (nth_error_Some svs i) ltac:(rewrite E; discriminate)) as Hix.
eapply rw_cells_agree; [exact (SL i s E) | exact AG |]. exists tbl, (40 * size). split; [apply Hi; right; left; reflexivity|].
rewrite slot_cells_size. unfold ent_addr. lia.
- unfold lh_keys in *. rewrite Forall_forall in *. intros e He. pose proof (KEYS e He) as HK.
eapply cstr_agree; [exact HK | exact AG | | destruct HK as (HK1 & _); lia].
apply Hi. unfold lh_blocks. right; right. apply in_map_iff. exists e. split; [reflexivity | exact He].
Qed.

#[using="Type"] Lemma lh_open_agree : forall BS m m' t tbl size es svs,
lh_open segs fn m t tbl size es svs -> agree_on BS m m' -> incl (lh_blocks t tbl size es) BS ->
lh_open segs fn m' t tbl size es svs.
Proof. intros. eapply lh_openf_agree; eassumption. Qed.

#[using="Type"] Lemma lhtab2_agree : forall BS m m' TBS t kvs,
lhtab2 segs fn m TBS t kvs -> agree_on BS m m' -> incl TBS BS -> lhtab2 segs fn m' TBS t kvs.
Proof.
intros BS m m' TBS t kvs (tbl & size & es & svs & Hkvs & E & OPEN) AG Hi. subst TBS.
exists tbl, size, es, svs. split; [exact Hkvs|]. split; [reflexivity|]. eapply lh_open_agree; eassumption.
Qed.

#[using="Type"] Lemma jval_agree : forall s BS m m' BS0 p rc,
jval segs fn s m BS0 p rc -> agree_on BS m m' -> incl BS0 BS -> jval segs fn s m' BS0 p rc.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2;
intros BS m m' BS0 p rc J AG Hi;
destruct J as (pb & PBS & REST & EBS & OPB & J); cbn [jval]; exists pb, PBS, REST;
(split; [exact EBS|]); (split; [eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; apply Hi; rewrite EBS; apply in_or_app; right; exact Hb] |]);
assert (HiR : incl REST BS) by (intros b Hb; apply Hi; rewrite EBS; apply in_or_app; left; exact Hb).
- destruct J as (b & junk & ER & H). exists b, junk. split; [exact ER|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
- destruct u.
+ destruct J as (bits & ud & udn & uds & ER & HU & H & HC). exists bits, ud, udn, uds. split; [exact ER|]. split; [exact HU|]. split.
* eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
* eapply cstr_agree; [exact HC | exact AG | apply HiR; rewrite ER; right; left; reflexivity | destruct HC as (HC1 & _); lia].
+ destruct J as (bits & ER & HS & H). exists bits. split; [exact ER|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
- destruct J as (cty & v & junk & ER & HC & H). exists cty, v, junk. split; [exact ER|]. split; [exact HC|].
eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
- destruct h.
+ destruct J as (len & pd & pdn & str & junk2 & ER & HL & HS & HP & H & HD).
exists len, pd, pdn, str, junk2. split; [exact ER|]. split; [exact HL|]. split; [exact HS|]. split; [exact HP|]. split.
* eapply rw_cells_agree; [exact H | exact AG | exists p, 56; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
* eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [apply HiR; rewrite ER; right; left; reflexivity |]].
destruct HD as [[Hwf _] _]. cbn in Hwf. cbn [cells_size csize]. lia.
+ destruct J as (len & str & junk & ER & HL & HS & H). exists len, str, junk. split; [exact ER|]. split; [exact HL|]. split; [exact HS|].
eapply rw_cells_agree; [exact H | exact AG | exists p, (str_objsize len); split; [apply HiR; rewrite ER; left; reflexivity |]].
rewrite cells_size_app. cbn [cells_size csize jhdr_cells]. unfold str_objsize. lia.
- destruct J as (t & TBS & kvs & KBS & ER & H & HT & L1 & L2 & KIDS). exists t, TBS, kvs, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply lhtab2_agree; [exact HT | exact AG | intros b Hb; apply HiR; rewrite ER; right; apply in_or_app; left; exact Hb].
+ assert (HiK : incl (concat KBS) BS) by (intros b Hb; apply HiR; rewrite ER; right; apply in_or_app; right; exact Hb).
clear ER H HT HiR L1 L2 OPB EBS Hi.
revert kvs KBS KIDS HiK. induction kids as [|k kids IH]; intros [|[kk v] kvs] [|bs KBS] KIDS HiK; try exact KIDS.
cbn in HiK. destruct KIDS as [K1 K2]. split.
* destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply (IHk s' ltac:(left; reflexivity)); [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
* apply IH; [intros s'' Hin; apply IHk; right; exact Hin | exact K2 | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
- destruct J as (a & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). exists a, ABS, ps, KBS.
split; [exact ER|]. split; [|split; [|split; [exact L1 | split; [exact L2|]]]].
+ eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply HiR; rewrite ER; left; reflexivity | cbn; lia]].
+ eapply alist_agree; [exact HA | exact AG | intros b Hb; apply HiR; rewrite ER; right; apply in_or_app; left; exact Hb].
+ assert (HiK : incl (concat KBS) BS) by (intros b Hb; apply HiR; rewrite ER; right; apply in_or_app; right; exact Hb).
clear ER H HA HiR L1 L2 OPB EBS Hi.
revert ps KBS KIDS HiK. induction kids as [|k kids IH]; intros [|v ps] [|bs KBS] KIDS HiK; try exact KIDS.
cbn in HiK. destruct KIDS as [K1 K2]. split.
* destruct k as [s'|]; [|exact K1]. destruct K1 as [Hv J]. split; [exact Hv|].
eapply (IHk s' ltac:(left; reflexivity)); [exact J | exact AG | intros b Hb; apply HiK; apply in_or_app; left; exact Hb].
* apply IH; [intros s'' Hin; apply IHk; right; exact Hin | exact K2 | intros b Hb; apply HiK; apply in_or_app; right; exact Hb].
Qed.

#[using="Type"] Lemma jopt_agree : forall BS m m' s bs p,
jopt segs fn s m bs p -> agree_on BS m m' -> incl bs BS -> jopt segs fn s m' bs p.
Proof.
intros BS m m' [s'|] bs p J AG Hi; cbn in *; [|exact J].
destruct J as [Hp J]. split; [exact Hp|]. eapply jval_agree; eauto.
Qed.

End WithSegs.

End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation TOK_SZ := 72 (only parsing).

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).
Notation lvl_ok := (lvl_ok segs fn).
Notation tstack := (tstack segs).
Notation pbuf := (pbuf segs).
Notation tokrep_with := (tokrep_with segs fn).
Notation tokrep := (tokrep segs fn).
Notation tok_fresh := (tok_fresh segs).

Definition tok_cells_g (mxd fl pb depth stack : Z) (x : tscal) : list cell :=
[C8 (wz 0); C8 (wz pb); C4 (wz mxd); C4 (wz depth);
C4 (ts_isd x); C4 (ts_stpos x); C4 (ts_choff x); C4 (ts_err x);
C4 (ts_ucs x); C4 (ts_high x); C1 (ts_quote x); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (wz stack); C4 (wz fl); C4 (wz 0)].
#[using="Type"] Lemma tok_cells_g32 : forall pb depth stack x, tok_cells pb depth stack x = tok_cells_g 32 0 pb depth stack x.
Proof. reflexivity. Qed.

Definition tokrep_with_g (mxd fl : Z) (m : word -> option byte) (BS : list blk) (tk : Z)
(stack pb depth : Z) (PBS : list blk) (levels : list tlevel) (x : tscal) : Prop :=
BS = (tk, TOK_SZ) :: (stack, 32 * mxd) :: PBS ++ concat (map lvl_blocks levels) /\
Z.of_nat (length levels) = mxd /\ (0 <= depth /\ depth < mxd <= 32 /\ 0 <= fl < 2^32) /\
rw_cells m tk (tok_cells_g mxd fl pb depth stack x) /\
pbuf m PBS pb /\ pb <> 0 /\
tstack m stack levels /\
(forall i l, nth_error levels i = Some l -> Z.of_nat i <= depth -> lvl_ok m l) /\
(forall i l, nth_error levels i = Some l -> depth < Z.of_nat i -> lvl_clean l).
Definition tokrep_g (mxd fl : Z) (m : word -> option byte) (BS : list blk) (tk : Z) : Prop :=
exists stack pb depth PBS levels x, tokrep_with_g mxd fl m BS tk stack pb depth PBS levels x.
Definition tok_fresh_g (mxd fl : Z) (m : word -> option byte) (BS : list blk) (tk : Z) : Prop :=
exists stack pb PBS,
BS = [(tk, TOK_SZ); (stack, 32 * mxd)] ++ PBS /\
(1 <= mxd <= 32 /\ 0 <= fl < 2^32) /\
rw_cells m tk (tok_cells_g mxd fl pb 0 stack (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0))) /\
pbuf m PBS pb /\ pb <> 0 /\
tstack m stack (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)).

#[using="Type"] Lemma tokrep_with_g32 : forall m BS tk stack pb depth PBS levels x,
tokrep_with m BS tk stack pb depth PBS levels x <-> tokrep_with_g 32 0 m BS tk stack pb depth PBS levels x.
Proof.
intros. unfold tokrep_with, tokrep_with_g, tok_cells, tok_cells_g.
split; intros (A & B & C & D); (split; [exact A|]); (split; [exact B|]); (split; [lia| exact D]).
Qed.
#[using="Type"] Lemma tokrep_g32 : forall m BS tk, tokrep m BS tk <-> tokrep_g 32 0 m BS tk.
Proof.
intros. unfold tokrep, tokrep_g. split; intros (stack & pb & depth & PBS & levels & x & H);
exists stack, pb, depth, PBS, levels, x; apply tokrep_with_g32; exact H.
Qed.
#[using="Type"] Lemma tok_fresh_g32 : forall m BS tk, tok_fresh m BS tk <-> tok_fresh_g 32 0 m BS tk.
Proof.
intros. unfold tok_fresh, tok_fresh_g, tok_cells, tok_cells_g. change (Z.to_nat 32 - 1)%nat with 31%nat.
split; intros (stack & pb & PBS & A & H); exists stack, pb, PBS; (split; [exact A|]).
- split; [lia | exact H].
- exact (proj2 H).
Qed.

#[using="Type"] Lemma concat_lvl_blocks_zero : forall n, concat (map lvl_blocks (repeat lvl_zero n)) = [].
Proof. induction n; [reflexivity | cbn; exact IHn]. Qed.

#[using="Type"] Lemma tok_fresh_tokrep_g : forall mxd fl m BS tk, tok_fresh_g mxd fl m BS tk -> tokrep_g mxd fl m BS tk.
Proof.
intros mxd fl m BS tk (stack & pb & PBS & HBS & HB & HT & HP & Hpb & HS).
exists stack, pb, 0, PBS, (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)), (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0)).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- rewrite HBS. cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app].
rewrite concat_lvl_blocks_zero. rewrite app_nil_r. reflexivity.
- cbn [length]. rewrite repeat_length. lia.
- lia.
- exact HT.
- exact HP.
- exact Hpb.
- exact HS.
- intros i l Hl Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn in Hl. injection Hl as <-.
split; [cbn; auto | left; cbn; auto].
- intros i l Hl Hi. destruct i as [|i]; [cbn in Hi; lia|]. cbn [nth_error] in Hl.
apply nth_error_repeat_some in Hl. subst l. apply lvl_zero_clean.
Qed.

End WithSegs.
