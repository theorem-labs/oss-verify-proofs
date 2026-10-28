(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseReaderRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma upd_map_upd_nat : forall {X} (f : Z -> X) (l : list Z) (i : nat) (v : Z),
upd (map f l) i (f v) = map f (upd_nat i v l).
Proof.
intros X f l. induction l as [|a l IH]; intros [|i] v; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.
Lemma upd_nat_app_zero : forall (acc : list Z) (k : nat) (v : Z), (1 <= k)%nat ->
upd_nat (length acc) v (acc ++ repeat 0 k) = (acc ++ [v]) ++ repeat 0 (k - 1).
Proof.
induction acc as [|a acc IH]; intros k v Hk; cbn [length app upd_nat].
- destruct k as [|k]; [lia|]. cbn. rewrite Nat.sub_0_r. reflexivity.
- rewrite IH by exact Hk. reflexivity.
Qed.
Lemma upd_nat_idem : forall (l : list Z) (i : nat) (v w : Z), upd_nat i v (upd_nat i w l) = upd_nat i v l.
Proof. induction l as [|a l IH]; intros [|i] v w; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma u16s_zero : forall k, u16s (map (Z_to_bv 64) (repeat 0 k)) = repeat (Z_to_bv 8 0) (2 * k).
Proof.
induction k as [|k IH]; [reflexivity|].
replace (2 * S k)%nat with (S (S (2 * k))) by lia. cbn [repeat map u16s]. rewrite IH. reflexivity.
Qed.
Lemma weight_nonneg : forall c, -1 <= c -> 0 <= weight c.
Proof. intros c Hc. unfold weight. destruct (Z.eqb_spec c (-1)); lia. Qed.
Lemma wsum_nonneg : forall l, Forall (fun c => -1 <= c) l -> 0 <= wsum l.
Proof.
induction l as [|a l IH]; intros H; cbn [wsum]; [lia|].
apply Forall_cons_iff in H as [Ha Hl]. pose proof (weight_nonneg a Ha). specialize (IH Hl). lia.
Qed.
Lemma wsum_bound : forall l c, Forall (fun c => -1 <= c) l -> In c l -> c <= wsum l.
Proof.
induction l as [|a l IH]; intros c H Hin; [destruct Hin|].
apply Forall_cons_iff in H as [Ha Hl]. cbn [wsum].
pose proof (weight_nonneg a Ha). pose proof (wsum_nonneg l Hl).
destruct Hin as [<-|Hin].
- unfold weight in *. destruct (Z.eqb_spec a (-1)); lia.
- specialize (IH c Hl Hin). lia.
Qed.
Lemma valid_ncount_short : forall nc msv tl, valid_ncount nc msv tl ->
Forall (fun c => - 32768 <= c < 32768) nc.
Proof.
intros nc msv tl (HL & HM & HT & HGE & _ & HZ & HS).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in HT.
assert (P : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
assert (GE : forall j, (j <= Z.to_nat msv)%nat -> -1 <= nth j nc 0).
{ intros j Hj. specialize (HGE (Z.of_nat j) ltac:(lia)). unfold Znth in HGE. rewrite Nat2Z.id in HGE. exact HGE. }
assert (FA : Forall (fun c => -1 <= c) (firstn (Z.to_nat (msv + 1)) nc)).
{ apply Forall_forall. intros c Hc. apply In_nth with (d := 0) in Hc. destruct Hc as (j & Hj & <-).
rewrite firstn_length in Hj. rewrite nth_firstn. destruct (Nat.ltb_spec j (Z.to_nat (msv + 1))); [|lia].
apply GE. lia. }
apply Forall_forall. intros c Hc. apply In_nth with (d := 0) in Hc. destruct Hc as (i & Hi & <-).
destruct (Z_le_gt_dec (Z.of_nat i) msv) as [L|G].
- pose proof (GE i ltac:(lia)).
assert (IN : In (nth i nc 0) (firstn (Z.to_nat (msv + 1)) nc)).
{ replace (nth i nc 0) with (nth i (firstn (Z.to_nat (msv + 1)) nc) 0).
- apply nth_In. rewrite firstn_length. lia.
- rewrite nth_firstn. destruct (Nat.ltb_spec i (Z.to_nat (msv + 1))); [reflexivity| lia]. }
pose proof (wsum_bound _ _ FA IN). lia.
- specialize (HZ (Z.of_nat i) ltac:(lia)). unfold Znth in HZ. rewrite Nat2Z.id in HZ. lia.
Qed.
Lemma write_bound_nonneg : forall msv tl, 0 <= msv -> 0 <= tl -> 0 <= write_bound msv tl.
Proof.
intros msv tl Hm Ht. unfold write_bound, FSE_NCOUNTBOUND. destruct (msv =? 0); [lia|].
assert (0 <= ((msv + 1) * tl + 4 + 2) / 8) by (apply Z.div_pos; nia). lia.
Qed.
Lemma fse_fill_step : forall f pl size s maxSV rw acc, s < maxSV -> 0 < rw ->
fse_fill (S f) pl size s maxSV rw acc =
(let '(n, size') := int32Range pl size (-1) rw in
fse_fill f pl size' (s + 1) maxSV (if n <? 0 then rw - 1 else rw - n) (acc ++ [n])).
Proof.
intros. cbn [fse_fill].
replace (s <? maxSV) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <? rw) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma fse_fill_stop : forall f pl size s maxSV rw acc, (maxSV <= s \/ rw <= 0) ->
fse_fill f pl size s maxSV rw acc = (acc, rw, size).
Proof.
intros [|f] pl size s maxSV rw acc H; cbn [fse_fill]; [reflexivity|].
destruct (Z.ltb_spec s maxSV); destruct (Z.ltb_spec 0 rw); cbn [andb]; try reflexivity. lia.
Qed.
Lemma fseB_tail_loop_step : forall f pl size acc,
fseB_tail_loop (S f) pl size acc =
(let '(c, size') := uint32Range pl size 0 255 in fseB_tail_loop f pl size' (acc ++ [to_byte c])).
Proof. reflexivity. Qed.
Lemma fseA_unfold : forall pl n,
exists tl r1 msv r2 pre rw r3 v' r4 bsz r5,
uint32Range pl n FSE_MIN_TABLELOG FSE_MAX_TABLELOG = (tl, r1)
/\ uint32Range pl r1 0 255 = (msv, r2)
/\ fse_fill 256 pl r2 0 msv (2^tl - 1) [] = (pre, rw, r3)
/\ (rw = 0 -> exists c, uint32Range pl r3 0 1 = (c, r4) /\ v' = (if c =? 1 then -1 else rw + 1))
/\ (rw <> 0 -> v' = rw + 1 /\ r4 = r3)
/\ (let nc := Zupd msv v' (pre ++ repeat 0 (256 - length pre)) in
uint32Range pl r4 (hdrSize nc msv tl) 512 = (bsz, r5)
/\ fseA pl n = (tl, msv, nc, fse_data nc msv tl, hdrSize nc msv tl, bsz, r5)).
Proof.
intros pl n. unfold fseA.
destruct (uint32Range pl n FSE_MIN_TABLELOG FSE_MAX_TABLELOG) as [tl r1] eqn:E1.
destruct (uint32Range pl r1 0 255) as [msv r2] eqn:E2.
destruct (fse_fill 256 pl r2 0 msv (2^tl - 1) []) as [[pre rw] r3] eqn:E3.
destruct (Z.eqb_spec (rw + 1) 1) as [E|E].
- destruct (uint32Range pl r3 0 1) as [c r4] eqn:EC.
destruct (uint32Range pl r4 (hdrSize (Zupd msv (if c =? 1 then -1 else rw + 1) (pre ++ repeat 0 (256 - length pre))) msv tl) 512) as [bsz r5] eqn:EB.
exists tl, r1, msv, r2, pre, rw, r3, (if c =? 1 then -1 else rw + 1), r4, bsz, r5.
split; [reflexivity|]. split; [exact E2|]. split; [exact E3|].
split; [intros _; exists c; split; [exact EC| reflexivity]|]. split; [intros; lia|].
cbv zeta. split; [exact EB| reflexivity].
- destruct (uint32Range pl r3 (hdrSize (Zupd msv (rw + 1) (pre ++ repeat 0 (256 - length pre))) msv tl) 512) as [bsz r5] eqn:EB.
exists tl, r1, msv, r2, pre, rw, r3, (rw + 1), r3, bsz, r5.
split; [reflexivity|]. split; [exact E2|]. split; [exact E3|].
split; [intros; lia|]. split; [intros _; split; reflexivity|].
cbv zeta. split; [exact EB| reflexivity].
Qed.
