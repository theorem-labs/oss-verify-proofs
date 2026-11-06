(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the plain-model and arithmetic facts of fuzz_reply's send_line walk on IMAGE B
   (lib/B/W_send_line_*.v): one round of the plain model (Prog/send_line_b_c.v sl_run through W_contract.v's
   send_line_cap / sl_cost_run / sl_alloc_run / sl_max_run), the control flags at a live and at a dead controller,
   and the pairwise disjointness of a list of extents.  No image fact: verbatim from image A's
   lib/A/W_send_line_loop.v:37-226 and :728-806 (a working branch 9367674296a), which states them over the
   same W_contract.v names. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* g_capout after one round of the plain model that sends n bytes (W_send_line_cx.v sl_n): doubled past the
   bytes when they do not fit. *)
Definition sl_capn (no n cap : Z) : Z := if cap <? no + n then (no + n) * 2 else cap.

Lemma sl_n_range : forall mx rem, 0 <= mx -> 0 < rem -> 0 < sl_n mx rem <= rem.
Proof.
intros mx rem Hmx Hrem. unfold sl_n.
destruct (Z.eqb_spec mx 0); destruct (Z.ltb_spec mx rem); simpl; lia.
Qed.

(* sl_run: Z.to_nat rem rounds of fuel are enough, more fuel changes nothing. *)
Lemma sl_run_fuel_eq : forall f f' mx no cap rem j o, 0 <= mx -> 0 <= rem ->
(Z.to_nat rem <= f)%nat -> (Z.to_nat rem <= f')%nat ->
send_line_b_c.sl_run f mx no cap rem j o = send_line_b_c.sl_run f' mx no cap rem j o.
Proof.
induction f as [|f IH]; intros f' mx no cap rem j o Hmx Hrem Hf Hf'.
- assert (rem = 0) by lia. subst rem. destruct f'; reflexivity.
- destruct (Z.le_gt_cases rem 0) as [Hle|Hgt].
  + assert (rem = 0) by lia. subst rem. destruct f'; reflexivity.
  + destruct f' as [|f']; [lia|].
    pose proof (sl_n_range mx rem Hmx Hgt) as Hn. unfold sl_n in Hn.
    cbn [send_line_b_c.sl_run]. rewrite (proj2 (Z.leb_gt rem 0) Hgt).
    set (n := if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) in *.
    destruct (cap <? no + n); rewrite (IH f') by lia; reflexivity.
Qed.

Lemma sl_run_fuel : forall f f' mx no cap rem j o, 0 <= mx -> 0 <= rem ->
(Z.to_nat rem <= f)%nat -> (Z.to_nat rem <= f')%nat ->
snd (send_line_b_c.sl_run f mx no cap rem j o) = snd (send_line_b_c.sl_run f' mx no cap rem j o).
Proof. intros. f_equal. apply sl_run_fuel_eq; assumption. Qed.

(* The capacity after the rounds does not depend on the addresses. *)
Lemma sl_run_cap_indep : forall f mx no cap rem j o j' o',
fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
induction f as [|f IH]; intros mx no cap rem j o j' o'; [reflexivity|].
cbn [send_line_b_c.sl_run]. destruct (rem <=? 0); [reflexivity|].
destruct (cap <? _); cbn [fst snd]; apply IH.
Qed.

Lemma send_line_cap_0 : forall mx no cap, send_line_b_c.send_line_cap true mx no cap 0 = cap.
Proof. reflexivity. Qed.

Lemma send_line_cap_step : forall mx no cap rem, 0 <= mx -> 0 < rem ->
send_line_b_c.send_line_cap true mx no cap rem =
send_line_b_c.send_line_cap true mx (no + sl_n mx rem) (sl_capn no (sl_n mx rem) cap) (rem - sl_n mx rem).
Proof.
intros mx no cap rem Hmx Hrem. unfold send_line_b_c.send_line_cap.
pose proof (sl_n_range mx rem Hmx Hrem) as Hn.
replace (Z.to_nat rem) with (S (Z.to_nat rem - 1)) by lia.
cbn [send_line_b_c.sl_run]. rewrite (proj2 (Z.leb_gt rem 0) Hrem).
change (if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) with (sl_n mx rem).
unfold sl_capn. destruct (cap <? no + sl_n mx rem); cbn [fst snd].
- rewrite (sl_run_fuel (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) by lia. apply sl_run_cap_indep.
- rewrite (sl_run_fuel (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) by lia. reflexivity.
Qed.

Section m.
Variable MT : ameter_ops.

Lemma sl_cost_run_0 : forall mx no cap, sl_cost_run MT 0%nat mx no cap 0 = 0.
Proof. reflexivity. Qed.

Lemma sl_cost_run_nonpos_rem : forall f mx no cap rem, rem <= 0 -> sl_cost_run MT f mx no cap rem = 0.
Proof.
intros [|f] mx no cap rem Hrem; [reflexivity|].
cbn [sl_cost_run]. rewrite (proj2 (Z.leb_le rem 0) Hrem). reflexivity.
Qed.

Lemma sl_cost_run_fuel : forall f f' mx no cap rem, 0 <= mx -> 0 <= rem ->
(Z.to_nat rem <= f)%nat -> (Z.to_nat rem <= f')%nat ->
sl_cost_run MT f mx no cap rem = sl_cost_run MT f' mx no cap rem.
Proof.
induction f as [|f IH]; intros f' mx no cap rem Hmx Hrem Hf Hf'.
- assert (rem = 0) by lia. subst rem. destruct f'; reflexivity.
- destruct (Z.le_gt_cases rem 0) as [Hle|Hgt].
  + rewrite !sl_cost_run_nonpos_rem by exact Hle. reflexivity.
  + destruct f' as [|f']; [lia|].
    pose proof (sl_n_range mx rem Hmx Hgt) as Hn. unfold sl_n in Hn.
    cbn [sl_cost_run]. rewrite (proj2 (Z.leb_gt rem 0) Hgt).
    set (n := if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) in *.
    destruct (cap <? no + n); rewrite (IH f') by lia; reflexivity.
Qed.

Lemma sl_cost_run_step : forall mx no cap rem, 0 <= mx -> 0 < rem ->
sl_cost_run MT (Z.to_nat rem) mx no cap rem =
(if cap <? no + sl_n mx rem then mo_malloc MT ((no + sl_n mx rem) * 2) + mo_free MT else 0) +
sl_cost_run MT (Z.to_nat (rem - sl_n mx rem)) mx (no + sl_n mx rem) (sl_capn no (sl_n mx rem) cap) (rem - sl_n mx rem).
Proof.
intros mx no cap rem Hmx Hrem.
pose proof (sl_n_range mx rem Hmx Hrem) as Hn.
replace (Z.to_nat rem) with (S (Z.to_nat rem - 1)) by lia.
cbn [sl_cost_run]. rewrite (proj2 (Z.leb_gt rem 0) Hrem).
change (if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) with (sl_n mx rem).
unfold sl_capn. destruct (cap <? no + sl_n mx rem).
- rewrite (sl_cost_run_fuel (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) by lia. reflexivity.
- rewrite (sl_cost_run_fuel (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) by lia. reflexivity.
Qed.

(* The charge is never negative.  The stated side condition 0 <= no alone does not give it: with mx < 0 a round
   sends n = mx < 0 bytes, no + n may be negative and mo_malloc is nonnegative only at nonnegative sizes.  0 <= mx
   (with 0 <= no) is enough; so is 0 <= cap alone (a growth happens only when cap < no + n). *)
Lemma sl_cost_run_nonneg_cap : forall f mx no cap rem, ameter_laws MT -> 0 <= cap ->
0 <= sl_cost_run MT f mx no cap rem.
Proof.
intros f mx no cap rem ML. revert mx no cap rem.
induction f as [|f IH]; intros mx no cap rem Hcap; [cbn; lia|].
cbn [sl_cost_run]. destruct (rem <=? 0); [lia|].
set (n := if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem).
destruct (Z.ltb_spec cap (no + n)) as [Hlt|Hge].
- pose proof (mo_malloc_nonneg MT ML ((no + n) * 2) ltac:(lia)).
  pose proof (mo_free_nonneg MT ML).
  pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) ltac:(lia)). lia.
- apply IH; exact Hcap.
Qed.

Lemma sl_cost_run_nonneg : forall f mx no cap rem, ameter_laws MT -> 0 <= no -> 0 <= mx ->
0 <= sl_cost_run MT f mx no cap rem.
Proof.
intros f mx no cap rem ML. revert no cap rem.
induction f as [|f IH]; intros no cap rem Hno Hmx; [cbn; lia|].
cbn [sl_cost_run]. destruct (Z.le_gt_cases rem 0) as [Hle|Hgt].
- rewrite (proj2 (Z.leb_le rem 0) Hle). lia.
- rewrite (proj2 (Z.leb_gt rem 0) Hgt).
  pose proof (sl_n_range mx rem Hmx Hgt) as Hn. unfold sl_n in Hn.
  set (n := if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) in *.
  destruct (cap <? no + n).
  + pose proof (mo_malloc_nonneg MT ML ((no + n) * 2) ltac:(lia)).
    pose proof (mo_free_nonneg MT ML).
    pose proof (IH (no + n) ((no + n) * 2) (rem - n) ltac:(lia) Hmx). lia.
  + apply IH; lia.
Qed.
End m.

(* The control flags at a live controller (open client, not broken, not dead, a nonempty line) and at a dead one. *)
Lemma sl_live_true : forall c len, ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> 0 < len -> sl_live c len = true.
Proof.
intros c len Hcl Hbr Hdd Hlen. unfold sl_live, send_line_c.send_live, send_line_c.send_off.
rewrite Hcl, Hbr, Hdd, (proj2 (Z.eqb_neq len 0)) by lia. reflexivity.
Qed.

Lemma sl_live_false_dead : forall c len, ct_dd c = 1 -> sl_live c len = false.
Proof.
intros c len Hdd. unfold sl_live, send_line_c.send_live. rewrite Hdd. apply andb_false_r.
Qed.

Lemma sl_ctl_on : forall c len, ct_cl c = 3 -> ct_br c = 0 -> 0 < len ->
sl_ctl c len = CTL 3 (ct_dd c) (ct_dd c) 0
  (if ct_dd c =? 1 then send_line_c.EPIPE_V else if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c).
Proof.
intros c len Hcl Hbr Hlen. unfold sl_ctl, send_line_c.send_off.
rewrite Hcl, Hbr, (proj2 (Z.eqb_neq len 0)) by lia. reflexivity.
Qed.

Lemma sl_O_live : forall c O Bl, ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> (0 < Z.of_nat (length Bl)) ->
sl_O c O Bl = O ++ Bl.
Proof. intros c O Bl Hcl Hbr Hdd Hlen. unfold sl_O. rewrite sl_live_true by assumption. reflexivity. Qed.

Lemma sl_O_dead : forall c O Bl, ct_dd c = 1 -> sl_O c O Bl = O.
Proof. intros c O Bl Hdd. unfold sl_O. rewrite sl_live_false_dead by assumption. reflexivity. Qed.

Lemma sl_no_live : forall c no len, ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> 0 < len -> sl_no c no len = no + len.
Proof. intros c no len Hcl Hbr Hdd Hlen. unfold sl_no. rewrite sl_live_true by assumption. reflexivity. Qed.

Lemma sl_no_dead : forall c no len, ct_dd c = 1 -> sl_no c no len = no.
Proof. intros c no len Hdd. unfold sl_no. rewrite sl_live_false_dead by assumption. reflexivity. Qed.

Lemma sl_cap_live : forall c mx no cap len, ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> 0 < len ->
sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx no cap len.
Proof. intros c mx no cap len Hcl Hbr Hdd Hlen. unfold sl_cap. rewrite sl_live_true by assumption. reflexivity. Qed.

Lemma sl_cap_dead : forall c mx no cap len, ct_dd c = 1 -> sl_cap c mx no cap len = cap.
Proof. intros c mx no cap len Hdd. unfold sl_cap. rewrite sl_live_false_dead by assumption. reflexivity. Qed.

(* two distinct extents of a pairwise-disjoint list are disjoint *)
Lemma zall_disjoint_nth : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma zpairwise_disjoint_nth : forall l i j d, zpairwise_disjoint l -> i <> j ->
(i < length l)%nat -> (j < length l)%nat -> zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hi Hj; cbn in Hi, Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i], j as [|j]; cbn [nth]; [lia | | |].
- apply zall_disjoint_nth; [exact H1 | lia].
- pose proof (zall_disjoint_nth a l i d H1 ltac:(lia)) as D. unfold zdisj in *. lia.
- apply IH; [exact H2 | lia | lia | lia].
Qed.


(* ---- Model and arithmetic facts of a data round. ---- *)
Lemma sl_max_run_nonpos_rem : forall f mx no cap rem, rem <= 0 -> sl_max_run f mx no cap rem = 0.
Proof.
intros [|f] mx no cap rem Hrem; [reflexivity|].
cbn [sl_max_run]. rewrite (proj2 (Z.leb_le rem 0) Hrem). reflexivity.
Qed.
Lemma sl_max_run_fuel : forall f f' mx no cap rem, 0 <= mx -> 0 <= rem ->
(Z.to_nat rem <= f)%nat -> (Z.to_nat rem <= f')%nat ->
sl_max_run f mx no cap rem = sl_max_run f' mx no cap rem.
Proof.
induction f as [|f IH]; intros f' mx no cap rem Hmx Hrem Hf Hf'.
- assert (rem = 0) by lia. subst rem. rewrite !sl_max_run_nonpos_rem by lia. reflexivity.
- destruct (Z.le_gt_cases rem 0) as [Hle|Hgt].
  + rewrite !sl_max_run_nonpos_rem by exact Hle. reflexivity.
  + destruct f' as [|f']; [lia|].
    pose proof (sl_n_range mx rem Hmx Hgt) as Hn. unfold sl_n in Hn.
    cbn [sl_max_run]. rewrite (proj2 (Z.leb_gt rem 0) Hgt).
    set (n := if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) in *.
    destruct (cap <? no + n); rewrite (IH f') by lia; reflexivity.
Qed.
(* C3 (W_contract.v sl_spec, sl_tr): the room the rounds need is the peak of their requests, carried from cut to cut
   as the peak of the rest of the trace, send_line_b_c.send_line_tr true .. 0 adr0.  A round that does not grow g_out
   requests nothing; a round that grows it requests (no + n) * 2 bytes, a malloc when cap = 0, else the realloc of
   the cap-byte block, which the new block replaces (W_tr_peak.v tr_peak_step_malloc / tr_peak_step_realloc).  The
   names play no part in the sizes (W_tr_peak.v sl_run_sz), so the rest restarts at 0 and adr0. *)
Lemma sl_tr_peak_keep : forall mx no cap rem, 0 <= mx -> 0 < rem -> no + sl_n mx rem <= cap ->
tr_peak (send_line_b_c.send_line_tr true mx no cap rem 0 RelayRunF.adr0) =
tr_peak (send_line_b_c.send_line_tr true mx (no + sl_n mx rem) cap (rem - sl_n mx rem) 0 RelayRunF.adr0).
Proof.
intros mx no cap rem Hmx Hrem Hc. unfold send_line_b_c.send_line_tr.
pose proof (sl_n_range mx rem Hmx Hrem) as Hn.
replace (Z.to_nat rem) with (S (Z.to_nat rem - 1)) by lia.
cbn [send_line_b_c.sl_run]. rewrite (proj2 (Z.leb_gt rem 0) Hrem).
change (if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) with (sl_n mx rem).
rewrite (proj2 (Z.ltb_ge cap (no + sl_n mx rem)) Hc).
rewrite (sl_run_fuel_eq (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) by lia. reflexivity.
Qed.
(* a growing round: realloc's live-bytes premise (W_journal.v arealloc_cf_rule) at the live bytes bb before it, and
   the peak of the rest at the live bytes after it (the old cap-byte block freed, the new one live) *)
Lemma sl_tr_peak_grow : forall mx no cap rem bb L, 0 <= mx -> 0 < rem -> cap < no + sl_n mx rem ->
bb + tr_peak (send_line_b_c.send_line_tr true mx no cap rem 0 RelayRunF.adr0) <= L ->
bb + (no + sl_n mx rem) * 2 <= L /\
bb - cap + (no + sl_n mx rem) * 2 +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) 0
    RelayRunF.adr0) <= L.
Proof.
intros mx no cap rem bb L Hmx Hrem Hc H. unfold send_line_b_c.send_line_tr in H |- *.
pose proof (sl_n_range mx rem Hmx Hrem) as Hn.
replace (Z.to_nat rem) with (S (Z.to_nat rem - 1)) in H by lia.
cbn [send_line_b_c.sl_run] in H |- *. rewrite (proj2 (Z.leb_gt rem 0) Hrem) in H.
change (if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) with (sl_n mx rem) in H.
rewrite (proj2 (Z.ltb_lt cap (no + sl_n mx rem)) Hc) in H. cbn [fst] in H.
rewrite (sl_run_fuel_eq (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) in H by lia.
rewrite <- (proj1 (W_tr_peak.tr_sz_measures _ _ (W_tr_peak.sl_run_sz (Z.to_nat (rem - sl_n mx rem)) mx
  (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) 1%nat (RelayRunT.Ret 0%nat) 0%nat RelayRunF.adr0))).
destruct (Z.eq_dec cap 0) as [E0 | E0].
- rewrite (proj2 (Z.eqb_eq cap 0) E0) in H. cbv beta iota in H.
  destruct (W_tr_peak.tr_peak_step_malloc _ _ _ _ H) as [H1 H2]. subst cap. split; lia.
- rewrite (proj2 (Z.eqb_neq cap 0) E0) in H. cbv beta iota in H.
  exact (W_tr_peak.tr_peak_step_realloc _ _ _ _ _ _ H).
Qed.
Lemma sl_max_run_step : forall mx no cap rem, 0 <= mx -> 0 < rem ->
sl_max_run (Z.to_nat rem) mx no cap rem =
(if cap <? no + sl_n mx rem
 then Z.max ((no + sl_n mx rem) * 2)
        (sl_max_run (Z.to_nat (rem - sl_n mx rem)) mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem))
 else sl_max_run (Z.to_nat (rem - sl_n mx rem)) mx (no + sl_n mx rem) cap (rem - sl_n mx rem)).
Proof.
intros mx no cap rem Hmx Hrem.
pose proof (sl_n_range mx rem Hmx Hrem) as Hn.
replace (Z.to_nat rem) with (S (Z.to_nat rem - 1)) by lia.
cbn [sl_max_run]. rewrite (proj2 (Z.leb_gt rem 0) Hrem).
change (if (negb (mx =? 0) && (mx <? rem))%bool then mx else rem) with (sl_n mx rem).
destruct (cap <? no + sl_n mx rem);
rewrite (sl_max_run_fuel (Z.to_nat rem - 1) (Z.to_nat (rem - sl_n mx rem))) by lia; reflexivity.
Qed.
