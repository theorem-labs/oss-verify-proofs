(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the loop segment of fuzz_reply's ASan send_line walk, in the form of the
   cgif donor's loop over concrete cut states (proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v tcbb_loopX). *)
(* The loop head L = 0x827c8 (A_sl_loop).  One round is one of
   - the EINTR round: g_send_eintr <> 0, cleared, errno := EINTR, back to L with the bound one smaller;
   - the dead round: g_send_dead <> 0, errno := EPIPE, g_client_broken := 1, out through the epilogue;
   - a data round: n = min(len - sent, g_send_max or len - sent) bytes, a realloc of g_out when it is short,
     an __asan_memcpy into it, g_nout := g_nout + n, then back to L or out through the epilogue.
   The statement is W_send_line_cx.v's sl_loop_stmt; the Section header below is that file's, verbatim. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_frame W_sites W_contract W_send_line_cx W_send_line_datab_cx W_send_line_grow_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* g_capout after one round of the plain model that sends n bytes (W_send_line_datab_cx.v sl_n): doubled past the
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

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
(* nothing a callee's journal may change is a read-only image byte (W_journal.v rom_out / ajournal_gx_rom_view); and
   aout_at's three read-only cells are program globals off the allocator's statics, so a realloc keeps them *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : exists r, In r (as_zero_shadow B) /\ fst r <= as_errno B /\ as_errno B + 4 <= fst r + snd r.
(* errno's 4 bytes are writable image bytes in the segments' own view (W_drain_cx.v HERRW, same text) *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
Let RUN := paj_run_x B LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition LBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---- the loop head's symbolic state ---- *)
(* The six kept auipc registers must be the listing's own hi atoms, because a PLdHi slot only runs when its
   base register still holds SOff (A_HI j) 0; s3 is pinned to 3 so that the bne against g_client decides. *)
Definition sr_L : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    19%bv (SLit 3))
    20%bv (SOff (A_HI 24) 0))
    21%bv (SOff (A_HI 16) 0))
    24%bv (SOff (A_HI 23) 0))
    25%bv (SOff (A_HI 19) 0))
    26%bv (SOff (A_HI 22) 0))
    27%bv (SOff (A_HI 20) 0).

Definition r_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 24 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff (A_HI 17) 0)); YP09.mkChunk 16 (CVal 8 (SOff (A_HI 21) 0))].
Definition r_client : YP09.region := YP09.mkRegion (Some (A_OBJ 9)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 3))].
Definition r_eintr : YP09.region := YP09.mkRegion (Some (A_OBJ 11)) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition r_dead : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition r_max : YP09.region := YP09.mkRegion (Some (A_HI 21)) 140 148 140 140 [YP09.mkChunk 140 (CVal 8 (SOff 37 0))].
Definition r_nout : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition r_capout : YP09.region := YP09.mkRegion (Some (A_OBJ 14)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition r_out : YP09.region := YP09.mkRegion (Some (A_OBJ 15)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
Definition r_broken : YP09.region := YP09.mkRegion (Some (A_HI 17)) 92 93 92 93 [YP09.mkChunk 92 (CVal 1 (SLit 0))].
Definition l_regions : smem :=
  [ r_frame; r_client; r_eintr; r_dead; r_max; r_nout; r_capout; r_out; r_broken ].

Definition OBJF : afact := mkAF 0x10000 0x5fb000 0.
Definition HIF : afact := mkAF 0 0x5fb000 0.
Definition l_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (23%nat, mkAF SB SB 0);
  (8%nat, mkAF 1 (2^63 - 1) 0); (9%nat, mkAF 0 (2^63 - 1) 0); (22%nat, mkAF 0 (2^63 - 1) 0);
  (32%nat, mkAF 0 1 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 0 (2^47) 0);
  (35%nat, mkAF 0 (2^47) 0); (36%nat, mkAF 0 (2^47) 0); (37%nat, mkAF 0 255 0);
  (A_OBJ 11, OBJF); (A_OBJ 13, OBJF); (A_OBJ 14, OBJF); (A_OBJ 15, OBJF);
  (A_HI 17, HIF); (A_HI 19, HIF); (A_HI 22, HIF); (A_HI 23, HIF); (A_HI 24, HIF) ] [] [].

Definition ss_L : sstate := mkSS A_sl_loop sr_L l_regions None l_facts.
Definition BxL : sv := SOff 23 0.
Definition l_extra (eiL dd no' capL outL mx : Z) : list word :=
  map (Z_to_bv 64) [eiL; dd; no'; capL; outL; mx].

(* HRGD split into the pairs the loop-head state needs.
   Index order: got, cell, client, broken, eintr, dead, max, nout, capout, out, errno. *)
Lemma sl_loop_entry : forall lyL SL (WL : world SEGS) regsL memL sp0 len line sent eiL dd no' capL outL mx evL O',
spZ regsL = sp0 - SL_FRAME ->
2 ^ 46 + SL_FRAME <= sp0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
sl_regsL regsL len line sent ->
1 <= len <= 2 ^ 63 - 1 -> 0 <= line <= 2 ^ 63 - 1 -> 0 <= sent <= 2 ^ 63 - 1 ->
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) ->
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) ->
aout_at B RG lyL SL WL memL (CTL 3 0 dd eiL evL) O' mx no' capL outL ->
0 <= no' <= 2 ^ 47 -> 0 <= capL <= 2 ^ 47 -> 0 <= outL <= 2 ^ 47 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsL (l_extra eiL dd no' capL outL mx))) ss_L
(restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS))).
Proof.
intros lyL SL WL regsL memL sp0 len line sent eiL dd no' capL outL mx evL O'
Hsp Hlo Hhi Hal HR Hlen Hline Hsent M8 M16 HOUT Rno Rcap Rout.
unfold SL_FRAME in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HR as (R8 & R9 & R19 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
destruct HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hcl & Hbr & Hdd & Hei & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev, Hcl, Hbr, Hdd, Hei.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsL (l_extra eiL dd no' capL outL mx))).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regsL 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regsL 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 9 9%bv eq_refl)).
assert (E22 : ew E 22 = getr regsL 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr regsL 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 dd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 no') by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (UV : forall n, (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew E n) = VAL n).
{ intros n Hn. subst E. rewrite Eimg_img by exact Hn. apply unsigned_lit_small. apply pa_val_range. }
assert (BV : forall n, (A_TEXT <= n < A_LIM)%nat -> base_val E (Some n) = VAL n).
{ intros n Hn. cbn [base_val]. exact (UV n Hn). }
assert (SVH : forall n, (A_TEXT <= n < A_LIM)%nat -> sv_denot E (SOff n 0) = w64 (VAL n)).
{ intros n Hn. cbn [sv_denot]. rewrite (UV n Hn). rewrite Z.add_0_r. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite E2; exact Hsp).
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 11 ltac:(lia)) as Q11.
pose proof (pa_obj_img 12 ltac:(lia)) as Q12. pose proof (pa_obj_img 13 ltac:(lia)) as Q13.
pose proof (pa_obj_img 14 ltac:(lia)) as Q14. pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
unfold ss_L, A_sl_loop. apply pa_entry_st_ok_full.
- unfold sr_L.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 20)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R27].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 22)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R26].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 19)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R25].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 23)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R24].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 16)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R21].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite (SVH (A_HI 24)) by (unfold A_HI, A_TEXT, A_LIM; lia); exact R20].
  apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R19].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (sp0 - 128) 8 8 (SOff (A_HI 17) 0) (VAL (A_HI 17)));
      [rewrite (SVH (A_HI 17)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 17)); zside | zside | exact M8].
    * apply (chunk_ok_val SEGS E _ (sp0 - 128) 16 8 (SOff (A_HI 21) 0) (VAL (A_HI 21)));
      [rewrite (SVH (A_HI 21)) by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity
      | pose proof (pa_val_range (A_HI 21)); zside | zside | exact M16].
  + rewrite (BV (A_OBJ 9)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_client RG) 0 4 (SLit 3) 3);
    [cbn [sv_denot]; reflexivity | zside | zside |].
    rewrite Z.add_0_r. replace 3 with (3 mod 2 ^ 32) by reflexivity. exact Vcl.
  + rewrite (BV (A_OBJ 11)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV11.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wei; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_send_eintr RG) 0 1 (SOff 32 0) eiL);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vei.
  + rewrite (BV (A_OBJ 12)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV12.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_send_dead RG) 0 1 (SOff 33 0) dd);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vdd.
  + rewrite (BV (A_HI 21)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (VAL (A_HI 21)) 140 8 (SOff 37 0) mx);
    [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite HH21. exact Vmx.
  + rewrite (BV (A_OBJ 13)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wno; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nout RG) 0 8 (SOff 34 0) no');
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vno.
  + rewrite (BV (A_OBJ 14)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV14.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wcap; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_capout RG) 0 8 (SOff 35 0) capL);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vcap.
  + rewrite (BV (A_OBJ 15)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV15.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Wout; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_out RG) 0 8 (SOff 36 0) outL);
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Vout.
  + rewrite (BV (A_HI 17)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. replace (VAL (A_HI 17) + o) with (rg_client_broken RG + (o - 92)) by lia. apply Wbr. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_HI 17)) 92 1 (SLit 0) 0);
      [cbn [sv_denot]; reflexivity | zside | zside |].
      rewrite HH17. exact Vbr.
- apply pairwise_disjoint_of_extents.
  unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (BV (A_OBJ 9)), (BV (A_OBJ 11)), (BV (A_OBJ 12)), (BV (A_HI 21)), (BV (A_OBJ 13)),
          (BV (A_OBJ 14)), (BV (A_OBJ 15)), (BV (A_HI 17)) by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  cbn [base_val]. rewrite Usp, HV9, HV11, HV12, HV13, HV14, HV15.
  replace (VAL (A_HI 21)) with (rg_send_max RG - 140) by lia.
  replace (VAL (A_HI 17)) with (rg_client_broken RG - 92) by lia.
  rewrite HV9 in Q9. rewrite HV10 in Q10. rewrite HV11 in Q11. rewrite HV12 in Q12.
  rewrite HV13 in Q13. rewrite HV14 in Q14. rewrite HV15 in Q15.
  cbn [zpairwise_disjoint zall_disjoint] in HRGD. unfold zdisj in HRGD. cbn [fst snd] in HRGD.
  destruct HRGD as (_ & _ &
   (D01 & D02 & D03 & D04 & D05 & D06 & D07 & _ & _) &
   (D08 & D09 & D10 & D11 & D12 & D13 & _ & _) &
   (D14 & D15 & D16 & D17 & D18 & _ & _) &
   (D19 & D20 & D21 & D22 & _ & _) &
   (D23 & D24 & D25 & _ & _) &
   (D26 & D27 & _ & _) &
   (D28 & _ & _) & _ & _ & _).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split;
  first [ solve [ clear - Hlo Q9 Q10 Q11 Q12 Q13 Q14 Q15 HSM; lia ]
        | match goal with H : _ \/ _ |- _ => solve [ clear - H; lia ] end ].
- split; [|split; [exact I | exact I]].
  cbn [l_facts f_atoms atoms_ok]. unfold afact_ok, OBJF, HIF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E8, E9, E22, E23, E32, E33, E34, E35, E36, E37.
  rewrite R8, R9, R22, R23.
  rewrite (UV (A_OBJ 11)), (UV (A_OBJ 13)), (UV (A_OBJ 14)), (UV (A_OBJ 15)),
          (UV (A_HI 17)), (UV (A_HI 19)), (UV (A_HI 22)), (UV (A_HI 23)), (UV (A_HI 24))
    by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I;
  first [ rewrite Zminus_mod, Hal; reflexivity
        | solve [ clear - Hlo Hhi Hlen Hline Hsent Hei Hdd Rno Rcap Rout Hmxr Q10 Q11 Q13 Q14 Q15
                    HH17 HH19 HH22 HH23 HH24 HV10 HV11 HV13 HV14 HV15; unfold SB; lia ] ].
Qed.

(* membership in the walk's globals *)
Ltac ing_tac := unfold G_SL; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].

(* The donor's paj_run_tok / paj_run_to_tok with a fuel that fits one round: the run's cost is linear in
   the fuel bound, and 200000 (W_kit's FUEL) is 60x more than any segment of this loop needs. *)
Definition L_FUEL : N := 3000%N.
Ltac lrun RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH L_FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
time "assert-hrun" assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH L_FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "lrun: no img_env" end in
time "eapply-run" eapply (RUN W L_FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; time "obls" (cbn [sh_obls]; srr_obls)
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
time "after" paj_after_run_tok HS HJ SHOK ]
end end
end
end.
Ltac lrun_to RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH L_FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH L_FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env val _ E |- _ => HEI | _ => fail "lrun_to: no img_env" end in
eapply (RUNTO W L_FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(repeat match goal with H : _ |- _ => clear H end; unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok HS HJ SHOK ]
end end
end
end.


(* HRGD as the zdisj fact of two of its extents, named by their positions in the list:
   0 VAL (A_OBJ 0), 1 VAL (A_OBJ 32), 2 g_client, 3 g_client_broken, 4 g_send_eintr, 5 g_send_dead,
   6 g_send_max, 7 g_nout, 8 g_capout, 9 g_out, 10 errno *)
Lemma sl_rgd : forall i j, i <> j -> (i < 11)%nat -> (j < 11)%nat ->
zdisj (nth i [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)] (0, 0))
(nth j [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)] (0, 0)).
Proof. intros i j Hij Hi Hj. apply zpairwise_disjoint_nth; [exact HRGD | exact Hij | cbn; lia | cbn; lia]. Qed.

(* a cell disjoint from the two ranges a round changes is kept by the round *)
Lemma sl_cell_kept : forall (W W' : world SEGS) mem mem' c1 n1 c2 n2 a n x,
(forall y, ~ (c1 <= y < c1 + n1) -> ~ (c2 <= y < c2 + n2) -> abyte_kept W mem W' mem' y) ->
zdisj (a, a + n) (c1, c1 + n1) -> zdisj (a, a + n) (c2, c2 + n2) ->
a <= x < a + n -> abyte_kept W mem W' mem' x.
Proof.
intros W W' mem mem' c1 n1 c2 n2 a n x HK D1 D2 Hx. unfold zdisj in D1, D2. cbn [fst snd] in D1, D2. apply HK; lia.
Qed.

(* the cell (a, n) at position i of HRGD, kept by a round that changes the cells at positions j and k *)
Local Ltac sl_d i j := exact (sl_rgd i j ltac:(lia) ltac:(lia) ltac:(lia)).
Local Ltac sl_vm HK i j k a n :=
  eapply (akept_vm _ _ _ _ a n); [intros x Hx; apply (sl_cell_kept _ _ _ _ _ _ _ _ a (Z.of_nat n) x HK);
    [sl_d i j | sl_d i k | exact Hx] |].
Local Ltac sl_wr HK i j k a n :=
  eapply (akept_awr _ _ _ _ a n); [intros x Hx; apply (sl_cell_kept _ _ _ _ _ _ _ _ a n x HK);
    [sl_d i j | sl_d i k | exact Hx] |].

(* send_line's EINTR round: g_send_eintr := 0 and errno := ev' (EINTR) *)
Lemma aout_at_eintr : forall ly S (W W' : world SEGS) mem mem' c O mx no cap out ev',
aout_at B RG ly S W mem c O mx no cap out ->
(forall a, ~ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) -> ~ (as_errno B <= a < as_errno B + 4) ->
   abyte_kept W mem W' mem' a) ->
(forall a, out <= a < out + cap -> ~ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W' mem') (rg_send_eintr RG) 1 0 ->
awr W' mem' (rg_send_eintr RG) 1 ->
val_mem SEGS (arm W' mem') (as_errno B) 4 ev' -> 0 <= ev' < 2 ^ 32 ->
awr W' mem' (as_errno B) 4 ->
aout_at B RG ly S W' mem' (CTL (ct_cl c) (ct_br c) (ct_dd c) 0 ev') O mx no cap out.
Proof.
intros ly S W W' mem mem' c O mx no cap out ev'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HO Ve We Vv Ev Wv.
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [sl_vm HK 6%nat 4%nat 10%nat (rg_send_max RG) 8%nat; exact H1|].
split; [sl_wr HK 6%nat 4%nat 10%nat (rg_send_max RG) 8; exact H2|].
split; [sl_vm HK 7%nat 4%nat 10%nat (rg_nout RG) 8%nat; exact H3|].
split; [sl_wr HK 7%nat 4%nat 10%nat (rg_nout RG) 8; exact H4|].
split; [sl_vm HK 8%nat 4%nat 10%nat (rg_capout RG) 8%nat; exact H5|].
split; [sl_wr HK 8%nat 4%nat 10%nat (rg_capout RG) 8; exact H6|].
split; [sl_vm HK 9%nat 4%nat 10%nat (rg_out RG) 8%nat; exact H7|].
split; [sl_wr HK 9%nat 4%nat 10%nat (rg_out RG) 8; exact H8|].
split; [sl_vm HK 2%nat 4%nat 10%nat (rg_client RG) 4%nat; exact H9|].
split; [sl_wr HK 2%nat 4%nat 10%nat (rg_client RG) 4; exact H10|].
split; [sl_vm HK 3%nat 4%nat 10%nat (rg_client_broken RG) 1%nat; exact H11|].
split; [sl_wr HK 3%nat 4%nat 10%nat (rg_client_broken RG) 1; exact H12|].
split; [sl_vm HK 5%nat 4%nat 10%nat (rg_send_dead RG) 1%nat; exact H13|].
split; [sl_wr HK 5%nat 4%nat 10%nat (rg_send_dead RG) 1; exact H14|].
split; [exact Ve|]. split; [exact We|].
split; [exact Vv|]. split; [exact Wv|]. split; [exact Ev|].
split; [exact H20|]. split; [exact H21|]. split; [exact H22|].
split; [left; reflexivity|].
split; [exact H24|]. split; [exact H25|].
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W mem); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
destruct (HO x ltac:(lia)) as [N1 N2]. exact (HK x N1 N2).
Qed.

(* send_line's dead round: g_client_broken := 1 and errno := ev' (EPIPE) *)
Lemma aout_at_broken : forall ly S (W W' : world SEGS) mem mem' c O mx no cap out ev',
aout_at B RG ly S W mem c O mx no cap out ->
(forall a, ~ (rg_client_broken RG <= a < rg_client_broken RG + 1) -> ~ (as_errno B <= a < as_errno B + 4) ->
   abyte_kept W mem W' mem' a) ->
(forall a, out <= a < out + cap -> ~ (rg_client_broken RG <= a < rg_client_broken RG + 1) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W' mem') (rg_client_broken RG) 1 1 ->
awr W' mem' (rg_client_broken RG) 1 ->
val_mem SEGS (arm W' mem') (as_errno B) 4 ev' -> 0 <= ev' < 2 ^ 32 ->
awr W' mem' (as_errno B) 4 ->
aout_at B RG ly S W' mem' (CTL (ct_cl c) 1 (ct_dd c) (ct_ei c) ev') O mx no cap out.
Proof.
intros ly S W W' mem mem' c O mx no cap out ev'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HO Vb Wb Vv Ev Wv.
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [sl_vm HK 6%nat 3%nat 10%nat (rg_send_max RG) 8%nat; exact H1|].
split; [sl_wr HK 6%nat 3%nat 10%nat (rg_send_max RG) 8; exact H2|].
split; [sl_vm HK 7%nat 3%nat 10%nat (rg_nout RG) 8%nat; exact H3|].
split; [sl_wr HK 7%nat 3%nat 10%nat (rg_nout RG) 8; exact H4|].
split; [sl_vm HK 8%nat 3%nat 10%nat (rg_capout RG) 8%nat; exact H5|].
split; [sl_wr HK 8%nat 3%nat 10%nat (rg_capout RG) 8; exact H6|].
split; [sl_vm HK 9%nat 3%nat 10%nat (rg_out RG) 8%nat; exact H7|].
split; [sl_wr HK 9%nat 3%nat 10%nat (rg_out RG) 8; exact H8|].
split; [sl_vm HK 2%nat 3%nat 10%nat (rg_client RG) 4%nat; exact H9|].
split; [sl_wr HK 2%nat 3%nat 10%nat (rg_client RG) 4; exact H10|].
split; [exact Vb|]. split; [exact Wb|].
split; [sl_vm HK 5%nat 3%nat 10%nat (rg_send_dead RG) 1%nat; exact H13|].
split; [sl_wr HK 5%nat 3%nat 10%nat (rg_send_dead RG) 1; exact H14|].
split; [sl_vm HK 4%nat 3%nat 10%nat (rg_send_eintr RG) 1%nat; exact H15|].
split; [sl_wr HK 4%nat 3%nat 10%nat (rg_send_eintr RG) 1; exact H16|].
split; [exact Vv|]. split; [exact Wv|]. split; [exact Ev|].
split; [exact H20|]. split; [right; reflexivity|]. split; [exact H22|].
split; [exact H23|].
split; [exact H24|]. split; [exact H25|].
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W mem); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
destruct (HO x ltac:(lia)) as [N1 N2]. exact (HK x N1 N2).
Qed.


(* A value is carried by a frame that keeps the view of its bytes. *)
Lemma vm_keep : forall (W : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HK Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
apply HK. lia.
Qed.
Lemma garr8_keep : forall (W : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l HK Hg. apply (garr8_frame SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) m') a l Hg).
intros x Hx. apply (mbyte_of_aview SEGS). exact (HK x Hx).
Qed.
(* Two memories that hold the same value at a cell view its bytes alike. *)
Lemma aview_of_vm2 : forall (W : world SEGS) m m' a n v,
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v ->
forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x.
Proof.
intros W m m' a n v H1 H2 x Hx. unfold aview.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H1 (Z.to_nat (x - a)) ltac:(lia)), (H2 (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.
(* An image atom's word. *)
Lemma ew_img : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (VAL n).
Proof.
intros E n HE Hn. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* errno's four bytes are addressable: HERRZ puts them inside one of the instance's zero-shadow ranges. *)
Lemma errno_ra : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (as_errno B) 4.
Proof.
intros ly S W mem md HAR.
destruct HERRZ as (r & Hin & Hlo & Hhi).
assert (Hin' : In r (zero_shadow_ranges B ly)) by (unfold zero_shadow_ranges; right; exact Hin).
pose proof (al_zshadow _ _ LAWS ly S W mem md r HAR Hin') as HZ.
pose proof HAR as (M & _).
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ M)) r Hin) as (R1 & R2 & R3 & R4 & R5).
pose proof (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF (fst r) (snd r) R3 R4 HZ) as HRA.
intros y Hy. apply HRA. clear - Hy Hlo Hhi. lia.
Qed.
Ltac clia := repeat match goal with X : _ |- _ => clear X end; lia.
Ltac awr_empty :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; intros a Ha; exfalso; clear - Ha; lia.
(* a is outside every writable window of a run's regions, because every such window is a G_SL cell *)
Ltac nowr BV BA NALL HnG :=
  intros (rr & Hin & Hr); cbn [ss_mem add_cond add_atom ss_L l_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r_frame r_client r_eintr r_dead r_max
           r_nout r_capout r_out r_broken] in Hr;
      try change (A_OBJ 11) with 252%nat in Hr; try change (A_OBJ 13) with 254%nat in Hr;
      try change (A_OBJ 14) with 255%nat in Hr; try change (A_OBJ 15) with 256%nat in Hr;
      try change (A_HI 17) with 297%nat in Hr;
      first [ solve [ clear - Hr; lia ]
            | solve [ exfalso;
                rewrite ?(BV 252%nat ltac:(cbv; lia)), ?(BV 299%nat ltac:(cbv; lia)),
                        ?(BV 254%nat ltac:(cbv; lia)), ?(BV 255%nat ltac:(cbv; lia)),
                        ?(BV 256%nat ltac:(cbv; lia)), ?(BV 297%nat ltac:(cbv; lia)), ?BA in Hr;
                apply HnG; clear - Hr NALL; ing_tac ] ] | ]);
  destruct Hin.
Ltac awr_gb BV m H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  rewrite (BV m) by (repeat match goal with X : _ |- _ => clear X end; unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia);
  intros a Ha; clear - Ha H; ing_tac.
Ltac awr_g m H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  lazymatch goal with BVE : forall _, _ -> base_val _ _ = _ |- _ =>
    rewrite (BVE m) by (repeat match goal with H : _ |- _ => clear H end; unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia) end;
  intros a Ha; clear - Ha H; ing_tac.

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
(* len - sent as the engine computes it: s0 + s6 * -1 *)
Lemma U_rem : forall E (len sent z : Z), ew E 8 = w64 len -> ew E 22 = w64 sent -> 0 <= sent <= len -> len < 2 ^ 64 ->
z mod 2 ^ 64 = 2 ^ 64 - 1 -> U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 22 0) (SLit z))) = len - sent.
Proof.
intros E len sent z E8 E22 Hs Hl Hz.
rewrite U_SAlu, U_SMd, (U_atom E 8 len E8), (U_atom E 22 sent E22), U_SLit by lia. cbn [zalu_raw zmd_raw].
unfold zcanon, M64. rewrite Hz, Z.add_mod_idemp_r by lia.
replace (len + sent * (2 ^ 64 - 1)) with ((len - sent) + sent * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* A state at 0x82824 with s2 = n and a1 forgotten: the three ways the n computation reaches it, made one. *)
Lemma sl_canon : forall E ss ms (v18 v11 : word) nf,
st_ok_pi SEGS VAL E ss ms -> YP07.ss_atoms_p (YP07.pband 38 A_TEXT) ss = true ->
getr (ms_regs ms) 18%bv = v18 -> getr (ms_regs ms) 11%bv = v11 ->
afact_ok (havoc E 38 [v18; v11]) 38 nf ->
st_ok_pi SEGS VAL (havoc E 38 [v18; v11])
  (add_atom (mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) 18%bv (SOff 38 0)) 11%bv (SOff 39 0)) (ss_mem ss) (ss_resv ss)
     (mkFacts (f_atoms (ss_facts ss)) [] [])) 38 nf) ms.
Proof.
intros E ss ms v18 v11 nf HS Hat H18 H11 Hf.
pose proof (st_ok_pi_havoc 38 E ss ms [v18; v11] HS Hat ltac:(cbn; unfold A_TEXT; lia)) as H1.
assert (D38 : sv_denot (havoc E 38 [v18; v11]) (SOff 38 0) = v18)
  by (cbn [sv_denot]; unfold havoc; cbn [ew]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (D39 : sv_denot (havoc E 38 [v18; v11]) (SOff 39 0) = v11)
  by (cbn [sv_denot]; unfold havoc; cbn [ew]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
pose proof (ast_ok_pi_set_reg_fp _ _ _ 18%bv (SOff 38 0) H1 eq_refl ltac:(rewrite D38; symmetry; exact H18)) as H2.
pose proof (ast_ok_pi_set_reg_fp _ _ _ 11%bv (SOff 39 0) H2 eq_refl ltac:(rewrite D39; symmetry; exact H11)) as H3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H3.
pose proof (st_ok_pi_facts_incl3 _ _ _ (f_atoms (ss_facts ss)) [] [] H3) as H4.
cbn [ss_facts set_facts ss_pc ss_regs ss_mem ss_resv] in H4.
apply st_ok_pi_add_fact; [|exact Hf].
apply H4; intros x Hx; [exact Hx | destruct Hx | destruct Hx].
Qed.

(* the write windows of the loop head's regions are G_SL cells *)
Lemma l_nowr : forall E a, img_env VAL A_LIM E -> ~ inG (G_SL B RG) a -> ~ in_wrange E l_regions a.
Proof.
intros E a HEI HnG (rr & Hin & Hr). unfold l_regions in Hin. cbn [In] in Hin.
pose proof (HEI (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U11.
pose proof (HEI (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U13.
pose proof (HEI (A_OBJ 14) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U14.
pose proof (HEI (A_OBJ 15) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U15.
pose proof (HEI (A_HI 17) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U17.
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi r_frame r_client r_eintr r_dead r_max r_nout r_capout r_out r_broken base_val] in Hr;
    rewrite ?U11, ?U13, ?U14, ?U15, ?U17 in Hr;
    first [ clear - Hr; lia
          | apply HnG; rewrite ?HV11, ?HV13, ?HV14, ?HV15 in Hr; clear - Hr HH17; ing_tac ] | ]).
destruct Hin.
Qed.

(* views and presence carried along the runs of a round: every frame_of / mem_grows from the start to the goal's memory *)
Ltac keep_chain HEI :=
  let a := fresh "a" in let Ha := fresh "Ha" in let HnG := fresh "HnG" in
  intros a Ha HnG;
  repeat match goal with
  | |- aview _ _ ?m a = aview _ _ ?m a => reflexivity
  | HF : frame_of _ _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- aview _ (w_H ?W) ?m2 a = _ =>
      rewrite (aview_kept_out _ _ (w_H W) m1 m2 HF a Ha (l_nowr _ a HEI HnG))
  end.
Ltac pres_chain :=
  let a := fresh "a" in let Hp := fresh "Hp" in
  intros a Hp;
  repeat match goal with
  | Hp' : apresent (w_H ?W) ?m a |- apresent (w_H ?W) ?m a => exact Hp'
  | Hp' : apresent (w_H ?W) ?m1 a, HG' : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
      apply (apresent_grows _ _ _ _ HG') in Hp'
  end.
Ltac keep_chainW :=
  let a := fresh "a" in let Ha := fresh "Ha" in let HnW := fresh "HnW" in
  intros a Ha HnW;
  repeat match goal with
  | |- aview _ _ ?m a = aview _ _ ?m a => reflexivity
  | HF : frame_of _ _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- aview _ (w_H ?W) ?m2 a = _ =>
      rewrite (aview_kept_out _ _ (w_H W) m1 m2 HF a Ha HnW)
  end.

(* the write windows of the loop head's regions, as cells *)
Definition l_cells (a : Z) : Prop :=
(rg_send_eintr RG <= a < rg_send_eintr RG + 1) \/ (rg_nout RG <= a < rg_nout RG + 8) \/
(rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8) \/
(rg_client_broken RG <= a < rg_client_broken RG + 1).
Lemma l_cells_dec : forall a, l_cells a \/ ~ l_cells a.
Proof. intros a. unfold l_cells. lia. Qed.
Lemma l_wrange_cells : forall E a, img_env VAL A_LIM E -> in_wrange E l_regions a -> l_cells a.
Proof.
intros E a HEI (rr & Hin & Hr). unfold l_regions in Hin. cbn [In] in Hin.
pose proof (HEI (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U11.
pose proof (HEI (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U13.
pose proof (HEI (A_OBJ 14) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U14.
pose proof (HEI (A_OBJ 15) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U15.
pose proof (HEI (A_HI 17) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U17.
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi r_frame r_client r_eintr r_dead r_max r_nout r_capout r_out r_broken base_val] in Hr;
    rewrite ?U11, ?U13, ?U14, ?U15, ?U17 in Hr;
    first [ exfalso; clear - Hr; lia
          | unfold l_cells; rewrite ?HV11, ?HV13, ?HV14, ?HV15 in Hr; clear - Hr HH17; lia ] | ]).
destruct Hin.
Qed.
(* the five cells read off a state whose regions are the loop head's *)
Lemma l_vals : forall Ex ss ms ei nov capv outv,
st_ok_pi SEGS VAL Ex ss ms -> ss_mem ss = l_regions -> img_env VAL A_LIM Ex ->
ew Ex 32 = w64 ei -> ew Ex 34 = w64 nov -> ew Ex 35 = w64 capv -> ew Ex 36 = w64 outv ->
0 <= ei < 2 ^ 8 -> 0 <= nov < 2 ^ 64 -> 0 <= capv < 2 ^ 64 -> 0 <= outv < 2 ^ 64 ->
val_mem SEGS (ms_mem ms) (rg_send_eintr RG) 1 ei /\ val_mem SEGS (ms_mem ms) (rg_nout RG) 8 nov /\
val_mem SEGS (ms_mem ms) (rg_capout RG) 8 capv /\ val_mem SEGS (ms_mem ms) (rg_out RG) 8 outv /\
val_mem SEGS (ms_mem ms) (rg_client_broken RG) 1 0.
Proof.
intros Ex ss ms ei nov capv outv HS Hm HEI E32 E34 E35 E36 R1 R2 R3 R4.
assert (RN : forall i r, nth_error l_regions i = Some r -> region_ok SEGS Ex (ms_mem ms) r)
  by (intros i r Hi; apply (st_ok_pi_region_nth Ex ss ms i r HS); rewrite Hm; exact Hi).
pose proof (RN 2%nat r_eintr eq_refl) as G2. pose proof (RN 5%nat r_nout eq_refl) as G5.
pose proof (RN 6%nat r_capout eq_refl) as G6. pose proof (RN 7%nat r_out eq_refl) as G7.
pose proof (RN 8%nat r_broken eq_refl) as G8.
unfold r_eintr, r_nout, r_capout, r_out, r_broken in G2, G5, G6, G7, G8.
pose proof (HEI (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U11.
pose proof (HEI (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U13.
pose proof (HEI (A_OBJ 14) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U14.
pose proof (HEI (A_OBJ 15) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as U15.
pose proof (HEI (A_HI 17) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)) as U17.
split; [|split; [|split; [|split]]].
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 0 1%N (SOff 32 0) ei G2 U11 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HV11, Z.add_0_r in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 0 8%N (SOff 34 0) nov G5 U13 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HV13, Z.add_0_r in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 0 8%N (SOff 35 0) capv G6 U14 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HV14, Z.add_0_r in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 0 8%N (SOff 36 0) outv G7 U15 ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HV15, Z.add_0_r in V. exact V.
- pose proof (field_of_region Ex _ _ _ _ _ _ _ _ 92 1%N (SLit 0) 0 G8 U17 ltac:(cbn; left; reflexivity)
    ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V. rewrite HH17 in V. exact V.
Qed.

(* ---- The loop at a bound n, and the three kinds of round. ---- *)
Ltac sl_intro HI :=
unfold SLI in HI;
destruct HI as (lyL & SL & kL & evL & capL & outL & spent & rest &
  HJ & Hsp & H3 & H4 & Hgp & Htp & HraE & HR & M8 & M16 & HSV & Hcl & Hbr & Hsent & Hei1 & Hei2 & Hdd1 & Hev &
  HOUT & HGL & Hline0 & Hline1 & HROM & HLOK & HLG & Hcapq & Hdd2 & HMM & HLM & HAPK & HMOK & HMLE & HCOST & Hspent0 &
  HPerm0 & HPerm1 & HFR).
Lemma sl_aout_blks_in : forall ly S W mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W mem c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.

(* ---- The exit: the epilogue, then sl_post from the concrete facts at 0x828f8. ---- *)
Lemma sl_exit : forall regsE ly S W mem md c O mx no cap out Bl lyX SX WX regsX memX mdX k out' rest,
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S W mem md [] lyX SX WX memX mdX k ->
spZ regsX = spZ regsE - SL_FRAME -> getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (spZ regsE - SL_FRAME) regsE ->
apres_kept B W mem WX memX ->
mo_le MT S SX (sl_cost MT c mx no cap (Z.of_nat (length Bl))) ->
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) ->
Permutation (ablocks B lyX SX) (aout_blks (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ++ rest) ->
aout_at B RG lyX SX WX memX (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl) mx (sl_no c no (Z.of_nat (length Bl)))
  (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ->
(sl_live c (Z.of_nat (length Bl)) = false -> out' = out) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros regsE ly S W mem md c O mx no cap out Bl lyX SX WX regsX memX mdX k out' rest HJ Hsp H3 H4 Hra HSV HAPK HMLE HP1 HP2 HOUT HOFF.
apply (sl_epi B RG LAWS HG W ly S mem md (spZ regsE) _ lyX SX WX regsX memX mdX k regsE _ HJ eq_refl Hsp H3 H4 Hra HSV).
intros regs' mem' md' HP Hm' HJ'.
assert (GRX : mem_grows (mrestrict (w_H WX) memX) (mrestrict (w_H WX) mem')) by (intros x Hx; rewrite Hm'; exact Hx).
exists lyX, SX, regs', mem', md', k, out'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|].
split; [intros a H1 H2 H3' Hp; exact (apresent_grows _ _ _ _ GRX (HAPK a H1 H2 H3' Hp))|].
split; [exact HMLE|].
split; [exists rest; split; [exact HP1 | exact HP2]|].
split; [|exact HOFF].
apply (aout_at_kept B RG lyX SX WX memX lyX SX WX mem' _ _ _ _ _ _ HOUT); [|intros b Hb; exact (sl_aout_blks_in _ _ _ _ _ _ _ _ _ _ HOUT b Hb)].
intros r _ a _. split.
- exact (aview_eq_of SEGS (w_H WX) memX mem' a (Hm' _)).
- unfold arm. apply writable_kept. intros Hp. exact (apresent_grows _ _ _ _ GRX Hp).
Qed.

(* Everything SLI / SLM says of a memory carries to a memory with the same view at every byte and no less presence. *)
Lemma aview_all_of_bounded : forall H (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HV a. rewrite (aview_wrap64 H m' a), (aview_wrap64 H m a). apply HV. apply Z.mod_pos_bound. lia.
Qed.
Lemma sl_moved : forall (W' : world SEGS) m m',
(forall a, aview SEGS (w_H W') m' a = aview SEGS (w_H W') m a) ->
(forall a, apresent (w_H W') m a -> apresent (w_H W') m' a) ->
(forall ly' S' c' O' mx' no' cap' out', aout_at B RG ly' S' W' m c' O' mx' no' cap' out' ->
   aout_at B RG ly' S' W' m' c' O' mx' no' cap' out') /\
(forall line l, garr8 SEGS (arm W' m) line l -> garr8 SEGS (arm W' m') line l) /\
(rom_view SEGS W' m -> rom_view SEGS W' m') /\
(forall a n v, val_mem SEGS (mrestrict (w_H W') m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v).
Proof.
intros W' m m' HV HP.
split; [|split; [|split]].
- intros ly' S' c' O' mx' no' cap' out' HOUT.
  apply (aout_at_kept B RG ly' S' W' m ly' S' W' m' _ _ _ _ _ _ HOUT); [|exact (sl_aout_blks_in _ _ _ _ _ _ _ _ _ _ HOUT)].
  intros r _ a _. split; [exact (HV a)|]. apply writable_kept. exact (HP _).
- intros line l Hg. apply (garr8_frame SEGS (mrestrict (w_H W') m) (mrestrict (w_H W') m') line l Hg).
  intros x _. apply (mbyte_of_aview SEGS). exact (HV x).
- intros HR a Ha. rewrite (HV a). exact (HR a Ha).
- intros a n v Hv. apply (vm_keep W' m m' a n v); [intros x _; exact (HV x) | exact Hv].
Qed.

Lemma sl_arm_eintr : forall n, sl_loop_at B MT MMAX RG n -> forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL -> eiL <> 0 ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat (Datatypes.S n) ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hne Hb. sl_intro HI. 
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & HstkL & _).
pose proof HstkL as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresL.
assert (WS : SL_STK = 16512) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev,
  Hclr, Hbrr, Hddr, Heir.
(* numeric ranges of the cells *)
assert (Rcapout : 0 <= capL /\ 0 <= outL /\ no + sent <= 2 ^ 47 /\ capL <= 2 ^ 47 /\ outL <= 2 ^ 47).
{ destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hc1 & Hn1 & Hin1 & _)].
  - repeat split; lia.
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hin1) as (_ & Hp4 & Hpc & _).
    assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
    rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlen1 : 1 <= len <= 2 ^ 63 - 1) by lia.
pose proof (sl_loop_entry lyL SL WL regsL memL (spZ regsE) len line sent eiL (ct_dd c)
  (no + sent) capL outL mx evL (O ++ firstn (Z.to_nat sent) Bl)
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR Hlen1 ltac:(lia) ltac:(lia)
  M8 M16 HOUT ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
pose proof (pa_obj_img 11 ltac:(lia)) as Q11. pose proof (pa_obj_img 12 ltac:(lia)) as Q12.
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 14 ltac:(lia)) as Q14.
pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
assert (HSF : SL_FRAME = 128) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R19 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsL 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 8 8%bv eq_refl); exact (proj1 HR)).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact (proj1 (proj2 HR))).
assert (E22 : ew E 22 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 22 22%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 HR))))).
assert (E23 : ew E 23 = getr regsL 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = w64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = w64 (ct_dd c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = w64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = w64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = w64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (N11 : VAL 252%nat = rg_send_eintr RG) by exact HV11.
assert (NALL : VAL 252%nat = rg_send_eintr RG /\ VAL 299%nat + 248 = rg_send_eintr RG /\
  VAL 254%nat = rg_nout RG /\ VAL 255%nat = rg_capout RG /\ VAL 256%nat = rg_out RG /\
  VAL 297%nat + 92 = rg_client_broken RG)
  by (repeat split; first [exact HV11 | exact HH19 | exact HV13 | exact HV14 | exact HV15 | exact HH17]).
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
assert (N14 : VAL 255%nat = rg_capout RG) by exact HV14.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
assert (N17 : VAL 297%nat + 92 = rg_client_broken RG) by exact HH17.
assert (N19 : VAL 299%nat + 248 = rg_send_eintr RG) by exact HH19.
assert (N22 : VAL 302%nat + 260 = rg_nout RG) by exact HH22.
assert (N23 : VAL 303%nat + 864 = rg_capout RG) by exact HH23.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WL) memL)) by constructor.
lrun RUN HS HJ SHOK LBspan.
{ unfold ss_L; cbn [ss_mem];
  unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken.
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 11) HV11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 13) HV13|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 14) HV14|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 15) HV15|].
  apply awr_ok_x_cons_g; [awr_g (A_HI 17) HH17|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUN BR HS SHOK LBspan.
- exfalso. rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc by (clear - Heir; lia).
  apply Hne. apply Z.eqb_eq in Hc. lia.
- (* g_send_eintr <> 0: the EINTR round *)
  rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc by (clear - Heir; lia).
  assert (HeiE : eiL = 1) by (clear - Hc Heir; apply Z.eqb_neq in Hc; lia).
  assert (HREL : VAL (A_OBJ 11) = VAL (A_HI 19) + 248) by (rewrite HV11, <- HH19; reflexivity).
  prebase HS 2%nat (A_HI 19) 248 HREL.
  lrun RUN HS HJ SHOK LBspan.
  { apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_cons_g; [awr_g 299%nat N19|].
    apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
    apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
    apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
    apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
    apply awr_ok_x_nil. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS (G_SL B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      WL (ms_regs ms0) (ms_mem ms0) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out))
      ly S W mem md ([] : list (Z * Z)) lyL SL _ kL (- SL_FRAME) (Z_to_bv 64 (BASE + 1268)) HG eq_refl HJ).
    - unfold spZ at 1. rewrite Q2, Usp. clear. unfold SL_FRAME. lia.
    - unfold SL_FRAME. reflexivity.
    - unfold SL_FRAME. clear. lia.
    - clear. lia.
    - clear. vm_compute. intros Hx. discriminate Hx.
    - rewrite Q3, E3, H3. exact Hgp.
    - rewrite Q4, E4, H4. exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
    - intros _. right. intros [].
    - intros a [].
    - intros a [].
    - intros HPRE _. exact (AERRNO lyL SL WL (ms_regs ms0) (ms_mem ms0) _ HPRE). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
  assert (WRc : forall a, writable_at SEGS (arm WL memL) a -> writable_at SEGS (mrestrict (w_H WL) mem2) a).
  { intros a Ha. apply (writable_kept (w_H WL) (ms_mem ms0) mem2 a (fun Hp => Hpres2 _ Hp)).
    eapply writable_at_grows; [exact HG1|]. eapply writable_at_grows; [exact HG0|]. exact Ha. }
  jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H WL) mem2) HP2 [0;1;2;3;4;5;6;7;8]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    assert (RKM : forall lo hi, 0x10000 - 1000 <= lo -> hi <= 0x5fb000 + 1000 ->
      forall a, lo <= a < hi -> mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem ms0)) a).
    { intros lo hi Hl Hh a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
      [ clear - Ha Hl Hh; lia | intros [] | clear - Ha Hl Hh QSP C1 HSF HES; lia ]. }
    assert (RKS : forall a, spZ regsE - SL_FRAME <= a < spZ regsE ->
      mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem ms0)) a).
    { intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
      [ clear - Ha QSP C1 HSF; lia | intros [] | clear - Ha HSF HES; lia ]. }
    repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?(HEI 250%nat ltac:(cbv; lia)), ?(HEI 299%nat ltac:(cbv; lia)), ?(HEI 253%nat ltac:(cbv; lia)),
            ?(HEI 301%nat ltac:(cbv; lia)), ?(HEI 254%nat ltac:(cbv; lia)), ?(HEI 255%nat ltac:(cbv; lia)),
            ?(HEI 256%nat ltac:(cbv; lia)), ?(HEI 297%nat ltac:(cbv; lia)), ?Usp;
    try change (VAL 250%nat) with (VAL (A_OBJ 9)); try change (VAL 299%nat) with (VAL (A_HI 19));
    try change (VAL 253%nat) with (VAL (A_OBJ 12)); try change (VAL 301%nat) with (VAL (A_HI 21));
    try change (VAL 254%nat) with (VAL (A_OBJ 13)); try change (VAL 255%nat) with (VAL (A_OBJ 14));
    try change (VAL 256%nat) with (VAL (A_OBJ 15)); try change (VAL 297%nat) with (VAL (A_HI 17));
    first
    [ intros a Ha; exfalso; clear - Ha; lia
    | intros a Ha; apply RKS; clear - Ha HSF; lia
    | apply RKM; clear - Q9 Q10 Q11 Q12 Q13 Q14 Q15 HSM HV9 HV10 HV11 HV12 HV13 HV14 HV15
        HH17 HH19 HH21 HH22 HH23 HH24; lia
    | intros a Ha _; apply WRc;
      first
      [ (replace a with (rg_send_eintr RG + (a - rg_send_eintr RG)) by (clear - Ha; lia);
         apply Wei; clear - Ha HH19 HV11; lia)
      | (replace a with (rg_nout RG + (a - rg_nout RG)) by (clear - Ha; lia);
         apply Wno; clear - Ha HV13 HH22; lia)
      | (replace a with (rg_capout RG + (a - rg_capout RG)) by (clear - Ha; lia);
         apply Wcap; clear - Ha HV14 HH23; lia)
      | (replace a with (rg_out RG + (a - rg_out RG)) by (clear - Ha; lia);
         apply Wout; clear - Ha HV15 HH24; lia)
      | (replace a with (rg_client_broken RG + (a - rg_client_broken RG)) by (clear - Ha; lia);
         apply Wbr; clear - Ha HH17; lia) ] ]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m)
    by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  clear HEa.
  prreg HS (10%bv : bv 5) R10.
  assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
  { assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
    { intros i Hi. assert (Hin : inG (G_SL B RG) (as_errno B + i)) by (clear - Hi; ing_tac).
      exact (proj1 (HG _ Hin)). }
    pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0.
    pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. clear - P0 P3. lia. }
  assert (WRerr : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H WL) mem2) (as_errno B + o))
    by (intros o Ho; apply WRc; exact (Wev o Ho)).
  assert (F42 : ew Ea 42 = Z_to_bv 64 (as_errno B))
    by (rewrite <- R10, Herr, <- HERRNO; reflexivity).
  assert (BVEa : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
    by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
  assert (Uspa : base_val Ea (Some 2%nat) = spZ regsE - SL_FRAME)
    by (cbn [base_val]; rewrite (OLDa 2%nat ltac:(clear; lia)); exact Usp).
  assert (BA42 : base_val Ea (Some 42%nat) = as_errno B)
    by (cbn [base_val]; rewrite F42; apply unsigned_lit_small; clear - HERRI; lia).
  apply (st_ok_pi_add_fact _ _ _ 42%nat OBJF) in HS;
    [|unfold afact_ok, OBJF; cbn [af_lo af_hi af_al2]; rewrite F42,
      (unsigned_lit_small (as_errno B)) by (clear - HERRI; lia);
      rewrite Z.pow_0_r, Z.mod_1_r; clear - HERRI; repeat split; lia].
  apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 42%nat) 0 4 0 4 [])) in HS;
    [ | vm_compute; reflexivity
      | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
        rewrite BA42; split; [clear - HERRI; lia|]; split; [clear - HERRI; lia|];
        split; [|apply Forall_nil]; intros o Ho; cbn [ms_mem restrict]; exact (WRerr o Ho)
      | cbn [ss_mem add_atom]; apply all_disjoint_of_extents; unfold extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
        rewrite BA42, ?(BVEa 250%nat ltac:(cbv; lia)), ?(BVEa 299%nat ltac:(cbv; lia)),
          ?(BVEa 253%nat ltac:(cbv; lia)), ?(BVEa 301%nat ltac:(cbv; lia)),
          ?(BVEa 254%nat ltac:(cbv; lia)), ?(BVEa 255%nat ltac:(cbv; lia)),
          ?(BVEa 256%nat ltac:(cbv; lia)), ?(BVEa 297%nat ltac:(cbv; lia)), ?Uspa;
        change (VAL 250%nat) with (VAL (A_OBJ 9)); change (VAL 299%nat) with (VAL (A_HI 19));
        change (VAL 253%nat) with (VAL (A_OBJ 12)); change (VAL 301%nat) with (VAL (A_HI 21));
        change (VAL 254%nat) with (VAL (A_OBJ 13)); change (VAL 255%nat) with (VAL (A_OBJ 14));
        change (VAL 256%nat) with (VAL (A_OBJ 15)); change (VAL 297%nat) with (VAL (A_HI 17));
        cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
        pose proof (sl_rgd 10 2 ltac:(lia) ltac:(lia) ltac:(lia)) as D2;
        pose proof (sl_rgd 10 4 ltac:(lia) ltac:(lia) ltac:(lia)) as D4;
        pose proof (sl_rgd 10 5 ltac:(lia) ltac:(lia) ltac:(lia)) as D5;
        pose proof (sl_rgd 10 6 ltac:(lia) ltac:(lia) ltac:(lia)) as D6;
        pose proof (sl_rgd 10 7 ltac:(lia) ltac:(lia) ltac:(lia)) as D7;
        pose proof (sl_rgd 10 8 ltac:(lia) ltac:(lia) ltac:(lia)) as D8;
        pose proof (sl_rgd 10 9 ltac:(lia) ltac:(lia) ltac:(lia)) as D9;
        pose proof (sl_rgd 10 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D3;
        cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9;
        unfold zdisj in D2, D3, D4, D5, D6, D7, D8, D9;
        cbn [fst snd] in D2, D3, D4, D5, D6, D7, D8, D9;
        repeat split;
        first [ solve [ clear - HERRI QSP C1 HSF; lia ]
              | match goal with H : _ \/ _ |- _ => solve [ clear - H HV9 HV11 HV12 HV13 HV14 HV15
                  HH17 HH19 HH21 HH22 HH23 HH24; lia ] end ] ].
  assert (UB : U Ea BxL = SHADOW_OFF).
  { unfold BxL. rewrite (U_atom Ea 23%nat SB); [reflexivity | | clear; unfold SB; lia].
    rewrite (OLDa 23%nat ltac:(clear; lia)), E23, R23. reflexivity. }
  assert (UE42 : U Ea (SOff 42%nat 0) = as_errno B)
    by (apply (U_atom Ea 42%nat); [exact F42 | clear - HERRI; lia]).
  assert (SHOKa : sh_ok SEGS BxL [mkSHE 42%nat 0 4] Ea (mrestrict (w_H WL) mem2)).
  { constructor; [|constructor].
    eapply (shent_ok_of_range SEGS (w_H WL) mem2 Ea BxL 42%nat (as_errno B) 4 (as_errno B) 0 4).
    - eapply errno_ra. eapply ajournal_gx_AR. exact HJ2.
    - exact UB.
    - exact UE42.
    - clear; lia.
    - clear; lia.
    - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. clear - Hx HERRI UB.
      rewrite <- SB_SHADOW_OFF. unfold SB. lia. }
  lrun RUN HS HJ2 SHOKa LBspan.
  {
    apply awr_ok_x_cons_g;
      [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BA42;
        intros a Ha; clear - Ha; ing_tac |].
    apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_cons_g; [awr_gb BVEa 299%nat N19|].
    apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_cons_g; [awr_gb BVEa 254%nat N13|].
    apply awr_ok_x_cons_g; [awr_gb BVEa 255%nat N14|].
    apply awr_ok_x_cons_g; [awr_gb BVEa 256%nat N15|].
    apply awr_ok_x_cons_g; [awr_gb BVEa 297%nat N17|].
    apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (BVEb : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ev (Some m) = VAL m)
      by (intros m Hm; cbn [base_val]; rewrite !ew_ewset_other by (clear - Hm; unfold A_LIM in Hm; lia);
          exact (HEIa m Hm));
    assert (BA42b : base_val Ev (Some 42%nat) = as_errno B)
      by (cbn [base_val]; rewrite !ew_ewset_other by (repeat match goal with X : _ |- _ => clear X end; lia);
          cbn [base_val] in BA42; exact BA42)
  end.
  assert (Hs0 : sent = 0)
    by (clear - Hei2 HeiE Hsent; destruct (Z.eq_dec sent 0) as [Hz|Hz];
        [exact Hz | exfalso; pose proof (Hei2 ltac:(lia)); lia]).
  assert (F22 : ew Ea 22 = w64 sent) by (rewrite (OLDa 22%nat ltac:(clear; lia)); exact E22).
  assert (F8 : ew Ea 8 = w64 len) by (rewrite (OLDa 8%nat ltac:(clear; lia)); exact E8).
  psrr_branch_tok RUN BR HS SHOKa LBspan.
  + lrun_to RUNTO HS HJ2 SHOKa LBspan A_sl_loop.
    {
    apply awr_ok_x_cons_g;
      [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BA42b;
        intros a Ha; clear - Ha; ing_tac |].
    apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_cons_g; [awr_gb BVEb 299%nat N19|].
    apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
    apply awr_ok_x_cons_g; [awr_gb BVEb 254%nat N13|].
    apply awr_ok_x_cons_g; [awr_gb BVEb 255%nat N14|].
    apply awr_ok_x_cons_g; [awr_gb BVEb 256%nat N15|].
    apply awr_ok_x_cons_g; [awr_gb BVEb 297%nat N17|].
    apply awr_ok_x_nil. }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ inG (G_SL B RG) a ->
      ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME) ->
      aview SEGS (w_H WL) (ms_mem ms2) a = aview SEGS (w_H WL) memL a).
    { intros a Ha HnG Hsc.
      assert (K1 : aview SEGS (w_H WL) (ms_mem ms2) a = aview SEGS (w_H WL) (ms_mem ms1) a).
      { apply (aview_kept_out _ _ (w_H WL) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha). nowr BVEb BA42b NALL HnG. }
      assert (K2 : aview SEGS (w_H WL) (ms_mem ms1) a = aview SEGS (w_H WL) mem2 a).
      { apply (aview_kept_out _ _ (w_H WL) mem2 (ms_mem ms1) HFr1 a Ha). nowr BVEa BA42 NALL HnG. }
      assert (K3 : aview SEGS (w_H WL) mem2 a = aview SEGS (w_H WL) (ms_mem ms0) a).
      { apply Hfr2; [exact Ha | intros HFx; destruct HFx | clear - Hsc HSF HES; lia]. }
      assert (K4 : aview SEGS (w_H WL) (ms_mem ms0) a = aview SEGS (w_H WL) (ms_mem ms) a).
      { apply (aview_kept_out _ _ (w_H WL) (ms_mem ms) (ms_mem ms0) HFr0 a Ha). nowr BVE BA42 NALL HnG. }
      assert (K5 : aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H WL) memL a).
      { apply (aview_kept_out _ _ (w_H WL) memL (ms_mem ms) HFr a Ha). nowr BVE BA42 NALL HnG. }
      rewrite K1, K2, K3, K4, K5. reflexivity. }
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
    prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
    prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
    assert (HRL : sl_regsL (ms_regs ms2) len line 0).
    { unfold sl_regsL.
      rewrite P8, P9, P19, P22, P23, P20, P21, P24, P25, P26, P27.
      rewrite (OLDa 8%nat ltac:(clia)), (OLDa 9%nat ltac:(clia)), (OLDa 22%nat ltac:(clia)), (OLDa 23%nat ltac:(clia)).
      rewrite E8, E9, E22, E23, R23, Hs0.
      rewrite !(ew_img _ _ HEIa) by (cbv; lia).
      repeat split; reflexivity. }
    assert (HSP2 : spZ (ms_regs ms2) = spZ regsE - SL_FRAME).
    { unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp. }
    assert (HR3 : getr (ms_regs ms2) 3 = getr regsE 3) by (rewrite P3, (OLDa 3%nat ltac:(clia)), E3; exact H3).
    assert (HR4 : getr (ms_regs ms2) 4 = getr regsE 4) by (rewrite P4, (OLDa 4%nat ltac:(clia)), E4; exact H4).
    (* presence and writability survive the round *)
    assert (PRall : forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem ms2) a).
    { intros a Hp. apply (apresent_grows _ _ _ _ HG3). apply (apresent_grows _ _ _ _ HG2).
      apply Hpres2. apply (apresent_grows _ _ _ _ HG1). apply (apresent_grows _ _ _ _ HG0). exact Hp. }
    assert (WRall : forall a, writable_at SEGS (arm WL memL) a ->
      writable_at SEGS (mrestrict (w_H WL) (ms_mem ms2)) a).
    { intros a Hw. eapply writable_at_grows; [exact HG3|]. eapply writable_at_grows; [exact HG2|].
      apply WRc. exact Hw. }
    assert (GLO : forall a, inG (G_SL B RG) a -> 0x10000 <= a < 0x5fb000)
      by (intros a Ha; exact (pa_img_range _ (proj1 (HG a Ha)))).
    (* bytes below alloc_ceiling and outside G_SL, and the frame's bytes, keep their view *)
    assert (KLO : forall x, 0 <= x < alloc_ceiling -> ~ inG (G_SL B RG) x ->
      aview SEGS (w_H WL) (ms_mem ms2) x = aview SEGS (w_H WL) memL x)
      by (intros x Hx Hg; apply KEEP; [clear - Hx C1; lia | exact Hg | clear - Hx Hceil Hslo WS HSF HES; lia]).
    assert (KFR : forall x, spZ regsE - SL_FRAME <= x < spZ regsE ->
      aview SEGS (w_H WL) (ms_mem ms2) x = aview SEGS (w_H WL) memL x)
      by (intros x Hx; apply KEEP; [clear - Hx QSP C1 HSF; lia
        | intros Hg; pose proof (GLO x Hg) as HL; clear - Hx HL QSP C1 HSF; lia
        | clear - Hx HSF HES; lia]).
    (* the cells, read off the final state's regions: errno, client, eintr, dead, max, nout, capout, out, broken *)
    lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF =>
      pose proof (st_ok_pi_region_nth Ev ssF msF 0 _ HS eq_refl) as RG0;
      pose proof (st_ok_pi_region_nth Ev ssF msF 2 _ HS eq_refl) as RG2;
      pose proof (st_ok_pi_region_nth Ev ssF msF 3 _ HS eq_refl) as RG3;
      pose proof (st_ok_pi_region_nth Ev ssF msF 4 _ HS eq_refl) as RG4;
      pose proof (st_ok_pi_region_nth Ev ssF msF 5 _ HS eq_refl) as RG5;
      pose proof (st_ok_pi_region_nth Ev ssF msF 6 _ HS eq_refl) as RG6;
      pose proof (st_ok_pi_region_nth Ev ssF msF 7 _ HS eq_refl) as RG7;
      pose proof (st_ok_pi_region_nth Ev ssF msF 8 _ HS eq_refl) as RG8;
      pose proof (st_ok_pi_region_nth Ev ssF msF 9 _ HS eq_refl) as RG9
    end.
    cbn [ms_mem restrict] in RG0, RG2, RG3, RG4, RG5, RG6, RG7, RG8, RG9.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (EB : forall m, (m < 38)%nat -> ew Ev m = ew E m)
        by (intros m Hm; rewrite !ew_ewset_other by (clear - Hm; lia); exact (OLDa m Hm));
      assert (UI : forall m, (A_TEXT <= m < A_LIM)%nat -> bv_unsigned (ew Ev m) = VAL m) by exact HEI3;
      assert (U42 : bv_unsigned (ew Ev 42) = as_errno B) by exact BA42b;
      assert (WMX : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_send_max RG) 8 mx)
        by (rewrite <- HH21; exact (field_of_region Ev _ (A_HI 21) _ _ _ _ _ _ 140 8 (SOff 37 0) mx RG5
              (UI 301%nat ltac:(cbv; lia)) (or_introl eq_refl)
              ltac:(cbn [sv_denot]; rewrite (EB 37%nat ltac:(clia)), E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
              ltac:(clear - Hmxr; cbn; lia) ltac:(cbn; lia)));
      assert (WNO : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_nout RG) 8 (no + sent))
        by (replace (rg_nout RG) with (VAL (A_OBJ 13) + 0) by (rewrite Z.add_0_r; exact HV13);
            exact (field_of_region Ev _ (A_OBJ 13) _ _ _ _ _ _ 0 8 (SOff 34 0) (no + sent) RG6
              (UI 254%nat ltac:(cbv; lia)) (or_introl eq_refl)
              ltac:(cbn [sv_denot]; rewrite (EB 34%nat ltac:(clia)), E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
              ltac:(clear - Rn47 HlenO; cbn; lia) ltac:(cbn; lia)));
      assert (WCAP : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_capout RG) 8 capL)
        by (replace (rg_capout RG) with (VAL (A_OBJ 14) + 0) by (rewrite Z.add_0_r; exact HV14);
            exact (field_of_region Ev _ (A_OBJ 14) _ _ _ _ _ _ 0 8 (SOff 35 0) capL RG7
              (UI 255%nat ltac:(cbv; lia)) (or_introl eq_refl)
              ltac:(cbn [sv_denot]; rewrite (EB 35%nat ltac:(clia)), E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
              ltac:(clear - Rc0 Rc47; cbn; lia) ltac:(cbn; lia)));
      assert (WOUT : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_out RG) 8 outL)
        by (replace (rg_out RG) with (VAL (A_OBJ 15) + 0) by (rewrite Z.add_0_r; exact HV15);
            exact (field_of_region Ev _ (A_OBJ 15) _ _ _ _ _ _ 0 8 (SOff 36 0) outL RG8
              (UI 256%nat ltac:(cbv; lia)) (or_introl eq_refl)
              ltac:(cbn [sv_denot]; rewrite (EB 36%nat ltac:(clia)), E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
              ltac:(clear - Ro0 Ro47; cbn; lia) ltac:(cbn; lia)));
      assert (WCL : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_client RG) 4 3)
        by (replace (rg_client RG) with (VAL (A_OBJ 9) + 0) by (rewrite Z.add_0_r; exact HV9);
            exact (field_of_region Ev _ (A_OBJ 9) _ _ _ _ _ _ 0 4 (SLit 3) 3 RG2
              (UI 250%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
              ltac:(cbn; lia) ltac:(cbn; lia)));
      assert (WBR : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_client_broken RG) 1 0)
        by (rewrite <- HH17;
            exact (field_of_region Ev _ (A_HI 17) _ _ _ _ _ _ 92 1 (SLit 0) 0 RG9
              (UI 297%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
              ltac:(cbn; lia) ltac:(cbn; lia)));
      assert (WDD : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_send_dead RG) 1 (ct_dd c))
        by (replace (rg_send_dead RG) with (VAL (A_OBJ 12) + 0) by (rewrite Z.add_0_r; exact HV12);
            exact (field_of_region Ev _ (A_OBJ 12) _ _ _ _ _ _ 0 1 (SOff 33 0) (ct_dd c) RG4
              (UI 253%nat ltac:(cbv; lia)) (or_introl eq_refl)
              ltac:(cbn [sv_denot]; rewrite (EB 33%nat ltac:(clia)), E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
              ltac:(clear - Hddr; cbn; lia) ltac:(cbn; lia)));
      assert (WEI : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (rg_send_eintr RG) 1 0)
        by (rewrite <- HH19;
            exact (field_of_region Ev _ (A_HI 19) _ _ _ _ _ _ 248 1 (SLit 0) 0 RG3
              (UI 299%nat ltac:(cbv; lia)) (or_introl eq_refl) eq_refl
              ltac:(cbn; lia) ltac:(cbn; lia)));
      assert (WER : val_mem SEGS (mrestrict (w_H WL) (ms_mem ms2)) (as_errno B) 4 4)
        by (replace (as_errno B) with (as_errno B + 0) at 1 by (apply Z.add_0_r);
            exact (field_of_region Ev _ 42 _ _ _ _ _ _ 0 4 (SLit 4) 4 RG0
              U42 (or_introl eq_refl) eq_refl
              ltac:(cbn; lia) ltac:(cbn; lia)))
    end.
    (* the line, the g_out block and the read-only bytes lie below alloc_ceiling and outside G_SL *)
    assert (GL2 : garr8 SEGS (arm WL (ms_mem ms2)) line (bzs Bl)).
    { apply (garr8_keep WL memL (ms_mem ms2)); [|exact HGL].
      intros x Hx. unfold bzs in Hx. rewrite length_map in Hx. change (Z.of_nat (length Bl)) with len in Hx.
      apply KLO; [|exact (HLG x Hx)].
      destruct HLOK as [HL0 | [(q & m & Hqm & _ & Hq1 & Hq2) | (HIr & _ & _)]];
        [clear - HL0 Hlen1; lia | |].
      - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL q m HARL Hqm) as (_ & _ & Hpc & _).
        clear - Hx Hq1 Hq2 Hpc Hline0. lia.
      - pose proof (pa_img_range _ (HIr x Hx)) as HXI. clear - HXI C1. lia. }
    assert (ROM2 : rom_view SEGS WL (ms_mem ms2)).
    { intros a Ha. rewrite KLO; [exact (HROM a Ha) | | intros Hg; exact (HGR a Hg Ha)].
      destruct Ha as (sg & Hsg & _ & Hr).
      assert (HIa : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
      pose proof (pa_img_range _ HIa) as HXI. clear - HXI C1. lia. }
    assert (BLK2 : (capL = 0 /\ outL = 0 /\ no + sent = 0) \/
      (0 < capL /\ no + sent <= capL /\ In (outL, capL) (ablocks B lyL SL) /\
       exists junk, Z.of_nat (length junk) = capL - (no + sent) /\
         garr8 SEGS (arm WL (ms_mem ms2)) outL (bzs ((O ++ firstn (Z.to_nat sent) Bl) ++ junk)))).
    { destruct Hblk as [Hb0 | (Hbc & Hbn & Hbi & junk & Hbj & Hbg)]; [left; exact Hb0 | right].
      split; [exact Hbc|]. split; [exact Hbn|]. split; [exact Hbi|].
      exists junk. split; [exact Hbj|].
      apply (garr8_keep WL memL (ms_mem ms2)); [|exact Hbg].
      destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hbi) as (_ & _ & Hpc & _).
      assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
      intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
      destruct (al_client_img _ _ LAWS lyL SL WL memL mdL x HARL) as (_ & Himg).
      { left. exists outL, capL. split; [exact Hbi|]. rewrite Hrq. clear - Hx Hbj HlenO. lia. }
      apply KLO; [clear - Hx Hbj HlenO Hpc Hrq Ro0 C1; lia|].
      intros HgX. exact (Himg (proj1 (HG x HgX))). }
    (* ---- the back edge: SLI at the new head with sent = 0, g_send_eintr = 0, errno = EINTR ---- *)
    assert (Hci : ct_ei c = 1) by (clear - Hei1 HeiE; lia).
    assert (HEV : (if (ct_ei c =? 1) && (0 =? 0) then send_line_c.EINTR_V else ct_ev c) = 4)
      by (rewrite Hci; reflexivity).
    subst sent.
    apply (IH regsE ly S W mem md c O mx no cap out line Bl WL (ms_regs ms2) (ms_mem ms2) _ 0 0).
    2: { clear - Hb HeiE. unfold len in Hb. rewrite Nat2Z.inj_succ in Hb. lia. }
    unfold SLI. cbv zeta.
    exists lyL, SL, kL, (if (ct_ei c =? 1) && (0 =? 0) then send_line_c.EINTR_V else ct_ev c), capL, outL, spent, rest.
    split; [exact HJ2|]. split; [exact HSP2|]. split; [exact HR3|]. split; [exact HR4|].
    split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|]. split; [exact HRL|].
    split; [apply (vm_keep WL memL (ms_mem ms2)); [intros x Hx; apply KFR; clear - Hx HSF; lia | exact M8]|].
    split; [apply (vm_keep WL memL (ms_mem ms2)); [intros x Hx; apply KFR; clear - Hx HSF; lia | exact M16]|].
    split; [intros i Hi; apply (vm_keep WL memL (ms_mem ms2));
      [intros x Hx; apply KFR; clear - Hx Hi HSF; lia | exact (HSV i Hi)]|].
    split; [exact Hcl|]. split; [exact Hbr|]. split; [clear - Hlen1; lia|].
    split; [right; reflexivity|]. split; [intros _; reflexivity|]. split; [intros _; reflexivity|].
    split; [reflexivity|].
    split.
    { unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev]. rewrite HEV.
      split; [exact WMX|]. split; [intros i Hi; apply WRall; exact (Wmx i Hi)|].
      split; [exact WNO|]. split; [intros i Hi; apply WRall; exact (Wno i Hi)|].
      split; [exact WCAP|]. split; [intros i Hi; apply WRall; exact (Wcap i Hi)|].
      split; [exact WOUT|]. split; [intros i Hi; apply WRall; exact (Wout i Hi)|].
      split; [exact WCL|]. split; [intros i Hi; apply WRall; exact (Wcl i Hi)|].
      split; [exact WBR|]. split; [intros i Hi; apply WRall; exact (Wbr i Hi)|].
      split; [exact WDD|]. split; [intros i Hi; apply WRall; exact (Wdd i Hi)|].
      split; [exact WEI|]. split; [intros i Hi; apply WRall; exact (Wei i Hi)|].
      split; [exact WER|]. split; [intros i Hi; apply WRall; exact (Wev i Hi)|].
      split; [clear; lia|].
      split; [left; reflexivity|]. split; [left; reflexivity|]. split; [exact Hddr|]. split; [left; reflexivity|].
      split; [exact Hmxr|]. split; [exact HlenO|].
      exact BLK2. }
    split; [exact GL2|]. split; [exact Hline0|]. split; [exact Hline1|]. split; [exact ROM2|].
    split; [exact HLOK|]. split; [exact HLG|]. split; [exact Hcapq|]. split; [exact Hdd2|].
    split; [exact HMM|]. split; [exact HLM|].
    split; [intros a Ha1 Ha2 Ha3 Hp; apply PRall; exact (HAPK a Ha1 Ha2 Ha3 Hp)|].
    split; [exact HMOK|]. split; [exact HMLE|]. split; [exact HCOST|]. split; [exact Hspent0|].
    split; [exact HPerm0|]. split; [exact HPerm1|]. exact HFR.
  + exfalso.
    lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (G22 : ew Ev 22 = w64 sent) by (rewrite !ew_ewset_other by (clear; lia); exact F22);
      assert (G8 : ew Ev 8 = w64 len) by (rewrite !ew_ewset_other by (clear; lia); exact F8);
      rewrite branch_ltu_U, (U_atom Ev 22%nat sent G22), (U_atom Ev 8%nat len G8) in Hc0
        by (clear - Hsent Hlen1; lia)
    end.
    clear - Hc0 Hsent Hs0 Hlen1. apply Z.ltb_ge in Hc0. lia.
Qed.

(* aout_at_broken with its keep premise asked only below alloc_ceiling: the scratch of the __errno_location call lies
   above alloc_ceiling and may change *)
Local Ltac sl_kl HK i C CC :=
  let x := fresh "x" in let Hx := fresh "Hx" in let D1 := fresh "D" in let D2 := fresh "D" in
  intros x Hx;
  pose proof (sl_rgd i 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D1;
  pose proof (sl_rgd i 10 ltac:(lia) ltac:(lia) ltac:(lia)) as D2;
  cbn [nth] in D1, D2; unfold zdisj in D1, D2; cbn [fst snd] in D1, D2;
  apply HK; [ clear - Hx C CC; lia | clear - Hx D1; lia | clear - Hx D2; lia ].
Lemma aout_at_broken_lo : forall ly S (W W' : world SEGS) mem mem' c O mx no cap out ev',
aout_at B RG ly S W mem c O mx no cap out ->
(forall a, 0 <= a < alloc_ceiling -> ~ (rg_client_broken RG <= a < rg_client_broken RG + 1) ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W' mem' a) ->
(forall a, out <= a < out + cap -> 0 <= a < alloc_ceiling /\
   ~ (rg_client_broken RG <= a < rg_client_broken RG + 1) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W' mem') (rg_client_broken RG) 1 1 ->
awr W' mem' (rg_client_broken RG) 1 ->
val_mem SEGS (arm W' mem') (as_errno B) 4 ev' -> 0 <= ev' < 2 ^ 32 ->
awr W' mem' (as_errno B) 4 ->
aout_at B RG ly S W' mem' (CTL (ct_cl c) 1 (ct_dd c) (ct_ei c) ev') O mx no cap out.
Proof.
intros ly S W W' mem mem' c O mx no cap out ev'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HO Vb Wb Vv Ev Wv.
pose proof asan_consts as (C1 & _).
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 11 ltac:(lia)) as Q11.
pose proof (pa_obj_img 12 ltac:(lia)) as Q12. pose proof (pa_obj_img 13 ltac:(lia)) as Q13.
pose proof (pa_obj_img 14 ltac:(lia)) as Q14. pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
rewrite HV9 in Q9. rewrite HV11 in Q11. rewrite HV12 in Q12. rewrite HV13 in Q13.
rewrite HV14 in Q14. rewrite HV15 in Q15.
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W mem); [sl_kl HK 6%nat HSM C1 | exact H1]|].
split; [apply (akept_awr W mem); [sl_kl HK 6%nat HSM C1 | exact H2]|].
split; [apply (akept_vm W mem); [sl_kl HK 7%nat Q13 C1 | exact H3]|].
split; [apply (akept_awr W mem); [sl_kl HK 7%nat Q13 C1 | exact H4]|].
split; [apply (akept_vm W mem); [sl_kl HK 8%nat Q14 C1 | exact H5]|].
split; [apply (akept_awr W mem); [sl_kl HK 8%nat Q14 C1 | exact H6]|].
split; [apply (akept_vm W mem); [sl_kl HK 9%nat Q15 C1 | exact H7]|].
split; [apply (akept_awr W mem); [sl_kl HK 9%nat Q15 C1 | exact H8]|].
split; [apply (akept_vm W mem); [sl_kl HK 2%nat Q9 C1 | exact H9]|].
split; [apply (akept_awr W mem); [sl_kl HK 2%nat Q9 C1 | exact H10]|].
split; [exact Vb|]. split; [exact Wb|].
split; [apply (akept_vm W mem); [sl_kl HK 5%nat Q12 C1 | exact H13]|].
split; [apply (akept_awr W mem); [sl_kl HK 5%nat Q12 C1 | exact H14]|].
split; [apply (akept_vm W mem); [sl_kl HK 4%nat Q11 C1 | exact H15]|].
split; [apply (akept_awr W mem); [sl_kl HK 4%nat Q11 C1 | exact H16]|].
split; [exact Vv|]. split; [exact Wv|]. split; [exact Ev|].
split; [exact H20|]. split; [right; reflexivity|]. split; [exact H22|].
split; [exact H23|].
split; [exact H24|]. split; [exact H25|].
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W mem); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
destruct (HO x ltac:(clear - Hx H25 Hj; lia)) as (N0 & N1 & N2). exact (HK x N0 N1 N2).
Qed.
(* a byte outside g_client_broken and errno is outside every write window of the dead path's runs *)
Local Ltac nowr_dl BV BA HH Hb He :=
  let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rr & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      first [ solve [ clear - Hr; lia ]
            | solve [ rewrite (BV 297%nat ltac:(cbv; lia)) in Hr; clear - Hr Hb HH; lia ]
            | solve [ rewrite BA in Hr; clear - Hr He; lia ] ] | ]);
  try destruct Hin.

(* the dead round: g_send_dead <> 0 (then sent = 0): errno := EPIPE, g_client_broken := 1, the epilogue *)
Lemma sl_arm_dead : forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL -> eiL = 0 -> ct_dd c = 1 ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hdd. sl_intro HI. 
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & HstkL & _).
pose proof HstkL as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresL.
assert (WS : SL_STK = 16512) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev,
  Hclr, Hbrr, Hddr, Heir.
(* numeric ranges of the cells *)
assert (Rcapout : 0 <= capL /\ 0 <= outL /\ no + sent <= 2 ^ 47 /\ capL <= 2 ^ 47 /\ outL <= 2 ^ 47).
{ destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hc1 & Hn1 & Hin1 & _)].
  - repeat split; lia.
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hin1) as (_ & Hp4 & Hpc & _).
    assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
    rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlen1 : 1 <= len <= 2 ^ 63 - 1) by lia.
pose proof (sl_loop_entry lyL SL WL regsL memL (spZ regsE) len line sent eiL (ct_dd c)
  (no + sent) capL outL mx evL (O ++ firstn (Z.to_nat sent) Bl)
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR Hlen1 ltac:(lia) ltac:(lia)
  M8 M16 HOUT ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
pose proof (pa_obj_img 11 ltac:(lia)) as Q11. pose proof (pa_obj_img 12 ltac:(lia)) as Q12.
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 14 ltac:(lia)) as Q14.
pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
assert (HSF : SL_FRAME = 128) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R19 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsL 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 8 8%bv eq_refl); exact (proj1 HR)).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact (proj1 (proj2 HR))).
assert (E22 : ew E 22 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 22 22%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 HR))))).
assert (E23 : ew E 23 = getr regsL 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = w64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = w64 (ct_dd c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = w64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = w64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = w64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (N11 : VAL 252%nat = rg_send_eintr RG) by exact HV11.
assert (NALL : VAL 252%nat = rg_send_eintr RG /\ VAL 299%nat + 248 = rg_send_eintr RG /\
  VAL 254%nat = rg_nout RG /\ VAL 255%nat = rg_capout RG /\ VAL 256%nat = rg_out RG /\
  VAL 297%nat + 92 = rg_client_broken RG)
  by (repeat split; first [exact HV11 | exact HH19 | exact HV13 | exact HV14 | exact HV15 | exact HH17]).
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
assert (N14 : VAL 255%nat = rg_capout RG) by exact HV14.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
assert (N17 : VAL 297%nat + 92 = rg_client_broken RG) by exact HH17.
assert (N19 : VAL 299%nat + 248 = rg_send_eintr RG) by exact HH19.
assert (N22 : VAL 302%nat + 260 = rg_nout RG) by exact HH22.
assert (N23 : VAL 303%nat + 864 = rg_capout RG) by exact HH23.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WL) memL)) by constructor.
(* the dead path writes only g_client_broken (and errno after the call): drop the other write windows *)
apply (st_ok_pi_submem _ _ _ [r_frame; r_client;
  YP09.mkRegion (Some (A_OBJ 11)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]; r_dead; r_broken]) in HS;
  [| apply YN2j.submemb_sound; vm_compute; reflexivity | vm_compute; reflexivity].
lrun RUN HS HJ SHOK LBspan.
{ cbn [ss_mem ss_L]; unfold r_frame, r_client, r_dead, r_broken.
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_HI 17) HH17|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUN BR HS SHOK LBspan.
2: exfalso; rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc by (clear - Heir; lia);
   apply Z.eqb_neq in Hc; lia.

(* g_send_eintr = 0: the load of g_send_dead and the bnez *)
apply (st_ok_pi_submem _ _ _ [r_frame; r_dead; r_broken]) in HS;
  [| apply YN2j.submemb_sound; vm_compute; reflexivity | vm_compute; reflexivity].
lrun RUN HS HJ SHOK LBspan.
{ cbn [ss_mem]; unfold r_frame, r_dead, r_broken.
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_HI 17) HH17|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUN BR HS SHOK LBspan.
2: exfalso; rewrite branch_ne_U, (U_atom E 33 (ct_dd c) E33), (U_lit E 0) in Hc0 by (clear - Hddr; lia);
   rewrite Hdd in Hc0; vm_compute in Hc0; discriminate Hc0.
(* g_send_dead <> 0: the call of __errno_location at 0x828d0 *)
apply (st_ok_pi_submem _ _ _ [r_frame; r_broken]) in HS;
  [| apply YN2j.submemb_sound; vm_compute; reflexivity | vm_compute; reflexivity].
lrun RUN HS HJ SHOK LBspan.
{ cbn [ss_mem]; unfold r_frame, r_broken.
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_HI 17) HH17|].
  apply awr_ok_x_nil. }

pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_SL B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
    WL (ms_regs ms1) (ms_mem ms1) SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out))
    ly S W mem md ([] : list (Z * Z)) lyL SL _ kL (- SL_FRAME) (Z_to_bv 64 (BASE + 1512)) HG eq_refl HJ).
  - unfold spZ at 1. rewrite Q2, Usp. clear. unfold SL_FRAME. lia.
  - unfold SL_FRAME. reflexivity.
  - unfold SL_FRAME. clear. lia.
  - clear. lia.
  - clear. vm_compute. intros Hx. discriminate Hx.
  - rewrite Q3, E3, H3. exact Hgp.
  - rewrite Q4, E4, H4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros _. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE _. exact (AERRNO lyL SL WL (ms_regs ms1) (ms_mem ms1) _ HPRE). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
assert (WRc : forall a, writable_at SEGS (arm WL memL) a -> writable_at SEGS (mrestrict (w_H WL) mem2) a).
{ intros a Ha. apply (writable_kept (w_H WL) (ms_mem ms1) mem2 a (fun Hp => Hpres2 _ Hp)).
  eapply writable_at_grows; [exact HG2|]. eapply writable_at_grows; [exact HG1|].
  eapply writable_at_grows; [exact HG0|]. exact Ha. }
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H WL) mem2) HP2 [0;1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (RKM : forall lo hi, 0x10000 - 1000 <= lo -> hi <= 0x5fb000 + 1000 ->
    forall a, lo <= a < hi -> mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem ms1)) a).
  { intros lo hi Hl Hh a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    [ clear - Ha Hl Hh; lia | intros [] | clear - Ha Hl Hh QSP C1 HSF HES; lia ]. }
  assert (RKS : forall a, spZ regsE - SL_FRAME <= a < spZ regsE ->
    mbyte SEGS (mrestrict (w_H WL) mem2) a = mbyte SEGS (mrestrict (w_H WL) (ms_mem ms1)) a).
  { intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    [ clear - Ha QSP C1 HSF; lia | intros [] | clear - Ha HSF HES; lia ]. }
  repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  rewrite ?(HEI 297%nat ltac:(cbv; lia)), ?Usp;
  try change (VAL 297%nat) with (VAL (A_HI 17));
  first
  [ intros a Ha; exfalso; clear - Ha; lia
  | intros a Ha; apply RKS; clear - Ha HSF; lia
  | apply RKM; clear - HH17 Q10 HV10; lia
  | intros a Ha _; apply WRc;
    (replace a with (rg_client_broken RG + (a - rg_client_broken RG)) by (clear - Ha; lia);
     apply Wbr; clear - Ha HH17; lia) ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.

remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 38)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10.
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. assert (Hin : inG (G_SL B RG) (as_errno B + i)) by (clear - Hi; ing_tac).
    exact (proj1 (HG _ Hin)). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0.
  pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. clear - P0 P3. lia. }
assert (WRerr : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H WL) mem2) (as_errno B + o))
  by (intros o Ho; apply WRc; exact (Wev o Ho)).
assert (F42 : ew Ea 42 = Z_to_bv 64 (as_errno B))
  by (rewrite <- R10, Herr, <- HERRNO; reflexivity).
assert (BVEa : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ea (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEIa m Hm)).
assert (Uspa : base_val Ea (Some 2%nat) = spZ regsE - SL_FRAME)
  by (cbn [base_val]; rewrite (OLDa 2%nat ltac:(clear; lia)); exact Usp).
assert (BA42 : base_val Ea (Some 42%nat) = as_errno B)
  by (cbn [base_val]; rewrite F42; apply unsigned_lit_small; clear - HERRI; lia).
apply (st_ok_pi_add_fact _ _ _ 42%nat OBJF) in HS;
  [|unfold afact_ok, OBJF; cbn [af_lo af_hi af_al2]; rewrite F42,
    (unsigned_lit_small (as_errno B)) by (clear - HERRI; lia);
    rewrite Z.pow_0_r, Z.mod_1_r; clear - HERRI; repeat split; lia].
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 42%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      rewrite BA42; split; [clear - HERRI; lia|]; split; [clear - HERRI; lia|];
      split; [|apply Forall_nil]; intros o Ho; cbn [ms_mem restrict]; exact (WRerr o Ho)
    | cbn [ss_mem add_atom]; apply all_disjoint_of_extents; unfold extent_of_region;
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
      rewrite BA42, ?(BVEa 297%nat ltac:(cbv; lia)), ?Uspa;
      change (VAL 297%nat) with (VAL (A_HI 17));
      cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
      pose proof (sl_rgd 10 3 ltac:(lia) ltac:(lia) ltac:(lia)) as D3;
      cbn [nth] in D3; unfold zdisj in D3; cbn [fst snd] in D3;
      repeat split;
      first [ solve [ clear - HERRI QSP C1 HSF; lia ]
            | solve [ clear - D3 HH17; lia ] ] ].
assert (UB : U Ea BxL = SHADOW_OFF).
{ unfold BxL. rewrite (U_atom Ea 23%nat SB); [reflexivity | | clear; unfold SB; lia].
  rewrite (OLDa 23%nat ltac:(clear; lia)), E23, R23. reflexivity. }
assert (UE42 : U Ea (SOff 42%nat 0) = as_errno B)
  by (apply (U_atom Ea 42%nat); [exact F42 | clear - HERRI; lia]).
assert (SHOKa : sh_ok SEGS BxL [mkSHE 42%nat 0 4] Ea (mrestrict (w_H WL) mem2)).
{ constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H WL) mem2 Ea BxL 42%nat (as_errno B) 4 (as_errno B) 0 4).
  - eapply errno_ra. eapply ajournal_gx_AR. exact HJ2.
  - exact UB.
  - exact UE42.
  - clear; lia.
  - clear; lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. clear - Hx HERRI UB.
    rewrite <- SB_SHADOW_OFF. unfold SB. lia. }

(* the shadow check of errno, errno := EPIPE, g_client_broken := 1, to the epilogue *)
lrun_to RUNTO HS HJ2 SHOKa LBspan A_sl_epi.
{ apply awr_ok_x_cons_g;
    [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BA42;
      intros a Ha; clear - Ha; ing_tac |].
  apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_gb BVEa 297%nat N17|].
  apply awr_ok_x_nil. }

(* the epilogue at 0x828f8: g_client_broken = 1, errno = EPIPE; nothing else of aout_at changed *)
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.

assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_client_broken RG <= a < rg_client_broken RG + 1) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (spZ regsE - SL_FRAME - ESTACK <= a < spZ regsE - SL_FRAME) ->
  aview SEGS (w_H WL) (ms_mem ms2) a = aview SEGS (w_H WL) memL a).
{ intros a Ha Hb He Hsc.
  assert (K1 : aview SEGS (w_H WL) (ms_mem ms2) a = aview SEGS (w_H WL) mem2 a).
  { apply (aview_kept_out _ _ (w_H WL) mem2 (ms_mem ms2) HFr2 a Ha). nowr_dl BVEa BA42 N17 Hb He. }
  assert (K2 : aview SEGS (w_H WL) mem2 a = aview SEGS (w_H WL) (ms_mem ms1) a).
  { apply Hfr2; [exact Ha | intros HFx; destruct HFx | clear - Hsc HSF HES; lia]. }
  assert (K3 : aview SEGS (w_H WL) (ms_mem ms1) a = aview SEGS (w_H WL) (ms_mem ms0) a).
  { apply (aview_kept_out _ _ (w_H WL) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha). nowr_dl BVE BA42 N17 Hb He. }
  assert (K4 : aview SEGS (w_H WL) (ms_mem ms0) a = aview SEGS (w_H WL) (ms_mem ms) a).
  { apply (aview_kept_out _ _ (w_H WL) (ms_mem ms) (ms_mem ms0) HFr0 a Ha). nowr_dl BVE BA42 N17 Hb He. }
  assert (K5 : aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H WL) memL a).
  { apply (aview_kept_out _ _ (w_H WL) memL (ms_mem ms) HFr a Ha). nowr_dl BVE BA42 N17 Hb He. }
  rewrite K1, K2, K3, K4, K5. reflexivity. }
clear HF HF0 HF1 HF2 HFr HFr0 HFr1 HFr2.

lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssF ?msF =>
  assert (BVEb : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ev (Some m) = VAL m)
    by (intros m Hm; cbn [base_val]; rewrite !ew_ewset_other by (clear - Hm; unfold A_LIM in Hm; lia);
        exact (HEIa m Hm));
  assert (BA42b : base_val Ev (Some 42%nat) = as_errno B)
    by (cbn [base_val]; rewrite !ew_ewset_other by clia; cbn [base_val] in BA42; exact BA42);
  pose proof (st_ok_pi_region_nth Ev ssF msF 0 _ HS eq_refl) as RG0;
  pose proof (st_ok_pi_region_nth Ev ssF msF 2 _ HS eq_refl) as RG2
end.
cbn [ms_mem restrict] in RG0, RG2.
assert (PRall : forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem ms2) a).
{ intros a Hp. apply (apresent_grows _ _ _ _ HG3). apply Hpres2. apply (apresent_grows _ _ _ _ HG2).
  apply (apresent_grows _ _ _ _ HG1). apply (apresent_grows _ _ _ _ HG0). exact Hp. }
assert (WRall : forall a, writable_at SEGS (arm WL memL) a ->
  writable_at SEGS (mrestrict (w_H WL) (ms_mem ms2)) a).
{ intros a Hw. eapply writable_at_grows; [exact HG3|]. apply WRc. exact Hw. }
assert (Hs0 : sent = 0) by exact (Hdd1 Hdd).
destruct (Hdd2 Hdd) as [HcapL HoutL].
change (BASE + 1548) with (BASE + A_sl_epi).
apply (sl_exit regsE ly S W mem md c O mx no cap out Bl lyL SL WL (ms_regs ms2) (ms_mem ms2) _ kL out rest HJ2).
- unfold spZ at 1. rewrite P2, (OLDa 2%nat ltac:(clia)), E2. exact Hsp.
- rewrite P3, (OLDa 3%nat ltac:(clia)), E3. exact H3.
- rewrite P4, (OLDa 4%nat ltac:(clia)), E4. exact H4.
- exact HraE.
- intros i Hi. apply (vm_keep WL memL (ms_mem ms2)); [|exact (HSV i Hi)].
  intros x Hx. apply KEEP; clear - Hx Hi QSP C1 HSF HES HERRI Q10 HV10; lia.
- intros a Ha1 Ha2 Ha3 Hp. apply PRall. exact (HAPK a Ha1 Ha2 Ha3 Hp).
- unfold sl_cost. rewrite (sl_live_false_dead c _ Hdd). rewrite <- (Hspent0 Hdd). exact HMLE.
- exact HPerm0.
- rewrite (sl_cap_dead c mx no cap _ Hdd). rewrite <- HcapL, <- HoutL. exact HPerm1.
- clear HS.
  rewrite (sl_ctl_on c (Z.of_nat (length Bl)) Hcl Hbr ltac:(change (0 < len); lia)), Hdd, Z.eqb_refl.
  rewrite (sl_O_dead c O Bl Hdd), (sl_no_dead c no _ Hdd), (sl_cap_dead c mx no cap _ Hdd).
  rewrite Hs0, Hei0, HcapL, HoutL, Hdd in HOUT.
  change (Z.to_nat 0) with 0%nat in HOUT. rewrite firstn_O, app_nil_r, Z.add_0_r in HOUT.
  rewrite HcapL, HoutL in Hblk.
  refine (aout_at_broken_lo lyL SL WL WL memL (ms_mem ms2) (CTL 3 0 1 0 evL) O mx no cap out
    send_line_c.EPIPE_V HOUT _ _ _ _ _ _ _).
  + intros a Ha Hb He. split.
    * apply KEEP; [clear - Ha C1; lia | exact Hb | exact He | clear - Ha Hceil Hslo WS HSF HES; lia].
    * exact (WRall a).
  + intros a Ha.
    destruct Hblk as [(Hcz & Hoz & Hnz) | (Hc1 & Hn1 & Hin1 & _)]; [exfalso; clear - Ha Hcz; lia|].
    pose proof (blk_off_imgP B lyL SL WL memL mdL out cap HARL Hin1) as OFF.
    destruct (al_blocks _ _ LAWS lyL SL WL memL mdL out cap HARL Hin1) as (_ & Hp4 & Hpc & _).
    assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
    unfold off_img in OFF. rewrite Hrq in OFF, Hpc.
    split; [clear - Ha Hp4 Hpc; lia|].
    split; [clear - Ha OFF Q10 HV10; lia | clear - Ha OFF HERRI; lia].
  + lazymatch type of RG2 with region_ok _ ?Ev _ _ =>
      pose proof (field_of_region Ev _ 297%nat (VAL 297%nat) _ _ _ _ _ 92 1%N (SLit 1) 1 RG2
        ltac:(rewrite <- (BVEb 297%nat ltac:(cbv; lia)); reflexivity) ltac:(left; reflexivity) eq_refl
        ltac:(cbn; lia) ltac:(cbn; lia)) as VB
    end.
    rewrite N17 in VB. exact VB.
  + intros i Hi. apply WRall. apply Wbr. exact Hi.
  + lazymatch type of RG0 with region_ok _ ?Ev _ _ =>
      pose proof (field_of_region Ev _ 42%nat (as_errno B) _ _ _ _ _ 0 4%N (SLit 32) 32 RG0
        ltac:(rewrite <- BA42b; reflexivity) ltac:(left; reflexivity) eq_refl
        ltac:(cbn; lia) ltac:(cbn; lia)) as VE
    end.
    rewrite Z.add_0_r in VE. exact VE.
  + change send_line_c.EPIPE_V with 32. lia.
  + intros i Hi. apply WRall. apply Wev. exact Hi.
- intros _. reflexivity.
Qed.

(* a data round: g_send_dead = 0: n bytes, the growth of g_out when it is short, the copy, g_nout += n *)
Lemma sl_arm_data : sl_copy_stmt B MT MMAX RG -> sl_grow_stmt B MT MMAX RG -> forall n, sl_loop_at B MT MMAX RG n -> forall regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL -> eiL = 0 -> ct_dd c = 0 ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat (Datatypes.S n) ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros COPY GROW n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hdd Hb. sl_intro HI. 
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & _).
pose proof HJi as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & HstkL & _).
pose proof HstkL as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
rewrite !Z.add_0_r in Hal16, Hstk0, Hslo, Hshi, Hbot, Htop2, HpresL.
assert (WS : SL_STK = 16512) by reflexivity.
pose proof HOUT as (Vmx & Wmx & Vno & Wno & Vcap & Wcap & Vout & Wout & Vcl & Wcl & Vbr & Wbr &
  Vdd & Wdd & Vei & Wei & Vev & Wev & Rev & Hclr & Hbrr & Hddr & Heir & Hmxr & HlenO & Hblk).
cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in Vmx, Vno, Vcap, Vout, Vcl, Vbr, Vdd, Vei, Vev, Rev,
  Hclr, Hbrr, Hddr, Heir.
(* numeric ranges of the cells *)
assert (Rcapout : 0 <= capL /\ 0 <= outL /\ no + sent <= 2 ^ 47 /\ capL <= 2 ^ 47 /\ outL <= 2 ^ 47).
{ destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hc1 & Hn1 & Hin1 & _)].
  - repeat split; lia.
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL outL capL HARL Hin1) as (_ & Hp4 & Hpc & _).
    assert (Hrq : req_size capL = capL) by (unfold req_size; destruct (Z.eqb_spec capL 0); lia).
    rewrite Hrq in Hpc. repeat split; lia. }
destruct Rcapout as (Rc0 & Ro0 & Rn47 & Rc47 & Ro47).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlen1 : 1 <= len <= 2 ^ 63 - 1) by lia.
pose proof (sl_loop_entry lyL SL WL regsL memL (spZ regsE) len line sent eiL (ct_dd c)
  (no + sent) capL outL mx evL (O ++ firstn (Z.to_nat sent) Bl)
  Hsp ltac:(unfold SL_FRAME, SL_STK in *; lia) ltac:(lia) Hal16 HR Hlen1 ltac:(lia) ltac:(lia)
  M8 M16 HOUT ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof (pa_obj_img 9 ltac:(lia)) as Q9. pose proof (pa_obj_img 10 ltac:(lia)) as Q10.
pose proof (pa_obj_img 11 ltac:(lia)) as Q11. pose proof (pa_obj_img 12 ltac:(lia)) as Q12.
pose proof (pa_obj_img 13 ltac:(lia)) as Q13. pose proof (pa_obj_img 14 ltac:(lia)) as Q14.
pose proof (pa_obj_img 15 ltac:(lia)) as Q15.
assert (HSF : SL_FRAME = 128) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (QSP : alloc_ceiling <= spZ regsE /\ spZ regsE <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
pose proof HR as HRc.
destruct HRc as (R8 & R9 & R19 & R22 & R23 & R20 & R21 & R24 & R25 & R26 & R27).
remember (Eimg (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsL (l_extra eiL (ct_dd c) (no + sent) capL outL mx)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (BVE : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val E (Some m) = VAL m)
  by (intros m Hm; cbn [base_val]; exact (HEI m Hm)).
assert (E1 : ew E 1 = getr regsL 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsL 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = w64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 8 8%bv eq_refl); exact (proj1 HR)).
assert (E9 : ew E 9 = w64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl); exact (proj1 (proj2 HR))).
assert (E22 : ew E 22 = w64 sent) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsL _ 22 22%bv eq_refl); exact (proj1 (proj2 (proj2 (proj2 HR))))).
assert (E23 : ew E 23 = getr regsL 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = w64 eiL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = w64 (ct_dd c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (E34 : ew E 34 = w64 (no + sent)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
assert (E35 : ew E 35 = w64 capL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
assert (E36 : ew E 36 = w64 outL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
assert (E37 : ew E 37 = w64 mx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsE - SL_FRAME) by (rewrite E2; exact Hsp).
clear HE.
assert (N11 : VAL 252%nat = rg_send_eintr RG) by exact HV11.
assert (NALL : VAL 252%nat = rg_send_eintr RG /\ VAL 299%nat + 248 = rg_send_eintr RG /\
  VAL 254%nat = rg_nout RG /\ VAL 255%nat = rg_capout RG /\ VAL 256%nat = rg_out RG /\
  VAL 297%nat + 92 = rg_client_broken RG)
  by (repeat split; first [exact HV11 | exact HH19 | exact HV13 | exact HV14 | exact HV15 | exact HH17]).
assert (N13 : VAL 254%nat = rg_nout RG) by exact HV13.
assert (N14 : VAL 255%nat = rg_capout RG) by exact HV14.
assert (N15 : VAL 256%nat = rg_out RG) by exact HV15.
assert (N17 : VAL 297%nat + 92 = rg_client_broken RG) by exact HH17.
assert (N19 : VAL 299%nat + 248 = rg_send_eintr RG) by exact HH19.
assert (N22 : VAL 302%nat + 260 = rg_nout RG) by exact HH22.
assert (N23 : VAL 303%nat + 864 = rg_capout RG) by exact HH23.
assert (N24 : VAL 304%nat + 892 = rg_out RG) by exact HH24.
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H WL) memL)) by constructor.
lrun RUN HS HJ SHOK LBspan.
{ unfold ss_L; cbn [ss_mem];
  unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken.
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 11) HV11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 13) HV13|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 14) HV14|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 15) HV15|].
  apply awr_ok_x_cons_g; [awr_g (A_HI 17) HH17|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUN BR HS SHOK LBspan.
2: exfalso; rewrite branch_eq_U, (U_atom E 32 eiL E32), (U_lit E 0) in Hc by (clear - Heir; lia);
   apply Z.eqb_neq in Hc; lia.
assert (Hlen32 : len < 2 ^ 32).
{ destruct HLOK as [H0 | [(q & m & Hin & _ & Hq & Hqm) | (Himg & _ & _)]].
  - clear - H0 Hlen1; lia.
  - destruct (al_blocks _ _ LAWS lyL SL WL memL mdL q m HARL Hin) as (_ & _ & _ & _ & _ & _ & Hm).
    unfold req_size in Hqm. unfold MALLOC_MAX in Hm. destruct (Z.eqb_spec m 0); clear - Hq Hqm Hm Hlen1 Hline0; lia.
  - pose proof (pa_img_range _ (Himg line ltac:(clear - Hlen1; lia))) as P1.
    pose proof (pa_img_range _ (Himg (line + len - 1) ltac:(clear - Hlen1; lia))) as P2. clear - P1 P2 Hlen1; lia. }
set (rem := len - sent) in *.
set (nn := sl_n mx rem) in *.
assert (Hnn : 0 < nn <= rem) by (apply sl_n_range; clear - Hmxr Hsent; lia).
pose (NF := mkAF 1 4294967295 0).
pose (ssN := add_atom (mkSS 1336 (sr_set (sr_set (sr_set sr_L 10%bv (SOff 37 0)) 18%bv (SOff 38 0)) 11%bv (SOff 39 0))
  l_regions None (mkFacts (f_atoms l_facts) [] [])) 38 NF).
assert (DATA : forall (ms0 : machine_state) (md0 : Model) (Ex : env),
  img_env VAL A_LIM Ex -> (forall m, (m < 38)%nat -> ew Ex m = ew E m) -> ew Ex 38 = w64 nn ->
  st_ok_pi SEGS VAL Ex ssN (restrict (w_H WL) ms0) ->
  ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK (spZ regsE) (ablocks_fp (aout_blks cap out)) ly S W mem md [] lyL SL WL (ms_mem ms0) md0 kL ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E l_regions a -> aview SEGS (w_H WL) (ms_mem ms0) a = aview SEGS (w_H WL) memL a) ->
  (forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem ms0) a) ->
  SRr SEGS WL (mkCfg ms0 md0) (sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl)).
{ intros ms0 md0 Ex HEIx OLDx X38 HSx HJx KEEP0 PR0.
  assert (BVEx : forall m, (A_TEXT <= m < A_LIM)%nat -> base_val Ex (Some m) = VAL m)
    by (intros m Hm; cbn [base_val]; exact (HEIx m Hm)).
  assert (SHOKx : sh_ok SEGS BxL [] Ex (mrestrict (w_H WL) (ms_mem ms0))) by constructor.

  assert (F32 : ew Ex 32 = w64 0) by (rewrite OLDx by lia; rewrite E32, Hei0; reflexivity).
  assert (F34 : ew Ex 34 = w64 (no + sent)) by (rewrite OLDx by lia; exact E34).
  assert (F35 : ew Ex 35 = w64 capL) by (rewrite OLDx by lia; exact E35).
  assert (F36 : ew Ex 36 = w64 outL) by (rewrite OLDx by lia; exact E36).
  rewrite Hdd, Hei0 in HOUT.
  assert (Hev0 : evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c))
    by (rewrite Hev, Hei0; destruct (ct_ei c =? 1); reflexivity).
  pose proof (sl_n_range mx rem ltac:(clear - Hmxr; lia) ltac:(clear - Hsent; lia)) as Hnr.
  assert (UADD : U Ex (SAlu ALU_ADD (SOff 34 0) (SOff 38 0)) = no + sent + nn).
  { rewrite U_SAlu, (U_atom Ex 34 (no + sent) F34), (U_atom Ex 38 nn X38) by (clear - Rn47 HlenO Hnn Hlen32 Hsent; lia).
    cbn [zalu_raw]. apply zcanon_id. unfold M64. clear - Rn47 HlenO Hnn Hlen32 Hsent; lia. }
  destruct (Z.lt_ge_cases capL (no + sent + nn)) as [HGW | HNG].
  { (* g_out is short: the growth half (W_send_line_grow_cx.v sl_grow_stmt) *)
    pose proof (l_vals Ex _ _ 0 (no + sent) capL outL HSx ltac:(vm_compute; reflexivity) HEIx F32 F34 F35 F36
      ltac:(lia) ltac:(clear - Rn47 HlenO; lia) ltac:(clear - Rc0 Rc47; lia) ltac:(clear - Ro0 Ro47; lia))
      as (NV1 & NV2 & NV3 & NV4 & NV5).
    cbn [ms_mem restrict] in NV1, NV2, NV3, NV4, NV5.
    assert (VIEW0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H WL) (ms_mem ms0) a = aview SEGS (w_H WL) memL a).
    { intros a Ha. destruct (l_cells_dec a) as [Hcl' | Hcl'].
      - rewrite Hei0 in Vei.
        destruct Hcl' as [Hx | [Hx | [Hx | [Hx | Hx]]]].
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 1 0 Vei NV1 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 8 _ Vno NV2 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 8 _ Vcap NV3 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 8 _ Vout NV4 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem ms0) _ 1 0 Vbr NV5 a ltac:(cbn; lia)).
      - apply KEEP0; [exact Ha|]. intros Hw. exact (Hcl' (l_wrange_cells E a HEI Hw)). }
    destruct (sl_moved WL memL (ms_mem ms0) (aview_all_of_bounded _ _ _ VIEW0) PR0) as (MvO & MvG & MvR & MvV).
    prreg HSx (2%bv : bv 5) K2. prreg HSx (3%bv : bv 5) K3. prreg HSx (4%bv : bv 5) K4.
    prreg HSx (8%bv : bv 5) K8. prreg HSx (9%bv : bv 5) K9. prreg HSx (18%bv : bv 5) K18. prreg HSx (22%bv : bv 5) K22.
    prreg HSx (23%bv : bv 5) K23. prreg HSx (20%bv : bv 5) K20. prreg HSx (21%bv : bv 5) K21. prreg HSx (24%bv : bv 5) K24.
    prreg HSx (25%bv : bv 5) K25. prreg HSx (26%bv : bv 5) K26. prreg HSx (27%bv : bv 5) K27.
    pmkst HSx.
    apply (GROW regsE ly S W mem md c O mx no cap out line Bl WL (ms_regs ms0) (ms_mem ms0) md0 sent nn).
    2: { intros WM regsM memM mdM HM.
         apply (COPY n regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent nn IH HM).
         change (Z.of_nat (length Bl)) with len; clear - Hb Hei0; lia. }
    unfold SLN. cbv zeta. change (Z.of_nat (length Bl)) with len.
    exists lyL, SL, kL, evL, capL, outL, spent, rest.
    split; [exact HJx|].
    split; [unfold spZ at 1; rewrite K2, (OLDx 2%nat ltac:(lia)), E2; exact Hsp|].
    split; [rewrite K3, (OLDx 3%nat ltac:(lia)), E3; exact H3|].
    split; [rewrite K4, (OLDx 4%nat ltac:(lia)), E4; exact H4|].
    split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|].
    split.
    { unfold sl_regsM.
      rewrite K8, K9, K18, K22, K23, K20, K21, K24, K25, K26, K27.
      rewrite (OLDx 8%nat ltac:(lia)), (OLDx 9%nat ltac:(lia)), (OLDx 22%nat ltac:(lia)), (OLDx 23%nat ltac:(lia)), X38.
      rewrite E8, E9, E22, E23, R23.
      rewrite !(ew_img _ _ HEIx) by (cbv; lia).
      repeat split; reflexivity. }
    split; [exact (MvV _ _ _ M8)|]. split; [exact (MvV _ _ _ M16)|].
    split; [intros i Hi; exact (MvV _ _ _ (HSV i Hi))|].
    split; [exact Hcl|]. split; [exact Hbr|]. split; [exact Hdd|]. split; [exact Hsent|].
    split; [reflexivity|]. split; [exact Hev0|].
    split; [exact (MvO _ _ _ _ _ _ _ _ HOUT)|].
    split; [exact HGW|].
    split; [exact (MvG _ _ HGL)|]. split; [exact Hline0|]. split; [exact Hline1|].
    split; [exact (MvR HROM)|]. split; [exact HLOK|]. split; [exact HLG|].
    split; [exact (Hcapq Hdd)|]. split; [exact (HMM Hdd)|]. split; [exact (HLM Hdd)|].
    split; [intros a Ha1 Ha2 Ha3 Hp; exact (PR0 a (HAPK a Ha1 Ha2 Ha3 Hp))|].
    split; [exact HMOK|]. split; [exact HMLE|].
    split; [exact (HCOST Hdd)|].
    split; [exact HPerm0|]. split; [exact HPerm1|]. exact HFR. }

  lrun RUN HSx HJx SHOKx LBspan.
{ unfold ssN; cbn [ss_mem add_atom]; unfold l_regions, r_frame, r_client, r_eintr, r_dead, r_max, r_nout, r_capout, r_out, r_broken.
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 11) HV11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 13) HV13|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 14) HV14|].
  apply awr_ok_x_cons_g; [awr_g (A_OBJ 15) HV15|].
  apply awr_ok_x_cons_g; [awr_g (A_HI 17) HH17|].
  apply awr_ok_x_nil. }
  psrr_branch_tok RUN BR HSx SHOKx LBspan.

  - (* g_capout >= g_nout + n: no growth, straight to the join *)
    lrun_to RUNTO HSx HJx SHOKx LBspan 1380%Z.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
    lazymatch type of HSx with st_ok_pi _ _ _ _ (restrict _ ?mk) => rename mk into msJ end.
    pmkst HSx.
    apply (COPY n regsE ly S W mem md c O mx no cap out line Bl WL (ms_regs msJ) (ms_mem msJ) _ sent nn IH).
    2: (change (Z.of_nat (length Bl)) with len; clear - Hb Hei0; lia).

    (* the registers at the join *)
    prreg HSx (2%bv : bv 5) J2. prreg HSx (3%bv : bv 5) J3. prreg HSx (4%bv : bv 5) J4.
    prreg HSx (8%bv : bv 5) J8. prreg HSx (9%bv : bv 5) J9. prreg HSx (18%bv : bv 5) J18. prreg HSx (22%bv : bv 5) J22.
    prreg HSx (23%bv : bv 5) J23. prreg HSx (20%bv : bv 5) J20. prreg HSx (21%bv : bv 5) J21. prreg HSx (24%bv : bv 5) J24.
    prreg HSx (25%bv : bv 5) J25. prreg HSx (26%bv : bv 5) J26. prreg HSx (27%bv : bv 5) J27.
    pose proof (l_vals Ex _ _ 0 (no + sent) capL outL HSx ltac:(vm_compute; reflexivity) HEIx F32 F34 F35 F36
      ltac:(lia) ltac:(clear - Rn47 HlenO; lia) ltac:(clear - Rc0 Rc47; lia) ltac:(clear - Ro0 Ro47; lia))
      as (JV1 & JV2 & JV3 & JV4 & JV5).
    cbn [ms_mem restrict] in JV1, JV2, JV3, JV4, JV5.
    assert (VIEW : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H WL) (ms_mem msJ) a = aview SEGS (w_H WL) memL a).
    { intros a Ha. destruct (l_cells_dec a) as [Hcl' | Hcl'].
      - rewrite Hei0 in Vei.
        destruct Hcl' as [Hx | [Hx | [Hx | [Hx | Hx]]]].
        + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 1 0 Vei JV1 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 8 _ Vno JV2 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 8 _ Vcap JV3 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 8 _ Vout JV4 a ltac:(cbn; lia)).
        + exact (aview_of_vm2 WL memL (ms_mem msJ) _ 1 0 Vbr JV5 a ltac:(cbn; lia)).
      - assert (HnW : ~ in_wrange E l_regions a) by (intros Hw; exact (Hcl' (l_wrange_cells E a HEI Hw))).
        assert (HnWx : ~ in_wrange Ex l_regions a) by (intros Hw; exact (Hcl' (l_wrange_cells Ex a HEIx Hw))).
        rewrite <- (KEEP0 a Ha HnW).
        repeat match goal with
        | |- aview _ _ ?m a = aview _ _ ?m a => reflexivity
        | HF : frame_of Ex _ (mrestrict (w_H WL) ?m1) (mrestrict (w_H WL) ?m2) |- aview _ (w_H WL) ?m2 a = _ =>
            rewrite (aview_kept_out _ _ (w_H WL) m1 m2 HF a Ha HnWx)
        end. }

    assert (PRJ : forall a, apresent (w_H WL) memL a -> apresent (w_H WL) (ms_mem msJ) a)
      by (intros a Hp; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact (PR0 a Hp)).
    destruct (sl_moved WL memL (ms_mem msJ) (aview_all_of_bounded _ _ _ VIEW) PRJ) as (MvO & MvG & MvR & MvV).
    rewrite branch_geu_U, (U_atom Ex 35 capL F35) in Hc0 by (clear - Rc0 Rc47; lia).
    rewrite UADD in Hc0. apply negb_true_iff, Z.ltb_ge in Hc0.
    assert (NOG : (capL <? no + sent + nn) = false) by (apply Z.ltb_ge; exact Hc0).

    unfold SLM. cbv zeta. change (Z.of_nat (length Bl)) with len.
    exists lyL, SL, kL, evL, capL, outL, spent, rest.
    split; [exact HJx|].
    split; [unfold spZ at 1; rewrite J2, (OLDx 2%nat ltac:(lia)), E2; exact Hsp|].
    split; [rewrite J3, (OLDx 3%nat ltac:(lia)), E3; exact H3|].
    split; [rewrite J4, (OLDx 4%nat ltac:(lia)), E4; exact H4|].
    split; [exact Hgp|]. split; [exact Htp|]. split; [exact HraE|].
    split.
    { unfold sl_regsM.
      rewrite J8, J9, J18, J22, J23, J20, J21, J24, J25, J26, J27.
      rewrite (OLDx 8%nat ltac:(lia)), (OLDx 9%nat ltac:(lia)), (OLDx 22%nat ltac:(lia)), (OLDx 23%nat ltac:(lia)), X38.
      rewrite E8, E9, E22, E23, R23.
      rewrite !(ew_img _ _ HEIx) by (cbv; lia).
      repeat split; reflexivity. }
    split; [exact (MvV _ _ _ M8)|]. split; [exact (MvV _ _ _ M16)|].
    split; [intros i Hi; exact (MvV _ _ _ (HSV i Hi))|].
    split; [exact Hcl|]. split; [exact Hbr|]. split; [exact Hdd|]. split; [exact Hsent|].
    split; [reflexivity|]. split; [exact Hev0|].
    split; [exact (MvO _ _ _ _ _ _ _ _ HOUT)|].
    split; [exact Hc0|].
    split; [exact (MvG _ _ HGL)|]. split; [exact Hline0|]. split; [exact Hline1|].
    split; [exact (MvR HROM)|]. split; [exact HLOK|]. split; [exact HLG|].
    split.
    { rewrite (Hcapq Hdd), send_line_cap_step by (clear - Hmxr Hsent; lia). fold rem nn.
      unfold sl_capn. rewrite NOG. reflexivity. }
    split.
    { pose proof (HMM Hdd) as HM. rewrite sl_max_run_step in HM by (clear - Hmxr Hsent; lia). fold rem nn in HM.
      rewrite NOG in HM. exact HM. }
    split.
    { pose proof (HLM Hdd) as HM.
      rewrite (sl_tr_peak_keep mx (no + sent) capL rem ltac:(clear - Hmxr; lia) ltac:(clear - Hsent; lia) Hc0) in HM.
      exact HM. }
    split; [intros a Ha1 Ha2 Ha3 Hp; exact (PRJ a (HAPK a Ha1 Ha2 Ha3 Hp))|].
    split; [exact HMOK|]. split; [exact HMLE|].
    split.
    { pose proof (HCOST Hdd) as HM. rewrite sl_cost_run_step in HM by (clear - Hmxr Hsent; lia). fold rem nn in HM.
      unfold sl_capn in HM. rewrite NOG in HM. cbv beta iota in HM. fold rem nn. clear - HM. lia. }
    split; [exact HPerm0|]. split; [exact HPerm1|]. exact HFR.

  - exfalso. rewrite branch_geu_U, (U_atom Ex 35 capL F35), UADD in Hc0 by (clear - Rc0 Rc47; lia).
    apply negb_false_iff, Z.ltb_lt in Hc0. clear - Hc0 HNG. lia.
}
lrun RUN HS HJ SHOK LBspan.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUN BR HS SHOK LBspan.
{ exfalso. rewrite branch_ne_U, (U_atom E 33 (ct_dd c) E33), (U_lit E 0) in Hc0 by (clear - Hddr; lia).
  rewrite Hdd in Hc0. vm_compute in Hc0. discriminate Hc0. }
lrun RUN HS HJ SHOK LBspan.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
psrr_branch_tok RUN BR HS SHOK LBspan.
- assert (Urem1 : U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 22 0) (SLit (-1)))) = rem)
    by (apply U_rem; first [exact E8 | exact E22 | clear - Hsent Hlen1; lia | reflexivity]).
  rewrite branch_ltu_U, Urem1, (U_atom E 37 mx E37) in Hc1 by (clear - Hmxr; lia).
  lrun RUN HS HJ SHOK LBspan.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
  psrr_branch_tok RUN BR HS SHOK LBspan.
  + exfalso. rewrite branch_eq_U, (U_atom E 37 mx E37), (U_lit E 0) in Hc2 by (clear - Hmxr; lia).
    apply Z.eqb_eq in Hc2. apply Z.ltb_lt in Hc1. clear - Hc1 Hc2 Hnn. lia.
  + lrun_to RUNTO HS HJ SHOK LBspan 1336%Z.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mk) => rename mk into msK end.
    assert (V18 : getr (ms_regs msK) 18%bv = w64 nn).
    { rewrite (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS).
      lazymatch goal with |- sv_denot E ?e = _ => let e' := eval vm_compute in e in change e with e' end.
      rewrite denot_lit_U, (U_rem E len sent _ E8 E22) by (first [clear - Hsent Hlen1; lia | reflexivity]).
      unfold nn, sl_n. apply Z.ltb_lt in Hc1. rewrite (proj2 (Z.eqb_neq mx 0)) by (clear - Hc1 Hnn; lia).
      rewrite (proj2 (Z.ltb_ge mx rem)) by (clear - Hc1; lia). reflexivity. }
    assert (X38 : ew (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 = w64 nn) by (unfold havoc; cbn [ew]; reflexivity).
    assert (NFok : afact_ok (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 NF).
    { unfold afact_ok, NF. cbn [af_lo af_hi af_al2]. rewrite X38. unfold w64.
      rewrite unsigned_lit_small by (clear - Hnn Hlen32 Hsent; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hnn Hlen32 Hsent; lia. }
    pose proof (sl_canon E _ _ (w64 nn) (getr (ms_regs msK) 11%bv) NF HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs restrict]; exact V18) ltac:(cbn [ms_regs restrict]; reflexivity) NFok) as HSn.
    lazymatch type of HSn with st_ok_pi ?a ?b ?c _ ?d => change (st_ok_pi a b c ssN d) in HSn end.
    eapply (DATA msK _ (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]));
      [ apply img_env_havoc; [exact HEI | cbv; lia]
      | intros m Hm; apply YN3v.ew_havoc_old; exact Hm
      | exact X38 | exact HSn | exact HJ | keep_chainW | pres_chain ].
- assert (Urem1 : U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 22 0) (SLit (-1)))) = rem)
    by (apply U_rem; first [exact E8 | exact E22 | clear - Hsent Hlen1; lia | reflexivity]).
  rewrite branch_ltu_U, Urem1, (U_atom E 37 mx E37) in Hc1 by (clear - Hmxr; lia).
  apply Z.ltb_ge in Hc1.
  lrun RUN HS HJ SHOK LBspan.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
  psrr_branch_tok RUN BR HS SHOK LBspan.
  + rewrite branch_eq_U, (U_atom E 37 mx E37), (U_lit E 0) in Hc2 by (clear - Hmxr; lia).
    apply Z.eqb_eq in Hc2. assert (Hmx0 : (mx =? 0) = true) by (apply Z.eqb_eq; exact Hc2).
    lrun_to RUNTO HS HJ SHOK LBspan 1336%Z.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mk) => rename mk into msK end.
    assert (V18 : getr (ms_regs msK) 18%bv = w64 nn).
    { rewrite (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS).
      lazymatch goal with |- sv_denot E ?e = _ => let e' := eval vm_compute in e in change e with e' end.
      rewrite denot_lit_U, (U_rem E len sent _ E8 E22) by (first [clear - Hsent Hlen1; lia | reflexivity]).
      unfold nn, sl_n. rewrite Hmx0. reflexivity. }
    assert (X38 : ew (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 = w64 nn) by (unfold havoc; cbn [ew]; reflexivity).
    assert (NFok : afact_ok (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 NF).
    { unfold afact_ok, NF. cbn [af_lo af_hi af_al2]. rewrite X38. unfold w64.
      rewrite unsigned_lit_small by (clear - Hnn Hlen32 Hsent; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hnn Hlen32 Hsent; lia. }
    pose proof (sl_canon E _ _ (w64 nn) (getr (ms_regs msK) 11%bv) NF HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs restrict]; exact V18) ltac:(cbn [ms_regs restrict]; reflexivity) NFok) as HSn.
    lazymatch type of HSn with st_ok_pi ?a ?b ?c _ ?d => change (st_ok_pi a b c ssN d) in HSn end.
    eapply (DATA msK _ (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]));
      [ apply img_env_havoc; [exact HEI | cbv; lia]
      | intros m Hm; apply YN3v.ew_havoc_old; exact Hm
      | exact X38 | exact HSn | exact HJ | keep_chainW | pres_chain ].

  + rewrite branch_eq_U, (U_atom E 37 mx E37), (U_lit E 0) in Hc2 by (clear - Hmxr; lia).
    apply Z.eqb_neq in Hc2. assert (Hmx0 : mx <> 0) by exact Hc2.
    lrun_to RUNTO HS HJ SHOK LBspan 1336%Z.
{ apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 252%nat N11|].
  apply awr_ok_x_cons; [awr_empty|]. apply awr_ok_x_cons; [awr_empty|].
  apply awr_ok_x_cons_g; [awr_g 254%nat N13|].
  apply awr_ok_x_cons_g; [awr_g 255%nat N14|].
  apply awr_ok_x_cons_g; [awr_g 256%nat N15|].
  apply awr_ok_x_cons_g; [awr_g 297%nat N17|].
  apply awr_ok_x_nil. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mk) => rename mk into msK end.
    assert (V18 : getr (ms_regs msK) 18%bv = w64 nn).
    { rewrite (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS).
      lazymatch goal with |- sv_denot E ?e = _ => let e' := eval vm_compute in e in change e with e' end.
      rewrite denot_lit_U, (U_atom E 37 mx E37) by (clear - Hmxr; lia).
      unfold nn, sl_n. rewrite (proj2 (Z.eqb_neq mx 0)) by exact Hmx0.
      destruct (Z.ltb_spec mx rem) as [Hlt|Hge]; cbn [negb andb]; [reflexivity | f_equal; clear - Hc1 Hge; lia]. }
    assert (X38 : ew (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 = w64 nn) by (unfold havoc; cbn [ew]; reflexivity).
    assert (NFok : afact_ok (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]) 38 NF).
    { unfold afact_ok, NF. cbn [af_lo af_hi af_al2]. rewrite X38. unfold w64.
      rewrite unsigned_lit_small by (clear - Hnn Hlen32 Hsent; lia). rewrite Z.pow_0_r, Z.mod_1_r. clear - Hnn Hlen32 Hsent; lia. }
    pose proof (sl_canon E _ _ (w64 nn) (getr (ms_regs msK) 11%bv) NF HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs restrict]; exact V18) ltac:(cbn [ms_regs restrict]; reflexivity) NFok) as HSn.
    lazymatch type of HSn with st_ok_pi ?a ?b ?c _ ?d => change (st_ok_pi a b c ssN d) in HSn end.
    eapply (DATA msK _ (havoc E 38 [w64 nn; getr (ms_regs msK) 11%bv]));
      [ apply img_env_havoc; [exact HEI | cbv; lia]
      | intros m Hm; apply YN3v.ew_havoc_old; exact Hm
      | exact X38 | exact HSn | exact HJ | keep_chainW | pres_chain ].
Qed.

(* The loop segment, given the copy half (W_send_line_datab_cx.v sl_copy_stmt) and the growth half
   (W_send_line_grow_cx.v sl_grow_stmt) of a data round. *)
Theorem pb_sl_loop_cut : sl_copy_stmt B MT MMAX RG -> sl_grow_stmt B MT MMAX RG -> sl_loop_stmt B MT MMAX RG.
Proof.
intros COPY GROW. unfold sl_loop_stmt. intros n. induction n as [|n IH];
intros regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hb;
pose proof HI as HI'; sl_intro HI';
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hddr & Heir & _);
cbn [ct_dd ct_ei] in Hddr, Heir.
- exfalso. lia.
- destruct (Z.eq_dec eiL 0) as [Hei0 | Hei0].
  + destruct Hddr as [Hd | Hd].
    * exact (sl_arm_data COPY GROW n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hd Hb).
    * exact (sl_arm_dead regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hd).
  + exact (sl_arm_eintr n IH regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hei0 Hb).
Qed.


End c.
End b.
End a.
