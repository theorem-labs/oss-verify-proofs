(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: memory helpers of the ASan walk of fuzz_reply's send_line loop
   (lib/A/W_send_line_loop.v), in the form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* send_line's two rounds that send nothing change two cells each: the EINTR round clears g_send_eintr and sets
   errno, the dead round sets g_client_broken and errno.  aout_at_eintr / aout_at_broken rebuild aout_at
   (lib/A/W_rep.v) after such a round: every other cell of aout_at is outside the two changed ranges (HRGD), and
   so is the g_out block (the premise on out and cap, which the walk discharges). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

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
Section c.
Variable B : asyms.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].

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

End c.
End b.
End a.
