(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma busy_of_Some_In : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b H. unfold busy_of, busy_slots in *.
  apply find_some in H. destruct H as [HIn HP]. apply andb_true_iff in HP. destruct HP as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  apply in_map_iff. exists b. split; [reflexivity|]. apply filter_In. split; [exact HIn| apply Z.eqb_refl].
Qed.

#[using="Type"] Lemma NoDup_app_disjoint : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [exact H1|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct H1 as [<-|H1].
  - apply NI. apply in_app_iff. right. exact H2.
  - exact (IH l2 x ND' H1 H2).
Qed.

#[using="Type"] Lemma nth_error_map_inv : forall {A B} (f : A -> B) l i y,
  nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ y = f x.
Proof.
  intros A B f l. induction l as [|a l IH]; intros [|i] y H; cbn in H; try discriminate.
  - injection H as <-. exists a. split; reflexivity.
  - apply IH. exact H.
Qed.

Section Kit.
Variable H : aholes.

#[using="Type"] Theorem kit_cache_pop : kit_cache_pop_stmt H.
Proof.
  unfold kit_cache_pop_stmt. intros L st X m c cnt AR HC CNT POS.
  (nd_pre AR 6%nat; intros WF RT INST THR CLS HOLES; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS ASTATS UNW; nd_post).
  destruct (CACHES c HC) as [tail (CR & CH & LEN)].
  (nd_pre (CLS c HC) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
  (nd_pre WF 11%nat; intros SB PA AL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (* [comment removed for export] *)
  assert (CI : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite <- CNT in POS. lia. }
  (* [comment removed for export] *)
  assert (LT : (Z.to_nat (cnt - 1) < length (xc_cache (x_cls X c)))%nat) by lia.
  destruct (nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1))) as [k|] eqn:NK.
  2: { exfalso. apply nth_error_None in NK. lia. }
  assert (INK : In k (xc_cache (x_cls X c))) by (eapply nth_error_In; exact NK).
  assert (KR : 0 <= k < ndist st c) by (apply RANGE; apply in_app_iff; right; apply in_app_iff; left; exact INK).
  assert (NB : busy_of X c k = None).
  { destruct (busy_of X c k) as [b|] eqn:E; [|reflexivity]. exfalso.
    apply busy_of_Some_In in E. rewrite app_assoc in ND.
    eapply (NoDup_app_disjoint (xc_free (x_cls X c) ++ xc_cache (x_cls X c)) (busy_slots X c) k ND); [| exact E].
    apply in_app_iff. right. exact INK. }
  exists k, (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail).
  split; [first [exact NK | reflexivity]|]. split; [exact NB|]. split; [exact KR|].
  split. { rewrite <- CNT. rewrite CI in CR. unfold max_count in CR |- *. rewrite CI in CR |- *. exact CR. }
  split; [exact CH|]. split; [rewrite length_app, length_map; lia|].
  split. { rewrite nth_error_app1 by (rewrite length_map; lia). rewrite nth_error_map, ?NK. reflexivity. }
  split.
  - destruct SLOTS as [SL _]. specialize (SL k KR). rewrite NB in SL. exact SL.
  - destruct SHADOW as [SH _]. specialize (SH k KR). rewrite NB in SH. unfold fill_at. cbn [slot_shadow_bytes] in SH. exact SH.
Qed.
End Kit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
#[using="Type"] Lemma skipn_repeat' : forall {A} (x : A) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

#[using="Type"] Lemma junk_split : forall m A a b, junk_at m A (a + b) -> 0 <= a -> 0 <= b ->
  junk_at m A a /\ junk_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

#[using="Type"] Lemma junk_merge : forall m A a b, junk_at m A a -> junk_at m (A + a) b -> 0 <= a -> 0 <= b -> junk_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  pose proof H1 as W1. destruct W1 as [[[L1 _] _] _]. cbn in L1.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exists (bs1 ++ bs2). rewrite Z2Nat.inj_add by lia. exact M.
Qed.

#[using="Type"] Lemma fill_split : forall m A a b v, fill_at m A (a + b) v -> 0 <= a -> 0 <= b ->
  fill_at m A a v /\ fill_at m (A + a) b v.
Proof.
  intros m A a b v H Ha Hb. unfold fill_at in *.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) (repeat (Z_to_bv 8 v) (Z.to_nat (a + b))) [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  rewrite firstn_repeat' in H1 by lia. rewrite skipn_repeat', firstn_repeat' in H2 by lia.
  split; assumption.
Qed.

#[using="Type"] Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v H1 H2 Ha Hb. unfold fill_at in *.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) (repeat (Z_to_bv 8 v) (Z.to_nat a))] ++ [CB (Z.to_nat b) (repeat (Z_to_bv 8 v) (Z.to_nat b))])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) (repeat (Z_to_bv 8 v) (Z.to_nat a))] ++ [CB (Z.to_nat b) (repeat (Z_to_bv 8 v) (Z.to_nat b))]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r, <- repeat_app in M. rewrite Z2Nat.inj_add by lia. exact M.
Qed.

#[using="Type"] Lemma fill_is_junk : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v H. eexists. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c8_of_junk : forall m A, junk_at m A 8 -> exists w : word, rw_cells asegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
#[using="Type"] Lemma c8c8_of_junk : forall m A, junk_at m A 16 -> exists w1 w2 : word, rw_cells asegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
#[using="Type"] Lemma hdr_of_junk : forall m A, junk_at m A 16 ->
  exists b0 b1 szh szl ctxj : Z,
    rw_cells asegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b0 < 256 /\ 0 <= b1 < 256.
Proof. intros m A [bs H]. exact (hdr_of_CB m A bs H). Qed.
#[using="Type"] Lemma c1_of_fill : forall m A v, 0 <= v < 256 -> fill_at m A 1 v -> rw_cells asegs m A [C1 (Z_to_bv 8 v)].
Proof.
  intros m A v Hv H. unfold fill_at in H. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op] in H.
  eapply InitMem.rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
#[using="Type"] Lemma junk_of_cells : forall m A cs, rw_cells asegs m A cs -> junk_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. destruct (rw_cells_forget asegs m A cs H) as [junk H']. exists junk. rewrite Nat2Z.id. exact H'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_carve : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ rz = 32 \/ rz = 64) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m AB HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. replace (S - 16 - n) with (S - 16 - n) by lia. exact TL.
  - assert (RZ2 : rz = 32 \/ rz = 64) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m _ HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    (nd_pre (c8c8_of_junk m AB LHJ) 3%nat; intros j1 j2 LH; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_carve : forall m SA gS grz g (room : Z),
  fill_at m SA gS 0xfa -> 2 <= grz -> 0 <= g -> grz + g + room <= gS -> 0 <= room <= 1 ->
     rw_cells asegs m SA [C1 (Z_to_bv 8 0xfa)]
  /\ fill_at m (SA + 1) (grz - 1) 0xfa
  /\ (exists sj, rw_cells asegs m (SA + grz) [CB (Z.to_nat g) sj])
  /\ (room = 1 -> rw_cells asegs m (SA + grz + g) [C1 (Z_to_bv 8 0xfa)])
  /\ fill_at m (SA + grz + g + room) (gS - grz - g - room) 0xfa.
Proof.
  intros m SA gS grz g room F GRZ G FIT ROOM.
  destruct (fill_split m SA 1 (gS - 1) 0xfa ltac:(replace (1 + (gS - 1)) with gS by lia; exact F) ltac:(lia) ltac:(lia)) as [F0 R1].
  destruct (fill_split m (SA + 1) (grz - 1) (gS - grz) 0xfa ltac:(replace (grz - 1 + (gS - grz)) with (gS - 1) by lia; exact R1) ltac:(lia) ltac:(lia)) as [F1 R2].
  replace (SA + 1 + (grz - 1)) with (SA + grz) in R2 by lia.
  destruct (fill_split m (SA + grz) g (gS - grz - g) 0xfa ltac:(replace (g + (gS - grz - g)) with (gS - grz) by lia; exact R2) ltac:(lia) ltac:(lia)) as [F2 R3].
  destruct (fill_split m (SA + grz + g) room (gS - grz - g - room) 0xfa ltac:(replace (room + (gS - grz - g - room)) with (gS - grz - g) by lia; exact R3) ltac:(lia) ltac:(lia)) as [F3 R4].
  split; [apply c1_of_fill; [lia| exact F0]|]. split; [exact F1|]. split; [eexists; exact F2|].
  split; [| exact R4]. intros ->. apply c1_of_fill; [lia| exact F3].
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma busy_of_Some_In : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b H. unfold busy_of, busy_slots in *.
  apply find_some in H. destruct H as [HIn HP]. apply andb_true_iff in HP. destruct HP as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  apply in_map_iff. exists b. split; [reflexivity|]. apply filter_In. split; [exact HIn| apply Z.eqb_refl].
Qed.

#[using="Type"] Lemma NoDup_app_disjoint : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [exact H1|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct H1 as [<-|H1].
  - apply NI. apply in_app_iff. right. exact H2.
  - exact (IH l2 x ND' H1 H2).
Qed.

#[using="Type"] Lemma nth_error_map_inv : forall {A B} (f : A -> B) l i y,
  nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ y = f x.
Proof.
  intros A B f l. induction l as [|a l IH]; intros [|i] y H; cbn in H; try discriminate.
  - injection H as <-. exists a. split; reflexivity.
  - apply IH. exact H.
Qed.

Section Kit.
Variable H : aholes.

#[using="Type"] Theorem kit_cache_pop : kit_cache_pop_stmt H.
Proof.
  unfold kit_cache_pop_stmt. intros L st X m c cnt AR HC CNT POS.
  (nd_pre AR 6%nat; intros WF RT INST THR CLS HOLES; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS ASTATS UNW; nd_post).
  destruct (CACHES c HC) as [tail (CR & CH & LEN)].
  (nd_pre (CLS c HC) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
  (nd_pre WF 11%nat; intros SB PA AL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (* [comment removed for export] *)
  assert (CI : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite <- CNT in POS. lia. }
  (* [comment removed for export] *)
  assert (LT : (Z.to_nat (cnt - 1) < length (xc_cache (x_cls X c)))%nat) by lia.
  destruct (nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1))) as [k|] eqn:NK.
  2: { exfalso. apply nth_error_None in NK. lia. }
  assert (INK : In k (xc_cache (x_cls X c))) by (eapply nth_error_In; exact NK).
  assert (KR : 0 <= k < ndist st c) by (apply RANGE; apply in_app_iff; right; apply in_app_iff; left; exact INK).
  assert (NB : busy_of X c k = None).
  { destruct (busy_of X c k) as [b|] eqn:E; [|reflexivity]. exfalso.
    apply busy_of_Some_In in E. rewrite app_assoc in ND.
    eapply (NoDup_app_disjoint (xc_free (x_cls X c) ++ xc_cache (x_cls X c)) (busy_slots X c) k ND); [| exact E].
    apply in_app_iff. right. exact INK. }
  exists k, (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail).
  split; [first [exact NK | reflexivity]|]. split; [exact NB|]. split; [exact KR|].
  split. { rewrite <- CNT. rewrite CI in CR. unfold max_count in CR |- *. rewrite CI in CR |- *. exact CR. }
  split; [exact CH|]. split; [rewrite length_app, length_map; lia|].
  split. { rewrite nth_error_app1 by (rewrite length_map; lia). rewrite nth_error_map, ?NK. reflexivity. }
  split.
  - destruct SLOTS as [SL _]. specialize (SL k KR). rewrite NB in SL. exact SL.
  - destruct SHADOW as [SH _]. specialize (SH k KR). rewrite NB in SH. unfold fill_at. cbn [slot_shadow_bytes] in SH. exact SH.
Qed.
End Kit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
#[using="Type"] Lemma skipn_repeat' : forall {A} (x : A) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

#[using="Type"] Lemma junk_split : forall m A a b, junk_at m A (a + b) -> 0 <= a -> 0 <= b ->
  junk_at m A a /\ junk_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

#[using="Type"] Lemma junk_merge : forall m A a b, junk_at m A a -> junk_at m (A + a) b -> 0 <= a -> 0 <= b -> junk_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  pose proof H1 as W1. destruct W1 as [[[L1 _] _] _]. cbn in L1.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exists (bs1 ++ bs2). rewrite Z2Nat.inj_add by lia. exact M.
Qed.

#[using="Type"] Lemma fill_split : forall m A a b v, fill_at m A (a + b) v -> 0 <= a -> 0 <= b ->
  fill_at m A a v /\ fill_at m (A + a) b v.
Proof.
  intros m A a b v H Ha Hb. unfold fill_at in *.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) (repeat (Z_to_bv 8 v) (Z.to_nat (a + b))) [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  rewrite firstn_repeat' in H1 by lia. rewrite skipn_repeat', firstn_repeat' in H2 by lia.
  split; assumption.
Qed.

#[using="Type"] Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v H1 H2 Ha Hb. unfold fill_at in *.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) (repeat (Z_to_bv 8 v) (Z.to_nat a))] ++ [CB (Z.to_nat b) (repeat (Z_to_bv 8 v) (Z.to_nat b))])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) (repeat (Z_to_bv 8 v) (Z.to_nat a))] ++ [CB (Z.to_nat b) (repeat (Z_to_bv 8 v) (Z.to_nat b))]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r, <- repeat_app in M. rewrite Z2Nat.inj_add by lia. exact M.
Qed.

#[using="Type"] Lemma fill_is_junk : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v H. eexists. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c8_of_junk : forall m A, junk_at m A 8 -> exists w : word, rw_cells asegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
#[using="Type"] Lemma c8c8_of_junk : forall m A, junk_at m A 16 -> exists w1 w2 : word, rw_cells asegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
#[using="Type"] Lemma hdr_of_junk : forall m A, junk_at m A 16 ->
  exists b0 b1 szh szl ctxj : Z,
    rw_cells asegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b0 < 256 /\ 0 <= b1 < 256.
Proof. intros m A [bs H]. exact (hdr_of_CB m A bs H). Qed.
#[using="Type"] Lemma c1_of_fill : forall m A v, 0 <= v < 256 -> fill_at m A 1 v -> rw_cells asegs m A [C1 (Z_to_bv 8 v)].
Proof.
  intros m A v Hv H. unfold fill_at in H. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op] in H.
  eapply InitMem.rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
#[using="Type"] Lemma junk_of_cells : forall m A cs, rw_cells asegs m A cs -> junk_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. destruct (rw_cells_forget asegs m A cs H) as [junk H']. exists junk. rewrite Nat2Z.id. exact H'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_carve : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ rz = 32 \/ rz = 64) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m AB HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. replace (S - 16 - n) with (S - 16 - n) by lia. exact TL.
  - assert (RZ2 : rz = 32 \/ rz = 64) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m _ HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    (nd_pre (c8c8_of_junk m AB LHJ) 3%nat; intros j1 j2 LH; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_carve : forall m SA gS grz g (room : Z),
  fill_at m SA gS 0xfa -> 2 <= grz -> 0 <= g -> grz + g + room <= gS -> 0 <= room <= 1 ->
     rw_cells asegs m SA [C1 (Z_to_bv 8 0xfa)]
  /\ fill_at m (SA + 1) (grz - 1) 0xfa
  /\ (exists sj, rw_cells asegs m (SA + grz) [CB (Z.to_nat g) sj])
  /\ (room = 1 -> rw_cells asegs m (SA + grz + g) [C1 (Z_to_bv 8 0xfa)])
  /\ fill_at m (SA + grz + g + room) (gS - grz - g - room) 0xfa.
Proof.
  intros m SA gS grz g room F GRZ G FIT ROOM.
  destruct (fill_split m SA 1 (gS - 1) 0xfa ltac:(replace (1 + (gS - 1)) with gS by lia; exact F) ltac:(lia) ltac:(lia)) as [F0 R1].
  destruct (fill_split m (SA + 1) (grz - 1) (gS - grz) 0xfa ltac:(replace (grz - 1 + (gS - grz)) with (gS - 1) by lia; exact R1) ltac:(lia) ltac:(lia)) as [F1 R2].
  replace (SA + 1 + (grz - 1)) with (SA + grz) in R2 by lia.
  destruct (fill_split m (SA + grz) g (gS - grz - g) 0xfa ltac:(replace (g + (gS - grz - g)) with (gS - grz) by lia; exact R2) ltac:(lia) ltac:(lia)) as [F2 R3].
  destruct (fill_split m (SA + grz + g) room (gS - grz - g - room) 0xfa ltac:(replace (room + (gS - grz - g - room)) with (gS - grz - g) by lia; exact R3) ltac:(lia) ltac:(lia)) as [F3 R4].
  split; [apply c1_of_fill; [lia| exact F0]|]. split; [exact F1|]. split; [eexists; exact F2|].
  split; [| exact R4]. intros ->. apply c1_of_fill; [lia| exact F3].
Qed.
End CANSEC2.
End TwB.
