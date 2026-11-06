(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From stdpp Require gmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Exec ITree Nodes Decode Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AKitR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Fixpoint words4_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => le_bytes_to_word [b0;b1;b2;b3] :: words4_of_bytes rest
  | _ => []
  end.

#[using="Type"] Lemma words4_of_bytes_ok : forall k bs, length bs = (4 * k)%nat ->
  u32s (words4_of_bytes bs) = bs /\ length (words4_of_bytes bs) = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn in L; try lia.
    destruct (IH rest ltac:(lia)) as [U Lk].
    cbn [words4_of_bytes u32s length]. rewrite le4_of_bytes by reflexivity. cbn. rewrite U, Lk. split; reflexivity.
Qed.

#[using="Type"] Lemma u32arr_of_CB : forall m A k bs,
  rw_cells asegs m A [CB (4 * k) bs] -> u32arr asegs m A (words4_of_bytes bs) /\ length (words4_of_bytes bs) = k.
Proof.
  intros m A k bs [[WF BA] WR]. cbn in WF. destruct WF as [L _].
  destruct (words4_of_bytes_ok k bs ltac:(lia)) as [U Lk].
  split; [|exact Lk]. split.
  - rewrite U. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
  - rewrite Lk. cbn [cells_size csize Nat.add] in WR. replace (4 * Z.of_nat k) with (Z.of_nat (4 * k + 0)) by lia. exact WR.
Qed.

#[using="Type"] Lemma u32arr_of_junk : forall m A n, junk_at m A (4 * n) -> 0 <= n ->
  exists ws, u32arr asegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (4 * n)) with (4 * Z.to_nat n)%nat in H by lia.
  destruct (u32arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words4_of_bytes bs). split; assumption.
Qed.

#[using="Type"] Lemma rw_cells_of_u32arr : forall m A ws,
  u32arr asegs m A ws -> rw_cells asegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u32s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (4 * length ws + 0)) with (4 * Z.of_nat (length ws)) by lia. exact W.
Qed.

#[using="Type"] Lemma junk_of_u32arr : forall m A ws, u32arr asegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws U. exists (u32s ws). replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia.
  apply rw_cells_of_u32arr. exact U.
Qed.

#[using="Type"] Lemma u32arr_firstn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
  u32arr asegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    specialize (B i ltac:(rewrite u32s_length; lia)). rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app1 by (rewrite u32s_length, length_firstn; lia). reflexivity.
  - split; [lia|]. split; [rewrite length_firstn; lia|].
    intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

#[using="Type"] Lemma u32arr_skipn' : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
  u32arr asegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed.

#[using="Type"] Lemma u32arr_app_inv : forall m A ws1 ws2, u32arr asegs m A (ws1 ++ ws2) ->
  u32arr asegs m A ws1 /\ u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 U. split.
  - replace ws1 with (firstn (length ws1) (ws1 ++ ws2)) by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    apply u32arr_firstn; [exact U| rewrite length_app; lia].
  - pose proof (u32arr_skipn' m A (ws1 ++ ws2) (length ws1) U ltac:(rewrite length_app; lia)) as V.
    rewrite skipn_app, skipn_all, Nat.sub_diag in V. exact V.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_of_cb : forall m A k bs, rw_cells asegs m A [CB (Z.to_nat k) bs] -> junk_at m A k.
Proof. intros m A k bs H. exists bs. exact H. Qed.

#[using="Type"] Lemma junk_at_eq : forall m A A' n n', junk_at m A n -> A = A' -> n = n' -> junk_at m A' n'.
Proof. intros m A A' n n' H <- <-. exact H. Qed.

#[using="Type"] Lemma Forall_firstn_skipn : forall {A} (P : A -> Prop) (l : list A) n k h,
  Forall P (firstn n l) -> (k + h <= n)%nat -> Forall P (firstn h (skipn k l)).
Proof.
  intros A P l n k h HF LE. rewrite firstn_skipn_comm.
  apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF x).
  assert (IN : In x (firstn (k + h) l)).
  { rewrite <- (firstn_skipn k (firstn (k + h) l)). apply in_or_app. right. exact Hx. }
  rewrite <- (firstn_skipn (k + h) (firstn n l)) . apply in_or_app. left.
  rewrite firstn_firstn. replace (Nat.min (k + h) n) with (k + h)%nat by lia. exact IN.
Qed.

#[using="Type"] Lemma u32arr_addr_eq : forall m A A' ws, u32arr asegs m A ws -> A = A' -> u32arr asegs m A' ws.
Proof. intros m A A' ws H <-. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_In' : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
#[using="Type"] Lemma sub_fp_by_incl' : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. (nd_pre HE 4%nat; intros jv Hin H1 H2; nd_post). cbn in H1, H2.
  pose proof (outside_In' W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
Ltac find_ivw tac :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [tac]
        | apply Exists_cons_tl; find_ivw tac ].
Ltac solve_sub_fpw tac :=
  apply sub_fp_by_incl'; repeat (apply Forall_cons; [find_ivw tac|]); apply Forall_nil.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma munch_trans_w : forall W W1 W2 m m1 m', munch W1 m m1 -> munch W2 m1 m' -> sub_fp W1 W -> sub_fp W2 W -> munch W m m'.
Proof. intros W W1 W2 m m1 m' A B S1 S2. eapply munch_trans; [eapply munch_weaken; [exact S1| exact A] | eapply munch_weaken; [exact S2| exact B]]. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Fixpoint words4_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => le_bytes_to_word [b0;b1;b2;b3] :: words4_of_bytes rest
  | _ => []
  end.

#[using="Type"] Lemma words4_of_bytes_ok : forall k bs, length bs = (4 * k)%nat ->
  u32s (words4_of_bytes bs) = bs /\ length (words4_of_bytes bs) = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn in L; try lia.
    destruct (IH rest ltac:(lia)) as [U Lk].
    cbn [words4_of_bytes u32s length]. rewrite le4_of_bytes by reflexivity. cbn. rewrite U, Lk. split; reflexivity.
Qed.

#[using="Type"] Lemma u32arr_of_CB : forall m A k bs,
  rw_cells asegs m A [CB (4 * k) bs] -> u32arr asegs m A (words4_of_bytes bs) /\ length (words4_of_bytes bs) = k.
Proof.
  intros m A k bs [[WF BA] WR]. cbn in WF. destruct WF as [L _].
  destruct (words4_of_bytes_ok k bs ltac:(lia)) as [U Lk].
  split; [|exact Lk]. split.
  - rewrite U. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
  - rewrite Lk. cbn [cells_size csize Nat.add] in WR. replace (4 * Z.of_nat k) with (Z.of_nat (4 * k + 0)) by lia. exact WR.
Qed.

#[using="Type"] Lemma u32arr_of_junk : forall m A n, junk_at m A (4 * n) -> 0 <= n ->
  exists ws, u32arr asegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (4 * n)) with (4 * Z.to_nat n)%nat in H by lia.
  destruct (u32arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words4_of_bytes bs). split; assumption.
Qed.

#[using="Type"] Lemma rw_cells_of_u32arr : forall m A ws,
  u32arr asegs m A ws -> rw_cells asegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u32s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (4 * length ws + 0)) with (4 * Z.of_nat (length ws)) by lia. exact W.
Qed.

#[using="Type"] Lemma junk_of_u32arr : forall m A ws, u32arr asegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws U. exists (u32s ws). replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia.
  apply rw_cells_of_u32arr. exact U.
Qed.

#[using="Type"] Lemma u32arr_firstn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
  u32arr asegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    specialize (B i ltac:(rewrite u32s_length; lia)). rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app1 by (rewrite u32s_length, length_firstn; lia). reflexivity.
  - split; [lia|]. split; [rewrite length_firstn; lia|].
    intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

#[using="Type"] Lemma u32arr_skipn' : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
  u32arr asegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed.

#[using="Type"] Lemma u32arr_app_inv : forall m A ws1 ws2, u32arr asegs m A (ws1 ++ ws2) ->
  u32arr asegs m A ws1 /\ u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 U. split.
  - replace ws1 with (firstn (length ws1) (ws1 ++ ws2)) by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    apply u32arr_firstn; [exact U| rewrite length_app; lia].
  - pose proof (u32arr_skipn' m A (ws1 ++ ws2) (length ws1) U ltac:(rewrite length_app; lia)) as V.
    rewrite skipn_app, skipn_all, Nat.sub_diag in V. exact V.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_of_cb : forall m A k bs, rw_cells asegs m A [CB (Z.to_nat k) bs] -> junk_at m A k.
Proof. intros m A k bs H. exists bs. exact H. Qed.

#[using="Type"] Lemma junk_at_eq : forall m A A' n n', junk_at m A n -> A = A' -> n = n' -> junk_at m A' n'.
Proof. intros m A A' n n' H <- <-. exact H. Qed.

#[using="Type"] Lemma Forall_firstn_skipn : forall {A} (P : A -> Prop) (l : list A) n k h,
  Forall P (firstn n l) -> (k + h <= n)%nat -> Forall P (firstn h (skipn k l)).
Proof.
  intros A P l n k h HF LE. rewrite firstn_skipn_comm.
  apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF x).
  assert (IN : In x (firstn (k + h) l)).
  { rewrite <- (firstn_skipn k (firstn (k + h) l)). apply in_or_app. right. exact Hx. }
  rewrite <- (firstn_skipn (k + h) (firstn n l)) . apply in_or_app. left.
  rewrite firstn_firstn. replace (Nat.min (k + h) n) with (k + h)%nat by lia. exact IN.
Qed.

#[using="Type"] Lemma u32arr_addr_eq : forall m A A' ws, u32arr asegs m A ws -> A = A' -> u32arr asegs m A' ws.
Proof. intros m A A' ws H <-. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_In' : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
#[using="Type"] Lemma sub_fp_by_incl' : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. (nd_pre HE 4%nat; intros jv Hin H1 H2; nd_post). cbn in H1, H2.
  pose proof (outside_In' W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
Ltac find_ivw tac :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [tac]
        | apply Exists_cons_tl; find_ivw tac ].
Ltac solve_sub_fpw tac :=
  apply sub_fp_by_incl'; repeat (apply Forall_cons; [find_ivw tac|]); apply Forall_nil.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma munch_trans_w : forall W W1 W2 m m1 m', munch W1 m m1 -> munch W2 m1 m' -> sub_fp W1 W -> sub_fp W2 W -> munch W m m'.
Proof. intros W W1 W2 m m1 m' A B S1 S2. eapply munch_trans; [eapply munch_weaken; [exact S1| exact A] | eapply munch_weaken; [exact S2| exact B]]. Qed.
End CANSEC2.
End TwB.
End AKitR.

(* [comment removed for export] *)
Module ARepFrame.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma get_cls_put_cls_eq : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_cls_put_cls_ne : forall c c' r st, c' <> c -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_next : forall v st c, get_cls (set_next v st) c = get_cls st c. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_live : forall v st c, get_cls (set_live v st) c = get_cls st c. Proof. reflexivity. Qed.
#[using="Type"] Lemma max_count_eq : forall st st' c, a_cinit st' = a_cinit st -> max_count st' c = max_count st c.
Proof. intros st st' c E. unfold max_count. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Definition st_fast (st : astate) (c n cnt : Z) : astate :=
  set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
    (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)).

#[using="Type"] Lemma st_fast_fields : forall st c n cnt,
     a_space_beg (st_fast st c n cnt) = a_space_beg st /\ a_ptr_array (st_fast st c n cnt) = a_ptr_array st
  /\ a_nres (st_fast st c n cnt) = a_nres st /\ a_nsec (st_fast st c n cnt) = a_nsec st
  /\ a_cinit (st_fast st c n cnt) = a_cinit st
  /\ a_live (st_fast st c n cnt) = <[ a_next st := CPrim c n ]> (a_live st)
  /\ a_next (st_fast st c n cnt) = N.succ (a_next st)
  /\ a_qloc (st_fast st c n cnt) = a_qloc st /\ a_qloc_bytes (st_fast st c n cnt) = a_qloc_bytes st
  /\ a_qglob (st_fast st c n cnt) = a_qglob st /\ a_qglob_bytes (st_fast st c n cnt) = a_qglob_bytes st.
Proof. intros. repeat split; reflexivity. Qed.

#[using="Type"] Lemma st_fast_cls : forall st c n cnt c',
  get_cls (st_fast st c n cnt) c' = if c' =? c then cls_set_count (cnt - 1) (get_cls st c) else get_cls st c'.
Proof.
  intros. unfold st_fast. rewrite get_cls_set_next, get_cls_set_live.
  destruct (Z.eqb_spec c' c) as [->|NE]; [apply get_cls_put_cls_eq | apply get_cls_put_cls_ne; exact NE].
Qed.

#[using="Type"] Lemma st_fast_counters : forall st c n cnt c',
     c_mapped_user (get_cls (st_fast st c n cnt) c') = c_mapped_user (get_cls st c')
  /\ c_allocated_user (get_cls (st_fast st c n cnt) c') = c_allocated_user (get_cls st c')
  /\ c_num_freed (get_cls (st_fast st c n cnt) c') = c_num_freed (get_cls st c')
  /\ c_mapped_free_array (get_cls (st_fast st c n cnt) c') = c_mapped_free_array (get_cls st c')
  /\ c_count (get_cls (st_fast st c n cnt) c') = (if c' =? c then cnt - 1 else c_count (get_cls st c')).
Proof. intros. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; repeat split; reflexivity. Qed.

#[using="Type"] Lemma st_fast_max_count : forall st c n cnt c', max_count (st_fast st c n cnt) c' = max_count st c'.
Proof. intros. apply max_count_eq. reflexivity. Qed.
#[using="Type"] Lemma st_fast_ndist : forall st c n cnt c', ndist (st_fast st c n cnt) c' = ndist st c'.
Proof. intros. unfold ndist. rewrite (proj1 (proj2 (st_fast_counters st c n cnt c'))). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma size_of_class_facts : forall c, 1 <= c < K_NUM_CLASSES ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  enough (B : (16 <=? size_of_class c) && (size_of_class c <=? 65536) && (size_of_class c mod 16 =? 0) = true).
  { apply andb_prop in B. destruct B as [B B3]. apply andb_prop in B. destruct B as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.eqb_eq in B3. lia. }
  assert (E : exists i, (0 <= i < 31)%nat /\ c = Z.of_nat i + 1).
  { exists (Z.to_nat (c - 1)). split; lia. }
  (nd_pre E 3%nat; intros i Hi ndR1__; nd_post; revert ndR1__; intros ->).
  do 31 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

#[using="Type"] Lemma shlen_div : forall d, shlen d = d / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
#[using="Type"] Lemma shad_div : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
#[using="Type"] Lemma shad_add : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + d / 8.
Proof. intros a d H. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shad_add_shlen : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + shlen d.
Proof. intros. rewrite shlen_div. apply shad_add. assumption. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma shad_sep : forall a1 n1 a2, a1 + n1 <= a2 -> a1 mod 8 = 0 -> shad a1 + shlen n1 <= shad a2.
Proof. intros a1 n1 a2 H M. rewrite !shad_div, shlen_div. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shlen_mono : forall a b, a <= b -> shlen a <= shlen b.
Proof. intros. rewrite !shlen_div. apply Z.div_le_mono; lia. Qed.
#[using="Type"] Lemma shlen_nonneg : forall a, 0 <= a -> 0 <= shlen a.
Proof. intros. rewrite shlen_div. apply Z.div_pos; lia. Qed.
#[using="Type"] Lemma shlen_mul8 : forall q, shlen (8 * q) = q.
Proof. intros. rewrite shlen_div. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
#[using="Type"] Lemma granules_eq : forall n, 0 <= n -> granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1).
Proof. intros n H. unfold granules. rewrite !shlen_div. destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma shlen_floor : forall n, shlen (n - n mod 8) = shlen n.
Proof. intros n. rewrite !shlen_div. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma aregion_mod : forall L c, al_space_beg L mod K_ALIGN = 0 -> aregion L c mod 65536 = 0.
Proof. intros L c H. unfold aregion, K_REGION, K_ALIGN in *. change (2^32) with (65536 * 65536). Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma regions_sep : forall L c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2.
Proof. intros L c1 c2 H. unfold aregion, K_REGION. nia. Qed.

#[using="Type"] Lemma slots_sep : forall L c k1 k2, 0 <= k1 -> k1 < k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2.
Proof. intros L c k1 k2 H1 H2 HS. unfold aslot_addr. nia. Qed.

#[using="Type"] Lemma slots_disjoint : forall L c k1 k2, 0 <= k1 -> 0 <= k2 -> k1 <> k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2 \/ aslot_addr L c k2 + size_of_class c <= aslot_addr L c k1.
Proof.
  intros L c k1 k2 H1 H2 NE HS. destruct (Z.lt_ge_cases k1 k2).
  - left. apply slots_sep; lia.
  - right. apply slots_sep; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_in_region : forall L st c k, let r := get_cls st c in let S := size_of_class c in
  0 < S -> 0 <= c_allocated_user r -> 0 <= k < ndist st c ->
  aregion L c <= aslot_addr L c k /\ aslot_addr L c k + S <= aregion L c + c_allocated_user r /\ 0 <= k * S.
Proof.
  intros L st c k r S HS HA HK. unfold ndist in HK. subst r S. unfold aslot_addr.
  set (A := c_allocated_user (get_cls st c)) in *. set (S := size_of_class c) in *.
  assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M1 : (k + 1) * S <= A / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  pose proof (Z.mul_div_le A S ltac:(lia)) as M2. rewrite Z.mul_comm in M2.
  split; [lia|]. split; [| exact P0]. rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. lia.
Qed.

#[using="Type"] Lemma slot_aligned : forall L c k, al_space_beg L mod K_ALIGN = 0 -> 1 <= c < K_NUM_CLASSES ->
  aslot_addr L c k mod 16 = 0.
Proof.
  intros L c k H Hc. pose proof (size_of_class_facts c Hc) as [_ M]. pose proof (aregion_mod L c H) as R.
  unfold aslot_addr. set (S := size_of_class c) in *. set (R0 := aregion L c) in *.
  replace (k * S) with ((k * (S / 16)) * 16) by (Z.div_mod_to_equations; nia).
  rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xcons (b : xbusy) (upd : Z -> xclass -> xclass) (X : aconc) : aconc :=
  mkAConc (fun c => if c =? xb_class b then upd c (x_cls X c) else x_cls X c) (b :: x_busy X).

#[using="Type"] Lemma busy_of_cons : forall b bs X c k,
  busy_of (mkAConc X (b :: bs)) c k =
    if (xb_class b =? c) && (xb_slot b =? k) then Some b else busy_of (mkAConc X bs) c k.
Proof. intros. unfold busy_of. cbn. destruct ((xb_class b =? c) && (xb_slot b =? k)); reflexivity. Qed.

#[using="Type"] Lemma busy_slots_cons : forall b bs X c,
  busy_slots (mkAConc X (b :: bs)) c = (if xb_class b =? c then [xb_slot b] else []) ++ busy_slots (mkAConc X bs) c.
Proof. intros. unfold busy_slots. cbn. destruct (xb_class b =? c); reflexivity. Qed.

#[using="Type"] Lemma busy_of_x_cls : forall X X' bs c k, busy_of (mkAConc X bs) c k = busy_of (mkAConc X' bs) c k.
Proof. reflexivity. Qed.
#[using="Type"] Lemma busy_slots_x_cls : forall X X' bs c, busy_slots (mkAConc X bs) c = busy_slots (mkAConc X' bs) c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_split_last : forall (l : list Z) k,
  nth_error l (length l - 1) = Some k -> l = removelast l ++ [k].
Proof.
  intros l k H. destruct l as [|a l'] eqn:E; [cbn in H; discriminate|]. rewrite <- E in *.
  assert (NE : l <> []) by (subst; discriminate).
  rewrite (app_removelast_last k NE) at 1. f_equal. f_equal.
  rewrite (app_removelast_last k NE) in H.
  rewrite length_app in H. cbn [length] in H. rewrite nth_error_app2 in H by lia.
  replace (length (removelast l) + 1 - 1 - length (removelast l))%nat with 0%nat in H by lia. cbn in H. congruence.
Qed.

#[using="Type"] Lemma length_removelast : forall {A} (l : list A), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros A l NE. induction l as [|a l IH]; [congruence|]. destruct l as [|b l'].
  - reflexivity.
  - cbn [removelast length]. cbn [removelast length] in IH. rewrite IH by discriminate. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

#[using="Type"] Lemma junk_frame : forall W m m' A n, junk_at m A n -> munch W m m' -> wmono asegs m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU WM D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma fill_frame : forall W m m' A n v, fill_at m A n v -> munch W m m' -> wmono asegs m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU WM D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma cells_frame : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros. eapply rw_cells_transport; eauto. Qed.

#[using="Type"] Lemma u64arr_frame : forall W m m' A ws, u64arr asegs m A ws -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros. eapply u64arr_transport; eauto. Qed.
#[using="Type"] Lemma u32arr_frame : forall W m m' A ws, u32arr asegs m A ws -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros. eapply u32arr_transport; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_cons : forall m A n v, 0 <= v < 256 -> 0 <= n ->
  rw_cells asegs m A [C1 (Z_to_bv 8 v)] -> fill_at m (A + 1) n v -> fill_at m A (1 + n) v.
Proof.
  intros m A n v Hv Hn H1 H2. apply (fill_merge m A 1 n v); [| exact H2 | lia | lia].
  unfold fill_at. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op].
  eapply rw_cells_recast; [exact H1 | cbn; tauto | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_app : forall m A n1 bs1 n2 bs2,
  rw_cells asegs m A [CB n1 bs1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells asegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells asegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB n1 bs1] ++ [CB n2 bs2]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exact M.
Qed.

#[using="Type"] Lemma cb_of_C1 : forall m A (b : byte), rw_cells asegs m A [C1 b] -> rw_cells asegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity]. Qed.

#[using="Type"] Lemma cb_of_fill : forall m A n v, fill_at m A n v ->
  rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof. intros m A n v H. exact H. Qed.

#[using="Type"] Lemma cb_nil : forall m A n bs, rw_cells asegs m A [CB n bs] -> rw_cells asegs m (A + Z.of_nat n) [CB 0 []].
Proof.
  intros m A n bs H. pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 _]]] [W0 [W1 _]]]. cbn in L, B1, W1.
  rewrite app_nil_r in B1. rewrite L in B1. rewrite Nat.add_0_r in W1.
  split; [split; [cbn; tauto|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac dforall H :=
  lazymatch type of H with
  | Forall _ (_ :: _) => let A := fresh "D" in pose proof (Forall_inv H) as A; cbn [fst snd] in A;
                         apply Forall_inv_tail in H; dforall H
  | _ => clear H
  end.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

Ltac xcell := eapply cells_frame; [eassumption | exact MU | exact WM | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)
Definition rt_hulls : list (Z * Z) :=
  [(0xa5490, 8); (0xa54a0, 48); (0xa54d0, 8); (0xa6018, 8); (0xa6108, 8); (0xa7358, 16);
   (0xabdb8, 13); (0xabdf8, 20); (0xabe24, 12); (0xabe4d, 1); (0xae5f8, 8); (0xade5c, 1);
   (0xade60, 1); (0xade64, 4); (0xaf2d8, 2); (0xaf2e0, 24); (0xaf2fc, 4); (0x130860, 3);
   (0x13e0a0, 8); (0x1400c0, 16); (0x140148, 8); (0x14014a, 1); (0x1401a0, 8); (ATP88, 8); (ATSD, 8);
   ((ATPv + 16), 4); (al_ctx L + 8, 4); (al_ctx L + 152, 8)]%Z.

#[using="MU WM"] Lemma arep_rt_frame : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt_hulls -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arelro_frame : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma azero_frame : forall A n, azero m A n -> munch W m m' -> wmono asegs m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros A n [Z0 WR] MU' WM' D. split.
  - intros i Hi. rewrite <- (Z0 i Hi). (pose proof WR as ndP__; nd_pre ndP__ 3%nat; intros W0 W1 _; nd_post).
    pose proof (MU' (wa (A + i))) as E. rewrite wa_unsigned in E by lia. apply E.
    eapply disjoint_outside; [apply D; lia | lia].
  - eapply wr_at_transport; [exact WR | exact WM'].
Qed.

#[using="MU WM"] Lemma ashadow_avail_frame : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frame; [exact Z1 | exact MU | exact WM | exact D1] | eapply azero_frame; [exact Z2 | exact MU | exact WM | exact D2]].
Qed.

#[using="MU WM"] Lemma arep_rt2_frame : arep_rt2 m -> disjoint_from W 0x14022c 1 -> disjoint_from W 0x1401b8 8 -> disjoint_from W 0xa71d8 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
Definition rt3_hulls : list (Z * Z) :=
  [(0xa7238, 16); (0xa7210, 8); (0xa7220, 8); (0xa7308, 8); (0xa7200, 8); (0x140178, 8); (0x140220, 8);
   (0xae600, 4); (0xabe58, 1); (0x13e098, 4);
   (0xa5490, 16); (0xa7398, 8); (0x13e0a0, 8); (0x140200, 8); (0x140218, 8); (0x601878, 8)]%Z.   (* [comment removed for export] *)
#[using="MU WM"] Lemma arep_rt3_frame : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  (nd_pre RT 17%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17; nd_post).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma ainstance_frame : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma aregion_cells_frame : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  (nd_pre RC 5%nat; intros A1 A2 A3 A4 A5; nd_post).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frame; [exact A5 | exact MU | exact WM | intros _; exact De].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma afreearray_frame : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  (nd_pre FA 3%nat; intros A1 A2 A3; nd_post).
  split; [| split].
  - eapply u32arr_frame; [exact A1 | exact MU | exact WM |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A2 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact DS].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma acache_cells_frame : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frame; [exact A1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frame; [exact A2 | exact MU | exact WM |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)
Definition xb_fits (b : xbusy) : Prop :=
  match xb_st b with
  | BBatch => True
  | _ => 0 <= xb_n b /\ 16 <= rz_size (xb_n b) /\ rz_size (xb_n b) + xb_n b <= size_of_class (xb_class b)
  end.

#[using="MU WM"] Lemma aslot_busy_frame : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact SB | exact MU | exact WM | intros _; exact D].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma aslots_update : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    (nd_pre (OTH k Hk NE) 3%nat; intros EB D WFB; nd_post). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + (nd_pre (WFB b eq_refl) 3%nat; intros C1' K1 FIT1; nd_post).
      eapply aslot_busy_frame; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma aslot_shadow_update : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells asegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
#[using="Type"] Lemma azero_cb : forall m A n k, azero m A n -> 0 <= k <= n ->
  rw_cells asegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. rewrite repeat_length. split; [lia|].
    intros i Hi. unfold mrd. rewrite Z0 by lia. symmetry. apply nth_error_repeat. exact Hi.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros i Hi. apply WR. lia.
Qed.
#[using="Type"] Lemma azero_split : forall m A n k, azero m A n -> 0 <= k <= n -> azero m (A + k) (n - k).
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split.
  - intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply Z0. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply WR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma busy_of_Some_facts : forall X c k b, busy_of X c k = Some b -> In b (x_busy X) /\ xb_class b = c /\ xb_slot b = k.
Proof.
  intros X c k b Hb. unfold busy_of in Hb. apply find_some in Hb. destruct Hb as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

#[using="Type"] Lemma rz_size_ge16 : forall n, 16 <= rz_size n.
Proof.
  intros n. rewrite rz_size_eq. assert (0 <= rz_log n) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
  assert (1 <= 2 ^ rz_log n) by (apply Z.pow_le_mono_r with (a := 2) in H; [| lia]; rewrite Z.pow_0_r in H; lia). lia.
Qed.

#[using="Type"] Lemma rounded_size_ge : forall n, n <= rounded_size n.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma awf_fits : forall L st X b, awf L st X -> In b (x_busy X) -> xb_fits b.
Proof.
  intros L st X b WF Hb. (nd_pre WF 9%nat; intros _ _ _ _ _ _ _ BUSY _; nd_post).
  destruct (BUSY b Hb) as [_ M]. unfold xb_fits.
  pose proof (rz_size_ge16 (xb_n b)) as R. pose proof (rounded_size_ge (xb_n b)) as RS.
  destruct (xb_st b); [| | exact I]; (nd_pre M 3%nat; intros N FIT _; nd_post); (split; [clear -N; lia|]); split; clear -R RS FIT; lia.
Qed.

#[using="Type"] Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

#[using="Type"] Lemma mod16_of_class : forall a s, a mod s = 0 -> s mod 16 = 0 -> 0 < s -> a mod 8 = 0.
Proof.
  intros a s H1 H2 Hs. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; [| exact H1]. eapply Z.divide_trans; [| exact H2]. exists 2. reflexivity.
Qed.

End CANSEC2.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma get_cls_put_cls_eq : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_cls_put_cls_ne : forall c c' r st, c' <> c -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_next : forall v st c, get_cls (set_next v st) c = get_cls st c. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_live : forall v st c, get_cls (set_live v st) c = get_cls st c. Proof. reflexivity. Qed.
#[using="Type"] Lemma max_count_eq : forall st st' c, a_cinit st' = a_cinit st -> max_count st' c = max_count st c.
Proof. intros st st' c E. unfold max_count. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Definition st_fast (st : astate) (c n cnt : Z) : astate :=
  set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
    (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)).

#[using="Type"] Lemma st_fast_fields : forall st c n cnt,
     a_space_beg (st_fast st c n cnt) = a_space_beg st /\ a_ptr_array (st_fast st c n cnt) = a_ptr_array st
  /\ a_nres (st_fast st c n cnt) = a_nres st /\ a_nsec (st_fast st c n cnt) = a_nsec st
  /\ a_cinit (st_fast st c n cnt) = a_cinit st
  /\ a_live (st_fast st c n cnt) = <[ a_next st := CPrim c n ]> (a_live st)
  /\ a_next (st_fast st c n cnt) = N.succ (a_next st)
  /\ a_qloc (st_fast st c n cnt) = a_qloc st /\ a_qloc_bytes (st_fast st c n cnt) = a_qloc_bytes st
  /\ a_qglob (st_fast st c n cnt) = a_qglob st /\ a_qglob_bytes (st_fast st c n cnt) = a_qglob_bytes st.
Proof. intros. repeat split; reflexivity. Qed.

#[using="Type"] Lemma st_fast_cls : forall st c n cnt c',
  get_cls (st_fast st c n cnt) c' = if c' =? c then cls_set_count (cnt - 1) (get_cls st c) else get_cls st c'.
Proof.
  intros. unfold st_fast. rewrite get_cls_set_next, get_cls_set_live.
  destruct (Z.eqb_spec c' c) as [->|NE]; [apply get_cls_put_cls_eq | apply get_cls_put_cls_ne; exact NE].
Qed.

#[using="Type"] Lemma st_fast_counters : forall st c n cnt c',
     c_mapped_user (get_cls (st_fast st c n cnt) c') = c_mapped_user (get_cls st c')
  /\ c_allocated_user (get_cls (st_fast st c n cnt) c') = c_allocated_user (get_cls st c')
  /\ c_num_freed (get_cls (st_fast st c n cnt) c') = c_num_freed (get_cls st c')
  /\ c_mapped_free_array (get_cls (st_fast st c n cnt) c') = c_mapped_free_array (get_cls st c')
  /\ c_count (get_cls (st_fast st c n cnt) c') = (if c' =? c then cnt - 1 else c_count (get_cls st c')).
Proof. intros. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; repeat split; reflexivity. Qed.

#[using="Type"] Lemma st_fast_max_count : forall st c n cnt c', max_count (st_fast st c n cnt) c' = max_count st c'.
Proof. intros. apply max_count_eq. reflexivity. Qed.
#[using="Type"] Lemma st_fast_ndist : forall st c n cnt c', ndist (st_fast st c n cnt) c' = ndist st c'.
Proof. intros. unfold ndist. rewrite (proj1 (proj2 (st_fast_counters st c n cnt c'))). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma size_of_class_facts : forall c, 1 <= c < K_NUM_CLASSES ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  enough (B : (16 <=? size_of_class c) && (size_of_class c <=? 65536) && (size_of_class c mod 16 =? 0) = true).
  { apply andb_prop in B. destruct B as [B B3]. apply andb_prop in B. destruct B as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.eqb_eq in B3. lia. }
  assert (E : exists i, (0 <= i < 31)%nat /\ c = Z.of_nat i + 1).
  { exists (Z.to_nat (c - 1)). split; lia. }
  (nd_pre E 3%nat; intros i Hi ndR1__; nd_post; revert ndR1__; intros ->).
  do 31 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

#[using="Type"] Lemma shlen_div : forall d, shlen d = d / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
#[using="Type"] Lemma shad_div : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
#[using="Type"] Lemma shad_add : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + d / 8.
Proof. intros a d H. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shad_add_shlen : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + shlen d.
Proof. intros. rewrite shlen_div. apply shad_add. assumption. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma shad_sep : forall a1 n1 a2, a1 + n1 <= a2 -> a1 mod 8 = 0 -> shad a1 + shlen n1 <= shad a2.
Proof. intros a1 n1 a2 H M. rewrite !shad_div, shlen_div. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shlen_mono : forall a b, a <= b -> shlen a <= shlen b.
Proof. intros. rewrite !shlen_div. apply Z.div_le_mono; lia. Qed.
#[using="Type"] Lemma shlen_nonneg : forall a, 0 <= a -> 0 <= shlen a.
Proof. intros. rewrite shlen_div. apply Z.div_pos; lia. Qed.
#[using="Type"] Lemma shlen_mul8 : forall q, shlen (8 * q) = q.
Proof. intros. rewrite shlen_div. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
#[using="Type"] Lemma granules_eq : forall n, 0 <= n -> granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1).
Proof. intros n H. unfold granules. rewrite !shlen_div. destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma shlen_floor : forall n, shlen (n - n mod 8) = shlen n.
Proof. intros n. rewrite !shlen_div. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma aregion_mod : forall L c, al_space_beg L mod K_ALIGN = 0 -> aregion L c mod 65536 = 0.
Proof. intros L c H. unfold aregion, K_REGION, K_ALIGN in *. change (2^32) with (65536 * 65536). Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma regions_sep : forall L c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2.
Proof. intros L c1 c2 H. unfold aregion, K_REGION. nia. Qed.

#[using="Type"] Lemma slots_sep : forall L c k1 k2, 0 <= k1 -> k1 < k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2.
Proof. intros L c k1 k2 H1 H2 HS. unfold aslot_addr. nia. Qed.

#[using="Type"] Lemma slots_disjoint : forall L c k1 k2, 0 <= k1 -> 0 <= k2 -> k1 <> k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2 \/ aslot_addr L c k2 + size_of_class c <= aslot_addr L c k1.
Proof.
  intros L c k1 k2 H1 H2 NE HS. destruct (Z.lt_ge_cases k1 k2).
  - left. apply slots_sep; lia.
  - right. apply slots_sep; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_in_region : forall L st c k, let r := get_cls st c in let S := size_of_class c in
  0 < S -> 0 <= c_allocated_user r -> 0 <= k < ndist st c ->
  aregion L c <= aslot_addr L c k /\ aslot_addr L c k + S <= aregion L c + c_allocated_user r /\ 0 <= k * S.
Proof.
  intros L st c k r S HS HA HK. unfold ndist in HK. subst r S. unfold aslot_addr.
  set (A := c_allocated_user (get_cls st c)) in *. set (S := size_of_class c) in *.
  assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M1 : (k + 1) * S <= A / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  pose proof (Z.mul_div_le A S ltac:(lia)) as M2. rewrite Z.mul_comm in M2.
  split; [lia|]. split; [| exact P0]. rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. lia.
Qed.

#[using="Type"] Lemma slot_aligned : forall L c k, al_space_beg L mod K_ALIGN = 0 -> 1 <= c < K_NUM_CLASSES ->
  aslot_addr L c k mod 16 = 0.
Proof.
  intros L c k H Hc. pose proof (size_of_class_facts c Hc) as [_ M]. pose proof (aregion_mod L c H) as R.
  unfold aslot_addr. set (S := size_of_class c) in *. set (R0 := aregion L c) in *.
  replace (k * S) with ((k * (S / 16)) * 16) by (Z.div_mod_to_equations; nia).
  rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xcons (b : xbusy) (upd : Z -> xclass -> xclass) (X : aconc) : aconc :=
  mkAConc (fun c => if c =? xb_class b then upd c (x_cls X c) else x_cls X c) (b :: x_busy X).

#[using="Type"] Lemma busy_of_cons : forall b bs X c k,
  busy_of (mkAConc X (b :: bs)) c k =
    if (xb_class b =? c) && (xb_slot b =? k) then Some b else busy_of (mkAConc X bs) c k.
Proof. intros. unfold busy_of. cbn. destruct ((xb_class b =? c) && (xb_slot b =? k)); reflexivity. Qed.

#[using="Type"] Lemma busy_slots_cons : forall b bs X c,
  busy_slots (mkAConc X (b :: bs)) c = (if xb_class b =? c then [xb_slot b] else []) ++ busy_slots (mkAConc X bs) c.
Proof. intros. unfold busy_slots. cbn. destruct (xb_class b =? c); reflexivity. Qed.

#[using="Type"] Lemma busy_of_x_cls : forall X X' bs c k, busy_of (mkAConc X bs) c k = busy_of (mkAConc X' bs) c k.
Proof. reflexivity. Qed.
#[using="Type"] Lemma busy_slots_x_cls : forall X X' bs c, busy_slots (mkAConc X bs) c = busy_slots (mkAConc X' bs) c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_split_last : forall (l : list Z) k,
  nth_error l (length l - 1) = Some k -> l = removelast l ++ [k].
Proof.
  intros l k H. destruct l as [|a l'] eqn:E; [cbn in H; discriminate|]. rewrite <- E in *.
  assert (NE : l <> []) by (subst; discriminate).
  rewrite (app_removelast_last k NE) at 1. f_equal. f_equal.
  rewrite (app_removelast_last k NE) in H.
  rewrite length_app in H. cbn [length] in H. rewrite nth_error_app2 in H by lia.
  replace (length (removelast l) + 1 - 1 - length (removelast l))%nat with 0%nat in H by lia. cbn in H. congruence.
Qed.

#[using="Type"] Lemma length_removelast : forall {A} (l : list A), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros A l NE. induction l as [|a l IH]; [congruence|]. destruct l as [|b l'].
  - reflexivity.
  - cbn [removelast length]. cbn [removelast length] in IH. rewrite IH by discriminate. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

#[using="Type"] Lemma junk_frame : forall W m m' A n, junk_at m A n -> munch W m m' -> wmono asegs m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU WM D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma fill_frame : forall W m m' A n v, fill_at m A n v -> munch W m m' -> wmono asegs m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU WM D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma cells_frame : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros. eapply rw_cells_transport; eauto. Qed.

#[using="Type"] Lemma u64arr_frame : forall W m m' A ws, u64arr asegs m A ws -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros. eapply u64arr_transport; eauto. Qed.
#[using="Type"] Lemma u32arr_frame : forall W m m' A ws, u32arr asegs m A ws -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros. eapply u32arr_transport; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_cons : forall m A n v, 0 <= v < 256 -> 0 <= n ->
  rw_cells asegs m A [C1 (Z_to_bv 8 v)] -> fill_at m (A + 1) n v -> fill_at m A (1 + n) v.
Proof.
  intros m A n v Hv Hn H1 H2. apply (fill_merge m A 1 n v); [| exact H2 | lia | lia].
  unfold fill_at. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op].
  eapply rw_cells_recast; [exact H1 | cbn; tauto | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_app : forall m A n1 bs1 n2 bs2,
  rw_cells asegs m A [CB n1 bs1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells asegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells asegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB n1 bs1] ++ [CB n2 bs2]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exact M.
Qed.

#[using="Type"] Lemma cb_of_C1 : forall m A (b : byte), rw_cells asegs m A [C1 b] -> rw_cells asegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity]. Qed.

#[using="Type"] Lemma cb_of_fill : forall m A n v, fill_at m A n v ->
  rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof. intros m A n v H. exact H. Qed.

#[using="Type"] Lemma cb_nil : forall m A n bs, rw_cells asegs m A [CB n bs] -> rw_cells asegs m (A + Z.of_nat n) [CB 0 []].
Proof.
  intros m A n bs H. pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 _]]] [W0 [W1 _]]]. cbn in L, B1, W1.
  rewrite app_nil_r in B1. rewrite L in B1. rewrite Nat.add_0_r in W1.
  split; [split; [cbn; tauto|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac dforall H :=
  lazymatch type of H with
  | Forall _ (_ :: _) => let A := fresh "D" in pose proof (Forall_inv H) as A; cbn [fst snd] in A;
                         apply Forall_inv_tail in H; dforall H
  | _ => clear H
  end.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

Ltac xcell := eapply cells_frame; [eassumption | exact MU | exact WM | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)
Definition rt_hulls : list (Z * Z) :=
  [(0xa5870, 8); (0xa5880, 48); (0xa58b0, 8); (0xa63f8, 8); (0xa64e8, 8); (0xa7738, 16);
   (0xac1b8, 13); (0xac1f8, 20); (0xac224, 12); (0xac24d, 1); (0xae9f8, 8); (0xae25c, 1);
   (0xae260, 1); (0xae264, 4); (0xaf6d8, 2); (0xaf6e0, 24); (0xaf6fc, 4); (0x130c60, 3);
   (0x13e4a0, 8); (0x1404c0, 16); (0x140548, 8); (0x14054a, 1); (0x1405a0, 8); (ATP88, 8); (ATSD, 8);
   ((ATPv + 16), 4); (al_ctx L + 8, 4); (al_ctx L + 152, 8)]%Z.

#[using="MU WM"] Lemma arep_rt_frame : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt_hulls -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arelro_frame : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma azero_frame : forall A n, azero m A n -> munch W m m' -> wmono asegs m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros A n [Z0 WR] MU' WM' D. split.
  - intros i Hi. rewrite <- (Z0 i Hi). (pose proof WR as ndP__; nd_pre ndP__ 3%nat; intros W0 W1 _; nd_post).
    pose proof (MU' (wa (A + i))) as E. rewrite wa_unsigned in E by lia. apply E.
    eapply disjoint_outside; [apply D; lia | lia].
  - eapply wr_at_transport; [exact WR | exact WM'].
Qed.

#[using="MU WM"] Lemma ashadow_avail_frame : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frame; [exact Z1 | exact MU | exact WM | exact D1] | eapply azero_frame; [exact Z2 | exact MU | exact WM | exact D2]].
Qed.

#[using="MU WM"] Lemma arep_rt2_frame : arep_rt2 m -> disjoint_from W 0x14062c 1 -> disjoint_from W 0x1405b8 8 -> disjoint_from W 0xa75b8 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
Definition rt3_hulls : list (Z * Z) :=
  [(0xa7618, 16); (0xa75f0, 8); (0xa7600, 8); (0xa76e8, 8); (0xa75e0, 8); (0x140578, 8); (0x140620, 8);
   (0xaea00, 4); (0xac258, 1); (0x13e498, 4);
   (0xa5870, 16); (0xa7778, 8); (0x13e4a0, 8); (0x140600, 8); (0x140618, 8); (0x601c78, 8)]%Z.   (* [comment removed for export] *)
#[using="MU WM"] Lemma arep_rt3_frame : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  (nd_pre RT 17%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17; nd_post).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma ainstance_frame : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma aregion_cells_frame : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  (nd_pre RC 5%nat; intros A1 A2 A3 A4 A5; nd_post).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frame; [exact A5 | exact MU | exact WM | intros _; exact De].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma afreearray_frame : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  (nd_pre FA 3%nat; intros A1 A2 A3; nd_post).
  split; [| split].
  - eapply u32arr_frame; [exact A1 | exact MU | exact WM |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A2 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact DS].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma acache_cells_frame : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frame; [exact A1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frame; [exact A2 | exact MU | exact WM |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)
Definition xb_fits (b : xbusy) : Prop :=
  match xb_st b with
  | BBatch => True
  | _ => 0 <= xb_n b /\ 16 <= rz_size (xb_n b) /\ rz_size (xb_n b) + xb_n b <= size_of_class (xb_class b)
  end.

#[using="MU WM"] Lemma aslot_busy_frame : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact SB | exact MU | exact WM | intros _; exact D].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma aslots_update : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    (nd_pre (OTH k Hk NE) 3%nat; intros EB D WFB; nd_post). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + (nd_pre (WFB b eq_refl) 3%nat; intros C1' K1 FIT1; nd_post).
      eapply aslot_busy_frame; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma aslot_shadow_update : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells asegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
#[using="Type"] Lemma azero_cb : forall m A n k, azero m A n -> 0 <= k <= n ->
  rw_cells asegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. rewrite repeat_length. split; [lia|].
    intros i Hi. unfold mrd. rewrite Z0 by lia. symmetry. apply nth_error_repeat. exact Hi.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros i Hi. apply WR. lia.
Qed.
#[using="Type"] Lemma azero_split : forall m A n k, azero m A n -> 0 <= k <= n -> azero m (A + k) (n - k).
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split.
  - intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply Z0. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply WR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma busy_of_Some_facts : forall X c k b, busy_of X c k = Some b -> In b (x_busy X) /\ xb_class b = c /\ xb_slot b = k.
Proof.
  intros X c k b Hb. unfold busy_of in Hb. apply find_some in Hb. destruct Hb as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

#[using="Type"] Lemma rz_size_ge16 : forall n, 16 <= rz_size n.
Proof.
  intros n. rewrite rz_size_eq. assert (0 <= rz_log n) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
  assert (1 <= 2 ^ rz_log n) by (apply Z.pow_le_mono_r with (a := 2) in H; [| lia]; rewrite Z.pow_0_r in H; lia). lia.
Qed.

#[using="Type"] Lemma rounded_size_ge : forall n, n <= rounded_size n.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma awf_fits : forall L st X b, awf L st X -> In b (x_busy X) -> xb_fits b.
Proof.
  intros L st X b WF Hb. (nd_pre WF 9%nat; intros _ _ _ _ _ _ _ BUSY _; nd_post).
  destruct (BUSY b Hb) as [_ M]. unfold xb_fits.
  pose proof (rz_size_ge16 (xb_n b)) as R. pose proof (rounded_size_ge (xb_n b)) as RS.
  destruct (xb_st b); [| | exact I]; (nd_pre M 3%nat; intros N FIT _; nd_post); (split; [clear -N; lia|]); split; clear -R RS FIT; lia.
Qed.

#[using="Type"] Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

#[using="Type"] Lemma mod16_of_class : forall a s, a mod s = 0 -> s mod 16 = 0 -> 0 < s -> a mod 8 = 0.
Proof.
  intros a s H1 H2 Hs. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; [| exact H1]. eapply Z.divide_trans; [| exact H2]. exists 2. reflexivity.
Qed.

End CANSEC2.
(* [comment removed for export] *)
End TwB.
End ARepFrame.

(* [comment removed for export] *)
Module ARepFrameD.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FramesD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.

Ltac xcell := eapply cells_frameD; [eassumption | exact MU | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)

#[using="MU"] Lemma arep_rt_frameD : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) (rt_hulls L) -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arelro_frameD : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)

#[using="MU"] Lemma ashadow_avail_frameD : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frameD; [exact Z1 | exact MU | exact D1] | eapply azero_frameD; [exact Z2 | exact MU | exact D2]].
Qed.

#[using="MU"] Lemma arep_rt2_frameD : arep_rt2 m -> disjoint_from W 0x14022c 1 -> disjoint_from W 0x1401b8 8 -> disjoint_from W 0xa71d8 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arep_rt3_frameD : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  (nd_pre RT 17%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17; nd_post).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma ainstance_frameD : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma aregion_cells_frameD : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  (nd_pre RC 5%nat; intros A1 A2 A3 A4 A5; nd_post).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frameD; [exact A3 | exact MU | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frameD; [exact A5 | exact MU | intros _; exact De].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma afreearray_frameD : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  (nd_pre FA 3%nat; intros A1 A2 A3; nd_post).
  split; [| split].
  - eapply u32arr_frameD; [exact A1 | exact MU |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A2 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A3 | exact MU | intros _; exact DS].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma acache_cells_frameD : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frameD; [exact A1 | exact MU |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frameD; [exact A2 | exact MU |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)

#[using="MU"] Lemma aslot_busy_frameD : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact SB | exact MU | intros _; exact D].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma aslots_updateD : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    (nd_pre (OTH k Hk NE) 3%nat; intros EB D WFB; nd_post). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + (nd_pre (WFB b eq_refl) 3%nat; intros C1' K1 FIT1; nd_post).
      eapply aslot_busy_frameD; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frameD; [exact SL | exact MU | intros _; exact D].
  - eapply junk_frameD; [exact UND | exact MU | exact DU].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma aslot_shadow_updateD : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells asegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frameD; [exact SL | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frameD; [exact UND | exact MU | exact DU].
Qed.
End FramesD.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FramesD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.

Ltac xcell := eapply cells_frameD; [eassumption | exact MU | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)

#[using="MU"] Lemma arep_rt_frameD : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) (rt_hulls L) -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  (nd_pre RT 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arelro_frameD : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)

#[using="MU"] Lemma ashadow_avail_frameD : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frameD; [exact Z1 | exact MU | exact D1] | eapply azero_frameD; [exact Z2 | exact MU | exact D2]].
Qed.

#[using="MU"] Lemma arep_rt2_frameD : arep_rt2 m -> disjoint_from W 0x14062c 1 -> disjoint_from W 0x1405b8 8 -> disjoint_from W 0xa75b8 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arep_rt3_frameD : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  (nd_pre RT 17%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17; nd_post).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma ainstance_frameD : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma aregion_cells_frameD : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  (nd_pre RC 5%nat; intros A1 A2 A3 A4 A5; nd_post).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frameD; [exact A3 | exact MU | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frameD; [exact A5 | exact MU | intros _; exact De].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma afreearray_frameD : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  (nd_pre FA 3%nat; intros A1 A2 A3; nd_post).
  split; [| split].
  - eapply u32arr_frameD; [exact A1 | exact MU |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A2 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A3 | exact MU | intros _; exact DS].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma acache_cells_frameD : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frameD; [exact A1 | exact MU |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frameD; [exact A2 | exact MU |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)

#[using="MU"] Lemma aslot_busy_frameD : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - (nd_pre FIT 3%nat; intros N RZ FIT; nd_post). (nd_pre SB 3%nat; intros LH [stb [E HDR]] UJ; nd_post). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact SB | exact MU | intros _; exact D].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma aslots_updateD : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    (nd_pre (OTH k Hk NE) 3%nat; intros EB D WFB; nd_post). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + (nd_pre (WFB b eq_refl) 3%nat; intros C1' K1 FIT1; nd_post).
      eapply aslot_busy_frameD; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frameD; [exact SL | exact MU | intros _; exact D].
  - eapply junk_frameD; [exact UND | exact MU | exact DU].
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma aslot_shadow_updateD : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells asegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frameD; [exact SL | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frameD; [exact UND | exact MU | exact DU].
Qed.
End FramesD.
End CANSEC1.
End TwB.
End ARepFrameD.

(* [comment removed for export] *)
Module ADeallocFn_kit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma aintal_flag_true : forall (ia : bool) m,
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  ia = true.
Proof.
  intros ia m [[_ B1] _] [[_ B2] _]. destruct ia; [reflexivity| exfalso].
  unfold AIA_FLAG in B1. (nd_pre B1 3%nat; intros _ _ H1; nd_post). (nd_pre B2 3%nat; intros _ _ H2; nd_post).
  specialize (H1 0%nat ltac:(cbn; lia)). specialize (H2 0%nat ltac:(cbn; lia)). rewrite H1 in H2. cbn in H2.
  injection H2 as E. vm_compute in E. discriminate.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma aintal_flag_true : forall (ia : bool) m,
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  ia = true.
Proof.
  intros ia m [[_ B1] _] [[_ B2] _]. destruct ia; [reflexivity| exfalso].
  unfold AIA_FLAG in B1. (nd_pre B1 3%nat; intros _ _ H1; nd_post). (nd_pre B2 3%nat; intros _ _ H2; nd_post).
  specialize (H1 0%nat ltac:(cbn; lia)). specialize (H2 0%nat ltac:(cbn; lia)). rewrite H1 in H2. cbn in H2.
  injection H2 as E. vm_compute in E. discriminate.
Qed.
End CANSEC1.
End TwB.
End ADeallocFn_kit.

(* [comment removed for export] *)
Module AFreeGeo.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Slot.
Variables (L : alayout) (st : astate) (X : aconc) (c k : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.

Let S := size_of_class c.
Let AB := aslot_addr L c k.

#[using="tlsI X ALO WF HC KR"] Lemma slot_geo :
     16 <= S <= 65536 /\ S mod 16 = 0 /\ AB mod 16 = 0
  /\ aregion L c <= AB /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)
  /\ c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) /\ c_mapped_user (get_cls st c) <= K_FREEARR_OFF
  /\ al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE
  /\ 0x10007fff8000 <= AB /\ AB + S <= ATOP
  /\ aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0.
Proof.
  pose proof (size_of_class_facts c HC) as [S1 S2].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  (nd_pre (PERC c HC) 5%nat; intros A1 A2 A3 A4 _; nd_post).
  (pose proof (slot_in_region L st c k ltac:(fold S; lia) ltac:(lia) KR) as ndP__; nd_pre ndP__ 3%nat; intros G1 G2 G3; nd_post).
  pose proof (slot_aligned L c k SAL HC) as AL16.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  assert (R8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0).
  { generalize SAL A4. clear. unfold aregion, K_REGION, K_USER_MAP, K_ALIGN. intros. Z.div_mod_to_equations. lia. }
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_FREEARR_OFF <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  subst S AB. generalize S1 S2 A1 A2 G1 G2 G3 AL16 SP1 SP2 R8 RS. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. intros. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI st X ALO WF HC KR"] Lemma slot_sep_objects :
     (al_t L + 4096 <= AB \/ AB + S <= al_t L) /\ (al_ctx L + 65536 <= AB \/ AB + S <= al_ctx L)
  /\ (al_nodes L + 1048576 <= AB \/ AB + S <= al_nodes L) /\ (al_store L + 8388608 <= AB \/ AB + S <= al_store L)
  /\ (al_fake L + 11571200 <= AB \/ AB + S <= al_fake L).
Proof.
  (pose proof slot_geo as ndP__; nd_pre ndP__ 10%nat; intros S1 _ _ _ _ _ _ G7 G8 _; nd_post).
  exact (alayout_slot_disj L AB S ALO G7 G8 ltac:(lia)).
Qed.

#[using="X ALO WF HC KR"] Lemma slot_rng : forall RNG, arng L RNG st -> rng RNG AB S /\ rng RNG (shad AB) (shlen S).
Proof.
  intros RNG (_ & _ & _ & _ & _ & _ & _ & _ & _ & RC & _). (nd_pre (RC c HC) 3%nat; intros R1 R2 _; nd_post).
  (pose proof slot_geo as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL G1 G2 G3 G4 _ _ _ _ R8 M8; nd_post).
  split.
  - eapply rng_sub; [exact R1| lia| lia].
  - eapply rng_sub; [exact R2| |].
    + rewrite !shad_div. generalize G1 R8. clear. intros. Z.div_mod_to_equations. lia.
    + rewrite !shad_div, !shlen_div. generalize G1 G2 G3 R8 M8 S1. clear. intros. Z.div_mod_to_equations. lia.
Qed.
End Slot.

(* [comment removed for export] *)
#[using="Type"] Lemma slots_sep_any : forall L st X c1 k1 c2 k2,
  alayout_ok L -> awf L st X -> 1 <= c1 < K_NUM_CLASSES -> 1 <= c2 < K_NUM_CLASSES ->
  0 <= k1 < ndist st c1 -> 0 <= k2 < ndist st c2 -> (c1 <> c2 \/ k1 <> k2) ->
  aslot_addr L c1 k1 + size_of_class c1 <= aslot_addr L c2 k2 \/ aslot_addr L c2 k2 + size_of_class c2 <= aslot_addr L c1 k1.
Proof.
  intros L st X c1 k1 c2 k2 ALO WF H1 H2 K1 K2 NE.
  (pose proof (slot_geo L st X c1 k1 ALO WF H1 K1) as ndP__; nd_pre ndP__ 8%nat; intros S1 _ _ G1 G2 G3 G4 _; nd_post).
  (pose proof (slot_geo L st X c2 k2 ALO WF H2 K2) as ndP__; nd_pre ndP__ 8%nat; intros T1 _ _ F1 F2 F3 F4 _; nd_post).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - apply (slots_disjoint L c1 k1 k2); lia.
  - generalize S1 G1 G2 G3 G4 T1 F1 F2 F3 F4 NC. clear. unfold aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    intros. destruct (Z.lt_ge_cases c1 c2); [left| right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
#[using="Type"] Lemma rz_size_facts : forall n, 0 <= n -> 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
  intros n Hn. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : exists i, (i <= 7)%nat /\ rz_log n = Z.of_nat i) by (exists (Z.to_nat (rz_log n)); split; lia).
  (nd_pre E 3%nat; intros i Hi ndR1__; nd_post; revert ndR1__; intros ->). do 8 (destruct i as [|i]; [cbn; lia|]). lia.
Qed.

#[using="Type"] Lemma rounded_size_facts : forall n, 0 <= n -> n <= rounded_size n /\ 8 <= rounded_size n /\ rounded_size n mod 8 = 0 /\ rup n 8 <= rounded_size n
  /\ rounded_size n <= n + 15.
Proof.
  intros n Hn. unfold rounded_size, rup. Z.div_mod_to_equations. nia.
Qed.

Section Chunk.
Variables (L : alayout) (st : astate) (X : aconc) (c k n : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : rounded_size n + rz_size n <= size_of_class c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let hm := UB - 16.

#[using="tlsI st X ALO WF HC KR N0 FIT"] Lemma chunk_geo :
     hm mod 16 = 0 /\ UB mod 16 = 0 /\ AB + 16 <= UB /\ AB <= hm
  /\ 0x10007fff8000 <= hm /\ UB + rup n 8 <= AB + S /\ AB + S <= ATOP /\ hm + 16 + rup n 8 <= ATOP /\ n <= 65536 /\ n <= Q_MAX
  /\ 0x10007fff8000 <= AB /\ n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ 8 <= S - rz_size n.
Proof.
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 12%nat; intros S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 _; nd_post).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. (pose proof (rounded_size_facts n N0) as ndP__; nd_pre ndP__ 5%nat; intros RS1 RS2 RS3 RS4 RS5; nd_post).
  subst S AB UB hm. generalize S1 S2 AL G1 G2 G7 G8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold Q_MAX, rup. intros. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI X ALO WF HC KR N0 FIT"] Lemma chunk_shadow_geo :
     shad UB = shad AB + shlen (rz_size n) /\ 2 <= shlen (rz_size n)
  /\ shlen (rup n 8) = granules n /\ 0 <= shlen (rup n 8)
  /\ shlen (rz_size n) + granules n <= shlen S
  /\ 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fff8000
  /\ shad (aregion L c) <= shad AB /\ shad AB + shlen S <= shad (aregion L c) + shlen (c_mapped_user (get_cls st c)).
Proof.
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. (pose proof (rounded_size_facts n N0) as ndP__; nd_pre ndP__ 5%nat; intros RS1 RS2 RS3 RS4 RS5; nd_post).
  subst S AB UB hm. unfold granules. rewrite !shad_div, !shlen_div.
  generalize S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold ASHOFF, rup, K_FREEARR_OFF, K_SPACE_SIZE. intros.
  Z.div_mod_to_equations. lia.
Qed.
End Chunk.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Slot.
Variables (L : alayout) (st : astate) (X : aconc) (c k : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.

Let S := size_of_class c.
Let AB := aslot_addr L c k.

#[using="tlsI X ALO WF HC KR"] Lemma slot_geo :
     16 <= S <= 65536 /\ S mod 16 = 0 /\ AB mod 16 = 0
  /\ aregion L c <= AB /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)
  /\ c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) /\ c_mapped_user (get_cls st c) <= K_FREEARR_OFF
  /\ al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE
  /\ 0x10007fff8000 <= AB /\ AB + S <= ATOP
  /\ aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0.
Proof.
  pose proof (size_of_class_facts c HC) as [S1 S2].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  (nd_pre (PERC c HC) 5%nat; intros A1 A2 A3 A4 _; nd_post).
  (pose proof (slot_in_region L st c k ltac:(fold S; lia) ltac:(lia) KR) as ndP__; nd_pre ndP__ 3%nat; intros G1 G2 G3; nd_post).
  pose proof (slot_aligned L c k SAL HC) as AL16.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  assert (R8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0).
  { generalize SAL A4. clear. unfold aregion, K_REGION, K_USER_MAP, K_ALIGN. intros. Z.div_mod_to_equations. lia. }
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_FREEARR_OFF <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  subst S AB. generalize S1 S2 A1 A2 G1 G2 G3 AL16 SP1 SP2 R8 RS. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. intros. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI st X ALO WF HC KR"] Lemma slot_sep_objects :
     (al_t L + 4096 <= AB \/ AB + S <= al_t L) /\ (al_ctx L + 65536 <= AB \/ AB + S <= al_ctx L)
  /\ (al_nodes L + 1048576 <= AB \/ AB + S <= al_nodes L) /\ (al_store L + 8388608 <= AB \/ AB + S <= al_store L)
  /\ (al_fake L + 11571200 <= AB \/ AB + S <= al_fake L).
Proof.
  (pose proof slot_geo as ndP__; nd_pre ndP__ 10%nat; intros S1 _ _ _ _ _ _ G7 G8 _; nd_post).
  exact (alayout_slot_disj L AB S ALO G7 G8 ltac:(lia)).
Qed.

#[using="X ALO WF HC KR"] Lemma slot_rng : forall RNG, arng L RNG st -> rng RNG AB S /\ rng RNG (shad AB) (shlen S).
Proof.
  intros RNG (_ & _ & _ & _ & _ & _ & _ & _ & _ & RC & _). (nd_pre (RC c HC) 3%nat; intros R1 R2 _; nd_post).
  (pose proof slot_geo as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL G1 G2 G3 G4 _ _ _ _ R8 M8; nd_post).
  split.
  - eapply rng_sub; [exact R1| lia| lia].
  - eapply rng_sub; [exact R2| |].
    + rewrite !shad_div. generalize G1 R8. clear. intros. Z.div_mod_to_equations. lia.
    + rewrite !shad_div, !shlen_div. generalize G1 G2 G3 R8 M8 S1. clear. intros. Z.div_mod_to_equations. lia.
Qed.
End Slot.

(* [comment removed for export] *)
#[using="Type"] Lemma slots_sep_any : forall L st X c1 k1 c2 k2,
  alayout_ok L -> awf L st X -> 1 <= c1 < K_NUM_CLASSES -> 1 <= c2 < K_NUM_CLASSES ->
  0 <= k1 < ndist st c1 -> 0 <= k2 < ndist st c2 -> (c1 <> c2 \/ k1 <> k2) ->
  aslot_addr L c1 k1 + size_of_class c1 <= aslot_addr L c2 k2 \/ aslot_addr L c2 k2 + size_of_class c2 <= aslot_addr L c1 k1.
Proof.
  intros L st X c1 k1 c2 k2 ALO WF H1 H2 K1 K2 NE.
  (pose proof (slot_geo L st X c1 k1 ALO WF H1 K1) as ndP__; nd_pre ndP__ 8%nat; intros S1 _ _ G1 G2 G3 G4 _; nd_post).
  (pose proof (slot_geo L st X c2 k2 ALO WF H2 K2) as ndP__; nd_pre ndP__ 8%nat; intros T1 _ _ F1 F2 F3 F4 _; nd_post).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - apply (slots_disjoint L c1 k1 k2); lia.
  - generalize S1 G1 G2 G3 G4 T1 F1 F2 F3 F4 NC. clear. unfold aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    intros. destruct (Z.lt_ge_cases c1 c2); [left| right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
#[using="Type"] Lemma rz_size_facts : forall n, 0 <= n -> 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
  intros n Hn. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : exists i, (i <= 7)%nat /\ rz_log n = Z.of_nat i) by (exists (Z.to_nat (rz_log n)); split; lia).
  (nd_pre E 3%nat; intros i Hi ndR1__; nd_post; revert ndR1__; intros ->). do 8 (destruct i as [|i]; [cbn; lia|]). lia.
Qed.

#[using="Type"] Lemma rounded_size_facts : forall n, 0 <= n -> n <= rounded_size n /\ 8 <= rounded_size n /\ rounded_size n mod 8 = 0 /\ rup n 8 <= rounded_size n
  /\ rounded_size n <= n + 15.
Proof.
  intros n Hn. unfold rounded_size, rup. Z.div_mod_to_equations. nia.
Qed.

Section Chunk.
Variables (L : alayout) (st : astate) (X : aconc) (c k n : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : rounded_size n + rz_size n <= size_of_class c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let hm := UB - 16.

#[using="tlsI st X ALO WF HC KR N0 FIT"] Lemma chunk_geo :
     hm mod 16 = 0 /\ UB mod 16 = 0 /\ AB + 16 <= UB /\ AB <= hm
  /\ 0x10007fff8000 <= hm /\ UB + rup n 8 <= AB + S /\ AB + S <= ATOP /\ hm + 16 + rup n 8 <= ATOP /\ n <= 65536 /\ n <= Q_MAX
  /\ 0x10007fff8000 <= AB /\ n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ 8 <= S - rz_size n.
Proof.
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 12%nat; intros S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 _; nd_post).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. (pose proof (rounded_size_facts n N0) as ndP__; nd_pre ndP__ 5%nat; intros RS1 RS2 RS3 RS4 RS5; nd_post).
  subst S AB UB hm. generalize S1 S2 AL G1 G2 G7 G8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold Q_MAX, rup. intros. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI X ALO WF HC KR N0 FIT"] Lemma chunk_shadow_geo :
     shad UB = shad AB + shlen (rz_size n) /\ 2 <= shlen (rz_size n)
  /\ shlen (rup n 8) = granules n /\ 0 <= shlen (rup n 8)
  /\ shlen (rz_size n) + granules n <= shlen S
  /\ 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fff8000
  /\ shad (aregion L c) <= shad AB /\ shad AB + shlen S <= shad (aregion L c) + shlen (c_mapped_user (get_cls st c)).
Proof.
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. (pose proof (rounded_size_facts n N0) as ndP__; nd_pre ndP__ 5%nat; intros RS1 RS2 RS3 RS4 RS5; nd_post).
  subst S AB UB hm. unfold granules. rewrite !shad_div, !shlen_div.
  generalize S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold ASHOFF, rup, K_FREEARR_OFF, K_SPACE_SIZE. intros.
  Z.div_mod_to_equations. lia.
Qed.
End Chunk.
End CANSEC1.
End TwB.
End AFreeGeo.

(* [comment removed for export] *)
Module ARepExt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition aext (L : alayout) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
  \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
  \/ ATOP <= fst iv
  \/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47)).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nonempty (iv : Z * Z) : bool := fst iv <? snd iv.

#[using="Type"] Lemma sub_fp_filter_nonempty : forall W, sub_fp W (List.filter nonempty W).
Proof.
  unfold sub_fp. induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
  unfold nonempty in Hx. cbn [fst snd] in Hx. destruct (Z.ltb_spec lo hi).
  - cbn in Hx. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact Hx].
Qed.
#[using="Type"] Lemma munch_filter_nonempty : forall W m m', munch W m m' -> munch (List.filter nonempty W) m m'.
Proof. intros W m m' MU. eapply munch_weaken; [apply sub_fp_filter_nonempty | exact MU]. Qed.

#[using="Type"] Lemma filter_cons_eq : forall {A} (f : A -> bool) x l, List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. reflexivity. Qed.

#[using="Type"] Lemma disjoint_from_Forall : forall W A k,
  Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros A k HF; cbn; [exact I|].
  inversion HF as [| x l H1 H2]; subst. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ext_clear : forall L W A k,
  Forall (aext L) W -> 0 <= k ->
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= A) ->
  A + k <= ATOP ->
  (A + k <= shad ATOP \/ shad (2^47) <= A) ->
  disjoint_from (List.filter nonempty W) A k.
Proof.
  intros L W A k EXT Hk D1 D2 D3 D4. apply disjoint_from_Forall.
  induction W as [|[lo hi] W IH]; [constructor|].
  inversion EXT as [| x l E1 E2]; subst.
  rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
  destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
  constructor; [| apply IH; exact E2]. cbn [fst snd].
  unfold aext in E1. cbn [fst snd] in E1. specialize (E1 LT).
  clear IH E2 EXT. lia.
Qed.

(* [comment removed for export] *)
Section Ext.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

#[using="HL"] Theorem AREP_frame_ext : forall L st X m m' W,
  alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
             (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
          \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
          \/ ATOP <= fst iv
          \/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47))) W ->      (* [comment removed for export] *)
  AREP H L st X m'.
Proof.
  intros L st X m m' W ALO AR MU0 WM EXT.
  change (Forall (aext L) W) in EXT.
  pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
  (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(lia)) as FKI. unfold aobj in FK. (nd_pre FK 5%nat; intros FK3 FK1 FK2 FKS _; nd_post).
  unfold sclr, KLS in FKS. unfold AIMG_HI in FKI. pose proof atop_range as ATR.
  pose proof (fun A k => ext_clear L W A k EXT) as KX. cbn beta in KX. fold W' in KX.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_res_hi L ALO) as ORH.
  unfold aobj, sclr, KLS in OT, OC, ORS, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_fake_res L ALO) as D_f_res.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_c_f, D_f_res, D_n_f, D_s_f.
  (* [comment removed for export] *)
  assert (SHF : 2147450880 + 787968 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= shad ATOP
                /\ shad ATOP + 1048576 <= shad (2^47) /\ shad (2^47) = 17594333495296).
  { rewrite !shad_div, shlen_div. change (2^47) with 140737488355328. unfold ASHOFF in *. clear -FKI FK2 ATR. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 4%nat; intros SF1 SF2 SF3 SF4; nd_post).
  assert (SF0 : shlen 11571200 = 1446400) by (rewrite shlen_div; reflexivity).
  assert (SAT : 0x10006fef8000 <= shad ATOP <= 0x10007fef8000) by (rewrite shad_div; unfold ASHOFF; clear -ATR; Z.div_mod_to_equations; lia).
  assert (SHR : shad (al_res L) + shlen 137439023104 <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad (al_res L)).
  { destruct D_f_res as [D|D]; [right | left]; apply shad_sep; [exact D | clear -FK3 | exact D | clear -ORS]; Z.div_mod_to_equations; lia. }
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= shad ATOP).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS ORH. Z.div_mod_to_equations. lia. }
  (nd_pre SHRES 3%nat; intros SR1 SR2 SR3; nd_post).
  (* [comment removed for export] *)
  assert (FKB : al_fake L + 11571200 <= 2147450880 \/ 17594333495296 <= al_fake L) by (clear -FKS; lia).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0 <= A -> 0 <= k -> A + k <= AIMG_HI -> disjoint_from W' A k).
  { intros A k H1 H2 H3. unfold AIMG_HI in H3. apply KX; [exact H2| clear -H3 FKI; lia| clear -H3 SF1; lia| clear -H3 ATR; lia| clear -H3 SF0 SF1 SF2; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply KX; [exact H2| | clear -H1 H2 H3 SHR SR2; lia| clear -H3 SR3 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| clear -H3 SR3; lia].
    clear -H1 H3 SR1 SR3 FKB ATR. rewrite (shad_div ATOP) in *. unfold ASHOFF in *. lia. }
  (* [comment removed for export] *)
  assert (Kobj : forall A k, 0 <= k -> A + k <= ATOP -> (A + k <= 2147450880 \/ 17594333495296 <= A) ->
                 (A + k <= al_fake L \/ al_fake L + 11571200 <= A) -> disjoint_from W' A k).
  { intros A k H2 H3 HB H4. apply KX; [exact H2| exact H4| clear -HB SF0 SF1 SF2 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| exact H3| clear -HB H3 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia]. }
  clear KX.
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 ORS; lia | clear -H1 ORH; lia | clear -H1 H3 D_f_res; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OT; lia | clear -H1 H3 OT; lia | clear -H1 H3 D_t_f; lia]. }
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OC; lia | clear -H1 H3 OC; lia | clear -H1 H3 D_c_f; lia]. }
  assert (Ktls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W' A k).      (* [comment removed for export] *)
  { pose proof atp_sclr as TS. pose proof atp_below_atop as TT. pose proof (ad_tls_fake L ALO) as D_tls_f. unfold sclr, KLS, adisj in TS, D_tls_f.
    intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 TT; lia | clear -H1 H3 TS; lia | clear -H1 H3 D_tls_f; lia]. }
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W' m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  split.
  { eapply (hq_frame _ HL L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE]. unfold nonempty in NE. cbn [fst snd] in NE. apply Z.ltb_lt in NE.
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E NE). change (2^47)%Z with 140737488355328%Z in E.
      unfold AINSTANCE in *. change (shad 140737488355328) with 17594333495296%Z in E.
      split; [clear -E OT D_t_f SF0 SF1 SF2 SAT; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |];
        clear -E B1 B2 ORS ORH D_f_res SF0 SF2 SAT; lia.
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
      atop_facts. clear -E Ha FK1 FK2.
      destruct E as [[E1 E2]|[[E1 E2]|[E1|[E1 E2]]]].
      + do 10 right. left. lia.
      + do 2 right. left. rewrite shlen_div in E2. lia.
      + do 4 right. left. lia.
      + do 3 right. left. rewrite (shad_div 140737488355328) in E2. change (140737488355328 / 8)%Z with 17592186044416%Z in E2. unfold ASHOFF in E2. lia.
    - apply sec_same_refl. }
  split.
  { eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
    apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
    unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
    pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
    change (shad 140737488355328) with 17594333495296%Z in E.
    clear -E Ha FKI SF0 SF1 SF2 SAT ON OS D_n_f D_s_f ATR. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Ext.

(* [comment removed for export] *)
#[using="Type"] Lemma AHEAP_P_hb_fake : forall H L RNG st LB m p A n,
  AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> A + n <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 G7; nd_post). (nd_pre G7 8%nat; intros _ _ _ _ _ _ CF _; nd_post).
       pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold SEC_UOFF. clear -G3 G4 G5 CF SF. lia. }
  destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. (nd_pre M 3%nat; intros N0 FIT _; nd_post).
  (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. unfold adisj in D.
  pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
  subst A n. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP D N0 FIT RG RZ. lia.
Qed.

#[using="Type"] Lemma AREP_relro : forall H L st X m, AREP H L st X m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L st X m AR. (nd_pre AR 10%nat; intros _ _ _ _ _ _ _ _ HRO _; nd_post). exact HRO. Qed.

#[using="Type"] Lemma AHEAP_P_relro : forall H L RNG st LB m, AHEAP_P H L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L RNG st LB m (_ & _ & [X [AR _]] & _). exact (AREP_relro H L st X m AR). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHEAP_P_hb_range : forall H L RNG st LB m p A n,
  AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> ablock_range A n.
Proof.
  intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 G7; nd_post).
       pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold ablock_range, SEC_UOFF in *. clear -G1 G2 G3 G4 G5 SF.
       split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. (nd_pre M 3%nat; intros N0 FIT _; nd_post).
  (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  pose proof (slot_aligned L (xb_class b) (xb_slot b) SAL CLB) as AL.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_res_hi L ALO) as ORH.
  pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rz_size_eq (xb_n b)) as RZE.
  assert (RZ16 : rz_size (xb_n b) mod 16 = 0).
  { rewrite RZE. assert (0 <= rz_log (xb_n b)) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
    replace (2 ^ rz_log (xb_n b)) with (2 ^ (rz_log (xb_n b) - 0)) by (f_equal; lia).
    rewrite Z.mul_comm. apply Z_mod_mult. }
  subst A n. unfold ablock_range, xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
  split; [right; split; [clear -P5 RSP ORS ORH CLB RZ; lia| clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia]|]. split; [clear -N0; lia|].
  split; [clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia|].
  clear -AL RZ16. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition aext (L : alayout) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
  \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
  \/ ATOP <= fst iv
  \/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47)).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nonempty (iv : Z * Z) : bool := fst iv <? snd iv.

#[using="Type"] Lemma sub_fp_filter_nonempty : forall W, sub_fp W (List.filter nonempty W).
Proof.
  unfold sub_fp. induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
  unfold nonempty in Hx. cbn [fst snd] in Hx. destruct (Z.ltb_spec lo hi).
  - cbn in Hx. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact Hx].
Qed.
#[using="Type"] Lemma munch_filter_nonempty : forall W m m', munch W m m' -> munch (List.filter nonempty W) m m'.
Proof. intros W m m' MU. eapply munch_weaken; [apply sub_fp_filter_nonempty | exact MU]. Qed.

#[using="Type"] Lemma filter_cons_eq : forall {A} (f : A -> bool) x l, List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. reflexivity. Qed.

#[using="Type"] Lemma disjoint_from_Forall : forall W A k,
  Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros A k HF; cbn; [exact I|].
  inversion HF as [| x l H1 H2]; subst. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ext_clear : forall L W A k,
  Forall (aext L) W -> 0 <= k ->
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= A) ->
  A + k <= ATOP ->
  (A + k <= shad ATOP \/ shad (2^47) <= A) ->
  disjoint_from (List.filter nonempty W) A k.
Proof.
  intros L W A k EXT Hk D1 D2 D3 D4. apply disjoint_from_Forall.
  induction W as [|[lo hi] W IH]; [constructor|].
  inversion EXT as [| x l E1 E2]; subst.
  rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
  destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
  constructor; [| apply IH; exact E2]. cbn [fst snd].
  unfold aext in E1. cbn [fst snd] in E1. specialize (E1 LT).
  clear IH E2 EXT. lia.
Qed.

(* [comment removed for export] *)
Section Ext.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

#[using="HL"] Theorem AREP_frame_ext : forall L st X m m' W,
  alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
             (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
          \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
          \/ ATOP <= fst iv
          \/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47))) W ->      (* [comment removed for export] *)
  AREP H L st X m'.
Proof.
  intros L st X m m' W ALO AR MU0 WM EXT.
  change (Forall (aext L) W) in EXT.
  pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
  (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(lia)) as FKI. unfold aobj in FK. (nd_pre FK 5%nat; intros FK3 FK1 FK2 FKS _; nd_post).
  unfold sclr, KLS in FKS. unfold AIMG_HI in FKI. pose proof atop_range as ATR.
  pose proof (fun A k => ext_clear L W A k EXT) as KX. cbn beta in KX. fold W' in KX.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_res_hi L ALO) as ORH.
  unfold aobj, sclr, KLS in OT, OC, ORS, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_fake_res L ALO) as D_f_res.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_c_f, D_f_res, D_n_f, D_s_f.
  (* [comment removed for export] *)
  assert (SHF : 2147450880 + 788480 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= shad ATOP
                /\ shad ATOP + 1048576 <= shad (2^47) /\ shad (2^47) = 17594333495296).
  { rewrite !shad_div, shlen_div. change (2^47) with 140737488355328. unfold ASHOFF in *. clear -FKI FK2 ATR. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 4%nat; intros SF1 SF2 SF3 SF4; nd_post).
  assert (SF0 : shlen 11571200 = 1446400) by (rewrite shlen_div; reflexivity).
  assert (SAT : 0x10006fef8000 <= shad ATOP <= 0x10007fef8000) by (rewrite shad_div; unfold ASHOFF; clear -ATR; Z.div_mod_to_equations; lia).
  assert (SHR : shad (al_res L) + shlen 137439023104 <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad (al_res L)).
  { destruct D_f_res as [D|D]; [right | left]; apply shad_sep; [exact D | clear -FK3 | exact D | clear -ORS]; Z.div_mod_to_equations; lia. }
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= shad ATOP).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS ORH. Z.div_mod_to_equations. lia. }
  (nd_pre SHRES 3%nat; intros SR1 SR2 SR3; nd_post).
  (* [comment removed for export] *)
  assert (FKB : al_fake L + 11571200 <= 2147450880 \/ 17594333495296 <= al_fake L) by (clear -FKS; lia).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0 <= A -> 0 <= k -> A + k <= AIMG_HI -> disjoint_from W' A k).
  { intros A k H1 H2 H3. unfold AIMG_HI in H3. apply KX; [exact H2| clear -H3 FKI; lia| clear -H3 SF1; lia| clear -H3 ATR; lia| clear -H3 SF0 SF1 SF2; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply KX; [exact H2| | clear -H1 H2 H3 SHR SR2; lia| clear -H3 SR3 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| clear -H3 SR3; lia].
    clear -H1 H3 SR1 SR3 FKB ATR. rewrite (shad_div ATOP) in *. unfold ASHOFF in *. lia. }
  (* [comment removed for export] *)
  assert (Kobj : forall A k, 0 <= k -> A + k <= ATOP -> (A + k <= 2147450880 \/ 17594333495296 <= A) ->
                 (A + k <= al_fake L \/ al_fake L + 11571200 <= A) -> disjoint_from W' A k).
  { intros A k H2 H3 HB H4. apply KX; [exact H2| exact H4| clear -HB SF0 SF1 SF2 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| exact H3| clear -HB H3 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia]. }
  clear KX.
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 ORS; lia | clear -H1 ORH; lia | clear -H1 H3 D_f_res; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OT; lia | clear -H1 H3 OT; lia | clear -H1 H3 D_t_f; lia]. }
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OC; lia | clear -H1 H3 OC; lia | clear -H1 H3 D_c_f; lia]. }
  assert (Ktls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W' A k).      (* [comment removed for export] *)
  { pose proof atp_sclr as TS. pose proof atp_below_atop as TT. pose proof (ad_tls_fake L ALO) as D_tls_f. unfold sclr, KLS, adisj in TS, D_tls_f.
    intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 TT; lia | clear -H1 H3 TS; lia | clear -H1 H3 D_tls_f; lia]. }
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W' m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  split.
  { eapply (hq_frame _ HL L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE]. unfold nonempty in NE. cbn [fst snd] in NE. apply Z.ltb_lt in NE.
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E NE). change (2^47)%Z with 140737488355328%Z in E.
      unfold AINSTANCE in *. change (shad 140737488355328) with 17594333495296%Z in E.
      split; [clear -E OT D_t_f SF0 SF1 SF2 SAT; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |];
        clear -E B1 B2 ORS ORH D_f_res SF0 SF2 SAT; lia.
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
      atop_facts. clear -E Ha FK1 FK2.
      destruct E as [[E1 E2]|[[E1 E2]|[E1|[E1 E2]]]].
      + do 10 right. left. lia.
      + do 2 right. left. rewrite shlen_div in E2. lia.
      + do 4 right. left. lia.
      + do 3 right. left. rewrite (shad_div 140737488355328) in E2. change (140737488355328 / 8)%Z with 17592186044416%Z in E2. unfold ASHOFF in E2. lia.
    - apply sec_same_refl. }
  split.
  { eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
    apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
    unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
    pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
    change (shad 140737488355328) with 17594333495296%Z in E.
    clear -E Ha FKI SF0 SF1 SF2 SAT ON OS D_n_f D_s_f ATR. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Ext.

(* [comment removed for export] *)
#[using="Type"] Lemma AHEAP_P_hb_fake : forall H L RNG st LB m p A n,
  AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> A + n <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 G7; nd_post). (nd_pre G7 8%nat; intros _ _ _ _ _ _ CF _; nd_post).
       pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold SEC_UOFF. clear -G3 G4 G5 CF SF. lia. }
  destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. (nd_pre M 3%nat; intros N0 FIT _; nd_post).
  (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. unfold adisj in D.
  pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
  subst A n. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP D N0 FIT RG RZ. lia.
Qed.

#[using="Type"] Lemma AREP_relro : forall H L st X m, AREP H L st X m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L st X m AR. (nd_pre AR 10%nat; intros _ _ _ _ _ _ _ _ HRO _; nd_post). exact HRO. Qed.

#[using="Type"] Lemma AHEAP_P_relro : forall H L RNG st LB m, AHEAP_P H L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L RNG st LB m (_ & _ & [X [AR _]] & _). exact (AREP_relro H L st X m AR). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHEAP_P_hb_range : forall H L RNG st LB m p A n,
  AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> ablock_range A n.
Proof.
  intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. (nd_pre G 7%nat; intros G1 G2 G3 G4 G5 G6 G7; nd_post).
       pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold ablock_range, SEC_UOFF in *. clear -G1 G2 G3 G4 G5 SF.
       split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. (nd_pre M 3%nat; intros N0 FIT _; nd_post).
  (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  pose proof (slot_aligned L (xb_class b) (xb_slot b) SAL CLB) as AL.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_res_hi L ALO) as ORH.
  pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rz_size_eq (xb_n b)) as RZE.
  assert (RZ16 : rz_size (xb_n b) mod 16 = 0).
  { rewrite RZE. assert (0 <= rz_log (xb_n b)) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
    replace (2 ^ rz_log (xb_n b)) with (2 ^ (rz_log (xb_n b) - 0)) by (f_equal; lia).
    rewrite Z.mul_comm. apply Z_mod_mult. }
  subst A n. unfold ablock_range, xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
  split; [right; split; [clear -P5 RSP ORS ORH CLB RZ; lia| clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia]|]. split; [clear -N0; lia|].
  split; [clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia|].
  clear -AL RZ16. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.
End TwB.
End ARepExt.
