(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StoreOk AgentLib.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
Definition TCAP : Z := 512.
(* [comment removed for export] *)
Definition IMGHI : Z := 0x5fc000.
Definition VATOP : Z := 2 ^ 47.

Section Depot.
Variable segs : list Segment.
Variables D SS : Z.

Definition mem := word -> option byte.
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

(* [comment removed for export] *)
Definition rdw (M : mem) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition wr_ok (M : mem) (a len : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= len -> store_ok segs M (Z_to_bv 64 (a + d)) m = true.

Record depot_st := DST { d_N : Z; d_T : Z }.

Definition DepotInvS (K b17 b18 : Z) (st : depot_st) (M : mem) : Prop :=
  let N := d_N st in let T := d_T st in
  0 <= K /\ 0 <= N /\ N + K < 65535 /\ 0 <= T /\ T + 5 * K <= TCAP
  /\ rdw M (D + 0x400000) 4 N /\ rdw M (D + 0x400010) 8 b17
  /\ rdw M SS 8 T /\ rdw M (SS + 16) 8 b18 /\ rdw M (SS + 24) 4 T
  /\ IMGHI <= b17 /\ b17 + 2^20 <= VATOP /\ b17 mod 4096 = 0
  /\ IMGHI <= b18 /\ b18 + 2^23 <= VATOP /\ b18 mod 4096 = 0
  /\ (b17 + 2^20 <= b18 \/ b18 + 8 * TCAP <= b17)
  /\ 0x10000 <= SS /\ SS + 32 <= D /\ D + 0x400018 <= IMGHI /\ D mod 8 = 0 /\ SS mod 8 = 0
  /\ wr_ok M D 0x400018 /\ wr_ok M SS 32 /\ wr_ok M b17 (2^20) /\ wr_ok M b18 (8 * TCAP)
  /\ (forall b, 0 <= b < 2^20 -> exists v, rdw M (D + 4 * b) 4 v /\ 0 <= v <= N)
  /\ (forall i, 1 <= i <= N -> exists l, rdw M (b17 + 16 * i + 8) 4 l /\ 0 <= l < i).

Definition DepotInv (K b17 b18 : Z) (M : mem) : Prop := exists st, DepotInvS K b17 b18 st M.

(* [comment removed for export] *)
Definition depot_fp (b17 b18 : Z) : list (Z * Z) :=
  [(SS, SS + 32); (D, D + 0x400018); (b17, b17 + 2^20); (b18, b18 + 8 * TCAP)].

Definition in_fp (fp : list (Z * Z)) (x : word) : Prop :=
  Exists (fun it => fst it <= bv_unsigned x < snd it) fp.

(* [comment removed for export] *)

Lemma store_ok_ext : forall (m1 m2 : mem) n (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m1 x = m2 x) ->
  store_ok segs m1 a n = true -> store_ok segs m2 a n = true.
Proof.
  intros m1 m2 n a Hnw Hext H.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview. rewrite <- (Hext x Hx).
  pose proof (store_ok_all segs m1 n a Hnw H x Hx) as W. unfold wview in W. exact W.
Qed.

Lemma wr_ok_frame : forall M M' a len,
  0 <= a -> a + len <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + len -> M' x = M x) ->
  wr_ok M a len -> wr_ok M' a len.
Proof.
  intros M M' a len Ha Hlen Hext H d m Hd Hdm. destruct m as [|m']; [reflexivity|].
  apply (store_ok_ext M M' (S m') (Z_to_bv 64 (a + d))); rewrite ?u64_lit by lia; [lia| |apply H; assumption].
  intros x Hx. symmetry. apply Hext. lia.
Qed.

Lemma rdw_frame : forall M M' a n v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M' x = M x) ->
  rdw M a n v -> rdw M' a n v.
Proof.
  intros M M' a n v Ha Hn Hext H. unfold rdw in *. destruct n as [|n']; [exact H|].
  rewrite (rdn_ext segs (S n') M' M (Z_to_bv 64 a)); rewrite ?u64_lit by lia; [exact H | lia |].
  intros x Hx. apply Hext. lia.
Qed.

(* [comment removed for export] *)
Theorem DepotInv_frame : forall K b17 b18 M M',
  (forall x : word, in_fp (depot_fp b17 b18) x -> M' x = M x) ->
  DepotInv K b17 b18 M -> DepotInv K b17 b18 M'.
Proof.
  intros K b17 b18 M M' Hext [[N T] HI]. exists (DST N T).
  unfold DepotInvS in *. cbn [d_N d_T] in *.
  destruct HI as (HK & HN & HNK & HT & HTK & RN & R17 & RT & R18 & RC & A1 & A2 & A3 & A4 & A5 & A6 & A7
                  & L1 & L2 & L3 & L4 & L5 & W1 & W2 & W3 & W4 & TAB & NODES).
  unfold TCAP, IMGHI, VATOP in *.
  assert (E1 : forall x : word, SS <= bv_unsigned x < SS + 32 -> M' x = M x)
    by (intros x Hx; apply Hext; unfold in_fp, depot_fp; apply Exists_cons_hd; cbn; lia).
  assert (E2 : forall x : word, D <= bv_unsigned x < D + 0x400018 -> M' x = M x)
    by (intros x Hx; apply Hext; unfold in_fp, depot_fp; apply Exists_cons_tl, Exists_cons_hd; cbn; lia).
  assert (E3 : forall x : word, b17 <= bv_unsigned x < b17 + 2^20 -> M' x = M x)
    by (intros x Hx; apply Hext; unfold in_fp, depot_fp; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn; lia).
  assert (E4 : forall x : word, b18 <= bv_unsigned x < b18 + 8 * 512 -> M' x = M x)
    by (intros x Hx; apply Hext; unfold in_fp, depot_fp, TCAP; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn; lia).
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - apply (rdw_frame M M'); try lia; [|exact RN]. intros x Hx. apply E2. cbn in Hx. lia.
  - apply (rdw_frame M M'); try lia; [|exact R17]. intros x Hx. apply E2. cbn in Hx. lia.
  - apply (rdw_frame M M'); try lia; [|exact RT]. intros x Hx. apply E1. cbn in Hx. lia.
  - apply (rdw_frame M M'); try lia; [|exact R18]. intros x Hx. apply E1. cbn in Hx. lia.
  - apply (rdw_frame M M'); try lia; [|exact RC]. intros x Hx. apply E1. cbn in Hx. lia.
  - apply (wr_ok_frame M M'); try lia; [|exact W1]. exact E2.
  - apply (wr_ok_frame M M'); try lia; [|exact W2]. exact E1.
  - apply (wr_ok_frame M M'); try lia; [|exact W3]. exact E3.
  - apply (wr_ok_frame M M'); try lia; [|exact W4]. exact E4.
  - intros b Hb. destruct (TAB b Hb) as (v & Rv & Bv). exists v. split; [|exact Bv].
    apply (rdw_frame M M'); try lia; [|exact Rv]. intros x Hx. apply E2. cbn in Hx. lia.
  - intros i Hi. destruct (NODES i Hi) as (l & Rl & Bl). exists l. split; [|exact Bl].
    apply (rdw_frame M M'); try lia; [|exact Rl]. intros x Hx. apply E3. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
Definition mem_extends (M M' : mem) : Prop :=
  (forall a v, M a = Some v -> M' a = Some v) /\ (forall a, M' a <> M a -> seg_rom segs a = None).

Lemma rdn_mem_extends : forall M M' n a bs, mem_extends M M' -> rdn segs M a n = Some bs -> rdn segs M' a n = Some bs.
Proof.
  intros M M' n. induction n as [|n IH]; intros a bs [HE1 HE2] H; [exact H|].
  cbn [rdn] in H |- *.
  assert (Hb : forall b, match M a with Some b0 => Some b0 | None => seg_rom segs a end = Some b ->
                       match M' a with Some b0 => Some b0 | None => seg_rom segs a end = Some b).
  { intros b Hm. destruct (M a) as [v|] eqn:EMa.
    - rewrite (HE1 a v EMa). exact Hm.
    - destruct (M' a) as [v'|] eqn:EM'a; [|exact Hm].
      exfalso. pose proof (HE2 a ltac:(rewrite EMa, EM'a; discriminate)) as X. rewrite X in Hm. discriminate. }
  destruct (match M a with Some b0 => Some b0 | None => seg_rom segs a end) as [b|] eqn:E1; [|discriminate].
  rewrite (Hb b eq_refl).
  destruct (rdn segs M (a + 1)%bv n) as [rest|] eqn:E2; [|discriminate].
  rewrite (IH _ _ (conj HE1 HE2) E2). exact H.
Qed.

Lemma wr_ok_extends : forall M M' a len, mem_extends M M' -> wr_ok M a len -> wr_ok M' a len.
Proof.
  intros M M' a len [HE1 _] H d m Hd Hdm. eapply store_ok_mono; [|apply H; assumption].
  intros x Hx. destruct (M x) as [v|] eqn:EM; [|exfalso; apply Hx; reflexivity]. rewrite (HE1 x v EM). discriminate.
Qed.

Theorem DepotInv_extends : forall K b17 b18 M M', mem_extends M M' -> DepotInv K b17 b18 M -> DepotInv K b17 b18 M'.
Proof.
  intros K b17 b18 M M' HX [[N T] HI]. exists (DST N T).
  unfold DepotInvS in *. cbn [d_N d_T] in *.
  destruct HI as (HK & HN & HNK & HT & HTK & RN & R17 & RT & R18 & RC & A1 & A2 & A3 & A4 & A5 & A6 & A7
                  & L1 & L2 & L3 & L4 & L5 & W1 & W2 & W3 & W4 & TAB & NODES).
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try (eapply rdn_mem_extends; [exact HX | assumption]);
    try (eapply wr_ok_extends; [exact HX | assumption]).
  - intros b Hb. destruct (TAB b Hb) as (v & Rv & Bv). exists v. split; [eapply rdn_mem_extends; [exact HX | exact Rv] | exact Bv].
  - intros i Hi. destruct (NODES i Hi) as (l & Rl & Bl). exists l. split; [eapply rdn_mem_extends; [exact HX | exact Rl] | exact Bl].
Qed.

Theorem DepotInv_mono : forall K K' b17 b18 M, 0 <= K' <= K -> DepotInv K b17 b18 M -> DepotInv K' b17 b18 M.
Proof.
  intros K K' b17 b18 M HK [[N T] HI]. exists (DST N T). unfold DepotInvS in *. cbn [d_N d_T] in *.
  unfold TCAP in *.
  repeat match goal with |- _ /\ _ => split end; try tauto; try lia.
Qed.

End Depot.
End WithFP1.

