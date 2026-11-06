(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout.
Import ListNotations.
Open Scope Z_scope.

Notation A0_DTV := 6187408%Z.
Notation A0_TLSB := 6189424%Z.

Definition fs_tls_env {HC : HasCeiling} (THR DTV TLSB BLK FSB0 : Z) (m : mem) : Prop :=
  rw_cells asegs m 0xabeb8 [C8 (wz 0xa3130)]
  /\ rw_cells asegs m 0xaadc0 [C8 (wz 1); C8 (wz 18446744073709549568); C8 (wz 8)]
  /\ rw_cells asegs m (A0_TP - 8) [C8 (wz DTV)] /\ rw_cells asegs m (DTV + 8) [C8 (wz TLSB)]
  /\ rw_cells asegs m (TLSB - 2048) [C8 (wz FSB0)]
  /\ rw_cells asegs m 0x1454b1 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xaa120 [C8 (wz 0x143398)] /\ rw_cells asegs m 0x143398 [C4 (wz 0)]
  /\ rw_cells asegs m (A0_TP + 8) [C8 (wz BLK)]
  /\ (exists e, rw_cells asegs m (BLK + 24) [C8 (wz e)] /\ 0 < e < 2^64)
  /\ (exists tb te, rw_cells asegs m (THR + 48) [C8 tb; C8 te])
  /\ 0 < DTV /\ DTV + 16 <= alloc_ceiling /\ 2048 <= TLSB <= alloc_ceiling /\ 0 < BLK /\ BLK + 32 <= alloc_ceiling.

Definition fsenv_cls {HC : HasCeiling} (FSB : Z) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (FSB <= fst iv /\ snd iv <= FSB + A0_FS_SIZE)
  \/ (0x7fff7000 <= fst iv /\ snd iv <= 0x10007fff8000)
  \/ (0x10000 <= fst iv /\ snd iv <= 0x609000 /\ env_safe [iv]).

Definition img_apart (A n : Z) : Prop :=
  0x32000 <= A /\ A + n <= 0x609000
  /\ (A + n <= 0xaeac8 \/ 0xaed18 <= A) /\ (A + n <= 0xb0290 \/ 0xb0291 <= A) /\ (A + n <= 0x606fc0 \/ 0x607480 <= A)
  /\ (A + n <= 0x5d5f40 \/ 0x5e5fa0 <= A) /\ (A + n <= 0x5e68c8 \/ 0x5e68d0 <= A) /\ (A + n <= 0x6069b0 \/ 0x6069b8 <= A)
  /\ (A + n <= 0x6069c0 \/ 0x6069d8 <= A) /\ (A + n <= 0x606be0 \/ 0x606be4 <= A) /\ (A + n <= 0x606c00 \/ 0x606c08 <= A)
  /\ (A + n <= 0xb0298 \/ 0xb10f8 <= A) /\ (A + n <= 0x1857c8 \/ 0x5957f8 <= A) /\ (A + n <= 0xb4b00 \/ 0x135b30 <= A)
  /\ (A + n <= 0x143388 \/ 0x14338c <= A).

Section F.
Context {HC : HasCeiling}.
Variable FSB : Z.

#[using="Type"] Lemma fsenv_cls_img : forall iv A n, 0 <= n -> env_safe [iv] -> 0x10000 <= fst iv -> snd iv <= 0x609000 -> img_apart A n ->
  A + n <= fst iv \/ snd iv <= A.
Proof.
  intros [lo hi] A n Hn SAFE LO HI IA. unfold env_safe in SAFE. inversion_clear SAFE as [|x l S1 _]. cbn [fst snd] in *.
  unfold img_apart in IA. destruct IA as (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14).
  destruct S1 as [S|[S|[S|[S|[S|[S|[S|[S|[S|[S|[S|[S|[S|[S|S]]]]]]]]]]]]]]; lia.
Qed.

#[using="Type"] Lemma fsenv_cls_disjoint : forall W, Forall (fsenv_cls FSB) W -> forall A n, 0 <= n ->
  A + n <= alloc_ceiling -> (A + n <= FSB \/ FSB + A0_FS_SIZE <= A) -> (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A) ->
  (A + n <= 0x10000 \/ 0x609000 <= A \/ img_apart A n) -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros FA A n Hn C1 C2 C3 C4; cbn [disjoint_from]; [exact I|].
  inversion_clear FA as [|x l F1 F2]. split; [| apply IH; assumption].
  unfold fsenv_cls in F1. cbn [fst snd] in F1. destruct F1 as [F|[F|[F|(F1 & F3 & F4)]]]; [lia| lia| lia|].
  destruct C4 as [C|[C|C]]; [lia| lia|]. exact (fsenv_cls_img (lo, hi) A n Hn F4 F1 F3 C).
Qed.
End F.

Section S.
Context {HC : HasCeiling}.

#[using="Type"] Lemma stack_disjoint : forall W, Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> forall A n, A + n <= alloc_ceiling -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros FA A n HA; cbn [disjoint_from]; [exact I|].
  inversion_clear FA as [|x l F1 F2]. cbn [fst] in F1. split; [lia| apply IH; assumption].
Qed.

#[using="Type"] Lemma thread_env_stack : forall TL W (m m' : mem), thread_env TL m -> thread_layout_ok TL -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> thread_env TL m'.
Proof.
  intros TL W m m' TE TLO MU WM FA. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof TLO as (_ & TC2 & _ & TT2 & _). unfold thread_env in *.
  destruct TE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  repeat match goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply (stack_disjoint W FA); cbn [cells_size csize Nat.add]; clear - ACR TC2 TT2; lia]).
Qed.

#[using="Type"] Lemma fs_tls_env_stack : forall THR DTV TLSB BLK FSB0 W (m m' : mem), fs_tls_env THR DTV TLSB BLK FSB0 m -> THR + 64 <= alloc_ceiling ->
  munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> fs_tls_env THR DTV TLSB BLK FSB0 m'.
Proof.
  intros THR DTV TLSB BLK FSB0 W m m' (RTG & DESC & DTVC & DTV1 & FSTLS & ITG & GVB & VB & BLKC & (e & ENT & ER) & (tb & te & THRC) & PURE) TH MU WM FA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof PURE as (D0 & DHI & TLR & B0 & BHI).
  assert (TR : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells asegs m' A cs)
    by (intros A cs H HA; eapply rw_cells_transport; [exact H| exact MU| exact WM| apply (stack_disjoint W FA); exact HA]).
  unfold fs_tls_env.
  split; [apply TR; [exact RTG| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [apply TR; [exact DESC| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [apply TR; [exact DTVC| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [apply TR; [exact DTV1| cbn [cells_size csize Nat.add]; clear - DHI; lia]|].
  split; [apply TR; [exact FSTLS| cbn [cells_size csize Nat.add]; clear - TLR; lia]|].
  split; [apply TR; [exact ITG| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [apply TR; [exact GVB| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [apply TR; [exact VB| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [apply TR; [exact BLKC| cbn [cells_size csize Nat.add]; clear - ACR; lia]|].
  split; [exists e; split; [apply TR; [exact ENT| cbn [cells_size csize Nat.add]; clear - BHI; lia]| exact ER]|].
  split; [exists tb, te; apply TR; [exact THRC| cbn [cells_size csize Nat.add]; clear - TH; lia]|].
  exact PURE.
Qed.
End S.

Section I.
Context {HC : HasCeiling}.
Variable L : alayout.
Variable BLK : Z.
Hypothesis AO : alayout_ok L.
Hypothesis BLK_R : region_ok (BLK, 4096).
Hypothesis BLK_FS : apart BLK 4096 (al_fsb L) A0_FS_SIZE.

Definition fsenv_B (m : mem) : Prop :=
  thread_env (al_thread L) m /\ fs_tls_env (at_thr (al_thread L)) A0_DTV A0_TLSB BLK (al_fsb L) m.

#[using="AO BLK_R BLK_FS"] Lemma fsenv_B_frame : forall m m' W, fsenv_B m -> munch W m m' -> Forall (fsenv_cls (al_fsb L)) W -> fsenv_B m'.
Proof.
  intros m m' W (TE & RTG & DESC & DTVC & DTV1 & FSTLS & ITG & GVB & VB & BLKC & (e & ENT & ER) & (tb & te & THRC) & PURE) MU FA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  layout_facts AO 2%nat RC. layout_facts AO 3%nat RT. layout_facts AO 4%nat RF.
  layout_apart_fact AO 2%nat 4%nat AC. layout_apart_fact AO 3%nat 4%nat AT.
  destruct RC as ((RC1 & _) & RC2 & _). destruct RT as ((RT1 & _) & RT2 & _). destruct RF as ((RF1 & _) & RF2 & _).
  destruct BLK_R as (RB1 & RB2 & _). cbn [fst snd] in RB1, RB2. unfold apart in BLK_FS.
  assert (FS0 : 0x609000 <= al_fsb L) by (clear - RF1; lia).
  pose proof (fsenv_cls_disjoint (al_fsb L) W FA) as DJ.
  assert (TR : forall A cs, rw_cells asegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs)
    by (intros A cs HC0 HD; eapply rw_cells_transport_mo; [exact HC0| exact MU| exact HD]).
  assert (IMG : forall A cs, rw_cells asegs m A cs -> img_apart A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs).
  { intros A cs HC0 IA. apply TR; [exact HC0|]. pose proof IA as (I0 & I1 & _). apply DJ; [lia| lia| lia| lia| right; right; exact IA]. }
  assert (THR : forall o cs, rw_cells asegs m (at_thr (al_thread L) + o) cs -> 0 <= o -> o + Z.of_nat (cells_size cs) <= 4096 ->
                             rw_cells asegs m' (at_thr (al_thread L) + o) cs).
  { intros o cs HC0 O1 O2. apply TR; [exact HC0|]. apply DJ; [lia| clear - RT2 O2; lia| clear - AT O1 O2; lia| clear - RT1 O1 O2; lia| clear - RT1 O1 O2; lia]. }
  split.
  - unfold thread_env in *. destruct TE as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
    repeat match goal with |- _ /\ _ => split end.
    + apply IMG; [exact T1| cbn; unfold img_apart; clear; lia].
    + apply IMG; [exact T2| cbn; unfold img_apart; clear; lia].
    + apply IMG; [exact T3| cbn; unfold img_apart; clear; lia].
    + apply IMG; [exact T4| cbn; unfold img_apart; clear; lia].
    + apply TR; [exact T5|]. cbn [cells_size csize Nat.add]. apply DJ; [lia| clear - RC2; lia| clear - AC; lia| clear - RC1; lia| clear - RC1; lia].
    + apply THR; [exact T6| lia| cbn; lia].
    + apply THR; [exact T7| lia| cbn; lia].
    + apply THR; [exact T8| lia| cbn; lia].
    + apply IMG; [exact T9| cbn; unfold img_apart; clear; lia].
    + apply IMG; [exact T10| cbn; unfold img_apart; clear; lia].
  - unfold fs_tls_env. change (A0_TP - 8) with 6187368 in *. change (A0_TP + 8) with 6187384 in *.
    change (A0_DTV + 8) with 6187416 in *. change (A0_TLSB - 2048) with 6187376 in *.
    split; [apply IMG; [exact RTG| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact DESC| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact DTVC| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact DTV1| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact FSTLS| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact ITG| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact GVB| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact VB| cbn; unfold img_apart; clear; lia]|].
    split; [apply IMG; [exact BLKC| cbn; unfold img_apart; clear; lia]|].
    split. { exists e. split; [| exact ER]. apply TR; [exact ENT|]. cbn [cells_size csize Nat.add].
             apply DJ; [lia| clear - RB2; lia| clear - BLK_FS; lia| clear - RB1; lia| clear - RB1; lia]. }
    split. { exists tb, te. apply THR; [exact THRC| lia| cbn; lia]. }
    exact PURE.
Qed.
End I.
